(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open Domains
open ControlFlowGraph
open Lexing

let assertion_failed _ (p, _) =
  (* on part du principe que les expressions des assertions tiennent sur une
     ligne *)
  Printf.eprintf "File \"%s\", line %d: Assertion failure\n"
    p.pos_fname p.pos_lnum

module Iterator (D : Domain.DOMAIN) = struct
  type state = Unexplored | Exploring | Finished

  let rec dfs states widens v =
    let state = match Hashtbl.find_opt states v with
      | None -> Unexplored
      | Some s -> s
    in
    if state = Exploring then
      Hashtbl.add widens v ()
    else if state = Unexplored then begin
      Hashtbl.replace states v Exploring;
      List.iter
        (fun {arc_dst; _} -> dfs states widens arc_dst) v.node_out;
      Hashtbl.replace states v Finished
    end

  module DMap = Map.Make(struct type t = D.t let compare = compare end)

  let show_map cfg map =
    let iter_node node : unit =
      Format.printf "<%i>: %a@ " node.node_id D.pp (NodeMap.find node map) in
    Format.printf "Node Values:@   @[<v 0>" ;
    List.iter iter_node cfg.cfg_nodes ;
    Format.printf "@]"

  let out_nodes {node_out; _} = List.map (fun {arc_dst; _} -> arc_dst) node_out

  let iter cfg =
    let widening_points = Hashtbl.create 4096 in
    dfs (Hashtbl.create 4096) widening_points cfg.cfg_init_entry;
    List.iter (fun {func_entry; _} ->
        dfs (Hashtbl.create 4096) widening_points func_entry) cfg.cfg_funcs;
    let memo_funcs = FuncHash.create 4096 in
    let rec loop bwd map = function
      | [] -> map
      | hd :: tl ->
        let vals =
          List.map (fun arc ->
              match NodeMap.find_opt arc.arc_src map with
              | None -> D.top, arc
              | Some v -> v, arc) (if bwd then hd.node_out else hd.node_in)
        in
        let treat_instr (v, {arc_inst; arc_src; _}) = match arc_inst with
          | CFG_skip _ -> v
          | CFG_assign (var, e) ->
            if bwd then
              D.bwd_assign (NodeMap.find arc_src map) var e v
            else D.assign v var e
          | CFG_guard e ->
            D.guard v e
          | CFG_assert (e, _) ->
            D.guard v e
          | CFG_call f ->
            if bwd then
              let m' = DMap.find v (FuncHash.find memo_funcs f) in
              let m' = NodeMap.add f.func_exit v m' in
              let m'' = loop true m' @@
                List.map (fun {arc_src; _} -> arc_src) f.func_exit.node_in
              in
              NodeMap.find f.func_entry m''
            else
              let m = match FuncHash.find_opt memo_funcs f with
                | None -> DMap.empty
                | Some m -> m
              in match DMap.find_opt v m with
              | Some m' -> NodeMap.find f.func_exit m'
              | None ->
                let m' = loop false (NodeMap.singleton f.func_entry v) @@
                  out_nodes f.func_entry
                in
                let v' = NodeMap.find f.func_exit m' in
                FuncHash.replace memo_funcs f (DMap.add v m' m);
                v'
        in
        let vals = List.map treat_instr vals in
        let v = List.fold_left
            (if Hashtbl.mem widening_points hd then D.widen else D.join)
            D.bottom
            vals
        in
        let tl =
          if NodeMap.find_opt hd map = Some v
          then tl
          else out_nodes hd @ tl
        in
        loop bwd (NodeMap.add hd v map) tl
    in

    let m = loop false (NodeMap.singleton cfg.cfg_init_entry D.init)
      (out_nodes cfg.cfg_init_entry)
    in
    let rec search_main = function
      | [] -> failwith "file has no main function"
      | {func_name; func_entry; _} :: _ when
          String.starts_with ~prefix:"main" func_name ->
        let m = NodeMap.add func_entry (NodeMap.find cfg.cfg_init_exit m) m in
        loop false m (out_nodes func_entry)
      | _ :: tl -> search_main tl
    in
    let map = search_main cfg.cfg_funcs in
    let check_assertation {arc_inst; arc_src; _} = match arc_inst with
    | CFG_assert (e, pos) ->
      let v = NodeMap.find arc_src map in
      let fail = D.guard v (CFG_bool_unary (AbstractSyntax.AST_NOT, e)) in
      if not D.(is_bottom fail) then
        if !Options.backward then begin
          let map_fail = NodeMap.add arc_src fail map in
          let map = loop true map_fail @@
            List.map (fun {arc_src; _} -> arc_src) arc_src.node_in
          in
          if not D.(is_bottom (NodeMap.find arc_src map)) then
            (assertion_failed e pos;
             Format.printf "It can fail in the following environment : %a."
               D.pp (NodeMap.find arc_src map))
          else
            print_endline "backward analysis eliminated a false positive"
        end else
          assertion_failed e pos
    | _ -> ()
    in
    List.iter check_assertation cfg.cfg_arcs;
    map
end

let iterate cfg (module D : Domains.Domain.DOMAIN) =
  let module I = Iterator(D) in
  let map = I.iter cfg in
  let _ = Random.self_init () in
  I.show_map cfg map
