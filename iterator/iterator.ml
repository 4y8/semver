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
  let out_nodes {node_out; _} = List.map (fun {arc_dst; _} -> arc_dst) node_out
  let iter cfg =
    let widening_points = Hashtbl.create 4096 in
    dfs (Hashtbl.create 4096) widening_points cfg.cfg_init_entry;
    List.iter (fun {func_entry; _} ->
        dfs (Hashtbl.create 4096) widening_points func_entry) cfg.cfg_funcs;
    let memo_funcs = FuncHash.create 4096 in
    let rec loop map = function
      | [] -> map
      | hd :: tl ->
        let vals =
          List.map (fun arc ->
              match NodeMap.find_opt arc.arc_src map with
              | None -> D.top, arc
              | Some v -> v, arc) hd.node_in
        in
        let treat_instr (v, {arc_inst; _}) = match arc_inst with
          | CFG_skip _ -> v
          | CFG_assign (var, e) -> D.assign v var e
          | CFG_guard e ->
            Format.printf "guard %d: %a, %a\n" hd.node_id D.pp v D.pp (D.guard v e);
            D.guard v e
          | CFG_assert (e, _) ->
            D.guard v e
          | CFG_call f ->
            let m = match FuncHash.find_opt memo_funcs f with
              | None -> DMap.empty
              | Some m -> m
            in match DMap.find_opt v m with
            | Some v' -> v'
            | None ->
              let m' = loop (NodeMap.singleton f.func_entry v)
                  (List.map (fun {arc_dst; _} -> arc_dst) f.func_entry.node_out)
              in
              let v' = NodeMap.find f.func_exit m' in
              FuncHash.replace memo_funcs f (DMap.add v v' m);
              v'
        in
        let vals = List.map treat_instr vals in
        let v = List.fold_left
            (if Hashtbl.mem widening_points hd then D.widen else D.join)
            D.bottom
            vals
        in let tl =
          if NodeMap.find_opt hd map = Some v
          then tl
          else out_nodes hd @ tl
        in
        loop (NodeMap.add hd v map) tl
    in
    let m = loop (NodeMap.singleton cfg.cfg_init_entry D.init)
      (out_nodes cfg.cfg_init_entry)
    in
    let rec search_main = function
      | [] -> failwith "file has no main function"
      | {func_name; func_entry; _} :: _ when String.starts_with ~prefix:"main" func_name ->
        let m = NodeMap.add func_entry (NodeMap.find cfg.cfg_init_exit m) m in
        loop m (out_nodes func_entry)
      | _ :: tl -> search_main tl
    in search_main cfg.cfg_funcs
end

let iterate cfg =
  let module D = Domains.Non_relational.NonRelational(struct let support = cfg.cfg_vars end)(Domains.Interval.Interval) in
  let module I = Iterator(D) in
  let map = I.iter cfg in
  let _ = Random.self_init () in
  let check_assertation {arc_inst; arc_src; _} = match arc_inst with
    | CFG_assert (e, pos) ->
      let v = NodeMap.find arc_src map in
      if not D.(is_bottom @@
                guard v (CFG_bool_unary (AbstractSyntax.AST_NOT, e))) then
        assertion_failed e pos;
    | _ -> ()
  in
  List.iter check_assertation cfg.cfg_arcs;
  let iter_node node : unit = Format.printf "<%i>: %a@ " node.node_id D.pp (NodeMap.find node map) in
  Format.printf "Node Values:@   @[<v 0>" ;
  List.iter iter_node cfg.cfg_nodes ;
  Format.printf "@]"
