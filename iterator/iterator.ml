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
  let iter cfg =
    let widening_points = Hashtbl.create 4096 in
    dfs (Hashtbl.create 4096) widening_points cfg.cfg_init_entry;
    List.iter (fun {func_entry; _} ->
        dfs (Hashtbl.create 4096) widening_points func_entry) cfg.cfg_funcs;
    let rec loop map = function
      | [] -> map
      | hd :: tl ->
        let vals =
          List.map (fun arc ->
              match NodeMap.find_opt arc.arc_src map with
              | None -> D.top, arc
              | Some v -> v, arc) hd.node_in
        in
        let memo_funcs = FuncHash.create 4096 in
        let treat_instr (v, {arc_inst; _}) = match arc_inst with
          | CFG_skip _ -> v
          | CFG_assign (var, e) -> D.assign v var e
          | CFG_guard e -> D.guard v e
          | CFG_assert (e, pos) ->
            if not D.(is_bottom @@
                      guard v (CFG_bool_unary (AbstractSyntax.AST_NOT, e))) then
              assertion_failed e pos;
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
          else List.map (fun {arc_dst; _} -> arc_dst) hd.node_out @ tl
        in
        loop (NodeMap.add hd v map) tl
    in
    
end

let iterate cfg =
  let _ = Random.self_init () in
  let iter_arc arc : unit = match arc.arc_inst with _ -> failwith "TODO" in
  let iter_node node : unit = Format.printf "<%i>: ⊤@ " node.node_id in
  List.iter iter_arc cfg.cfg_arcs ;
  Format.printf "Node Values:@   @[<v 0>" ;
  List.iter iter_node cfg.cfg_nodes ;
  Format.printf "@]"
