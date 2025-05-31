open Frontend
open AbstractSyntax
open ControlFlowGraph

module IEMap = Map.Make(struct type t = int_expr let compare = compare end)

module NonRelational (V : Domain.VARS) (D : ValueDomain.VALUE_DOMAIN) :
  Domain.DOMAIN = struct
  type t = D.t VarMap.t

  let pp fmt m =
    Format.fprintf fmt "@[";
    VarMap.iter (fun k v -> Format.fprintf fmt "%s: %a;@ " k.var_name D.pp v) m;
    Format.fprintf fmt "@]"

  let init =
    VarMap.of_list (List.map (fun v -> v, D.const Z.zero) V.support)

  let bottom =
    VarMap.of_list (List.map (fun v -> v, D.bottom) V.support)

  let top =
    VarMap.of_list (List.map (fun v -> v, D.top) V.support)

  let rec eval env e =
    let v, m = match e with
      | CFG_int_unary (op, e) ->
        let v, m = eval env e in
        D.unary v op, m
      | CFG_int_binary (op, e, e') ->
        let v, m = eval env e in
        let v', m' = eval env e' in
        D.binary v v' op,
        IEMap.merge (fun _ o o' -> if o = None then o' else o) m m'
      | CFG_int_var v -> VarMap.find v env, IEMap.empty
      | CFG_int_const n -> D.const n, IEMap.empty
      | CFG_int_rand (a, b) -> D.rand a b, IEMap.empty
    in
    v, IEMap.add e v m

  let assign env var e =
    let v, _ = eval env e in
    if v = D.bottom then
      bottom
    else
      VarMap.add var v env

  exception Bottom

  let meet m m' =
    try
      VarMap.merge
        (fun _ e e' -> match e, e' with
           | None, v | v, None -> v
           | Some v, Some v' ->
             let m = D.meet v v' in
             if D.is_bottom m then raise Bottom else Some m)
        m m'
    with
      Bottom -> bottom

  let join = VarMap.merge
      (fun _ e e' -> match e, e' with
         | None, v | v, None -> v
         | Some v, Some v' -> Some (D.join v v'))

  let rec bwd_expr env m r = function
    | CFG_int_const n ->
      if D.(leq (const n) r)
      then VarMap.empty
      else bottom
    | CFG_int_rand (a, b) ->
      if D.(is_bottom @@ meet (rand a b) r)
      then bottom
      else VarMap.empty
    | CFG_int_var v ->
      VarMap.singleton v (D.meet r VarMap.(find v env))
    | CFG_int_unary (op, e) ->
      bwd_expr env m D.(bwd_unary (IEMap.find e m) op r) e
    | CFG_int_binary (op, e, e') ->
      let r, r' = D.bwd_binary (IEMap.find e m) (IEMap.find e' m) op r in
      meet (bwd_expr env m r e) (bwd_expr env m r' e')

  let rec guard env = function
    | CFG_bool_const true -> env
    | CFG_bool_const false -> bottom
    | CFG_bool_rand -> env
    | CFG_bool_unary (AST_NOT, e) -> guard env (elim_not e)
    | CFG_bool_binary (AST_AND, e, e') -> meet (guard env e) (guard env e')
    | CFG_bool_binary (AST_OR, e, e') -> join (guard env e) (guard env e')
    | CFG_compare (op, e, e') ->
      let v, m = eval env e in
      let v', m' = eval env e' in
      let m = IEMap.merge (fun _ o o' -> if o = None then o' else o) m m' in
      let r, r' = D.compare v v' op in
      meet env (meet (bwd_expr env m r e) (bwd_expr env m r' e'))

  let widen = VarMap.merge (fun _ o o' -> match o, o' with
      | None, o | o, None -> o
      | Some v, Some v' -> Some (D.widen v v'))

  let narrow m m' = try
      VarMap.merge (fun _ o o' -> match o, o' with
          | None, o | o, None -> o
          | Some v, Some v' -> let v'' = D.narrow v v' in
            if D.is_bottom v'' then raise Bottom else Some v'') m m'
    with
    | Bottom -> bottom

  let leq m m' = VarMap.for_all (fun var v -> D.leq v (VarMap.find var m')) m

  let bwd_assign x v e r =
    let x' = try
        VarMap.merge (fun v' o o' -> match o, o' with
            | o, _ when v' = v -> o
            | None, o | o, None -> failwith "impossible"
            | Some v, Some v' -> let v = D.meet v v' in
              if D.is_bottom v then raise Bottom
              else Some v) x r
      with
        Bottom -> bottom
    in
    let _, m = eval x' e in
    bwd_expr x' m (VarMap.find v r) e

  let is_bottom m = leq m bottom
end
