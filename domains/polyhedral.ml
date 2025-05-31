open Frontend
open AbstractSyntax
open Apron
open ControlFlowGraph

module Polyhedral (V : Domain.VARS) () : Domain.DOMAIN = struct
  type t = Polka.loose Polka.t Abstract1.t

  (* we transit by strings to avoid losing precision because of machine integers
  ; a more optimal solution would be to directly look at the C representations
  to make the translation *)
  let mpq_of_z n =
    Mpq.of_mpz (Mpz.of_string (Z.to_string n))

  let manager = Polka.manager_alloc_loose ()

  let apron_var_of_var {var_id; _} =
    Apron.Var.of_string @@ "x_" ^  string_of_int var_id

  let vars =
    List.map apron_var_of_var V.support |> Array.of_list

  let env =
    Environment.make vars [||]

  let init =
    let v = Abstract1.top manager env in
    let zeros =
      Array.map (fun _ -> Texpr1.(of_expr env (Cst (Coeff.s_of_int 0)))) vars in
    Abstract1.assign_texpr_array manager v vars zeros None

  let bottom = Abstract1.bottom manager env

  let top = Abstract1.top manager env

  let is_bottom = Abstract1.is_bottom manager

  let leq = Abstract1.is_leq manager

  let join = Abstract1.join manager

  let meet = Abstract1.meet manager

  let widen = Abstract1.widening manager

  (* really not precise but we don't use narrowing *)
  let narrow t t' = t

  let rec expr1_of_int_expr = function
    | CFG_int_var v ->
      Texpr1.Var (apron_var_of_var v)
    | CFG_int_const n ->
      Texpr1.Cst (Coeff.s_of_mpq (mpq_of_z n))
    | CFG_int_rand (a, b) ->
      Texpr1.Cst (Coeff.i_of_mpq (mpq_of_z a) (mpq_of_z b))
    | CFG_int_unary (AST_UNARY_PLUS, e) ->
      expr1_of_int_expr e
    | CFG_int_unary (AST_UNARY_MINUS, e) ->
      Texpr1.(Unop (Neg, expr1_of_int_expr e, Int, Zero))
    | CFG_int_binary (AST_PLUS, e, e') ->
      Texpr1.(Binop (Add, expr1_of_int_expr e, expr1_of_int_expr e', Int, Zero))
    | CFG_int_binary (AST_MINUS, e, e') ->
      Texpr1.(Binop (Sub, expr1_of_int_expr e, expr1_of_int_expr e', Int, Zero))
    | CFG_int_binary (AST_MULTIPLY, e, e') ->
      Texpr1.(Binop (Mul, expr1_of_int_expr e, expr1_of_int_expr e', Int, Zero))
    | CFG_int_binary (AST_DIVIDE, e, e') ->
      Texpr1.(Binop (Div, expr1_of_int_expr e, expr1_of_int_expr e', Int, Zero))
    | CFG_int_binary (AST_MODULO, e, e') ->
      Texpr1.(Binop (Mod, expr1_of_int_expr e, expr1_of_int_expr e', Int, Zero))

  let guard x e =
    (* add the constraints described by an expression to acc ; we don't
    calculate the constraints alone because, as we approximate, we don't have
    the commutativity/associativity of meet *)
    let rec build_polyhedron acc = function
      | CFG_bool_rand -> acc
      | CFG_bool_const true -> acc
      | CFG_bool_const false -> bottom
      | CFG_bool_unary (AST_NOT, e) ->
        build_polyhedron acc (elim_not e)
      | CFG_bool_binary (AST_AND, e, e') ->
        build_polyhedron (build_polyhedron acc e) e'
      | CFG_bool_binary (AST_OR, e, e') ->
        join (build_polyhedron acc e) (build_polyhedron acc e')
      | CFG_compare (AST_LESS, e, e') ->
        build_polyhedron acc (CFG_compare (AST_GREATER, e', e))
      | CFG_compare (AST_LESS_EQUAL, e, e') ->
        build_polyhedron acc (CFG_compare (AST_GREATER_EQUAL, e', e))
      | CFG_compare (AST_NOT_EQUAL, e, e') ->
        build_polyhedron acc @@
        CFG_bool_binary (AST_OR, CFG_compare(AST_GREATER, e, e'),
                         CFG_compare(AST_GREATER, e', e))
      | CFG_compare (AST_GREATER | AST_GREATER_EQUAL | AST_EQUAL as op, e, e') ->
        let e = expr1_of_int_expr (CFG_int_binary (AST_MINUS, e, e')) in
        let a = Tcons1.array_make env 1 in
        let op = match op with
          | AST_GREATER -> Tcons1.SUP
          | AST_GREATER_EQUAL -> Tcons1.SUPEQ
          | AST_EQUAL -> Tcons1.EQ
          | AST_NOT_EQUAL -> Tcons1.DISEQ
          | _ -> failwith "impossible"
        in
        Tcons1.array_set a 0 Tcons1.(make (Texpr1.of_expr env e) op);
        Abstract1.meet_tcons_array manager acc a
    in
    build_polyhedron x e

  let assign x v e =
    let e = Texpr1.of_expr env (expr1_of_int_expr e) in
    Abstract1.assign_texpr manager x (apron_var_of_var v) e None

  (* we didn't implement backward assignment yet *)
  let bwd_assign x v e r = x

  let pp = Abstract1.print
end
