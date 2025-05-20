open Frontend
open AbstractSyntax

module ISet = Set.Make(Z)

let (<<=) n n' = Z.compare n n' <= 0
let (<<) n n' = Z.compare n n' < 0

module Interval : ValueDomain.VALUE_DOMAIN = struct
  type t = Top | MInf of Z.t | PInf of Z.t | Fin of Z.t * Z.t | Bot
  let top = Top
  let bottom = Bot
  let abs s =
    Fin (ISet.min_elt s, ISet.max_elt s)
  let const z = Fin (z, z)
  let fin (n, n') = if n <<= n' then Fin (n, n') else Bot
  let rand a b = fin (a, b)
  let unary v = function
    | AST_UNARY_PLUS -> v
    | AST_UNARY_MINUS ->
      match v with
      | Fin (a, b) -> Fin (Z.neg b, Z.neg a)
      | MInf a -> PInf (Z.neg a)
      | PInf a -> MInf (Z.neg a)
      | Top -> Top
      | Bot -> Bot
    
  let plus n n' = match n, n' with
    | Top, _ | _, Top -> Top
    | Fin (a, b), Fin (a', b') -> Fin (Z.add a a', Z.add b b')
    | MInf _, PInf _ | PInf _, MInf _ -> Top
    | MInf n, MInf n'
    | MInf n, Fin (_, n')
    | Fin (_, n'), MInf n -> MInf (Z.add n n')
    | PInf n, PInf n'
    | PInf n, Fin (_, n')
    | Fin (_, n'), PInf n -> PInf (Z.add n n')
    | Bot, _ | _, Bot -> Bot

  let minus n n' = plus n (unary n' AST_UNARY_MINUS)

  let binary n n' = function
    | AST_PLUS -> plus n n'
    | AST_MINUS -> minus n n'
    | _ -> failwith "todo binary"

  let join n n' = match n, n' with
    | Top, _ | _, Top -> Top
    | Fin (a, b), Fin (a', b') -> Fin (Z.min a a', Z.max b b')
    | MInf _, PInf _ | PInf _, MInf _ -> Top
    | MInf n, MInf n'
    | MInf n, Fin (_, n')
    | Fin (_, n'), MInf n -> MInf (Z.max n n')
    | PInf n, PInf n'
    | PInf n, Fin (_, n')
    | Fin (_, n'), PInf n -> PInf (Z.min n n')
    | Bot, n | n, Bot -> n

  let meet n n' = match n, n' with
    | Top, n | n, Top -> n
    | Fin (a, b), Fin (a', b') ->
      let c = Z.max a a' in
      let d = Z.min b b' in
      fin (c, d)
    | MInf n, PInf n' | PInf n', MInf n
    | MInf n, Fin (n', _) | Fin (n', _), MInf n
    | PInf n', Fin (_, n) | Fin (_, n), PInf n'-> fin (n', n)
    | MInf n, MInf n' -> MInf Z.(min n n')
    | PInf n, PInf n' -> PInf Z.(max n n')
    | Bot, _ | _, Bot -> Bot

  let rec compare n n' = function
    | AST_EQUAL -> let e = meet n n' in e, e
    | AST_NOT_EQUAL ->
      begin match n, n' with
        | Bot, _ | _, Bot -> Bot, Bot
        | Fin (a, b), Fin (c, d) when a = b && b = c && c = d -> Bot, Bot
        | n, n' -> n, n'
      end
    | AST_GREATER_EQUAL
    | AST_GREATER ->
      let n', n = compare n' n AST_LESS in
      n, n'
    | AST_LESS | AST_LESS_EQUAL ->
      let l = match n' with
        | Bot -> Bot
        | PInf _
        | Top -> Top
        | MInf a | Fin (_, a) -> MInf a
      in
      let r = match n with
        | Bot -> Bot
        | MInf _
        | Top -> Top
        | PInf a | Fin (a, _) -> PInf a
      in
      meet l n, meet r n'

  let bwd_unary v op r = 
    meet v (unary r op)

  let bwd_binary x y op r = match op with
    | AST_PLUS -> meet x (binary r y AST_MINUS), meet y (binary r x AST_MINUS)
    | AST_MINUS -> meet x (binary r y AST_PLUS), meet y (binary r x AST_PLUS)
    | _ -> failwith "todo bwd_binary"

  let leq i i' = match i, i' with
    | _, Top | Bot, _ -> true
    | _, Bot | Top, _ -> i = i'
    | Fin (_, n), MInf n'
    | MInf n, MInf n' -> Z.compare n n' <= 0
    | Fin (n, _), PInf n'
    | PInf n, PInf n' -> Z.compare n n' >= 0
    | MInf _, PInf _ | PInf _, MInf _
    | MInf _, Fin (_, _) | PInf _, Fin (_, _) -> false
    | Fin (a, b), Fin (a', b') ->
      Z.compare a a' >= 0 && Z.compare b b' <= 0

  let widen i i' = match i, i' with
    | Bot, i | i, Bot -> i
    | Top, _ | _, Top -> Top
    | PInf _, MInf _
    | MInf _, PInf _ -> Top
    | MInf n, MInf n'
    | Fin (_, n), MInf n'
    | MInf n, Fin (_, n') ->
      if n << n' then Top
      else MInf n
    | PInf n, PInf n'
    | Fin (n, _), PInf n'
    | PInf n, Fin (n', _) ->
      if n <<= n' then PInf n
      else Top
    | Fin (n, m), Fin (n', m') ->
      if n <<= n' then
        if m << m' then
          PInf n
        else
          Fin (n, m)
      else if m << m' then
        Top
      else MInf m

  let narrow i i' = match i, i' with
    | Bot, _ | _, Bot -> Bot
    | Top, i | i, Top -> i
    | MInf n, MInf _ -> MInf n
    | MInf n, Fin (n', _) -> fin (n', n)
    | PInf n, PInf _ -> PInf n
    | PInf n, Fin (_, n') -> fin (n, n')
    | Fin (n, n'), _ -> fin (n, n')
    | MInf n, PInf n' -> fin (n', n)
    | PInf n, MInf n' -> fin (n, n')

  let is_bottom = (=) Bot
  let pp fmt = function
    | Top -> Format.fprintf fmt "⊤"
    | Bot -> Format.fprintf fmt "⊥"
    | MInf n -> Format.fprintf fmt "]-∞;%a]" Z.pp_print n
    | PInf n -> Format.fprintf fmt "[%a;+[∞" Z.pp_print n
    | Fin (a, b) -> Format.fprintf fmt "[%a;%a]" Z.pp_print a Z.pp_print b
end
