open Frontend
open AbstractSyntax
type cong = Bot | Cong of Z.t * Z.t

module Congruence : (ValueDomain.VALUE_DOMAIN with type t = cong) = struct
  type t = cong

  let bottom = Bot

  let top = Cong (Z.one, Z.zero)

  let is_bottom = (=) Bot

  let const n = Cong (Z.zero, n)

  let rand n n' = if n = n' then const n else top

  let leq v v' = match v, v' with
    | Bot, _ -> true
    | _, Bot -> false
    | Cong (a, b), Cong (a', b') ->
      if a' = Z.zero then
        Z.(a = zero && b = b')
      else
        Z.(rem a a' = zero && rem (b - b') a' = zero)

  let meet v v' = match v, v' with
    | Bot, _ | _, Bot -> Bot
    | Cong (a, b), Cong (a', b') when a = Z.zero && a' = Z.zero ->
      if b <> b' then bottom else v
    | Cong (a, b), Cong (a', b') when a = Z.zero ->
      if (Z.(rem (b - b') a' = zero)) then v else bottom
    | Cong (a', b'), Cong (a, b) when a = Z.zero ->
      if (Z.(rem (b - b') a' = zero)) then v' else bottom
    | Cong (a, b), Cong (a', b') ->
      let p, s, t = Z.gcdext a a' in
      if Z.(rem (b - b') p = zero) then
        Cong (Z.lcm a a', Z.((b * a' * s + b' * a * t) / p))
      else Bot

  let join v v' = match v, v' with
    | Bot, v | v, Bot -> v
    | Cong (a, b), Cong (a', b') ->
      Cong (Z.(gcd (gcd a a') (abs (b - b'))), b)

  let widen = join
  let narrow v v' =
    if is_bottom v' then bottom else v (* pas optimal mais on n'utilise pas de resserrement *)

  let pp fmt = function
    | Bot -> Format.fprintf fmt "⊥"
    | Cong (a, b) -> Format.fprintf fmt "%aℤ + %a" Z.pp_print a Z.pp_print b

  let unary v = function
    | AST_UNARY_PLUS -> v
    | AST_UNARY_MINUS ->
      match v with
      | Bot -> Bot
      | Cong (a, b) -> Cong (a, Z.neg b)

  let binary v v' op = match v, v' with
    | Bot, _ | _, Bot -> Bot
    | Cong (a, b), Cong (a', b') ->
      match op with
      | AST_PLUS -> Cong (Z.gcd a a', Z.(b + b'))
      | AST_MINUS -> Cong (Z.gcd a a', Z.(b - b'))
      | AST_MULTIPLY -> Cong (Z.(gcd (gcd (a * a') (a * b')) (a' * b)),
                              Z.(b * b'))
      | AST_DIVIDE ->
        if a' = Z.zero && b' = Z.zero
        then Bot
        else if a' = Z.zero && Z.rem a b' = Z.zero && Z.rem b b' = Z.zero
        then Cong (Z.(a / abs b'), Z.(b / b'))
        else top
      | AST_MODULO ->
        if a' = Z.zero && b' = Z.zero
        then Bot
        else if a' = Z.zero && Z.rem a b' = Z.zero then
          if Z.rem b b' = Z.zero then
            const Z.zero
              else
          Cong (b', Z.rem b b')
        else if a = Z.zero && b = Z.zero then
          const Z.zero
        else
          Cong (Z.(gcd (gcd a a') b'), b)

  let rec compare v v' op = match v, v' with
    | Bot, _ | _, Bot -> Bot, Bot
    | Cong (a, b), Cong (a', b') ->
      match op with
      | AST_EQUAL -> meet v v', meet v v'
      | AST_NOT_EQUAL ->
        if a = Z.zero && a' = Z.zero && b = b'
        then Bot, Bot
        else v, v'
      | AST_GREATER -> let x, y = compare v' v AST_LESS in y, x
      | AST_LESS ->
        if a = Z.zero && a' = Z.zero && Z.compare b b' >= 0
        then Bot, Bot
        else v, v'
      | AST_GREATER_EQUAL -> let x, y = compare v' v AST_LESS_EQUAL in y, x
      | AST_LESS_EQUAL ->
        if a = Z.zero && a' = Z.zero && Z.compare b b' > 0
        then Bot, Bot
        else v, v'

  let bwd_unary x op r =
    meet x (unary r op)

  let bwd_binary x y op r = match x, y with
    | Bot, _ | _, Bot -> Bot, Bot
    | Cong (a, b), Cong (a', b') ->
      match op with
      | AST_PLUS -> meet x (binary r y AST_MINUS), meet y (binary r x AST_MINUS)
      | AST_MINUS -> meet x (binary r y AST_PLUS), meet y (binary r x AST_PLUS)
      | AST_MULTIPLY ->
        let x' = if Z.rem b' a' = Z.zero && leq (const Z.zero) r then x else
          meet x (binary r y AST_DIVIDE)
        in let y' = if Z.rem b a = Z.zero && leq (const Z.zero) r then y else
               meet y (binary r x AST_DIVIDE)
        in x', y'
      | AST_DIVIDE ->
        if a' = Z.zero && b' = Z.zero then Bot, Bot else
          begin match r with
            | Bot -> Bot, Bot
            | Cong (_, _) -> x, y
          end
      | AST_MODULO ->
        if a' = Z.zero && b' = Z.zero then Bot, Bot else
          match r with
          | Bot -> Bot, Bot
          | Cong (c, d) ->
            if c = Z.zero && a' = Z.zero then
              meet x (Cong (b', d)), y
            else
              x, y
end
