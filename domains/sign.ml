open Frontend
open AbstractSyntax

type sign = { zero : bool ; pos : bool ; neg : bool }

module Signs : (ValueDomain.VALUE_DOMAIN with type t = sign) = struct
  type t = sign

  let pp fmt = function
    | { zero = false ; pos = false ; neg = false } -> Format.fprintf fmt "⊥"
    | { zero = true ; pos = false ; neg = false } -> Format.fprintf fmt "=0"
    | { zero = true ; pos = false ; neg = true } -> Format.fprintf fmt "≤0"
    | { zero = false ; pos = false ; neg = true } -> Format.fprintf fmt "<0"
    | { zero = false ; pos = true ; neg = true } -> Format.fprintf fmt "≠0"
    | { zero = true ; pos = true ; neg = false } -> Format.fprintf fmt "≥0"
    | { zero = false ; pos = true ; neg = false } -> Format.fprintf fmt ">0"
    | { zero = true ; pos = true ; neg = true } -> Format.fprintf fmt "⊤"


  let top  = { zero = true ; pos = true ; neg = true }
  let bottom = { zero = false ; pos = false ; neg = false }

  let const n = match Z.sign n with
    | 0 -> { bottom with zero = true }
    | 1 -> { bottom with pos = true }
    | -1 -> { bottom with neg = true }
    | _ -> failwith "impossible"

  let rand a b =
    if Z.compare a b > 0 then bottom else
    if Z.sign b <= 0 then
      let v = { bottom with neg = true } in
      if b = Z.zero then { v with zero = true }
      else v
    else if Z.sign a >= 0 then
      let v = { bottom with pos = true } in
      if b = Z.zero then { v with zero = true }
      else v
    else
      top

  let unary v = function
    | AST_UNARY_PLUS -> v
    | AST_UNARY_MINUS -> { zero = v.zero ; neg = v.pos ; pos = v.neg }

  let meet v v' =
    { zero = v.zero && v'.zero ; neg = v.neg && v'.neg ; pos = v.pos && v'.pos }

  let join v v' =
    { zero = v.zero || v'.zero ; neg = v.neg || v'.neg ; pos = v.pos || v'.pos }

  let is_bottom = (=) bottom

  let widen = join
  let narrow = meet

  let leq v v' =
    let impl b b' = b' || not b in
    impl v.zero v'.zero && impl v.pos v'.pos && impl v.neg v'.neg

  let rec binary v v' = function
    | AST_PLUS ->
      begin match v, v' with
        | { neg = true ; zero = true ; pos = true }, _
        | _, { neg = true ; zero = true ; pos = true } -> top
        | { neg = false ; zero = false ; pos = false }, _
        | _, { neg = false ; zero = false ; pos = false } -> bottom
        | { neg = false ; zero = true ; pos = false }, v
        | v, { neg = false ; zero = true ; pos = false } -> v
        | { pos = true ; _ }, { neg = true; _ }
        | { neg = true ; _ }, { pos = true; _ } -> top
        | { pos = true ; zero = b ; neg = false },
          { pos = true ; zero = b' ; neg = false } ->
          { pos = true ; zero = b || b' ; neg = false}
        | { pos = false ; zero = b ; neg = true },
          { pos = false ; zero = b' ; neg = true } ->
          { pos = false ; zero = b || b' ; neg = true }
      end
    | AST_MINUS ->
      binary v (unary v' AST_UNARY_MINUS) AST_PLUS
    | AST_MULTIPLY ->
      { pos = v.pos && v'.pos || v.neg && v'.neg
      ; zero = v.zero || v'.zero
      ; neg = v.pos && v'.neg || v.neg && v'.pos }
    | AST_DIVIDE ->
      if v' = const Z.zero then
        bottom
      else
        { pos = v.pos && v'.pos || v.neg && v'.neg
        ; zero = v.zero
        ; neg = v.pos && v'.neg || v.neg && v'.pos }
    | AST_MODULO ->
      if v' = const Z.zero then
        bottom
      else
        { v with zero = true }

  let rec compare v v' = function
    | AST_EQUAL -> meet v v', meet v v'
    | AST_NOT_EQUAL ->
      { v with zero = v.zero && v' <> const Z.zero },
      { v' with zero = v'.zero && v <> const Z.zero }
    | AST_GREATER_EQUAL -> let x, y = compare v' v AST_LESS_EQUAL in y, x
    | AST_LESS_EQUAL ->
      let x =
        if v'.pos then v
        else if v' = bottom then bottom
        else meet { v' with neg = true } v
      in let y =
           if v.neg then v'
           else if v = bottom then bottom
           else meet { v with pos = true } v'
      in x, y
    | AST_GREATER -> let x, y = compare v' v AST_GREATER in y, x
    | AST_LESS ->
      let x = match v' with
        | { pos = true ; _} -> v
        | { zero = true ; neg = false ; pos = false } ->
          meet v { zero = false ; neg = true ; pos = false }
        | { zero = false ; neg = false ; pos = false } ->
          bottom
        | v' -> meet v { v' with neg = true }
      in let y = match v' with
        | { neg = true ; _} -> v'
        | { zero = true ; neg = false ; pos = false } ->
          meet v' { zero = false ; neg = false ; pos = true }
        | { zero = false ; neg = false ; pos = false } ->
          bottom
        | v -> meet v' { v with pos = true }
      in x, y

  let bwd_unary v op r =
    meet v (unary r op)

  let bwd_binary x y op r = match op with
    | AST_PLUS -> meet x (binary r y AST_MINUS), meet y (binary r x AST_MINUS)
    | AST_MINUS -> meet x (binary r y AST_PLUS), meet y (binary r x AST_PLUS)
    | AST_MULTIPLY ->
      let x' = if y.zero && r.zero then x else
          meet x (binary r y AST_DIVIDE)
      in let y' = if x.zero && r.zero then y else
             meet y (binary r x AST_DIVIDE)
      in x', y'
    | AST_DIVIDE ->
      if y = const Z.zero then bottom, bottom else
        meet x (binary r y AST_MULTIPLY), meet y (binary x r AST_DIVIDE)
    | AST_MODULO ->
      meet x r, y
end
