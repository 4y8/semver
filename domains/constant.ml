open Frontend
open AbstractSyntax

let (<<) n n' = Z.compare n n' < 0
let (<<=) n n' = Z.compare n n' <= 0

module Constant : ValueDomain.VALUE_DOMAIN = struct
  type t = Cst of Z.t | Top | Bot

  let top = Top
  let bottom = Bot
  let const n = Cst n

  let is_bottom = (=) Bot

  let pp fmt = function
    | Top -> Format.fprintf fmt "⊤"
    | Bot -> Format.fprintf fmt "⊥"
    | Cst n -> Format.fprintf fmt "%a" Z.pp_print n

  let rand a b =
    if a << b then Top
    else if a = b then Cst a
    else Bot

  let unary v op =
    if op = AST_UNARY_MINUS then
      match v with
      | Cst n -> Cst (Z.neg n)
      | v -> v
    else v

  let binary v v' op =
    if (op = AST_MULTIPLY && (v = Cst Z.zero || v' = Cst Z.zero)) ||
       (op = AST_DIVIDE && v = Cst Z.zero)
    then Cst Z.zero
    else if op = AST_DIVIDE && v' = Cst Z.zero
    then Bot
    else
      match v, v' with
      | Top, _ | _, Top -> Top
      | Bot, _ | _, Bot -> Bot
      | Cst n, Cst n' ->
        match op with
        | AST_PLUS -> Cst Z.(add n n')
        | AST_MINUS -> Cst Z.(sub n n')
        | AST_MULTIPLY -> Cst Z.(mul n n')
        | AST_DIVIDE -> Cst Z.(div n n')
        | AST_MODULO -> Cst Z.(rem n n')

  let meet v v' = match v, v' with
    | Top, v | v, Top -> v
    | Bot, _ | _, Bot -> Bot
    | Cst a, Cst b ->
      if a = b then v else Bot

  let join v v' = match v, v' with
    | Top, _ | _, Top -> Top
    | Bot, v | v, Bot -> v
    | Cst a, Cst b ->
      if a = b then v else Top

  (* le treillis est de hauteur finie *)
  let narrow = meet
  let widen = join

  let leq v v' = match v, v' with
    | Bot, _ -> true
    | _, Top -> true
    | Cst a, Cst b -> a = b
    | _, Bot -> false
    | Top, _ -> false

  let rec compare v v' = function
    | AST_EQUAL -> let e = meet v v' in e, e
    | AST_NOT_EQUAL ->
      begin match v, v' with
        | Bot, _ | _, Bot -> Bot, Bot
        | Top, v -> Top, v
        | v, Top -> v, Top
        | Cst a, Cst b ->
          if a = b then Bot, Bot else v, v'
      end
    | AST_LESS ->
      let x, y = compare v' v AST_GREATER in
      y, x
    | AST_GREATER ->
      begin match v, v' with
        | Bot, _ | _, Bot -> Bot, Bot
        | Top, v -> Top, v
        | v, Top -> v, Top
        | Cst a, Cst b -> if b << a then v, v' else Bot, Bot
      end
    | AST_LESS_EQUAL ->
      let x, y = compare v' v AST_GREATER_EQUAL in
      y, x
    | AST_GREATER_EQUAL ->
      begin match v, v' with
        | Bot, _ | _, Bot -> Bot, Bot
        | Top, v -> Top, v
        | v, Top -> v, Top
        | Cst a, Cst b -> if b <<= a then v, v' else Bot, Bot
      end

  let bwd_unary x op r =
    meet x (unary r op)

  let bwd_binary x y op r = match op with
    | AST_PLUS -> meet x (binary r y AST_MINUS), meet y (binary r x AST_MINUS)
    | AST_MINUS -> meet x (binary r y AST_PLUS), meet y (binary r x AST_PLUS)
    | AST_MULTIPLY ->
      let x' = if leq (const Z.zero) y && leq (const Z.zero) r then x else
          meet x (binary r y AST_DIVIDE)
      in let y' = if leq (const Z.zero) x && leq (const Z.zero) r then y else
             meet y (binary r x AST_DIVIDE)
      in x', y'
    | AST_DIVIDE ->
      if y = const Z.zero then
        Bot, Bot
      else begin match x, y, r with
        | Bot, _, _ | _, Bot, _ | _, _, Bot -> Bot, Bot
        | x, y, Top -> x, y
        | Top, Top, _ -> Top, Top
        | Cst a, Top, Cst b ->
          (* franchement pas optimal *)
          if Z.abs a << Z.abs b
          then Bot, Bot
          else Cst a, Top
        | Top, Cst a, Cst _ -> Top, Cst a
        | Cst a, Cst b, Cst c ->
          if Z. (div a b = c) then Cst a, Cst b else Bot, Bot
      end
    | AST_MODULO ->
      if y = const Z.zero then
        Bot, Bot
      else begin match x, y, r with
        | Bot, _, _ | _, Bot, _ | _, _, Bot -> Bot, Bot
        | x, y, Top -> x, y
        | Top, Top, _ -> Top, Top
        | Cst a, Top, Cst b ->
          if (Z.sign a >= 0 && Z.sign b < 0) ||
             (Z.sign a < 0 && Z.sign b >= 0)
          then Bot, Bot
          else Cst a, Top
        | Top, Cst a, Cst b ->
          if Z.abs a <<= Z.abs b
          then Bot, Bot
          else Top, Cst a
        | Cst a, Cst b, Cst c ->
          if Z.(rem a b) = c
          then Cst a, Cst b
          else Bot, Bot
      end
end
