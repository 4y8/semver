open Frontend
open AbstractSyntax

let (<<=) n n' = Z.compare n n' <= 0
let (<<) n n' = Z.compare n n' < 0

module Interval : ValueDomain.VALUE_DOMAIN = struct
  type t = Top | MInf of Z.t | PInf of Z.t | Fin of Z.t * Z.t | Bot
  let top = Top
  let bottom = Bot
  let const z = Fin (z, z)
  let fin (n, n') = if n <<= n' then Fin (n, n') else Bot
  let rand a b = fin (a, b)

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

  let abs_val = function
    | Fin (a, b) ->
      let m = Z.(max (abs a) (abs b)) in
      Fin (Z.neg m, m)
    | Bot -> Bot
    | MInf _ | PInf _ | Top -> Top

  let sign = function
    | Bot -> Bot
    | Top -> Top
    | Fin (a, b) when b <<= Z.zero -> MInf Z.zero
    | Fin (a, b) when Z.zero <<= a -> PInf Z.zero
    | Fin (_, _) -> Top
    | PInf n when n << Z.zero -> Top
    | MInf n when Z.zero << n -> Top
    | PInf _ -> PInf Z.zero
    | MInf _ -> MInf Z.zero

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

  let rec mult n n' = match n, n' with
    | Bot, _ | _, Bot -> Bot
    | Top, n | n, Top ->
      if n = const Z.zero then const Z.zero else Top
    | MInf _, PInf _ | PInf _, MInf _ -> Top
    | MInf n, Fin (a, b)
    | Fin (a, b), MInf n ->
      mult (Fin (Z.neg b, Z.neg a)) (PInf (Z.neg n))
    | Fin (a, b), Fin (c, d) ->
      let p1 = Z.mul a c in
      let p2 = Z.mul a d in
      let p3 = Z.mul b c in
      let p4 = Z.mul b d in
      fin (Z.(min (min p1 p2) (min p3 p4)), Z.(max (max p1 p2) (max p3 p4)))
    | PInf n, Fin (a, b)
    | Fin (a, b), PInf n ->
      if a = Z.zero && b = Z.zero then
        const Z.zero
      else if b << Z.zero then
        MInf (Z.(max (mul a n) (mul b n)))
      else if a << Z.zero then
        Top
      else
        PInf (Z.(min (mul a n) (mul b n)))
    | MInf n, MInf n' -> mult (PInf (Z.neg n)) (PInf (Z.neg n'))
    | PInf n, PInf n' ->
      if Z.zero << n && Z.zero << n' then
        PInf (Z.mul n n')
      else Top

  let rec div n n' =
    if n' = const Z.zero then Bot
    else match n, n' with
      | Bot, _ | _, Bot -> Bot
      | Top, n ->
        Top
      | MInf n, Fin (a, b) ->
        div (PInf (Z.neg n)) (Fin (Z.neg b, Z.neg a))
      | PInf c, Fin (a, b) ->
        if Z.zero << a then
          PInf (Z.(min (div c a) (div c b)))
        else if b << Z.zero then
          MInf (Z.(max (div c a) (div c b)))
        else
          join (div n (meet n' (PInf Z.one)))
            (div n (meet n' (MInf Z.minus_one)))
      | PInf a, MInf b ->
        if Z.zero << b then Top
        else MInf Z.zero
      | MInf a, PInf b ->
        div (PInf (Z.neg a)) (MInf (Z.neg b))
      | Fin (a, b), Top ->
        let m = Z.(max (abs a) (abs b)) in
        fin (Z.neg m, m)
      | MInf _, Top
      | PInf _, Top -> Top
      | MInf a, MInf b ->
        div (PInf (Z.neg a)) (PInf (Z.neg b))
      | PInf a, PInf b ->
        if b << Z.zero then Top
        else
          PInf Z.zero
      | Fin (a, b), Fin (c, d) ->
        if Z.zero << c then
          fin (Z.(min (div a c) (div a d)), Z.(max (div b c) (div b d)))
        else if d << Z.zero then
          fin (Z.(min (div b c) (div b d)), Z.(max (div a c) (div a d)))
        else
          join (div n (meet n' (PInf Z.one)))
            (div n (meet n' (MInf Z.minus_one)))
      | Fin (a, b), MInf c ->
        if c << Z.zero then
          fin (Z.(min zero (div b c)), Z.(max zero (div a c)))
        else
          join (div n (meet n' (PInf Z.one)))
            (div n (meet n' (MInf Z.minus_one)))
      | Fin (a, b), PInf c ->
        unary (div n (MInf (Z.neg c))) AST_UNARY_MINUS

  let modulo n n' =
    meet (meet (minus n (mult n' (div n n'))) (abs_val n'))
      (meet (sign n) (abs_val n'))

  let binary n n' = function
    | AST_PLUS -> plus n n'
    | AST_MINUS -> minus n n'
    | AST_MULTIPLY -> mult n n'
    | AST_DIVIDE -> div n n'
    | AST_MODULO -> modulo n n'

  let rec compare n n' = function
    | AST_EQUAL -> let e = meet n n' in e, e
    | AST_NOT_EQUAL ->
      begin match n, n' with
        | Bot, _ | _, Bot -> Bot, Bot
        | Fin (a, b), Fin (c, d) when a = b && b = c && c = d -> Bot, Bot
        | n, n' -> n, n'
      end
    | AST_GREATER ->
      let n', n = compare n' n AST_LESS in
      n, n'
    | AST_GREATER_EQUAL ->
      let n', n = compare n' n AST_LESS_EQUAL in
      n, n'
    | AST_LESS_EQUAL ->
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
    | AST_LESS ->
      let l = match n' with
        | Bot -> Bot
        | PInf _ | Top -> Top
        | MInf a | Fin (_, a) -> MInf (Z.add Z.minus_one a)
      in
      let r = match n with
        | Bot -> Bot
        | MInf _ | Top -> Top
        | PInf a | Fin (a, _) -> PInf (Z.add Z.one a)
      in
      meet l n, meet r n'

  let bwd_unary v op r =
    meet v (unary r op)

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
      if y = const Z.zero then Bot, Bot else
        (* on prend en compte les arrondis *)
        let r = binary r (rand Z.minus_one Z.one) AST_PLUS in
        meet x (binary r y AST_MULTIPLY), meet y (binary x r AST_DIVIDE)
    | AST_MODULO ->
      meet x (sign r), y

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
