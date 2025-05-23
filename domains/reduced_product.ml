module Interval : ValueDomain.VALUE_DOMAIN = struct
  type t = Sign.sign * Congruence.cong * Interval.inter

  module S = Sign.Signs
  module I = Interval.Interval
  module C = Congruence.Congruence

  let top = S.top, C.top, I.top
  let bottom = S.bottom, C.bottom, I.bottom

  let pp fmt (s, c, i) =
    Format.fprintf fmt "%a × %a × %a" S.pp s C.pp c I.pp i

  let const n =
    S.const n, C.const n, I.const n

  let rand a b =
    S.rand a b, C.rand a b, I.rand a b

  let rho_step (Sign.{pos ; neg ; zero}, c, i) =
    match c with
    | Congruence.Bot -> bottom
    | Congruence.Cong (a, b) ->
      let s =
        Sign.{
          pos = not I.(is_bottom @@ meet (Interval.PInf Z.one) i) && pos &&
                (a <> Z.zero || Z.sign b > 0)
        ; neg = not I.(is_bottom @@ meet (Interval.MInf Z.minus_one) i) &&
                neg && (a <> Z.zero || Z.sign b < 0)
        ; zero = I.(leq (const Z.zero) i) && zero && b = Z.zero }
      in
      let i = match s with
        | { zero = true  ; neg = true  ; pos = true  } ->
          i
        | { zero = true  ; neg = true  ; pos = false } ->
          I.(meet i (Interval.MInf Z.zero))
        | { zero = true  ; neg = false ; pos = true  } ->
          I.(meet i (Interval.PInf Z.zero))
        | { zero = true  ; neg = false ; pos = false } ->
          I.(meet i (const Z.zero))
        | { zero = false ; neg = true  ; pos = false } ->
          I.(meet i (Interval.MInf Z.minus_one))
        | { zero = false ; neg = false ; pos = true  } ->
          I.(meet i (Interval.PInf Z.one))
        | { zero = false ; neg = true  ; pos = true  } ->
          if I.(leq i (Interval.PInf Z.zero))then
            I.(meet i (Interval.PInf Z.one))
          else if I.(leq i (Interval.MInf Z.zero)) then
            I.(meet i (Interval.MInf Z.minus_one))
          else
            i
        | { zero = false ; neg = false ; pos = false } ->
          I.bottom
      in
      let c, i = if a = Z.zero then c, I.(meet (const b) i) else
          match i with
          | Interval.Bot -> Congruence.Bot, Interval.Bot
          | Interval.Top ->
            c, i
          | Interval.MInf n ->
            let rn = Z.erem n a in
            let rb = Z.erem b a in
            let n' =
              if Z.leq rb rn
              then Z.(n - rn + rb)
              else Z.(n - rn + rb - b)
            in
            c, Interval.MInf n'
          | Interval.PInf n ->
            let rn = Z.erem n a in
            let rb = Z.erem b a in
            let n' =
              if Z.leq rb rn
              then Z.(n - rn + rb + b)
              else Z.(n - rn + rb)
            in
            c, Interval.PInf n'
          | Interval.Fin (n, m) ->
            let rn = Z.erem n a in
            let rm = Z.erem m a in
            let rb = Z.erem b a in
            let n' =
              if Z.leq rb rn
              then Z.(n - rn + rb + b)
              else Z.(n - rn + rb)
            in
            let m' =
              if Z.leq rb rm
              then Z.(m - rm + rb)
              else Z.(m - rm + rb - b)
            in
            if Z.(n' > m') then
              C.bottom, I.bottom
            else if n' = m' then
              C.const n', I.const n'
            else
              c, I.rand n' m'
      in
      (s, c, i)

  let rec rho v =
    let (s, c, i) as v' = rho_step v in
    if S.is_bottom s || C.is_bottom c || I.is_bottom i then
      bottom
    else if v = v' then
      v'
    else
      rho v'

  let apply_op_then_rho fs fc fi =
    fun (s, c, i) (s', c', i') ->
    rho (fs s s', fc c c', fi i i')

  let apply_op_then_rho2 fs fc fi =
    fun (s, c, i) (s', c', i') ->
    let s, s' = fs s s' in
    let c, c' = fc c c' in
    let i, i' = fi i i' in
    rho (s, c, i), rho (s', c', i')

  let join =
    apply_op_then_rho S.join C.join I.join

  let meet =
    apply_op_then_rho S.meet C.meet I.meet

  let widen (s, c, i) (s', c', i') =
    (S.widen s s', C.widen c c', I.widen i i')

  let narrow (s, c, i) (s', c', i') =
    (S.narrow s s', C.narrow c c', I.narrow i i')

  let unary (s, c, i) op =
    rho (S.unary s op, C.unary c op, I.unary i op)

  let binary v v' op =
    let app_op_end f x y = f x y op in
    apply_op_then_rho (app_op_end S.binary) (app_op_end C.binary)
      (app_op_end I.binary) v v'

  let compare v v' op =
    let app_op_end f x y = f x y op in
    apply_op_then_rho2 (app_op_end S.compare) (app_op_end C.compare)
      (app_op_end I.compare) v v'

  let bwd_unary x op r =
    let app_op_mid f x y = f x op y in
    apply_op_then_rho (app_op_mid S.bwd_unary) (app_op_mid C.bwd_unary)
      (app_op_mid I.bwd_unary) x r

  let bwd_binary x y op (rs, rc, ri) =
    apply_op_then_rho2 (fun x y -> S.bwd_binary x y op rs)
      (fun x y -> C.bwd_binary x y op rc)
      (fun x y -> I.bwd_binary x y op ri) x y

  let is_bottom v =
    let s, c, i = rho v in
    S.is_bottom s && C.is_bottom c && I.is_bottom i

  let leq (s, c, i) (s', c', i') =
    S.leq s s' && C.leq c c' && I.leq i i'
end
