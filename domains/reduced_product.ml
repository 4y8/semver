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
end
