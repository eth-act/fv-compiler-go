/-!
# Go's `%g` for `float64`

`fmt.Sprintf("%g", x)` = `strconv.FormatFloat(x, 'g', -1, 64)` (with `+Inf`, `-Inf`, `NaN`):
the shortest decimal that reads back as `x` (nearest to `x` among the shortest, ties to even),
in `%e` form if the decimal exponent is `< -4` or `≥ 6` (precision 6 for shortest), else `%f`.
The shortest digits are found exactly with natural-number arithmetic.
-/

namespace GoFV.SSA.FmtFloat

/-- Shortest decimal digits `k` and exponent `p` (value `k·10^p`) of the positive finite
double `m·2^e` whose rounding interval is `[lo, hi]·2^(e-2)` (inclusive iff `incl`). -/
def shortest (m : Nat) (e : Int) (loNum hiNum : Nat) (incl : Bool) : Nat × Int := Id.run do
  -- x·2^(e-2) = x·T/S
  let S : Nat := 2 ^ (2 - e).toNat
  let T : Nat := 2 ^ (e - 2).toNat
  -- compare k·10^p with x·T/S
  let cmp (k : Nat) (p : Int) (x : Nat) : Ordering :=
    if p ≥ 0 then compare (k * 10 ^ p.toNat * S) (x * T)
    else compare (k * S) (x * T * 10 ^ (-p).toNat)
  let inside (k : Nat) (p : Int) : Bool :=
    match cmp k p loNum, cmp k p hiNum with
    | .gt, .lt => true
    | .eq, _ => incl
    | _, .eq => incl
    | _, _ => false
  let v := 4 * m
  -- start above the value: 10^p0 > hi
  let mut p : Int := 0
  for _ in [0:400] do
    if cmp 1 p hiNum == .gt then break
    p := p + 1
  for _ in [0:800] do
    -- kd = floor(v / 10^p)
    let kd : Nat := if p ≥ 0 then (v * T) / (10 ^ p.toNat * S) else (v * T * 10 ^ (-p).toNat) / S
    let c0 := inside kd p && kd != 0
    let c1 := inside (kd + 1) p
    if c0 || c1 then
      let k :=
        if c0 && c1 then
          -- nearest to v: compare v - kd·10^p with (kd+1)·10^p - v, i.e. 2v vs (2kd+1)·10^p
          match cmp (2 * kd + 1) p (2 * v) with
          | .gt => kd
          | .lt => kd + 1
          | .eq => if kd % 2 == 0 then kd else kd + 1
        else if c0 then kd else kd + 1
      -- strip trailing zeros
      let mut k := k
      let mut q := p
      for _ in [0:20] do
        if k % 10 != 0 || k == 0 then break
        k := k / 10
        q := q + 1
      return (k, q)
    p := p - 1
  return (0, 0)

/-- `strconv.FormatFloat(x, 'g', -1, 64)` of the double with bits `bits`, as `%g` prints it. -/
def fmtG (bits : UInt64) : String := Id.run do
  let neg := bits >>> 63 == 1
  let ex := ((bits >>> 52) &&& 0x7ff).toNat
  let frac := (bits &&& 0xfffffffffffff).toNat
  let sign := if neg then "-" else ""
  if ex == 0x7ff then
    return if frac != 0 then "NaN" else if neg then "-Inf" else "+Inf"
  if ex == 0 && frac == 0 then return sign ++ "0"
  let (m, e) : Nat × Int := if ex == 0 then (frac, -1074) else (frac + 2^52, (ex : Int) - 1075)
  let lo := if frac == 0 && ex > 1 then 4 * m - 1 else 4 * m - 2
  let (k, p) := shortest m e lo (4 * m + 2) (m % 2 == 0)
  let ds := toString k
  let nd : Int := ds.length
  let dp : Int := p + nd
  let exp := dp - 1
  if exp < -4 || exp ≥ 6 then
    let d := ds.toList
    let mant := match d with
      | [c] => c.toString
      | c :: cs => c.toString ++ "." ++ String.ofList cs
      | [] => "0"
    let es := if exp < 0 then "-" else "+"
    let ea := exp.natAbs
    let estr := if ea < 10 then "0" ++ toString ea else toString ea
    return sign ++ mant ++ "e" ++ es ++ estr
  else
    -- %f with max(nd - dp, 0) decimals
    let intPart :=
      if dp > 0 then
        (ds.take dp.toNat).toString ++ String.ofList (List.replicate (dp - nd).toNat '0')
      else "0"
    let decs := (nd - dp).toNat
    if decs == 0 then return sign ++ intPart
    let frac := String.ofList <| (List.range decs).map fun (i : Nat) =>
      let j : Int := dp + (i : Int)
      if 0 ≤ j && j < nd then ds.toList[j.toNat]! else '0'
    return sign ++ intPart ++ "." ++ frac

end GoFV.SSA.FmtFloat
