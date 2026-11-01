import GoFV.Opt.ProveCheck.Range

/-!
# prove's validator: deciding comparisons under assumptions (issue #24)

`decides D tabs A k fuel c v`: under the assumptions `A`, the term `c` is `.bool v` whenever
it is not `poison` — by its definition (`ConstBool`), a path fact on `c` itself, `Not`, the
ranges of a comparison's sides (`rng`), or a path fact relating the same two sides
(`pairDecides`). A bounds check is `poison` on a negative length, so it is decided with the
length assumed nonnegative. Untrusted; `GoFV.Proof.ProveCheck` proves it sound.
-/

namespace GoFV.Opt.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck

/-- `x ⋈ y` follows from the known relation `k = (kx ⋈' ky)` (same width), given the signs
(`xNN`: `x ≥s 0`, `yNN`). -/
def relImplies (k : ID × ID × Rel) (x y : ID) (t : Rel) (xNN yNN : Bool) : Bool :=
  let (kx, ky, kr) := k
  if kx == x && ky == y then
    match kr, t with
    | .lt s st, .lt s' st' =>
      (st || !st') && (s == s' || (s && !s' && xNN && yNN) || (!s && s' && xNN && yNN))
    | .eq true, .lt _ st' => !st'
    | .eq b, .eq b' => b == b'
    | .lt _ true, .eq false => true
    | _, _ => false
  else if kx == y && ky == x then
    match kr, t with
    | .eq b, .eq b' => b == b'
    | .eq true, .lt _ st' => !st'
    | .lt _ true, .eq false => true
    | _, _ => false
  else false

/-- The negation of `x ⋈ y` as `y ⋈' x` (orders) or the other equality. -/
def Rel.neg : Rel → Rel
  | .lt s st => .lt s (!st)
  | .eq b => .eq (!b)

variable (D : ID → Option Value) (tabs : Tables) (A : Asm) (k : Nat)

/-- `x ⋈ y` at width `w` (`v = true`) or its negation follows from a path fact. -/
def pairDecides (x y : ID) (w : Width) (t : Rel) (v : Bool) : Bool :=
  let nn (z : ID) : Bool := 0 ≤ (rng D tabs A k w z).slo
  let xNN := nn x
  let yNN := nn y
  let rels := A.facts.filterMap fun fact => match relOf D tabs fact with
    | some (a, b, w', r) => if w' == w then some (a, b, r) else none
    | none => none
  match v, t with
  | true, t => rels.any fun r => relImplies r x y t xNN yNN
  | false, .lt s st => rels.any fun r => relImplies r y x (.lt s (!st)) yNN xNN
  | false, .eq b => rels.any fun r => relImplies r x y (.eq (!b)) xNN yNN

/-- The ranges of `x` and `y` decide `x ⋈ y` to be `v`. -/
def rangeDecides (rx ry : Rng) (t : Rel) (v : Bool) : Bool :=
  rx.empty || ry.empty ||
  match t, v with
  | .lt true true, true => rx.shi < ry.slo
  | .lt true true, false => ry.shi ≤ rx.slo
  | .lt true false, true => rx.shi ≤ ry.slo
  | .lt true false, false => ry.shi < rx.slo
  | .lt false true, true => rx.uhi < ry.ulo
  | .lt false true, false => ry.uhi ≤ rx.ulo
  | .lt false false, true => rx.uhi ≤ ry.ulo
  | .lt false false, false => ry.uhi < rx.ulo
  | .eq b, v =>
    if b == v then rx.ulo == rx.uhi && ry.ulo == ry.uhi && rx.ulo == ry.ulo
    else rx.uhi < ry.ulo || ry.uhi < rx.ulo

/-- `x ⋈ y` at width `w` is decided to be `v`. -/
def relDecides (x y : ID) (w : Width) (t : Rel) (v : Bool) : Bool :=
  rangeDecides (rng D tabs A k w x) (rng D tabs A k w y) t v || pairDecides D tabs A k x y w t v

/-- A comparison `a ⋈ b` of kind `ck` is decided to be `v` (a bounds check with its length
assumed nonnegative). -/
def cmpDecides (ck : CmpK) (a b : ID) (v : Bool) : Bool :=
  match ck with
  | .lt w s st => relDecides D tabs A k a b w (.lt s st) v
  | .eq w isEq => relDecides D tabs A k a b w (.eq isEq) v
  | .bounds sl =>
    match widthOf D tabs a with
    | some w =>
      let A' := { A with inv := (b, w, Rng.nonneg w.bits) :: A.inv }
      if v then relDecides D tabs A' k a b w (.lt false (!sl)) true
      else relDecides D tabs A' k b a w (.lt false sl) true
    | none => false

/-- The term `c` is `.bool v` or `poison` under `A` (`fuel` bounds the `Not` nesting). -/
def decides : Nat → ID → Bool → Bool
  | 0, _, _ => false
  | fuel + 1, c, v =>
    A.facts.contains (c, v) ||
    match D c with
    | none => false
    | some cv =>
      termOp cv.op &&
      match cv.args.toList with
      | [] => cv.op == .ConstBool && (cv.auxInt != 0) == v
      | [a] => cv.op == .Not && decides fuel a (!v)
      | [a, b] =>
        match cTab.lookup cv.op with
        | some ck => cmpDecides D tabs A k ck a b v
        | none => false
      | _ => false

end GoFV.Opt.ProveCheck
