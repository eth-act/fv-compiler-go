import GoFV.Opt.ProveCheck.Range

/-!
# prove's validator: deciding comparisons under assumptions (issue #24)

`decides D tabs A k c v`: under the assumptions `A`, the term `c` is `.bool v` whenever it is
not `poison` — by its definition (`ConstBool`), a path fact on `c` itself, `Not`, the ranges of
a comparison's sides (`rng`), or relations between the same two sides known from the facts
(`pairDecides`). Untrusted; `GoFV.Proof.ProveCheck` proves it sound.
-/

namespace GoFV.Opt.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck

/-- A relation between two `w`-bit integers `x` and `y`. -/
inductive Rel where
  /-- `x < y` (`strict`) or `x ≤ y`, signed or unsigned. -/
  | lt (signed strict : Bool)
  /-- `x = y` (`true`) or `x ≠ y`. -/
  | eq (b : Bool)
  deriving BEq, Repr, Inhabited, DecidableEq

/-- The relation `y ⋈ x` equivalent to the negation of `x ⋈ y`, for orders: `¬(x < y) ↔ y ≤ x`. -/
def Rel.negSwap : Rel → Rel
  | .lt s st => .lt s (!st)
  | .eq b => .eq (!b)

/-- A known relation between two values. -/
structure RelFact where
  x : ID
  y : ID
  w : Width
  r : Rel
  deriving BEq, Repr, Inhabited

/-- What a path fact `(c, v)` says as a relation (with `IsInBounds`/`IsSliceInBounds` also
the sign of the length, which `rangeOf` gives separately). -/
def relOf (D : ID → Option Value) (tabs : Tables) (fact : ID × Bool) : Option RelFact :=
  let (c, v) := fact
  match D c with
  | none => none
  | some cv =>
    match cv.args.toList with
    | [a, b] =>
      match cmpOf cv.op, eqOf cv.op with
      | some (w, s, st), _ =>
        if v then some ⟨a, b, w, .lt s st⟩ else some ⟨b, a, w, .lt s (!st)⟩
      | none, some (w, isEq) => some ⟨a, b, w, .eq (isEq == v)⟩
      | none, none =>
        if cv.op == .IsInBounds || cv.op == .IsSliceInBounds then
          match (D a).bind fun u => (tabs.ty u.type).width? with
          | some w =>
            let st := cv.op == .IsInBounds
            if v then some ⟨a, b, w, .lt false st⟩ else some ⟨b, a, w, .lt false (!st)⟩
          | none => none
        else none
    | _ => none

/-- `x ⋈ y` follows from the known relation `k` and the signs (`xNN`: `x ≥s 0`, `yNN`). -/
def relImplies (k : RelFact) (x y : ID) (w : Width) (t : Rel) (xNN yNN : Bool) : Bool :=
  k.w == w &&
  if k.x == x && k.y == y then
    match k.r, t with
    | .lt s st, .lt s' st' =>
      -- same order, weaker strictness; or signed → unsigned when `x ≥ 0`; unsigned → signed
      -- when `y ≥ 0`
      (st || !st') && (s == s' || (s && !s' && xNN) || (!s && s' && yNN))
    | .eq true, .lt _ st' => !st'
    | .eq b, .eq b' => b == b'
    | .lt _ true, .eq false => true
    | _, _ => false
  else if k.x == y && k.y == x then
    match k.r, t with
    | .eq b, .eq b' => b == b'
    | .eq true, .lt _ st' => !st'
    | .lt _ true, .eq false => true
    | _, _ => false
  else false

variable (D : ID → Option Value) (tabs : Tables) (A : Asm) (k : Nat)

/-- `x ⋈ y` (true) or its negation (false) follows from the path facts and the signs. -/
def pairDecides (x y : ID) (w : Width) (t : Rel) (v : Bool) : Bool :=
  let nn (z : ID) : Bool := 0 ≤ (rng D tabs A k w z).slo
  let xNN := nn x
  let yNN := nn y
  let rels := A.facts.filterMap (relOf D tabs)
  if v then rels.any fun r => relImplies r x y w t xNN yNN
  else
    -- `¬(x ⋈ y)`: for orders `y ⋈' x`; for `=` the other equality
    match t with
    | .lt s st => rels.any fun r => relImplies r y x w (.lt s (!st)) yNN xNN
    | .eq b => rels.any fun r => relImplies r x y w (.eq (!b)) xNN yNN

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
    else rx.uhi < ry.ulo || ry.uhi < rx.ulo || rx.shi < ry.slo || ry.shi < rx.slo

/-- `x ⋈ y` at width `w` is decided to be `v`. -/
def relDecides (x y : ID) (w : Width) (t : Rel) (v : Bool) : Bool :=
  rangeDecides (rng D tabs A k w x) (rng D tabs A k w y) t v || pairDecides D tabs A k x y w t v

/-- The term `c` is `.bool v` or `poison` under `A` (`fuel` bounds the `Not` nesting). -/
def decides : Nat → ID → Bool → Bool
  | 0, _, _ => false
  | fuel + 1, c, v =>
    A.facts.contains (c, v) ||
    match D c with
    | none => false
    | some cv =>
      if !termOp cv.op then false else
      match cv.op, cv.args.toList with
      | .ConstBool, [] => (cv.auxInt != 0) == v
      | .Not, [a] => decides fuel a (!v)
      | op, [a, b] =>
        match cmpOf op, eqOf op with
        | some (w, s, st), _ => relDecides D tabs A k a b w (.lt s st) v
        | none, some (w, isEq) => relDecides D tabs A k a b w (.eq isEq) v
        | none, none =>
          if op == .IsInBounds || op == .IsSliceInBounds then
            match (D a).bind fun u => (tabs.ty u.type).width? with
            | some w =>
              let st := op == .IsInBounds
              -- a negative length is `poison`; otherwise an unsigned comparison
              (rng D tabs A k w b).shi < 0 ||
              (if v then relDecides D tabs A k a b w (.lt false st) true
               else relDecides D tabs A k b a w (.lt false (!st)) true)
            | none => false
          else false
      | _, _ => false

end GoFV.Opt.ProveCheck
