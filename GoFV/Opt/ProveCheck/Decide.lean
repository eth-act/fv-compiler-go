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

/-- The value of `x ⋈ x`. -/
def Rel.refl : Rel → Bool
  | .lt _ st => !st
  | .eq b => b

variable (D : ID → Option Value) (tabs : Tables) (A : Asm) (k : Nat)

/-- `x ⋈ y` at width `w` (`v = true`) or its negation follows from a path fact relating their
`canon`ical forms, or they are the same. -/
def pairDecides (x y : ID) (w : Width) (t : Rel) (v : Bool) : Bool :=
  let x := canon D tabs x
  let y := canon D tabs y
  let nn (z : ID) : Bool := 0 ≤ (rng D tabs A k w z).slo
  let xNN := nn x
  let yNN := nn y
  let rels := A.facts.filterMap fun fact => match relOf D tabs fact with
    | some (a, b, w', r) => if w' == w then some (a, b, r) else none
    | none => none
  (x == y && t.refl == v) ||
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

/-! ## Differences `V(u) - V(v) ≤ c` from chains of path facts -/

/-- The bounds of `r` in the reading `s` (signed: `toInt`, unsigned: `toNat`). -/
def Rng.lo (s : Bool) (r : Rng) : Int := if s then r.slo else r.ulo
def Rng.hi (s : Bool) (r : Rng) : Int := if s then r.shi else r.uhi

/-- The least and the greatest `n`-bit integer in the reading `s`. -/
def readMin (n : Nat) (s : Bool) : Int := if s then -2 ^ (n - 1) else 0
def readMax (n : Nat) (s : Bool) : Int := if s then 2 ^ (n - 1) - 1 else 2 ^ n - 1

/-- Add `(v, d)` unless `v` already has a bound at most `d`. -/
def addDist (dist : List (ID × Int)) (v : ID) (d : Int) : List (ID × Int) :=
  if dist.any (fun (z, e) => z == v && e ≤ d) then dist else (v, d) :: dist

/-- One round of relaxing the edges `(u, v, c)` (`V(u) - V(v) ≤ c`). -/
def relax (es : List (ID × ID × Int)) (dist : List (ID × Int)) : List (ID × Int) :=
  es.foldl (fun dist (u, v, c) =>
    dist.foldl (fun acc (z, d) => if z == u then addDist acc v (d + c) else acc) dist) dist

/-- Bounds `V(x) - V(z) ≤ d` along paths of edges from `x`. -/
def distFrom (es : List (ID × ID × Int)) (x : ID) : List (ID × Int) :=
  (List.range es.length).foldl (fun dist _ => relax es dist) [(x, 0)]

/-- `V(x) - V(y) ≤ c` follows from the edges. -/
def diffLe (es : List (ID × ID × Int)) (x y : ID) (c : Int) : Bool :=
  (distFrom es x).any fun (z, e) => z == y && e ≤ c

/-- `V(x) - V(y) ≤ c` follows from the edges `es`, or from them up to some `z` and a last edge
`(z, y, c')` of `rs` (which, unlike `es`, need not hold when their ends are undefined). -/
def diffLeR (es rs : List (ID × ID × Int)) (x y : ID) (c : Int) : Bool :=
  diffLe es x y c || rs.any fun (z, y', c') => y' == y && diffLe es x z (c - c')

/-- The signed value of `z` if it is a `w`-bit constant. -/
def constVal (w : Width) (z : ID) : Option Int :=
  match D z with
  | some zv =>
    if termOp zv.op && rTab.lookup zv.op == some (.const w) then
      some (BitVec.ofInt w.bits zv.auxInt.toInt).toInt
    else none
  | none => none

/-- `x` is `a + c` at width `w` (as terms): an `Add` with a constant argument of signed value
`c`, or a `Sub` of a constant of signed value `-c`. -/
def addConst (w : Width) (x : ID) : Option (ID × Int) :=
  match D x with
  | some v =>
    if termOp v.op then
      match rTab.lookup v.op, v.args.toList with
      | some (.add w'), [a, b] =>
        if w' == w then
          match constVal D w b, constVal D w a with
          | some c, _ => some (a, c)
          | none, some c => some (b, c)
          | none, none => none
        else none
      | some (.sub w'), [a, b] =>
        if w' == w then (constVal D w b).map fun c => (a, -c) else none
      | _, _ => none
    else none
  | none => none

/-- `x` as `base + c` in the reading `s` at width `w`, without wraparound (by `base`'s range,
`addConst`); otherwise `x + 0`. -/
def offOf (s : Bool) (w : Width) (x0 : ID) : ID × Int :=
  let x := canon D tabs x0
  match addConst D w x with
  | some (b, c) =>
    let r := rng D tabs A k w b
    if readMin w.bits s ≤ r.lo s + c && r.hi s + c ≤ readMax w.bits s then (canon D tabs b, c)
    else (x, 0)
  | none => (x, 0)

/-- The edges `V(u) - V(v) ≤ c` (reading `s`, width `w`) a path fact gives: an order in the
same reading or between nonnegative sides; an equality both ways. -/
def factEdges (s : Bool) (w : Width) (fact : ID × Bool) : List (ID × ID × Int) :=
  match relOf D tabs fact with
  | some (a, b, w', r) =>
    if w' != w then [] else
    let (ba, ca) := offOf D tabs A k s w a
    let (bb, cb) := offOf D tabs A k s w b
    match r with
    | .lt s' st =>
      if s' == s || (0 ≤ (rng D tabs A k w a).slo && 0 ≤ (rng D tabs A k w b).slo) then
        [(ba, bb, cb - ca - (if st then 1 else 0))]
      else []
    | .eq true => [(ba, bb, cb - ca), (bb, ba, ca - cb)]
    | .eq false => []
  | none => []

/-- The edges `V(z) - V(y) ≤ c` (signed, width `w`) of the relations into `y`, if `y` is
nonnegative. -/
def relEdges (w : Width) (y : ID) : List (ID × ID × Int) :=
  let rs := A.rels.filterMap fun (z, y', w', c) =>
    if w' == w && y' == y then some (z, y, c) else none
  if !rs.isEmpty && 0 ≤ (rng D tabs A k w y).slo then rs else []

/-- The path facts' edges in the reading `s` at width `w`. -/
def linFacts (s : Bool) (w : Width) : List (ID × ID × Int) :=
  A.facts.flatMap (factEdges D tabs A k s w)

/-- The last edges (`diffLeR`) into `y` in the reading `s` at width `w`: in the signed reading
the relations'. -/
def linRels (s : Bool) (w : Width) (y : ID) : List (ID × ID × Int) :=
  if s then relEdges D tabs A k w y else []

/-- `x ⋈ y` at width `w` is decided to be `v` in the reading `s` by differences. -/
def linIn (s : Bool) (x y : ID) (w : Width) (t : Rel) (v : Bool) : Bool :=
  let es := linFacts D tabs A k s w
  let (bx, cx) := offOf D tabs A k s w x
  let (by', cy) := offOf D tabs A k s w y
  let le (a b : ID) (c : Int) := diffLeR es (linRels D tabs A k s w b) a b c
  match t with
  | .lt _ st =>
    if v then le bx by' (cy - cx - (if st then 1 else 0))
    else le by' bx (cx - cy - (if st then 0 else 1))
  | .eq b =>
    if b == v then le bx by' (cy - cx) && le by' bx (cx - cy)
    else le bx by' (cy - cx - 1) || le by' bx (cx - cy - 1)

/-- `x ⋈ y` at width `w` is decided to be `v` by differences: orders in their own reading (an
unsigned order also in the signed reading when both sides are nonnegative), equalities in
either. -/
def linDecides (x y : ID) (w : Width) (t : Rel) (v : Bool) : Bool :=
  match t with
  | .lt s st => linIn D tabs A k s x y w t v ||
    (!s && 0 ≤ (rng D tabs A k w x).slo && 0 ≤ (rng D tabs A k w y).slo &&
      linIn D tabs A k true x y w (.lt true st) v)
  | .eq _ => linIn D tabs A k true x y w t v || linIn D tabs A k false x y w t v

/-- `V(x) - V(y) ≤ c` (signed, width `w`) follows from the differences. -/
def diffDecides (x y : ID) (w : Width) (c : Int) : Bool :=
  let (bx, cx) := offOf D tabs A k true w x
  let (by', cy) := offOf D tabs A k true w y
  diffLeR (linFacts D tabs A k true w) (linRels D tabs A k true w by') bx by' (c - cx + cy)

/-- Depth of the range analysis inside `linDecides` (offsets, signs of fact sides). -/
def linFuel : Nat := 2

/-- `x ⋈ y` at width `w` is decided to be `v`. -/
def relDecides (x y : ID) (w : Width) (t : Rel) (v : Bool) : Bool :=
  rangeDecides (rng D tabs A k w x) (rng D tabs A k w y) t v || pairDecides D tabs A k x y w t v ||
    linDecides D tabs A linFuel x y w t v

/-- A comparison `a ⋈ b` of kind `ck` is decided to be `v` (a bounds check with its length
assumed nonnegative). -/
def cmpDecides (ck : CmpK) (a b : ID) (v : Bool) : Bool :=
  match ck with
  | .lt w s st => relDecides D tabs A k a b w (.lt s st) v
  | .eq w isEq => relDecides D tabs A k a b w (.eq isEq) v
  | .bounds sl =>
    match widthOf D tabs a with
    | some w =>
      let A' := { A with inv := (canon D tabs b, w, Rng.nonneg w.bits) :: A.inv }
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
