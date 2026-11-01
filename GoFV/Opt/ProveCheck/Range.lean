import GoFV.SSA.Sem.Pure
import GoFV.Opt.RewriteCheck

/-!
# prove's validator: value ranges over terms (issue #24)

`rng D tabs A k w x` is an interval for the unsigned and the signed reading of `x`'s value as a
`w`-bit integer, computed on the input's definitions (`D = f.value?`) as terms over the atoms,
under assumptions `A`: path facts (a comparison value `c` holds `.bool v`, from the dominating
branches) and range invariants (of `Phi`s; also a nonnegative length while deciding a bounds
check). Nothing here is trusted: `GoFV.Proof.ProveCheck` proves that whenever a term's value is
a `w`-bit integer it lies in the range.

The ops the analysis looks into and the comparisons it reads facts from are table lookups
(`rTab`, `cTab`), so the proofs enumerate small tables instead of splitting on `Op`.
-/

namespace GoFV.Opt.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck

/-- An interval on the unsigned (`toNat`) and signed (`toInt`) readings of an integer. -/
structure Rng where
  ulo : Nat
  uhi : Nat
  slo : Int
  shi : Int
  deriving Repr, BEq, Inhabited, DecidableEq

namespace Rng

/-- Every `n`-bit integer. -/
def top (n : Nat) : Rng := ⟨0, 2 ^ n - 1, -2 ^ (n - 1), 2 ^ (n - 1) - 1⟩

/-- `x` lies in `r`. -/
def Mem {n : Nat} (r : Rng) (x : BitVec n) : Prop :=
  r.ulo ≤ x.toNat ∧ x.toNat ≤ r.uhi ∧ r.slo ≤ x.toInt ∧ x.toInt ≤ r.shi

def meet (a b : Rng) : Rng := ⟨max a.ulo b.ulo, min a.uhi b.uhi, max a.slo b.slo, min a.shi b.shi⟩

/-- The unsigned bounds alone (signed: everything). -/
def ofU (n lo hi : Nat) : Rng := ⟨lo, hi, -2 ^ (n - 1), 2 ^ (n - 1) - 1⟩

/-- The signed bounds alone. -/
def ofS (n : Nat) (lo hi : Int) : Rng := ⟨0, 2 ^ n - 1, lo, hi⟩

/-- Nonnegative (signed). -/
def nonneg (n : Nat) : Rng := ofS n 0 (2 ^ (n - 1) - 1)

/-- One value. -/
def point {n : Nat} (x : BitVec n) : Rng := ⟨x.toNat, x.toNat, x.toInt, x.toInt⟩

/-- Signed bounds from unsigned ones below `2 ^ (n-1)`, where the readings agree. -/
def norm1 (n : Nat) (r : Rng) : Rng :=
  if r.uhi < 2 ^ (n - 1) then ⟨r.ulo, r.uhi, max r.slo r.ulo, min r.shi r.uhi⟩ else r

/-- Signed bounds from unsigned ones from `2 ^ (n-1)` on, where they differ by `2 ^ n`. -/
def norm2 (n : Nat) (r : Rng) : Rng :=
  if 2 ^ (n - 1) ≤ r.ulo then ⟨r.ulo, r.uhi, max r.slo (r.ulo - 2 ^ n), min r.shi (r.uhi - 2 ^ n)⟩
  else r

/-- Unsigned bounds from nonnegative signed ones. -/
def norm3 (r : Rng) : Rng :=
  if 0 ≤ r.slo then ⟨max r.ulo r.slo.toNat, min r.uhi r.shi.toNat, r.slo, r.shi⟩ else r

/-- Unsigned bounds from negative signed ones. -/
def norm4 (n : Nat) (r : Rng) : Rng :=
  if r.shi < 0 then ⟨max r.ulo (r.slo + 2 ^ n).toNat, min r.uhi (r.shi + 2 ^ n).toNat, r.slo, r.shi⟩
  else r

/-- Exchange bounds between the two readings. -/
def norm (n : Nat) (r : Rng) : Rng := norm4 n (norm3 (norm2 n (norm1 n r)))

/-- Remove the single value `p` (if `p` is a point) from the ends of `r`. -/
def excl (r p : Rng) : Rng :=
  if p.ulo == p.uhi && p.slo == p.shi then
    let r := if r.ulo == p.ulo then { r with ulo := r.ulo + 1 } else r
    let r := if r.uhi == p.ulo then { r with uhi := r.uhi - 1 } else r
    let r := if r.slo == p.slo then { r with slo := r.slo + 1 } else r
    if r.shi == p.slo then { r with shi := r.shi - 1 } else r
  else r

/-- No integer lies in `r`. -/
def empty (r : Rng) : Bool := r.uhi < r.ulo || r.shi < r.slo

end Rng

/-- The assumptions at a block: path facts and range invariants. -/
structure Asm where
  facts : List (ID × Bool) := []
  inv : List (ID × Width × Rng) := []
  deriving Inhabited

/-- Term ops the range analysis evaluates. -/
inductive ROp where
  | const (w : Width)
  | zext (a b : Width)
  | sext (a b : Width)
  | and (w : Width)
  | modu (w : Width)
  | add (w : Width)
  | sub (w : Width)
  | bitLen (w : Width)
  | popCount (w : Width)
  | b2u
  deriving DecidableEq, Repr, Inhabited

/-- The ops of `ROp`. -/
def rTab : List (Op × ROp) :=
  [(.Const8, .const .w8), (.Const16, .const .w16), (.Const32, .const .w32), (.Const64, .const .w64),
   (.ZeroExt8to16, .zext .w8 .w16), (.ZeroExt8to32, .zext .w8 .w32),
   (.ZeroExt8to64, .zext .w8 .w64), (.ZeroExt16to32, .zext .w16 .w32),
   (.ZeroExt16to64, .zext .w16 .w64), (.ZeroExt32to64, .zext .w32 .w64),
   (.SignExt8to16, .sext .w8 .w16), (.SignExt8to32, .sext .w8 .w32),
   (.SignExt8to64, .sext .w8 .w64), (.SignExt16to32, .sext .w16 .w32),
   (.SignExt16to64, .sext .w16 .w64), (.SignExt32to64, .sext .w32 .w64),
   (.And8, .and .w8), (.And16, .and .w16), (.And32, .and .w32), (.And64, .and .w64),
   (.Mod8u, .modu .w8), (.Mod16u, .modu .w16), (.Mod32u, .modu .w32), (.Mod64u, .modu .w64),
   (.Add8, .add .w8), (.Add16, .add .w16), (.Add32, .add .w32), (.Add64, .add .w64),
   (.Sub8, .sub .w8), (.Sub16, .sub .w16), (.Sub32, .sub .w32), (.Sub64, .sub .w64),
   (.BitLen8, .bitLen .w8), (.BitLen16, .bitLen .w16), (.BitLen32, .bitLen .w32),
   (.BitLen64, .bitLen .w64), (.PopCount8, .popCount .w8), (.PopCount16, .popCount .w16),
   (.PopCount32, .popCount .w32), (.PopCount64, .popCount .w64), (.CvtBoolToUint8, .b2u)]

/-- Comparisons the analysis reads: `x < y`/`x ≤ y` (signed or not), `x = y`/`x ≠ y`, bounds
checks (`IsSliceInBounds`: `slice`). -/
inductive CmpK where
  | lt (w : Width) (signed strict : Bool)
  | eq (w : Width) (isEq : Bool)
  | bounds (slice : Bool)
  deriving DecidableEq, Repr, Inhabited

def cTab : List (Op × CmpK) :=
  [(.Less8, .lt .w8 true true), (.Less16, .lt .w16 true true), (.Less32, .lt .w32 true true),
   (.Less64, .lt .w64 true true), (.Leq8, .lt .w8 true false), (.Leq16, .lt .w16 true false),
   (.Leq32, .lt .w32 true false), (.Leq64, .lt .w64 true false),
   (.Less8U, .lt .w8 false true), (.Less16U, .lt .w16 false true),
   (.Less32U, .lt .w32 false true), (.Less64U, .lt .w64 false true),
   (.Leq8U, .lt .w8 false false), (.Leq16U, .lt .w16 false false),
   (.Leq32U, .lt .w32 false false), (.Leq64U, .lt .w64 false false),
   (.Eq8, .eq .w8 true), (.Eq16, .eq .w16 true), (.Eq32, .eq .w32 true), (.Eq64, .eq .w64 true),
   (.Neq8, .eq .w8 false), (.Neq16, .eq .w16 false), (.Neq32, .eq .w32 false),
   (.Neq64, .eq .w64 false), (.IsInBounds, .bounds false), (.IsSliceInBounds, .bounds true)]

/-- The integer width of `x`'s type in `D`. -/
def widthOf (D : ID → Option Value) (tabs : Tables) (x : ID) : Option Width :=
  (D x).bind fun u => (tabs.ty u.type).width?

/-- A known relation between two `w`-bit integers: `x < y` (`strict`) or `x ≤ y`, signed or
unsigned (`lt`), `x = y` (`eq true`) or `x ≠ y`. -/
inductive Rel where
  | lt (signed strict : Bool)
  | eq (b : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- A path fact as a relation `x ⋈ y` at width `w` (bounds checks: unsigned order). -/
def relOf (D : ID → Option Value) (tabs : Tables) (fact : ID × Bool) : Option (ID × ID × Width × Rel) :=
  let (c, v) := fact
  match D c with
  | none => none
  | some cv =>
    match cv.args.toList, cTab.lookup cv.op with
    | [a, b], some (.lt w s st) =>
      if v then some (a, b, w, .lt s st) else some (b, a, w, .lt s (!st))
    | [a, b], some (.eq w isEq) => some (a, b, w, .eq (isEq == v))
    | [a, b], some (.bounds sl) =>
      match widthOf D tabs a with
      | some w => if v then some (a, b, w, .lt false (!sl)) else some (b, a, w, .lt false sl)
      | none => none
    | _, _ => none

/-- Bounds on `x` from `x ⋈ y` (`lt`: `x` on the left) and `y`'s range. -/
def boundBy (n : Nat) (signed strict lt : Bool) (ry : Rng) : Rng :=
  let d : Nat := if strict then 1 else 0
  if signed then
    if lt then Rng.ofS n (-2 ^ (n - 1)) (ry.shi - d) else Rng.ofS n (ry.slo + d) (2 ^ (n - 1) - 1)
  else
    if lt then Rng.ofU n 0 (ry.uhi - d) else Rng.ofU n (ry.ulo + d) (2 ^ n - 1)

/-- The bounds a path fact gives `x` at width `w`, from the other side's range (`R`); a bounds
check also says its length is nonnegative. -/
def factRng (D : ID → Option Value) (tabs : Tables) (R : Width → ID → Rng) (w : Width) (x : ID)
    (fact : ID × Bool) : Rng :=
  let n := w.bits
  let top := Rng.top n
  let lenNN := match D fact.1 with
    | some cv =>
      match cTab.lookup cv.op with
      | some (.bounds _) => if cv.args[1]? == some x then Rng.nonneg n else top
      | _ => top
    | none => top
  match relOf D tabs fact with
  | some (a, b, w', r) =>
    if w' != w then top else
    let rx := match r with
      | .lt s st =>
        if a == x then boundBy n s st true (R w b)
        else if b == x then boundBy n s st false (R w a) else top
      | .eq true => if a == x then R w b else if b == x then R w a else top
      | .eq false => top
    rx.meet lenNN
  | none => top

/-- Exclude the other side's value from `x`'s range, if the fact says they differ. -/
def factExcl (D : ID → Option Value) (tabs : Tables) (R : Width → ID → Rng) (w : Width) (x : ID)
    (r : Rng) (fact : ID × Bool) : Rng :=
  match relOf D tabs fact with
  | some (a, b, w', .eq false) =>
    if w' != w then r else if a == x then r.excl (R w b) else if b == x then r.excl (R w a) else r
  | _ => r

/-- The range of an `ROp` node at width `w` from its arguments' ranges. -/
def rOpRng (R : Width → ID → Rng) (w : Width) (c : ROp) (auxInt : Int64) (args : Array ID) : Rng :=
  let n := w.bits
  let top := Rng.top n
  let a0 := args[0]?.getD 0
  let a1 := args[1]?.getD 0
  match c with
  | .const w' => if w' == w then Rng.point (BitVec.ofInt n auxInt.toInt) else top
  | .zext a b => if b == w && a.bits ≤ b.bits then let r := R a a0; Rng.ofU n r.ulo r.uhi else top
  | .sext a b => if b == w && a.bits ≤ b.bits then let r := R a a0; Rng.ofS n r.slo r.shi else top
  | .and w' => if w' == w then Rng.ofU n 0 (min (R w a0).uhi (R w a1).uhi) else top
  | .modu w' =>
    if w' == w then
      let ry := R w a1
      if 1 ≤ ry.ulo then Rng.ofU n 0 (min (R w a0).uhi (ry.uhi - 1)) else top
    else top
  | .add w' =>
    if w' == w then
      let rx := R w a0
      let ry := R w a1
      let u := if rx.uhi + ry.uhi < 2 ^ n then Rng.ofU n (rx.ulo + ry.ulo) (rx.uhi + ry.uhi) else top
      let s := if -2 ^ (n - 1) ≤ rx.slo + ry.slo ∧ rx.shi + ry.shi < 2 ^ (n - 1) then
        Rng.ofS n (rx.slo + ry.slo) (rx.shi + ry.shi) else top
      u.meet s
    else top
  | .sub w' =>
    if w' == w then
      let rx := R w a0
      let ry := R w a1
      let u := if ry.uhi ≤ rx.ulo then Rng.ofU n (rx.ulo - ry.uhi) (rx.uhi - ry.ulo) else top
      let s := if -2 ^ (n - 1) ≤ rx.slo - ry.shi ∧ rx.shi - ry.slo < 2 ^ (n - 1) then
        Rng.ofS n (rx.slo - ry.shi) (rx.shi - ry.slo) else top
      u.meet s
    else top
  | .bitLen a | .popCount a => Rng.ofU n 0 a.bits
  | .b2u => if w == .w8 then Rng.ofU n 0 1 else top

/-- `v`'s type has the shape of `w`-bit integers. -/
def intAt (tabs : Tables) (v : Value) (w : Width) : Bool :=
  (tabs.ty v.type).width? == some w

variable (D : ID → Option Value) (tabs : Tables) (A : Asm)

/-- The range of `x` at width `w` with depth `k`: its definition (an `ROp` node of shape
`int w`), the invariants, the path facts (bounds, then exclusions). -/
def rng : Nat → Width → ID → Rng
  | 0, w, _ => Rng.top w.bits
  | k + 1, w, x =>
    let R := rng k
    let n := w.bits
    let base := match D x with
      | some v =>
        if termOp v.op && intAt tabs v w then
          match rTab.lookup v.op with
          | some c => rOpRng R w c v.auxInt v.args
          | none => Rng.top n
        else Rng.top n
      | none => Rng.top n
    let r := A.inv.foldl (fun r (y, w', ry) => if y == x && w' == w then r.meet ry else r) base
    let r := A.facts.foldl (fun r fact => r.meet (factRng D tabs R w x fact)) r
    let r := (r.norm n)
    (A.facts.foldl (factExcl D tabs R w x) r).norm n

end GoFV.Opt.ProveCheck
