import GoFV.SSA.Sem.Pure
import GoFV.Opt.RewriteCheck

/-!
# prove's validator: value ranges over terms (issue #24)

`rng R … w x` is an interval for the unsigned and the signed reading of `x`'s value as a
`w`-bit integer, computed on the input's definitions (`D = f.value?`) as terms over the atoms,
under assumptions `Asm`: path facts (a comparison value `c` holds `.bool v`, from the dominating
branches) and range invariants of `Phi`s. Nothing here is trusted: `GoFV.Proof.ProveCheck`
proves that whenever a term's value is a `w`-bit integer it lies in the range (`rng_sound`).
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
def ofU (n lo hi : Nat) : Rng := { top n with ulo := lo, uhi := hi }

/-- The signed bounds alone. -/
def ofS (n : Nat) (lo hi : Int) : Rng := { top n with slo := lo, shi := hi }

/-- One value. -/
def point {n : Nat} (x : BitVec n) : Rng := ⟨x.toNat, x.toNat, x.toInt, x.toInt⟩

/-- Exchange bounds between the readings: below `2 ^ (n-1)` they agree, above they differ by
`2 ^ n`. -/
def norm (n : Nat) (r : Rng) : Rng :=
  let h : Nat := 2 ^ (n - 1)
  let r := if r.uhi < h then ⟨r.ulo, r.uhi, max r.slo r.ulo, min r.shi r.uhi⟩ else r
  let r := if h ≤ r.ulo then ⟨r.ulo, r.uhi, max r.slo (r.ulo - 2 ^ n), min r.shi (r.uhi - 2 ^ n)⟩
    else r
  let r := if 0 ≤ r.slo then ⟨max r.ulo r.slo.toNat, min r.uhi r.shi.toNat, r.slo, r.shi⟩ else r
  if r.shi < 0 then ⟨max r.ulo (r.slo + 2 ^ n).toNat, min r.uhi (r.shi + 2 ^ n).toNat, r.slo, r.shi⟩
  else r

/-- No integer lies in `r`. -/
def empty (r : Rng) : Bool := r.uhi < r.ulo || r.shi < r.slo

end Rng

/-- The assumptions at a block: path facts and `Phi` range invariants. -/
structure Asm where
  facts : List (ID × Bool) := []
  inv : List (ID × Width × Rng) := []
  deriving Inhabited

/-- The comparison ops by width, `(op, signed, strict)`; `Eq`/`Neq` are separate. -/
def cmpOf : Op → Option (Width × Bool × Bool)
  | .Less8 => some (.w8, true, true) | .Less16 => some (.w16, true, true)
  | .Less32 => some (.w32, true, true) | .Less64 => some (.w64, true, true)
  | .Leq8 => some (.w8, true, false) | .Leq16 => some (.w16, true, false)
  | .Leq32 => some (.w32, true, false) | .Leq64 => some (.w64, true, false)
  | .Less8U => some (.w8, false, true) | .Less16U => some (.w16, false, true)
  | .Less32U => some (.w32, false, true) | .Less64U => some (.w64, false, true)
  | .Leq8U => some (.w8, false, false) | .Leq16U => some (.w16, false, false)
  | .Leq32U => some (.w32, false, false) | .Leq64U => some (.w64, false, false)
  | _ => none

/-- `Eq`/`Neq` by width: `(width, isEq)`. -/
def eqOf : Op → Option (Width × Bool)
  | .Eq8 => some (.w8, true) | .Eq16 => some (.w16, true)
  | .Eq32 => some (.w32, true) | .Eq64 => some (.w64, true)
  | .Neq8 => some (.w8, false) | .Neq16 => some (.w16, false)
  | .Neq32 => some (.w32, false) | .Neq64 => some (.w64, false)
  | _ => none

/-- A known relation `x ⋈ y` between two `n`-bit integers, as bounds on `x` from `y`'s range:
`signed`/`strict` order, `lt = true` for `x < y` (`x ≤ y`), `false` for `x > y` (`x ≥ y`). -/
def boundBy (n : Nat) (signed strict lt : Bool) (ry : Rng) : Rng :=
  let d : Int := if strict then 1 else 0
  if signed then
    if lt then Rng.ofS n (-2 ^ (n - 1)) (ry.shi - d) else Rng.ofS n (ry.slo + d) (2 ^ (n - 1) - 1)
  else
    if lt then Rng.ofU n 0 (ry.uhi - d.toNat) else Rng.ofU n (ry.ulo + d.toNat) (2 ^ n - 1)

/-- `v`'s type has the shape of `w`-bit integers. -/
def intAt (tabs : Tables) (v : Value) (w : Width) : Bool :=
  match tabs.ty v.type with
  | .int w' => w' == w
  | _ => false

variable (D : ID → Option Value) (tabs : Tables) (A : Asm)

/-- The bounds a path fact `(c, v)` gives `x` at width `w`, from the other side's range. -/
def factRng (R : Width → ID → Rng) (w : Width) (x : ID) (fact : ID × Bool) : Rng :=
  let n := w.bits
  let (c, v) := fact
  match D c with
  | none => Rng.top n
  | some cv =>
    match cv.args.toList with
    | [a, b] =>
      match cmpOf cv.op, eqOf cv.op with
      | some (w', s, st), _ =>
        if w' != w then Rng.top n else
        -- `v`: a ⋈ b; `!v`: b ⋈' a with the converse strictness
        let st' := if v then st else !st
        let (l, r, lt) := if v then (a, b, true) else (b, a, true)
        if l == x then boundBy n s st' lt (R w r)
        else if r == x then boundBy n s st' (!lt) (R w l)
        else Rng.top n
      | none, some (w', isEq) =>
        if w' != w || isEq != v then Rng.top n
        else if a == x then R w b else if b == x then R w a else Rng.top n
      | none, none =>
        if cv.op == .IsInBounds || cv.op == .IsSliceInBounds then
          -- `a < b` (`≤` for slices) unsigned, and `b` is nonnegative
          let st := cv.op == .IsInBounds
          if v then
            if a == x then boundBy n false st true ((R w b).meet (Rng.ofS n 0 (2 ^ (n - 1) - 1)))
            else if b == x then (boundBy n false st false (R w a)).meet (Rng.ofS n 0 (2 ^ (n - 1) - 1))
            else Rng.top n
          else
            if a == x then boundBy n false (!st) false (R w b)
            else if b == x then (boundBy n false (!st) true (R w a)).meet
              (Rng.ofS n 0 (2 ^ (n - 1) - 1))
            else Rng.top n
        else Rng.top n
    | _ => Rng.top n

/-- The range of a term node `v` at width `w` from its arguments' ranges (`R`). -/
def opRng (R : Width → ID → Rng) (w : Width) (v : Value) : Rng :=
  let n := w.bits
  let top := Rng.top n
  let a0 := v.args[0]?.getD 0
  let a1 := v.args[1]?.getD 0
  let ext (a : Width) (signed : Bool) : Rng :=
    if a.bits < n then
      let r := R a a0
      if signed then Rng.ofS n r.slo r.shi else Rng.ofU n r.ulo r.uhi
    else top
  match v.op with
  | .Const8 | .Const16 | .Const32 | .Const64 =>
    if (match v.op, w with
        | .Const8, .w8 | .Const16, .w16 | .Const32, .w32 | .Const64, .w64 => true
        | _, _ => false) then Rng.point (BitVec.ofInt n v.auxInt.toInt) else top
  | .Copy => R w a0
  | .ZeroExt8to16 => if w == .w16 then ext .w8 false else top
  | .ZeroExt8to32 => if w == .w32 then ext .w8 false else top
  | .ZeroExt8to64 => if w == .w64 then ext .w8 false else top
  | .ZeroExt16to32 => if w == .w32 then ext .w16 false else top
  | .ZeroExt16to64 => if w == .w64 then ext .w16 false else top
  | .ZeroExt32to64 => if w == .w64 then ext .w32 false else top
  | .SignExt8to16 => if w == .w16 then ext .w8 true else top
  | .SignExt8to32 => if w == .w32 then ext .w8 true else top
  | .SignExt8to64 => if w == .w64 then ext .w8 true else top
  | .SignExt16to32 => if w == .w32 then ext .w16 true else top
  | .SignExt16to64 => if w == .w64 then ext .w16 true else top
  | .SignExt32to64 => if w == .w64 then ext .w32 true else top
  | .And8 | .And16 | .And32 | .And64 =>
    if (match v.op, w with
        | .And8, .w8 | .And16, .w16 | .And32, .w32 | .And64, .w64 => true
        | _, _ => false) then Rng.ofU n 0 (min (R w a0).uhi (R w a1).uhi) else top
  | .Mod8u | .Mod16u | .Mod32u | .Mod64u =>
    if (match v.op, w with
        | .Mod8u, .w8 | .Mod16u, .w16 | .Mod32u, .w32 | .Mod64u, .w64 => true
        | _, _ => false) then
      let ry := R w a1
      if 1 ≤ ry.ulo then Rng.ofU n 0 (min (R w a0).uhi (ry.uhi - 1)) else top
    else top
  | .Add8 | .Add16 | .Add32 | .Add64 =>
    if (match v.op, w with
        | .Add8, .w8 | .Add16, .w16 | .Add32, .w32 | .Add64, .w64 => true
        | _, _ => false) then
      let rx := R w a0
      let ry := R w a1
      let u := if rx.uhi + ry.uhi < 2 ^ n then Rng.ofU n (rx.ulo + ry.ulo) (rx.uhi + ry.uhi) else top
      let s := if -2 ^ (n - 1) ≤ rx.slo + ry.slo ∧ rx.shi + ry.shi < 2 ^ (n - 1) then
        Rng.ofS n (rx.slo + ry.slo) (rx.shi + ry.shi) else top
      u.meet s
    else top
  | .Sub8 | .Sub16 | .Sub32 | .Sub64 =>
    if (match v.op, w with
        | .Sub8, .w8 | .Sub16, .w16 | .Sub32, .w32 | .Sub64, .w64 => true
        | _, _ => false) then
      let rx := R w a0
      let ry := R w a1
      let u := if ry.uhi ≤ rx.ulo then Rng.ofU n (rx.ulo - ry.uhi) (rx.uhi - ry.ulo) else top
      let s := if -2 ^ (n - 1) ≤ rx.slo - ry.shi ∧ rx.shi - ry.slo < 2 ^ (n - 1) then
        Rng.ofS n (rx.slo - ry.shi) (rx.shi - ry.slo) else top
      u.meet s
    else top
  | .Ctz8 | .Ctz8NonZero | .BitLen8 | .PopCount8 => Rng.ofU n 0 8
  | .Ctz16 | .Ctz16NonZero | .BitLen16 | .PopCount16 => Rng.ofU n 0 16
  | .Ctz32 | .Ctz32NonZero | .BitLen32 | .PopCount32 => Rng.ofU n 0 32
  | .Ctz64 | .Ctz64NonZero | .BitLen64 | .PopCount64 => Rng.ofU n 0 64
  | .CvtBoolToUint8 => if w == .w8 then Rng.ofU n 0 1 else top
  | _ => top

/-- The range of `x` at width `w` with depth `k`: its definition (if a term node of shape
`int w`), the path facts and the invariants. -/
def rng : Nat → Width → ID → Rng
  | 0, w, _ => Rng.top w.bits
  | k + 1, w, x =>
    let R := rng k
    let n := w.bits
    let base := match D x with
      | some v => if termOp v.op && intAt tabs v w then opRng R w v else Rng.top n
      | none => Rng.top n
    let fs := A.facts.foldl (fun r fact => r.meet (factRng D R w x fact)) base
    let r := A.inv.foldl (fun r (y, w', ry) => if y == x && w' == w then r.meet ry else r) fs
    r.norm n

end GoFV.Opt.ProveCheck
