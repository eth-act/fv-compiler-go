import GoFV.Opt.Prove.Ctx
import GoFV.Opt.Prove.Limit
import GoFV.Opt.Prove.Poset

/-!
# prove: the facts table (`prove.go:486-1373`, `2205-2297`)

`factsTable` with its limits, orderings, the two posets and the undo stacks; `newLimit` and
`update` (mutually recursive, with Go's `recurseCheck` guard), `checkpoint`/`restore`,
`initLimit`, `getBranch`, `addBranchRestrictions`, `addRestrictions`, `addIndVarRestrictions`.
Verbatim: the order of recursive calls, orderings lists walked newest-first and limits read at
the points Go reads them decide the result (`docs/PASSES.md`, prove, parity traps).

The table is a pure value threaded through; the function `f` is read-only here (fact
derivation never changes it). Go's domains and relations are bit masks (`signed = 1`,
`unsigned = 2`, `pointer = 4`, `boolean = 8`; `lt = 1`, `eq = 2`, `gt = 4`), kept as `Nat`.

`newLimit`/`update` recurse through each other without a structural measure; they are
written as non-recursive steps taking the recursive calls as a `Rec` argument, and `Rec.mk'`
ties the knot with fuel (a recursion depth). Running out of fuel records an error, which the
pass reports instead of a wrong result.

Also the API late fuse's `fuseBranchRedirect` uses: `FactsTable.new`, `checkpoint`, `restore`,
`addBranchRestrictions`, `unsat`.
-/

namespace GoFV.Opt.Prove

open GoFV.SSA

/-! ## Domains, relations, branches -/

abbrev dSigned : Nat := 1
abbrev dUnsigned : Nat := 2
abbrev dPointer : Nat := 4
abbrev dBoolean : Nat := 8
abbrev rLt : Nat := 1
abbrev rEq : Nat := 2
abbrev rGt : Nat := 4

/-- `reverseBits[r]`. -/
def reverseBits (r : Nat) : Nat := #[0, 4, 2, 6, 1, 5, 3, 7][r]?.getD 0

/-- `domainRelationTable[op]`. -/
def domainRelation : Op → Option (Nat × Nat)
  | .Eq8 | .Eq16 | .Eq32 | .Eq64 => some (dSigned ||| dUnsigned, rEq)
  | .EqPtr => some (dPointer, rEq)
  | .EqB => some (dBoolean, rEq)
  | .Neq8 | .Neq16 | .Neq32 | .Neq64 => some (dSigned ||| dUnsigned, rLt ||| rGt)
  | .NeqPtr => some (dPointer, rLt ||| rGt)
  | .NeqB => some (dBoolean, rLt ||| rGt)
  | .Less8 | .Less16 | .Less32 | .Less64 => some (dSigned, rLt)
  | .Less8U | .Less16U | .Less32U | .Less64U => some (dUnsigned, rLt)
  | .Leq8 | .Leq16 | .Leq32 | .Leq64 => some (dSigned, rLt ||| rEq)
  | .Leq8U | .Leq16U | .Leq32U | .Leq64U => some (dUnsigned, rLt ||| rEq)
  | _ => none

/-- `opMin[op]`, `opMax[op]`, `opUMax[op]` (0 for other ops, as Go's map lookup). -/
def opMin : Op → Int64
  | .Add64 | .Sub64 => minInt64
  | .Add32 | .Sub32 => -0x80000000
  | _ => 0
def opMax : Op → Int64
  | .Add64 | .Sub64 => maxInt64
  | .Add32 | .Sub32 => 0x7FFFFFFF
  | _ => 0
def opUMax : Op → UInt64
  | .Add64 | .Sub64 => maxUint64
  | .Add32 | .Sub32 => 0xFFFFFFFF
  | _ => 0

/-- `branch`: `unknown`, `positive`, `negative`, `jumpTable0 + i`. -/
inductive Branch where
  | unknown
  | positive
  | negative
  | jumpTable (i : Nat)
  deriving DecidableEq, Inhabited, Repr

/-! ## The table -/

/-- One `ordering` (the `v` is the list it is in). -/
structure Ordering where
  w : ID
  d : Nat
  r : Nat
  deriving Inhabited, Repr

structure FactsTable where
  unsat : Bool := false
  unsatDepth : Nat := 0
  orderS : Poset := {}
  orderU : Poset := {}
  /-- `orderings[v]`, newest first, by value ID. -/
  orderings : Array (List Ordering) := #[]
  /-- IDs that had an ordering added; `0` marks a checkpoint. -/
  orderingsStack : Array ID := #[]
  limits : Array Limit := #[]
  /-- Previous limits; `vid == 0` marks a checkpoint. -/
  limitStack : Array (ID × Limit) := #[]
  recurseCheck : Array Bool := #[]
  /-- `lens[s]`/`caps[s]`: the first live `SliceLen`/`SliceCap` of slice `s` (`0`: none). -/
  lens : Array ID := #[]
  caps : Array ID := #[]
  /-- Set when a recursion ran out of fuel or Go would have panicked. -/
  err : Option String := none
  deriving Inhabited

namespace FactsTable

@[inline] def lim (ft : FactsTable) (v : ID) : Limit := ft.limits[v]?.getD default
@[inline] def isNonNegative (ft : FactsTable) (v : ID) : Bool := (ft.lim v).min ≥ 0
@[inline] def ords (ft : FactsTable) (v : ID) : List Ordering := ft.orderings[v]?.getD []
@[inline] def len? (ft : FactsTable) (s : ID) : ID := ft.lens[s]?.getD 0
@[inline] def cap? (ft : FactsTable) (s : ID) : ID := ft.caps[s]?.getD 0

@[inline] def fail (ft : FactsTable) (msg : String) : FactsTable :=
  if ft.err.isSome then ft else { ft with err := some msg }

/-- Grow an array to cover index `i`. -/
@[inline] def cover {α} (a : Array α) (i : Nat) (d : α) : Array α :=
  if i < a.size then a else a ++ Array.replicate (i + 1 - a.size) d

/-- `ft.addOrdering(v, w, d, r)`. -/
def addOrdering (ft : FactsTable) (v w : ID) (d r : Nat) : FactsTable :=
  let os := cover ft.orderings v []
  { ft with orderings := os.modify v (⟨w, d, r⟩ :: ·),
            orderingsStack := ft.orderingsStack.push v }

/-- `ft.checkpoint()`. -/
def checkpoint (ft : FactsTable) : FactsTable :=
  { ft with unsatDepth := if ft.unsat then ft.unsatDepth + 1 else ft.unsatDepth,
            limitStack := ft.limitStack.push (0, default),
            orderS := ft.orderS.checkpoint, orderU := ft.orderU.checkpoint,
            orderingsStack := ft.orderingsStack.push 0 }

/-- `ft.restore()`. -/
def restore (ft : FactsTable) : FactsTable := Id.run do
  let mut ft := if ft.unsatDepth > 0 then { ft with unsatDepth := ft.unsatDepth - 1 }
    else { ft with unsat := false }
  for _ in [0:ft.limitStack.size] do
    let some (vid, l) := ft.limitStack.back? | break
    ft := { ft with limitStack := ft.limitStack.pop }
    if vid == 0 then break
    ft := { ft with limits := ft.limits.set! vid l }
  ft := { ft with orderS := ft.orderS.undoAll, orderU := ft.orderU.undoAll }
  for _ in [0:ft.orderingsStack.size] do
    let some id := ft.orderingsStack.back? | break
    ft := { ft with orderingsStack := ft.orderingsStack.pop }
    if id == 0 then break
    ft := { ft with orderings := ft.orderings.modify id List.tail }
  return ft

end FactsTable

/-! ## `initLimit` -/

/-- `initLimit(v)`. -/
def initLimit (cx : Ctx) (f : Func) (v : ID) : Limit :=
  let x := f.getV v
  if cx.isBool x.type then
    if x.op == .ConstBool then ⟨x.auxInt, x.auxInt, x.auxInt.toUInt64, x.auxInt.toUInt64⟩
    else ⟨0, 1, 0, 1⟩
  else if cx.isPtrShaped x.type then
    match x.op with
    | .ConstNil => ⟨0, 0, 0, 0⟩
    | .Addr | .LocalAddr => { noLimit with umin := 1 }
    | _ => noLimit
  else if !cx.isInteger x.type then noLimit
  else
    let lim := noLimitForBitsize (cx.bits x.type)
    let a := x.auxInt
    let lim : Limit := match x.op with
      | .Const64 => ⟨a, a, a.toUInt64, a.toUInt64⟩
      | .Const32 => ⟨a, a, a.toUInt64.toUInt32.toUInt64, a.toUInt64.toUInt32.toUInt64⟩
      | .Const16 => ⟨a, a, a.toUInt64.toUInt16.toUInt64, a.toUInt64.toUInt16.toUInt64⟩
      | .Const8 => ⟨a, a, a.toUInt64.toUInt8.toUInt64, a.toUInt64.toUInt8.toUInt64⟩
      | .ZeroExt8to64 | .ZeroExt8to32 | .ZeroExt8to16 =>
        (lim.signedMinMax 0 255).unsignedMax 255
      | .ZeroExt16to64 | .ZeroExt16to32 => (lim.signedMinMax 0 65535).unsignedMax 65535
      | .ZeroExt32to64 => (lim.signedMinMax 0 0xFFFFFFFF).unsignedMax 0xFFFFFFFF
      | .SignExt8to64 | .SignExt8to32 | .SignExt8to16 => lim.signedMinMax (-128) 127
      | .SignExt16to64 | .SignExt16to32 => lim.signedMinMax (-32768) 32767
      | .SignExt32to64 => lim.signedMinMax (-0x80000000) 0x7FFFFFFF
      | .Ctz64 | .BitLen64 | .PopCount64 | .Ctz32 | .BitLen32 | .PopCount32
      | .Ctz16 | .BitLen16 | .PopCount16 | .Ctz8 | .BitLen8 | .PopCount8 =>
        lim.unsignedMax (Int64.ofInt (cx.size (f.getV x.args[0]!).type * 8)).toUInt64
      | .CvtBoolToUint8 => lim.unsignedMax 1
      | .SliceLen | .SliceCap =>
        let es := (((cx.info (f.getV x.args[0]!).type).elemSize?).getD 0)
        let lim := if es > 0 then
            let heap := shl 1 (goUint (cx.ptrSize * 8)) - 1
            lim.unsignedMax (heap / (Int64.ofInt es).toUInt64)
          else lim
        lim.signedMin 0
      | .StringLen => lim.signedMin 0
      | _ => lim
    let lim := if lim.min ≥ 0 then lim.unsignedMinMax lim.min.toUInt64 lim.max.toUInt64 else lim
    if fitsInBitsU lim.umax (goUint (8 * cx.size x.type - 1)) then
      lim.signedMinMax lim.umin.toInt64 lim.umax.toInt64
    else lim

namespace FactsTable

/-- `newFactsTable(f)`: limits of every value of `f.Blocks` from `initLimit`, four zero
records on the limit stack. -/
def new (cx : Ctx) (f : Func) : FactsTable := Id.run do
  let n := f.vidLast + 1
  let mut limits := Array.replicate n default
  for b in f.blocks do
    for v in (f.getB b).values do
      limits := limits.set! v (initLimit cx f v)
  return { limits, limitStack := Array.replicate 4 (0, default),
           recurseCheck := Array.replicate n false, orderings := Array.replicate n [] }

/-- `ft.initLimitForNewValue(v)` (grows the table to `f.NumValues()`, no undo record). -/
def initLimitForNewValue (cx : Ctx) (f : Func) (ft : FactsTable) (v : ID) : FactsTable :=
  let limits := if v < ft.limits.size then ft.limits
    else ft.limits ++ Array.replicate (f.vidLast + 1 - ft.limits.size) default
  { ft with limits := limits.set! v (initLimit cx f v) }

end FactsTable

/-! ## `newLimit` and `update` -/

/-- The recursive calls a step may make. -/
structure Rec where
  newLimit : Func → FactsTable → ID → Limit → FactsTable
  update : Func → FactsTable → ID → ID → Nat → Nat → FactsTable

namespace Rec

variable (rc : Rec) (f : Func)

def signedMin (ft : FactsTable) (v : ID) (m : Int64) : FactsTable :=
  rc.newLimit f ft v ⟨m, maxInt64, 0, maxUint64⟩
def signedMax (ft : FactsTable) (v : ID) (m : Int64) : FactsTable :=
  rc.newLimit f ft v ⟨minInt64, m, 0, maxUint64⟩
def signedMinMax (ft : FactsTable) (v : ID) (lo hi : Int64) : FactsTable :=
  rc.newLimit f ft v ⟨lo, hi, 0, maxUint64⟩
def setNonNegative (ft : FactsTable) (v : ID) : FactsTable := rc.signedMin f ft v 0
def unsignedMin (ft : FactsTable) (v : ID) (m : UInt64) : FactsTable :=
  rc.newLimit f ft v ⟨minInt64, maxInt64, m, maxUint64⟩
def unsignedMax (ft : FactsTable) (v : ID) (m : UInt64) : FactsTable :=
  rc.newLimit f ft v ⟨minInt64, maxInt64, 0, m⟩
def unsignedMinMax (ft : FactsTable) (v : ID) (lo hi : UInt64) : FactsTable :=
  rc.newLimit f ft v ⟨minInt64, maxInt64, lo, hi⟩
def booleanFalse (ft : FactsTable) (v : ID) : FactsTable := rc.newLimit f ft v ⟨0, 0, 0, 0⟩
def booleanTrue (ft : FactsTable) (v : ID) : FactsTable := rc.newLimit f ft v ⟨1, 1, 1, 1⟩
def pointerNil (ft : FactsTable) (v : ID) : FactsTable := rc.newLimit f ft v ⟨0, 0, 0, 0⟩
def pointerNonNil (ft : FactsTable) (v : ID) : FactsTable :=
  rc.newLimit f ft v { noLimit with umin := 1 }

/-- `addRestrictions(parent, ft, t, v, w, r)`. -/
def addRestrictions (ft : FactsTable) (t : Nat) (v w : ID) (r : Nat) : FactsTable :=
  [dSigned, dUnsigned, dPointer, dBoolean].foldl (init := ft) fun ft i =>
    if i ≤ t && t &&& i != 0 then rc.update f ft v w i r else ft

end Rec

/-- Propagate `v`'s new limit `lim` to the value of one of its orderings (`newLimit`'s loop
body). -/
def propagate (rc : Rec) (f : Func) (lim : Limit) (ft : FactsTable) (o : Ordering) :
    FactsTable :=
  let w := o.w
  if o.d == dSigned then
    match o.r with
    | 2 => rc.signedMinMax f ft w lim.min lim.max
    | 3 => rc.signedMin f ft w lim.min
    | 1 => rc.signedMin f ft w (lim.min + 1)
    | 6 => rc.signedMax f ft w lim.max
    | 4 => rc.signedMax f ft w (lim.max - 1)
    | 5 =>
      if lim.min == lim.max then
        let c := lim.min
        let ft := if (ft.lim w).min == c then rc.signedMin f ft w (c + 1) else ft
        if (ft.lim w).max == c then rc.signedMax f ft w (c - 1) else ft
      else ft
    | _ => ft
  else if o.d == dUnsigned then
    match o.r with
    | 2 => rc.unsignedMinMax f ft w lim.umin lim.umax
    | 3 => rc.unsignedMin f ft w lim.umin
    | 1 => rc.unsignedMin f ft w (lim.umin + 1)
    | 6 => rc.unsignedMax f ft w lim.umax
    | 4 => rc.unsignedMax f ft w (lim.umax - 1)
    | 5 =>
      if lim.umin == lim.umax then
        let c := lim.umin
        let ft := if (ft.lim w).umin == c then rc.unsignedMin f ft w (c + 1) else ft
        if (ft.lim w).umax == c then rc.unsignedMax f ft w (c - 1) else ft
      else ft
    | _ => ft
  else if o.d == dBoolean then
    match o.r with
    | 2 =>
      let ft := if lim.min == 0 && lim.max == 0 then rc.booleanFalse f ft w else ft
      if lim.min == 1 && lim.max == 1 then rc.booleanTrue f ft w else ft
    | 5 =>
      let ft := if lim.min == 0 && lim.max == 0 then rc.booleanTrue f ft w else ft
      if lim.min == 1 && lim.max == 1 then rc.booleanFalse f ft w else ft
    | _ => ft
  else if o.d == dPointer then
    match o.r with
    | 2 =>
      let ft := if lim.umax == 0 then rc.pointerNil f ft w else ft
      if lim.umin > 0 then rc.pointerNonNil f ft w else ft
    | 5 => if lim.umax == 0 then rc.pointerNonNil f ft w else ft
    | _ => ft
  else ft

/-- `newLimit`'s tail for a boolean `v` that became constant: relations between its
arguments. -/
def boolFacts (rc : Rec) (f : Func) (ft : FactsTable) (v : ID) (lim : Limit) : FactsTable :=
  let x := f.getV v
  let isTrue := lim.min == 1
  -- only read by the branches below, which exist for ops with arguments
  let a0 := x.args[0]?.getD 0
  let ft := match domainRelation x.op with
    | some (d, r) =>
      let d := if d == dSigned && ft.isNonNegative a0 && ft.isNonNegative x.args[1]! then
        d ||| dUnsigned else d
      let r := if !isTrue then r ^^^ 7 else r
      rc.addRestrictions f ft d a0 x.args[1]! r
    | none => ft
  match x.op with
  | .IsNonNil => if isTrue then rc.pointerNonNil f ft a0 else rc.pointerNil f ft a0
  | .IsInBounds | .IsSliceInBounds =>
    let a1 := x.args[1]!
    let r := if x.op == .IsSliceInBounds then rLt ||| rEq else rLt
    if isTrue then
      let ft := rc.setNonNegative f ft a0
      let ft := rc.update f ft a0 a1 dSigned r
      rc.update f ft a0 a1 dUnsigned r
    else
      let r := r ^^^ 7
      let ft := if ft.isNonNegative a0 then rc.update f ft a0 a1 dSigned r else ft
      rc.update f ft a0 a1 dUnsigned r
  | _ => ft

/-- `ft.newLimit(v, newLim)`, one step. -/
def newLimitStep (cx : Ctx) (rc : Rec) (f : Func) (ft : FactsTable) (v : ID) (newLim : Limit) :
    FactsTable :=
  let oldLim := ft.lim v
  let lim := oldLim.intersect newLim
  let lim := if lim.min ≥ 0 then lim.unsignedMinMax lim.min.toUInt64 lim.max.toUInt64 else lim
  let vt := (f.getV v).type
  let lim := if fitsInBitsU lim.umax (goUint (8 * cx.size vt - 1)) then
      lim.signedMinMax lim.umin.toInt64 lim.umax.toInt64 else lim
  if lim == oldLim then ft
  else if lim.unsat then { ft with unsat := true }
  else if ft.recurseCheck[v]?.getD false then ft
  else
    let ft := { ft with recurseCheck := ft.recurseCheck.set! v true,
                        limitStack := ft.limitStack.push (v, oldLim),
                        limits := ft.limits.set! v lim }
    let ft := (ft.ords v).foldl (propagate rc f lim) ft
    let ft := if cx.isBool vt then boolFacts rc f ft v lim else ft
    { ft with recurseCheck := ft.recurseCheck.set! v false }

/-- `update`'s limit derivation from the relation (`prove.go:927-1064`); `vl`/`wl` are the
limits read before any of these calls. -/
def updateLimits (rc : Rec) (f : Func) (ft : FactsTable) (v w : ID) (d r : Nat)
    (vl wl : Limit) : FactsTable :=
  if d == dSigned then
    match r with
    | 2 => let ft := rc.signedMinMax f ft v wl.min wl.max; rc.signedMinMax f ft w vl.min vl.max
    | 1 => let ft := rc.signedMax f ft v (wl.max - 1); rc.signedMin f ft w (vl.min + 1)
    | 3 => let ft := rc.signedMax f ft v wl.max; rc.signedMin f ft w vl.min
    | 4 => let ft := rc.signedMin f ft v (wl.min + 1); rc.signedMax f ft w (vl.max - 1)
    | 6 => let ft := rc.signedMin f ft v wl.min; rc.signedMax f ft w vl.max
    | 5 =>
      let ft := if vl.min == vl.max then
          let c := vl.min
          let ft := if wl.min == c then rc.signedMin f ft w (c + 1) else ft
          if wl.max == c then rc.signedMax f ft w (c - 1) else ft
        else ft
      if wl.min == wl.max then
        let c := wl.min
        let ft := if vl.min == c then rc.signedMin f ft v (c + 1) else ft
        if vl.max == c then rc.signedMax f ft v (c - 1) else ft
      else ft
    | _ => ft
  else if d == dUnsigned then
    match r with
    | 2 =>
      let ft := rc.unsignedMinMax f ft v wl.umin wl.umax; rc.unsignedMinMax f ft w vl.umin vl.umax
    | 1 => let ft := rc.unsignedMax f ft v (wl.umax - 1); rc.unsignedMin f ft w (vl.umin + 1)
    | 3 => let ft := rc.unsignedMax f ft v wl.umax; rc.unsignedMin f ft w vl.umin
    | 4 => let ft := rc.unsignedMin f ft v (wl.umin + 1); rc.unsignedMax f ft w (vl.umax - 1)
    | 6 => let ft := rc.unsignedMin f ft v wl.umin; rc.unsignedMax f ft w vl.umax
    | 5 =>
      let ft := if vl.umin == vl.umax then
          let c := vl.umin
          let ft := if wl.umin == c then rc.unsignedMin f ft w (c + 1) else ft
          if wl.umax == c then rc.unsignedMax f ft w (c - 1) else ft
        else ft
      if wl.umin == wl.umax then
        let c := wl.umin
        let ft := if vl.umin == c then rc.unsignedMin f ft v (c + 1) else ft
        if vl.umax == c then rc.unsignedMax f ft v (c - 1) else ft
      else ft
    | _ => ft
  else if d == dBoolean then
    match r with
    | 2 =>
      let ft := if vl.min == 1 then rc.booleanTrue f ft w else ft
      let ft := if vl.max == 0 then rc.booleanFalse f ft w else ft
      let ft := if wl.min == 1 then rc.booleanTrue f ft v else ft
      if wl.max == 0 then rc.booleanFalse f ft v else ft
    | 5 =>
      let ft := if vl.min == 1 then rc.booleanFalse f ft w else ft
      let ft := if vl.max == 0 then rc.booleanTrue f ft w else ft
      let ft := if wl.min == 1 then rc.booleanFalse f ft v else ft
      if wl.max == 0 then rc.booleanTrue f ft v else ft
    | _ => ft
  else if d == dPointer then
    match r with
    | 2 =>
      let ft := if vl.umax == 0 then rc.pointerNil f ft w else ft
      let ft := if vl.umin > 0 then rc.pointerNonNil f ft w else ft
      let ft := if wl.umax == 0 then rc.pointerNil f ft v else ft
      if wl.umin > 0 then rc.pointerNonNil f ft v else ft
    | 5 =>
      let ft := if vl.umax == 0 then rc.pointerNonNil f ft w else ft
      if wl.umax == 0 then rc.pointerNonNil f ft v else ft
    | _ => ft
  else ft

/-- `update`'s len/cap cross facts (`prove.go:1076-1095`). -/
def updateLenCap (rc : Rec) (f : Func) (ft : FactsTable) (v w : ID) (d r : Nat) :
    FactsTable :=
  let x := f.getV v
  let y := f.getV w
  let ft := if x.op == .SliceLen && r &&& rLt == 0 && ft.cap? x.args[0]! != 0 then
      rc.update f ft (ft.cap? x.args[0]!) w d (r ||| rGt) else ft
  let ft := if y.op == .SliceLen && r &&& rGt == 0 && ft.cap? y.args[0]! != 0 then
      rc.update f ft v (ft.cap? y.args[0]!) d (r ||| rLt) else ft
  let ft := if x.op == .SliceCap && r &&& rGt == 0 && ft.len? x.args[0]! != 0 then
      rc.update f ft (ft.len? x.args[0]!) w d (r ||| rLt) else ft
  if y.op == .SliceCap && r &&& rLt == 0 && ft.len? y.args[0]! != 0 then
    rc.update f ft v (ft.len? y.args[0]!) d (r ||| rGt) else ft

/-- `isConstDelta(v)` with the given `delta`. -/
@[inline] def constDeltaIs (f : Func) (v : ID) (delta : Int64) : Option ID :=
  match isConstDelta f v with
  | some (x, dl) => if dl == delta then some x else none
  | none => none

/-- `update`'s fence-post implications (`prove.go:1104-1132`), with `r` already `>` or `>=`. -/
def updateFence (rc : Rec) (f : Func) (ft : FactsTable) (v w : ID) (d r : Nat) : FactsTable :=
  if r == rGt then
    match constDeltaIs f v 1 with
    | some x => rc.update f ft x w d (rGt ||| rEq)
    | none =>
      match constDeltaIs f w (-1) with
      | some x => rc.update f ft v x d (rGt ||| rEq)
      | none => ft
  else if r == rGt ||| rEq then
    match constDeltaIs f v (-1) with
    | some x =>
      let l := ft.lim x
      if (d == dSigned && l.min > opMin (f.getV v).op) || (d == dUnsigned && l.umin > 0) then
        rc.update f ft x w d rGt
      else ft
    | none =>
      match constDeltaIs f w 1 with
      | some x =>
        let l := ft.lim x
        let wop := (f.getV w).op
        if (d == dSigned && l.max < opMax wop) || (d == dUnsigned && l.umax < opUMax wop) then
          rc.update f ft v x d rGt
        else ft
      | none => ft
  else ft

/-- `update`'s `x+delta > w` facts (`prove.go:1136-1222`), signed only. -/
def updateDelta (cx : Ctx) (rc : Rec) (f : Func) (ft : FactsTable) (v w : ID) (d r : Nat) :
    FactsTable :=
  if !(r == rGt || r == rGt ||| rEq) || d != dSigned then ft else
  match isConstDelta f v with
  | none => ft
  | some (x, delta) =>
    let xs := cx.size (f.getV x).type
    let underflow := if delta < 0 then
        let l := ft.lim x
        !((xs == 8 && l.min ≥ minInt64 - delta) || (xs == 4 && l.min ≥ -0x80000000 - delta))
      else true
    let ft := if delta < 0 && !underflow then rc.update f ft x v dSigned rGt else ft
    let wv := f.getV w
    if !wv.op.isGenericIntConst then
      if delta < 0 && !underflow then rc.update f ft x w dSigned r else ft
    else
      let mm : Option (Int64 × Int64) := match xs with
        | 8 => some (wv.auxInt - delta, maxInt64 - delta)
        | 4 => some ((wv.auxInt.toInt32 - delta.toInt32).toInt64,
                     ((0x7FFFFFFF : Int32) - delta.toInt32).toInt64)
        | 2 => some ((wv.auxInt.toInt16 - delta.toInt16).toInt64,
                     ((0x7FFF : Int16) - delta.toInt16).toInt64)
        | 1 => some ((wv.auxInt.toInt8 - delta.toInt8).toInt64,
                     ((0x7F : Int8) - delta.toInt8).toInt64)
        | _ => none
      match mm with
      | none => ft.fail "prove: update: unimplemented size"
      | some (mn, mx) =>
        if mn < mx then
          let mn := if r == rGt then mn + 1 else mn
          rc.signedMinMax f ft x mn mx
        else
          let l := ft.lim x
          if l.max ≤ mn then
            if r &&& rEq == 0 || l.max < mn then rc.signedMax f ft x mx else ft
          else if l.min > mx then
            rc.signedMin f ft x (if r == rGt then mn + 1 else mn)
          else ft

/-- `ft.update(parent, v, w, d, r)`, one step. -/
def updateStep (cx : Ctx) (rc : Rec) (f : Func) (ft : FactsTable) (v w : ID) (d r : Nat) :
    FactsTable :=
  if ft.unsat then ft
  else if v == w then (if r &&& rEq == 0 then { ft with unsat := true } else ft)
  else
    -- signed/unsigned: the posets
    let (ok, ft) : Bool × FactsTable :=
      if d == dSigned || d == dUnsigned then
        let po := if d == dUnsigned then ft.orderU else ft.orderS
        let (ok, po, bad) : Bool × Poset × Bool := match r with
          | 1 => let (ok, po) := po.setOrderLt v w; (ok, po, false)
          | 4 => let (ok, po) := po.setOrderLt w v; (ok, po, false)
          | 3 => let (ok, po) := po.setOrderOrEqual v w; (ok, po, false)
          | 6 => let (ok, po) := po.setOrderOrEqual w v; (ok, po, false)
          | 2 => let (ok, po) := po.setEqual v w; (ok, po, false)
          | 5 => let (ok, po) := po.setNonEqual v w; (ok, po, false)
          | _ => (true, po, true)
        let ft := if d == dUnsigned then { ft with orderU := po } else { ft with orderS := po }
        let ft := if bad then ft.fail "prove: update: unknown relation" else ft
        let ft := (ft.addOrdering v w d r).addOrdering w v d (reverseBits r)
        (ok, if ok then ft else { ft with unsat := true })
      else (true, ft)
    if !ok then ft else
    -- boolean/pointer: the orderings list
    let dup : Option Bool :=
      if d == dBoolean || d == dPointer then
        ((ft.ords v).find? fun o => o.d == d && o.w == w).map (·.r != r)
      else none
    match dup with
    | some contra => if contra then { ft with unsat := true } else ft
    | none =>
    let ft := if d == dBoolean || d == dPointer then
        (ft.addOrdering v w d r).addOrdering w v d r else ft
    let ft := updateLimits rc f ft v w d r (ft.lim v) (ft.lim w)
    if d != dSigned && d != dUnsigned then ft else
    let ft := updateLenCap rc f ft v w d r
    let (v, w, r) := if r == rLt || r == rLt ||| rEq then (w, v, reverseBits r) else (v, w, r)
    let ft := updateFence rc f ft v w d r
    let ft := updateDelta cx rc f ft v w d r
    let ft := if isCleanExt cx f v then
        let a := (f.getV v).args[0]!
        let s := cx.isSigned (f.getV a).type
        if (d == dSigned && s) || (d == dUnsigned && !s) then rc.update f ft a w d r else ft
      else ft
    if isCleanExt cx f w then
      let a := (f.getV w).args[0]!
      let s := cx.isSigned (f.getV a).type
      if (d == dSigned && s) || (d == dUnsigned && !s) then rc.update f ft v a d r else ft
    else ft

/-- The recursion with `fuel` levels of depth. -/
def Rec.mk' (cx : Ctx) : Nat → Rec
  | 0 => { newLimit := fun _ ft _ _ => ft.fail "prove: newLimit recursion out of fuel",
           update := fun _ ft _ _ _ _ => ft.fail "prove: update recursion out of fuel" }
  | n + 1 =>
    let rc := Rec.mk' cx n
    { newLimit := newLimitStep cx rc, update := updateStep cx rc }

/-- Recursion depth bound for `newLimit`/`update`. -/
def recFuel : Nat := 4096

/-! ## Branches -/

/-- `getBranch(sdom, p, b)`; `p = none` is Go's nil parent. -/
def getBranch (isAncestorEq : ID → ID → Bool) (f : Func) (p : Option ID) (b : ID) : Branch :=
  match p with
  | none => .unknown
  | some p =>
    let pb := f.getB p
    let ok (e : Edge) : Bool := isAncestorEq e.b b && (f.getB e.b).preds.size == 1
    match pb.kind with
    | .If =>
      if ok pb.succs[0]! then .positive
      else if ok pb.succs[1]! then .negative
      else .unknown
    | .JumpTable =>
      match pb.succs.findIdx? ok with
      | some i => .jumpTable i
      | none => .unknown
    | _ => .unknown

/-- `addBranchRestrictions(ft, b, br)`. -/
def addBranchRestrictions (rc : Rec) (f : Func) (ft : FactsTable) (b : ID) (br : Branch) :
    FactsTable :=
  let c := (f.getB b).controls[0]!
  match br with
  | .negative => rc.booleanFalse f ft c
  | .positive => rc.booleanTrue f ft c
  | .jumpTable i =>
    let v : Int64 := Int64.ofNat i
    let (c, v) := match isConstDelta f c with
      | some (x, off) => (x, v - off)
      | none => (c, v)
    rc.newLimit f ft c ⟨v, v, v.toUInt64, v.toUInt64⟩
  | .unknown => ft.fail "prove: unknown branch"

/-! ## Entry points for prove and late fuse -/

/-- The context and the tied recursion, built once per run. -/
structure Prover where
  cx : Ctx
  rc : Rec

/-- Build the `Prover` of a run. -/
def Prover.ofEnv (env : PassEnv) : Except String Prover := do
  let cx ← Ctx.ofEnv env
  return ⟨cx, Rec.mk' cx recFuel⟩

/-- `addBranchRestrictions(ft, b, br)`. -/
@[inline] def Prover.addBranchRestrictions (p : Prover) (f : Func) (ft : FactsTable) (b : ID)
    (br : Branch) : FactsTable :=
  GoFV.Opt.Prove.addBranchRestrictions p.rc f ft b br

end GoFV.Opt.Prove
