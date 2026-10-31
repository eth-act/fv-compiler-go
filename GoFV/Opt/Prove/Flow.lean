import GoFV.Opt.Prove.FactsTable

/-!
# prove: facts from values (`prove.go:1375-1540`, `1853-2203`, `2299-2646`)

`flowLimit` (range propagation from the arguments, with `detectMod`, `detectSliceLenRelation`,
`detectSubRelations`, `modLimit`), `addValueFact` (relational facts, with
`checkForChunkedIndexBounds` and `addLocalFactsPhi`) and `addSlicesOfSameLen`
(`getSliceInfo`). All read the function and extend the facts table only. Limits are read at
the points Go reads them (some are captured once at the start of a case, as in Go).
-/

namespace GoFV.Opt.Prove

open GoFV.SSA

variable (p : Prover) (f : Func)

@[inline] def Prover.update (ft : FactsTable) (v w : ID) (d r : Nat) : FactsTable :=
  p.rc.update f ft v w d r
@[inline] def Prover.newLimit (ft : FactsTable) (v : ID) (l : Limit) : FactsTable :=
  p.rc.newLimit f ft v l

/-- `ft.modLimit(signed, v, p, q)`. -/
def modLimit (ft : FactsTable) (signed : Bool) (v pv q : ID) : FactsTable :=
  let a := ft.lim pv
  let b := ft.lim q
  if signed && a.min < 0 && b.min > 0 then
    p.rc.signedMinMax f ft v (-(b.max - 1)) (b.max - 1)
  else if signed && !(a.nonnegative && b.nonnegative) then ft
  else
    let ft := if signed && a.min ≥ 0 && b.min > 0 then p.rc.setNonNegative f ft v else ft
    p.rc.unsignedMax f ft v (minU a.umax (b.umax - 1))

/-- `ft.detectMod(v)` (`v` is a `Sub`). -/
def detectMod (ft : FactsTable) (v : ID) : FactsTable :=
  let x := f.getV v
  let (opDiv, opDivU, opMul, opConst) : Op × Op × Op × Op := match x.op with
    | .Sub64 => (.Div64, .Div64u, .Mul64, .Const64)
    | .Sub32 => (.Div32, .Div32u, .Mul32, .Const32)
    | .Sub16 => (.Div16, .Div16u, .Mul16, .Const16)
    | .Sub8 => (.Div8, .Div8u, .Mul8, .Const8)
    | _ => (.Invalid, .Invalid, .Invalid, .Invalid)
  let mul := f.getV x.args[1]!
  if mul.op != opMul then ft else
  let (div, con) := if (f.getV mul.args[0]!).op == opConst then (mul.args[1]!, mul.args[0]!)
    else (mul.args[0]!, mul.args[1]!)
  let dv := f.getV div
  let cv := f.getV con
  if cv.op != opConst || (dv.op != opDiv && dv.op != opDivU) || dv.args[0]! != x.args[0]! ||
      (f.getV dv.args[1]!).op != opConst || (f.getV dv.args[1]!).auxInt != cv.auxInt then ft
  else modLimit p f ft (dv.op == opDiv) v x.args[0]! con

/-- `bound` is `SliceLen`/`StringLen` of `slice`. -/
@[inline] def isLenOf (f : Func) (bound slice : ID) : Bool :=
  let b := f.getV bound
  (b.op == .SliceLen || b.op == .StringLen) && b.args[0]! == slice

/-- `ft.detectSliceLenRelation(v)`. -/
def detectSliceLenRelation (ft : FactsTable) (v : ID) : FactsTable :=
  let x := f.getV v
  if x.op != .Sub64 then ft else
  let a0 := f.getV x.args[0]!
  if !(a0.op == .SliceLen || a0.op == .StringLen || a0.op == .SliceCap) then ft else
  let index := x.args[1]!
  if !ft.isNonNegative index then ft else
  let slice := a0.args[0]!
  (ft.ords index).foldl (init := ft) fun ft o =>
    if o.d != dSigned || (o.r != rLt && o.r != rLt ||| rEq) then ft else
    let ow := f.getV o.w
    if ow.op != .Add64 && ow.op != .Sub64 then ft else
    let lenOffset : Option ID :=
      if isLenOf f ow.args[0]! slice then some ow.args[1]!
      else if isLenOf f ow.args[1]! slice then (if ow.op == .Add64 then some ow.args[0]! else none)
      else none
    match lenOffset with
    | none => ft
    | some lo =>
      let lv := f.getV lo
      if lv.op != .Const64 then ft else
      let k := if ow.op == .Add64 then -lv.auxInt else lv.auxInt
      if k < 0 then ft else
      let k := if o.r == rLt then k + 1 else k
      if k < 0 then ft else p.rc.signedMin f ft v k

/-- `ft.detectSubRelations(v)` (`v` is a `Sub`). -/
def detectSubRelations (cx : Ctx) (ft : FactsTable) (v : ID) : FactsTable :=
  let xv := f.getV v
  let x := xv.args[0]!
  let y := xv.args[1]!
  if x == y then p.rc.signedMinMax f ft v 0 0 else
  let xl := ft.lim x
  let yl := ft.lim y
  let width := cx.bits xv.type
  let (ft, one) :=
    if (safeSub xl.min yl.max width).isSome && (safeSub xl.max yl.min width).isSome then
      let ft := if yl.min > 0 then p.update f ft v x dSigned rLt
        else if yl.min == 0 then p.update f ft v x dSigned (rLt ||| rEq) else ft
      if ft.orderS.ordered y x then (p.rc.signedMin f ft v 1, true)
      else if ft.orderS.orderedOrEqual y x then (p.rc.setNonNegative f ft v, false)
      else (ft, false)
    else (ft, false)
  let ft := if (safeSubU xl.umin yl.umax width).isSome then
      p.update f ft v x dUnsigned (if yl.umin > 0 then rLt else rLt ||| rEq)
    else ft
  if !one && ft.orderU.ordered y x then p.rc.unsignedMin f ft v 1 else ft

/-- `ft.flowLimit(v)`. -/
def flowLimit (ft : FactsTable) (v : ID) : FactsTable :=
  let cx := p.cx
  let x := f.getV v
  if !cx.isInteger x.type then ft else
  let a0 := x.args[0]?.getD 0
  let a1 := x.args[1]?.getD 0
  let la := ft.lim a0
  let lb := ft.lim a1
  let bits := cx.bits x.type
  let abits := cx.bits (f.getV a0).type
  match x.op with
  | .ZeroExt8to64 | .ZeroExt8to32 | .ZeroExt8to16 | .ZeroExt16to64 | .ZeroExt16to32
  | .ZeroExt32to64 => p.rc.unsignedMinMax f ft v la.umin la.umax
  | .SignExt8to64 | .SignExt8to32 | .SignExt8to16 | .SignExt16to64 | .SignExt16to32
  | .SignExt32to64 => p.rc.signedMinMax f ft v la.min la.max
  | .Trunc64to8 | .Trunc64to16 | .Trunc64to32 | .Trunc32to8 | .Trunc32to16 | .Trunc16to8 =>
    if la.umax ≤ shl 1 bits - 1 then p.rc.unsignedMinMax f ft v la.umin la.umax else ft
  | .Ctz64 | .Ctz32 | .Ctz16 | .Ctz8 => p.newLimit f ft v (la.ctz abits)
  | .PopCount64 | .PopCount32 | .PopCount16 | .PopCount8 => p.newLimit f ft v (la.popcount abits)
  | .BitLen64 | .BitLen32 | .BitLen16 | .BitLen8 => p.newLimit f ft v (la.bitlen abits)
  | .Or64 | .Or32 | .Or16 | .Or8 =>
    p.rc.unsignedMinMax f ft v (maxU la.umin lb.umin) (shl 1 (len64 (la.umax ||| lb.umax)) - 1)
  | .Xor64 | .Xor32 | .Xor16 | .Xor8 =>
    p.rc.unsignedMax f ft v (shl 1 (len64 (la.umax ||| lb.umax)) - 1)
  | .Com64 | .Com32 | .Com16 | .Com8 => p.newLimit f ft v (la.com bits)
  | .Add64 | .Add32 | .Add16 | .Add8 => p.newLimit f ft v (la.add lb bits)
  | .Sub64 | .Sub32 | .Sub16 | .Sub8 =>
    let ft := p.newLimit f ft v (la.sub lb bits)
    let ft := detectMod p f ft v
    let ft := detectSliceLenRelation p f ft v
    detectSubRelations p f cx ft v
  | .Neg64 | .Neg32 | .Neg16 | .Neg8 => p.newLimit f ft v (la.neg bits)
  | .Mul64 | .Mul32 | .Mul16 | .Mul8 => p.newLimit f ft v (la.mul lb bits)
  | .Lsh64x64 | .Lsh64x32 | .Lsh64x16 | .Lsh64x8 | .Lsh32x64 | .Lsh32x32 | .Lsh32x16
  | .Lsh32x8 | .Lsh16x64 | .Lsh16x32 | .Lsh16x16 | .Lsh16x8 | .Lsh8x64 | .Lsh8x32 | .Lsh8x16
  | .Lsh8x8 => p.newLimit f ft v (la.mul (lb.exp2 bits) bits)
  | .Rsh64x64 | .Rsh64x32 | .Rsh64x16 | .Rsh64x8 | .Rsh32x64 | .Rsh32x32 | .Rsh32x16
  | .Rsh32x8 | .Rsh16x64 | .Rsh16x32 | .Rsh16x16 | .Rsh16x8 | .Rsh8x64 | .Rsh8x32 | .Rsh8x16
  | .Rsh8x8 =>
    if lb.min ≥ 0 then
      let s0 := lb.min.toNatClampNeg
      let s1 := lb.max.toNatClampNeg
      p.rc.signedMinMax f ft v (minI (sar la.min s0) (sar la.min s1))
        (maxI (sar la.max s0) (sar la.max s1))
    else ft
  | .Rsh64Ux64 | .Rsh64Ux32 | .Rsh64Ux16 | .Rsh64Ux8 | .Rsh32Ux64 | .Rsh32Ux32 | .Rsh32Ux16
  | .Rsh32Ux8 | .Rsh16Ux64 | .Rsh16Ux32 | .Rsh16Ux16 | .Rsh16Ux8 | .Rsh8Ux64 | .Rsh8Ux32
  | .Rsh8Ux16 | .Rsh8Ux8 =>
    if lb.min ≥ 0 then
      p.rc.unsignedMinMax f ft v (shr la.umin lb.max.toNatClampNeg)
        (shr la.umax lb.min.toNatClampNeg)
    else ft
  | .Div64 | .Div32 | .Div16 | .Div8 | .Div64u | .Div32u | .Div16u | .Div8u =>
    let signed := match x.op with
      | .Div64 | .Div32 | .Div16 | .Div8 => true
      | _ => false
    if signed && !(la.nonnegative && lb.nonnegative) then ft else
    let lim := noLimit
    let lim := if lb.umax > 0 then lim.unsignedMin (la.umin / lb.umax) else lim
    let lim := if lb.umin > 0 then lim.unsignedMax (la.umax / lb.umin) else lim
    p.newLimit f ft v lim
  | .Mod64 | .Mod32 | .Mod16 | .Mod8 => modLimit p f ft true v a0 a1
  | .Mod64u | .Mod32u | .Mod16u | .Mod8u => modLimit p f ft false v a0 a1
  | .Phi =>
    let l := x.args.foldl (init := ft.lim a0) (start := 1) fun l a =>
      let l2 := ft.lim a
      { min := minI l.min l2.min, max := maxI l.max l2.max,
        umin := minU l.umin l2.umin, umax := maxU l.umax l2.umax }
    p.newLimit f ft v l
  | _ => ft

/-! ## `addValueFact` -/

/-- `unsignedAddOverflows(a, b, t)` (`none`: Go panics). -/
def unsignedAddOverflows (a b : UInt64) (size : Int) : Option Bool :=
  match size with
  | 8 => some (a + b < a)
  | 4 => some (a + b > 0xFFFFFFFF)
  | 2 => some (a + b > 0xFFFF)
  | 1 => some (a + b > 0xFF)
  | _ => none

/-- `signedAddOverflowsOrUnderflows(a, b, t)` (`none`: Go panics). -/
def signedAddOverflowsOrUnderflows (a b : Int64) (size : Int) : Option Bool :=
  let r := a + b
  match size with
  | 8 => some ((a ≥ 0 && b ≥ 0 && r < 0) || (a < 0 && b < 0 && r ≥ 0))
  | 4 => some (r < -0x80000000 || 0x7FFFFFFF < r)
  | 2 => some (r < -0x8000 || 0x7FFF < r)
  | 1 => some (r < -0x80 || 0x7F < r)
  | _ => none

/-- `checkForChunkedIndexBounds(ft, b, index, bound, isReslice)`. -/
def checkForChunkedIndexBounds (ft : FactsTable) (index bound : ID) (isReslice : Bool) : Bool :=
  let bv := f.getV bound
  if bv.op != .SliceLen && bv.op != .StringLen && bv.op != .SliceCap then false else
  let slice := bv.args[0]!
  if (ft.lim index).min < 0 then false else
  match isConstDelta f index with
  | none => false
  | some (i, delta) =>
    if delta < 0 then false else
    (ft.ords i).any fun o =>
      if o.d != dSigned then false else
      let ow := f.getV o.w
      if ow.op != .Add64 then false else
      let lenOffset : Option ID :=
        if isLenOf f ow.args[0]! slice then some ow.args[1]!
        else if isLenOf f ow.args[1]! slice then some ow.args[0]!
        else none
      match lenOffset with
      | none => false
      | some lo =>
        let lv := f.getV lo
        if lv.op != .Const64 then false else
        let k := -lv.auxInt
        if k < 0 then false else
        let k := if isReslice then k + 1 else k
        let (orr, k) := if o.r == rLt then (rLt ||| rEq, k + 1) else (o.r, k)
        if k < 0 then false else delta < k && orr == rLt ||| rEq

/-- `b.uniquePred()`. -/
@[inline] def uniquePred (f : Func) (b : ID) : Option ID :=
  let bb := f.getB b
  if bb.preds.size == 1 then some bb.preds[0]!.b else none

/-- `addLocalFactsPhi(ft, v)`: min/max phis. -/
def addLocalFactsPhi (ft : FactsTable) (v : ID) : FactsTable :=
  let xv := f.getV v
  if xv.args.size != 2 then ft else
  let b := f.getB xv.block
  let x := xv.args[0]!
  let y := xv.args[1]!
  let bx := b.preds[0]!.b
  let by_ := b.preds[1]!.b
  let z : Option ID :=
    if bx == by_ then some bx
    else if uniquePred f by_ == some bx then some bx
    else if uniquePred f bx == some by_ then some by_
    else if uniquePred f bx == uniquePred f by_ then uniquePred f bx
    else none
  match z with
  | none => ft
  | some z =>
    let zb := f.getB z
    if zb.kind != .If then ft else
    let c := f.getV zb.controls[0]!
    if c.args.size != 2 then ft else
    let isMin := if bx == z then b.preds[0]!.i == 0 else (f.getB bx).preds[0]!.i == 0
    let isMin? : Option Bool :=
      if c.args[0]! == x && c.args[1]! == y then some isMin
      else if c.args[0]! == y && c.args[1]! == x then some !isMin
      else none
    match isMin? with
    | none => ft
    | some isMin =>
      let dom? : Option Nat := match c.op with
        | .Less64 | .Less32 | .Less16 | .Less8 | .Leq64 | .Leq32 | .Leq16 | .Leq8 => some dSigned
        | .Less64U | .Less32U | .Less16U | .Less8U | .Leq64U | .Leq32U | .Leq16U | .Leq8U =>
          some dUnsigned
        | _ => none
      match dom? with
      | none => ft
      | some dom =>
        let rel := if isMin then rLt ||| rEq else rGt ||| rEq
        let ft := p.update f ft v x dom rel
        p.update f ft v y dom rel

def isRshSigned : Op → Bool
  | .Rsh8x64 | .Rsh8x32 | .Rsh8x16 | .Rsh8x8 | .Rsh16x64 | .Rsh16x32 | .Rsh16x16 | .Rsh16x8
  | .Rsh32x64 | .Rsh32x32 | .Rsh32x16 | .Rsh32x8 | .Rsh64x64 | .Rsh64x32 | .Rsh64x16
  | .Rsh64x8 => true
  | _ => false

def isRshUnsigned : Op → Bool
  | .Rsh8Ux64 | .Rsh8Ux32 | .Rsh8Ux16 | .Rsh8Ux8 | .Rsh16Ux64 | .Rsh16Ux32 | .Rsh16Ux16
  | .Rsh16Ux8 | .Rsh32Ux64 | .Rsh32Ux32 | .Rsh32Ux16 | .Rsh32Ux8 | .Rsh64Ux64 | .Rsh64Ux32
  | .Rsh64Ux16 | .Rsh64Ux8 => true
  | _ => false

/-- The shared tail of `addValueFact`'s `Div`/`Rsh` cases (round-up division pattern). -/
def divRshFacts (ft : FactsTable) (v : ID) : FactsTable :=
  let xv := f.getV v
  let add := f.getV xv.args[0]!
  let ft := match add.op with
    | .Add64 | .Add32 | .Add16 | .Add8 =>
      let zl := ft.lim xv.args[1]!
      let uminDivisor := if isRshSigned xv.op || isRshUnsigned xv.op then shl 1 zl.umin.toNat
        else zl.umin
      let x := add.args[0]!
      let y := add.args[1]!
      let xl := ft.lim x
      let yl := ft.lim y
      match unsignedAddOverflows xl.umax yl.umax (p.cx.size add.type) with
      | none => ft.fail "prove: unsignedAddOverflows: bad size"
      | some true => ft
      | some false =>
        let ft := if xl.umax < uminDivisor then p.update f ft v y dUnsigned (rLt ||| rEq) else ft
        if yl.umax < uminDivisor then p.update f ft v x dUnsigned (rLt ||| rEq) else ft
    | _ => ft
  p.update f ft v xv.args[0]! dUnsigned (rLt ||| rEq)

/-- `addValueFact`'s `Add` case. -/
def addFacts (ft : FactsTable) (v : ID) : FactsTable :=
  let xv := f.getV v
  let a0 := xv.args[0]!
  let a1 := xv.args[1]!
  let x := ft.lim a0
  let y := ft.lim a1
  let size := p.cx.size xv.type
  match unsignedAddOverflows x.umax y.umax size,
      signedAddOverflowsOrUnderflows x.max y.max size,
      signedAddOverflowsOrUnderflows x.min y.min size with
  | some uo, some soMax, some soMin =>
    let ft := if !uo then
        let ft := p.update f ft v a1 dUnsigned (if x.maybeZero then rGt ||| rEq else rGt)
        p.update f ft v a0 dUnsigned (if y.maybeZero then rGt ||| rEq else rGt)
      else ft
    let ft := if x.min ≥ 0 && !soMax then
        p.update f ft v a1 dSigned (if x.maybeZero then rGt ||| rEq else rGt) else ft
    let ft := if y.min ≥ 0 && !soMax then
        p.update f ft v a0 dSigned (if y.maybeZero then rGt ||| rEq else rGt) else ft
    let ft := if x.max ≤ 0 && !soMin then
        p.update f ft v a1 dSigned (if x.maybeZero then rLt ||| rEq else rLt) else ft
    if y.max ≤ 0 && !soMin then
      p.update f ft v a0 dSigned (if y.maybeZero then rLt ||| rEq else rLt) else ft
  | _, _, _ => ft.fail "prove: addValueFact: bad add size"

/-- `ft.addValueFact(b, v)`. -/
def addValueFact (ft : FactsTable) (v : ID) : FactsTable :=
  let xv := f.getV v
  match xv.op with
  | .Add64 | .Add32 | .Add16 | .Add8 => addFacts p f ft v
  | .Sub64 | .Sub32 | .Sub16 | .Sub8 =>
    let x := ft.lim xv.args[0]!
    let y := ft.lim xv.args[1]!
    if !(x.umin < y.umax) then
      p.update f ft v xv.args[0]! dUnsigned (if y.maybeZero then rLt ||| rEq else rLt)
    else ft
  | .And64 | .And32 | .And16 | .And8 =>
    let ft := p.update f ft v xv.args[0]! dUnsigned (rLt ||| rEq)
    let ft := p.update f ft v xv.args[1]! dUnsigned (rLt ||| rEq)
    let ft := if ft.isNonNegative xv.args[0]! then
        p.update f ft v xv.args[0]! dSigned (rLt ||| rEq) else ft
    if ft.isNonNegative xv.args[1]! then p.update f ft v xv.args[1]! dSigned (rLt ||| rEq)
    else ft
  | .Div64 | .Div32 | .Div16 | .Div8 =>
    if !ft.isNonNegative xv.args[1]! then ft
    else if !ft.isNonNegative xv.args[0]! then ft
    else divRshFacts p f ft v
  | .Div64u | .Div32u | .Div16u | .Div8u => divRshFacts p f ft v
  | .Mod64 | .Mod32 | .Mod16 | .Mod8 | .Mod64u | .Mod32u | .Mod16u | .Mod8u =>
    let signed := match xv.op with
      | .Mod64 | .Mod32 | .Mod16 | .Mod8 => true
      | _ => false
    if signed && (!ft.isNonNegative xv.args[0]! || !ft.isNonNegative xv.args[1]!) then ft else
    let ft := p.update f ft v xv.args[0]! dUnsigned (rLt ||| rEq)
    p.update f ft v xv.args[1]! dUnsigned rLt
  | .StringLen =>
    let a := f.getV xv.args[0]!
    if a.op == .StringMake then p.update f ft v a.args[1]! dSigned rEq else ft
  | .SliceLen =>
    let a := f.getV xv.args[0]!
    if a.op == .SliceMake then p.update f ft v a.args[1]! dSigned rEq else ft
  | .SliceCap =>
    let a := f.getV xv.args[0]!
    if a.op == .SliceMake then p.update f ft v a.args[2]! dSigned rEq else ft
  | .IsInBounds =>
    if checkForChunkedIndexBounds f ft xv.args[0]! xv.args[1]! false then
      p.rc.booleanTrue f ft v else ft
  | .IsSliceInBounds =>
    if checkForChunkedIndexBounds f ft xv.args[0]! xv.args[1]! true then
      p.rc.booleanTrue f ft v else ft
  | .Phi => addLocalFactsPhi p f ft v
  | op =>
    if isRshSigned op then
      if !ft.isNonNegative xv.args[0]! then ft else divRshFacts p f ft v
    else if isRshUnsigned op then divRshFacts p f ft v
    else ft

/-! ## `addSlicesOfSameLen` -/

/-- `sliceInfo{lengthDiff, sliceWhere, predIndex}`; `sliceWhere`: 0 unknown, 1 in for, 2 in if. -/
structure SliceInfo where
  lengthDiff : Int64 := 0
  sliceWhere : Nat := 0
  predIndex : Nat := 0
  deriving DecidableEq, Inhabited

/-- `getSliceInfo(vp)`. -/
def getSliceInfo (vp : ID) : SliceInfo :=
  let x := f.getV vp
  if x.op != .Phi || x.args.size != 2 then {} else
  let a0 := f.getV x.args[0]!
  let a1 := f.getV x.args[1]!
  let li? : Option (ID × Nat) :=
    if a0.op != .SliceMake && a1.op == .SliceMake then some (a1.args[1]!, 1)
    else if a0.op == .SliceMake && a1.op != .SliceMake then some (a0.args[1]!, 0)
    else none
  match li? with
  | none => {}
  | some (l, i) =>
    let lv := f.getV l
    let op? : Option Op := match lv.op with
      | .Add64 => some .Const64
      | .Add32 => some .Const32
      | _ => none
    match op? with
    | none => {}
    | some op =>
      let l0 := f.getV lv.args[0]!
      let l1 := f.getV lv.args[1]!
      let other := x.args[1 - i]!
      if l0.op == op && l1.op == .SliceLen && l1.args[0]! == vp then ⟨l0.auxInt, 1, i⟩
      else if l1.op == op && l0.op == .SliceLen && l0.args[0]! == vp then ⟨l1.auxInt, 1, i⟩
      else if l0.op == op && l1.op == .SliceLen && l1.args[0]! == other then ⟨l0.auxInt, 2, i⟩
      else if l1.op == op && l0.op == .SliceLen && l0.args[0]! == other then ⟨l1.auxInt, 2, i⟩
      else {}

/-- `addSlicesOfSameLen(ft, b)`. -/
def addSlicesOfSameLen (ft : FactsTable) (b : ID) : FactsTable := Id.run do
  let mut ft := ft
  let mut u : ID := 0
  let mut w : ID := 0
  let mut i : SliceInfo := {}
  let mut k : SliceInfo := {}
  for v in (f.getB b).values do
    let x := f.getV v
    if x.uses == 0 then continue
    if !(x.op == .Phi && x.args.size == 2 && ft.len? v != 0) then continue
    let j := getSliceInfo f v
    if j.sliceWhere == 0 then continue
    if j.predIndex == 1 && ft.len? x.args[0]! != 0 then
      if w == 0 then
        k := j
        w := v
        continue
      let wx := f.getV w
      if j == k && ft.orderS.equal (ft.len? x.args[0]!) (ft.len? wx.args[0]!) then
        ft := p.update f ft (ft.len? v) (ft.len? w) dSigned rEq
    else if j.predIndex == 0 && ft.len? x.args[1]! != 0 then
      if u == 0 then
        i := j
        u := v
        continue
      let ux := f.getV u
      if j == i && ft.orderS.equal (ft.len? x.args[1]!) (ft.len? ux.args[1]!) then
        ft := p.update f ft (ft.len? v) (ft.len? u) dSigned rEq
  return ft

end GoFV.Opt.Prove
