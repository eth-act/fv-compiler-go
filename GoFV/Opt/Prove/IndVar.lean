import GoFV.Opt.Prove.FactsTable
import GoFV.SSA.ConstCache
import GoFV.SSA.Analysis.CfgCache

/-!
# prove: induction variables (`loopbce.go`)

`findIndVar` (with `parseIndVar`, `findKNN` and the overflow helpers), and
`addIndVarRestrictions` (`prove.go:2240`). `findIndVar` reads `f.Sdom()` (computing and caching
it if needed) and may create a cached constant for a tightened loop limit
(`f.constVal(limit.Op, limit.Type, v, true)`, `loopbce.go:253,305`) even when the induction
variable is later unused (`docs/PASSES.md`, prove, T0), so it returns the updated function.
-/

namespace GoFV.Opt.Prove

open GoFV.SSA GoFV.SSA.Analysis

/-- `indVarMinExc`, `indVarMaxInc`. -/
abbrev indVarMinExc : Nat := 1
abbrev indVarMaxInc : Nat := 2

/-- `indVar`. -/
structure IndVar where
  ind : ID
  nxt : ID
  min : ID
  max : ID
  entry : ID
  step : Int64
  flags : Nat
  deriving Inhabited, Repr

/-- `parseIndVar(ind)`: `(min, inc, nxt, loopReturn)`. -/
def parseIndVar (f : Func) (ind : ID) : Option (ID × ID × ID × Edge) :=
  let x := f.getV ind
  if x.op != .Phi then none else
  let isAdd (o : Op) : Bool := o == .Add64 || o == .Add32 || o == .Add16 || o == .Add8
  let cand (n : ID) : Bool :=
    let nv := f.getV n
    isAdd nv.op && (nv.args[0]! == ind || nv.args[1]! == ind)
  let preds := (f.getB x.block).preds
  let r? : Option (ID × ID × Edge) :=
    if cand x.args[0]! then some (x.args[1]!, x.args[0]!, preds[0]!)
    else if cand x.args[1]! then some (x.args[0]!, x.args[1]!, preds[1]!)
    else none
  r?.map fun (mn, nxt, lr) =>
    let nv := f.getV nxt
    let inc := if nv.args[0]! == ind then nv.args[1]! else nv.args[0]!
    (mn, inc, nxt, lr)

/-- `minSignedValue(t)`, `maxSignedValue(t)` for a type of `size` bytes. -/
def minSignedValue (size : Int) : Int64 := shlI (-1) (goUint (size * 8 - 1))
def maxSignedValue (size : Int) : Int64 := shlI 1 (goUint (size * 8 - 1)) - 1

/-- `subWillUnderflow(x, y, min)`, `addWillOverflow(x, y, max)`. -/
@[inline] def subWillUnderflow (x y mn : Int64) : Bool := x < mn + y
@[inline] def addWillOverflow (x y mx : Int64) : Bool := x > mx - y

/-- `diff(x, y)`. -/
@[inline] def diffU (x y : Int64) : UInt64 := (x - y).toUInt64

/-- `addU(x, y)` (Go's `Fatalf` checks are not replicated). -/
def addU (x : Int64) (y : UInt64) : Int64 :=
  let (x, y) := if y ≥ 0x8000000000000000 then (x + maxInt64 + 1, y - 0x8000000000000000)
    else (x, y)
  x + y.toInt64

/-- `subU(x, y)`. -/
def subU (x : Int64) (y : UInt64) : Int64 :=
  let (x, y) := if y ≥ 0x8000000000000000 then (x - maxInt64 - 1, y - 0x8000000000000000)
    else (x, y)
  x - y.toInt64

/-- `findKNN(v)`: `v` is `x - c` with `x` a length; `(x, c)`. -/
def findKNN (f : Func) (v : ID) : Option (ID × Int64) :=
  let vv := f.getV v
  let isAdd := vv.op == .Add64 || vv.op == .Add32 || vv.op == .Add16 || vv.op == .Add8
  let isSub := vv.op == .Sub64 || vv.op == .Sub32 || vv.op == .Sub16 || vv.op == .Sub8
  let (x, y?) : ID × Option ID :=
    if isSub then (vv.args[0]!, some vv.args[1]!)
    else if isAdd then
      if (f.getV vv.args[0]!).op.isGenericIntConst then (vv.args[1]!, some vv.args[0]!)
      else (vv.args[0]!, some vv.args[1]!)
    else (v, none)
  let xo := (f.getV x).op
  if !(xo == .SliceLen || xo == .StringLen || xo == .SliceCap) then none else
  match y? with
  | none => some (x, 0)
  | some y =>
    let yv := f.getV y
    if !yv.op.isGenericIntConst then none
    else if isAdd then some (x, -yv.auxInt) else some (x, yv.auxInt)

/-- The overflow check of `findIndVar` (its `ok` closure): whether the increment never wraps,
with the possibly tightened limit and inclusiveness, and the function (`constVal`). -/
def indVarOk (cx : Ctx) (f : Func) (ind init limit : ID) (step : Int64) (inclusive : Bool) :
    Bool × ID × Bool × Func :=
  let lv := f.getV limit
  let iv := f.getV init
  let indSize := cx.size (f.getV ind).type
  let limSize := cx.size lv.type
  let tighten (v : Int64) (better : Bool) : Bool × ID × Bool × Func :=
    if better then
      let (f, c) := f.constVal cx.sameType lv.op lv.type v true
      (true, c, true, f)
    else (true, limit, inclusive, f)
  if step > 0 then
    if lv.op.isGenericIntConst then
      let v := lv.auxInt
      if !inclusive && v == minSignedValue limSize then (false, limit, inclusive, f) else
      let v := if !inclusive then v - 1 else v
      if iv.op.isGenericIntConst && iv.auxInt > v then (false, limit, inclusive, f) else
      let v := if iv.op.isGenericIntConst then
          addU iv.auxInt (diffU v iv.auxInt / step.toUInt64 * step.toUInt64) else v
      if addWillOverflow v step (maxSignedValue indSize) then (false, limit, inclusive, f) else
      tighten v (inclusive && v != lv.auxInt || !inclusive && v + 1 != lv.auxInt)
    else if step == 1 && !inclusive then (true, limit, inclusive, f)
    else
      match findKNN f limit with
      | none => (false, limit, inclusive, f)
      | some (_, k) =>
        if k < 0 then (false, limit, inclusive, f)
        else if inclusive then (step ≤ k, limit, inclusive, f)
        else (step ≤ k + 1 && k != maxSignedValue limSize, limit, inclusive, f)
  else
    if lv.op.isGenericIntConst then
      let v := lv.auxInt
      if !inclusive && v == maxSignedValue limSize then (false, limit, inclusive, f) else
      let v := if !inclusive then v + 1 else v
      if iv.op.isGenericIntConst && iv.auxInt < v then (false, limit, inclusive, f) else
      let v := if iv.op.isGenericIntConst then
          subU iv.auxInt (diffU iv.auxInt v / (-step).toUInt64 * (-step).toUInt64) else v
      if subWillUnderflow v (-step) (minSignedValue indSize) then (false, limit, inclusive, f)
      else tighten v (inclusive && v != lv.auxInt || !inclusive && v - 1 != lv.auxInt)
    else if step == -1 && !inclusive then (true, limit, inclusive, f)
    else (false, limit, inclusive, f)

/-- One candidate of `findIndVar`: block `b` with control `c`, argument order `idx`. -/
def indVarAt (cx : Ctx) (sdom : SparseTree) (f : Func) (b : ID) (c : ID) (idx : Nat)
    (inclusive : Bool) : Option IndVar × Func :=
  let bb := f.getB b
  let cv := f.getV c
  let less := idx == 0
  let ind := cv.args[idx]!
  let limit := cv.args[1 - idx]!
  match parseIndVar f ind with
  | none => (none, f)
  | some (init, inc, nxt, loopReturn) =>
    let indv := f.getV ind
    if (f.getB indv.block).preds.size != 2 then (none, f) else
    let incv := f.getV inc
    if !incv.op.isGenericIntConst then (none, f) else
    let step := incv.auxInt
    if step == 0 || step == minSignedValue (cx.size indv.type) then (none, f) else
    let sb? : Option (Edge × Bool × Bool) :=
      if sdom.isAncestorEq bb.succs[0]!.b loopReturn.b then some (bb.succs[0]!, less, inclusive)
      else if sdom.isAncestorEq bb.succs[1]!.b loopReturn.b then
        some (bb.succs[1]!, !less, !inclusive)
      else none
    match sb? with
    | none => (none, f)
    | some (startBody, less, inclusive) =>
      if step > 0 && !less then (none, f) else
      if step < 0 && less then (none, f) else
      if (f.getB startBody.b).preds.size != 1 then (none, f) else
      if !sdom.isAncestorEq startBody.b (f.getV nxt).block then (none, f) else
      let (ok, limit, inclusive, f) := indVarOk cx f ind init limit step inclusive
      if !ok then (none, f) else
      let iv : IndVar :=
        if step > 0 then
          { ind, nxt, min := init, max := limit, entry := startBody.b, step,
            flags := if inclusive then indVarMaxInc else 0 }
        else
          { ind, nxt, min := limit, max := init, entry := startBody.b, step := -step,
            flags := indVarMaxInc ||| (if inclusive then 0 else indVarMinExc) }
      (some iv, f)

/-- `findIndVar(f)`. -/
def findIndVar (cx : Ctx) (f : Func) : Array IndVar × Func := Id.run do
  let (sdom, f) := f.sdom
  let mut f := f
  let mut ivs : Array IndVar := #[]
  for b in f.blocks do
    let bb := f.getB b
    if bb.kind != .If then continue
    let c := bb.controls[0]!
    for idx in [0:2] do
      let inclusive? : Option Bool := match (f.getV c).op with
        | .Leq64 | .Leq32 | .Leq16 | .Leq8 => some true
        | .Less64 | .Less32 | .Less16 | .Less8 => some false
        | _ => none
      let some inclusive := inclusive? | break
      let (iv?, f') := indVarAt cx sdom f b c idx inclusive
      f := f'
      if let some iv := iv? then ivs := ivs.push iv
  return (ivs, f)

/-- `addIndVarRestrictions(ft, b, iv)`. -/
def addIndVarRestrictions (p : Prover) (f : Func) (ft : FactsTable) (iv : IndVar) :
    FactsTable :=
  let d := if ft.isNonNegative iv.min && ft.isNonNegative iv.max then dSigned ||| dUnsigned
    else dSigned
  let ft := p.rc.addRestrictions f ft d iv.min iv.ind
    (if iv.flags &&& indVarMinExc == 0 then rLt ||| rEq else rLt)
  p.rc.addRestrictions f ft d iv.ind iv.max
    (if iv.flags &&& indVarMaxInc == 0 then rLt else rLt ||| rEq)

end GoFV.Opt.Prove
