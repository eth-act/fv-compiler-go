import GoFV.Opt.Prove.Flow
import GoFV.SSA.ConstCache
import GoFV.SSA.Edges
import GoFV.Util.PdqSort

/-!
# prove: the rewrites (`prove.go:2648-3177`)

`simplifyValue` (T4–T14 of `docs/PASSES.md`, prove), `constantFoldArguments` (T3),
`simplifyBlock` and `removeBranch` (T15/T16) and `topoSortValuesInBlock` (T2). These change the
function; new constants come from the constant cache (`constVal`, `NoXPos`, end of
`f.Entry`), `Mul → CondSelect` appends its `Neq` check to the block. Each takes and returns the
function and the facts table.
-/

namespace GoFV.Opt.Prove

open GoFV.SSA

abbrev St := Func × FactsTable

/-- `bytesizeToConst`, `bytesizeToNeq`, `bytesizeToAnd`. -/
def bytesizeToConst : Int → Op
  | 1 => .Const8 | 2 => .Const16 | 4 => .Const32 | 8 => .Const64 | _ => .Invalid
def bytesizeToNeq : Int → Op
  | 1 => .Neq8 | 2 => .Neq16 | 4 => .Neq32 | 8 => .Neq64 | _ => .Invalid
def bytesizeToAnd : Int → Op
  | 1 => .And8 | 2 => .And16 | 4 => .And32 | 8 => .And64 | _ => .Invalid

def ctzNonZeroOp : Op → Op
  | .Ctz8 => .Ctz8NonZero | .Ctz16 => .Ctz16NonZero | .Ctz32 => .Ctz32NonZero
  | .Ctz64 => .Ctz64NonZero | _ => .Invalid

/-- `mostNegativeDividend[op]` (0 for other ops). -/
def mostNegativeDividend : Op → Int64
  | .Div16 | .Mod16 => -0x8000
  | .Div32 | .Mod32 => -0x80000000
  | .Div64 | .Mod64 => minInt64
  | _ => 0

/-- `unsignedOp[op]`. -/
def unsignedOp : Op → Op
  | .Div8 => .Div8u | .Div16 => .Div16u | .Div32 => .Div32u | .Div64 => .Div64u
  | .Mod8 => .Mod8u | .Mod16 => .Mod16u | .Mod32 => .Mod32u | .Mod64 => .Mod64u
  | .Rsh8x8 => .Rsh8Ux8 | .Rsh8x16 => .Rsh8Ux16 | .Rsh8x32 => .Rsh8Ux32 | .Rsh8x64 => .Rsh8Ux64
  | .Rsh16x8 => .Rsh16Ux8 | .Rsh16x16 => .Rsh16Ux16 | .Rsh16x32 => .Rsh16Ux32
  | .Rsh16x64 => .Rsh16Ux64
  | .Rsh32x8 => .Rsh32Ux8 | .Rsh32x16 => .Rsh32Ux16 | .Rsh32x32 => .Rsh32Ux32
  | .Rsh32x64 => .Rsh32Ux64
  | .Rsh64x8 => .Rsh64Ux8 | .Rsh64x16 => .Rsh64Ux16 | .Rsh64x32 => .Rsh64Ux32
  | .Rsh64x64 => .Rsh64Ux64
  | _ => .Invalid

/-- `invertEqNeqOp[op]`. -/
def invertEqNeqOp : Op → Op
  | .Eq8 => .Neq8 | .Neq8 => .Eq8 | .Eq16 => .Neq16 | .Neq16 => .Eq16
  | .Eq32 => .Neq32 | .Neq32 => .Eq32 | .Eq64 => .Neq64 | .Neq64 => .Eq64
  | _ => .Invalid

def isLshOrRshU : Op → Bool
  | .Lsh8x8 | .Lsh8x16 | .Lsh8x32 | .Lsh8x64 | .Lsh16x8 | .Lsh16x16 | .Lsh16x32 | .Lsh16x64
  | .Lsh32x8 | .Lsh32x16 | .Lsh32x32 | .Lsh32x64 | .Lsh64x8 | .Lsh64x16 | .Lsh64x32
  | .Lsh64x64 => true
  | op => isRshUnsigned op

/-- `isPowerOfTwo` on `int64` and `uint64`. -/
@[inline] def isPowerOfTwoI (n : Int64) : Bool := n > 0 && n &&& (n - 1) == 0
@[inline] def isPowerOfTwoU (n : UInt64) : Bool := n > 0 && n &&& (n - 1) == 0

variable (p : Prover)

/-- `f.constVal(op, t, 0, true)` followed by `ft.initLimitForNewValue`. -/
def zeroConst (st : St) (op : Op) (t : TypeRef) : St × ID :=
  let (f, ft) := st
  let (f, z) := f.constVal p.cx.sameType op t 0 true
  ((f, ft.initLimitForNewValue p.cx f z), z)

/-- The "remove a no-op `And`/`Or`" cases: `x` (the non-constant side) and the constant. -/
def constSide (ft : FactsTable) (a0 a1 : ID) : Option (ID × Int64) :=
  match (ft.lim a0).constValue, (ft.lim a1).constValue with
  | some _, some _ => none
  | some c, none => some (a1, c)
  | none, some c => some (a0, c)
  | none, none => none

/-- The shift-bounded check (`AuxInt = 1`) of `simplifyValue`. -/
def shiftBounded (st : St) (v : ID) : St :=
  let (f, ft) := st
  let x := f.getV v
  let by_ := x.args[1]!
  let lim := ft.lim by_
  let bits : Int64 := Int64.ofInt (8 * p.cx.size (f.getV x.args[0]!).type)
  if lim.umax < bits.toUInt64 || (lim.max < bits && ft.isNonNegative by_) then
    (f.modV v fun y => { y with auxInt := 1 }, ft)
  else st

/-- `simplifyValue`'s `Mul` case (T10, T11). -/
def simplifyMul (st : St) (b v : ID) : St :=
  let (f, ft) := st
  let vl := ft.lim v
  if vl.min == vl.max || vl.umin == vl.umax then st else
  let xv := f.getV v
  let x := xv.args[0]!
  let y := xv.args[1]!
  let xl := ft.lim x
  let yl := ft.lim y
  if xl.umin == xl.umax && isPowerOfTwoU xl.umin || xl.min == xl.max && isPowerOfTwoI xl.min ||
      yl.umin == yl.umax && isPowerOfTwoU yl.umin || yl.min == yl.max && isPowerOfTwoI yl.min
  then st else
  let xOne := xl.umax ≤ 1
  let yOne := yl.umax ≤ 1
  let size := p.cx.size xv.type
  if xOne && yOne then (f.modV v fun z => { z with op := bytesizeToAnd size }, ft)
  else
    let xy? : Option (ID × ID) :=
      if yOne && p.cx.haveCondSelect then some (y, x)
      else if xOne && p.cx.haveCondSelect then some (x, y)
      else none
    match xy? with
    | none => st
    | some (x, y) =>
      match canCondSelect p.cx.tables p.cx.regSize p.cx.arch f v false with
      | .error e => (f, ft.fail s!"prove: canCondSelect: {e}")
      | .ok false => st
      | .ok true =>
        let ((f, ft), zc) := zeroConst p (f, ft) (bytesizeToConst size) xv.type
        let (f, check) := f.newValueArgs b xv.pos (bytesizeToNeq size) p.cx.boolType 0 none
          #[zc, x]
        let ft := ft.initLimitForNewValue p.cx f check
        let f := f.resetValue v .CondSelect
        (f.addArgs v #[y, zc, check], ft)

/-- `ft.simplifyValue(b, v)`. -/
def simplifyValue (st : St) (b v : ID) : St :=
  let (f, ft) := st
  let xv := f.getV v
  match xv.op with
  | .Slicemask =>
    let cap := xv.args[0]!
    let toConst (f : Func) : Func :=
      let f := f.resetValue v (if p.cx.size xv.type == 8 then .Const64 else .Const32)
      f.modV v fun y => { y with auxInt := -1 }
    match isConstDelta f cap with
    | some (x, delta) => if (ft.lim x).umin > (-delta).toUInt64 then (toConst f, ft) else st
    | none => if (ft.lim cap).umin > 0 then (toConst f, ft) else st
  | .Ctz8 | .Ctz16 | .Ctz32 | .Ctz64 =>
    let lim := ft.lim xv.args[0]!
    if lim.umin > 0 || lim.min > 0 || lim.max < 0 then
      (f.modV v fun y => { y with op := ctzNonZeroOp y.op }, ft)
    else st
  | .Div8 | .Div16 | .Div32 | .Div64 | .Mod8 | .Mod16 | .Mod32 | .Mod64 =>
    let pl := ft.lim xv.args[0]!
    let ql := ft.lim xv.args[1]!
    if pl.nonnegative && ql.nonnegative then
      (f.modV v fun y => { y with op := unsignedOp y.op, auxInt := 0 }, ft)
    else if xv.op != .Div8 && xv.op != .Mod8 &&
        (ql.max < -1 || ql.min > -1 || pl.min > mostNegativeDividend xv.op) &&
        (p.cx.arch == "386" || p.cx.arch == "amd64") then
      (f.modV v fun y => { y with auxInt := 1 }, ft)
    else st
  | .Mul64 | .Mul32 | .Mul16 | .Mul8 => simplifyMul p st b v
  | .Eq64 | .Eq32 | .Eq16 | .Eq8 | .Neq64 | .Neq32 | .Neq16 | .Neq8 =>
    let a0 := xv.args[0]!
    let a1 := xv.args[1]!
    let c? : Option (ID × Nat × Int64) :=
      match (ft.lim a0).constValue, (ft.lim a1).constValue with
      | some _, some _ => none
      | some c, none => some (a1, 0, c)
      | none, some c => some (a0, 1, c)
      | none, none => none
    match c? with
    | none => st
    | some (x, yPos, yConst) =>
      if yConst != 1 || (ft.lim x).umax > 1 then st else
      let ((f, ft), zc) := zeroConst p st (bytesizeToConst (p.cx.size (f.getV x).type))
        (f.getV x).type
      let f := f.modV v fun y => { y with op := invertEqNeqOp y.op }
      (f.setArg v yPos zc, ft)
  | .And64 | .And32 | .And16 | .And8 =>
    match constSide ft xv.args[0]! xv.args[1]! with
    | none => st
    | some (x, yConst) =>
      let (knownBits, fixedLen) := (ft.lim x).unsignedFixedLeadingBits
      let wantBits := knownBits ||| (shl 1 (64 - fixedLen) - 1)
      if wantBits &&& yConst.toUInt64 != wantBits then st else (f.copyOf v x, ft)
  | .Or64 | .Or32 | .Or16 | .Or8 =>
    match constSide ft xv.args[0]! xv.args[1]! with
    | none => st
    | some (x, yConst) =>
      let (wantBits, _) := (ft.lim x).unsignedFixedLeadingBits
      if wantBits ||| yConst.toUInt64 != wantBits then st else (f.copyOf v x, ft)
  | op =>
    if isRshSigned op then
      let f := if ft.isNonNegative xv.args[0]! then
          f.modV v fun y => { y with op := unsignedOp y.op } else f
      shiftBounded p (f, ft) v
    else if isLshOrRshU op then shiftBounded p st v
    else st

/-- `ft.constantFoldArguments(v)` (T3). -/
def constantFoldArguments (st : St) (v : ID) : St := Id.run do
  let mut (f, ft) := st
  let n := (f.getV v).args.size
  for i in [0:n] do
    let arg := (f.getV v).args[i]!
    let some cv := (ft.lim arg).constValue | continue
    let av := f.getV arg
    match av.op with
    | .Const64 | .Const32 | .Const16 | .Const8 | .ConstBool | .ConstNil => continue
    | _ => pure ()
    let t := av.type
    let size := p.cx.size t
    let eq := p.cx.sameType
    let r? : Option (Func × ID) :=
      if p.cx.isBool t then some (f.constBool eq t (cv != 0))
      else if p.cx.isInteger t && size == 1 then some (f.constInt8 eq t cv.toInt8)
      else if p.cx.isInteger t && size == 2 then some (f.constInt16 eq t cv.toInt16)
      else if p.cx.isInteger t && size == 4 then some (f.constInt32 eq t cv.toInt32)
      else if p.cx.isInteger t && size == 8 then some (f.constInt64 eq t cv)
      else if p.cx.isPtrShaped t then (if cv == 0 then some (f.constNil eq t) else none)
      else none
    let some (f', c) := r? | continue
    f := f'.setArg v i c
    ft := ft.initLimitForNewValue p.cx f c
  return (f, ft)

/-- `removeBranch(b, branch)`. -/
def removeBranch (f : Func) (b : ID) (br : Branch) : Func :=
  let bb := f.getB b
  let f := match bb.controls[0]? with
    | some c =>
      let cp := (f.getV c).pos
      if cp.isStmt == Pos.isStmtMark && cp.sameFileAndLine bb.pos then
        f.modB b fun x => { x with pos := x.pos.withIsStmt }
      else f
    | none => f
  match br with
  | .positive => ((f.modB b fun x => { x with kind := .First }).resetControls b).swapSuccessors b
  | .negative => (f.modB b fun x => { x with kind := .First }).resetControls b
  | _ => f

/-- `ft.simplifyBlock(sdom, b)` (T16). -/
def simplifyBlock (isAncestorEq : ID → ID → Bool) (st : St) (b : ID) : St := Id.run do
  let (f, ft) := st
  if (f.getB b).kind != .If then return st
  let mut f := f
  let mut ft := ft
  for (i, br) in [(0, Branch.positive), (1, Branch.negative)] do
    let child := (f.getB b).succs[i]!.b
    if getBranch isAncestorEq f (some b) child != .unknown then continue
    let ft1 := p.addBranchRestrictions f ft.checkpoint b br
    let unsat := ft1.unsat
    ft := ft1.restore
    if unsat then
      f := removeBranch f b br
      break
  return (f, ft)

/-- `getDependencyScore(scores, v)` for the values of one block, memoised in `scores`
(`fuel` bounds the depth: same-block arguments of non-phis are acyclic). -/
def depScore (f : Func) : Nat → Std.TreeMap ID Nat → ID → Std.TreeMap ID Nat × Nat
  | 0, scores, _ => (scores, 0)
  | fuel + 1, scores, v =>
    match scores.get? v with
    | some s => (scores, s)
    | none =>
      let x := f.getV v
      if x.op == .Phi then (scores.insert v 1, 1) else
      let (scores, s) := x.args.foldl (init := (scores, 2)) fun (scores, s) a =>
        if (f.getV a).block != x.block then (scores, s) else
        let (scores, sa) := depScore f fuel scores a
        (scores, max s (sa + 1))
      (scores.insert v s, s)

/-- `ft.topoSortValuesInBlock(b)` (T2): sort `b.Values` by (dependency score, ID); the key is
unique, so any correct sort gives Go's order. -/
def topoSortValuesInBlock (f : Func) (b : ID) : Func :=
  let vs := (f.getB b).values
  let fuel := vs.size + 1
  let (_, keyed) := vs.foldl (init := (({} : Std.TreeMap ID Nat), (#[] : Array (Nat × ID))))
    fun (scores, acc) v =>
      let (scores, s) := depScore f fuel scores v
      (scores, acc.push (s, v))
  let sorted := GoFV.Util.PdqSort.sortBy (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) keyed
  f.modB b fun x => { x with values := sorted.map (·.2) }

end GoFV.Opt.Prove
