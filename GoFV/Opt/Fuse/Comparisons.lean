import GoFV.Opt.Speculate
import GoFV.SSA.Edges

/-!
# Comparison fusion (`fuse_comparisons.go`)

`fuseIntInRange`, `fuseNanCheck`, `fuseSingleBitDifference` → `fuseComparisons`: an `If` block
`b` whose single predecessor `p` is an `If` sharing its true (`OrB`) or false (`AndB`)
successor, not bypassed according to `p.Likely`, with combinable controls and speculatively
executable values: `v = op(pc, bc)` (new value at `bc.Pos`, appended to `b`) becomes `b`'s
control; `p.removeEdge(i)`, `p` becomes `Plain`, `Likely = BranchUnknown`, controls reset.
-/

namespace GoFV.Opt.Fuse

open GoFV.SSA

/-- `getConstIntArgIndex(v)`: the first `Const8/16/32/64` argument. -/
def getConstIntArgIndex (f : Func) (v : Value) : Option Nat :=
  v.args.findIdx? fun a => match (f.getV a).op with
    | .Const8 | .Const16 | .Const32 | .Const64 => true
    | _ => false

def isSignedInequality : Op → Bool
  | .Less64 | .Less32 | .Less16 | .Less8 | .Leq64 | .Leq32 | .Leq16 | .Leq8 => true
  | _ => false

def isUnsignedInequality : Op → Bool
  | .Less64U | .Less32U | .Less16U | .Less8U | .Leq64U | .Leq32U | .Leq16U | .Leq8U => true
  | _ => false

/-- `canOptIntInRange(x, y, op)`. -/
def canOptIntInRange (f : Func) (x y : Value) (_op : Op) : Bool :=
  let check (p : Op → Bool) : Option Bool :=
    if !p x.op || !p y.op then none else
    match getConstIntArgIndex f x, getConstIntArgIndex f y with
    | some xi, some yi => some (x.args[xi ^^^ 1]! == y.args[yi ^^^ 1]!)
    | _, _ => some false
  match check isSignedInequality with
  | some r => r
  | none => (check isUnsignedInequality).getD false

/-- One `x` of `canOptNanCheck`'s loop: `some r` returns `r`, `none` continues. -/
def nanCheckOne (f : Func) (x y : Value) : Option Bool :=
  if x.args.size != 2 || x.args[0]! != x.args[1]! then none else
  let v := x.args[0]!
  let scan (lt le cst : Op) (signOk : Value → Bool) : Option Bool :=
    if y.op != lt && y.op != le then some false else
    let rec go : Nat → Option Bool
      | 0 => none
      | j + 1 =>
        let k := 1 - j
        let a := f.getV y.args[k]!
        let b := f.getV y.args[k ^^^ 1]!
        if a.op != cst then go j
        else if signOk b && b.args[0]! == v then some true
        else some (b.id == v)
    go 2
  match x.op with
  | .Neq64F => scan .Less64F .Leq64F .Const64F fun b => b.op == .Abs || b.op == .Neg64F
  | .Neq32F => scan .Less32F .Leq32F .Const32F fun b => b.op == .Neg32F
  | _ => none

/-- `canOptNanCheck(x, y, op)`. -/
def canOptNanCheck (f : Func) (x y : Value) (op : Op) : Bool :=
  if op != .OrB then false else
  match nanCheckOne f x y with
  | some r => r
  | none => (nanCheckOne f y x).getD false

/-- `oneBit(x)` (`rewrite.go:504`). -/
def oneBit (x : Int64) : Bool := x &&& (x - 1) == 0 && x != 0

/-- `canOptSingleBitDifference(x, y, op)`. -/
def canOptSingleBitDifference (f : Func) (x y : Value) (op : Op) : Bool :=
  if x.op != y.op then false else
  let opOk := match x.op with
    | .Eq64 | .Eq32 | .Eq16 | .Eq8 => some (op == .OrB)
    | .Neq64 | .Neq32 | .Neq16 | .Neq8 => some (op == .AndB)
    | _ => none
  match opOk with
  | some true =>
    match getConstIntArgIndex f x, getConstIntArgIndex f y with
    | some xi, some yi =>
      x.args[xi ^^^ 1]! == y.args[yi ^^^ 1]! &&
        oneBit ((f.getV x.args[xi]!).auxInt ^^^ (f.getV y.args[yi]!).auxInt)
    | _, _ => false
  | _ => false

/-- `fuseComparisons(b, canOptControls)`. -/
def fuseComparisons (isMem : TypeRef → Bool) (canOpt : Func → Value → Value → Op → Bool)
    (f : Func) (b : ID) : Func × Bool := Id.run do
  let bb := f.getB b
  if bb.preds.size != 1 then return (f, false)
  let p := bb.preds[0]!.b
  let pb := f.getB p
  if bb.kind != .If || pb.kind != .If then return (f, false)
  if pb.likely == .likely && pb.succs[0]!.b != b then return (f, false)
  if pb.likely == .unlikely && pb.succs[1]!.b != b then return (f, false)
  for (i, op) in [(0, Op.OrB), (1, Op.AndB)] do
    if pb.succs[i]!.b != bb.succs[i]!.b then continue
    let bc := f.getV bb.controls[0]!
    let pc := pb.controls[0]!
    if !canOpt f bc (f.getV pc) op then return (f, false)
    if !canSpeculativelyExecute isMem f b then return (f, false)
    let (f, v) := f.newValueArgs b bc.pos op bc.type (args := #[pc, bc.id])
    let f := f.setControl b v
    let f := f.removeEdge p i
    let f := f.modB p fun x => { x with kind := .Plain, likely := .unknown }
    return (f.resetControls p, true)
  return (f, false)

end GoFV.Opt.Fuse
