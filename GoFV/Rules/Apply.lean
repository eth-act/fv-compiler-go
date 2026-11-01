import GoFV.Rules.Interp
import GoFV.Opt.CopyElim
import GoFV.SSA.Edges
import GoFV.SSA.TypePred

/-!
# The rewrite driver (`rewrite.go: applyRewrite`)

`applyRewrite t removeDead` is `applyRewrite(f, rewriteBlock<file>, rewriteValue<file>,
deadcode)` (`rewrite.go:41-232`, docs/contracts/rules.md "The fixpoint loop"): sweeps over
`f.Blocks` × `b.Values` (the value list as it was when the block's sweep started) until nothing
changes; per block, copy controls are followed and the block rules tried; per value, unused
removable values are reset to `OpInvalid` (when `removeDead`), phis eliminated, copy arguments
replaced by their source (unused copies invalidated recursively) and the value rules tried,
with Go's statement-mark moves; finally every `OpInvalid` value is freed, in block and value
order, and pending statement marks are settled.

Go detects rewrite cycles by hashing the function after `max(NumBlocks, 20)` iterations and
aborts compilation on a repeat; the port aborts after `iterFuel` iterations instead (no
function the compiler accepted cycles).
-/

namespace GoFV.Rules

open GoFV.SSA

namespace Apply

open RwM

/-- Bound on fixpoint iterations (Go's cycle detection aborts on cycles; see the module doc). -/
def iterFuel : Nat := 100000

/-- `isPoorStatementOp(op)` (`numberlines.go:13`). -/
def isPoorStatementOp : Op → Bool
  | .Addr | .LocalAddr | .OffPtr | .StructSelect | .Phi | .ITab | .IData | .IMake | .StringMake
  | .SliceMake | .StructMake | .ConstBool | .Const8 | .Const16 | .Const32 | .Const64
  | .Const32F | .Const64F | .SB | .SP | .ArgIntReg | .ArgFloatReg => true
  | _ => false

/-- `nextGoodStatementIndex(v, i, b)` (`numberlines.go:31`), over the current `b.Values`. -/
def nextGoodStatementIndex (f : Func) (v : Value) (i : Nat) (vals : Array ID) : Nat := Id.run do
  if i + 1 ≥ vals.size then return i
  if !isPoorStatementOp v.op then return i
  for j in [i + 1:vals.size] do
    let u := f.getV vals[j]!
    if u.pos.isStmt == Pos.notStmt then continue
    if u.pos.sameFileAndLine v.pos then
      if isPoorStatementOp u.op then continue
      return j
    return i
  return i

/-- `pendingLines.set(p, b)`. -/
def pendingSet (p : Pos) (b : ID) : RwM Unit := do
  let s ← get
  match s.pending with
  | none => throw "applyRewrite: f.cachedLineStarts is nil"
  | some m =>
    match m.set p b with
    | .ok m => set { s with pending := some m }
    | .error e => throw e

def pendingGet (p : Pos) : RwM (Option Int) := do
  match (← get).pending with
  | none => throw "applyRewrite: f.cachedLineStarts is nil"
  | some m => return m.get p

def pendingRemove (p : Pos) : RwM Unit :=
  modify fun s => { s with pending := s.pending.map (·.remove p) }

@[inline] def setPos (v : ID) (p : Pos) : RwM Unit :=
  modF fun f => f.modV v fun x => { x with pos := p }

/-- Copy-argument elimination for `v` (`rewrite.go:110-153`); true if an argument changed. -/
def elimCopyArgs (v : ID) : RwM Bool := do
  let mut changed := false
  let n := (← val v).args.size
  for i in [0:n] do
    let a := (← val v).args[i]!
    let ax ← val a
    if ax.op != .Copy then continue
    let aa ← modFGet fun f => GoFV.Opt.copySource f a
    modF fun f => f.setArg v i aa
    logEv fun _ => .copyArg v i aa
    let ax ← val a
    if ax.pos.isStmt == Pos.isStmtMark then
      let aax ← val aa
      let vx ← val v
      if aax.block == ax.block && aax.pos.line == ax.pos.line && aax.pos.isStmt != Pos.notStmt then
        setPos aa aax.pos.withIsStmt
      else if vx.block == ax.block && vx.pos.line == ax.pos.line && vx.pos.isStmt != Pos.notStmt then
        setPos v vx.pos.withIsStmt
      else
        pendingSet ax.pos ax.block
      setPos a ax.pos.withNotStmt
    changed := true
    let mut a := a
    for _ in [0:(← getF).vidLast + 1] do
      let x ← val a
      if x.uses != 0 then break
      let next := x.args[0]!
      reset a .Invalid
      a := next
  return changed

/-- One sweep over `f.Blocks`; returns `(change, deadChange)`. -/
def sweep (t : Interp.Table) (removeDead : Bool) (mem void : TypeRef) : RwM (Bool × Bool) := do
  let mut change := false
  let mut deadChange := false
  let blocks := (← getF).blocks
  for b in blocks do
    -- follow copy controls
    let nc := (← blk b).controls.size
    for i in [0:nc] do
      let mut c := (← blk b).controls[i]!
      for _ in [0:(← getF).vidLast + 1] do
        let cx ← val c
        if cx.op != .Copy then break
        c := cx.args[0]!
        modF fun f => f.replaceControl b i c
        logEv fun _ => .control b i c
    if ← Interp.rewriteBlock t b then change := true
    let vals := (← blk b).values
    for j in [0:vals.size] do
      let v := vals[j]!
      let x ← val v
      if x.uses == 0 && (← tables).removeable mem void x then
        if x.op != .Invalid && removeDead then
          reset v .Invalid
          deadChange := true
        continue
      let mut vchange ← modFGet fun f => f.phielimValue v
      if vchange && (← get).log.isSome then
        let x ← val v
        logEv fun _ => .phielim v x
      if ← elimCopyArgs v then vchange := true
      if ← Interp.rewriteValue t v then
        vchange := true
        let x ← val v
        if x.pos.isStmt == Pos.isStmtMark then
          let f ← getF
          let cur := (f.getB b).values
          let k := nextGoodStatementIndex f x j cur
          if k != j then
            setPos v x.pos.withNotStmt
            let w := cur[k]!
            setPos w (f.getV w).pos.withIsStmt
      change := change || vchange
  return (change, deadChange)

/-- The final sweep: free `OpInvalid` values, settle pending statement marks. -/
def cleanup : RwM Unit := do
  for b in (← getF).blocks do
    let vals := (← blk b).values
    let mut kept : Array ID := #[]
    for v in vals do
      let x ← val v
      if x.op == .Invalid then
        if x.pos.isStmt == Pos.isStmtMark then pendingSet x.pos b
        modF fun f => f.freeValue v
        continue
      if x.pos.isStmt != Pos.notStmt && !x.op.notStmtBoundary then
        if (← pendingGet x.pos) == some (b : Int) then
          pendingRemove x.pos
          setPos v x.pos.withIsStmt
      kept := kept.push v
    let bx ← blk b
    if (← pendingGet bx.pos) == some (b : Int) then
      let p := bx.pos.withIsStmt
      modF fun f => f.modB b fun y => { y with pos := p }
      pendingRemove p
    modF fun f => f.modB b fun y => { y with values := kept }

/-- `applyRewrite(f, rb, rv, deadcode)` with the rule table `t`. -/
def applyRewrite (t : Interp.Table) (removeDead : Bool) : RwM Unit := do
  match (← get).pending with
  | none => throw "applyRewrite: f.cachedLineStarts is nil"
  | some m => modify fun s => { s with pending := some m.clear }
  let mem ← typ "Mem"
  let void ← typ "Void"
  let mut done := false
  for _ in [0:iterFuel] do
    let (change, deadChange) ← sweep t removeDead mem void
    if !change && !deadChange then
      done := true
      break
  if !done then throw "rewrite cycle detected"
  cleanup

end Apply

end GoFV.Rules
