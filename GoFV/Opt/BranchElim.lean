import GoFV.Opt.Pass
import GoFV.Opt.Speculate
import GoFV.Opt.CanCondSelect
import GoFV.Opt.BranchElimCheck
import GoFV.Opt.NumberLines
import GoFV.SSA.TypePred
import GoFV.SSA.Analysis.CfgCache

/-!
# branchelim (`branchelim.go`)

Only when `Config.haveCondSelect` (`docs/PASSES.md`, branchelim):

1. `loadAddr`: the values used to compute a load address — `Args[0]` of the loads, `Args[1]` of
   `Move`, then (fixpoint over the cached `f.postorder()`) the integer/pointer arguments of
   members. Only membership is observable.
2. Repeat over `f.Blocks` until nothing changes: `elimIf(b) || elimIfElse(b)`. Each turns the
   phis of a diamond's join block into `CondSelect`s (in place, arguments swapped by the edge
   order, the `If` control appended), splices the join block's kind, controls, aux and
   successors into the `If` block, appends the arm and join values to it (dom, simple, post /
   b, yes, no, post), clobbers the merged blocks (`BlockInvalid`, left in `f.Blocks`) and
   invalidates the CFG caches. `elimIf` also moves the merged blocks' statement marks.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace BranchElim

/-- What the rewrites read besides the function. -/
structure Ctx where
  tabs : Tables
  isMem : TypeRef → Bool
  arch : String
  regSize : Int
  loadAddr : Array Bool

/-- `isLeafPlain(b)`. -/
@[inline] def isLeafPlain (f : Func) (b : ID) : Bool :=
  let x := f.getB b
  x.kind == .Plain && x.preds.size == 1

/-- `clobberBlock(b)`. -/
def clobberBlock (f : Func) (b : ID) : Func :=
  let f := f.modB b fun x => { x with values := #[], preds := #[], succs := #[], aux := none }
  (f.resetControls b).modB b fun x => { x with likely := .unknown, kind := .Invalid }

/-- `post` has phis and every one passes `canCondSelect`. -/
def phisOk (c : Ctx) (f : Func) (post : ID) : Except String Bool := do
  let mut hasphis := false
  for v in (f.getB post).values do
    if (f.getV v).op == .Phi then
      hasphis := true
      if !(← canCondSelect c.tabs c.regSize c.arch f v (c.loadAddr.getD v false)) then
        return false
  return hasphis

/-- The phis of `post` become `CondSelect`s of `ctrl` (arguments swapped if `swap`). -/
def phisToCondSelect (f : Func) (post ctrl : ID) (swap : Bool) : Func :=
  (f.getB post).values.foldl (init := f) fun f v =>
    if (f.getV v).op != .Phi then f else
    let f := f.modV v fun x =>
      { x with op := .CondSelect,
               args := if swap then (x.args.swapIfInBounds 0 1) else x.args }
    f.addArg v ctrl

/-- Give `dom` the kind, controls, aux and successors of `post` (retargeting the successors'
predecessor edges), and move the values of `blocks` (in order) to the end of `dom`. -/
def splice (f : Func) (dom post : ID) (blocks : Array ID) : Func := Id.run do
  let p := f.getB post
  let mut f := f.modB dom fun x => { x with kind := p.kind }
  f := f.copyControls dom post
  f := f.modB dom fun x => { x with aux := p.aux, succs := p.succs }
  for e in p.succs do
    f := f.modB e.b fun x => { x with preds := x.preds.modify e.i fun pe => { pe with b := dom } }
  for b in blocks do
    for v in (f.getB b).values do
      f := f.modV v fun x => { x with block := dom }
  return f

/-- Append the values of `blocks` to `dom.Values`. -/
def appendValues (f : Func) (dom : ID) (blocks : Array ID) : Func :=
  let vs := blocks.foldl (fun acc b => acc ++ (f.getB b).values) (f.getB dom).values
  f.modB dom fun x => { x with values := vs }

@[inline] def isStmtPos (p : Pos) : Bool := p.isStmt == Pos.isStmtMark

/-- `findBlockPos(b)`. -/
def findBlockPos (f : Func) (b : ID) : Bool :=
  let x := f.getB b
  x.values.any fun v => let p := (f.getV v).pos; x.pos.sameFileAndLine p && isStmtPos p

/-- `setBlockPos(b)`. -/
def setBlockPos (f : Func) (b : ID) : Func × Bool :=
  let x := f.getB b
  match x.values.find? fun v =>
      let y := f.getV v; x.pos.sameFileAndLine y.pos && !NumberLines.isPoorStatementOp y.op with
  | some v => (f.modV v fun y => { y with pos := y.pos.withIsStmt }, true)
  | none => (f, false)

/-- The statement-mark preservation of `elimIf` (`branchelim.go:196-276`), after the splice. -/
def moveStmts (f : Func) (dom simple post : ID) : Func := Id.run do
  let simplePos := (f.getB simple).pos
  let postPos := (f.getB post).pos
  let mut simpleStmt := isStmtPos simplePos
  let mut postStmt := isStmtPos postPos
  let mut f := f
  if simpleStmt then
    simpleStmt := !findBlockPos f simple
    if !simpleStmt && simplePos.sameFileAndLine postPos then postStmt := false
  if postStmt then postStmt := !findBlockPos f post
  if simpleStmt then
    let (f', ok) := setBlockPos f simple
    f := f'
    if ok && simplePos.sameFileAndLine postPos then postStmt := false
  if postStmt then
    let (f', ok) := setBlockPos f post
    f := f'
    postStmt := !ok
  if postStmt then
    let d := f.getB dom
    if !isStmtPos d.pos then
      f := f.modB dom fun x => { x with pos := postPos }
    else if d.succs.size == 1 && (f.getB d.succs[0]!.b).preds.size == 1 then
      let succ := d.succs[0]!.b
      for v in (f.getB succ).values do
        let y := f.getV v
        if NumberLines.isPoorStatementOp y.op then continue
        if postPos.sameFileAndLine y.pos then
          f := f.modV v fun y => { y with pos := y.pos.withIsStmt }
        postStmt := false
        break
      if postStmt && !isStmtPos (f.getB succ).pos then
        f := f.modB succ fun x => { x with pos := postPos }
  return f

/-- `elimIf(f, loadAddr, dom)`: the rewritten function, or `none`. -/
def elimIf (c : Ctx) (f : Func) (dom : ID) : Except String (Option Func) := do
  let d := f.getB dom
  if d.kind != .If || d.likely != .unknown then return none
  let mut found : Option (ID × ID) := none
  for h : i in [0:d.succs.size] do
    let bb := d.succs[i].b
    let other := d.succs[i ^^^ 1]!.b
    if isLeafPlain f bb && (f.getB bb).succs[0]!.b == other then
      found := some (bb, other)
      break
  let some (simple, post) := found | return none
  if (f.getB post).preds.size != 2 || post == dom then return none
  if !(← phisOk c f post) then return none
  if (f.getB simple).values.size > 2 || !canSpeculativelyExecute c.isMem f simple then
    return none
  let swap := ((f.getB post).preds[0]!.b == dom) != (d.succs[0]!.b == post)
  let mut f := phisToCondSelect f post d.controls[0]! swap
  f := splice f dom post #[simple, post]
  f := moveStmts f dom simple post
  f := appendValues f dom #[simple, post]
  f := clobberBlock (clobberBlock f post) simple
  return some f.invalidateCFG

/-- `shouldElimIfElse(no, yes, post, arch)`. -/
def shouldElimIfElse (f : Func) (no yes post : ID) (arch : String) : Bool :=
  if arch != "amd64" then true else
  let (phi, other) := (f.getB post).values.foldl (init := (0, 0)) fun (phi, other) v =>
    let x := f.getV v
    let phi := if x.op == .Phi then phi + 1 else phi
    let other := x.args.foldl (init := other) fun o a =>
      let ab := (f.getV a).block
      if ab == no || ab == yes then o + 1 else o
    (phi, other)
  let cost := phi + (if phi > 1 then other else 0)
  cost < 2

/-- `elimIfElse(f, loadAddr, b)`. -/
def elimIfElse (c : Ctx) (f : Func) (b : ID) : Except String (Option Func) := do
  let x := f.getB b
  if x.kind != .If || x.likely != .unknown then return none
  let yes := x.succs[0]!.b
  let no := x.succs[1]!.b
  let armOk (a : ID) : Bool :=
    isLeafPlain f a && (f.getB a).values.size ≤ 1 && canSpeculativelyExecute c.isMem f a
  if !armOk yes || !armOk no then return none
  let post := (f.getB yes).succs[0]!.b
  if post != (f.getB no).succs[0]!.b then return none
  if (f.getB post).preds.size != 2 || post == b then return none
  if !(← phisOk c f post) then return none
  if !shouldElimIfElse f no yes post c.arch then return none
  let swap := (f.getB post).preds[0]!.b != yes
  let mut f := phisToCondSelect f post x.controls[0]! swap
  f := splice f b post #[post, yes, no]
  f := appendValues f b #[yes, no, post]
  f := clobberBlock (clobberBlock (clobberBlock f yes) no) post
  return some f.invalidateCFG

/-- The `loadAddr` set (`branchelim.go:31-62`), by value ID. -/
def loadAddrSet (tabs : Tables) (f : Func) (po : Array ID) : Except String (Array Bool) := do
  let mut s := Array.replicate (f.vidLast + 1) false
  let mut n := 0
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      let a? : Option ID := match x.op with
        | .Load | .AtomicLoad8 | .AtomicLoad32 | .AtomicLoad64 | .AtomicLoadPtr
        | .AtomicLoadAcq32 | .AtomicLoadAcq64 => some x.args[0]!
        | .Move => some x.args[1]!
        | _ => none
      if let some a := a? then
        if !s.getD a false then s := s.set! a true; n := n + 1
  -- each round that does not stop adds a value
  for _ in [0:f.vidLast + 2] do
    let n0 := n
    for b in po do
      let vs := (f.getB b).values
      for k in [0:vs.size] do
        let v := vs[vs.size - 1 - k]!
        if !s.getD v false then continue
        for a in (f.getV v).args do
          let k ← Rules.Ty.kind tabs (f.getV a).type
          if Rules.Ty.isIntegerKind k || k == .PTR || k == .UNSAFEPTR then
            if !s.getD a false then s := s.set! a true; n := n + 1
    if n == n0 then break
  return s

/-- One sweep of the rewrite loop over `blocks`: at each block `elimIf`, else `elimIfElse`; a
rewrite is kept only if the step checker `stepOK` accepts it (`branchelim.go:65-68`, checked). -/
def sweep (c : Ctx) (ce : CheckEnv) : List ID → Func → Bool → Except String (Func × Bool)
  | [], f, change => pure (f, change)
  | b :: bs, f, change => do
    match (← elimIf c f b).filter (stepOK ce f · b) with
    | some f' => sweep c ce bs f' true
    | none =>
      match (← elimIfElse c f b).filter (stepOK ce f · b) with
      | some f' => sweep c ce bs f' true
      | none => sweep c ce bs f change

/-- Sweeps until nothing changes (at most `n`). -/
def rounds (c : Ctx) (ce : CheckEnv) : Nat → Func → Except String Func
  | 0, f => pure f
  | n + 1, f => do
    let (f', change) ← sweep c ce f.blocks.toList f false
    if change then rounds c ce n f' else pure f'

end BranchElim

/-- What the rewrites read: the configuration and the `loadAddr` set of `f` (with its cached
postorder `po`). -/
def BranchElim.ctxOf (env : PassEnv) (f : Func) (po : Array ID) : Except String BranchElim.Ctx := do
  let some mem := env.typ? "Mem" | throw "branchelim: no typ.Mem"
  let some #[.word arch] := env.config? "arch" | throw "branchelim: config arch"
  let some #[.word rs] := env.config? "regsize" | throw "branchelim: config regsize"
  let some regSize := decInt? rs | throw "branchelim: config regsize"
  let loadAddr ← BranchElim.loadAddrSet env.tables f po
  return { tabs := env.tables, isMem := env.tables.isMemory mem, arch, regSize, loadAddr }

open BranchElim in
/-- `branchelim(f)`, each rewrite checked (`BranchElim.stepOK`). -/
def branchelim (env : PassEnv) (f : Func) : Except String Func := do
  if !(← env.flag "havecondselect") then return f
  let (po, f) := f.postorder
  let c ← ctxOf env f po
  let ce : CheckEnv := { tabs := env.tables, typs := env.typs }
  -- the step checker's proof assumes a checked input (every corpus input passes)
  if !checkOK ce f then return f
  -- each successful rewrite clobbers at least one block of `f.Blocks`
  rounds c ce (f.blocks.size + 1) f

/-- The `branchelim` pass. -/
def branchelimPass : Pass := Pass.ofFunc branchelim

end GoFV.Opt
