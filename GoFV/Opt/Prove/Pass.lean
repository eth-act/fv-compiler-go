import GoFV.Opt.Prove.Simplify
import GoFV.Opt.Prove.Downward

/-!
# prove: the pass (`prove.go:1573-1738`)

1. Induction variables (`findIndVar`); those used only for counting are rewritten into
   downward counting loops, the others are recorded per entry block.
2. The facts table, with every live `SliceLen`/`SliceCap` of a slice set equal to its first.
3. A walk of the dominator tree with an explicit stack: on descent, checkpoint and add the
   facts of the induction variables, of the dominating branch and of same-length slices; an
   unsatisfiable block is cut off (`removeBranch`) and its subtree skipped; otherwise its values
   are sorted (T2) and visited (`flowLimit`, `constantFoldArguments`, `addValueFact`,
   `simplifyValue`), its branch simplified, and a restore entry pushed before its dominator-tree
   children (so siblings are visited in reverse child-list order).

`f.Idom()`/`f.Sdom()` come from the CFG cache (prove never invalidates it).
-/

namespace GoFV.Opt.Prove

open GoFV.SSA GoFV.SSA.Analysis

/-- Reject functions whose value types prove needs the size of but the export does not have. -/
def checkSizes (cx : Ctx) (f : Func) : Except String Unit := do
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      let i := cx.info x.type
      if (i.isBool || i.isInteger || i.isPtrShaped) && i.size?.isNone then
        throw s!"prove: v{v}: size of t{x.type} not calculated"
      if x.op == .SliceLen || x.op == .SliceCap then
        let a := cx.info (f.getV x.args[0]!).type
        if a.elemSize?.isNone then
          throw s!"prove: v{v}: slice element size of t{(f.getV x.args[0]!).type} unknown"

/-- `prove`'s first loop: induction variables. -/
def proveIndVars (cx : Ctx) (f : Func) : Except String (Std.HashMap ID (Array IndVar) × Func) := do
  let (ivs, f) := findIndVar cx f
  let mut f := f
  let mut indVars : Std.HashMap ID (Array IndVar) := {}
  for v in ivs do
    if (f.getV v.ind).args.size != 2 then throw "prove: unexpected induction with too many parents"
    if !((f.getV v.ind).uses == 2 && (f.getV v.nxt).uses == 1) then
      indVars := indVars.insert v.entry ((indVars.getD v.entry #[]).push v)
      continue
    f ← maybeRewriteLoopToDownwardCountingLoop cx f v
  return (indVars, f)

/-- `prove`'s second loop: lengths and capacities of the same slice are equal. -/
def proveLensCaps (p : Prover) (f : Func) (ft : FactsTable) : FactsTable := Id.run do
  let mut ft := { ft with lens := Array.replicate (f.vidLast + 1) 0,
                          caps := Array.replicate (f.vidLast + 1) 0 }
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      if x.uses == 0 then continue
      if x.op == .SliceLen then
        let s := x.args[0]!
        let l := ft.len? s
        if l != 0 then ft := p.update f ft v l dSigned rEq
        else ft := { ft with lens := ft.lens.set! s v }
      else if x.op == .SliceCap then
        let s := x.args[0]!
        let c := ft.cap? s
        if c != 0 then ft := p.update f ft v c dSigned rEq
        else ft := { ft with caps := ft.caps.set! s v }
  return ft

/-- Visit block `b` on descent (its facts are already in the table): T2, the values, T16. -/
def proveVisit (p : Prover) (isAnc : ID → ID → Bool) (st : St) (b : ID) : St := Id.run do
  let (f, ft) := st
  let f := topoSortValuesInBlock f b
  let mut st := (f, ft)
  for v in (f.getB b).values do
    let (f, ft) := st
    let ft := flowLimit p f ft v
    let st' := constantFoldArguments p (f, ft) v
    let (f, ft) := st'
    let ft := addValueFact p f ft v
    st := simplifyValue p (f, ft) b v
  simplifyBlock p isAnc st b

/-- The dominator-tree walk. -/
def proveWalk (p : Prover) (indVars : Std.HashMap ID (Array IndVar)) (idom : Array (Option ID))
    (sdom : SparseTree) (st : St) : St := Id.run do
  let isAnc := sdom.isAncestorEq
  let (f, _) := st
  -- (block, descend?) pairs
  let mut work : Array (ID × Bool) := #[(f.entry, true)]
  let mut st := st
  for _ in [0:2 * (f.bidLast + 1) + 2] do
    let some (b, descend) := work.back? | break
    work := work.pop
    let (f, ft) := st
    let parent := (idom[b]?).join
    let branch := getBranch isAnc f parent b
    if !descend then
      st := (f, ft.restore)
      continue
    let mut ft := ft.checkpoint
    for iv in indVars.getD b #[] do
      ft := addIndVarRestrictions p f ft iv
    if branch != .unknown then
      ft := p.addBranchRestrictions f ft (parent.getD 0) branch
    ft := addSlicesOfSameLen p f ft b
    if ft.unsat then
      let f := match parent with
        | some pb => removeBranch f pb branch
        | none => f
      st := (f, ft.restore)
      continue
    st := proveVisit p isAnc (f, ft) b
    work := work.push (b, false)
    let mut s := sdom.child b
    for _ in [0:sdom.size + 1] do
      let some c := s | break
      work := work.push (c, true)
      s := sdom.sibling c
  return st

/-- `prove(f)`. -/
def prove (p : Prover) (f : Func) : Except String Func := do
  checkSizes p.cx f
  let (indVars, f) ← proveIndVars p.cx f
  let ft := (FactsTable.new p.cx f).checkpoint
  let ft := proveLensCaps p f ft
  let (idom, f) := f.idom
  let (sdom, f) := f.sdom
  let (f, ft) := proveWalk p indVars idom sdom (f, ft)
  let ft := ft.restore
  if let some e := ft.err then throw e
  return f

end GoFV.Opt.Prove

namespace GoFV.Opt

/-- The `prove` pass. -/
def provePass : Pass := Pass.ofFunc fun env f => do
  let p ← Prove.Prover.ofEnv env
  Prove.prove p f

end GoFV.Opt
