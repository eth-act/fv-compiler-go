import GoFV.SSA.Alloc

/-!
# CFG edge primitives

Verbatim ports of `block.go:269-380` (`AddEdgeTo`, `removePred`, `removeSucc`,
`swapSuccessors`, `swapSuccessorsByIdx`, `removePhiArg`), `phielimValue` (`copyelim.go:124`,
called by `removePhiArg`) and `Block.removeEdge` (`deadcode.go:311`). Removal is
swap-with-last, so it permutes `Preds`/`Succs` and phi arguments exactly as Go does.
`AddEdgeTo`, `removePred` and `removeSucc` invalidate the CFG caches; the `swapSuccessors*`
do **not** (`docs/PASSES.md` §1.3: a later pass can see a stale postorder).
-/

namespace GoFV.SSA.Func

/-- `b.AddEdgeTo(c)`. -/
def addEdgeTo (f : Func) (b c : ID) : Func :=
  let i := (f.getB b).succs.size
  let j := (f.getB c).preds.size
  let f := f.modB b fun x => { x with succs := x.succs.push ⟨c, j⟩ }
  let f := f.modB c fun x => { x with preds := x.preds.push ⟨b, i⟩ }
  f.invalidateCFG

/-- `b.removePred(i)`: swap-remove `b.Preds[i]`, fixing the moved edge's back index. The
caller removes the successor edge and the phi arguments. -/
def removePred (f : Func) (b : ID) (i : Nat) : Func :=
  let ps := (f.getB b).preds
  let n := ps.size - 1
  let f := if i != n then
      let e := ps[n]!
      let f := f.modB b fun x => { x with preds := x.preds.set! i e }
      f.modB e.b fun x => { x with succs := x.succs.modify e.i fun s => { s with i } }
    else f
  (f.modB b fun x => { x with preds := x.preds.pop }).invalidateCFG

/-- `b.removeSucc(i)`: swap-remove `b.Succs[i]`, fixing the moved edge's back index. -/
def removeSucc (f : Func) (b : ID) (i : Nat) : Func :=
  let ss := (f.getB b).succs
  let n := ss.size - 1
  let f := if i != n then
      let e := ss[n]!
      let f := f.modB b fun x => { x with succs := x.succs.set! i e }
      f.modB e.b fun x => { x with preds := x.preds.modify e.i fun p => { p with i } }
    else f
  (f.modB b fun x => { x with succs := x.succs.pop }).invalidateCFG

/-- `b.swapSuccessors()`: exchange the two successors and negate `Likely` (no CFG cache
invalidation). -/
def swapSuccessors (f : Func) (b : ID) : Func :=
  let ss := (f.getB b).succs
  let e0 := ss[0]!
  let e1 := ss[1]!
  let f := f.modB b fun x => { x with succs := #[e1, e0] }
  let f := f.modB e0.b fun x => { x with preds := x.preds.modify e0.i fun p => { p with i := 1 } }
  let f := f.modB e1.b fun x => { x with preds := x.preds.modify e1.i fun p => { p with i := 0 } }
  f.modB b fun x => { x with likely := x.likely.neg }

/-- `b.swapSuccessorsByIdx(x, y)` (no CFG cache invalidation, `Likely` unchanged). -/
def swapSuccessorsByIdx (f : Func) (b : ID) (x y : Nat) : Func :=
  if x == y then f else
  let ss := (f.getB b).succs
  let ex := ss[x]!
  let ey := ss[y]!
  let f := f.modB b fun k => { k with succs := (k.succs.set! x ey).set! y ex }
  let f := f.modB ex.b fun k => { k with preds := k.preds.modify ex.i fun p => { p with i := y } }
  f.modB ey.b fun k => { k with preds := k.preds.modify ey.i fun p => { p with i := x } }

/-- `phielimValue(v)` (`copyelim.go:124`): a phi whose arguments other than itself are all
one value `w` becomes `Copy w` (op set directly, type and position kept). Returns whether it
changed. -/
def phielimValue (f : Func) (v : ID) : Func × Bool :=
  let x := f.getV v
  if x.op != .Phi then (f, false) else
  -- `none`: no candidate yet; `some (some w)`: the one candidate; `some none`: two distinct
  let w : Option (Option ID) := x.args.foldl (init := none) fun w a =>
    if a == v then w else
    match w with
    | none => some (some a)
    | some (some w') => if a == w' then w else some none
    | some none => w
  match w with
  | some (some w) => ((f.modV v fun y => { y with op := .Copy }).setArgs1 v w, true)
  | _ => (f, false)

/-- `b.removePhiArg(phi, i)`: after `b.removePred(i)`, swap-remove the phi's `i`th argument,
then `phielimValue(phi)`. -/
def removePhiArg (f : Func) (b phi : ID) (i : Nat) : Func :=
  let n := (f.getB b).preds.size
  let args := (f.getV phi).args
  let f := (f.decUses args[i]!).modV phi fun x => { x with args := (x.args.set! i args[n]!).pop }
  (f.phielimValue phi).1

/-- `b.removeEdge(i)` (`deadcode.go:311`): remove `b.Succs[i]`, the matching predecessor
edge of its target `c`, and the matching argument of each of `c`'s phis (which may become
copies). -/
def removeEdge (f : Func) (b : ID) (i : Nat) : Func :=
  let e := (f.getB b).succs[i]!
  let c := e.b
  let j := e.i
  let f := (f.removeSucc b i).removePred c j
  (f.getB c).values.foldl (init := f) fun f v =>
    if (f.getV v).op == .Phi then f.removePhiArg c v j else f

end GoFV.SSA.Func
