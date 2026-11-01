import GoFV.SSA.Alloc

/-!
# fuseBlockPlain (`fuse.go:189-343`)

Merge a maximal run `b … c` of `Plain` blocks whose interior blocks have single predecessors
(cycle-safe) into `c`: end-of-block statement marks move forward (comparing lines only), the
values of the run are concatenated in run order into `c.Values` (Go's choice of backing
storage does not change the order), `c.Preds := b.Preds` with the predecessors' successor edges
redirected, `f.Entry = c` if `b` was the entry, and `b … c` (exclusive) become `BlockInvalid`
with nil `Values`/`Preds`/`Succs`. Nothing is freed.
-/

namespace GoFV.Opt.Fuse

open GoFV.SSA

/-- Walk back from `b` to the earliest block of the run (`fuse.go:200-203`). -/
def runStart (f : Func) (c : ID) : Nat → ID → ID
  | 0, b => b
  | fuel + 1, b =>
    let x := f.getB b
    if h : x.preds.size = 1 then
      let p := x.preds[0].b
      if p != c && (f.getB p).kind == .Plain then runStart f c fuel p else b
    else b

/-- Walk forward from `c` to the latest block of the run (`fuse.go:205-219`). -/
def runEnd (f : Func) (b : ID) : Nat → ID → ID
  | 0, c => c
  | fuel + 1, c =>
    let x := f.getB c
    if x.kind != .Plain then c else
    let n := x.succs[0]!.b
    if n == b then c else
    if (f.getB n).preds.size != 1 then c else
    runEnd f b fuel n

/-- The run `b, b.Succs[0].b, …` up to and including `c`. -/
def runBlocks (f : Func) (c : ID) : Nat → ID → Array ID → Array ID
  | 0, _, acc => acc
  | fuel + 1, bx, acc =>
    if bx == c then acc.push bx else runBlocks f c fuel (f.getB bx).succs[0]!.b (acc.push bx)

/-- The scan of `moveEndStmt` over `next`'s values (`fuse.go:233-245`): the first statement
value on line `l` (the scan stops there and `l` becomes 0), else the final `l` and whether a
later statement line was met (`outOfOrder`). `f` does not change during the scan. -/
def endScan (f : Func) : Nat → Bool → List ID → Option ID × Nat × Bool
  | l, o, [] => (none, l, o)
  | l, o, v :: vs =>
    let p := (f.getV v).pos
    if p.isStmt == Pos.notStmt then endScan f l o vs
    else if l == p.line then (some v, 0, o)
    else endScan f l (o || decide (l < p.line)) vs

/-- Move the end-of-block statement mark of `bx` into `next` (`fuse.go:226-252`). -/
def moveEndStmt (f : Func) (bx next : ID) : Func :=
  let bpos := (f.getB bx).pos
  if bpos.isStmt != Pos.isStmtMark then f else
  let (hit, l, outOfOrder) := endScan f bpos.line false (f.getB next).values.toList
  let f := match hit with
    | some v =>
      let p := (f.getV v).pos
      f.modV v fun x => { x with pos := p.withIsStmt }
    | none => f
  let npos := (f.getB next).pos
  if l != 0 && !outOfOrder && (npos.line == l || npos.isStmt != Pos.isStmtMark) then
    f.modB next fun x => { x with pos := bpos.withIsStmt }
  else f

/-- The run `fuseBlockPlain f b` fuses, if it fires: its first block `b₀`, its last block `c`
and the run `b₀ … c` (`fuse.go:189-219`). -/
def plainRunOf (f : Func) (b : ID) : Option (ID × ID × Array ID) :=
  let bb := f.getB b
  if bb.kind != .Plain then none else
  let c := bb.succs[0]!.b
  if (f.getB c).preds.size != 1 || c == b then none else
  let fuel := f.blocks.size + 1
  let b := runStart f c fuel b
  let c := runEnd f b fuel c
  some (b, c, runBlocks f c fuel b #[])

/-- Every value of block `bx` now belongs to `c`. -/
def retagBlock (c bx : ID) (f : Func) : Func :=
  (f.getB bx).values.foldl (fun f v => f.modV v fun x => { x with block := c }) f

/-- Statement marks move forward, and every value of the run now belongs to `c`. -/
def retag (c : ID) (run : Array ID) (f : Func) : Func :=
  (List.range (run.size - 1)).foldl
    (fun f k => retagBlock c run[k]! (moveEndStmt f run[k]! run[k + 1]!)) f

/-- Replace the `b → c` edge with `preds(b) → c`: the predecessors' successor edges. -/
def redirectPreds (c : ID) (preds : Array Edge) (f : Func) : Func :=
  (List.range preds.size).foldl
    (fun f i => f.modB preds[i]!.b fun x => { x with succs := x.succs.set! preds[i]!.i ⟨c, i⟩ }) f

/-- The run's blocks but `c` become `BlockInvalid` with nil `Values`/`Preds`/`Succs`. -/
def killRun (run : Array ID) (f : Func) : Func :=
  (List.range (run.size - 1)).foldl
    (fun f k => f.modB run[k]! fun x =>
      { x with kind := .Invalid, values := #[], preds := #[], succs := #[] }) f

/-- Fuse the run `run` from `b` to `c`. -/
def fuseRun (f : Func) (b c : ID) (run : Array ID) : Func :=
  let f := retag c run f
  let vals := run.foldl (init := #[]) fun acc bx => acc ++ (f.getB bx).values
  let f := f.modB c fun x => { x with values := vals }
  let preds := (f.getB b).preds
  let f := f.modB c fun x => { x with preds }
  let f := redirectPreds c preds f
  let f := if f.entry == b then { f with entry := c } else f
  killRun run f

/-- `fuseBlockPlain(b)`. -/
def fuseBlockPlain (f : Func) (b : ID) : Func × Bool :=
  match plainRunOf f b with
  | none => (f, false)
  | some (b, c, run) => (fuseRun f b c run, true)

end GoFV.Opt.Fuse
