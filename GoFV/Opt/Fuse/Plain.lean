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

/-- Move the end-of-block statement mark of `bx` into `next` (`fuse.go:226-252`). -/
def moveEndStmt (f : Func) (bx next : ID) : Func := Id.run do
  let bpos := (f.getB bx).pos
  if bpos.isStmt != Pos.isStmtMark then return f
  let mut f := f
  let mut l := bpos.line
  let mut outOfOrder := false
  for v in (f.getB next).values do
    let p := (f.getV v).pos
    if p.isStmt == Pos.notStmt then continue
    if l == p.line then
      f := f.modV v fun x => { x with pos := p.withIsStmt }
      l := 0
      break
    if l < p.line then outOfOrder := true
  let npos := (f.getB next).pos
  if l != 0 && !outOfOrder && (npos.line == l || npos.isStmt != Pos.isStmtMark) then
    f := f.modB next fun x => { x with pos := bpos.withIsStmt }
  return f

/-- `fuseBlockPlain(b)`. -/
def fuseBlockPlain (f : Func) (b : ID) : Func × Bool := Id.run do
  let bb := f.getB b
  if bb.kind != .Plain then return (f, false)
  let c := bb.succs[0]!.b
  if (f.getB c).preds.size != 1 || c == b then return (f, false)
  let fuel := f.blocks.size + 1
  let b := runStart f c fuel b
  let c := runEnd f b fuel c
  let run := runBlocks f c fuel b #[]
  let mut f := f
  -- statement marks, and every value of the run now belongs to `c`
  for k in [0:run.size - 1] do
    let bx := run[k]!
    f := moveEndStmt f bx run[k + 1]!
    for v in (f.getB bx).values do
      f := f.modV v fun x => { x with block := c }
  let vals := run.foldl (init := #[]) fun acc bx => acc ++ (f.getB bx).values
  f := f.modB c fun x => { x with values := vals }
  -- replace the b → c edge with preds(b) → c
  let preds := (f.getB b).preds
  f := f.modB c fun x => { x with preds }
  for h : i in [0:preds.size] do
    let e := preds[i]
    f := f.modB e.b fun x => { x with succs := x.succs.set! e.i ⟨c, i⟩ }
  if f.entry == b then f := { f with entry := c }
  for k in [0:run.size - 1] do
    f := f.modB run[k]! fun x =>
      { x with kind := .Invalid, values := #[], preds := #[], succs := #[] }
  return (f, true)

end GoFV.Opt.Fuse
