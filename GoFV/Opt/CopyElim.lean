import GoFV.Opt.Pass
import GoFV.SSA.Edges

/-!
# copyelim / phielim (`copyelim.go`)

`copyelim` = `phielim` (fixpoint over `f.Blocks` × `b.Values`: zero-size struct/array values
become `OpEmpty`, copy arguments are replaced by their source, redundant phis become copies),
then copy controls and copy entries of `f.NamedValues` (via `f.Names`) are replaced by their
argument, one step (`docs/PASSES.md`, early phielim and copyelim). Also run by every
`deadcode`. `copySource` is shared with the rewrite driver (`applyRewrite`).
-/

namespace GoFV.Opt

open GoFV.SSA

namespace CopyElim

/-- Follow `args[0]` from `w` while the value is a `Copy`, with Go's tortoise/hare cycle check
(`copySource`, `copyelim.go:44-62`): returns the source and the function, where on a copy
cycle the meeting point has been `reset(OpUnknown)`. -/
def chase (f : Func) (w0 : ID) : Func × ID := Id.run do
  let mut w := w0
  let mut slow := w0
  let mut advance := false
  let mut f := f
  for _ in [0:2 * (f.vidLast + 1) + 2] do
    if (f.getV w).op != .Copy then break
    w := (f.getV w).args[0]!
    if w == slow then
      f := f.resetValue w .Unknown
      break
    if advance then slow := (f.getV slow).args[0]!
    advance := !advance
  return (f, w)

end CopyElim

/-- `copySource(v)` (`copyelim.go:36`): the ultimate non-copy source of the copy `v`; every
copy on the way is pointed directly at it (`SetArg(0, w)`). -/
def copySource (f : Func) (v : ID) : Func × ID := Id.run do
  let (f, w) := CopyElim.chase f (f.getV v).args[0]!
  let mut f := f
  let mut v := v
  for _ in [0:f.vidLast + 2] do
    if v == w then break
    let x := (f.getV v).args[0]!
    f := f.setArg v 0 w
    v := x
  return (f, w)

/-- `copyelimValue(v)`: no argument of `v` is a copy afterwards. Go ranges over the argument
slice, reading each element when it gets there. -/
def copyelimValue (f : Func) (v : ID) : Func := Id.run do
  let n := (f.getV v).args.size
  let mut f := f
  for i in [0:n] do
    let some a := (f.getV v).args[i]? | break
    if (f.getV a).op == .Copy then
      let (f', w) := copySource f a
      f := f'.setArg v i w
  return f

/-- `(t.IsStruct() || t.IsArray()) && t.Size() == 0`; an uncalculated size is an error (Go's
backend cannot calculate sizes). -/
def zeroSizeAggregate (tables : Tables) (t : TypeRef) : Except String Bool := do
  let some d := tables.type? t | throw s!"type t{t} not defined"
  if d.kind != .STRUCT && d.kind != .ARRAY then return false
  let some s := d.size | throw s!"phielim: size of t{t} not calculated"
  return s == 0

/-- One `phielim` sweep over `f.Blocks` × `b.Values`; returns whether a phi changed. -/
def phielimSweep (tables : Tables) (f : Func) : Except String (Func × Bool) := do
  let mut f := f
  let mut change := false
  for b in f.blocks do
    for v in (f.getB b).values do
      if ← zeroSizeAggregate tables (f.getV v).type then
        f := f.resetValue v .Empty
      f := copyelimValue f v
      let (f', c) := f.phielimValue v
      f := f'
      change := c || change
  return (f, change)

/-- `phielim(f)`: sweep until no phi changes. Every changing sweep turns a phi into a copy for
good, so `#values + 1` sweeps suffice. -/
def phielim (tables : Tables) (f : Func) : Except String Func := do
  let mut f := f
  for _ in [0:f.vidLast + 2] do
    let (f', change) ← phielimSweep tables f
    f := f'
    if !change then break
  return f

/-- `copyelim(f)`. -/
def copyelim (tables : Tables) (f : Func) : Except String Func := do
  let mut f ← phielim tables f
  for b in f.blocks do
    let cs := (f.getB b).controls
    for h : i in [0:cs.size] do
      let c := cs[i]
      if (f.getV c).op == .Copy then
        f := f.replaceControl b i (f.getV c).args[0]!
  let names := f.names.map fun (s, vs) =>
    (s, vs.map fun v => let x := f.getV v; if x.op == .Copy then x.args[0]! else v)
  return { f with names }

/-- The `early phielim and copyelim` pass. -/
def copyelimPass : Pass := Pass.ofFunc fun env f => copyelim env.tables f

end GoFV.Opt
