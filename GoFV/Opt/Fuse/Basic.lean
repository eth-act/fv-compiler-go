import GoFV.SSA.Alloc
import GoFV.SSA.TypePred

/-!
# fuse driver and block helpers

`fuse(f, typ)` (`fuse.go:33-66`): repeat sweeps over `f.Blocks` **backwards** by index, each
block running the selected per-block transformations in a fixed order; after a sweep, the
optional whole-function step (`fuseBranchRedirect`); `f.invalidateCFG()` after a changed round.
The per-block step and the final step are parameters, so `shortcircuit` (`fuseTypePlain |
fuseTypeShortCircuit`) and early/late fuse share this driver without importing each other.
Fusion never adds or removes entries of `f.Blocks` (fused-away blocks stay as `BlockInvalid`).

Also `Block.replaceUses` and `Value.moveTo` (`shortcircuit.go:500-536`).
-/

namespace GoFV.Opt.Fuse

open GoFV.SSA

/-- The type tables and the `types.TypeMem`/`types.TypeVoid` numbers fuse needs. -/
structure TypeView where
  tabs : Tables
  mem : TypeRef
  void : TypeRef

/-- `t.IsMemory()`. -/
@[inline] def TypeView.isMem (tv : TypeView) (t : TypeRef) : Bool := tv.tabs.isMemory tv.mem t

/-- `v.removeable()`. -/
@[inline] def TypeView.removeable (tv : TypeView) (v : Value) : Bool :=
  tv.tabs.removeable tv.mem tv.void v

/-- Bound on fuse rounds (Go loops until nothing changes; every round that changes something
removes an edge, a block or a value use, so this is never reached on real input). -/
def roundFuel : Nat := 1000000

/-- One backwards sweep: `step` on `f.Blocks[n-1] … f.Blocks[0]`. -/
def sweep (step : Func → ID → Except String (Func × Bool)) (f : Func) :
    Except String (Func × Bool) := do
  let blocks := f.blocks
  let mut f := f
  let mut changed := false
  for k in [0:blocks.size] do
    let (f', c) ← step f blocks[blocks.size - 1 - k]!
    f := f'
    changed := c || changed
  return (f, changed)

/-- `fuse(f, typ)`: rounds of `sweep step` followed by `final` (if any) until nothing changes. -/
def fuseLoop (step : Func → ID → Except String (Func × Bool))
    (final : Option (Func → Except String (Func × Bool))) : Nat → Func → Except String Func
  | 0, _ => throw "fuse: round bound exceeded"
  | fuel + 1, f => do
    let (f, changed) ← sweep step f
    let (f, changed) ← match final with
      | some g => do let (f, c) ← g f; pure (f, c || changed)
      | none => pure (f, changed)
    if changed then fuseLoop step final fuel f.invalidateCFG else return f

/-- `b.replaceUses(old, new)` (`shortcircuit.go:500`): every argument and control of `b` equal to
`old` becomes `new` (`SetArg` / `ReplaceControl`, in `b.Values` × `Args` order). -/
def replaceUses (f : Func) (b old new : ID) : Func := Id.run do
  let mut f := f
  for v in (f.getB b).values do
    let n := (f.getV v).args.size
    for i in [0:n] do
      if (f.getV v).args[i]! == old then f := f.setArg v i new
  let n := (f.getB b).controls.size
  for i in [0:n] do
    if (f.getB b).controls[i]! == old then f := f.replaceControl b i new
  return f

/-- `v.moveTo(dst, i)` (`shortcircuit.go:516`): `v` is `v.Block.Values[i]`; append it to
`dst.Values` and swap-remove it from its block. -/
def moveTo (f : Func) (v dst : ID) (i : Nat) : Func :=
  let src := (f.getV v).block
  if src == dst then f else
  let f := f.modV v fun x => { x with block := dst }
  let f := f.modB dst fun x => { x with values := x.values.push v }
  f.modB src fun x =>
    let last := x.values.size - 1
    { x with values := (x.values.set! i x.values[last]!).pop }

end GoFV.Opt.Fuse
