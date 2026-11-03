import GoFV.Opt.Pass
import GoFV.SSA.CopyInto
import GoFV.SSA.TypePred

/-!
# tighten tuple selectors (`tuple.go:14-71`, `tightenTupleSelectors`)

docs/PASSES2.md, tighten tuple selectors (issue #395). Over `f.Blocks` × `b.Values` (Go's
`range` reads each block's value list when it reaches the block, so clones appended to a later
block are visited, clones appended to the current or an earlier block are not): each `Select0`,
`Select1` and `SelectN` is keyed by `(generator ID, index)`. The first selector of a key wins;
a later one becomes a `Copy` of it. A first selector outside its generator's block is cloned
there (`copyInto`: appended, position without statement mark) and becomes a `Copy` of the
clone.
-/

namespace GoFV.Opt

open GoFV.SSA


/-- `tightenTupleSelectors(f)`. -/
def tightenTupleSelectors (tabs : Tables) (isMem : TypeRef → Bool) (f : Func) :
    Except String Func := do
  let mut sel : Std.HashMap (ID × Int) ID := {}
  let mut f := f
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      let isSel := x.op == .Select0 || x.op == .Select1 || x.op == .SelectN
      if !isSel then continue
      let some tuple := x.args[0]? | throw s!"v{v}: selector without argument"
      let kind := (tabs.type? (f.getV tuple).type).map (·.kind)
      let idx : Int ← match x.op with
        | .SelectN =>
          if kind != some .RESULTS then
            throw s!"arg of result selector v{v} is not a results: v{tuple}"
          pure x.auxInt.toInt
        | op =>
          if kind != some .TUPLE then
            throw s!"arg of tuple selector v{v} is not a tuple: v{tuple}"
          pure (if op == .Select1 then 1 else 0)
      let key := (tuple, idx)
      if let some t := sel[key]? then
        f := f.copyOf v t
        continue
      let tb := (f.getV tuple).block
      if x.block != tb then
        let (f', t) ← f.copyInto isMem v tb
        f := f'.copyOf v t
        sel := sel.insert key t
        continue
      sel := sel.insert key v
  return f

/-- The `tighten tuple selectors` pass. -/
def tightenTupleSelectorsPass : Pass := Pass.ofFunc fun env f => do
  let some mem := env.typ? "Mem" | throw "typs: no Mem"
  tightenTupleSelectors env.tables (env.tables.isMemory mem) f

end GoFV.Opt
