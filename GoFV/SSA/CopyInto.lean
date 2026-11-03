import GoFV.SSA.Alloc

/-!
# Value clones (`value.go:446-458`)

`v.copyInto(b)`, used by `tighten tuple selectors`, `phi tighten` and `flagalloc`
(docs/PASSES2.md §1.4). A separate module so that `GoFV.SSA.Alloc`'s many dependents do not
rebuild.
-/

namespace GoFV.SSA.Func

/-- `v.copyInto(b)`: a new value with `v`'s op, type, aux, `AuxInt` and arguments appended to
`b`, at `v.Pos.WithNotStmt()`; fatal (after the allocation, as in Go) if an argument is
memory-typed (`isMem`). -/
def copyInto (f : Func) (isMem : TypeRef → Bool) (v b : ID) : Except String (Func × ID) := do
  let x := f.getV v
  let (f, c) := f.newValueArgs b x.pos.withNotStmt x.op x.type x.auxInt x.aux x.args
  for a in x.args do
    if isMem (f.getV a).type then throw s!"v{v}: can't move a value with a memory arg"
  return (f, c)

end GoFV.SSA.Func
