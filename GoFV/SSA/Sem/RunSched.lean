import GoFV.SSA.Sem.RunL

variable [GoFV.SSA.Sem.Addrs]

/-!
# `GoFV.SSA.runSched`: scheduled SSA (L1, `docs/plans/semantics2.md` §6)

From `schedule` on, `b.Values` is the execution order (`schedule`, `late nilcheck`,
`flagalloc`). `runSched` is `runL`'s runner (`runCtxL`) in two respects different:

* **Order.** A block's non-`Phi` values run in `b.Values` order (`schedOrder`), instead of
  `run`'s own dependency order (`kahn`). The order must be a schedule: every argument defined by
  a non-`Phi` value of the block comes before its use, and the memory is linear: every memory
  argument is the block's latest memory value before the use (a value of type `mem`; a tuple
  holding a memory — a call, an atomic — makes every memory use before its memory selector
  invalid), or, before the block defines one, the one memory live into the block. A block whose
  order is not one is `stuck` on entry (its `sched` entry is `none`).
* **Faulting memory ops** (`LMode.faulting`). Every op with `faultOnNilArg0`/`faultOnNilArg1`
  whose address argument has base nil and lies in the nil page (`Ptr.nilFault`, below
  `minZeroPage`) panics with `nilDeref` (`nilFaults`, `Sem/RunL.lean`), as the machine does; a
  `LoweredNilCheck` of a wild pointer (`Ptr.wild`, into the nil block but not nil) is undefined
  (`stuck`, `wildNil`). `late nilcheck` deletes the `LoweredNilCheck`s these faults make
  redundant; under `runL` the access would be an invalid load (`poison`), not a panic.

The ready-root order question of the `schedule` pass (#96) is about relating `runSched` of the
pass's output to `run` of its input; `runSched` itself does not depend on it.
-/

namespace GoFV.SSA.Sem

/-- `b.Values` without the `Phi`s, if it is a schedule of `b` (see the module comment) under the
value shapes `tys`. -/
def schedOrder (f : Func) (tys : Array Ty) (b : Block) : Option (Array ID) := Id.run do
  let n := f.valueTab.size
  let isPhi (id : ID) : Bool := ((f.value? id).map (·.op == .Phi)).getD false
  let order := b.values.filter (!isPhi ·)
  -- the non-`Phi` values of the block, by ID
  let mut inBlock : Array Bool := Array.replicate n false
  for id in order do inBlock := inBlock.set! id true
  let isMem (id : ID) : Bool := match tys[id]? with
    | some .mem => true
    | _ => false
  let holdsMem (id : ID) : Bool := match tys[id]? with
    | some (.tuple ts) => ts.any fun | .mem => true | _ => false
    | _ => false
  let mut seen : Array Bool := Array.replicate n false
  -- the block's latest memory-defining value; `entry`: the memory used before the first one
  let mut cur : Option ID := none
  let mut entry : Option ID := none
  for id in order do
    let some v := f.value? id | return none
    for a in v.args do
      if inBlock.getD a false && !seen.getD a false then return none
      if isMem a then
        match cur with
        | some c => if a != c then return none
        | none =>
          match entry with
          | some e => if a != e then return none
          | none => entry := some a
    if isMem id || holdsMem id then cur := some id
    seen := seen.set! id true
  return some order

/-- The context of `runSched` for `f` (its export section's tables `tabs`): `runL`'s, with the
`b.Values` order. -/
def Ctx.makeSched (tabs : Tables) (f : Func) : Ctx :=
  let c := Ctx.makeL tabs f
  { c with sched := f.blockTab.map fun o => o.bind (schedOrder f c.tys) }

/-- The mode of `runSched` for `f`: memory ops fault. -/
def LMode.sched (f : Func) : LMode := ⟨f.lowered, true⟩

end GoFV.SSA.Sem

namespace GoFV.SSA

/-- `GoFV.SSA.runSched`: the outcome of running scheduled `f` (L1) on `args` from memory `mem`
with at most `fuel` block entries. -/
def runSched (env : Sem.Env) (tabs : Tables) (f : Func) (args : List Sem.Val) (mem : Sem.Mem)
    (fuel : Nat) : Sem.Outcome :=
  Sem.runCtxL (Sem.LMode.sched f) env (Sem.Ctx.makeSched tabs f) args mem fuel

end GoFV.SSA
