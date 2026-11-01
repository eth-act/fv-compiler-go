import GoFV.Proof.Pass.StructStoreSrc
import GoFV.Proof.Pass.SegCall
import GoFV.Proof.Pass.SegZeroMem
import GoFV.Proof.MemInv

/-!
# Segments: the obligation of a segment (issue #151)

A segment rewrite (`GoFV.Opt.RewriteCheck.segOK`) redefines the anchor `x` in place, drops values
`D` of `f` and puts in fresh values `N` (dependency order). `SegSound` is what the segment
simulation asks of each segment: in a source frame whose available values (`CSE.Mem.Avail`)
include the segment's roots in `f`, the target's definitions of `N ++ [x]` evaluate in order from
that frame, and the target's anchor refines the source's if the source evaluated it. The chain
segments (`generic.rules:1833` family, `SegChain.lean`) and the call segments (`:1638`, `:1730`,
`SegCallSeg.lean`) discharge it.
-/

namespace GoFV.Proof.Seg

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.CSE.Mem (Avail)

/-- **A segment's obligation**: the segment's roots in `f` (its dropped roots and, if a root of
`f`, its anchor) never panic; and in a source frame `S` with at least `g`'s registers whose
available values `A` (evaluated, closed under arguments, `Avail`; typed, with their own IDs)
include those roots and whose memories are `Q` (the source run's memory invariant), the
target's definitions of the fresh values and the anchor evaluate in
order from `S`, and if the anchor is available, the target's anchor refines the source's. -/
def SegSound (Q : Mem → Prop) (env : Env) (tabs : Tables) (f g : Func) (x : ID) (D N : List ID) : Prop :=
  (∀ s ∈ D ++ [x], CSE.rootNode f s = true → ∀ sv fr e m, f.value? s = some sv →
    evalValue env (Ctx.make tabs f) fr sv ≠ .panic e m) ∧
  ∀ (S : Frame) (A : ID → Prop), Avail env tabs f S A → Proof.Typed (Ctx.make tabs f) S →
    (∀ (z : ID) (y : Val), S.regs[z]? = some (some y) → MemInv.MemsOK Q y) → (∀ z v, A z → f.value? z = some v → v.id = z) → g.valueTab.size ≤ S.regs.size →
    (∀ s ∈ D ++ [x], CSE.rootNode f s = true → A s) →
    ∃ S', evalAll env (Ctx.make tabs g) S (N ++ [x]) = .ok S' ∧
      (A x → ∃ y y', S.regs[x]? = some (some y) ∧ S'.regs[x]? = some (some y') ∧
        Sem.Refines y y')

end GoFV.Proof.Seg
