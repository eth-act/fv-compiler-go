import GoFV.Proof.Pass.NilLateLEval
import GoFV.Proof.FrameL
import GoFV.Proof.SimL
import GoFV.Proof.CongL

variable [GoFV.SSA.Sem.Addrs]

/-!
# `late nilcheck` under `runSched`: the relation the validator decides

`NLRel tabs f g rm`: what `nilLateB tabs f g` establishes (`nlRel_of`), with `rm` the removed
values: `g` is `f` with the removed values absent and dropped from the blocks, up to positions and
use counts; nothing reads them; where `f`'s block is a schedule, `g`'s is it without them, and
each is a redundant `LoweredNilCheck` (`blockB`). Also the facts on the two `runSched` contexts
(same tables, parameters, activation; the same shapes of the kept values) and on frames.
-/

namespace GoFV.Proof.NilLateL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Opt.NilLate

/-- What `nilLateB` decides (module doc). -/
structure NLRel (tabs : Tables) (f g : Func) (rm : ID → Bool) : Prop where
  entry : g.entry = f.entry
  ownAux : g.ownAux = f.ownAux
  lowered : g.lowered = f.lowered
  vsize : g.valueTab.size = f.valueTab.size
  value : ∀ i, (g.value? i).map eraseV = if rm i then none else (f.value? i).map eraseV
  block : ∀ i, (g.block? i).map eraseB = (f.block? i).map (eraseB ∘ dropB rm)
  usedV : ∀ i v, rm i = false → f.value? i = some v → ∀ a ∈ v.args, rm a = false
  usedC : ∀ i b, f.block? i = some b → ∀ c ∈ b.controls, rm c = false
  rmOp : ∀ i, rm i = true → ∃ v, f.value? i = some v ∧ v.op = .ARM64LoweredNilCheck
  blk : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∀ o,
    ((Ctx.makeSched tabs f).sched[bid]?).join = some o →
      o.toList = orderOf f fb ∧
      ((Ctx.makeSched tabs g).sched[bid]?).join =
        some ((orderOf f fb).filter (!rm ·)).toArray ∧
      blockB f rm fb.values (phisOf f fb) (orderOf f fb) = true

private theorem value_none_of_ge {f : Func} {i : ID} (h : f.valueTab.size ≤ i) : f.value? i = none := by
  simp [Func.value?, Array.getElem?_eq_none h]

private theorem block_none_of_ge {f : Func} {i : ID} (h : f.blockTab.size ≤ i) : f.block? i = none := by
  simp [Func.block?, Array.getElem?_eq_none h]

/-- **`nilLateB` decides `NLRel`** for the removed values `removedSet f g`. -/
theorem nlRel_of {tabs : Tables} {f g : Func} (h : nilLateB tabs f g = true) :
    NLRel tabs f g (fun i => (removedSet f g).getD i false) := by
  unfold nilLateB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hs, hu⟩, hb⟩ := h
  unfold shapeB at hs
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨⟨⟨⟨⟨he, ho⟩, hl⟩, hvs⟩, hbs⟩, hv⟩, hbl⟩ := hs
  unfold unusedB at hu
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hu
  obtain ⟨hu1, hu2⟩ := hu
  have hrs : ∀ i, f.valueTab.size ≤ i → (removedSet f g).getD i false = false := by
    intro i hi
    simp [removedSet, Array.getD, Nat.not_lt.2 hi]
  refine ⟨he.symm, ho.symm, hl.symm, hvs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i < f.valueTab.size
    · exact hv i hi
    · have hi' : f.valueTab.size ≤ i := Nat.le_of_not_lt hi
      rw [hrs i hi', value_none_of_ge hi', value_none_of_ge (f := g) (i := i) (by rw [hvs]; exact hi')]
      rfl
  · intro i
    by_cases hi : i < f.blockTab.size
    · exact hbl i hi
    · have hi' : f.blockTab.size ≤ i := Nat.le_of_not_lt hi
      rw [block_none_of_ge hi', block_none_of_ge (f := g) (i := i) (by rw [hbs]; exact hi')]
      rfl
  · intro i v hr hfv a ha
    have h1 := hu1 i (lt_of_value? hfv)
    rw [hr, hfv] at h1
    simp only [Bool.false_eq_true, ite_false, Option.map_some, Option.getD_some,
      Array.all_eq_true, Bool.not_eq_true'] at h1
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ha
    exact h1 k hk
  · intro i b hfb c hc
    have hi : i < f.blockTab.size := by
      refine Classical.byContradiction fun hn => ?_
      rw [block_none_of_ge (f := f) (i := i) (Nat.le_of_not_lt hn)] at hfb; cases hfb
    have h2 := hu2 i hi
    rw [hfb] at h2
    simp only [Option.map_some, Option.getD_some, Array.all_eq_true, Bool.not_eq_true'] at h2
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hc
    exact h2 k hk
  · intro i hr
    have hi : i < f.valueTab.size := by
      refine Classical.byContradiction fun hn => ?_
      rw [hrs i (Nat.le_of_not_lt hn)] at hr; cases hr
    have h1 := hu1 i hi
    rw [hr] at h1
    simp only [ite_true] at h1
    cases hfv : f.value? i with
    | none => rw [hfv] at h1; cases h1
    | some v =>
      rw [hfv] at h1
      simp only [Option.map_some, Option.getD_some, beq_iff_eq] at h1
      exact ⟨v, rfl, h1⟩
  · intro bid hbid fb hfb o ho
    have h3 := (Array.all_eq_true.1 hb)
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hbid
    have h4 := h3 k hk
    simp only [hfb] at h4
    unfold blockOKB at h4
    rw [ho] at h4
    simp only [Bool.and_eq_true, beq_iff_eq] at h4
    exact ⟨h4.1.1, h4.1.2, h4.2⟩

end GoFV.Proof.NilLateL
