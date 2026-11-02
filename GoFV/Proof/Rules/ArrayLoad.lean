import GoFV.Proof.Rules.ConstString
import GoFV.Rules.Generated.Generic.Values05

/-!
# Rule lemma: a `Load` of a one-element array (`generic.rules:994`)

`(Load <t> ptr mem) && t.IsArray() && t.NumElem() == 1 && CanSSA(t) => (ArrayMake1 (Load
<t.Elem()> ptr mem))` under `Rule.SoundT` (`DenT.lean`): `FrameOK`, which the rewrite validator
checks (`condFrameOK`), says that `t` (with `t.NumElem() == 1`) has the shape of one field at
offset 0 that fills it, `.agg [(0, f)] f.size` (`Sem.tyOf` of `[1]T`), so `t.Elem()` is `f`
(`methodE`). Both loads read the same `f.size` bytes; the aggregate load is `poison` or the
one-field aggregate of the field load (`load_one`; issue #69).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- A load of an aggregate of one field that fills it is `poison` or that field's load. -/
theorem load_one (m : Mem) (p : Ptr) (f : Ty) :
    m.load (.agg [(0, f)] f.size) p = .poison ∨
      m.load (.agg [(0, f)] f.size) p = .agg [m.load f p] := by
  have hl : m.load (.agg [(0, f)] f.size) p = match m.read p f.size with
      | some bs => decodeLoad bs 0 (.agg [(0, f)] f.size)
      | none => .poison := rfl
  rw [hl]
  cases hr : m.read p f.size with
  | none => exact .inl rfl
  | some bs =>
    dsimp only
    rw [decodeLoad]
    split
    · exact .inl rfl
    · refine .inr ?_
      simp only [decodeLoadFields, Nat.add_zero]
      cases f <;> first | rfl | (unfold Mem.load; simp only [hr])

/-- `generic.rules:994`: `(Load <t> ptr mem) && t.IsArray() && t.NumElem() == 1 && CanSSA(t) => (ArrayMake1 (Load <t.Elem()> ptr mem))` -/
theorem r_generic_994_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_994 := by
  refine ⟨rfl, fun tabs e or hbt => ?_⟩
  simp only [sigmaT_pure tabs e (pat := GoFV.Rules.Generated.Generic.r_generic_994.pat) rfl,
    Pat.denT_pure tabs e [] GoFV.Rules.Generated.Generic.r_generic_994.pat rfl,
    Pat.rawT_pure tabs e (pat := GoFV.Rules.Generated.Generic.r_generic_994.pat) rfl,
    resDenT_pure tabs _ or _ _ (res := GoFV.Rules.Generated.Generic.r_generic_994.result) rfl]
  intro hfr
  obtain ⟨f, hf⟩ := hfr.2.2.2.1 0
    (by simp [GoFV.Rules.Generated.Generic.r_generic_994, numElem1Vars])
  clear hfr
  dsimp only [GoFV.Rules.Generated.Generic.r_generic_994, rule_unfold_ds] at hf ⊢
  simp only [rule_helper, rule_unfold_s] at hf ⊢
  have ht : e.ty [] = .agg [(0, f)] f.size := DV.ty.inj hf
  rw [ht]
  intro _ _ _ hty _ _ _
  generalize e.leaf [0] = P at hty ⊢
  generalize e.leaf [1] = Mv at hty ⊢
  by_cases hpm : ∃ p m, P.asPtrWord = some p ∧ Mv = .mem m
  · obtain ⟨p, m, hp, rfl⟩ := hpm
    simp only [loadOp, hp] at hty ⊢
    rcases load_one m p f with h | h <;> rw [h] at hty ⊢
    · exact .poison _
    · have h1 : (m.load f p).hasTy f = true := by simpa [Val.hasTy, Val.hasTyList] using hty
      rw [Val.retype_of_hasTy h1]
      show Refines _ (Val.retype _ (.agg [_]))
      rw [Val.retype_of_hasTy hty]
      exact Refines.refl _
  · have hl : loadOp (.agg [(0, f)] f.size) [P, Mv] = .poison := by
      unfold loadOp; split
      · rename_i a m heq
        simp only [List.cons.injEq, and_true] at heq
        obtain ⟨ha, hm⟩ := heq
        cases hp : a.asPtrWord with
        | none => rfl
        | some p => exact absurd ⟨p, m, by rw [ha]; exact hp, hm⟩ hpm
      · rfl
    rw [hl]
    exact .poison _

/-! ## Non-vacuity (`rule-sat` draws no tables) -/

/-- A heap block of eight zero bytes. -/
def zeroMem : Mem := { blocks := #[(.heap 0, { data := Array.replicate 8 (.b 0) })] }

/-- `generic.rules:994` at a `Load <[1]int64>` of eight zero bytes (the heap block's address
word `2^40`). -/
theorem inst_r_generic_994 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_994 {}
    { leaf := fun p => if p = [0] then .int .w64 (2 ^ 40) else .mem zeroMem
      ty := fun p => if p = [] then .agg [(0, .int .w64)] 8 else if p = [0] then .ptr (some 8)
        else .mem
      auxInt := fun _ => 0, aux := fun _ => none }
    (Oracle.const true) := by
  refine ⟨Oracle.const_boolTyped true, ?_⟩
  simp [GoFV.Rules.Generated.Generic.r_generic_994, FrameOK, Result.nodes, emptyStrVars, sameLeaves,
    samePtrVars, numElem1Vars, shiftAmt?, Pat.rawT, Pat.densT, Pat.denT, sigmaT, Pat.bindsT,
    Pat.bindssT, opVal]
  rule_eval
  refine ⟨⟨.int .w64, by simp [sigmaT, Pat.bindsT, Pat.bindssT]; rfl⟩, by decide +kernel, ?_⟩
  intro h
  have h' : (loadOp (.agg [(0, .int .w64)] 8) [.int .w64 (2#64 ^ 40), .mem zeroMem]).hasTy .other =
      false := by decide +kernel
  rw [h] at h'
  cases h'

end GoFV.Proof.Rules
