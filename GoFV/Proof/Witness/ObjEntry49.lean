import GoFV.Proof.Obj.Entry49
import GoFV.Proof.Witness.GenG49

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: a store into a `NAME_PARAM` window that holds garbage (`g60L_entryStore`)

`runtime.getm`'s ABI0 wrapper (`GenG49`): its `v2 = MOVDstore {~r0} SP v8 v7` stores `R0` into the
result `~r0` at its `NAME_PARAM` operand (`MOVD R0, ~r0+0(FP)`), a store `checkG51` rejects and
G49's frame-variable path accepts (`entryStore?` gives its operand offset 0 and width 8); `checkG60`
accepts the wrapper with `checkG49`'s tables. The
machine `mG` before it is `GenG49.m0 7` with garbage (`0xAB`) in the 8 bytes of that window
(`SP + 24`): `runLoc`'s state `s0 7` is `LocMatch`ed to `mG` with its memory replaced by
`GenG49`'s (0 everywhere), which agrees with `mG`'s outside the window. `g60L_entryStore` runs the
`MOVD` from `mG` to `m'`, `LocMatch`ed (in full: no byte left out, `W = ∅`) to the state after the
store. By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`;
`entry_facts`): `entryStore?` of `v2`, and `checkG60`'s acceptance.
-/

namespace GoFV.Proof.Witness.ObjEntry49

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen GoFV.Proof.Obj
open GoFV.Proof.Witness.GenG49 (lc lc0 ps bs g tab kt blk val L E s0 m0 sp)

/-- What compiled evaluation checks: `v2` is an entry store at operand offset 0, of 8 bytes;
`checkG60` accepts the wrapper with `checkG49`'s tables. -/
def eFacts : Bool :=
  entryStore? lc g (val 2) == some (0, 8) && (checkG60 lc0 ps bs g).toOption == some (tab, kt)

theorem entry_facts : eFacts = true := by
  native_decide

/-- The machine before `v2`: `GenG49.m0 7` with `0xAB` in the 8 bytes of `~r0`'s window. -/
def mG : MState :=
  { m0 7 with mem := fun y => if (y - (sp + 24)).toNat < 8 then 0xAB else 0 }

/-- **An entry store from a window of garbage** (`g60L_entryStore` on the `getm` wrapper's `v2`):
`stepLoc` runs `v2` from `s0 7`, and from the machine `mG`, whose `~r0` window holds `0xAB`, the P0
run of `MOVD R0, 24(RSP)` reaches a state `LocMatch`ed to the state after `v2`. -/
theorem entryStore_witness :
    entryStore? lc g (val 2) = some (0, 8) ∧ mG.mem (sp + 24) = 0xAB ∧
      ∃ s1 m', stepLoc default lc (s0 7) (val 2) = .ok s1 ∧
        PStar GenG2.H0 L ps.toList 0 mG m' ∧ LocMatch E s1 1 6 m' := by
  obtain ⟨hl, hc, -, hm1, hb, hv2, hi5, -, hk0, -, hav, hvo, hfg, hact, hsl, hoff, hrun⟩ :=
    GenG49.facts
  obtain ⟨s1, hs1, -⟩ := GenG1.okThen_spec hrun
  have hE := GenG49.g49Env hc hl hav hvo hfg hact hsl hoff
  have hef := entry_facts
  simp only [eFacts, Bool.and_eq_true, beq_iff_eq] at hef
  obtain ⟨hes, hres⟩ := hef
  have hc60 : checkG60 lc0 ps bs g = .ok (tab, kt) := by
    revert hres; cases checkG60 lc0 ps bs g <;> simp [Except.toOption]
  have hm : LocMatch E (s0 7) 1 5 { mG with mem := fun _ => 0 } := GenG49.locMatch0 7
  have hW : ∀ y, ¬ (fun _ => False) y → (∀ j, j < 8 → y ≠ E.sp + BitVec.ofInt 64
      (frameOff L .PARAM 0) + BitVec.ofNat 64 j) → (fun _ => (0 : BitVec 8)) y = mG.mem y := by
    intro y _ hy
    rw [hoff] at hy
    show (0 : BitVec 8) = if (y - (sp + 24)).toNat < 8 then 0xAB else 0
    split
    · rename_i h
      exfalso
      refine hy (y - (sp + 24)).toNat h ?_
      show y = sp + BitVec.ofInt 64 24 + BitVec.ofNat 64 (y - (sp + 24)).toNat
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      have : BitVec.ofInt 64 24 = (24 : BitVec 64) := by decide
      rw [this]
      bv_omega
    · rfl
  obtain ⟨m', M', hp, -, hm', -, -, hag⟩ := g60L_entryStore (H := GenG2.H0) (env := default)
    (W := fun _ => False) (checkG60_spec hc60).2 hE hm1 hb hi5 hv2 hes hm hW
    (GenG49.g49Inv0 7 hk0) hs1
  have hM : M' = m'.mem := funext fun y => hag y id
  subst hM
  exact ⟨hes, by decide, s1, m', hs1, hp, hm'⟩

end GoFV.Proof.Witness.ObjEntry49
