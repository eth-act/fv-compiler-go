import GoFV.Proof.Gen.Stack

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity of `Blk.writableFrom` and `SepFromW` (issue #553, `docs/plans/proofs3.md` §8 item 7)

An outgoing-arguments block of 16 `poison` bytes injected at `4096`, whose first byte is at an
address of `P` (as the saved `LR` at `SP`): a write at its offset 0 is `stuck`, one at offset 8
succeeds; `SepFromW` holds where `SepFrom` fails, and the write keeps it (`SepFromW.write`, from
`write_back`); `MemInj` holds and survives a machine byte change at `4096` (`memInj_of_sepW`,
through `memInj_congr_poison` and `ne_poison_of_ptrWordAt`); `SepFrom.w` gives `SepFromW` of a
block away from `P`.
-/

namespace GoFV.Proof.Witness.SepFromW

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.Gen

/-- `outargs 0` at `4096`. -/
def wι : Blk → Option (BitVec 64)
  | .nil => some 0
  | .outargs 0 => some 4096
  | _ => none

/-- The memory: `outargs 0`, 16 `poison` bytes. -/
def wm : Mem := { blocks := #[(.outargs 0, { data := Array.replicate 16 .poison })] }

/-- The address of the saved `LR`. -/
def wP (y : BitVec 64) : Prop := y = 4096

theorem wm_mem {b : Blk} {al : Alloc} (h : (b, al) ∈ wm.blocks) :
    b = .outargs 0 ∧ al = { data := Array.replicate 16 .poison } := by
  simpa [wm] using h

/-- A nonempty write below `writableFrom` is `stuck`; at offset 8 it succeeds. -/
theorem write_witness :
    (wm.write ⟨.outargs 0, 0⟩ (Array.replicate 8 (.b 1))).isSome = false ∧
      (wm.write ⟨.outargs 0, 8⟩ (Array.replicate 8 (.b 1))).isSome = true := by
  decide +kernel

theorem keys : KeysNodup wm := by
  simp [KeysNodup, wm]

theorem sepW : SepFromW wι wP wm := by
  intro b al a hb ha y hy i hi he
  obtain ⟨rfl, rfl⟩ := wm_mem hb
  obtain rfl : a = 4096 := (Option.some.inj ha).symm
  unfold wP at hy
  subst hy
  have h4 : (4096 : BitVec 64).toNat = 4096 := rfl
  obtain rfl : i = 0 := by omega
  exact ⟨by decide, by simp⟩

theorem not_sep : ¬ SepFrom wι wP wm := fun h =>
  h (.outargs 0) { data := Array.replicate 16 .poison } 4096 (by simp [wm]) rfl 4096 rfl
    ⟨Nat.le_refl _, by simp⟩

/-- `SepFromW.write` at offset 8. -/
theorem sepW_write : ∃ m', wm.write ⟨.outargs 0, 8⟩ (Array.replicate 8 (.b 1)) = some m' ∧
    SepFromW wι wP m' := by
  obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.1 write_witness.2
  exact ⟨m', hm', sepW.write keys hm'⟩

theorem inj (M : GoFV.Arm64.Memory) : MemInj wι wm M := by
  refine ⟨rfl, ?_, ?_, ⟨fun _ _ => False, ?_⟩⟩
  · intro b al hb
    obtain ⟨rfl, rfl⟩ := wm_mem hb
    exact ⟨4096, rfl, fun _ => by simp, by simp⟩
  · intro b al b' al' a a' hb hb' hne
    obtain ⟨rfl, rfl⟩ := wm_mem hb
    obtain ⟨rfl, rfl⟩ := wm_mem hb'
    exact absurd rfl hne
  · intro b al a hb ha
    obtain ⟨rfl, rfl⟩ := wm_mem hb
    refine ⟨fun o ho => ho.elim, fun o _ ho => ho.elim, fun i hi _ => ?_⟩
    simp [ByteRel]

/-- `memInj_of_sepW`: the machine byte at `4096` (the saved `LR`) changes, `MemInj` stays. -/
theorem inj_spill : MemInj wι wm (fun y => if y = 4096 then 7 else 0) :=
  memInj_of_sepW (inj fun _ => 0) sepW fun _ hy => if_neg hy

/-- `SepFrom.w`: no block byte at `8`. -/
theorem sepW_of_sep : SepFromW wι (· = 8) wm :=
  SepFrom.w fun b al a hb ha y hy hin => by
    obtain ⟨rfl, rfl⟩ := wm_mem hb
    obtain rfl : a = 4096 := (Option.some.inj ha).symm
    subst hy
    have h4 : (4096 : BitVec 64).toNat = 4096 := rfl
    have h8 : (8 : BitVec 64).toNat = 8 := rfl
    omega

end GoFV.Proof.Witness.SepFromW
