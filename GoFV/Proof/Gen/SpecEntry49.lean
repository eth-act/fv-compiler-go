import GoFV.Gen.Entry49
import GoFV.Proof.Gen.Spec49
import GoFV.Proof.Gen.Progs2

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `entryStoresOK` checked (`GoFV/Gen/Entry49.lean`)

`InWins L sp ws`: the machine bytes of the `NAME_PARAM` windows `ws` (operand offset, size) of an
activation whose `SP` is `sp` (`frameOff`). `entryStoresOK_cover`: under `entryStoresOK lc g k`,
the bytes of the pending windows (`pendWins`) are among those of the entry stores from value `k`
(`entryStores`). `entryStore?_spec`: an entry store `vkind49` accepted is a store or `STP` of
G49's frame-variable path (`VKVar49`) at its `NAME_PARAM` operand, of the width `entryStore?`
gives.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-- The machine bytes of the `NAME_PARAM` windows `ws` (operand offset, size) from `SP = sp`. -/
def InWins (L : Link) (sp : BitVec 64) (ws : List (Int × Nat)) (y : BitVec 64) : Prop :=
  ∃ w ∈ ws, ∃ j, j < w.2 ∧ y = sp + BitVec.ofInt 64 (frameOff L .PARAM w.1) + BitVec.ofNat 64 j

theorem inWins_nil {L : Link} {sp y : BitVec 64} : ¬ InWins L sp [] y := by
  rintro ⟨w, hw, -⟩; cases hw

theorem inWins_cons {L : Link} {sp y : BitVec 64} {w : Int × Nat} {ws : List (Int × Nat)} :
    InWins L sp (w :: ws) y ↔ (∃ j, j < w.2 ∧
      y = sp + BitVec.ofInt 64 (frameOff L .PARAM w.1) + BitVec.ofNat 64 j) ∨ InWins L sp ws y := by
  constructor
  · rintro ⟨w', hw', hj⟩
    rcases List.mem_cons.1 hw' with rfl | hw'
    · exact .inl hj
    · exact .inr ⟨w', hw', hj⟩
  · rintro (hj | ⟨w', hw', hj⟩)
    · exact ⟨w, List.mem_cons_self .., hj⟩
    · exact ⟨w', List.mem_cons_of_mem _ hw', hj⟩

/-- A byte of a `NAME_PARAM` window inside another window. -/
theorem frameOff_param_shift (L : Link) (sp : BitVec 64) {o o' : Int} {j : Nat} (h : o' ≤ o + j) :
    sp + BitVec.ofInt 64 (frameOff L .PARAM o) + BitVec.ofNat 64 j =
      sp + BitVec.ofInt 64 (frameOff L .PARAM o') + BitVec.ofNat 64 (o + j - o').toNat := by
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofInt_natCast, ← BitVec.ofInt_natCast,
    ← BitVec.ofInt_add, ← BitVec.ofInt_add]
  congr 2
  simp only [frameOff]
  omega

/-- **What `entryStoresOK` checked**: every byte of a pending window is written by an entry
store. -/
theorem entryStoresOK_cover {lc : LocCtx} {g : G2In} {k : Nat}
    (h : entryStoresOK lc g k = true) (L : Link) (sp : BitVec 64) {y : BitVec 64}
    (hy : InWins L sp (pendWins lc g) y) : InWins L sp (entryStores lc g k) y := by
  obtain ⟨⟨o, n⟩, hw, j, hj, rfl⟩ := hy
  simp only [entryStoresOK, List.all_eq_true, List.mem_range] at h
  have h1 := h (o, n) hw j hj
  simp only [inWins, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨o', n'⟩, hw', hlo, hhi⟩ := h1
  refine ⟨(o', n'), hw', (o + j - o').toNat, by simp only; omega, ?_⟩
  exact frameOff_param_shift L sp hlo

/-- **An entry store that `vkind49` accepted**: an access of a frame variable `x` at its
`NAME_PARAM` operand `off` with no temporary register (`FrameVar49OK`), of G49's frame-variable
kinds (`VKVar49`), a store of `n` bytes (`storeOp?`) or an `STP` (`n = 16`). -/
theorem entryStore?_spec {lc : LocCtx} {g : G2In} {v : Value} {off : Int} {n : Nat}
    {kd : VKind2} (h : entryStore? lc g v = some (off, n)) (hk : vkind49 lc g v = .ok kd) :
    ∃ x, FrameVar49OK lc g v x .PARAM off ∧ (lc.temps[v.id]?).join = none ∧
      VKVar49 lc v .PARAM off kd ∧
      ((∃ as, storeOp? v.op = some (as, n)) ∨ (v.op = .ARM64STP ∧ n = 16)) := by
  unfold entryStore? at h
  unfold vkind49 at hk
  cases h51 : vkind51 lc g v with
  | ok _ => rw [h51] at h; cases h
  | error e =>
    rw [h51] at h hk
    simp only at h hk
    cases hf : frameVar49? lc g v with
    | none => rw [hf] at h; cases h
    | some r =>
      obtain ⟨x, nc, off'⟩ := r
      rw [hf] at h hk
      simp only at h hk
      cases nc
      case NONE | EXTERN | STATIC | AUTO | GOTREF | TOCREF => simp at h
      split at hk
      · cases hk
      rename_i ht
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at ht
      have hfv := frameVar49?_spec hf
      have hvk := vkindVar49_spec hk
      cases hs : storeOp? v.op with
      | some an =>
        obtain ⟨as, n'⟩ := an
        rw [hs] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨x, hfv, ht, hvk, .inl ⟨as, rfl⟩⟩
      | none =>
        rw [hs] at h
        simp only at h
        split at h
        · rename_i hop
          simp only [beq_iff_eq] at hop
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨x, hfv, ht, hvk, .inr ⟨hop, rfl⟩⟩
        · cases h

end GoFV.Proof.Gen
