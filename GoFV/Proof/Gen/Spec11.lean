import GoFV.Gen.Check11
import GoFV.Proof.Gen.Spec10

/-!
# What the genssa validator's slice G11 accepted (`docs/plans/proofs3.md` §4)

`checkG11 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G11.lean`) uses (`checkG11_spec`): G10's (`Spec10.lean`) with G11's value check
(`vkind11_spec`, `VK11`: G10's values and `LoweredGetClosurePtr` homed in `R26`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind11` accepted of a value that is not an entry value, and what it emits. -/
inductive VK11 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G10. -/
  | g10 {kd : VKind2} : VK10 lc g v kd → VK11 lc g v kd
  /-- The closure context: no argument, homed in `R26` at a 64-bit shape; no code. -/
  | clo : v.op = .ARM64LoweredGetClosurePtr → v.args.size = 0 →
      lc.home v.id = some (.reg ctxReg) → cls (lc.ty v.id) = some 64 → VK11 lc g v .none

/-- What `cloKind` accepted. -/
theorem cloKind_spec {lc : LocCtx} {v : Value} {kd : VKind2} (h : cloKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ v.args.size = 0 ∧ lc.home v.id = some (.reg ctxReg) ∧
      cls (lc.ty v.id) = some 64 ∧ kd = .none := by
  unfold cloKind at h
  split at h
  · cases h
  · rename_i ht
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨by simpa using ht, hc.1.1, hc.1.2, hc.2, rfl⟩
    · cases h

/-- What `vkind11` accepted of a value that is not an entry value: no temporary, and `VK11`. -/
theorem vkind11_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind11 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK11 lc g v kd := by
  unfold vkind11 at h
  split at h
  · rename_i hop
    simp only [beq_iff_eq] at hop
    obtain ⟨ht, hsz, hh, hc, rfl⟩ := cloKind_spec h
    exact ⟨ht, .clo hop hsz hh hc⟩
  · obtain ⟨ht, h10⟩ := vkind10_spec h hen
    exact ⟨ht, .g10 h10⟩

/-- What `checkG11` accepted: G10's facts with G11's value check. -/
theorem checkG11_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG11 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind11 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG11 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  cases hf : List.find? (fun x => !homeOK10 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨-, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb⟩
    by_cases hi : i < lc.homes.size
    · have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
      simpa using this
    · have hh : lc.home i = none := by
        simp only [LocCtx.home]
        rw [getElem?_neg lc.homes i hi]
        rfl
      unfold homeOK10 homeOK4 homeOK3 homeOK2 homeOK
      rw [hh]
      rfl

end GoFV.Gen.Check
