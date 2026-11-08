import GoFV.Gen.Check5
import GoFV.Proof.Gen.Spec4

/-!
# What the genssa validator's slice G5 accepted (`docs/plans/proofs3.md` §4)

`checkG5 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G5.lean`) uses (`checkG5_spec`): G4's (`Spec4.lean`) with G5's value check
(`vkind5_spec`, `VK5`: G4's values and the memory markers `VarDef`, `VarLive`, `KeepAlive`,
`WBend`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind5` accepted of a value that is not an entry value, and what it emits. -/
inductive VK5 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G4. -/
  | g4 {kd : VKind2} : markOp? v.op = none → VK4 lc g v kd → VK5 lc g v kd
  /-- A memory marker of `n` arguments, the memory last, of the memory shape with no home: no
  code. -/
  | mark {n : Nat} : markOp? v.op = some n → v.args.size = n → memTy (lc.ty v.id) = true →
      lc.home v.id = none → memArg lc v (n - 1) = .ok () → VK5 lc g v .none

/-- What `vkind5` accepted of a value that is not an entry value: no temporary, and `VK5`. -/
theorem vkind5_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : vkind5 lc g v = .ok kd)
    (hen : entryOp3 v.op = false) : (lc.temps[v.id]?).join = none ∧ VK5 lc g v kd := by
  unfold vkind5 at h
  cases hm : markOp? v.op with
  | none =>
    rw [hm] at h
    obtain ⟨ht, h4⟩ := vkind4_spec h hen
    exact ⟨ht, VK5.g4 hm h4⟩
  | some n =>
    rw [hm] at h
    simp only at h
    by_cases ht : (lc.temps[v.id]?).join = none
    · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hs, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hs
      obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      exact ⟨ht, VK5.mark hm hsz hmt hhn hma⟩
    · simp [ht, ex_throw, ex_bind_error] at h

/-- What `checkG5` accepted: G4's facts with G5's value check. -/
theorem checkG5_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG5 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind5 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK4 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG5 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  cases hf : List.find? (fun x => !homeOK4 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
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
      unfold homeOK4 homeOK3 homeOK2 homeOK
      rw [hh]

end GoFV.Gen.Check
