import GoFV.Gen.Check30
import GoFV.Proof.Gen.Spec29

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G30 accepted (`docs/plans/proofs3.md` §4)

`checkG30 lc ps bstart g = .ok (tab, kt)` unfolded (`checkG30_lowered`, `checkNL30_spec`): on a
function with an arm64 op, `checkG29`'s acceptance; on one without, `checkNL`'s facts with the
value check `vkindNL30` (`vkindNL30_spec`: G12's `Convert`, or what `vkindNL` accepts).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- On a function with an arm64 op, G30 is G29. -/
theorem checkG30_lowered {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = true)
    (h : checkG30 lc ps bstart g = r) : checkG29 lc ps bstart g = r := by
  simpa [checkG30, hl] using h

/-- On a function with no arm64 op, G30 is `checkNL30`. -/
theorem checkG30_nl {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG30 lc ps bstart g = r) : checkNL30 lc ps bstart g = r := by
  simpa [checkG30, hl] using h

/-- What `vkindNL30` accepted of a value that is not an entry value: no temporary, and either a
`Convert` in its argument's register of class 64 with the memory last (no code), or what
`vkindNL` accepts. -/
theorem vkindNL30_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkindNL30 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧
      ((v.op = .Convert ∧ v.args.size = 2 ∧
          (∃ o, argObj lc v 0 = .ok (64, o) ∧ resObj lc v = .ok (64, o)) ∧
          memArg lc v 1 = .ok () ∧ kd = .none) ∨
        ((v.op = .MakeResult ∨ v.op = .InlMark ∨ v.op = .Copy) ∧
          ∃ kd1, kd = kd1.v2 ∧ VK lc v kd1)) := by
  unfold vkindNL30 at h
  split at h
  · rename_i hop
    simp only [beq_iff_eq] at hop
    obtain ⟨ht, hsz, ho, hm, rfl⟩ := convKind_spec h
    exact ⟨ht, .inl ⟨hop, hsz, ho, hm, rfl⟩⟩
  · obtain ⟨ht, hops, hk⟩ := vkindNL_spec h hen
    exact ⟨ht, .inr ⟨hops, hk⟩⟩

/-- What `checkNL30` accepted: `checkNL_spec`'s facts with `vkindNL30`. -/
theorem checkNL30_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkNL30 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkindNL30 lc g ∧ c.tm = c.cx.termG3 ∧
      allRet lc = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK lc = true := by
  unfold checkNL30 at h
  obtain ⟨hr, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
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
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hr, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd⟩
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
