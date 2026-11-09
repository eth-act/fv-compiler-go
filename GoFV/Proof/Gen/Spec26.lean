import GoFV.Gen.Check26
import GoFV.Proof.Gen.Spec25

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G26 accepted (`docs/plans/proofs3.md` §4)

`checkG26 lc ps bstart g = .ok (tab, kt)` unfolded (`checkG26_lowered`, `checkNL_spec`): on a
function with an arm64 op, `checkG25`'s acceptance; on one without, G25's facts with the value
check `vkindNL` (`vkindNL_spec`: G1's `MakeResult`, `InlMark` and `Copy`) and `Ret` blocks only.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- On a function with an arm64 op, G26 is G25. -/
theorem checkG26_lowered {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = true)
    (h : checkG26 lc ps bstart g = r) : checkG25 lc ps bstart g = r := by
  simpa [checkG26, hl] using h

/-- On a function with no arm64 op, G26 is `checkNL`. -/
theorem checkG26_nl {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG26 lc ps bstart g = r) : checkNL lc ps bstart g = r := by
  simpa [checkG26, hl] using h

/-- What `vkindNL` accepted of a value that is not an entry value: no temporary, a G1 value
(`VK`) whose op is `MakeResult`, `InlMark` or `Copy`, emitting what G1 emits. -/
theorem vkindNL_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkindNL lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧
      (v.op = .MakeResult ∨ v.op = .InlMark ∨ v.op = .Copy) ∧
      ∃ kd1, kd = kd1.v2 ∧ VK lc v kd1 := by
  unfold vkindNL at h
  cases hc : (v.op == .MakeResult || v.op == .InlMark || v.op == .Copy) with
  | true =>
    simp only [hc, ↓reduceIte] at h
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    have hen1 : entryOp v.op = false := by
      rcases hc with (h1 | h1) | h1 <;> rw [h1] <;> rfl
    obtain ⟨kd1, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨ht, hvk⟩ := vkind_spec hk hen1
    simp only [ex_pure, Except.ok.injEq] at h
    refine ⟨ht, by rcases hc with (h1 | h1) | h1 <;> simp [h1], kd1, ?_, hvk⟩
    rw [← h]
    cases kd1 <;> rfl
  | false =>
    simp only [hc, Bool.false_eq_true, ↓reduceIte, hen] at h
    simp only [ex_throw, reduceCtorEq] at h

/-- An `allRet` function's blocks have kind `Ret`. -/
theorem allRet_spec {lc : LocCtx} (h : allRet lc = true) {bid : ID} {blk : Block}
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk) :
    blk.kind = .Ret := by
  unfold allRet at h
  have := List.all_eq_true.1 h bid hbid
  rw [hb] at this
  simpa using this

/-- What `checkNL` accepted: G25's facts (`checkG25_spec`) with `vkindNL` and `Ret` blocks, on a
function with no arm64 op. -/
theorem checkNL_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkNL lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkindNL lc g ∧ c.tm = c.cx.termG3 ∧
      allRet lc = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK lc = true := by
  unfold checkNL at h
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
