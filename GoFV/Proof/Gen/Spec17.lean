import GoFV.Gen.Check17
import GoFV.Proof.Gen.Spec16

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G17 accepted (`docs/plans/proofs3.md` §4)

`checkG17 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G17.lean`) uses (`checkG17_spec`): G16's (`Spec16.lean`) with G17's value check
(`vkind17_spec`, `VK17`: G16's values and `GetG`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind17` accepted of a value that is not an entry value, and what it emits. -/
inductive VK17 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G16. -/
  | g16 {kd : VKind2} : VK16 lc g v kd → VK17 lc g v kd
  /-- The goroutine: the memory its only argument, homed in `g` at a 64-bit shape; no code. -/
  | getG : v.op = .GetG → v.args.size = 1 → memArg lc v 0 = .ok () →
      lc.home v.id = some (.reg gReg) → cls (lc.ty v.id) = some 64 → VK17 lc g v .none

/-- What `getGKind` accepted. -/
theorem getGKind_spec {lc : LocCtx} {v : Value} {kd : VKind2} (h : getGKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ v.args.size = 1 ∧ memArg lc v 0 = .ok () ∧
      lc.home v.id = some (.reg gReg) ∧ cls (lc.ty v.id) = some 64 ∧ kd = .none := by
  unfold getGKind at h
  obtain ⟨ht, h1⟩ := ex_guard h
  obtain ⟨hs, h2⟩ := ex_guard h1
  obtain ⟨⟨⟩, hm, h3⟩ := ex_bind_eq_ok h2
  simp only [ex_pure, Except.ok.injEq] at h3
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  exact ⟨ht, hs.1.1, hm, hs.1.2, hs.2, h3.symm⟩

/-- What `vkind17` accepted of a value that is not an entry value: no temporary, and `VK17`. -/
theorem vkind17_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind17 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK17 lc g v kd := by
  unfold vkind17 at h
  by_cases hop : v.op = .GetG
  · simp only [hop, beq_self_eq_true, ↓reduceIte] at h
    obtain ⟨ht, hsz, hm, hh, hc, rfl⟩ := getGKind_spec h
    exact ⟨ht, .getG hop hsz hm hh hc⟩
  · simp only [beq_iff_eq, hop, ↓reduceIte] at h
    obtain ⟨ht, h16⟩ := vkind16_spec h hen
    exact ⟨ht, .g16 h16⟩

/-- What `checkG17` accepted: G16's facts with G17's value check. -/
theorem checkG17_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG17 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind17 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG17 at h
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
