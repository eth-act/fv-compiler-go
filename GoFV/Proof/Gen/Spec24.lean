import GoFV.Gen.Check24
import GoFV.Proof.Gen.Spec23

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G24 accepted (`docs/plans/proofs3.md` §4)

`checkG24 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G24.lean`) uses (`checkG24_spec`): G23's (`Spec23.lean`) with G24's value check
(`vkind24_spec`, `VK24`: G23's values, and `SP` as a value without code).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind24` accepted of a value that is not an entry value, and what it emits. -/
inductive VK24 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G23 (not `SP`). -/
  | g23 {kd : VKind2} : v.op ≠ .SP → VK23 lc g v kd → VK24 lc g v kd
  /-- `SP`: no code, no argument, a register shape, no home or the home `SP`. -/
  | sp : v.op = .SP → v.args.size = 0 → (cls (lc.ty v.id)).isSome = true →
      (lc.home v.id = none ∨ lc.home v.id = some (.reg spReg)) → VK24 lc g v .none

/-- An activation value of G24 is one of G3's. -/
theorem entryOp3_of_24 {op : Op} (h : entryOp24 op = false) (hsp : op ≠ .SP) :
    entryOp3 op = false := by
  unfold entryOp24 at h
  have : (op != .SP) = true := by simpa using hsp
  rw [this, Bool.and_true] at h
  exact h

/-- G3's activation values are G24's. -/
theorem entryOp24_of_3 {op : Op} (h : entryOp3 op = false) : entryOp24 op = false := by
  unfold entryOp24; rw [h, Bool.false_and]

/-- What `vkind24` accepted of a value that is not an entry value: no temporary, and `VK24`. -/
theorem vkind24_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind24 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK24 lc g v kd := by
  unfold vkind24 at h
  by_cases hsp : v.op = .SP
  · simp only [hsp, beq_self_eq_true, ↓reduceIte] at h
    obtain ⟨ht, h⟩ := ex_guard h
    simp only [beq_iff_eq] at ht
    obtain ⟨hs, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
    simp only [ex_pure, Except.ok.injEq] at h
    subst h
    exact ⟨ht, .sp hsp hs.1.1 hs.1.2 hs.2⟩
  · have hne : (v.op == .SP) = false := by simpa using hsp
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨ht, h23⟩ := vkind23_spec h (entryOp3_of_24 hen hsp)
    exact ⟨ht, .g23 hsp h23⟩

/-- What `checkG24` accepted: G23's facts with G24's value check. -/
theorem checkG24_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG24 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind24 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK lc = true := by
  unfold checkG24 at h
  obtain ⟨hl, h⟩ := ex_guard h
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
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
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
