import GoFV.Gen.Check12
import GoFV.Proof.Gen.Spec11

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G12 accepted (`docs/plans/proofs3.md` §4)

`checkG12 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G12.lean`) uses (`checkG12_spec`): G11's (`Spec11.lean`) with G12's value check
(`vkind12_spec`, `VK12`: G11's values and `Convert` in its argument's register).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind12` accepted of a value that is not an entry value, and what it emits. -/
inductive VK12 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G11. -/
  | g11 {kd : VKind2} : VK11 lc g v kd → VK12 lc g v kd
  /-- A pointer conversion: the argument and the value in one register of class 64, the memory
  last; no code. -/
  | conv {o : Int} : v.op = .Convert → v.args.size = 2 → argObj lc v 0 = .ok (64, o) →
      resObj lc v = .ok (64, o) → memArg lc v 1 = .ok () → VK12 lc g v .none

/-- What `convKind` accepted. -/
theorem convKind_spec {lc : LocCtx} {v : Value} {kd : VKind2} (h : convKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ v.args.size = 2 ∧
      (∃ o, argObj lc v 0 = .ok (64, o) ∧ resObj lc v = .ok (64, o)) ∧ memArg lc v 1 = .ok () ∧
      kd = .none := by
  unfold convKind at h
  obtain ⟨ht, h1⟩ := ex_guard h
  obtain ⟨hsz, h2⟩ := ex_guard h1
  obtain ⟨⟨ca, ra⟩, ha, h3⟩ := ex_bind_eq_ok h2
  obtain ⟨⟨cd, rd⟩, hr, h4⟩ := ex_bind_eq_ok h3
  obtain ⟨⟨⟩, hm, h5⟩ := ex_bind_eq_ok h4
  simp only [beq_iff_eq] at ht
  refine ⟨ht, by simpa using hsz, ?_⟩
  split at h5
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
    simp only [ex_pure, Except.ok.injEq] at h5
    exact ⟨⟨ra, ha, hr⟩, hm, h5.symm⟩
  · exact (ex_throw_bind h5).elim

/-- What `vkind12` accepted of a value that is not an entry value: no temporary, and `VK12`. -/
theorem vkind12_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind12 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK12 lc g v kd := by
  unfold vkind12 at h
  split at h
  · rename_i hop
    simp only [beq_iff_eq] at hop
    obtain ⟨ht, hsz, ⟨o, ha, hr⟩, hm, rfl⟩ := convKind_spec h
    exact ⟨ht, .conv hop hsz ha hr hm⟩
  · obtain ⟨ht, h11⟩ := vkind11_spec h hen
    exact ⟨ht, .g11 h11⟩

/-- What `checkG12` accepted: G11's facts with G12's value check. -/
theorem checkG12_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG12 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind12 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG12 at h
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
