import GoFV.Gen.Check18
import GoFV.Proof.Gen.Spec17

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G18 accepted (`docs/plans/proofs3.md` §4)

`checkG18 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G18.lean`) uses (`checkG18_spec`): G17's (`Spec17.lean`) with G18's value check
(`vkind18_spec`, `VK18`: G17's values and the register-index stores of `storeIdxOp?`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind18` accepted of a value that is not an entry value, and what it emits. -/
inductive VK18 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G17. -/
  | g17 {kd : VKind2} : VK17 lc g v kd → VK18 lc g v kd
  /-- A register-index store: the memory shape and no home, `ptr` and `idx` in registers of class
  64, `val` in a register as a store's, the memory last; one store to `idxA`. -/
  | stIdx {as : As} {n sh : Nat} {cs : Nat} {rn ri rs : Int} :
      storeIdxOp? v.op = some (as, n, sh) → v.args.size = 4 → memTy (lc.ty v.id) = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rn) → argObj lc v 1 = .ok (64, ri) →
      argObj lc v 2 = .ok (cs, rs) → memArg lc v 3 = .ok () → (8 * n ≤ cs ∨ cs = 1 ∧ n = 1) →
      VK18 lc g v (.prog ⟨plain as (· == regA rs) (· == idxA rn ri sh), as.name⟩)

/-- What `stIdxKind` accepted. -/
theorem stIdxKind_spec {lc : LocCtx} {v : Value} {as : As} {n sh : Nat} {kd : VKind2}
    (h : stIdxKind lc v as n sh = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ v.args.size = 4 ∧ memTy (lc.ty v.id) = true ∧
      lc.home v.id = none ∧ ∃ rn ri cs rs,
      argObj lc v 0 = .ok (64, rn) ∧ argObj lc v 1 = .ok (64, ri) ∧ argObj lc v 2 = .ok (cs, rs) ∧
      memArg lc v 3 = .ok () ∧ (8 * n ≤ cs ∨ cs = 1 ∧ n = 1) ∧
      kd = .prog ⟨plain as (· == regA rs) (· == idxA rn ri sh), as.name⟩ := by
  unfold stIdxKind at h
  obtain ⟨ht, h1⟩ := ex_guard h
  obtain ⟨hsz, h2⟩ := ex_guard h1
  obtain ⟨⟨ca, rn⟩, ha, h3⟩ := ex_bind_eq_ok h2
  obtain ⟨⟨ci, ri⟩, hi, h4⟩ := ex_bind_eq_ok h3
  obtain ⟨hc64, h5⟩ := ex_guard h4
  obtain ⟨⟨cs, rs⟩, hso, h6⟩ := ex_bind_eq_ok h5
  obtain ⟨hw, h7⟩ := ex_guard h6
  obtain ⟨⟨⟩, hm, h8⟩ := ex_bind_eq_ok h7
  simp only [ex_pure, Except.ok.injEq] at h8
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hsz
  simp only [Bool.and_eq_true, beq_iff_eq] at hc64
  obtain ⟨rfl, rfl⟩ := hc64
  refine ⟨ht, hsz.1.1, hsz.1.2, hsz.2, rn, ri, cs, rs, ha, hi, hso, hm, ?_, h8.symm⟩
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hw
  exact hw

/-- What `vkind18` accepted of a value that is not an entry value: no temporary, and `VK18`. -/
theorem vkind18_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind18 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK18 lc g v kd := by
  unfold vkind18 at h
  split at h
  · rename_i as n sh hop
    obtain ⟨ht, hsz, hmt, hhn, rn, ri, cs, rs, ha, hi, hso, hm, hw, rfl⟩ := stIdxKind_spec h
    exact ⟨ht, .stIdx hop hsz hmt hhn ha hi hso hm hw⟩
  · obtain ⟨ht, h17⟩ := vkind17_spec h hen
    exact ⟨ht, .g17 h17⟩

/-- What `checkG18` accepted: G17's facts with G18's value check. -/
theorem checkG18_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG18 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind18 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG18 at h
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
