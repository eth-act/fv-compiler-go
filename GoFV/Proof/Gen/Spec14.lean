import GoFV.Gen.Check14
import GoFV.Proof.Gen.Spec13

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G14 accepted (`docs/plans/proofs3.md` §4)

`checkG14 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G14.lean`) uses (`checkG14_spec`): G13's (`Spec13.lean`) with G14's value check
(`vkind14_spec`, `VK14`: G13's values and the register-index loads of `loadIdxOp?`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind14` accepted of a value that is not an entry value, and what it emits. -/
inductive VK14 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G13. -/
  | g13 {kd : VKind2} : VK13 lc g v kd → VK14 lc g v kd
  /-- A register-index load: `ptr` and `idx` in registers of class 64, the memory last, the
  destination as a load's; one load from `idxA`. -/
  | idx {as : As} {n sh : Nat} {sg : Bool} {c : Nat} {rn ri rd : Int} :
      loadIdxOp? v.op = some (as, n, sh, sg) → v.args.size = 3 → argObj lc v 0 = .ok (64, rn) →
      argObj lc v 1 = .ok (64, ri) → memArg lc v 2 = .ok () → resObj lc v = .ok (c, rd) →
      (8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false) →
      VK14 lc g v (.prog ⟨plain as (· == idxA rn ri sh) (· == regA rd), as.name⟩)

/-- What `idxKind` accepted. -/
theorem idxKind_spec {lc : LocCtx} {v : Value} {as : As} {n sh : Nat} {sg : Bool} {kd : VKind2}
    (h : idxKind lc v as n sh sg = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ v.args.size = 3 ∧ ∃ rn ri c rd,
      argObj lc v 0 = .ok (64, rn) ∧ argObj lc v 1 = .ok (64, ri) ∧ memArg lc v 2 = .ok () ∧
      resObj lc v = .ok (c, rd) ∧ (8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false) ∧
      kd = .prog ⟨plain as (· == idxA rn ri sh) (· == regA rd), as.name⟩ := by
  unfold idxKind at h
  obtain ⟨ht, h1⟩ := ex_guard h
  obtain ⟨hsz, h2⟩ := ex_guard h1
  obtain ⟨⟨ca, rn⟩, ha, h3⟩ := ex_bind_eq_ok h2
  obtain ⟨⟨ci, ri⟩, hi, h4⟩ := ex_bind_eq_ok h3
  obtain ⟨hc64, h5⟩ := ex_guard h4
  obtain ⟨⟨⟩, hm, h6⟩ := ex_bind_eq_ok h5
  obtain ⟨⟨c, rd⟩, hr, h7⟩ := ex_bind_eq_ok h6
  obtain ⟨hw, h8⟩ := ex_guard h7
  simp only [ex_pure, Except.ok.injEq] at h8
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, beq_iff_eq] at hc64
  obtain ⟨rfl, rfl⟩ := hc64
  refine ⟨ht, hsz, rn, ri, c, rd, ha, hi, hm, hr, ?_, h8.symm⟩
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
    at hw
  rcases hw with hw | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl hw
  · exact Or.inr ⟨h1, h2, h3⟩

/-- What `vkind14` accepted of a value that is not an entry value: no temporary, and `VK14`. -/
theorem vkind14_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind14 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK14 lc g v kd := by
  unfold vkind14 at h
  split at h
  · rename_i as n sh sg hop
    obtain ⟨ht, hsz, rn, ri, c, rd, ha, hi, hm, hr, hw, rfl⟩ := idxKind_spec h
    exact ⟨ht, .idx hop hsz ha hi hm hr hw⟩
  · obtain ⟨ht, h13⟩ := vkind13_spec h hen
    exact ⟨ht, .g13 h13⟩

/-- What `checkG14` accepted: G13's facts with G14's value check. -/
theorem checkG14_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG14 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind14 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG14 at h
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
