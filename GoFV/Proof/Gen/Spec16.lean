import GoFV.Gen.Check16
import GoFV.Proof.Gen.Spec15

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G16 accepted (`docs/plans/proofs3.md` §4)

`checkG16 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G16.lean`) uses (`checkG16_spec`): G15's (`Spec15.lean`) with G16's value check
(`vkind16_spec`, `VK16`: G15's values and `ADDshiftLL`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind16` accepted of a value that is not an entry value, and what it emits. -/
inductive VK16 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G15. -/
  | g15 {kd : VKind2} : VK15 lc g v kd → VK16 lc g v kd
  /-- `ADDshiftLL [k] x y`: two register arguments, a result of at least 8 bits no wider than
  either, `0 ≤ k < 64`; one `ADD Rm<<k, Rn, Rd`. -/
  | addSh {ca cb c : Nat} {rn rm rd : Int} :
      v.op = .ARM64ADDshiftLL → v.args.size = 2 → 0 ≤ v.auxInt.toInt → v.auxInt.toInt < 64 →
      argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) →
      8 ≤ c → c ≤ ca → c ≤ cb →
      VK16 lc g v (.prog (.ofShape
        { as := .ADD, from_ := shiftLLA rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }))

/-- What `addShKind` accepted. -/
theorem addShKind_spec {lc : LocCtx} {v : Value} {kd : VKind2} (h : addShKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ v.args.size = 2 ∧ 0 ≤ v.auxInt.toInt ∧
      v.auxInt.toInt < 64 ∧ ∃ ca cb c rn rm rd,
      argObj lc v 0 = .ok (ca, rn) ∧ argObj lc v 1 = .ok (cb, rm) ∧ resObj lc v = .ok (c, rd) ∧
      8 ≤ c ∧ c ≤ ca ∧ c ≤ cb ∧
      kd = .prog (.ofShape
        { as := .ADD, from_ := shiftLLA rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }) := by
  unfold addShKind at h
  obtain ⟨ht, h1⟩ := ex_guard h
  obtain ⟨hsz, h2⟩ := ex_guard h1
  obtain ⟨hk, h3⟩ := ex_guard h2
  obtain ⟨⟨ca, rn⟩, ha, h4⟩ := ex_bind_eq_ok h3
  obtain ⟨⟨cb, rm⟩, hb, h5⟩ := ex_bind_eq_ok h4
  obtain ⟨⟨c, rd⟩, hr, h6⟩ := ex_bind_eq_ok h5
  obtain ⟨hw, h7⟩ := ex_guard h6
  simp only [ex_pure, Except.ok.injEq] at h7
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk hw
  exact ⟨ht, hsz, hk.1, hk.2, ca, cb, c, rn, rm, rd, ha, hb, hr, hw.1.1, hw.1.2, hw.2, h7.symm⟩

/-- What `vkind16` accepted of a value that is not an entry value: no temporary, and `VK16`. -/
theorem vkind16_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind16 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK16 lc g v kd := by
  unfold vkind16 at h
  by_cases hop : v.op = .ARM64ADDshiftLL
  · simp only [hop, beq_self_eq_true, ↓reduceIte] at h
    obtain ⟨ht, hsz, hk0, hk64, ca, cb, c, rn, rm, rd, ha, hb, hr, h8, hca, hcb, rfl⟩ :=
      addShKind_spec h
    exact ⟨ht, .addSh hop hsz hk0 hk64 ha hb hr h8 hca hcb⟩
  · simp only [beq_iff_eq, hop, ↓reduceIte] at h
    obtain ⟨ht, h15⟩ := vkind15_spec h hen
    exact ⟨ht, .g15 h15⟩

/-- What `checkG16` accepted: G15's facts with G16's value check. -/
theorem checkG16_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG16 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind16 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG16 at h
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
