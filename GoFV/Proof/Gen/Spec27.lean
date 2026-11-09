import GoFV.Gen.Check27
import GoFV.Proof.Gen.Spec26

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G27 accepted (`docs/plans/proofs3.md` §4)

`checkG27 lc ps bstart g = .ok (tab, kt)` unfolded: on a function with an arm64 op, G25's facts
(`checkG27_spec`) with G27's value check (`vkind27_spec`, `VK27`: G25's values, the shifted
logic ops as `AND`/`ORR`/`EOR`/`BIC Rm SHIFT k, Rn, Rd`); on one without, G26's
(`checkG26_of_27`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind27` accepted of a value that is not an entry value, and what it emits. -/
inductive VK27 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G25 (no shifted logic op). -/
  | g25 {kd : VKind2} : logSh? v.op = none → VK25 lc g v kd → VK27 lc g v kd
  /-- `op [k] x y`: `op Rm SHIFT k, Rn, Rd`. -/
  | logSh {as : As} {typ ca cb c : Nat} {rn rm rd : Int} :
      logSh? v.op = some (as, typ) → v.args.size = 2 → 0 ≤ v.auxInt.toInt →
      v.auxInt.toInt < 64 → argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → c ≤ ca → (typ = 0 → c ≤ cb) → (typ ≠ 0 → cb = 64) →
      VK27 lc g v (.prog (.ofShape
        { as, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }))

/-- What `logShKind` accepted: no temporary, and `VK27`'s `logSh`. -/
theorem logShKind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {typ : Nat}
    {kd : VKind2} (hop : logSh? v.op = some (as, typ)) (h : logShKind lc v as typ = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK27 lc g v kd := by
  unfold logShKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨hk, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨h8, hca⟩, hcb⟩ := hw
  refine ⟨ht, .logSh hop hsz hk.1 hk.2 hao hbo hro h8 hca (fun h0 => ?_) (fun h0 => ?_)⟩
  · simpa [h0] using hcb
  · simpa [h0] using hcb

/-- What `vkind27` accepted of a value that is not an entry value: no temporary, and `VK27`. -/
theorem vkind27_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind27 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK27 lc g v kd := by
  unfold vkind27 at h
  cases hs : logSh? v.op with
  | some p =>
    rw [hs] at h
    exact logShKind_spec hs h
  | none =>
    rw [hs] at h
    obtain ⟨htm, h25⟩ := vkind25_spec h hen
    exact ⟨htm, .g25 hs h25⟩

/-- On a function with no arm64 op, G27 is G26. -/
theorem checkG26_of_27 {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG27 lc ps bstart g = r) : checkG26 lc ps bstart g = r := by
  simpa [checkG26, checkG27, hl] using h

/-- What `checkG27` accepted of a function with an arm64 op: G25's facts with G27's value check. -/
theorem checkG27_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG27 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind27 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK lc = true := by
  simp only [checkG27, hl, ↓reduceIte] at h
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
