import GoFV.Gen.Check42
import GoFV.Proof.Gen.Spec41

/-!
# What `checkG42` accepted (`GoFV/Gen/Check42.lean`)

`VK42`: G41's kinds (`VK41`, through `vkind41`) and `ANDconst` widening a narrow argument
(`vkind42_spec`); on `InitMem`, `vkind42` is `vkind40` (`vkind42_initMem`). `checkG42L_spec` is
`checkG41L_spec` with `vkind42`, and `checkG42_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind42` accepted of a value that is not an entry value, and what it emits. -/
inductive VK42 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G41. -/
  | g41 {kd : VKind2} : VK41 lc g v kd → VK42 lc g v kd
  /-- `ANDconst [k] x` of class `c ≥ 8`, `0 ≤ k < 2^ca` with `ca` the class of `x`:
  `AND $k, Rn, Rd`. -/
  | andW {ca c : Nat} {rn rd : Int} : v.op = .ARM64ANDconst → v.args.size = 1 →
      argObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) → 8 ≤ c → 0 ≤ v.auxInt.toInt →
      v.auxInt.toInt < 2 ^ ca →
      VK42 lc g v (.prog (.ofShape
        { as := .AND, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }))

/-- What `andWKind` accepted: no temporary, and `VK42`'s `andW`. -/
theorem andWKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64ANDconst) (h : andWKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK42 lc g v kd := by
  unfold andWKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hk, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  exact ⟨ht, .andW hop hsz hao hro hk.1.1 hk.1.2 hk.2⟩

/-- What `vkind42` accepted of a value that is not an entry value: no temporary, and `VK42`. -/
theorem vkind42_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind42 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK42 lc g v kd := by
  unfold vkind42 at h
  cases h41 : vkind41 lc g v with
  | ok kd' =>
    rw [h41] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind41_spec h41 hen
    exact ⟨ht, .g41 hVK⟩
  | error e =>
    rw [h41] at h
    by_cases hc : v.op = .ARM64ANDconst
    · simp only [hc, beq_self_eq_true, ↓reduceIte] at h
      exact andWKind_spec hc h
    · have hc' : (v.op == .ARM64ANDconst) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
      cases h

/-- On `InitMem`, `vkind42` is `vkind40`. -/
theorem vkind42_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind42 lc g v = vkind40 lc g v := by
  unfold vkind42
  rw [vkind41_initMem hop]
  cases vkind40 lc g v with
  | ok _ => rfl
  | error e => simp [hop]

/-- On a function with no arm64 op, G42's check is G33. -/
theorem checkG33_of_42L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG42L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG42L, hl] using h

/-- What `checkG42L` accepted of a function with an arm64 op: G41's facts with G42's value
check. -/
theorem checkG42L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG42L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind42 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG42L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
  simp only [Bool.and_eq_true] at hmovd
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
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd.1, hmovd.2⟩
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

/-- What `checkG42` accepted: `refsLive`, and G42's check on the context without the removed
homes. -/
theorem checkG42_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG42 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG42L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG42 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
