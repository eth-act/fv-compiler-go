import GoFV.Gen.Check53
import GoFV.Proof.Gen.Spec52
import GoFV.Proof.Gen.Spec53a

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG53` accepted (`GoFV/Gen/Check53.lean`)

`VK53`: G52's kinds (`VK52`, through `vkind52`) and `LoweredMove` (`VK53a`, `Spec53a.lean`). On
`InitMem`, `vkind53` is `vkind52` (`vkind53_initMem`), and so on any op but `LoweredMove`
(`vkind53_eq52`). `checkG53L_spec` is `checkG52L_spec` with `vkind53`, and `checkG53_spec` splits
off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind53` accepted of a value that is not an entry value, and what it emits. -/
inductive VK53 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G52. -/
  | g52 {kd : VKind2} : VK52 lc g v kd → VK53 lc g v kd
  /-- A `LoweredMove` of G53 (`Check53a.lean`). -/
  | a {kd : VKind2} : VK53a lc v kd → VK53 lc g v kd

/-- What `vkind53` accepted of a value that is not an entry value: no temporary, and `VK53`. -/
theorem vkind53_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind53 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK53 lc g v kd := by
  unfold vkind53 at h
  cases h52 : vkind52 lc g v with
  | ok kd' =>
    rw [h52] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind52_spec h52 hen
    exact ⟨ht, .g52 hVK⟩
  | error e =>
    rw [h52] at h
    simp only at h
    cases ha : vkind53a lc v with
    | some r =>
      rw [ha] at h
      subst h
      obtain ⟨ht, hVK⟩ := vkind53a_spec ha
      exact ⟨ht, .a hVK⟩
    | none =>
      rw [ha] at h
      cases h

/-- On `InitMem`, `vkind53` is `vkind52`. -/
theorem vkind53_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind53 lc g v = vkind52 lc g v := by
  unfold vkind53
  cases vkind52 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind53a_none (by rw [hop]; rfl)]

/-- On an op off G53's group A, `vkind53` is `vkind52`. -/
theorem vkind53_eq52 {lc : LocCtx} {g : G2In} {v : Value} (h : op53a v.op = false) :
    vkind53 lc g v = vkind52 lc g v := by
  unfold vkind53
  cases vkind52 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind53a_none h]

/-- On a function with no arm64 op, G53's check is G33. -/
theorem checkG33_of_53L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG53L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG53L, hl] using h

/-- What `checkG53L` accepted of a function with an arm64 op: G52's facts with G53's value
check. -/
theorem checkG53L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG53L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind53 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG53L, hl, ↓reduceIte] at h
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

/-- What `checkG53` accepted: `refsLive`, and `checkG53L` on `liveCtx`. -/
theorem checkG53_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG53 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG53L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG53 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
