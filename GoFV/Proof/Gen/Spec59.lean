import GoFV.Gen.Check59
import GoFV.Proof.Gen.Spec58
import GoFV.Proof.Gen.Spec59p

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG59` accepted (`GoFV/Gen/Check59.lean`)

`VK59`: G58's kinds (`VK58`, through `vkind58`) and G59's group P (`VK59p`, `Spec59p.lean`), with no
temporary. On `InitMem`, `vkind59` is `vkind58` (`vkind59_initMem`).
`checkG59L_spec` is `checkG58L_spec` with `vkind59`, and `checkG59_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind59` accepted of a value that is not an entry value, and what it emits. -/
inductive VK59 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G58. -/
  | g58 {kd : VKind2} : VK58 lc g v kd → VK59 lc g v kd
  /-- A value of G59's group P (`Check59p.lean`), with no temporary. -/
  | p {kd : VKind2} : (lc.temps[v.id]?).join = none → VK59p lc g v kd → VK59 lc g v kd

/-- What `vkind59` accepted of a value that is not an entry value. -/
theorem vkind59_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind59 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK59 lc g v kd := by
  unfold vkind59 at h
  cases h58 : vkind58 lc g v with
  | ok kd' =>
    rw [h58] at h
    cases h
    exact .g58 (vkind58_spec h58 hen)
  | error e =>
    rw [h58] at h
    simp only at h
    cases hp : vkind59p lc g v with
    | some r =>
      rw [hp] at h
      subst h
      obtain ⟨ht, hVK⟩ := vkind59p_spec hp
      exact .p ht hVK
    | none =>
      rw [hp] at h
      cases h

/-- On `InitMem`, `vkind59` is `vkind58`. -/
theorem vkind59_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind59 lc g v = vkind58 lc g v := by
  unfold vkind59
  cases vkind58 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind59p_none (by rw [hop]; rfl)]

/-- On a function with no arm64 op, G59's check is G33. -/
theorem checkG33_of_59L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG59L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG59L, hl] using h

/-- What `checkG59L` accepted of a function with an arm64 op: G58's facts with G59's value
check. -/
theorem checkG59L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG59L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind59 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true ∧
      spHomes48 lc = true := by
  simp only [checkG59L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hlp, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
  simp only [Bool.and_eq_true] at hmovd
  cases hf : List.find? (fun x => !homeOK10 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨-, h⟩ := ex_guard h
    obtain ⟨hsph, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd.1, hmovd.2, hlp,
      hsph⟩
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

/-- What `checkG59` accepted: `refsLive`, and `checkG59L` on `liveCtx`. -/
theorem checkG59_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG59 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG59L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG59 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
