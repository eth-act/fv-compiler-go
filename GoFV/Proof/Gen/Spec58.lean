import GoFV.Gen.Check58
import GoFV.Proof.Gen.Spec48
import GoFV.Proof.Gen.Spec58a

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG58` accepted (`GoFV/Gen/Check58.lean`)

`VK58`: G48's kinds (`VK48`, through `vkind48`) and G58's group A (`VK58a`, `Spec58a.lean`), with no
temporary. On `InitMem`, `vkind58` is `vkind48` (`vkind58_initMem`).
`checkG58L_spec` is `checkG48L_spec` with `vkind58`, and `checkG58_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind58` accepted of a value that is not an entry value, and what it emits. -/
inductive VK58 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G48. -/
  | g48 {kd : VKind2} : VK48 lc g v kd → VK58 lc g v kd
  /-- A value of G58's group A (`Check58a.lean`), with no temporary. -/
  | a {kd : VKind2} : (lc.temps[v.id]?).join = none → VK58a lc v kd → VK58 lc g v kd

/-- What `vkind58` accepted of a value that is not an entry value. -/
theorem vkind58_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind58 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK58 lc g v kd := by
  unfold vkind58 at h
  cases h48 : vkind48 lc g v with
  | ok kd' =>
    rw [h48] at h
    cases h
    exact .g48 (vkind48_spec h48 hen)
  | error e =>
    rw [h48] at h
    simp only at h
    cases ha : vkind58a lc g v with
    | some r =>
      rw [ha] at h
      subst h
      obtain ⟨ht, hVK⟩ := vkind58a_spec ha
      exact .a ht hVK
    | none =>
      rw [ha] at h
      cases h

/-- On `InitMem`, `vkind58` is `vkind48`. -/
theorem vkind58_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind58 lc g v = vkind48 lc g v := by
  unfold vkind58
  cases vkind48 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind58a_none (by rw [hop]; rfl)]

/-- On a function with no arm64 op, G58's check is G33. -/
theorem checkG33_of_58L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG58L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG58L, hl] using h

/-- What `checkG58L` accepted of a function with an arm64 op: G48's facts with G58's value
check. -/
theorem checkG58L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG58L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind58 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true ∧
      spHomes48 lc = true := by
  simp only [checkG58L, hl, ↓reduceIte] at h
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

/-- What `checkG58` accepted: `refsLive`, and `checkG58L` on `liveCtx`. -/
theorem checkG58_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG58 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG58L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG58 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
