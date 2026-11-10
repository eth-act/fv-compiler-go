import GoFV.Gen.Check55
import GoFV.Proof.Gen.Spec54
import GoFV.Proof.Gen.Spec55a
import GoFV.Proof.Gen.Spec55b

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG55` accepted (`GoFV/Gen/Check55.lean`)

`VK55`: G54's kinds (`VK54`, through `vkind54`) and G55's groups A (`VK55a`, `Spec55a.lean`) and B
(`VK55b`, `Spec55b.lean`), each with no temporary. On `InitMem`, `vkind55` is `vkind54`
(`vkind55_initMem`).
`checkG55L_spec` is `checkG54L_spec` with `vkind55`, and `checkG55_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind55` accepted of a value that is not an entry value, and what it emits. -/
inductive VK55 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G54. -/
  | g54 {kd : VKind2} : VK54 lc g v kd → VK55 lc g v kd
  /-- A value of G55's group A (`Check55a.lean`), with no temporary. -/
  | a {kd : VKind2} : (lc.temps[v.id]?).join = none → VK55a lc v kd → VK55 lc g v kd
  /-- A value of G55's group B (`Check55b.lean`), with no temporary. -/
  | b {kd : VKind2} : (lc.temps[v.id]?).join = none → VK55b lc v kd → VK55 lc g v kd

/-- What `vkind55` accepted of a value that is not an entry value. -/
theorem vkind55_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind55 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK55 lc g v kd := by
  unfold vkind55 at h
  cases h54 : vkind54 lc g v with
  | ok kd' =>
    rw [h54] at h
    cases h
    exact .g54 (vkind54_spec h54 hen)
  | error e =>
    rw [h54] at h
    simp only at h
    cases ha : vkind55a lc v with
    | some r =>
      rw [ha] at h
      subst h
      obtain ⟨ht, hVK⟩ := vkind55a_spec ha
      exact .a ht hVK
    | none =>
      rw [ha] at h
      simp only at h
      cases hb : vkind55b lc v with
      | some r =>
        rw [hb] at h
        subst h
        obtain ⟨ht, hVK⟩ := vkind55b_spec hb
        exact .b ht hVK
      | none =>
        rw [hb] at h
        cases h

/-- On `InitMem`, `vkind55` is `vkind54`. -/
theorem vkind55_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind55 lc g v = vkind54 lc g v := by
  unfold vkind55
  cases vkind54 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind55a_none (by rw [hop]; rfl), vkind55b_none (by rw [hop]; rfl)]

/-- On an op off G55's groups A and B, `vkind55` is `vkind54`. -/
theorem vkind55_eq54 {lc : LocCtx} {g : G2In} {v : Value} (ha : op55a v.op = false)
    (hb : op55b v.op = false) : vkind55 lc g v = vkind54 lc g v := by
  unfold vkind55
  cases vkind54 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind55a_none ha, vkind55b_none hb]

/-- On a function with no arm64 op, G55's check is G33. -/
theorem checkG33_of_55L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG55L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG55L, hl] using h

/-- What `checkG55L` accepted of a function with an arm64 op: G54's facts with G55's value
check. -/
theorem checkG55L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG55L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind55 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true := by
  simp only [checkG55L, hl, ↓reduceIte] at h
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
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd.1, hmovd.2, hlp⟩
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

/-- What `checkG55` accepted: `refsLive`, and `checkG55L` on `liveCtx`. -/
theorem checkG55_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG55 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG55L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG55 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
