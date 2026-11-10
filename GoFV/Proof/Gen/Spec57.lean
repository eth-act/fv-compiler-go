import GoFV.Gen.Check57
import GoFV.Proof.Gen.Spec55
import GoFV.Proof.Gen.Spec57a
import GoFV.Proof.Gen.Spec57b

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG57` accepted (`GoFV/Gen/Check57.lean`)

`VK57`: G55's kinds (`VK55`, through `vkind55`) and G57's groups A (`VK57a`, `Spec57a.lean`) and B
(`VK57b`, `Spec57b.lean`), each with no temporary. On `InitMem`, `vkind57` is `vkind55`
(`vkind57_initMem`).
`checkG57L_spec` is `checkG55L_spec` with `vkind57`, and `checkG57_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind57` accepted of a value that is not an entry value, and what it emits. -/
inductive VK57 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G55. -/
  | g55 {kd : VKind2} : VK55 lc g v kd → VK57 lc g v kd
  /-- A value of G57's group A (`Check57a.lean`), with no temporary. -/
  | a {kd : VKind2} : (lc.temps[v.id]?).join = none → VK57a lc g v kd → VK57 lc g v kd
  /-- A value of G57's group B (`Check57b.lean`), with no temporary. -/
  | b {kd : VKind2} : (lc.temps[v.id]?).join = none → VK57b lc g v kd → VK57 lc g v kd

/-- What `vkind57` accepted of a value that is not an entry value. -/
theorem vkind57_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind57 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK57 lc g v kd := by
  unfold vkind57 at h
  cases h55 : vkind55 lc g v with
  | ok kd' =>
    rw [h55] at h
    cases h
    exact .g55 (vkind55_spec h55 hen)
  | error e =>
    rw [h55] at h
    simp only at h
    cases ha : vkind57a lc g v with
    | some r =>
      rw [ha] at h
      subst h
      obtain ⟨ht, hVK⟩ := vkind57a_spec ha
      exact .a ht hVK
    | none =>
      rw [ha] at h
      simp only at h
      cases hb : vkind57b lc g v with
      | some r =>
        rw [hb] at h
        subst h
        obtain ⟨ht, hVK⟩ := vkind57b_spec hb
        exact .b ht hVK
      | none =>
        rw [hb] at h
        cases h

/-- On `InitMem`, `vkind57` is `vkind55`. -/
theorem vkind57_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind57 lc g v = vkind55 lc g v := by
  unfold vkind57
  cases vkind55 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind57a_none (by rw [hop]; rfl), vkind57b_none (by rw [hop]; rfl)]

/-- On a function with no arm64 op, G57's check is G33. -/
theorem checkG33_of_57L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG57L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG57L, hl] using h

/-- What `checkG57L` accepted of a function with an arm64 op: G55's facts with G57's value
check. -/
theorem checkG57L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG57L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind57 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true := by
  simp only [checkG57L, hl, ↓reduceIte] at h
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

/-- What `checkG57` accepted: `refsLive`, and `checkG57L` on `liveCtx`. -/
theorem checkG57_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG57 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG57L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG57 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
