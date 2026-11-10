import GoFV.Gen.Check54
import GoFV.Proof.Gen.Spec53
import GoFV.Proof.Gen.Spec54a

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG54` accepted (`GoFV/Gen/Check54.lean`)

`VK54`: G53's kinds (`VK53`, through `vkind53`, with no temporary) and the loops (`VK54a`,
`Spec54a.lean`). On `InitMem`, `vkind54` is `vkind53` (`vkind54_initMem`), and so on any op but
the loops (`vkind54_eq53`); on an op of none of G52–G54's groups, `vkind54` is `vkind49`
(`vkind54_eq49`). `checkG54L_spec` is `checkG53L_spec` with `vkind54` and `loopOK`, and
`checkG54_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind54` accepted of a value that is not an entry value, and what it emits. -/
inductive VK54 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G53, with no temporary. -/
  | g53 {kd : VKind2} : (lc.temps[v.id]?).join = none → VK53 lc g v kd → VK54 lc g v kd
  /-- A loop of G54 (`Check54a.lean`). -/
  | a {kd : VKind2} : VK54a lc v kd → VK54 lc g v kd

/-- What `vkind54` accepted of a value that is not an entry value. -/
theorem vkind54_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind54 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK54 lc g v kd := by
  unfold vkind54 at h
  cases h53 : vkind53 lc g v with
  | ok kd' =>
    rw [h53] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind53_spec h53 hen
    exact .g53 ht hVK
  | error e =>
    rw [h53] at h
    simp only at h
    cases ha : vkind54a lc v with
    | some r =>
      rw [ha] at h
      subst h
      exact .a (vkind54a_spec ha)
    | none =>
      rw [ha] at h
      cases h

/-- On `InitMem`, `vkind54` is `vkind53`. -/
theorem vkind54_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind54 lc g v = vkind53 lc g v := by
  unfold vkind54
  cases vkind53 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind54a_none (by rw [hop]; rfl)]

/-- On an op off G54's group A, `vkind54` is `vkind53`. -/
theorem vkind54_eq53 {lc : LocCtx} {g : G2In} {v : Value} (h : op54a v.op = false) :
    vkind54 lc g v = vkind53 lc g v := by
  unfold vkind54
  cases vkind53 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind54a_none h]

/-- On an op of none of G52's, G53's and G54's groups, `vkind54` is `vkind49`. -/
theorem vkind54_eq49 {lc : LocCtx} {g : G2In} {v : Value} (h2 : op52b v.op = false)
    (h3 : op53a v.op = false) (h4 : op54a v.op = false) : vkind54 lc g v = vkind49 lc g v := by
  rw [vkind54_eq53 h4, vkind53_eq52 h3, vkind52_eq49 h2]

/-- On a function with no arm64 op, G54's check is G33. -/
theorem checkG33_of_54L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG54L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG54L, hl] using h

/-- What `checkG54L` accepted of a function with an arm64 op: G53's facts with G54's value check,
and `loopOK`. -/
theorem checkG54L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG54L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind54 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true := by
  simp only [checkG54L, hl, ↓reduceIte] at h
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

/-- What `checkG54` accepted: `refsLive`, and `checkG54L` on `liveCtx`. -/
theorem checkG54_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG54 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG54L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG54 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
