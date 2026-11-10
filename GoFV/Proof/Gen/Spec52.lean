import GoFV.Gen.Check52
import GoFV.Proof.Gen.Spec49
import GoFV.Proof.Gen.Spec52b

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG52` accepted (`GoFV/Gen/Check52.lean`)

`VK52`: G49's kinds (`VK49`, through `vkind49`) and the remainders (`VK52b`, `Spec52b.lean`). On
`InitMem`, `vkind52` is `vkind49` (`vkind52_initMem`), and so on any op off G52's group B
(`vkind52_eq49`). `checkG52L_spec` is `checkG49L_spec` with `vkind52`, and `checkG52_spec` splits
off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind52` accepted of a value that is not an entry value, and what it emits. -/
inductive VK52 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G49. -/
  | g49 {kd : VKind2} : VK49 lc g v kd → VK52 lc g v kd
  /-- A remainder of G52 (`Check52b.lean`). -/
  | b {kd : VKind2} : VK52b lc v kd → VK52 lc g v kd

/-- What `vkind52` accepted of a value that is not an entry value: no temporary, and `VK52`. -/
theorem vkind52_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind52 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK52 lc g v kd := by
  unfold vkind52 at h
  cases h49 : vkind49 lc g v with
  | ok kd' =>
    rw [h49] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind49_spec h49 hen
    exact ⟨ht, .g49 hVK⟩
  | error e =>
    rw [h49] at h
    simp only at h
    cases hb : vkind52b lc v with
    | some r =>
      rw [hb] at h
      subst h
      obtain ⟨ht, hVK⟩ := vkind52b_spec hb
      exact ⟨ht, .b hVK⟩
    | none =>
      rw [hb] at h
      cases h

/-- On `InitMem`, `vkind52` is `vkind49`. -/
theorem vkind52_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind52 lc g v = vkind49 lc g v := by
  unfold vkind52
  cases vkind49 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind52b_none (by rw [hop]; rfl)]

/-- On an op off G52's group B, `vkind52` is `vkind49`. -/
theorem vkind52_eq49 {lc : LocCtx} {g : G2In} {v : Value} (h : op52b v.op = false) :
    vkind52 lc g v = vkind49 lc g v := by
  unfold vkind52
  cases vkind49 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind52b_none h]

/-- On a function with no arm64 op, G52's check is G33. -/
theorem checkG33_of_52L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG52L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG52L, hl] using h

/-- What `checkG52L` accepted of a function with an arm64 op: G49's facts with G52's value
check. -/
theorem checkG52L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG52L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind52 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG52L, hl, ↓reduceIte] at h
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

/-- What `checkG52` accepted: `refsLive`, and `checkG52L` on `liveCtx`. -/
theorem checkG52_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG52 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG52L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG52 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
