import GoFV.Gen.Check51
import GoFV.Proof.Gen.Spec51a
import GoFV.Proof.Gen.Spec51b
import GoFV.Proof.Gen.Spec51c

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG51` accepted (`GoFV/Gen/Check51.lean`)

`VK51`: G50's kinds (`VK50`, through `vkind50`), the flag and conditional ops (`VK51a`,
`Spec51a.lean`), the ALU ops (`VK51b`, `Spec51b.lean`) and the boolean operands (`VK51c`,
`Spec51c.lean`). On `InitMem`, `vkind51` is `vkind50`
(`vkind51_initMem`). `checkG51L_spec` is `checkG50L_spec` with `vkind51`, and `checkG51_spec`
splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind51` accepted of a value that is not an entry value, and what it emits. -/
inductive VK51 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G50. -/
  | g50 {kd : VKind2} : VK50 lc g v kd → VK51 lc g v kd
  /-- A flag or conditional op of G51 (`Check51a.lean`). -/
  | a {kd : VKind2} : VK51a lc v kd → VK51 lc g v kd
  /-- An ALU op of G51 (`Check51b.lean`). -/
  | b {kd : VKind2} : VK51b lc v kd → VK51 lc g v kd
  /-- A boolean operand of an add, subtract or shifted op (`Check51c.lean`). -/
  | c {kd : VKind2} : VK51c lc v kd → VK51 lc g v kd

/-- What `vkind51` accepted of a value that is not an entry value: no temporary, and `VK51`. -/
theorem vkind51_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind51 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK51 lc g v kd := by
  unfold vkind51 at h
  cases h50 : vkind50 lc g v with
  | ok kd' =>
    rw [h50] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind50_spec h50 hen
    exact ⟨ht, .g50 hVK⟩
  | error e =>
    rw [h50] at h
    simp only at h
    cases ha : vkind51a lc v with
    | some r =>
      rw [ha] at h
      subst h
      obtain ⟨ht, hVK⟩ := vkind51a_spec ha
      exact ⟨ht, .a hVK⟩
    | none =>
      rw [ha] at h
      cases hb : vkind51b lc v with
      | some r =>
        rw [hb] at h
        subst h
        obtain ⟨ht, hVK⟩ := vkind51b_spec hb
        exact ⟨ht, .b hVK⟩
      | none =>
        rw [hb] at h
        cases hc : vkind51c lc v with
        | some r =>
          rw [hc] at h
          subst h
          obtain ⟨ht, hVK⟩ := vkind51c_spec hc
          exact ⟨ht, .c hVK⟩
        | none =>
          rw [hc] at h
          cases h

/-- On `InitMem`, `vkind51` is `vkind50`. -/
theorem vkind51_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind51 lc g v = vkind50 lc g v := by
  unfold vkind51
  cases vkind50 lc g v with
  | ok _ => rfl
  | error e =>
    simp only
    rw [vkind51a_none (by rw [hop]; rfl), vkind51b_none (by rw [hop]; rfl),
      vkind51c_none (by rw [hop]; rfl)]

/-- On a function with no arm64 op, G51's check is G33. -/
theorem checkG33_of_51L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG51L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG51L, hl] using h

/-- What `checkG51L` accepted of a function with an arm64 op: G50's facts with G51's value
check. -/
theorem checkG51L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG51L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind51 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG51L, hl, ↓reduceIte] at h
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

/-- What `checkG51` accepted: `refsLive`, and G51's check on the context without the removed
homes. -/
theorem checkG51_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG51 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG51L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG51 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
