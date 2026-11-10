import GoFV.Gen.Check61
import GoFV.Proof.Gen.Spec60
import GoFV.Proof.Gen.Spec61a

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG61` accepted (`GoFV/Gen/Check61.lean`)

`VK61`: G60's kinds (`VK60`), or G61's group A (`VK61a`: the atomics and their components). On
`InitMem`, `vkind61` is `vkind60` (`vkind61_initMem`). `checkG61L_spec` is `checkG60L_spec` with
`vkind61` and `atomOK`, and `checkG61_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind61` accepted of a value that is not an entry value. -/
inductive VK61 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G60. -/
  | g60 {kd : VKind2} : VK60 lc g v kd → VK61 lc g v kd
  /-- An atomic of group A, or one of its components. -/
  | a {kd : VKind2} : VK61a lc v kd → VK61 lc g v kd

/-- What `vkind61` accepted of a value that is not an entry value. -/
theorem vkind61_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind61 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK61 lc g v kd := by
  unfold vkind61 at h
  cases h60 : vkind60 lc g v with
  | ok kd' =>
    rw [h60] at h
    cases h
    exact .g60 (vkind60_spec h60 hen)
  | error e =>
    rw [h60] at h
    simp only at h
    split at h
    · rename_i r ha
      cases h
      exact .a (vkind61a_spec ha)
    · cases h

/-- On `InitMem`, `vkind61` is `vkind60`. -/
theorem vkind61_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind61 lc g v = vkind60 lc g v := by
  have hn : vkind61a lc v = none := vkind61a_none (by simp [op61a, atom61?, hop])
  unfold vkind61
  cases vkind60 lc g v <;> simp [hn]

/-- On a function with no arm64 op, G61's check is G33. -/
theorem checkG33_of_61L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG61L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG61L, hl] using h

/-- What `checkG61L` accepted of a function with an arm64 op: G60's facts with G61's value check,
and `atomOK`. -/
theorem checkG61L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG61L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind61 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true ∧
      spHomes48 lc = true ∧ atomOK lc ps tab = true := by
  simp only [checkG61L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hlp, h⟩ := ex_guard h
  obtain ⟨hat, h⟩ := ex_guard h
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
      hsph, hat⟩
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

/-- What `checkG61` accepted: `refsLive`, and `checkG61L` on `liveCtx`. -/
theorem checkG61_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG61 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG61L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG61 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
