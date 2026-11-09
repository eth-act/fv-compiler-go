import GoFV.Gen.Check40
import GoFV.Proof.Gen.Spec38

/-!
# What `checkG40` accepted (`GoFV/Gen/Check40.lean`)

`vkind40` is `vkind38` but on `InitMem` (`vkind40_spec`: on a value that is not an entry value,
G38's `VK38`), where, in a function whose values keep the memory (`memPure_spec`), it accepts an
`InitMem` without temporary, argument or home, of shape `mem` (`vkind40_initMem`). `checkG40L_spec`
is `checkG38_spec` with `vkind40`, and `checkG40_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `memKeep` accepted of a value. -/
theorem memKeep_spec {lc : LocCtx} {u : Value} (h : memKeep lc u = true) :
    u.op = .Phi ∨ memInert (lc.ty u.id) = true ∨
      (u.op = .InitMem ∧ (lc.temps[u.id]?).join = none ∧ lc.home u.id = none ∧
        memTy (lc.ty u.id) = true) ∨
      (u.op = .MakeResult ∧ (lc.temps[u.id]?).join = none ∧
        (lc.home u.id = none ∨ lc.home u.id = some (.results #[])) ∧
        resultsTy lc u.args (lc.ty u.id) = true ∧
        ∀ a ∈ u.args.toList, memTy (lc.ty a) = true → lc.home a = none) := by
  unfold memKeep at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem,
    Bool.not_eq_true'] at h
  rcases h with ((h | h) | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact .inr (.inr (.inl ⟨h1, h2, h3, h4⟩))
  · obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine .inr (.inr (.inr ⟨h1, h2, h3, h4, fun a ha hm => ?_⟩))
    rcases h5 a (Array.mem_toList_iff.1 ha) with h | h
    · rw [hm] at h; cases h
    · exact h

/-- Under `memPure`, every value of the function keeps the memory (`memKeep`). -/
theorem memPure_spec {lc : LocCtx} (h : memPure lc = true) {id : ID} {u : Value}
    (hu : lc.ctx.f.value? id = some u) : memKeep lc u = true := by
  have hlt : id < lc.ctx.f.valueTab.size := by
    unfold Func.value? at hu
    refine Nat.lt_of_not_le fun hge => ?_
    rw [Array.getElem?_eq_none hge] at hu
    cases hu
  unfold memPure at h
  have h1 := List.all_eq_true.1 h id (List.mem_range.2 hlt)
  rw [hu] at h1
  exact h1

/-- What `initMemKind` accepted: no temporary, no argument, no home, shape `mem`, no code. -/
theorem initMemKind_spec {lc : LocCtx} {v : Value} {kd : VKind2} (h : initMemKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ v.args.size = 0 ∧ lc.home v.id = none ∧
      memTy (lc.ty v.id) = true ∧ kd = .none := by
  unfold initMemKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hs, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  exact ⟨ht, hs.1.1, hs.1.2, hs.2, h.symm⟩

/-- What `vkind40` accepted of a value that is not an entry value: G38's. -/
theorem vkind40_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind40 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK38 lc g v kd := by
  have hne : (v.op == .InitMem) = false := by
    cases hop : v.op <;> simp_all [entryOp24, entryOp3, entryOp]
  unfold vkind40 at h
  simp only [hne, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
  exact vkind38_spec h hen

/-- What `vkind40` accepted of an `InitMem` in a function whose values keep the memory: no
temporary, no argument, no home, shape `mem`, and no code. -/
theorem vkind40_initMem {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind40 lc g v = .ok kd) (hop : v.op = .InitMem) (hp : memPure lc = true) :
    (lc.temps[v.id]?).join = none ∧ v.args.size = 0 ∧ lc.home v.id = none ∧
      memTy (lc.ty v.id) = true ∧ kd = .none := by
  unfold vkind40 at h
  simp only [hop, hp, beq_self_eq_true, Bool.and_self, ↓reduceIte] at h
  exact initMemKind_spec h

/-- On a function with no arm64 op, G40's check is G33. -/
theorem checkG33_of_40L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG40L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG40L, hl] using h

/-- What `checkG40L` accepted of a function with an arm64 op: G38's facts with G40's value
check. -/
theorem checkG40L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG40L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind40 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG40L, hl, ↓reduceIte] at h
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

/-- What `checkG40` accepted: `refsLive`, and G40's check on the context without the removed
homes. -/
theorem checkG40_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG40 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG40L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG40 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
