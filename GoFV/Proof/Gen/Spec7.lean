import GoFV.Gen.Check7
import GoFV.Proof.Gen.Spec6

/-!
# What the genssa validator's slice G7 accepted (`docs/plans/proofs3.md` §4)

`checkG7 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G7.lean`) uses (`checkG7_spec`): G6's (`Spec6.lean`) with G7's value check
(`vkind7_spec`, `VK7`: G6's values and the nil checks).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind7` accepted of a value that is not an entry value, and what it emits. -/
inductive VK7 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G6. -/
  | g6 {kd : VKind2} : v.op ≠ .ARM64LoweredNilCheck → VK6 lc g v kd → VK7 lc g v kd
  /-- `LoweredNilCheck p mem` with no home and a dropped shape, `p` in the 64-bit register `Rp`:
  `MOVB (Rp), R27`. -/
  | nil {rp : Int} : v.op = .ARM64LoweredNilCheck → v.args.size = 2 → lc.home v.id = none →
      dropTy (lc.ty v.id) = true → argObj lc v 0 = .ok (64, rp) → memArg lc v 1 = .ok () →
      VK7 lc g v (.prog (.ofShape (nilShape rp)))

/-- What `vkind7` accepted of a value that is not an entry value: no temporary, and `VK7`. -/
theorem vkind7_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : vkind7 lc g v = .ok kd)
    (hen : entryOp3 v.op = false) : (lc.temps[v.id]?).join = none ∧ VK7 lc g v kd := by
  unfold vkind7 at h
  by_cases hop : v.op = .ARM64LoweredNilCheck
  · simp only [hop, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    by_cases ht : (lc.temps[v.id]?).join = none
    · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hs, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨⟨hsz, hhn⟩, hc⟩ := hs
      obtain ⟨⟨c, rp⟩, ha, h⟩ := ex_bind_eq_ok h
      obtain ⟨hc64, h⟩ := ex_guard h
      simp only [beq_iff_eq] at hc64
      subst hc64
      obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      exact ⟨ht, VK7.nil hop hsz hhn hc ha hma⟩
    · simp [ht, ex_throw, ex_bind_error] at h
  · simp only [bne_iff_ne, ne_eq, hop, not_false_eq_true, ↓reduceIte] at h
    obtain ⟨ht, h6⟩ := vkind6_spec h hen
    exact ⟨ht, VK7.g6 hop h6⟩

/-- What `checkG7` accepted: G6's facts with G7's value check. -/
theorem checkG7_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG7 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind7 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK4 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG7 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  cases hf : List.find? (fun x => !homeOK4 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb⟩
    by_cases hi : i < lc.homes.size
    · have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
      simpa using this
    · have hh : lc.home i = none := by
        simp only [LocCtx.home]
        rw [getElem?_neg lc.homes i hi]
        rfl
      unfold homeOK4 homeOK3 homeOK2 homeOK
      rw [hh]

end GoFV.Gen.Check
