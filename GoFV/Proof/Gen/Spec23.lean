import GoFV.Gen.Check23
import GoFV.Proof.Gen.Spec22

/-!
# What the genssa validator's slice G23 accepted (`docs/plans/proofs3.md` §4)

`checkG23 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G23.lean`) uses (`checkG23_spec`): G22's (`Spec22.lean`) with G23's value check
(`vkind23_spec`, `VK23`: G22's values, and the comparison pseudo-ops as `CSET`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind23` accepted of a value that is not an entry value, and what it emits. -/
inductive VK23 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G22 (no comparison pseudo-op). -/
  | g22 {kd : VKind2} : (Cond.ofOp v.op).isSome = false → VK22 lc g v kd → VK23 lc g v kd
  /-- A comparison pseudo-op: `CSET cond, Rd`, its flags argument in the flags register, a
  boolean result. -/
  | cset {cc : Int} {a : ID} {rd : Int} :
      (Cond.ofOp v.op).isSome = true → ARM64.condBits v.op = some cc → v.args.size = 1 →
      v.args[0]? = some a → (lc.ty a).isFlags = true → lc.home a = none →
      resObj lc v = .ok (1, rd) →
      VK23 lc g v (.prog ⟨plain .CSET (· == specA cc) (· == regA rd), "CSET"⟩)

/-- What `csetKind` accepted: no temporary, and `VK23`'s `cset`. -/
theorem csetKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hc : (Cond.ofOp v.op).isSome = true) (h : csetKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK23 lc g v kd := by
  unfold csetKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  split at h
  next cc hcc =>
    obtain ⟨hsz, h⟩ := ex_guard h
    simp only [beq_iff_eq] at hsz
    split at h
    next a ha =>
      obtain ⟨hfl, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq] at hfl
      obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
      obtain ⟨hc1, h⟩ := ex_guard h
      simp only [beq_iff_eq] at hc1
      subst hc1
      simp only [ex_pure, Except.ok.injEq, beq_self_eq_true, ↓reduceIte] at h
      subst h
      exact VK23.cset hc hcc hsz ha hfl.1 hfl.2 hro
    next => simp [ex_throw] at h
  next => simp [ex_throw] at h

/-- What `vkind23` accepted of a value that is not an entry value: no temporary, and `VK23`. -/
theorem vkind23_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind23 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK23 lc g v kd := by
  unfold vkind23 at h
  cases hc : (Cond.ofOp v.op).isSome with
  | true =>
    simp only [hc, ↓reduceIte] at h
    exact csetKind_spec hc h
  | false =>
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨ht, h22⟩ := vkind22_spec h hen
    exact ⟨ht, .g22 hc h22⟩

/-- What `checkG23` accepted: G22's facts with G23's value check. -/
theorem checkG23_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG23 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind23 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK lc = true := by
  unfold checkG23 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
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
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd⟩
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

end GoFV.Gen.Check
