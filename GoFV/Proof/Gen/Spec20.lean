import GoFV.Gen.Check20
import GoFV.Proof.Gen.Spec19

/-!
# What the genssa validator's slice G20 accepted (`docs/plans/proofs3.md` §4)

`checkG20 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G20.lean`) uses (`checkG20_spec`): G19's (`Spec19.lean`) with G20's value check
(`vkind20_spec`, `VK20`: G19's values and `MOVDnop`), and the upper-bit table at each `MOVDnop`
and `MOVDreg` (`movdOK_spec`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind20` accepted of a value that is not an entry value, and what it emits. -/
inductive VK20 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G19 (not a `MOVDnop`). -/
  | g19 {kd : VKind2} : v.op ≠ .ARM64MOVDnop → VK19 lc g v kd → VK20 lc g v kd
  /-- `MOVDnop x`: homed in `x`'s register `r` (one G1 may write) at an integer class, `x` of
  class 8, 16 or 32; no code. -/
  | nop {x r : Nat} : v.op = .ARM64MOVDnop → v.args.size = 1 → v.args[0]? = some x →
      regHome? lc v.id = some r → destOK r = true → r ≠ zeroReg → regHome? lc x = some r →
      (cls (lc.ty v.id) = some 8 ∨ cls (lc.ty v.id) = some 16 ∨ cls (lc.ty v.id) = some 32 ∨
        cls (lc.ty v.id) = some 64) →
      (cls (lc.ty x) = some 8 ∨ cls (lc.ty x) = some 16 ∨ cls (lc.ty x) = some 32) →
      VK20 lc g v .none

/-- What `nopKind` accepted. -/
theorem nopKind_spec {lc : LocCtx} {v : Value} {kd : VKind2} (h : nopKind lc v = .ok kd)
    (hop : v.op = .ARM64MOVDnop) {g : G2In} :
    (lc.temps[v.id]?).join = none ∧ VK20 lc g v kd := by
  unfold nopKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  cases hx : v.args[0]? with
  | none => rw [hx] at h; simp [ex_throw] at h
  | some x =>
    rw [hx] at h
    obtain ⟨hsz, h⟩ := ex_guard h
    cases hr : regHome? lc v.id with
    | none => rw [hr] at h; simp [ex_throw] at h
    | some r =>
      rw [hr] at h
      obtain ⟨hd, h⟩ := ex_guard h
      obtain ⟨hcv, h⟩ := ex_guard h
      obtain ⟨hcx, h⟩ := ex_guard h
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      simp only [beq_iff_eq] at ht hsz
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hd
      simp only [Bool.or_eq_true, beq_iff_eq] at hcv hcx
      refine ⟨ht, .nop hop hsz hx hr hd.1.1 hd.1.2 hd.2 ?_ ?_⟩
      · rcases hcv with ((h | h) | h) | h <;> simp [h]
      · rcases hcx with (h | h) | h <;> simp [h]

/-- What `vkind20` accepted of a value that is not an entry value: no temporary, and `VK20`. -/
theorem vkind20_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind20 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK20 lc g v kd := by
  unfold vkind20 at h
  by_cases hop : v.op = .ARM64MOVDnop
  · rw [if_pos (by simp [hop])] at h
    exact nopKind_spec h hop
  · rw [if_neg (by simp [hop])] at h
    obtain ⟨ht, h19⟩ := vkind19_spec h hen
    exact ⟨ht, .g19 hop h19⟩

/-- What `movdOK` checked: before a `MOVDnop x` or `MOVDreg x` at index `i` of block `bid`, the
upper-bit table names `x`'s register at `x`'s class with the signedness `signOf` gives `x`. -/
theorem movdOK_spec {lc : LocCtx} (h : movdOK lc = true) {bid : ID}
    (hbid : bid ∈ lc.ctx.f.blocks.toList) {b : Block} (hb : lc.ctx.f.block? bid = some b)
    {i : Nat} {id : ID} (hi : b.values[i]? = some id) {v : Value}
    (hv : lc.ctx.f.value? id = some v) (hop : v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg)
    {x : ID} (hx : v.args[0]? = some x) :
    ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
      uAt lc b i = some (r, c, lc.signOf lc.ctx.f.valueTab.size x) := by
  unfold movdOK at h
  have := List.all_eq_true.1 h _ hbid
  simp only [hb] at this
  have hi' : i < b.values.size := (Array.getElem?_eq_some_iff.1 hi).1
  have := List.all_eq_true.1 this i (List.mem_range.2 hi')
  have hne : (v.op != .ARM64MOVDnop && v.op != .ARM64MOVDreg) = false := by
    rcases hop with h | h <;> rw [h] <;> rfl
  simp only [hi, Option.bind_some, hv, hne, Bool.false_or, hx] at this
  revert this
  cases hr : regHome? lc x with
  | none => simp
  | some r =>
    cases hc : cls (lc.ty x) with
    | none => simp
    | some c =>
      intro hu
      exact ⟨r, c, rfl, rfl, by simpa using hu⟩

/-- What `checkG20` accepted: G19's facts with G20's value check, and `movdOK`. -/
theorem checkG20_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG20 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind20 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK lc = true := by
  unfold checkG20 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hnop, h⟩ := ex_guard h
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
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hnop⟩
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
