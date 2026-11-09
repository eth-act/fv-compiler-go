import GoFV.Gen.Check13
import GoFV.Proof.Gen.Spec12

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G13 accepted (`docs/plans/proofs3.md` §4)

`checkG13 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G13.lean`) uses (`checkG13_spec`): G12's (`Spec12.lean`) with G13's value check
(`vkind13_spec`, `VK13`: G12's values and `LoweredZero` with `zeroTail`'s stores), and what
`zeroCovers` decided (`zeroCovers_spec`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind13` accepted of a value that is not an entry value, and what it emits. -/
inductive VK13 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G12. -/
  | g12 {kd : VKind2} : VK12 lc g v kd → VK13 lc g v kd
  /-- `LoweredZero [n] p mem`: `p` in a register of class 64, the memory last, a memory with no
  home, `16 ≤ n`; the stores of `zeroTail` off `p`'s register, inside the `n` bytes and covering
  them. -/
  | zero {rp : Int} : v.op = .ARM64LoweredZero → v.args.size = 2 → memTy (lc.ty v.id) = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rp) → memArg lc v 1 = .ok () →
      16 ≤ v.auxInt.toInt → zeroCovers v.auxInt.toInt.toNat (zeroOffs v.auxInt.toInt.toNat) = true →
      VK13 lc g v (.progs ((zeroOffs v.auxInt.toInt.toNat).map (zeroPat rp)))

/-- What `zeroKind` accepted. -/
theorem zeroKind_spec {lc : LocCtx} {v : Value} {kd : VKind2} (h : zeroKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ v.args.size = 2 ∧ memTy (lc.ty v.id) = true ∧
      lc.home v.id = none ∧ ∃ rp, argObj lc v 0 = .ok (64, rp) ∧ memArg lc v 1 = .ok () ∧
      16 ≤ v.auxInt.toInt ∧ zeroCovers v.auxInt.toInt.toNat (zeroOffs v.auxInt.toInt.toNat) = true ∧
      kd = .progs ((zeroOffs v.auxInt.toInt.toNat).map (zeroPat rp)) := by
  unfold zeroKind at h
  obtain ⟨ht, h1⟩ := ex_guard h
  obtain ⟨hsh, h2⟩ := ex_guard h1
  obtain ⟨⟨c, rp⟩, ha, h3⟩ := ex_bind_eq_ok h2
  obtain ⟨⟨⟩, hm, h4⟩ := ex_bind_eq_ok h3
  obtain ⟨hc, h5⟩ := ex_guard h4
  obtain ⟨hcov, h6⟩ := ex_guard h5
  simp only [ex_pure, Except.ok.injEq] at h6
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨rfl, h16⟩ := hc
  exact ⟨ht, hsh.1.1, hsh.1.2, hsh.2, rp, ha, hm, h16, hcov, h6.symm⟩

/-- What `vkind13` accepted of a value that is not an entry value: no temporary, and `VK13`. -/
theorem vkind13_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind13 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK13 lc g v kd := by
  unfold vkind13 at h
  split at h
  · rename_i hop
    simp only [beq_iff_eq] at hop
    obtain ⟨ht, hsz, hmt, hh, rp, ha, hm, h16, hcov, rfl⟩ := zeroKind_spec h
    exact ⟨ht, .zero hop hsz hmt hh ha hm h16 hcov⟩
  · obtain ⟨ht, h12⟩ := vkind12_spec h hen
    exact ⟨ht, .g12 h12⟩

/-- What `zeroCovers` decided: every store lies inside the `n` bytes, and every byte is covered
by a store. -/
theorem zeroCovers_spec {n : Nat} {offs : List (Bool × Nat)} (h : zeroCovers n offs = true) :
    (∀ st ∈ offs, st.2 + zeroW st.1 ≤ n) ∧
      ∀ j, j < n → ∃ st ∈ offs, st.2 ≤ j ∧ j < st.2 + zeroW st.1 := by
  simp only [zeroCovers, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    List.any_eq_true] at h
  refine ⟨fun st hst => h.1 st hst, fun j hj => ?_⟩
  obtain ⟨st, hst, hc⟩ := h.2 j hj
  exact ⟨st, hst, hc⟩

/-- What `checkG13` accepted: G12's facts with G13's value check. -/
theorem checkG13_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG13 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind13 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG13 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
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
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb⟩
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
