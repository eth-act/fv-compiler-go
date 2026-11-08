import GoFV.Gen.Check21
import GoFV.Proof.Gen.Spec20

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G21 accepted (`docs/plans/proofs3.md` §4)

`checkG21 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G21.lean`) uses (`checkG21_spec`): G20's (`Spec20.lean`) with G21's value check
(`vkind21_spec`, `VK21`: G20's values and `MOVDreg`), and the upper-bit table at each `MOVDnop`
and `MOVDreg` (`movdOK`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind21` accepted of a value that is not an entry value, and what it emits. -/
inductive VK21 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G20 (not a `MOVDreg`). -/
  | g20 {kd : VKind2} : v.op ≠ .ARM64MOVDreg → VK20 lc g v kd → VK21 lc g v kd
  /-- `MOVDreg x` with `x` in the value's register (not `ZERO`): no code. -/
  | regSame {ca cd : Nat} {r : Int} : v.op = .ARM64MOVDreg → v.args.size = 1 →
      argObj lc v 0 = .ok (ca, r) → resObj lc v = .ok (cd, r) → r ≠ ARM64.REGZERO →
      (ca = 8 ∨ ca = 16 ∨ ca = 32) → (cd = 8 ∨ cd = 16 ∨ cd = 32 ∨ cd = 64) → VK21 lc g v .none
  /-- `MOVDreg x` with `x` in another register (not `ZERO`): `MOVD Rx, Rv`. -/
  | regMov {ca cd : Nat} {ra rd : Int} : v.op = .ARM64MOVDreg → v.args.size = 1 →
      argObj lc v 0 = .ok (ca, ra) → resObj lc v = .ok (cd, rd) → ra ≠ ARM64.REGZERO →
      (ca = 8 ∨ ca = 16 ∨ ca = 32) → (cd = 8 ∨ cd = 16 ∨ cd = 32 ∨ cd = 64) → ra ≠ rd →
      VK21 lc g v (.prog (.ofShape { as := .MOVD, from_ := regA ra, to := regA rd }))

/-- What `movRegKind` accepted. -/
theorem movRegKind_spec {lc : LocCtx} {v : Value} {kd : VKind2} (h : movRegKind lc v = .ok kd)
    (hop : v.op = .ARM64MOVDreg) {g : G2In} :
    (lc.temps[v.id]?).join = none ∧ VK21 lc g v kd := by
  unfold movRegKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, ra⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cd, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hz, h⟩ := ex_guard h
  obtain ⟨hca, h⟩ := ex_guard h
  obtain ⟨hcd, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht hsz
  simp only [bne_iff_ne, ne_eq] at hz
  simp only [Bool.or_eq_true, beq_iff_eq] at hca hcd
  have hca' : ca = 8 ∨ ca = 16 ∨ ca = 32 := by rcases hca with (h | h) | h <;> simp [h]
  have hcd' : cd = 8 ∨ cd = 16 ∨ cd = 32 ∨ cd = 64 := by
    rcases hcd with ((h | h) | h) | h <;> simp [h]
  by_cases hrr : ra = rd
  · subst hrr
    simp only [beq_self_eq_true, ↓reduceIte, ex_pure, Except.ok.injEq] at h
    subst h
    exact ⟨ht, .regSame hop hsz hao hro hz hca' hcd'⟩
  · simp only [beq_iff_eq, hrr, ↓reduceIte, ex_pure, Except.ok.injEq] at h
    subst h
    exact ⟨ht, .regMov hop hsz hao hro hz hca' hcd' hrr⟩

/-- What `vkind21` accepted of a value that is not an entry value: no temporary, and `VK21`. -/
theorem vkind21_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind21 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK21 lc g v kd := by
  unfold vkind21 at h
  by_cases hop : v.op = .ARM64MOVDreg
  · rw [if_pos (by simp [hop])] at h
    exact movRegKind_spec h hop
  · rw [if_neg (by simp [hop])] at h
    obtain ⟨ht, h20⟩ := vkind20_spec h hen
    exact ⟨ht, .g20 hop h20⟩

/-- What `checkG21` accepted: G20's facts with G21's value check. -/
theorem checkG21_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG21 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind21 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK lc = true := by
  unfold checkG21 at h
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
