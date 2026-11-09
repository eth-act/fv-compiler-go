import GoFV.Gen.Check36
import GoFV.Proof.Gen.Spec35

/-!
# What the genssa validator's slice G36 accepted (`docs/plans/proofs3.md` §4)

`checkG36 lc ps bstart g = .ok (tab, kt)` unfolded: on a function with an arm64 op, G35's facts
(`checkG36_spec`) with G36's value check (`vkind36_spec`, `VK36`: G33's values, the register
shifts, the shifted adds and subtracts, and `TST`); on one without, G33's (`checkG33_of_36`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind36` accepted of a value that is not an entry value, and what it emits. -/
inductive VK36 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G33 (none of G36's ops). -/
  | g33 {kd : VKind2} : sh36? v.op = none → shOp36? v.op = none → v.op ≠ .ARM64TST →
      VK33 lc g v kd → VK36 lc g v kd
  /-- `SLL`, `SRL`, `SRA x y`: `op Rm, Rn, Rd`, `y` of at least 8 bits, `x` of at least the
  result's class (`LSL`) or of 64 bits. -/
  | sh {as : As} {ca cb c : Nat} {rn rm rd : Int} :
      sh36? v.op = some as → v.args.size = 2 → argObj lc v 0 = .ok (ca, rn) →
      argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) → 8 ≤ c → 8 ≤ cb →
      (as = .LSL → c ≤ ca) → (as ≠ .LSL → ca = 64) →
      VK36 lc g v (.prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }))
  /-- A shifted add or subtract `x ± (y SHIFT k)`: `op Rm SHIFT k, Rn, Rd`, `x` of at least the
  result's class, `y` too (`LSL`) or of 64 bits. -/
  | shOp {as : As} {typ : Nat} {ca cb c : Nat} {rn rm rd : Int} :
      shOp36? v.op = some (as, typ) → v.args.size = 2 → 0 ≤ v.auxInt.toInt →
      v.auxInt.toInt < 64 → argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → c ≤ ca → (typ = 0 → c ≤ cb) → (typ ≠ 0 → cb = 64) →
      VK36 lc g v (.prog (.ofShape
        { as, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }))
  /-- `TST x y`: `TST Rm, Rn`, of two 64-bit arguments. -/
  | tst {rn rm : Int} :
      v.op = .ARM64TST → v.args.size = 2 → (lc.ty v.id).isFlags = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rn) → argObj lc v 1 = .ok (64, rm) →
      VK36 lc g v (.prog (.ofShape { as := .TST, from_ := regA rm, reg := rn }))

/-- What `sh36Kind` accepted: no temporary, and `VK36`'s `sh`. -/
theorem sh36Kind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {kd : VKind2}
    (hop : sh36? v.op = some as) (h : sh36Kind lc v as = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK36 lc g v kd := by
  unfold sh36Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨h8, hcb⟩, hw⟩ := hw
  refine ⟨ht, .sh hop hsz hao hbo hro h8 hcb (fun hl => ?_) (fun hl => ?_)⟩
  · simpa [hl] using hw
  · simpa [hl] using hw

/-- What `shOp36Kind` accepted: no temporary, and `VK36`'s `shOp`. -/
theorem shOp36Kind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {typ : Nat}
    {kd : VKind2} (hop : shOp36? v.op = some (as, typ)) (h : shOp36Kind lc v as typ = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK36 lc g v kd := by
  unfold shOp36Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨hk, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk hw
  obtain ⟨⟨h8, hca⟩, hw⟩ := hw
  refine ⟨ht, .shOp hop hsz hk.1 hk.2 hao hbo hro h8 hca (fun hl => ?_) (fun hl => ?_)⟩
  · simpa [hl] using hw
  · simpa [hl] using hw

/-- What `tst36Kind` accepted: no temporary, and `VK36`'s `tst`. -/
theorem tst36Kind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64TST) (h : tst36Kind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK36 lc g v kd := by
  unfold tst36Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsh, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh hw
  obtain ⟨⟨hsz, hfl⟩, hhn⟩ := hsh
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨ht, .tst hop hsz hfl hhn hao hbo⟩

/-- What `vkind36` accepted of a value that is not an entry value: no temporary, and `VK36`. -/
theorem vkind36_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind36 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK36 lc g v kd := by
  unfold vkind36 at h
  cases h1 : sh36? v.op with
  | some as => rw [h1] at h; exact sh36Kind_spec h1 h
  | none =>
    cases h2 : shOp36? v.op with
    | some p =>
      obtain ⟨as, typ⟩ := p
      rw [h1, h2] at h
      exact shOp36Kind_spec h2 h
    | none =>
      rw [h1, h2] at h
      by_cases ht : v.op = .ARM64TST
      · simp only [ht, beq_self_eq_true, ↓reduceIte] at h
        exact tst36Kind_spec ht h
      have ht' : (v.op == .ARM64TST) = false := by simpa using ht
      simp only [ht', Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨htm, h33⟩ := vkind33_spec h hen
      exact ⟨htm, .g33 h1 h2 ht h33⟩

/-- On a function with no arm64 op, G36 is G33. -/
theorem checkG33_of_36 {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG36 lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG36, hl] using h

/-- What `checkG36` accepted of a function with an arm64 op: G35's facts with G36's value check. -/
theorem checkG36_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG36 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind36 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG36, hl, ↓reduceIte] at h
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

end GoFV.Gen.Check
