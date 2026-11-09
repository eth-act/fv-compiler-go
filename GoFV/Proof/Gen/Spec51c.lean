import GoFV.Gen.Check51c
import GoFV.Proof.Gen.Spec50

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `vkind51c` accepted (`GoFV/Gen/Check51c.lean`)

`VK51c`: G1's adds and subtracts (`alu`, `aluK`), `ADDshiftLL` (`addSh`) and the shifted adds,
subtracts and logic ops (`sh`) with a boolean argument, each with its widths spelled out
(`wid51c_spec`, `shWid51c_spec`). `vkind51c_spec` reads them off an accepted value,
`vkind51c_none` is `vkind51c` off its ops and `vk51c_op` puts an accepted value on them.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind51c` accepted, and what it emits. -/
inductive VK51c (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- `ADD`, `SUB x y`: `OP Rm, Rn, Rd`, a result of at least 8 bits, each argument at least as
  wide or a boolean, one of them a boolean. -/
  | alu {as : As} {ca cb c : Nat} {rn rm rd : Int} :
      (v.op = .ARM64ADD ∧ as = .ADD ∨ v.op = .ARM64SUB ∧ as = .SUB) → v.args.size = 2 →
      argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) →
      8 ≤ c → (c ≤ ca ∨ ca = 1) → (c ≤ cb ∨ cb = 1) → (ca = 1 ∨ cb = 1) →
      VK51c lc v (.prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }))
  /-- `ADDconst`, `SUBconst [k] x`: `OP $k, Rn, Rd`, a result of at least 8 bits, `x` a boolean. -/
  | aluK {as : As} {c : Nat} {rn rd : Int} :
      (v.op = .ARM64ADDconst ∧ as = .ADD ∨ v.op = .ARM64SUBconst ∧ as = .SUB) →
      v.args.size = 1 → argObj lc v 0 = .ok (1, rn) → resObj lc v = .ok (c, rd) → 8 ≤ c →
      VK51c lc v (.prog (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }))
  /-- `ADDshiftLL [k] x y`: `ADD Rm<<k, Rn, Rd`, `0 ≤ k < 64`, `alu`'s widths. -/
  | addSh {ca cb c : Nat} {rn rm rd : Int} :
      v.op = .ARM64ADDshiftLL → v.args.size = 2 → 0 ≤ v.auxInt.toInt → v.auxInt.toInt < 64 →
      argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) →
      8 ≤ c → (c ≤ ca ∨ ca = 1) → (c ≤ cb ∨ cb = 1) → (ca = 1 ∨ cb = 1) →
      VK51c lc v (.prog (.ofShape
        { as := .ADD, from_ := shiftLLA rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }))
  /-- A shifted logic op (`logSh?`) or shifted add or subtract (`shOp36?`) `x op (y SHIFT k)`:
  `op Rm SHIFT k, Rn, Rd`, `0 ≤ k < 64`, `x` at least as wide as the result or a boolean, `y`
  too for a left shift, else of 64 bits or a boolean, one of them a boolean. -/
  | sh {as : As} {typ ca cb c : Nat} {rn rm rd : Int} :
      (logSh? v.op = some (as, typ) ∨ shOp36? v.op = some (as, typ)) → v.args.size = 2 →
      0 ≤ v.auxInt.toInt → v.auxInt.toInt < 64 →
      argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) →
      8 ≤ c → (c ≤ ca ∨ ca = 1) → (typ = 0 → c ≤ cb ∨ cb = 1) → (typ ≠ 0 → cb = 64 ∨ cb = 1) →
      (ca = 1 ∨ cb = 1) →
      VK51c lc v (.prog (.ofShape
        { as, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }))

theorem wid51c_spec {c ca : Nat} (h : wid51c c ca = true) : c ≤ ca ∨ ca = 1 := by
  simpa [wid51c] using h

theorem shWid51c_spec {typ c cb : Nat} (h : shWid51c typ c cb = true) :
    (typ = 0 → c ≤ cb ∨ cb = 1) ∧ (typ ≠ 0 → cb = 64 ∨ cb = 1) := by
  by_cases h0 : typ = 0
  · subst h0
    exact ⟨fun _ => wid51c_spec (by simpa [shWid51c] using h), fun h => absurd rfl h⟩
  · refine ⟨fun h => absurd h h0, fun _ => ?_⟩
    simpa [shWid51c, h0] using h

/-- What `arith51c` accepted: `VK51c.alu`. -/
theorem arith51c_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64ADD ∨ v.op = .ARM64SUB) (h : arith51c lc v = .ok kd) : VK51c lc v kd := by
  unfold arith51c at h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at hsz
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨⟨⟨h8, hca⟩, hcb⟩, h1⟩ := hw
  have has : v.op = .ARM64ADD ∧ (if v.op == .ARM64ADD then As.ADD else As.SUB) = .ADD ∨
      v.op = .ARM64SUB ∧ (if v.op == .ARM64ADD then As.ADD else As.SUB) = .SUB := by
    rcases hop with hop | hop <;> simp [hop]
  exact .alu has hsz hao hbo hro h8 (wid51c_spec hca) (wid51c_spec hcb) h1

/-- What `arithK51c` accepted: `VK51c.aluK`. -/
theorem arithK51c_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64ADDconst ∨ v.op = .ARM64SUBconst) (h : arithK51c lc v = .ok kd) :
    VK51c lc v kd := by
  unfold arithK51c at h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨h8, rfl⟩ := hw
  have has : v.op = .ARM64ADDconst ∧
        (if v.op == .ARM64ADDconst then As.ADD else As.SUB) = .ADD ∨
      v.op = .ARM64SUBconst ∧ (if v.op == .ARM64ADDconst then As.ADD else As.SUB) = .SUB := by
    rcases hop with hop | hop <;> simp [hop]
  exact .aluK has hsz hao hro h8

/-- What `addSh51c` accepted: `VK51c.addSh`. -/
theorem addSh51c_spec {lc : LocCtx} {v : Value} {kd : VKind2} (hop : v.op = .ARM64ADDshiftLL)
    (h : addSh51c lc v = .ok kd) : VK51c lc v kd := by
  unfold addSh51c at h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨hk, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨⟨⟨h8, hca⟩, hcb⟩, h1⟩ := hw
  exact .addSh hop hsz hk.1 hk.2 hao hbo hro h8 (wid51c_spec hca) (wid51c_spec hcb) h1

/-- What `sh51c` accepted: `VK51c.sh`. -/
theorem sh51c_spec {lc : LocCtx} {v : Value} {as : As} {typ : Nat} {what : String}
    {kd : VKind2} (hop : logSh? v.op = some (as, typ) ∨ shOp36? v.op = some (as, typ))
    (h : sh51c lc v as typ what = .ok kd) : VK51c lc v kd := by
  unfold sh51c at h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨hk, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨⟨⟨h8, hca⟩, hcb⟩, h1⟩ := hw
  obtain ⟨hll, hrr⟩ := shWid51c_spec hcb
  exact .sh hop hsz hk.1 hk.2 hao hbo hro h8 (wid51c_spec hca) hll hrr h1

/-- What `kind51c` accepted: no temporary, and `VK51c`. -/
theorem kind51c_spec {lc : LocCtx} {v : Value} {kd : VKind2} (h : kind51c lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK51c lc v kd := by
  unfold kind51c at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  cases hl : logSh? v.op with
  | some p =>
    obtain ⟨as, typ⟩ := p
    simp only [hl] at h
    exact sh51c_spec (.inl hl) h
  | none =>
  cases hs : shOp36? v.op with
  | some p =>
    obtain ⟨as, typ⟩ := p
    simp only [hl, hs] at h
    exact sh51c_spec (.inr hs) h
  | none =>
    simp only [hl, hs] at h
    by_cases h1 : v.op = .ARM64ADDshiftLL
    · simp only [h1, beq_self_eq_true, ↓reduceIte] at h
      exact addSh51c_spec h1 h
    · simp only [h1, beq_iff_eq, ↓reduceIte] at h
      by_cases h2 : v.op = .ARM64ADD ∨ v.op = .ARM64SUB
      · have h2' : (v.op == .ARM64ADD || v.op == .ARM64SUB) = true := by
          rcases h2 with h2 | h2 <;> simp [h2]
        simp only [h2', ↓reduceIte] at h
        exact arith51c_spec h2 h
      · have h2' : (v.op == .ARM64ADD || v.op == .ARM64SUB) = false := by
          simpa only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, not_or] using h2
        simp only [h2', Bool.false_eq_true, ↓reduceIte] at h
        by_cases h3 : v.op = .ARM64ADDconst ∨ v.op = .ARM64SUBconst
        · have h3' : (v.op == .ARM64ADDconst || v.op == .ARM64SUBconst) = true := by
            rcases h3 with h3 | h3 <;> simp [h3]
          simp only [h3', ↓reduceIte] at h
          exact arithK51c_spec h3 h
        · have h3' : (v.op == .ARM64ADDconst || v.op == .ARM64SUBconst) = false := by
            simpa only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, not_or] using h3
          simp only [h3', Bool.false_eq_true, ↓reduceIte] at h
          simp [ex_throw] at h

/-- What `vkind51c` accepted: no temporary, and `VK51c`. -/
theorem vkind51c_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (h : vkind51c lc v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK51c lc v kd := by
  unfold vkind51c at h
  split at h
  · exact kind51c_spec (Option.some.inj h)
  · cases h

/-- Off G51c's ops, `vkind51c` is `none`. -/
theorem vkind51c_none {lc : LocCtx} {v : Value} (h : op51c v.op = false) : vkind51c lc v = none := by
  simp [vkind51c, h]

/-- An accepted value of G51c is one of its ops. -/
theorem vk51c_op {lc : LocCtx} {v : Value} {kd : VKind2} (h : VK51c lc v kd) :
    op51c v.op = true := by
  cases h with
  | alu hop => rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [op51c, h]
  | aluK hop => rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [op51c, h]
  | addSh hop => simp [op51c, hop]
  | sh hop => rcases hop with h | h <;> simp [op51c, h]

end GoFV.Gen.Check
