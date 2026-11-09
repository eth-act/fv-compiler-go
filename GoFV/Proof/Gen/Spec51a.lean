import GoFV.Gen.Check51a
import GoFV.Proof.Gen.Spec50

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `vkind51a` accepted (`GoFV/Gen/Check51a.lean`)

`VK51a`: the values of G51's group A and what each emits: `CSNEG` (`csneg`), `TSTW` and `CMNW`
(`cmpW`), `CMN` (`cmn`) and `CMPshiftRA` (`cmpShRA`) (`vkind51a_spec`). `vkind51a` is `none` off
`op51a` (`vkind51a_none`), and every `VK51a` value's op is one of `op51a` (`vk51a_op`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind51a` accepted, and what it emits. -/
inductive VK51a (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- `CSNEG [cc] x y f`: `CSNEG cond, Rx, Ry, Rd`. -/
  | csneg {f : ID} {o : Op} {cc rn rm rd : Int} {ca cb c : Nat} :
      v.op = .ARM64CSNEG → v.args.size = 3 → v.args[2]? = some f → (lc.ty f).isFlags = true →
      lc.home f = none → ccOp? v.auxInt = some o → (Cond.ofOp o).isSome = true →
      ARM64.condBits o = some cc → argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → c ≤ ca → c ≤ cb →
      VK51a lc v (.prog ⟨csnegOK cc rn rm rd, "CSNEG"⟩)
  /-- `TSTW`, `CMNW x y`: `TSTW`/`CMNW Rm, Rn`, `x` and `y` of classes at least 32. -/
  | cmpW {as : As} {ca cb : Nat} {rn rm : Int} :
      (v.op = .ARM64TSTW ∧ as = .TSTW ∨ v.op = .ARM64CMNW ∧ as = .CMNW) → v.args.size = 2 →
      (lc.ty v.id).isFlags = true → lc.home v.id = none → argObj lc v 0 = .ok (ca, rn) →
      argObj lc v 1 = .ok (cb, rm) → 32 ≤ ca → 32 ≤ cb →
      VK51a lc v (.prog (.ofShape { as, from_ := regA rm, reg := rn }))
  /-- `CMN x y`: `CMN Rm, Rn`, `x` and `y` of 64 bits. -/
  | cmn {rn rm : Int} :
      v.op = .ARM64CMN → v.args.size = 2 → (lc.ty v.id).isFlags = true → lc.home v.id = none →
      argObj lc v 0 = .ok (64, rn) → argObj lc v 1 = .ok (64, rm) →
      VK51a lc v (.prog (.ofShape { as := .CMN, from_ := regA rm, reg := rn }))
  /-- `CMPshiftRA [k] x y`: `CMP Rm->k, Rn`, `x` and `y` of 64 bits. -/
  | cmpShRA {rn rm : Int} :
      v.op = .ARM64CMPshiftRA → v.args.size = 2 → (lc.ty v.id).isFlags = true →
      lc.home v.id = none → 0 ≤ v.auxInt.toInt → v.auxInt.toInt < 64 →
      argObj lc v 0 = .ok (64, rn) → argObj lc v 1 = .ok (64, rm) →
      VK51a lc v (.prog (.ofShape
        { as := .CMP, from_ := shiftA 2 rm v.auxInt.toInt.toNat, reg := rn }))

/-- What `csnegKind` accepted: no temporary, and `VK51a`'s `csneg`. -/
theorem csnegKind_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64CSNEG) (h : csnegKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK51a lc v kd := by
  unfold csnegKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  obtain ⟨hsz, h⟩ := ex_guard h
  simp only [beq_iff_eq] at hsz
  split at h
  next f hf =>
    obtain ⟨hfl, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hfl
    split at h
    next o ho =>
      obtain ⟨hco, h⟩ := ex_guard h
      split at h
      next cc hcc =>
        obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
        obtain ⟨hw, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        simp only [ex_pure, Except.ok.injEq] at h
        subst h
        exact .csneg hop hsz hf hfl.1 hfl.2 ho hco hcc hao hbo hro hw.1.1 hw.1.2 hw.2
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next => simp [ex_throw] at h

/-- What `cmpRegKind51a` accepted for `TSTW`, `CMNW` (32 bits) and `CMN` (64 bits): no temporary,
and `VK51a`'s `cmpW` or `cmn`. -/
theorem cmpRegKind51a_spec {lc : LocCtx} {v : Value} {as : As} {w : Nat} {kd : VKind2}
    (hop : v.op = .ARM64TSTW ∧ as = .TSTW ∧ w = 32 ∨ v.op = .ARM64CMNW ∧ as = .CMNW ∧ w = 32 ∨
      v.op = .ARM64CMN ∧ as = .CMN ∧ w = 64)
    (h : cmpRegKind51a lc v as w = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK51a lc v kd := by
  unfold cmpRegKind51a at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  obtain ⟨hsh, h⟩ := ex_guard h
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  rcases hop with ⟨hop, rfl, rfl⟩ | ⟨hop, rfl, rfl⟩ | ⟨hop, rfl, rfl⟩
  · have hw' : 32 ≤ ca ∧ 32 ≤ cb := by simpa using hw
    exact .cmpW (.inl ⟨hop, rfl⟩) hsh.1.1 hsh.1.2 hsh.2 hao hbo hw'.1 hw'.2
  · have hw' : 32 ≤ ca ∧ 32 ≤ cb := by simpa using hw
    exact .cmpW (.inr ⟨hop, rfl⟩) hsh.1.1 hsh.1.2 hsh.2 hao hbo hw'.1 hw'.2
  · simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact .cmn hop hsh.1.1 hsh.1.2 hsh.2 hao hbo

/-- What `cmpShRAKind` accepted: no temporary, and `VK51a`'s `cmpShRA`. -/
theorem cmpShRAKind_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64CMPshiftRA) (h : cmpShRAKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK51a lc v kd := by
  unfold cmpShRAKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsh, h⟩ := ex_guard h
  obtain ⟨hk, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨hcab, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hcab hsh
  obtain ⟨rfl, rfl⟩ := hcab
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  exact ⟨ht, .cmpShRA hop hsh.1.1 hsh.1.2 hsh.2 hk.1 hk.2 hao hbo⟩

/-- What `vkind51a` accepted: no temporary, and `VK51a`. -/
theorem vkind51a_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (h : vkind51a lc v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK51a lc v kd := by
  unfold vkind51a at h
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    exact csnegKind_spec (by simpa using hc) h
  next =>
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    exact cmpRegKind51a_spec (.inl ⟨by simpa using hc, rfl, rfl⟩) h
  next =>
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    exact cmpRegKind51a_spec (.inr (.inl ⟨by simpa using hc, rfl, rfl⟩)) h
  next =>
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    exact cmpRegKind51a_spec (.inr (.inr ⟨by simpa using hc, rfl, rfl⟩)) h
  next =>
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    exact cmpShRAKind_spec (by simpa using hc) h
  next => cases h

/-- Off the ops of G51's group A, `vkind51a` is `none`. -/
theorem vkind51a_none {lc : LocCtx} {v : Value} (h : op51a v.op = false) : vkind51a lc v = none := by
  simp only [op51a, Bool.or_eq_false_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [vkind51a, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]

/-- A value `VK51a` accepted has an op of G51's group A. -/
theorem vk51a_op {lc : LocCtx} {v : Value} {kd : VKind2} (h : VK51a lc v kd) :
    op51a v.op = true := by
  cases h with
  | csneg hop => rw [hop]; rfl
  | cmpW hop => rcases hop with ⟨hop, -⟩ | ⟨hop, -⟩ <;> rw [hop] <;> rfl
  | cmn hop => rw [hop]; rfl
  | cmpShRA hop => rw [hop]; rfl

end GoFV.Gen.Check
