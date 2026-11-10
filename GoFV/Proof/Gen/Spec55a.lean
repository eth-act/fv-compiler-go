import GoFV.Gen.Check55a
import GoFV.Proof.Gen.Spec46

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `vkind55a` accepted (`GoFV/Gen/Check55a.lean`)

`VK55a`: `VCNT`, `VUADDLV` and the `FRINT` rounds, and the one Prog each emits (`vkind55a_spec`).
`vkind55a` is `none` off `op55a` (`vkind55a_none`), and every `VK55a` value's op is one of `op55a`
(`vk55a_op`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind55a` accepted, and what it emits. -/
inductive VK55a (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- `VCNT x` (`cnt`): `VCNT Va.B8, Vd.B8`; `VUADDLV x`: `VUADDLV Va.B8, Vd`; `x` and the result
  64-bit values in V registers. -/
  | simd {cnt : Bool} {ra rd : Int} :
      v.op = cond cnt .ARM64VCNT .ARM64VUADDLV → v.args.size = 1 → fargObj lc v 0 = .ok (64, ra) →
      fresObj lc v = .ok (64, rd) →
      VK55a lc v (.prog (.ofShape (simdShape cnt ra rd)))
  /-- `FRINTN`/`FRINTP`/`FRINTM`/`FRINTZ`/`FRINTA`: `op Fa, Fd`. -/
  | frint {n : Nat} {ft : BitVec 2} {opc : BitVec 6} {ra rd : Int} :
      frintOf v.op = some (n, ft, opc) → v.args.size = 1 → fargObj lc v 0 = .ok (8 * n, ra) →
      fresObj lc v = .ok (8 * n, rd) →
      VK55a lc v (.prog (.ofShape { as := opAsm v.op, from_ := regA ra, to := regA rd }))

theorem frintOf_some {op : Op} {n : Nat} {ft : BitVec 2} {opc : BitVec 6}
    (h : frintOf op = some (n, ft, opc)) :
    op = .ARM64FRINTND ∧ n = 8 ∧ ft = 1 ∧ opc = 8 ∨ op = .ARM64FRINTNS ∧ n = 4 ∧ ft = 0 ∧ opc = 8 ∨
    op = .ARM64FRINTPD ∧ n = 8 ∧ ft = 1 ∧ opc = 9 ∨ op = .ARM64FRINTPS ∧ n = 4 ∧ ft = 0 ∧ opc = 9 ∨
    op = .ARM64FRINTMD ∧ n = 8 ∧ ft = 1 ∧ opc = 10 ∨ op = .ARM64FRINTMS ∧ n = 4 ∧ ft = 0 ∧ opc = 10 ∨
    op = .ARM64FRINTZD ∧ n = 8 ∧ ft = 1 ∧ opc = 11 ∨ op = .ARM64FRINTZS ∧ n = 4 ∧ ft = 0 ∧ opc = 11 ∨
    op = .ARM64FRINTAD ∧ n = 8 ∧ ft = 1 ∧ opc = 12 ∨ op = .ARM64FRINTAS ∧ n = 4 ∧ ft = 0 ∧ opc = 12 := by
  unfold frintOf at h
  repeat' split at h
  all_goals (cases h <;> simp_all)

section Helpers

variable {lc : LocCtx} {v : Value} {kd : VKind2}

private theorem simd55_spec {cnt : Bool} (hop : v.op = cond cnt .ARM64VCNT .ARM64VUADDLV)
    (h : simd55 lc v cnt = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK55a lc v kd := by
  unfold simd55 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, ra⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cd, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨ht, .simd hop hsz hao hro⟩

private theorem frint55_spec {n : Nat} {ft : BitVec 2} {opc : BitVec 6}
    (hop : frintOf v.op = some (n, ft, opc)) (h : fun46 lc v n n = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK55a lc v kd := by
  unfold fun46 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, ra⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cd, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨ht, .frint hop hsz hao hro⟩

end Helpers

/-- What `vkind55a` accepted: no temporary, and `VK55a`. -/
theorem vkind55a_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (h : vkind55a lc v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK55a lc v kd := by
  unfold vkind55a at h
  by_cases h1 : v.op = .ARM64VCNT
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h
    exact simd55_spec (cnt := true) h1 h
  · by_cases h2 : v.op = .ARM64VUADDLV
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq, reduceCtorEq] at h
      exact simd55_spec (cnt := false) h2 h
    · simp only [h1, h2, ↓reduceIte] at h
      cases hf : frintOf v.op with
      | none => rw [hf] at h; cases h
      | some p =>
        obtain ⟨n, ft, opc⟩ := p
        rw [hf] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact frint55_spec hf h

/-- Off the ops of G55's group A, `vkind55a` is `none`. -/
theorem vkind55a_none {lc : LocCtx} {v : Value} (h : op55a v.op = false) :
    vkind55a lc v = none := by
  simp only [op55a, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [vkind55a, h1, h2, h3, ↓reduceIte, Option.map_none]

/-- A value `VK55a` accepted has an op of G55's group A. -/
theorem vk55a_op {lc : LocCtx} {v : Value} {kd : VKind2} (h : VK55a lc v kd) :
    op55a v.op = true := by
  cases h with
  | @simd cnt _ _ hop => cases cnt <;> simp [op55a, hop]
  | frint hop => simp [op55a, hop]

end GoFV.Gen.Check
