import GoFV.Gen.Check51b
import GoFV.Proof.Gen.Spec50

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G51, group b, accepted (`GoFV/Gen/Check51b.lean`)

`VK51b`: what `vkind51b` accepted of a value, one constructor per op family (`mvnSh`: the shifted
`MVN`s, `sbfiz`, `rorK`: the constant rotates, `ror`: the register rotates). `vkind51b_spec`
unfolds an accepted value, `vkind51b_none` says `vkind51b` is `none` outside `op51b`, and
`vk51b_op` that a `VK51b` value is one of `op51b`'s ops.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind51b` accepted of a value, and what it emits. -/
inductive VK51b (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- `MVNshiftXX [k] x`: `MVN Rm SHIFT k, Rd`, `x` of at least the result's class (`LSL`) or of
  64 bits. -/
  | mvnSh {typ ca c : Nat} {rm rd : Int} :
      mvnSh51b? v.op = some typ → v.args.size = 1 → 0 ≤ v.auxInt.toInt →
      v.auxInt.toInt < 64 → argObj lc v 0 = .ok (ca, rm) → resObj lc v = .ok (c, rd) → 8 ≤ c →
      (typ = 0 → c ≤ ca) → (typ ≠ 0 → ca = 64) →
      VK51b lc v (.prog (.ofShape
        { as := .MVN, from_ := shiftA typ rm v.auxInt.toInt.toNat, to := regA rd }))
  /-- `SBFIZ [k] x`: `SBFIZ $lsb, Rn, $width, Rd`, `0 < width ≤ 64`, `width ≤ ca` or `c ≤ ca`. -/
  | sbfiz {ca c : Nat} {rn rd : Int} :
      v.op = .ARM64SBFIZ → v.args.size = 1 → 0 ≤ v.auxInt.toInt → v.auxInt.toInt < 2 ^ 16 →
      argObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) → 8 ≤ c →
      0 < v.auxInt.toInt % 256 → v.auxInt.toInt % 256 ≤ 64 →
      (v.auxInt.toInt % 256 ≤ ca ∨ c ≤ ca) →
      VK51b lc v (.prog ⟨sbfizOK (v.auxInt.toInt / 256) (v.auxInt.toInt % 256) rn rd, "SBFIZ"⟩)
  /-- `RORconst`, `RORWconst [k] x`: `ROR`/`RORW $k, Rn, Rd`, `0 ≤ k < w`, `x` of at least `w`
  bits. -/
  | rorK {as : As} {w ca c : Nat} {rn rd : Int} :
      rorK51b? v.op = some (as, w) → v.args.size = 1 → argObj lc v 0 = .ok (ca, rn) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → w ≤ ca → 0 ≤ v.auxInt.toInt → v.auxInt.toInt < w →
      VK51b lc v (.prog (.ofShape
        { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }))
  /-- `ROR`, `RORW x y`: `ROR`/`RORW Rm, Rn, Rd`, `x` of at least `w` bits, `y` of at least 8. -/
  | ror {as : As} {w ca cb c : Nat} {rn rm rd : Int} :
      ror51b? v.op = some (as, w) → v.args.size = 2 → argObj lc v 0 = .ok (ca, rn) →
      argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) → 8 ≤ c → w ≤ ca → 8 ≤ cb →
      VK51b lc v (.prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }))

/-- What `sbfizOK` fixes of a Prog. -/
theorem sbfizOK_spec {lsb width rn rd : Int} {p : Prog} (h : sbfizOK lsb width rn rd p = true) :
    p.as = .SBFIZ ∧ p.from_ = constA lsb ∧ p.reg = rn ∧ p.to = regA rd ∧ p.scond = 0 ∧
      p.regTo2 = 0 ∧ ∃ x, p.rest = #[(x, constA width)] := by
  unfold sbfizOK at h
  obtain ⟨h, hm⟩ := Eq.mp (Bool.and_eq_true _ _) h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨has, hf⟩, hr⟩, ht⟩, hs⟩, h2⟩ := h
  refine ⟨has, hf, hr, ht, hs, h2, ?_⟩
  generalize p.rest = r at hm ⊢
  rcases r with ⟨_ | ⟨⟨x, a⟩, _ | ⟨y, l⟩⟩⟩
  · exact absurd hm Bool.false_ne_true
  · have h3 : (a == constA width) = true := hm
    exact ⟨x, by rw [beq_iff_eq.mp h3]⟩
  · exact absurd hm Bool.false_ne_true

/-- What `mvnSh51bKind` accepted: no temporary, and `VK51b`'s `mvnSh`. -/
theorem mvnSh51bKind_spec {lc : LocCtx} {v : Value} {typ : Nat} {kd : VKind2}
    (hop : mvnSh51b? v.op = some typ) (h : mvnSh51bKind lc v typ = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK51b lc v kd := by
  unfold mvnSh51bKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨hk, h⟩ := ex_guard h
  obtain ⟨⟨ca, rm⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk hw
  obtain ⟨h8, hw⟩ := hw
  refine ⟨ht, .mvnSh hop hsz hk.1 hk.2 hao hro h8 (fun hl => ?_) (fun hl => ?_)⟩
  · simpa [hl] using hw
  · simpa [hl] using hw

/-- What `sbfiz51bKind` accepted: no temporary, and `VK51b`'s `sbfiz`. -/
theorem sbfiz51bKind_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64SBFIZ) (h : sbfiz51bKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK51b lc v kd := by
  unfold sbfiz51bKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hsz hw
  exact ⟨ht, .sbfiz hop hsz.1.1 hsz.1.2 hsz.2 hao hro hw.1.1.1 hw.1.1.2 hw.1.2 hw.2⟩

/-- What `rorK51bKind` accepted: no temporary, and `VK51b`'s `rorK`. -/
theorem rorK51bKind_spec {lc : LocCtx} {v : Value} {as : As} {w : Nat} {kd : VKind2}
    (hop : rorK51b? v.op = some (as, w)) (h : rorK51bKind lc v as w = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK51b lc v kd := by
  unfold rorK51bKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨ht, .rorK hop hsz hao hro hw.1.1.1 hw.1.1.2 hw.1.2 hw.2⟩

/-- What `ror51bKind` accepted: no temporary, and `VK51b`'s `ror`. -/
theorem ror51bKind_spec {lc : LocCtx} {v : Value} {as : As} {w : Nat} {kd : VKind2}
    (hop : ror51b? v.op = some (as, w)) (h : ror51bKind lc v as w = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK51b lc v kd := by
  unfold ror51bKind at h
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
  exact ⟨ht, .ror hop hsz hao hbo hro hw.1.1 hw.1.2 hw.2⟩

/-- What `vkind51b` accepted: no temporary, and `VK51b`. -/
theorem vkind51b_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (h : vkind51b lc v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK51b lc v kd := by
  unfold vkind51b at h
  cases h1 : mvnSh51b? v.op with
  | some typ =>
    rw [h1] at h
    exact mvnSh51bKind_spec h1 (Option.some.inj h)
  | none =>
    rw [h1] at h
    by_cases hs : v.op = .ARM64SBFIZ
    · simp only [hs, ↓reduceIte] at h
      exact sbfiz51bKind_spec hs (Option.some.inj h)
    simp only [hs, ↓reduceIte] at h
    cases h2 : rorK51b? v.op with
    | some p =>
      obtain ⟨as, w⟩ := p
      rw [h2] at h
      exact rorK51bKind_spec h2 (Option.some.inj h)
    | none =>
      rw [h2] at h
      cases h3 : ror51b? v.op with
      | some p =>
        obtain ⟨as, w⟩ := p
        rw [h3] at h
        exact ror51bKind_spec h3 (Option.some.inj h)
      | none => rw [h3] at h; cases h

/-- Outside `op51b`, `vkind51b` is `none`. -/
theorem vkind51b_none {lc : LocCtx} {v : Value} (h : op51b v.op = false) : vkind51b lc v = none := by
  simp only [op51b, Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  unfold vkind51b
  rw [h1]
  simp only [h2, ↓reduceIte]
  rw [h3, h4]

/-- A `VK51b` value is one of `op51b`'s ops. -/
theorem vk51b_op {lc : LocCtx} {v : Value} {kd : VKind2} (h : VK51b lc v kd) : op51b v.op = true := by
  cases h with
  | mvnSh hop => simp [op51b, hop]
  | sbfiz hop => simp [op51b, hop]
  | rorK hop => simp [op51b, hop]
  | ror hop => simp [op51b, hop]

end GoFV.Gen.Check
