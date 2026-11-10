import GoFV.Gen.Check55b
import GoFV.Proof.Gen.Spec51b

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G55, group B, accepted (`GoFV/Gen/Check55b.lean`)

`VK55b`: what `vkind55b` accepted of a value, one constructor per op family (`negSh`: the shifted
`NEG`s, `clzw`, `mull`, `extr`: the extracts). `vkind55b_spec` unfolds an accepted value,
`vkind55b_none` says `vkind55b` is `none` outside `op55b`, and `vk55b_op` that a `VK55b` value is
one of `op55b`'s ops.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind55b` accepted of a value, and what it emits. -/
inductive VK55b (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- `NEGshiftXX [k] x`: `NEG Rm SHIFT k, Rd`, `x` of at least the result's class (`LSL`) or of
  64 bits. -/
  | negSh {typ ca c : Nat} {rm rd : Int} :
      negSh55b? v.op = some typ → v.args.size = 1 → 0 ≤ v.auxInt.toInt →
      v.auxInt.toInt < 64 → argObj lc v 0 = .ok (ca, rm) → resObj lc v = .ok (c, rd) → 8 ≤ c →
      (typ = 0 → c ≤ ca) → (typ ≠ 0 → ca = 64) →
      VK55b lc v (.prog (.ofShape
        { as := .NEG, from_ := shiftA typ rm v.auxInt.toInt.toNat, to := regA rd }))
  /-- `CLZW x`: `CLZW Rm, Rd`, `x` of at least 32 bits. -/
  | clzw {cx c : Nat} {rm rd : Int} :
      v.op = .ARM64CLZW → v.args.size = 1 → argObj lc v 0 = .ok (cx, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → 32 ≤ cx →
      VK55b lc v (.prog (.ofShape { as := .CLZW, from_ := regA rm, to := regA rd }))
  /-- `MULL x y`: `SMULL Rm, Rn, Rd`, `x` and `y` of at least 32 bits. -/
  | mull {cx cy c : Nat} {rn rm rd : Int} :
      v.op = .ARM64MULL → v.args.size = 2 → argObj lc v 0 = .ok (cx, rn) →
      argObj lc v 1 = .ok (cy, rm) → resObj lc v = .ok (c, rd) → 8 ≤ c → 32 ≤ cx → 32 ≤ cy →
      VK55b lc v (.prog (.ofShape { as := .SMULL, from_ := regA rm, reg := rn, to := regA rd }))
  /-- `EXTRconst`, `EXTRWconst [k] x y`: `EXTR`/`EXTRW $k, Rx, Ry, Rd`, `0 ≤ k < w`, `x` and `y`
  of at least `w` bits. -/
  | extr {as : As} {w ca cb c : Nat} {rn rm rd : Int} :
      extr55b? v.op = some (as, w) → v.args.size = 2 → argObj lc v 0 = .ok (ca, rn) →
      argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) → 8 ≤ c → w ≤ ca → w ≤ cb →
      0 ≤ v.auxInt.toInt → v.auxInt.toInt < w →
      VK55b lc v (.prog ⟨extrOK as v.auxInt.toInt rn rm rd, as.name⟩)

/-- What `extrOK` fixes of a Prog. -/
theorem extrOK_spec {as : As} {k rn rm rd : Int} {p : Prog} (h : extrOK as k rn rm rd p = true) :
    p.as = as ∧ p.from_ = constA k ∧ p.reg = rm ∧ p.to = regA rd ∧ p.scond = 0 ∧
      p.regTo2 = 0 ∧ ∃ x, p.rest = #[(x, regA rn)] := by
  unfold extrOK at h
  obtain ⟨h, hm⟩ := Eq.mp (Bool.and_eq_true _ _) h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨has, hf⟩, hr⟩, ht⟩, hs⟩, h2⟩ := h
  refine ⟨has, hf, hr, ht, hs, h2, ?_⟩
  generalize p.rest = r at hm ⊢
  rcases r with ⟨_ | ⟨⟨x, a⟩, _ | ⟨y, l⟩⟩⟩
  · exact absurd hm Bool.false_ne_true
  · have h3 : (a == regA rn) = true := hm
    exact ⟨x, by rw [beq_iff_eq.mp h3]⟩
  · exact absurd hm Bool.false_ne_true

/-- What `negSh55bKind` accepted: no temporary, and `VK55b`'s `negSh`. -/
theorem negSh55bKind_spec {lc : LocCtx} {v : Value} {typ : Nat} {kd : VKind2}
    (hop : negSh55b? v.op = some typ) (h : negSh55bKind lc v typ = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK55b lc v kd := by
  unfold negSh55bKind at h
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
  refine ⟨ht, .negSh hop hsz hk.1 hk.2 hao hro h8 (fun hl => ?_) (fun hl => ?_)⟩
  · simpa [hl] using hw
  · simpa [hl] using hw

/-- What `un37Kind lc v .CLZW 32` accepted of `CLZW`: no temporary, and `VK55b`'s `clzw`. -/
theorem clzw55bKind_spec {lc : LocCtx} {v : Value} {kd : VKind2} (hop : v.op = .ARM64CLZW)
    (h : un37Kind lc v .CLZW 32 = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK55b lc v kd := by
  unfold un37Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨cx, rm⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨ht, .clzw hop hsz hao hro hw.1 hw.2⟩

/-- What `bin37Kind lc v .SMULL 32` accepted of `MULL`: no temporary, and `VK55b`'s `mull`. -/
theorem mull55bKind_spec {lc : LocCtx} {v : Value} {kd : VKind2} (hop : v.op = .ARM64MULL)
    (h : bin37Kind lc v .SMULL 32 = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK55b lc v kd := by
  unfold bin37Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨cx, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cy, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨ht, .mull hop hsz hao hbo hro hw.1.1 hw.1.2 hw.2⟩

/-- What `extr55bKind` accepted: no temporary, and `VK55b`'s `extr`. -/
theorem extr55bKind_spec {lc : LocCtx} {v : Value} {as : As} {w : Nat} {kd : VKind2}
    (hop : extr55b? v.op = some (as, w)) (h : extr55bKind lc v as w = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK55b lc v kd := by
  unfold extr55bKind at h
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
  exact ⟨ht, .extr hop hsz hao hbo hro hw.1.1.1.1 hw.1.1.1.2 hw.1.1.2 hw.1.2 hw.2⟩

/-- What `vkind55b` accepted: no temporary, and `VK55b`. -/
theorem vkind55b_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (h : vkind55b lc v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK55b lc v kd := by
  unfold vkind55b at h
  cases h1 : negSh55b? v.op with
  | some typ =>
    rw [h1] at h
    exact negSh55bKind_spec h1 (Option.some.inj h)
  | none =>
    rw [h1] at h
    by_cases hc : v.op = .ARM64CLZW
    · simp only [hc, ↓reduceIte] at h
      exact clzw55bKind_spec hc (Option.some.inj h)
    simp only [hc, ↓reduceIte] at h
    by_cases hm : v.op = .ARM64MULL
    · simp only [hm, ↓reduceIte] at h
      exact mull55bKind_spec hm (Option.some.inj h)
    simp only [hm, ↓reduceIte] at h
    cases h2 : extr55b? v.op with
    | some p =>
      obtain ⟨as, w⟩ := p
      rw [h2] at h
      exact extr55bKind_spec h2 (Option.some.inj h)
    | none => rw [h2] at h; cases h

/-- Outside `op55b`, `vkind55b` is `none`. -/
theorem vkind55b_none {lc : LocCtx} {v : Value} (h : op55b v.op = false) : vkind55b lc v = none := by
  simp only [op55b, Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  unfold vkind55b
  rw [h1]
  simp only [h2, h3, ↓reduceIte]
  rw [h4]

/-- A `VK55b` value is one of `op55b`'s ops. -/
theorem vk55b_op {lc : LocCtx} {v : Value} {kd : VKind2} (h : VK55b lc v kd) : op55b v.op = true := by
  cases h with
  | negSh hop => simp [op55b, hop]
  | clzw hop => simp [op55b, hop]
  | mull hop => simp [op55b, hop]
  | extr hop => simp [op55b, hop]

end GoFV.Gen.Check
