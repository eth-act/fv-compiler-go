import GoFV.Gen.Check58a
import GoFV.Proof.Gen.Spec51c

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G58, group A, accepted (`GoFV/Gen/Check58a.lean`)

`VK58a`: what `vkind58a` accepted of a value, one constructor per kind (`rev16w`, `maddw`, `bin`,
`binK`, `sh`, `ubfiz`, `csinc`, `stlr`, `round`). `vkind58a_spec` unfolds an accepted value,
`vkind58a_none` says `vkind58a` is `none` off `op58a`, `vk58a_op` that a `VK58a` value has one of
`op58a`'s ops, and `ops58a_facts` what those ops are not.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind58a` accepted of a value, and what it emits. -/
inductive VK58a (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- `REV16W x`: `REV16W Rm, Rd`, `x` of at least 16 bits, the result of at most 16. -/
  | rev16w {cx c : Nat} {rm rd : Int} :
      v.op = .ARM64REV16W → v.args.size = 1 → argObj lc v 0 = .ok (cx, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → c ≤ 16 → 16 ≤ cx →
      VK58a lc v (.prog (.ofShape { as := .REV16W, from_ := regA rm, to := regA rd }))
  /-- `MADDW`, `MSUBW a x y`: `as Rm, Ra, Rn, Rd`, the result of class `c ≤ 32`, the arguments of
  at least `c` bits. -/
  | maddw {as : As} {ca cx cy c : Nat} {ra rm rn rd : Int} :
      madd37? v.op = some (as, true) → v.args.size = 3 → argObj lc v 0 = .ok (ca, ra) →
      argObj lc v 1 = .ok (cx, rm) → argObj lc v 2 = .ok (cy, rn) → resObj lc v = .ok (c, rd) →
      8 ≤ c → c ≤ 32 → c ≤ ca → c ≤ cx → c ≤ cy →
      VK58a lc v (.prog ⟨maddOK as ra rm rn rd, as.name⟩)
  /-- A register op of G32: `as Rm, Rn, Rd`, each argument of at least the result's class or a
  boolean. -/
  | bin {as : As} {ca cb c : Nat} {rn rm rd : Int} :
      bin32? v.op = some as → v.args.size = 2 → argObj lc v 0 = .ok (ca, rn) →
      argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) → 8 ≤ c → (c ≤ ca ∨ ca = 1) →
      (c ≤ cb ∨ cb = 1) →
      VK58a lc v (.prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }))
  /-- A constant op of G32 of a boolean: `as $k, Rn, Rd`. -/
  | binK {as : As} {ca c : Nat} {rn rd : Int} :
      binK32? v.op = some as → v.args.size = 1 → argObj lc v 0 = .ok (ca, rn) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → ca = 1 →
      VK58a lc v (.prog (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }))
  /-- A register shift of G36 by a boolean: `as Rm, Rn, Rd`, `x` of at least the result's class
  (`LSL`) or of 64 bits. -/
  | sh {as : As} {ca cb c : Nat} {rn rm rd : Int} :
      sh36? v.op = some as → v.args.size = 2 → argObj lc v 0 = .ok (ca, rn) →
      argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) → 8 ≤ c → cb = 1 →
      (as = .LSL → c ≤ ca) → (as ≠ .LSL → ca = 64) →
      VK58a lc v (.prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }))
  /-- `UBFIZ [k] x` of a boolean: `UBFIZ $lsb, Rn, $width, Rd`. -/
  | ubfiz {ca c : Nat} {rn rd : Int} :
      v.op = .ARM64UBFIZ → v.args.size = 1 → 0 ≤ v.auxInt.toInt → v.auxInt.toInt < 2 ^ 16 →
      argObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) → 8 ≤ c → ca = 1 →
      VK58a lc v (.prog ⟨ubfizOK (v.auxInt.toInt / 256) (v.auxInt.toInt % 256) rn rd, "UBFIZ"⟩)
  /-- `CSINC [cc] x y f`: `CSINC cond, Rx, Ry, Rd`, each argument of at least the result's class
  or a boolean. -/
  | csinc {f : ID} {o : Op} {cc rn rm rd : Int} {ca cb c : Nat} :
      v.op = .ARM64CSINC → v.args.size = 3 → v.args[2]? = some f → (lc.ty f).isFlags = true →
      lc.home f = none → ccOp? v.auxInt = some o → (Cond.ofOp o).isSome = true →
      ARM64.condBits o = some cc → argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → (c ≤ ca ∨ ca = 1) → (c ≤ cb ∨ cb = 1) →
      VK58a lc v (.prog ⟨csincOK cc rn rm rd, "CSINC"⟩)
  /-- A store-release of `n` bytes of a source of at least `8 n` bits: `as Rx, (Rp)`. -/
  | stlr {as : As} {n ca cs : Nat} {rn rs : Int} :
      (v.op = .ARM64STLRW ∨ v.op = .ARM64STLRB) → stlr? v.op = some (as, n) → v.args.size = 3 →
      memTy (lc.ty v.id) = true →
      lc.home v.id = none → v.aux = none → v.auxInt.toInt = 0 → argObj lc v 0 = .ok (ca, rn) →
      argObj lc v 1 = .ok (cs, rs) → memArg lc v 2 = .ok () → ca = 64 → 8 * n ≤ cs →
      VK58a lc v (.prog ⟨plain as (· == regA rs) (· == memA rn 0), as.name⟩)
  /-- `LoweredRound32F`, `LoweredRound64F x`: no code, the result in `x`'s `F` register at `x`'s
  class. -/
  | round {c : Nat} {ra : Int} :
      (v.op = .ARM64LoweredRound32F ∧ c = 32 ∨ v.op = .ARM64LoweredRound64F ∧ c = 64) →
      v.args.size = 1 → fargObj lc v 0 = .ok (c, ra) → fresObj lc v = .ok (c, ra) →
      VK58a lc v .none

section Helpers

variable {lc : LocCtx} {v : Value} {kd : VKind2}

theorem rev16w58_spec (hop : v.op = .ARM64REV16W) (h : rev16w58 lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK58a lc v kd := by
  unfold rev16w58 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨cx, rm⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨ht, .rev16w hop hsz hao hro hw.1.1 hw.1.2 hw.2⟩

theorem maddw58_spec {as : As} (hop : madd37? v.op = some (as, true))
    (h : maddw58 lc v as = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK58a lc v kd := by
  unfold maddw58 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, ra⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cx, rm⟩, hxo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cy, rn⟩, hyo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨h8, h32⟩, hca⟩, hcx⟩, hcy⟩ := hw
  exact ⟨ht, .maddw hop hsz hao hxo hyo hro h8 h32 hca hcx hcy⟩

theorem bin58_spec {as : As} (hop : bin32? v.op = some as) (h : bin58 lc v as = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK58a lc v kd := by
  unfold bin58 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [wid51c, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  exact ⟨ht, .bin hop hsz hao hbo hro hw.1.1 hw.1.2 hw.2⟩

theorem binK58_spec {as : As} (hop : binK32? v.op = some as) (h : binK58 lc v as = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK58a lc v kd := by
  unfold binK58 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  exact ⟨ht, .binK hop hsz hao hro hw.1 hw.2⟩

theorem sh58_spec {as : As} (hop : sh36? v.op = some as) (h : sh58 lc v as = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK58a lc v kd := by
  unfold sh58 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨⟨h8, hcb⟩, hx⟩ := hw
  refine ⟨ht, .sh hop hsz hao hbo hro h8 hcb (fun hl => ?_) (fun hl => ?_)⟩
  · simpa [hl] using hx
  · simpa [hl] using hx

theorem ubfiz58_spec (hop : v.op = .ARM64UBFIZ) (h : ubfiz58 lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK58a lc v kd := by
  unfold ubfiz58 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsz hw
  exact ⟨ht, .ubfiz hop hsz.1.1 hsz.1.2 hsz.2 hao hro hw.1 hw.2⟩

theorem csinc58_spec (hop : v.op = .ARM64CSINC) (h : csinc58 lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK58a lc v kd := by
  unfold csinc58 at h
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
        simp only [wid51c, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
          beq_iff_eq] at hw
        simp only [ex_pure, Except.ok.injEq] at h
        subst h
        exact .csinc hop hsz hf hfl.1 hfl.2 ho hco hcc hao hbo hro hw.1.1 hw.1.2 hw.2
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next => simp [ex_throw] at h

theorem stlr58_spec {as : As} {n : Nat} (hw0 : v.op = .ARM64STLRW ∨ v.op = .ARM64STLRB)
    (hop : stlr? v.op = some (as, n))
    (h : stlr58 lc v as n = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK58a lc v kd := by
  unfold stlr58 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsh, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cs, rs⟩, hso, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsh hw
  obtain ⟨⟨⟨⟨hsz, hmt⟩, hhn⟩, haux⟩, hk⟩ := hsh
  exact ⟨ht, .stlr hw0 hop hsz hmt hhn haux hk hao hso hma hw.1 hw.2⟩

theorem round58_spec {c : Nat}
    (hop : v.op = .ARM64LoweredRound32F ∧ c = 32 ∨ v.op = .ARM64LoweredRound64F ∧ c = 64)
    (h : round58 lc v c = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK58a lc v kd := by
  unfold round58 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, ra⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cd, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hw
  exact ⟨ht, .round hop hsz hao hro⟩

end Helpers

/-- What `vkind58a` accepted: no temporary, and `VK58a`. -/
theorem vkind58a_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind58a lc g v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK58a lc v kd := by
  unfold vkind58a at h
  by_cases h1 : v.op = .ARM64REV16W
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h
    exact rev16w58_spec h1 h
  by_cases h2 : v.op = .ARM64MADDW
  · simp only [h1, h2, ↓reduceIte, reduceCtorEq, Option.some.injEq] at h
    exact maddw58_spec (by rw [h2]; rfl) h
  by_cases h3 : v.op = .ARM64MSUBW
  · simp only [h1, h2, h3, ↓reduceIte, reduceCtorEq, Option.some.injEq] at h
    exact maddw58_spec (by rw [h3]; rfl) h
  by_cases h4 : v.op = .ARM64UBFIZ
  · simp only [h1, h2, h3, h4, ↓reduceIte, reduceCtorEq, Option.some.injEq] at h
    exact ubfiz58_spec h4 h
  by_cases h5 : v.op = .ARM64CSINC
  · simp only [h1, h2, h3, h4, h5, ↓reduceIte, reduceCtorEq, Option.some.injEq] at h
    exact csinc58_spec h5 h
  by_cases h6 : v.op = .ARM64STLRW
  · simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte, reduceCtorEq, Option.some.injEq] at h
    exact stlr58_spec (.inl h6) (by rw [h6]; rfl) h
  by_cases h7 : v.op = .ARM64STLRB
  · simp only [h1, h2, h3, h4, h5, h6, h7, ↓reduceIte, reduceCtorEq, Option.some.injEq] at h
    exact stlr58_spec (.inr h7) (by rw [h7]; rfl) h
  by_cases h8 : v.op = .ARM64LoweredRound32F
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte, reduceCtorEq, Option.some.injEq] at h
    exact round58_spec (.inl ⟨h8, rfl⟩) h
  by_cases h9 : v.op = .ARM64LoweredRound64F
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, ↓reduceIte, reduceCtorEq,
      Option.some.injEq] at h
    exact round58_spec (.inr ⟨h9, rfl⟩) h
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, ↓reduceIte] at h
  cases hb : bin32? v.op with
  | some as =>
    rw [hb] at h
    exact bin58_spec hb (Option.some.inj h)
  | none =>
    rw [hb] at h
    cases hk : binK32? v.op with
    | some as =>
      rw [hk] at h
      exact binK58_spec hk (Option.some.inj h)
    | none =>
      rw [hk] at h
      cases hs : sh36? v.op with
      | some as =>
        rw [hs] at h
        exact sh58_spec hs (Option.some.inj h)
      | none => rw [hs] at h; cases h

/-- Off the ops of G58's group A, `vkind58a` is `none`. -/
theorem vkind58a_none {lc : LocCtx} {g : G2In} {v : Value} (h : op58a v.op = false) :
    vkind58a lc g v = none := by
  simp only [op58a, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hb⟩, hk⟩, hs⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  simp only [vkind58a, h1, h2, h3, h4, h5, h6, h7, h8, h9, ↓reduceIte, hb, hk, hs]

/-- A value `VK58a` accepted has an op of G58's group A. -/
theorem vk58a_op {lc : LocCtx} {v : Value} {kd : VKind2} (h : VK58a lc v kd) :
    op58a v.op = true := by
  cases h with
  | rev16w hop => simp [op58a, hop]
  | maddw hop =>
    revert hop; unfold madd37?
    split <;> intro hop <;> (cases hop <;> simp_all [op58a])
  | bin hop => simp [op58a, hop]
  | binK hop => simp [op58a, hop]
  | sh hop => simp [op58a, hop]
  | ubfiz hop => simp [op58a, hop]
  | csinc hop => simp [op58a, hop]
  | stlr hop =>
    rcases hop with h | h <;> simp [op58a, h]
  | round hop => rcases hop with ⟨hop, -⟩ | ⟨hop, -⟩ <;> simp [op58a, hop]

/-! ## The ops -/

/-- G58's group A. -/
def ops58a : List Op :=
  [.ARM64REV16W, .ARM64MADDW, .ARM64MSUBW, .ARM64MUL, .ARM64MNEG, .ARM64AND, .ARM64OR, .ARM64XOR,
    .ARM64BIC, .ARM64EON, .ARM64ORN, .ARM64ORconst, .ARM64XORconst, .ARM64SLL, .ARM64SRL,
    .ARM64SRA, .ARM64UBFIZ, .ARM64CSINC, .ARM64STLRW, .ARM64STLRB, .ARM64LoweredRound32F,
    .ARM64LoweredRound64F]

theorem ops58a_of {op : Op} (h : op58a op = true) : op ∈ ops58a := by
  simp only [op58a, Bool.or_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
  rcases h with ((((((((((h | h) | h) | ⟨as, h⟩) | ⟨as, h⟩) | ⟨as, h⟩) | h) | h) | h) | h) | h) | h
  all_goals first
    | (subst h; simp [ops58a])
    | (revert h; first | unfold bin32? | unfold binK32? | unfold sh36?
       split <;> intro h <;> (cases h <;> simp [ops58a]))

/-- G58's group A clobber nothing and are no `Phi`, nil check, bounds check or entry value. -/
theorem ops58a_facts {op : Op} (hmem : op ∈ ops58a) :
    op ≠ .Phi ∧ op ≠ .LoadReg ∧ op ≠ .StoreReg ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64MOVDnop ∧
      op.regInfo.clobbers.isEmpty = true ∧ op.regInfo.clobbersArg0 = false ∧
      op.regInfo.clobbersArg1 = false ∧ op.clobberFlags = false ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false ∧ entryOp24 op = false := by
  simp only [ops58a, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h <;> subst h <;>
    exact ⟨nofun, nofun, nofun, nofun, nofun, rfl, rfl, rfl, rfl, nofun, rfl, rfl⟩

end GoFV.Gen.Check
