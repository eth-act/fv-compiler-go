import GoFV.Gen.Check57a
import GoFV.Proof.Gen.Spec50

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `vkind57a` accepted (`GoFV/Gen/Check57a.lean`)

`VK57a`: `STPW` (`stpw`) and the `LDPW`/`LDPSW` with an aux of a global (`glob`) or of a frame
variable in a `Blk.temp` block (`var`), and the one Prog each emits (`vkind57a_spec`). `vkind57a`
is `none` off `op57a` (`vkind57a_none`), and every `VK57a` value's op is one of `op57a`
(`vk57a_op`). The ops (`ops57a`) are no `Phi`, nil check, bounds check or entry value and clobber
nothing (`ops57a_facts`); the upper-bit table is empty after `STPW` (`uStep35_57a`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `LDPW` (zero-extended) or `LDPSW` (sign-extended, `sg`), with the opcode `as` it emits. -/
def LdpwOp (op : Op) (as : As) (sg : Bool) : Prop :=
  op = .ARM64LDPW ∧ as = .LDPW ∧ sg = false ∨ op = .ARM64LDPSW ∧ as = .LDPSW ∧ sg = true

theorem LdpwOp.pairOp {op : Op} {as : As} {sg : Bool} (h : LdpwOp op as sg) :
    pairOp50 op = some (as, 4, sg, false) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rfl

/-- What `vkind57a` accepted, and what it emits. -/
inductive VK57a (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- `STPW (Rx, Ry), off(Rn)`: the address in a 64-bit register, sources of at least 32 bits. -/
  | stpw {rn rx ry : Int} {cx cy : Nat} :
      v.op = .ARM64STPW → v.args.size = 4 → v.aux = none → memTy (lc.ty v.id) = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rn) → argObj lc v 1 = .ok (cx, rx) →
      argObj lc v 2 = .ok (cy, ry) → memArg lc v 3 = .ok () → 32 ≤ cx → 32 ≤ cy →
      VK57a lc g v
        (.prog (.ofShape { as := .STPW, from_ := pairA rx ry, to := memA rn v.auxInt.toInt }))
  /-- `LDPW`/`LDPSW sym+off(SB), (Ra, Rb)` of a global, into two distinct X registers G1 may
  write, two components of integer classes of at least 8 bits. -/
  | glob {as : As} {sg : Bool} {x : AuxRef} {name : GoStr} {abi : Nat} {ra rb : Nat} {oa ob : Int}
      {t0 t1 : Ty} {c0 c1 : Nat} :
      LdpwOp v.op as sg → v.args.size = 2 → v.aux = some x →
      symOf? lc.ctx.tabs x = some (name, abi) →
      lc.ty v.id = .tuple [t0, t1] → cls t0 = some c0 → cls t1 = some c1 → 8 ≤ c0 → 8 ≤ c1 →
      memArg lc v 1 = .ok () →
      lc.home v.id = some (.pair (some ra) (some rb)) → ra ≠ rb → ra ≠ zeroReg → rb ≠ zeroReg →
      destOK ra = true → destOK rb = true → objOf? ra = some oa → objOf? rb = some ob →
      VK57a lc g v (.prog ⟨plain as (globA g name abi v.auxInt.toInt) (· == pairA oa ob),
        "LDPW sym(SB)"⟩)
  /-- `LDPW`/`LDPSW off'(RSP), (Ra, Rb)` of a frame variable in a `Blk.temp` block at its
  `NAME_AUTO` operand `off` (`FrameVarOK`). -/
  | var {as : As} {sg : Bool} {x : AuxRef} {off : Int} {ra rb : Nat} {oa ob : Int}
      {t0 t1 : Ty} {c0 c1 : Nat} :
      LdpwOp v.op as sg → v.args.size = 2 → FrameVarOK lc g v x off →
      lc.ty v.id = .tuple [t0, t1] → cls t0 = some c0 → cls t1 = some c1 → 8 ≤ c0 → 8 ≤ c1 →
      memArg lc v 1 = .ok () →
      lc.home v.id = some (.pair (some ra) (some rb)) → ra ≠ rb → ra ≠ zeroReg → rb ≠ zeroReg →
      destOK ra = true → destOK rb = true → objOf? ra = some oa → objOf? rb = some ob →
      VK57a lc g v (.prog ⟨plain as (slotA · .AUTO off) (· == pairA oa ob), "LDPW var"⟩)

section Helpers

variable {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}

private theorem stpw57_spec (hop : v.op = .ARM64STPW) (h : stpw57 lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK57a lc g v kd := by
  unfold stpw57 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hs, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cx, rx⟩, hxo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cy, ry⟩, hyo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at ht hs hw
  obtain ⟨⟨⟨hsz, hax⟩, hmt⟩, hhn⟩ := hs
  obtain ⟨⟨rfl, hx⟩, hy⟩ := hw
  exact ⟨ht, .stpw hop hsz hax hmt hhn hao hxo hyo hma hx hy⟩

private theorem ldpw57_spec {as : As} {sg : Bool} (hop : LdpwOp v.op as sg)
    (h : ldpw57 lc g v as = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK57a lc g v kd := by
  unfold ldpw57 at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  obtain ⟨hs, h⟩ := ex_guard h
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨hsz, hty⟩ := hs
  obtain ⟨t0, t1, c0, c1, hty, h0, h1, h80, h81⟩ := pairTys_spec hty
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  split at h
  next ra rb hph =>
    obtain ⟨hr, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hr
    obtain ⟨⟨⟨⟨hne, hza⟩, hzb⟩, hda⟩, hdb⟩ := hr
    split at h
    next oa hoa =>
      split at h
      next ob hob =>
        split at h
        next x hx =>
          split at h
          next name abi hsy =>
            simp only [ex_pure, Except.ok.injEq] at h
            subst h
            exact .glob hop hsz hx hsy hty h0 h1 h80 h81 hma (pairHome?_eq hph) hne hza hzb hda
              hdb hoa hob
          next =>
            obtain ⟨r, hfv, h⟩ := ex_bind_eq_ok h
            split at h
            next x' off =>
              simp only [ex_pure, Except.ok.injEq] at h
              subst h
              exact .var hop hsz (frameVar?_spec hfv) hty h0 h1 h80 h81 hma (pairHome?_eq hph)
                hne hza hzb hda hdb hoa hob
            next => simp [ex_throw] at h
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next => simp [ex_throw] at h

end Helpers

/-- What `vkind57a` accepted: no temporary, and `VK57a`. -/
theorem vkind57a_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind57a lc g v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK57a lc g v kd := by
  unfold vkind57a at h
  by_cases h1 : v.op = .ARM64STPW
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h
    exact stpw57_spec h1 h
  · by_cases h2 : v.op = .ARM64LDPW
    · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at h
      split at h
      · simp only [Option.some.injEq] at h
        exact ldpw57_spec (.inl ⟨h2, rfl, rfl⟩) h
      · cases h
    · by_cases h3 : v.op = .ARM64LDPSW
      · simp only [h1, h2, h3, ↓reduceIte, reduceCtorEq] at h
        split at h
        · simp only [Option.some.injEq] at h
          exact ldpw57_spec (.inr ⟨h3, rfl, rfl⟩) h
        · cases h
      · simp only [h1, h2, h3, ↓reduceIte, reduceCtorEq] at h

/-- Off the ops of G57's group A, `vkind57a` is `none`. -/
theorem vkind57a_none {lc : LocCtx} {g : G2In} {v : Value} (h : op57a v.op = false) :
    vkind57a lc g v = none := by
  simp only [op57a, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [vkind57a, h1, h2, h3, ↓reduceIte]

/-- A value `VK57a` accepted has an op of G57's group A. -/
theorem vk57a_op {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK57a lc g v kd) :
    op57a v.op = true := by
  cases h with
  | stpw hop => simp [op57a, hop]
  | glob hop => rcases hop with ⟨hop, -⟩ | ⟨hop, -⟩ <;> simp [op57a, hop]
  | var hop => rcases hop with ⟨hop, -⟩ | ⟨hop, -⟩ <;> simp [op57a, hop]

/-! ## The ops -/

/-- G57's group A: `STPW`, `LDPW`, `LDPSW`. -/
def ops57a : List Op := [.ARM64STPW, .ARM64LDPW, .ARM64LDPSW]

theorem ops57a_of {op : Op} (h : op57a op = true) : op ∈ ops57a := by
  simp only [op57a, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl <;> simp [ops57a]

/-- G57's group A are memory ops that clobber nothing, no `Phi`, nil check, bounds check or entry
value. -/
theorem ops57a_facts {op : Op} (hmem : op ∈ ops57a) :
    op ≠ .Phi ∧ op ≠ .LoadReg ∧ op ≠ .StoreReg ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64MOVDnop ∧
      op.regInfo.clobbers.isEmpty = true ∧ op.regInfo.clobbersArg0 = false ∧
      op.regInfo.clobbersArg1 = false ∧ op.clobberFlags = false ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false ∧ entryOp24 op = false := by
  simp only [ops57a, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h <;> subst h <;>
    exact ⟨nofun, nofun, nofun, nofun, nofun, rfl, rfl, rfl, rfl, nofun, rfl, rfl⟩

/-- G35's table is empty after `STPW` (the word pair loads of G57's group A follow G35's table
register by register, `uStep35_ldpX`). -/
theorem uStep35_57a {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (h : v.op = .ARM64STPW) : uStep35 lc L v = [] := by
  simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
    keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

end GoFV.Gen.Check
