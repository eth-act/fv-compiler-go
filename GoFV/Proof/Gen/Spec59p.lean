import GoFV.Gen.Check59p
import GoFV.Proof.Gen.Spec57a

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `vkind59p` accepted (`GoFV/Gen/Check59p.lean`)

`VK59p`: the `FLDPD`/`FLDPS` with an aux of a global (`glob`) or of a frame variable in a
`Blk.temp` block (`var`), and the one Prog each emits (`vkind59p_spec`). `vkind59p` is `none` off
`op59p` (`vkind59p_none`), and every `VK59p` value's op is one of `op59p` (`vk59p_op`). The ops
(`ops59p`) are no `Phi`, nil check, bounds check or entry value and clobber nothing
(`ops59p_facts`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `FLDPD` (8-byte elements) or `FLDPS` (4-byte), with the opcode `as` it emits. -/
def FldpOp (op : Op) (as : As) (n : Nat) : Prop :=
  op = .ARM64FLDPD ∧ as = .FLDPD ∧ n = 8 ∨ op = .ARM64FLDPS ∧ as = .FLDPS ∧ n = 4

theorem FldpOp.pairOp {op : Op} {as : As} {n : Nat} (h : FldpOp op as n) :
    pairOp50 op = some (as, n, false, true) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rfl

/-- The opcode and element bytes of `FLDPD`/`FLDPS`. -/
theorem FldpOp.asN {op : Op} {as : As} {n : Nat} (h : FldpOp op as n) :
    as = .FLDPD ∧ n = 8 ∨ as = .FLDPS ∧ n = 4 := by
  rcases h with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨h1, h2⟩

/-- What `vkind59p` accepted, and what it emits. -/
inductive VK59p (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- `FLDPD`/`FLDPS sym+off(SB), (Fa, Fb)` of a global, into two distinct V registers, two
  components of float shapes of the element's width. -/
  | glob {as : As} {n : Nat} {x : AuxRef} {name : GoStr} {abi : Nat} {ra rb : Nat} {oa ob : Int}
      {t0 t1 : Ty} :
      FldpOp v.op as n → v.args.size = 2 → v.aux = some x →
      symOf? lc.ctx.tabs x = some (name, abi) →
      lc.ty v.id = .tuple [t0, t1] → fTy t0 = true → fTy t1 = true → cls t0 = some (8 * n) →
      cls t1 = some (8 * n) → memArg lc v 1 = .ok () →
      lc.home v.id = some (.pair (some ra) (some rb)) → ra ≠ rb →
      fobjOf? ra = some oa → fobjOf? rb = some ob →
      VK59p lc g v (.prog ⟨plain as (globA g name abi v.auxInt.toInt) (· == pairA oa ob),
        "FLDP sym(SB)"⟩)
  /-- `FLDPD`/`FLDPS off'(RSP), (Fa, Fb)` of a frame variable in a `Blk.temp` block at its
  `NAME_AUTO` operand `off` (`FrameVarOK`). -/
  | var {as : As} {n : Nat} {x : AuxRef} {off : Int} {ra rb : Nat} {oa ob : Int} {t0 t1 : Ty} :
      FldpOp v.op as n → v.args.size = 2 → FrameVarOK lc g v x off →
      lc.ty v.id = .tuple [t0, t1] → fTy t0 = true → fTy t1 = true → cls t0 = some (8 * n) →
      cls t1 = some (8 * n) → memArg lc v 1 = .ok () →
      lc.home v.id = some (.pair (some ra) (some rb)) → ra ≠ rb →
      fobjOf? ra = some oa → fobjOf? rb = some ob →
      VK59p lc g v (.prog ⟨plain as (slotA · .AUTO off) (· == pairA oa ob), "FLDP var"⟩)

section Helpers

variable {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}

private theorem fldp59_spec {as : As} {n : Nat} (hop : FldpOp v.op as n)
    (h : fldp59 lc g v as n = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK59p lc g v kd := by
  unfold fldp59 at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  obtain ⟨hs, h⟩ := ex_guard h
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨hsz, hty⟩ := hs
  obtain ⟨t0, t1, hty, hf0, hf1, h0, h1⟩ := fpairTys_spec hty
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  split at h
  next ra rb hph =>
    obtain ⟨hne, h⟩ := ex_guard h
    simp only [bne_iff_ne, ne_eq] at hne
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
            exact .glob hop hsz hx hsy hty hf0 hf1 h0 h1 hma (pairHome?_eq hph) hne hoa hob
          next =>
            obtain ⟨r, hfv, h⟩ := ex_bind_eq_ok h
            split at h
            next x' off =>
              simp only [ex_pure, Except.ok.injEq] at h
              subst h
              exact .var hop hsz (frameVar?_spec hfv) hty hf0 hf1 h0 h1 hma (pairHome?_eq hph)
                hne hoa hob
            next => simp [ex_throw] at h
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next => simp [ex_throw] at h

end Helpers

/-- What `vkind59p` accepted: no temporary, and `VK59p`. -/
theorem vkind59p_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind59p lc g v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK59p lc g v kd := by
  unfold vkind59p at h
  by_cases h1 : v.op = .ARM64FLDPD
  · simp only [h1, ↓reduceIte] at h
    split at h
    · simp only [Option.some.injEq] at h
      exact fldp59_spec (.inl ⟨h1, rfl, rfl⟩) h
    · cases h
  · by_cases h2 : v.op = .ARM64FLDPS
    · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at h
      split at h
      · simp only [Option.some.injEq] at h
        exact fldp59_spec (.inr ⟨h2, rfl, rfl⟩) h
      · cases h
    · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at h

/-- Off the ops of G59's group P, `vkind59p` is `none`. -/
theorem vkind59p_none {lc : LocCtx} {g : G2In} {v : Value} (h : op59p v.op = false) :
    vkind59p lc g v = none := by
  simp only [op59p, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨h1, h2⟩ := h
  simp only [vkind59p, h1, h2, ↓reduceIte]

/-- A value `VK59p` accepted has an op of G59's group P. -/
theorem vk59p_op {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK59p lc g v kd) :
    op59p v.op = true := by
  cases h with
  | glob hop => rcases hop with ⟨hop, -⟩ | ⟨hop, -⟩ <;> simp [op59p, hop]
  | var hop => rcases hop with ⟨hop, -⟩ | ⟨hop, -⟩ <;> simp [op59p, hop]

/-! ## The ops -/

/-- G59's group P: `FLDPD`, `FLDPS`. -/
def ops59p : List Op := [.ARM64FLDPD, .ARM64FLDPS]

theorem ops59p_of {op : Op} (h : op59p op = true) : op ∈ ops59p := by
  simp only [op59p, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> simp [ops59p]

/-- G59's group P are memory ops that clobber nothing, no `Phi`, nil check, bounds check or entry
value. -/
theorem ops59p_facts {op : Op} (hmem : op ∈ ops59p) :
    op ≠ .Phi ∧ op ≠ .LoadReg ∧ op ≠ .StoreReg ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64MOVDnop ∧
      op.regInfo.clobbers.isEmpty = true ∧ op.regInfo.clobbersArg0 = false ∧
      op.regInfo.clobbersArg1 = false ∧ op.clobberFlags = false ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false ∧ entryOp24 op = false := by
  simp only [ops59p, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h <;> subst h <;>
    exact ⟨nofun, nofun, nofun, nofun, nofun, rfl, rfl, rfl, rfl, nofun, rfl, rfl⟩

end GoFV.Gen.Check
