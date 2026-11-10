import GoFV.Gen.Check57b
import GoFV.Proof.Gen.Spec49

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `vkind57b` accepted (`GoFV/Gen/Check57b.lean`)

`VK57b`: `DMB`, `PRFM`, and the float stores (`FMOVSstore`, `FMOVDstore`, `FSTPS`, `FSTPD`) of a
frame variable (`FVar57`: G49's `FrameVar49OK` or G6's `FrameVarOK`), and the one Prog each emits
(`vkind57b_spec`). `vkind57b` is `none` off `op57b` (`vkind57b_none`), and every `VK57b` value's op
is one of `op57b` (`vk57b_op`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- An access of a frame variable at the operand `nc`, `off` (`fvar57?`): G49's (`Blk.local`) or,
when G49's does not apply, G6's (`Blk.temp`, `NAME_AUTO`). -/
inductive FVar57 (lc : LocCtx) (g : G2In) (v : Value) : AddrName → Int → Prop
  | loc {x : AuxRef} {nc : AddrName} {off : Int} : FrameVar49OK lc g v x nc off → FVar57 lc g v nc off
  | temp {x : AuxRef} {off : Int} : FrameVarOK lc g v x off → FVar57 lc g v .AUTO off

theorem fvar57?_spec {lc : LocCtx} {g : G2In} {v : Value} {nc : AddrName} {off : Int}
    (h : fvar57? lc g v = some (nc, off)) : FVar57 lc g v nc off := by
  unfold fvar57? at h
  split at h
  · rename_i x nc' off' h49
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .loc (frameVar49?_spec h49)
  · split at h
    · rename_i x off' h6
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .temp (frameVar?_spec h6)
    · cases h

theorem fstpOf_some {op : Op} {n : Nat} (h : fstpOf op = some n) :
    op = .ARM64FSTPD ∧ n = 8 ∨ op = .ARM64FSTPS ∧ n = 4 := by
  unfold fstpOf at h
  repeat' split at h
  all_goals (cases h <;> simp_all)

/-- What `vkind57b` accepted, and what it emits. -/
inductive VK57b (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- `DMB [k] mem`: `DMB $k`. -/
  | dmb : v.op = .ARM64DMB → v.args.size = 1 → memTy (lc.ty v.id) = true → lc.home v.id = none →
      memArg lc v 0 = .ok () → VK57b lc g v (.prog (.ofShape (dmbShape v.auxInt.toInt)))
  /-- `PRFM [k] addr mem`: `PRFM 0(Rn), $k`, `Rn` the register of `addr`. -/
  | prfm {c : Nat} {rn : Int} : v.op = .ARM64PRFM → v.args.size = 2 →
      memTy (lc.ty v.id) = true → lc.home v.id = none → argObj lc v 0 = .ok (c, rn) →
      memArg lc v 1 = .ok () → VK57b lc g v (.prog (.ofShape (prfmShape rn v.auxInt.toInt)))
  /-- `FMOVSstore`/`FMOVDstore` of a frame variable: `FMOVS`/`FMOVD Fs, off(<nc>)`. -/
  | store {nc : AddrName} {off : Int} {rs : Int} : FVar57 lc g v nc off →
      (v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore) → v.args.size = 3 →
      memTy (lc.ty v.id) = true → lc.home v.id = none →
      fargObj lc v 1 = .ok (8 * fBytes v.op, rs) → memArg lc v 2 = .ok () →
      VK57b lc g v (.prog ⟨plain (fmovAs (8 * fBytes v.op)) (· == regA rs) (slotA · nc off),
        (fmovAs (8 * fBytes v.op)).name⟩)
  /-- `FSTPS`/`FSTPD` of `n`-byte elements to a frame variable: `FSTPS`/`FSTPD (Fa, Fb),
  off(<nc>)`. -/
  | stp {n : Nat} {nc : AddrName} {off : Int} {rx ry : Int} : FVar57 lc g v nc off →
      fstpOf v.op = some n → v.args.size = 4 → memTy (lc.ty v.id) = true →
      lc.home v.id = none → fargObj lc v 1 = .ok (8 * n, rx) → fargObj lc v 2 = .ok (8 * n, ry) →
      memArg lc v 3 = .ok () →
      VK57b lc g v (.prog ⟨plain (fstpAs n) (· == pairA rx ry) (slotA · nc off), (fstpAs n).name⟩)

section Helpers

variable {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}

private theorem dmb57_spec (hop : v.op = .ARM64DMB) (h : dmb57 lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK57b lc g v kd := by
  unfold dmb57 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz
  obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
  exact ⟨ht, .dmb hop hsz hmt hhn hma⟩

private theorem prfm57_spec (hop : v.op = .ARM64PRFM) (h : prfm57 lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK57b lc g v kd := by
  unfold prfm57 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨c, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz
  obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
  exact ⟨ht, .prfm hop hsz hmt hhn hao hma⟩

private theorem store57_spec {nc : AddrName} {off : Int} (hfv : FVar57 lc g v nc off)
    (hop : v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore)
    (h : fvarStore57 lc v nc off = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK57b lc g v kd := by
  unfold fvarStore57 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨cs, rs⟩, hso, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw
  obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
  subst hw
  exact ⟨ht, .store hfv hop hsz hmt hhn hso hma⟩

private theorem stp57_spec {n : Nat} {nc : AddrName} {off : Int} (hfv : FVar57 lc g v nc off)
    (hop : fstpOf v.op = some n) (h : fvarStp57 lc v n nc off = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK57b lc g v kd := by
  unfold fvarStp57 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨cx, rx⟩, hxo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cy, ry⟩, hyo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw
  obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨ht, .stp hfv hop hsz hmt hhn hxo hyo hma⟩

end Helpers

/-- What `vkind57b` accepted: no temporary, and `VK57b`. -/
theorem vkind57b_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind57b lc g v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK57b lc g v kd := by
  unfold vkind57b at h
  by_cases h1 : v.op = .ARM64DMB
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h
    exact dmb57_spec h1 h
  simp only [h1, ↓reduceIte] at h
  by_cases h2 : v.op = .ARM64PRFM
  · simp only [h2, ↓reduceIte, Option.some.injEq, reduceCtorEq] at h
    exact prfm57_spec h2 h
  simp only [h2, ↓reduceIte] at h
  by_cases h3 : v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore
  · simp only [h3, ↓reduceIte] at h
    cases hf : fvar57? lc g v with
    | none => simp only [hf, Option.map_none, reduceCtorEq] at h
    | some p =>
      obtain ⟨nc, off⟩ := p
      simp only [hf, Option.map_some, Option.some.injEq] at h
      exact store57_spec (fvar57?_spec hf) h3 h
  simp only [h3, ↓reduceIte] at h
  cases hn : fstpOf v.op with
  | none => simp only [hn, reduceCtorEq] at h
  | some n =>
    cases hf : fvar57? lc g v with
    | none => simp only [hn, hf, Option.map_none, reduceCtorEq] at h
    | some p =>
      obtain ⟨nc, off⟩ := p
      simp only [hn, hf, Option.map_some, Option.some.injEq] at h
      exact stp57_spec (fvar57?_spec hf) hn h

/-- Off the ops of G57's group B, `vkind57b` is `none`. -/
theorem vkind57b_none {lc : LocCtx} {g : G2In} {v : Value} (h : op57b v.op = false) :
    vkind57b lc g v = none := by
  simp only [op57b, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have h34 : ¬ (v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore) := by
    rintro (h | h) <;> contradiction
  simp only [vkind57b, h1, h2, h34, h5, ↓reduceIte]

/-- A value `VK57b` accepted has an op of G57's group B. -/
theorem vk57b_op {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK57b lc g v kd) :
    op57b v.op = true := by
  cases h with
  | dmb hop => simp [op57b, hop]
  | prfm hop => simp [op57b, hop]
  | store _ hop => rcases hop with hop | hop <;> simp [op57b, hop]
  | stp _ hop => simp [op57b, hop]

end GoFV.Gen.Check
