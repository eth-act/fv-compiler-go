import GoFV.Proof.Gen.Rel

variable [GoFV.SSA.Sem.Addrs]

/-!
# `runLoc` on the values of slice G1 (`docs/plans/proofs3.md` §3)

What `stepLoc` does for each op the genssa validator accepts: the arguments read from their
homes at their shapes (`read_reg`), the op's result (`Arm64.evalPure`, Phase 1's `evalPure` for
`Copy`), no clobber, the result written to its home at its shape.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

variable {lc : LocCtx} {s : LocState}

/-- A lowered function reads values as registers. -/
theorem lmode_retype {f : Func} (hl : f.lowered = true) (t : Ty) (v : Val) :
    (LMode.loc f).retype t v = v.retypeL t := by
  simp [LMode.loc, LMode.sched, LMode.retype, hl]

/-- A value with a register home, read at its shape. -/
theorem read_reg {a r c : Nat} (hl : lc.ctx.f.lowered = true) (hh : lc.home a = some (.reg r))
    (hc : cls (lc.ty a) = some c) :
    s.read lc a = .ok ((s.reg (lc.ty a) r).retypeL (lc.ty a)) := by
  have hraw : s.raw lc a = .ok (s.reg (lc.ty a) r) := by
    unfold LocState.raw
    cases ht : lc.ty a <;> simp_all [cls]
  unfold LocState.read
  rw [hraw]; simp only [lmode_retype hl]
  rfl

/-- The memory argument: no home, shape `mem`. -/
theorem read_mem {a : Nat} (hl : lc.ctx.f.lowered = true) (hh : lc.home a = none)
    (ht : memTy (lc.ty a) = true) {mm : Mem} (hm : s.mem = .mem mm) :
    s.read lc a = .ok (.mem mm) := by
  have ht' : lc.ty a = .mem := by cases h : lc.ty a <;> simp_all [memTy]
  have hraw : s.raw lc a = .ok s.mem := by
    unfold LocState.raw
    rw [hh, ht']
  unfold LocState.read
  rw [hraw, hm]; simp only [lmode_retype hl, ht']
  rfl

/-- The flags: no home, the flags shape. -/
theorem read_flags {a : Nat} (hl : lc.ctx.f.lowered = true) (hh : lc.home a = none)
    (ht : (lc.ty a).isFlags = true) :
    s.read lc a = .ok (s.flags.retypeL (lc.ty a)) := by
  have hraw : s.raw lc a = .ok s.flags := by
    unfold LocState.raw
    cases h : lc.ty a <;> simp_all [Ty.isFlags]
  unfold LocState.read
  rw [hraw]; simp only [lmode_retype hl]
  rfl

/-- Writing a value with a register home: `setReg`. -/
theorem write_reg {r c : Nat} {id : ID} {x : Val} (hh : lc.home id = some (.reg r))
    (hc : cls (lc.ty id) = some c) : s.write lc id x = s.setReg r x := by
  unfold LocState.write
  cases ht : lc.ty id <;> simp_all [cls]

/-- Writing a value of the flags shape without a home: the flags register. -/
theorem write_flags {id : ID} {x : Val} (hh : lc.home id = none) (ht : (lc.ty id).isFlags = true) :
    s.write lc id x = { s with flags := x } := by
  unfold LocState.write
  cases h : lc.ty id <;> simp_all [Ty.isFlags]

/-- Writing a value of shape `mem` without a home: the memory. -/
theorem write_mem {id : ID} {x : Val} (hh : lc.home id = none) (ht : memTy (lc.ty id) = true) :
    s.write lc id x = { s with mem := x } := by
  have ht' : lc.ty id = .mem := by cases h : lc.ty id <;> simp_all [memTy]
  simp [LocState.write, hh, ht']

/-- An op that clobbers nothing (no register in `regInfo.clobbers`, no clobbered argument, no
temporary, flags kept) leaves the state alone. -/
theorem clobber_none {v : Value} (hc : v.op.regInfo.clobbers.isEmpty = true)
    (h0 : v.op.regInfo.clobbersArg0 = false) (h1 : v.op.regInfo.clobbersArg1 = false)
    (ht : (lc.temps[v.id]?).join = none) (hf : v.op.clobberFlags = false) :
    s.clobber lc v = s := by
  simp [LocState.clobber, LocState.clobberMask, hc, h0, h1, ht, hf]

end GoFV.Proof.Gen
