import GoFV.Proof.Gen.Loc
import GoFV.SSA.Sem.Arm64.Mem

/-!
# `stepLoc` on each op of slice G1 (`docs/plans/proofs3.md` §3)

What a successful `stepLoc` does for each op the genssa validator accepts, in a lowered function
(`Val.retypeL`) for a value with no temporary register (so `LocState.clobber` changes nothing):
the arguments read from their homes (`LocState.read`), the op's result (`Arm64.evalPure` for the
pure arm64 ops, Phase 1's `Copy`/`MakeResult`, `arm64Op`'s 8-byte load and store), written to the
value's home at its shape.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- A phi whose arguments share its home does nothing. -/
theorem stepLoc_phi (hop : v.op = .Phi) (h : stepLoc env lc s v = .ok s') : s' = s := by
  sorry

/-- The pure arm64 ops of G1: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_pure (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64ZERO ∨ v.op = .ARM64MOVDconst ∨ v.op = .ARM64ADD ∨ v.op = .ARM64SUB ∨
      v.op = .ARM64ADDconst ∨ v.op = .ARM64SUBconst ∨ v.op = .ARM64CMP ∨ v.op = .ARM64CMPconst)
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL (lc.ty v.id)) := by
  sorry

/-- `Copy` of one argument: the argument at the value's shape. -/
theorem stepLoc_copy (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .Copy) {a : ID} (ha : v.args = #[a]) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a = .ok x ∧ s' = s.write lc v.id (x.retypeL (lc.ty v.id)) := by
  sorry

/-- `MakeResult`: the tuple of its arguments at the value's shape. -/
theorem stepLoc_makeResult (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .MakeResult) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Val.tuple argv).retypeL (lc.ty v.id)) := by
  sorry

/-- An inline mark with no home and a shape `write` drops changes nothing. -/
theorem stepLoc_inlMark (ht : (lc.temps[v.id]?).join = none) (hop : v.op = .InlMark)
    (hh : lc.home v.id = none) (hi : inertTy (lc.ty v.id) = true)
    (h : stepLoc env lc s v = .ok s') : s' = s := by
  sorry

/-- `MOVDload [off] a mem` without a symbol: the 8-byte load at `a + off` (`poison` if `a` is not
an address). -/
theorem stepLoc_load (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64MOVDload) {a0 a1 : ID} (ha : v.args = #[a0, a1]) (haux : v.aux = none)
    {mm : Mem} (hm : s.read lc a1 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id
        (((Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt)).elim .poison
          (Arm64.loadN (lc.ty v.id) 8 false mm)).retypeL (lc.ty v.id)) := by
  sorry

/-- `MOVDstore [off] a x mem` without a symbol: the 8-byte store of `x` at `a + off`, which
succeeded. -/
theorem stepLoc_store (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64MOVDstore) {a0 a1 a2 : ID} (ha : v.args = #[a0, a1, a2])
    (haux : v.aux = none) {mm : Mem} (hm : s.read lc a2 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x y p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧
      Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p ∧
      mm.write p (Arm64.storeBytes 8 y) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  sorry

end GoFV.Proof.Gen
