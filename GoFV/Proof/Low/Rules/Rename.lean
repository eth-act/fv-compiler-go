import GoFV.Proof.Low.Rules.Kit
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemmas: atom renames and atomic loads (`ARM64.rules:376-377`, `438-439`, `442-455`, `482-485`, `507`, `512-516`)

`ArmRule.Rename` of the ellipsis rules renaming an atom (`renameOp`): calls, tail calls, nil
checks, the closure pointer and the bounds panic; the rules folding a constant operand into a
lowered bounds panic (`ArmRule.Mem`, `pbAtom`) and lowering a `Zero` to `LoweredZero` or
`LoweredZeroLoop` or a `Move` to `LoweredMove` or `LoweredMoveLoop` (`ArmRule.Mem`).
`ArmRule.SetOp` of the write barrier (`WB` and `LoweredWB` are terms, both `wbOp`) and of the
atomic loads: `AtomicLoad{8,32,64,Ptr}` and the acquiring loads `LDAR{B,W,}` they lower to are
terms (`ldarOp`), both Phase 1's `atomicLoad` (`armPure_ldar`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low GoFV.Opt.LowerTerm
open GoFV.Rules.Generated.ARM64

/-- `ARM64.rules:507`: `(WB ...) => (LoweredWB ...)` -/
theorem r_ARM64_507_sound : ArmRule.Checked r_ARM64_507 :=
  checked_setOp .WB .ARM64LoweredWB rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_arm _ rfl rfl rfl) fun tabs ty ai ax args _ => by
      rw [opValL_gen rfl rfl, opValL_arm rfl rfl rfl]
      exact Refines.refl _

/-- `ARM64.rules:512`: `(PanicBounds ...) => (LoweredPanicBoundsRR ...)` -/
theorem r_ARM64_512_sound : ArmRule.Checked r_ARM64_512 :=
  checked_rename .PanicBounds .ARM64LoweredPanicBoundsRR rfl rfl rfl rfl rfl

/-- `ARM64.rules:513`: `(LoweredPanicBoundsRR [kind] x (MOVDconst [c]) mem) =>
(LoweredPanicBoundsRC [kind] x {PanicBoundsC{C:c}} mem)`, a rule on a lowered bounds panic
(`pbAtom`; the validator checks its result, `GoFV.Opt.LowerCheck.pbFoldEv`). -/
theorem r_ARM64_513_sound : ArmRule.Checked r_ARM64_513 := checked_pb rfl rfl

/-- `ARM64.rules:514`: `(LoweredPanicBoundsRR [kind] (MOVDconst [c]) y mem) =>
(LoweredPanicBoundsCR [kind] {PanicBoundsC{C:c}} y mem)` (`pbAtom`). -/
theorem r_ARM64_514_sound : ArmRule.Checked r_ARM64_514 := checked_pb rfl rfl

/-- `ARM64.rules:515`: `(LoweredPanicBoundsRC [kind] {p} (MOVDconst [c]) mem) =>
(LoweredPanicBoundsCC [kind] {PanicBoundsCC{Cx:c, Cy:p.C}} mem)` (`pbAtom`). -/
theorem r_ARM64_515_sound : ArmRule.Checked r_ARM64_515 := checked_pb rfl rfl

/-- `ARM64.rules:516`: `(LoweredPanicBoundsCR [kind] {p} (MOVDconst [c]) mem) =>
(LoweredPanicBoundsCC [kind] {PanicBoundsCC{Cx:p.C, Cy:c}} mem)` (`pbAtom`). -/
theorem r_ARM64_516_sound : ArmRule.Checked r_ARM64_516 := checked_pb rfl rfl

/-- `ARM64.rules:376`: `(Zero [s] ptr mem) && s > 16 && s < 192 => (LoweredZero [s] ptr mem)`, a rule
on a `Zero` (`ArmRule.Mem`; the validator pairs the result with the `Zero`, `bulkLower`). -/
theorem r_ARM64_376_sound : ArmRule.Checked r_ARM64_376 := checked_zero rfl

/-- `ARM64.rules:377`: `(Zero [s] ptr mem) && s >= 192 => (LoweredZeroLoop [s] ptr mem)`
(`ArmRule.Mem`, `bulkLower`). -/
theorem r_ARM64_377_sound : ArmRule.Checked r_ARM64_377 := checked_zero rfl

/-- `ARM64.rules:438`: `(Move [s] dst src mem) && s > 64 && s < 192 && logLargeCopy(v, s) =>
(LoweredMove [s] dst src mem)`, a rule on a `Move` (`ArmRule.Mem`; the validator pairs the result
with the `Move`, `bulkLower`). -/
theorem r_ARM64_438_sound : ArmRule.Checked r_ARM64_438 := checked_move rfl

/-- `ARM64.rules:439`: `(Move [s] dst src mem) && s >= 192 && logLargeCopy(v, s) =>
(LoweredMoveLoop [s] dst src mem)` (`ArmRule.Mem`, `bulkLower`). -/
theorem r_ARM64_439_sound : ArmRule.Checked r_ARM64_439 := checked_move rfl

/-- `ARM64.rules:442`: `(StaticCall ...) => (CALLstatic ...)` -/
theorem r_ARM64_442_sound : ArmRule.Checked r_ARM64_442 :=
  checked_rename .StaticCall .ARM64CALLstatic rfl rfl rfl rfl rfl

/-- `ARM64.rules:443`: `(ClosureCall ...) => (CALLclosure ...)` -/
theorem r_ARM64_443_sound : ArmRule.Checked r_ARM64_443 :=
  checked_rename .ClosureCall .ARM64CALLclosure rfl rfl rfl rfl rfl

/-- `ARM64.rules:444`: `(InterCall ...) => (CALLinter ...)` -/
theorem r_ARM64_444_sound : ArmRule.Checked r_ARM64_444 :=
  checked_rename .InterCall .ARM64CALLinter rfl rfl rfl rfl rfl

/-- `ARM64.rules:445`: `(TailCall ...) => (CALLtail ...)` -/
theorem r_ARM64_445_sound : ArmRule.Checked r_ARM64_445 :=
  checked_rename .TailCall .ARM64CALLtail rfl rfl rfl rfl rfl

/-- `ARM64.rules:446`: `(TailCallInter ...) => (CALLtailinter ...)` -/
theorem r_ARM64_446_sound : ArmRule.Checked r_ARM64_446 :=
  checked_rename .TailCallInter .ARM64CALLtailinter rfl rfl rfl rfl rfl

/-- `ARM64.rules:449`: `(NilCheck ...) => (LoweredNilCheck ...)` -/
theorem r_ARM64_449_sound : ArmRule.Checked r_ARM64_449 :=
  checked_rename .NilCheck .ARM64LoweredNilCheck rfl rfl rfl rfl rfl

/-- `ARM64.rules:455`: `(GetClosurePtr ...) => (LoweredGetClosurePtr ...)` -/
theorem r_ARM64_455_sound : ArmRule.Checked r_ARM64_455 :=
  checked_rename .GetClosurePtr .ARM64LoweredGetClosurePtr rfl rfl rfl rfl rfl

/-- An atomic load `o` lowered to an acquiring load `o'`: both `atomicLoad`. -/
private theorem setOpSound_ldar {o o' : Op} (hg : o.generic = true) (hf : frameOp o = false)
    (hd : ldarOp o' = true) (he : ∀ ty ai ax args, evalPure o ty ai ax args = atomicLoad ty args) :
    SetOpSound o o' := by
  intro tabs ty ai ax args _
  have hg' : o'.generic = false := by rcases ldarOp_cases hd with rfl | rfl | rfl <;> rfl
  have hm : (o' == .ARM64MOVDaddr) = false := by rcases ldarOp_cases hd with rfl | rfl | rfl <;> rfl
  rw [opValL_gen hg hf, opValL_arm hg' hm (ldOp?_of_ldar hd), armPure_ldar hd, he]
  exact Refines.refl _

/-- `ARM64.rules:482`: `(AtomicLoad8 ...) => (LDARB ...)` -/
theorem r_ARM64_482_sound : ArmRule.Checked r_ARM64_482 :=
  checked_setOp .AtomicLoad8 .ARM64LDARB rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_ldar _ rfl) (setOpSound_ldar rfl rfl rfl fun _ _ _ _ => rfl)

/-- `ARM64.rules:483`: `(AtomicLoad32 ...) => (LDARW ...)` -/
theorem r_ARM64_483_sound : ArmRule.Checked r_ARM64_483 :=
  checked_setOp .AtomicLoad32 .ARM64LDARW rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_ldar _ rfl) (setOpSound_ldar rfl rfl rfl fun _ _ _ _ => rfl)

/-- `ARM64.rules:484`: `(AtomicLoad64 ...) => (LDAR ...)` -/
theorem r_ARM64_484_sound : ArmRule.Checked r_ARM64_484 :=
  checked_setOp .AtomicLoad64 .ARM64LDAR rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_ldar _ rfl) (setOpSound_ldar rfl rfl rfl fun _ _ _ _ => rfl)

/-- `ARM64.rules:485`: `(AtomicLoadPtr ...) => (LDAR ...)` -/
theorem r_ARM64_485_sound : ArmRule.Checked r_ARM64_485 :=
  checked_setOp .AtomicLoadPtr .ARM64LDAR rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_ldar _ rfl) (setOpSound_ldar rfl rfl rfl fun _ _ _ _ => rfl)

end GoFV.Proof.Low.Rules
