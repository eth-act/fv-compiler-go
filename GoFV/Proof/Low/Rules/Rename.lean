import GoFV.Proof.Low.Rules.Kit
import GoFV.Rules.Generated.ARM64

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lowering rule lemmas: atom renames, atomics and `MemEq` (`ARM64.rules:376-377`, `438-439`, `442-458`, `482-490`, `492-504`, `507`, `512-516`)

`ArmRule.Rename` of the ellipsis rules renaming an atom (`renameOp`): calls, tail calls, nil
checks, the closure pointer, the bounds panic and the atomics (`atomicRen`: an arm64 atomic
runs as the generic atomic it is on its operands fitted to the location, `Sem.atomicArgs`, and
`STLR` stores what `AtomicStorePtrNoWB` stores); the
rules folding a constant operand into a lowered bounds panic (`ArmRule.Mem`, `pbAtom`) and
lowering a `Zero` to `LoweredZero` or `LoweredZeroLoop` or a `Move` to `LoweredMove` or
`LoweredMoveLoop` (`ArmRule.Mem`).
`ArmRule.SetOp` of the write barrier (`WB` and `LoweredWB` are terms, both `wbOp`) and of the
atomic loads and `MemEq`: `AtomicLoad{8,32,64,Ptr}` and the acquiring loads `LDAR{B,W,}` they
lower to are terms (`pureActOp`), both Phase 1's `atomicLoad`, and so are `MemEq` and
`LoweredMemEq`, both `memEq` (`setOpSound_pureAct`).
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

/-- `ARM64.rules:456`: `(GetCallerSP ...) => (LoweredGetCallerSP ...)` -/
theorem r_ARM64_456_sound : ArmRule.Checked r_ARM64_456 :=
  checked_rename .GetCallerSP .ARM64LoweredGetCallerSP rfl rfl rfl rfl rfl

/-- A generic term op `o` lowered to an activation op `o'` that `Sem.arm64Op` runs as its
`Arm64.evalPure` (`pureActOp`) with the same value: an atomic load and its acquiring load (both
`atomicLoad`), `MemEq` and `LoweredMemEq` (both `memEq`). -/
private theorem setOpSound_pureAct {o o' : Op} (hg : o.generic = true) (hf : frameOp o = false)
    (hd : pureActOp o' = true)
    (he : ∀ ty ai ax args, evalPure o ty ai ax args = Arm64.evalPure o' ty ai ax args) :
    SetOpSound o o' := by
  intro tabs ty ai ax args _
  have hg' : o'.generic = false := by rcases pureActOp_cases hd with rfl | rfl | rfl | rfl <;> rfl
  have hm : (o' == .ARM64MOVDaddr) = false := by
    rcases pureActOp_cases hd with rfl | rfl | rfl | rfl <;> rfl
  rw [opValL_gen hg hf, opValL_arm hg' hm (ldOp?_of_pureAct hd), he]
  exact Refines.refl _

/-- `ARM64.rules:482`: `(AtomicLoad8 ...) => (LDARB ...)` -/
theorem r_ARM64_482_sound : ArmRule.Checked r_ARM64_482 :=
  checked_setOp .AtomicLoad8 .ARM64LDARB rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_pureAct _ rfl) (setOpSound_pureAct rfl rfl rfl fun _ _ _ _ => rfl)

/-- `ARM64.rules:483`: `(AtomicLoad32 ...) => (LDARW ...)` -/
theorem r_ARM64_483_sound : ArmRule.Checked r_ARM64_483 :=
  checked_setOp .AtomicLoad32 .ARM64LDARW rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_pureAct _ rfl) (setOpSound_pureAct rfl rfl rfl fun _ _ _ _ => rfl)

/-- `ARM64.rules:484`: `(AtomicLoad64 ...) => (LDAR ...)` -/
theorem r_ARM64_484_sound : ArmRule.Checked r_ARM64_484 :=
  checked_setOp .AtomicLoad64 .ARM64LDAR rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_pureAct _ rfl) (setOpSound_pureAct rfl rfl rfl fun _ _ _ _ => rfl)

/-- `ARM64.rules:485`: `(AtomicLoadPtr ...) => (LDAR ...)` -/
theorem r_ARM64_485_sound : ArmRule.Checked r_ARM64_485 :=
  checked_setOp .AtomicLoadPtr .ARM64LDAR rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_pureAct _ rfl) (setOpSound_pureAct rfl rfl rfl fun _ _ _ _ => rfl)

/-- `ARM64.rules:458`: `(MemEq ...) => (LoweredMemEq ...)` -/
theorem r_ARM64_458_sound : ArmRule.Checked r_ARM64_458 :=
  checked_setOp .MemEq .ARM64LoweredMemEq rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_pureAct _ rfl) (setOpSound_pureAct rfl rfl rfl fun _ _ _ _ => rfl)

/-- `ARM64.rules:487`: `(AtomicStore8 ...) => (STLRB ...)` -/
theorem r_ARM64_487_sound : ArmRule.Checked r_ARM64_487 :=
  checked_rename .AtomicStore8 .ARM64STLRB rfl rfl rfl rfl rfl

/-- `ARM64.rules:488`: `(AtomicStore32 ...) => (STLRW ...)` -/
theorem r_ARM64_488_sound : ArmRule.Checked r_ARM64_488 :=
  checked_rename .AtomicStore32 .ARM64STLRW rfl rfl rfl rfl rfl

/-- `ARM64.rules:489`: `(AtomicStore64 ...) => (STLR ...)` -/
theorem r_ARM64_489_sound : ArmRule.Checked r_ARM64_489 :=
  checked_rename .AtomicStore64 .ARM64STLR rfl rfl rfl rfl rfl

/-- `ARM64.rules:490`: `(AtomicStorePtrNoWB ...) => (STLR ...)` (`atomicRen`: `STLR` runs as
`AtomicStore64`, which stores a pointer as `AtomicStorePtrNoWB` does,
`GoFV.Proof.Low.Sim.atomicRoot_ptrStore`) -/
theorem r_ARM64_490_sound : ArmRule.Checked r_ARM64_490 :=
  checked_rename .AtomicStorePtrNoWB .ARM64STLR rfl rfl rfl rfl rfl

/-- `ARM64.rules:492`: `(AtomicExchange(8|32|64) ...) => (LoweredAtomicExchange(8|32|64) ...)` -/
theorem r_ARM64_492_sound : ArmRule.Checked r_ARM64_492 :=
  checked_rename .AtomicExchange32 .ARM64LoweredAtomicExchange32 rfl rfl rfl rfl rfl

/-- `ARM64.rules:492`: `(AtomicExchange(8|32|64) ...) => (LoweredAtomicExchange(8|32|64) ...)` -/
theorem r_ARM64_492_2_sound : ArmRule.Checked r_ARM64_492_2 :=
  checked_rename .AtomicExchange64 .ARM64LoweredAtomicExchange64 rfl rfl rfl rfl rfl

/-- `ARM64.rules:492`: `(AtomicExchange(8|32|64) ...) => (LoweredAtomicExchange(8|32|64) ...)` -/
theorem r_ARM64_492_3_sound : ArmRule.Checked r_ARM64_492_3 :=
  checked_rename .AtomicExchange8 .ARM64LoweredAtomicExchange8 rfl rfl rfl rfl rfl

/-- `ARM64.rules:493`: `(AtomicAdd(32|64) ...) => (LoweredAtomicAdd(32|64) ...)` -/
theorem r_ARM64_493_sound : ArmRule.Checked r_ARM64_493 :=
  checked_rename .AtomicAdd32 .ARM64LoweredAtomicAdd32 rfl rfl rfl rfl rfl

/-- `ARM64.rules:493`: `(AtomicAdd(32|64) ...) => (LoweredAtomicAdd(32|64) ...)` -/
theorem r_ARM64_493_2_sound : ArmRule.Checked r_ARM64_493_2 :=
  checked_rename .AtomicAdd64 .ARM64LoweredAtomicAdd64 rfl rfl rfl rfl rfl

/-- `ARM64.rules:494`: `(AtomicCompareAndSwap(32|64) ...) => (LoweredAtomicCas(32|64) ...)` -/
theorem r_ARM64_494_sound : ArmRule.Checked r_ARM64_494 :=
  checked_rename .AtomicCompareAndSwap32 .ARM64LoweredAtomicCas32 rfl rfl rfl rfl rfl

/-- `ARM64.rules:494`: `(AtomicCompareAndSwap(32|64) ...) => (LoweredAtomicCas(32|64) ...)` -/
theorem r_ARM64_494_2_sound : ArmRule.Checked r_ARM64_494_2 :=
  checked_rename .AtomicCompareAndSwap64 .ARM64LoweredAtomicCas64 rfl rfl rfl rfl rfl

/-- `ARM64.rules:496`: `(AtomicAdd(32|64)Variant ...) => (LoweredAtomicAdd(32|64)Variant ...)` -/
theorem r_ARM64_496_sound : ArmRule.Checked r_ARM64_496 :=
  checked_rename .AtomicAdd32Variant .ARM64LoweredAtomicAdd32Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:496`: `(AtomicAdd(32|64)Variant ...) => (LoweredAtomicAdd(32|64)Variant ...)` -/
theorem r_ARM64_496_2_sound : ArmRule.Checked r_ARM64_496_2 :=
  checked_rename .AtomicAdd64Variant .ARM64LoweredAtomicAdd64Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:497`: `(AtomicExchange(8|32|64)Variant ...) => (LoweredAtomicExchange(8|32|64)Variant ...)` -/
theorem r_ARM64_497_sound : ArmRule.Checked r_ARM64_497 :=
  checked_rename .AtomicExchange32Variant .ARM64LoweredAtomicExchange32Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:497`: `(AtomicExchange(8|32|64)Variant ...) => (LoweredAtomicExchange(8|32|64)Variant ...)` -/
theorem r_ARM64_497_2_sound : ArmRule.Checked r_ARM64_497_2 :=
  checked_rename .AtomicExchange64Variant .ARM64LoweredAtomicExchange64Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:497`: `(AtomicExchange(8|32|64)Variant ...) => (LoweredAtomicExchange(8|32|64)Variant ...)` -/
theorem r_ARM64_497_3_sound : ArmRule.Checked r_ARM64_497_3 :=
  checked_rename .AtomicExchange8Variant .ARM64LoweredAtomicExchange8Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:498`: `(AtomicCompareAndSwap(32|64)Variant ...) => (LoweredAtomicCas(32|64)Variant ...)` -/
theorem r_ARM64_498_sound : ArmRule.Checked r_ARM64_498 :=
  checked_rename .AtomicCompareAndSwap32Variant .ARM64LoweredAtomicCas32Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:498`: `(AtomicCompareAndSwap(32|64)Variant ...) => (LoweredAtomicCas(32|64)Variant ...)` -/
theorem r_ARM64_498_2_sound : ArmRule.Checked r_ARM64_498_2 :=
  checked_rename .AtomicCompareAndSwap64Variant .ARM64LoweredAtomicCas64Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:501`: `(AtomicAnd(64|32|8)value ...) => (LoweredAtomicAnd(64|32|8) ...)` -/
theorem r_ARM64_501_sound : ArmRule.Checked r_ARM64_501 :=
  checked_rename .AtomicAnd32value .ARM64LoweredAtomicAnd32 rfl rfl rfl rfl rfl

/-- `ARM64.rules:501`: `(AtomicAnd(64|32|8)value ...) => (LoweredAtomicAnd(64|32|8) ...)` -/
theorem r_ARM64_501_2_sound : ArmRule.Checked r_ARM64_501_2 :=
  checked_rename .AtomicAnd64value .ARM64LoweredAtomicAnd64 rfl rfl rfl rfl rfl

/-- `ARM64.rules:501`: `(AtomicAnd(64|32|8)value ...) => (LoweredAtomicAnd(64|32|8) ...)` -/
theorem r_ARM64_501_3_sound : ArmRule.Checked r_ARM64_501_3 :=
  checked_rename .AtomicAnd8value .ARM64LoweredAtomicAnd8 rfl rfl rfl rfl rfl

/-- `ARM64.rules:502`: `(AtomicOr(64|32|8)value ...) => (LoweredAtomicOr(64|32|8) ...)` -/
theorem r_ARM64_502_sound : ArmRule.Checked r_ARM64_502 :=
  checked_rename .AtomicOr32value .ARM64LoweredAtomicOr32 rfl rfl rfl rfl rfl

/-- `ARM64.rules:502`: `(AtomicOr(64|32|8)value ...) => (LoweredAtomicOr(64|32|8) ...)` -/
theorem r_ARM64_502_2_sound : ArmRule.Checked r_ARM64_502_2 :=
  checked_rename .AtomicOr64value .ARM64LoweredAtomicOr64 rfl rfl rfl rfl rfl

/-- `ARM64.rules:502`: `(AtomicOr(64|32|8)value ...) => (LoweredAtomicOr(64|32|8) ...)` -/
theorem r_ARM64_502_3_sound : ArmRule.Checked r_ARM64_502_3 :=
  checked_rename .AtomicOr8value .ARM64LoweredAtomicOr8 rfl rfl rfl rfl rfl

/-- `ARM64.rules:503`: `(AtomicAnd(64|32|8)valueVariant ...) => (LoweredAtomicAnd(64|32|8)Variant ...)` -/
theorem r_ARM64_503_sound : ArmRule.Checked r_ARM64_503 :=
  checked_rename .AtomicAnd32valueVariant .ARM64LoweredAtomicAnd32Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:503`: `(AtomicAnd(64|32|8)valueVariant ...) => (LoweredAtomicAnd(64|32|8)Variant ...)` -/
theorem r_ARM64_503_2_sound : ArmRule.Checked r_ARM64_503_2 :=
  checked_rename .AtomicAnd64valueVariant .ARM64LoweredAtomicAnd64Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:503`: `(AtomicAnd(64|32|8)valueVariant ...) => (LoweredAtomicAnd(64|32|8)Variant ...)` -/
theorem r_ARM64_503_3_sound : ArmRule.Checked r_ARM64_503_3 :=
  checked_rename .AtomicAnd8valueVariant .ARM64LoweredAtomicAnd8Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:504`: `(AtomicOr(64|32|8)valueVariant ...) => (LoweredAtomicOr(64|32|8)Variant ...)` -/
theorem r_ARM64_504_sound : ArmRule.Checked r_ARM64_504 :=
  checked_rename .AtomicOr32valueVariant .ARM64LoweredAtomicOr32Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:504`: `(AtomicOr(64|32|8)valueVariant ...) => (LoweredAtomicOr(64|32|8)Variant ...)` -/
theorem r_ARM64_504_2_sound : ArmRule.Checked r_ARM64_504_2 :=
  checked_rename .AtomicOr64valueVariant .ARM64LoweredAtomicOr64Variant rfl rfl rfl rfl rfl

/-- `ARM64.rules:504`: `(AtomicOr(64|32|8)valueVariant ...) => (LoweredAtomicOr(64|32|8)Variant ...)` -/
theorem r_ARM64_504_3_sound : ArmRule.Checked r_ARM64_504_3 :=
  checked_rename .AtomicOr8valueVariant .ARM64LoweredAtomicOr8Variant rfl rfl rfl rfl rfl

end GoFV.Proof.Low.Rules
