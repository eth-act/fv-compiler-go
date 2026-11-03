import GoFV.Proof.Low.Rules.Tactic
import GoFV.Rules.Generated.ARM64.Blocks

/-!
# Lowering block rule lemmas: conditional blocks on a `CSET` (`ARM64.rules:461-554`)

`BlockRuleL.Sound` of `(If cond)` → `(TBNZ [0] cond)` and of the rules branching directly on the
flags a `CSET` pseudo-op (`Equal`, `LessThanU`, …) reads: `If`, `NZ` and `TBNZ [0]` on
`(X cc)` take the edge `X`'s condition gives on `cc`, which is the new flags kind's
(`if_cset`, `nz_cset`, `tbnz_cset`, `brVal_cond`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- `ARM64.rules:476`: `(If cond yes no) => (TBNZ [0] cond yes no)` -/
theorem r_ARM64_476_sound : BlockRuleL.Sound r_ARM64_476 := by
  arm_bunfold
  rw [Bool.bne_false]
  exact tbnz_of_if rfl hbr

/-- `ARM64.rules:461`: `(If (Equal cc) yes no) => (EQ cc yes no)` -/
theorem r_ARM64_461_sound : BlockRuleL.Sound r_ARM64_461 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:462`: `(If (NotEqual cc) yes no) => (NE cc yes no)` -/
theorem r_ARM64_462_sound : BlockRuleL.Sound r_ARM64_462 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:463`: `(If (LessThan cc) yes no) => (LT cc yes no)` -/
theorem r_ARM64_463_sound : BlockRuleL.Sound r_ARM64_463 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:464`: `(If (LessThanU cc) yes no) => (ULT cc yes no)` -/
theorem r_ARM64_464_sound : BlockRuleL.Sound r_ARM64_464 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:465`: `(If (LessEqual cc) yes no) => (LE cc yes no)` -/
theorem r_ARM64_465_sound : BlockRuleL.Sound r_ARM64_465 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:466`: `(If (LessEqualU cc) yes no) => (ULE cc yes no)` -/
theorem r_ARM64_466_sound : BlockRuleL.Sound r_ARM64_466 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:467`: `(If (GreaterThan cc) yes no) => (GT cc yes no)` -/
theorem r_ARM64_467_sound : BlockRuleL.Sound r_ARM64_467 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:468`: `(If (GreaterThanU cc) yes no) => (UGT cc yes no)` -/
theorem r_ARM64_468_sound : BlockRuleL.Sound r_ARM64_468 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:469`: `(If (GreaterEqual cc) yes no) => (GE cc yes no)` -/
theorem r_ARM64_469_sound : BlockRuleL.Sound r_ARM64_469 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:470`: `(If (GreaterEqualU cc) yes no) => (UGE cc yes no)` -/
theorem r_ARM64_470_sound : BlockRuleL.Sound r_ARM64_470 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:471`: `(If (LessThanF cc) yes no) => (FLT cc yes no)` -/
theorem r_ARM64_471_sound : BlockRuleL.Sound r_ARM64_471 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:472`: `(If (LessEqualF cc) yes no) => (FLE cc yes no)` -/
theorem r_ARM64_472_sound : BlockRuleL.Sound r_ARM64_472 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:473`: `(If (GreaterThanF cc) yes no) => (FGT cc yes no)` -/
theorem r_ARM64_473_sound : BlockRuleL.Sound r_ARM64_473 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:474`: `(If (GreaterEqualF cc) yes no) => (FGE cc yes no)` -/
theorem r_ARM64_474_sound : BlockRuleL.Sound r_ARM64_474 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (if_cset hbr)

/-- `ARM64.rules:526`: `(NZ (Equal cc) yes no) => (EQ cc yes no)` -/
theorem r_ARM64_526_sound : BlockRuleL.Sound r_ARM64_526 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:527`: `(NZ (NotEqual cc) yes no) => (NE cc yes no)` -/
theorem r_ARM64_527_sound : BlockRuleL.Sound r_ARM64_527 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:528`: `(NZ (LessThan cc) yes no) => (LT cc yes no)` -/
theorem r_ARM64_528_sound : BlockRuleL.Sound r_ARM64_528 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:529`: `(NZ (LessThanU cc) yes no) => (ULT cc yes no)` -/
theorem r_ARM64_529_sound : BlockRuleL.Sound r_ARM64_529 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:530`: `(NZ (LessEqual cc) yes no) => (LE cc yes no)` -/
theorem r_ARM64_530_sound : BlockRuleL.Sound r_ARM64_530 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:531`: `(NZ (LessEqualU cc) yes no) => (ULE cc yes no)` -/
theorem r_ARM64_531_sound : BlockRuleL.Sound r_ARM64_531 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:532`: `(NZ (GreaterThan cc) yes no) => (GT cc yes no)` -/
theorem r_ARM64_532_sound : BlockRuleL.Sound r_ARM64_532 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:533`: `(NZ (GreaterThanU cc) yes no) => (UGT cc yes no)` -/
theorem r_ARM64_533_sound : BlockRuleL.Sound r_ARM64_533 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:534`: `(NZ (GreaterEqual cc) yes no) => (GE cc yes no)` -/
theorem r_ARM64_534_sound : BlockRuleL.Sound r_ARM64_534 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:535`: `(NZ (GreaterEqualU cc) yes no) => (UGE cc yes no)` -/
theorem r_ARM64_535_sound : BlockRuleL.Sound r_ARM64_535 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:536`: `(NZ (LessThanF cc) yes no) => (FLT cc yes no)` -/
theorem r_ARM64_536_sound : BlockRuleL.Sound r_ARM64_536 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:537`: `(NZ (LessEqualF cc) yes no) => (FLE cc yes no)` -/
theorem r_ARM64_537_sound : BlockRuleL.Sound r_ARM64_537 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:538`: `(NZ (GreaterThanF cc) yes no) => (FGT cc yes no)` -/
theorem r_ARM64_538_sound : BlockRuleL.Sound r_ARM64_538 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:539`: `(NZ (GreaterEqualF cc) yes no) => (FGE cc yes no)` -/
theorem r_ARM64_539_sound : BlockRuleL.Sound r_ARM64_539 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (nz_cset hbr)

/-- `ARM64.rules:541`: `(TBNZ [0] (Equal cc) yes no) => (EQ cc yes no)` -/
theorem r_ARM64_541_sound : BlockRuleL.Sound r_ARM64_541 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:542`: `(TBNZ [0] (NotEqual cc) yes no) => (NE cc yes no)` -/
theorem r_ARM64_542_sound : BlockRuleL.Sound r_ARM64_542 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:543`: `(TBNZ [0] (LessThan cc) yes no) => (LT cc yes no)` -/
theorem r_ARM64_543_sound : BlockRuleL.Sound r_ARM64_543 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:544`: `(TBNZ [0] (LessThanU cc) yes no) => (ULT cc yes no)` -/
theorem r_ARM64_544_sound : BlockRuleL.Sound r_ARM64_544 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:545`: `(TBNZ [0] (LessEqual cc) yes no) => (LE cc yes no)` -/
theorem r_ARM64_545_sound : BlockRuleL.Sound r_ARM64_545 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:546`: `(TBNZ [0] (LessEqualU cc) yes no) => (ULE cc yes no)` -/
theorem r_ARM64_546_sound : BlockRuleL.Sound r_ARM64_546 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:547`: `(TBNZ [0] (GreaterThan cc) yes no) => (GT cc yes no)` -/
theorem r_ARM64_547_sound : BlockRuleL.Sound r_ARM64_547 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:548`: `(TBNZ [0] (GreaterThanU cc) yes no) => (UGT cc yes no)` -/
theorem r_ARM64_548_sound : BlockRuleL.Sound r_ARM64_548 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:549`: `(TBNZ [0] (GreaterEqual cc) yes no) => (GE cc yes no)` -/
theorem r_ARM64_549_sound : BlockRuleL.Sound r_ARM64_549 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:550`: `(TBNZ [0] (GreaterEqualU cc) yes no) => (UGE cc yes no)` -/
theorem r_ARM64_550_sound : BlockRuleL.Sound r_ARM64_550 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:551`: `(TBNZ [0] (LessThanF cc) yes no) => (FLT cc yes no)` -/
theorem r_ARM64_551_sound : BlockRuleL.Sound r_ARM64_551 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:552`: `(TBNZ [0] (LessEqualF cc) yes no) => (FLE cc yes no)` -/
theorem r_ARM64_552_sound : BlockRuleL.Sound r_ARM64_552 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:553`: `(TBNZ [0] (GreaterThanF cc) yes no) => (FGT cc yes no)` -/
theorem r_ARM64_553_sound : BlockRuleL.Sound r_ARM64_553 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

/-- `ARM64.rules:554`: `(TBNZ [0] (GreaterEqualF cc) yes no) => (FGE cc yes no)` -/
theorem r_ARM64_554_sound : BlockRuleL.Sound r_ARM64_554 := by
  arm_bunfold
  arm_norm
  exact brVal_cond _ (fun _ _ => rfl) (tbnz_cset hb hbr)

end GoFV.Proof.Low.Rules
