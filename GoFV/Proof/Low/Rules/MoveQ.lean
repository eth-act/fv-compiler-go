import GoFV.Proof.Low.Rules.Kit
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemmas: `Move [16]`/`Move [32]` to 128-bit stores (`ARM64.rules:418`, `426`, `779`, `782`, `909`, `913`)

`(Move [16] dst src mem) => (FMOVQstore dst (FMOVQload src mem) mem)` and `(Move [32] dst src
mem) => (FSTPQ dst (Select0 (FLDPQ src mem)) (Select1 (FLDPQ src mem)) mem)`: the validator
replays the event as the 128-bit store at the `Move` and fresh load terms of its source
(`LowerCheck.moveDef`) and pairs the store with the `Move` (`moveQLower`,
`GoFV.Proof.Low.Sim.moveQ_lower_eval`), so these are rules on a `Move` (`ArmRule.Mem`,
`checked_move`). The offsets and symbols or frame variables folded into the 128-bit stores
(`779`, `782`, `909`, `913`) are replayed as the store's new definition (`LowerCheck.qFold`, its
address related by `AddrRef` as an arm64 store's), rules on a `qStore` (`checked_qStore`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- `ARM64.rules:418`: `(Move [16] dst src mem) => (FMOVQstore dst (FMOVQload src mem) mem)` -/
theorem r_ARM64_418_sound : ArmRule.Checked r_ARM64_418 := checked_move rfl

/-- `ARM64.rules:426`: `(Move [32] dst src mem) => (FSTPQ dst (Select0 <typ.Vec128> (FLDPQ src mem)) (Select1 <typ.Vec128> (FLDPQ src mem)) mem)` -/
theorem r_ARM64_426_sound : ArmRule.Checked r_ARM64_426 := checked_move rfl

/-- `ARM64.rules:779`: `(FMOVQstore [off1] {sym} (ADDconst [off2] ptr) val mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (FMOVQstore [off1+int32(off2)] {sym} ptr val mem)` -/
theorem r_ARM64_779_sound : ArmRule.Checked r_ARM64_779 := checked_qStore rfl rfl

/-- `ARM64.rules:782`: `(FSTPQ [off1] {sym} (ADDconst [off2] ptr) val1 val2 mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (FSTPQ [off1+int32(off2)] {sym} ptr val1 val2 mem)` -/
theorem r_ARM64_782_sound : ArmRule.Checked r_ARM64_782 := checked_qStore rfl rfl

/-- `ARM64.rules:909`: `(FMOVQstore [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (FMOVQstore [off1+off2] {mergeSym(sym1,sym2)} ptr val mem)` -/
theorem r_ARM64_909_sound : ArmRule.Checked r_ARM64_909 := checked_qStore rfl rfl

/-- `ARM64.rules:913`: `(FSTPQ [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val1 val2 mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (FSTPQ [off1+off2] {mergeSym(sym1,sym2)} ptr val1 val2 mem)` -/
theorem r_ARM64_913_sound : ArmRule.Checked r_ARM64_913 := checked_qStore rfl rfl

end GoFV.Proof.Low.Rules
