import GoFV.Proof.Low.Rules.Kit
import GoFV.Rules.Generated.ARM64

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lowering rule lemmas: `Zero [n]` to stores of `0` (`ARM64.rules:336`-`373`, `770`, `897`)

`(Zero [8] ptr mem) => (MOVDstore ptr (MOVDconst [0]) mem)` and its siblings at 1, 2 and 4 bytes,
`(Zero [16] ptr mem) => (STP [0] ptr (MOVDconst [0]) (MOVDconst [0]) mem)`, and the two
overlapping stores of `Zero [3]`, `[5]` … `[15]`: the validator replays the event as the store at
the `Zero` (the outer one; the inner one at a fresh ID) and a fresh `MOVDconst [0]` term
(`LowerCheck.zeroDef`, `zeroDef2`) and pairs the store with the `Zero` (`zeroLower`,
`zero2Lower`; `GoFV.Proof.Low.Sim.zeroSt_lower_eval`, `zero2_inner_eval`, `zero2_outer_eval`),
so these are rules on a `Zero` (`ArmRule.Mem`, `checked_zero`). The offsets and symbols or frame
variables folded into an `STP` (`770`, `897`) are replayed as its new definition
(`LowerCheck.qFold`), rules on an `STP` (`checked_stp`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- `ARM64.rules:336`: `(Zero [1] ptr mem) => (MOVBstore ptr (MOVDconst [0]) mem)` -/
theorem r_ARM64_336_sound : ArmRule.Checked r_ARM64_336 := checked_zero rfl

/-- `ARM64.rules:337`: `(Zero [2] ptr mem) => (MOVHstore ptr (MOVDconst [0]) mem)` -/
theorem r_ARM64_337_sound : ArmRule.Checked r_ARM64_337 := checked_zero rfl

/-- `ARM64.rules:338`: `(Zero [4] ptr mem) => (MOVWstore ptr (MOVDconst [0]) mem)` -/
theorem r_ARM64_338_sound : ArmRule.Checked r_ARM64_338 := checked_zero rfl

/-- `ARM64.rules:339`: `(Zero [3] ptr mem) => (MOVBstore [2] ptr (MOVDconst [0]) (MOVHstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_339_sound : ArmRule.Checked r_ARM64_339 := checked_zero rfl

/-- `ARM64.rules:342`: `(Zero [5] ptr mem) => (MOVBstore [4] ptr (MOVDconst [0]) (MOVWstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_342_sound : ArmRule.Checked r_ARM64_342 := checked_zero rfl

/-- `ARM64.rules:345`: `(Zero [6] ptr mem) => (MOVHstore [4] ptr (MOVDconst [0]) (MOVWstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_345_sound : ArmRule.Checked r_ARM64_345 := checked_zero rfl

/-- `ARM64.rules:348`: `(Zero [7] ptr mem) => (MOVWstore [3] ptr (MOVDconst [0]) (MOVWstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_348_sound : ArmRule.Checked r_ARM64_348 := checked_zero rfl

/-- `ARM64.rules:351`: `(Zero [8] ptr mem) => (MOVDstore ptr (MOVDconst [0]) mem)` -/
theorem r_ARM64_351_sound : ArmRule.Checked r_ARM64_351 := checked_zero rfl

/-- `ARM64.rules:352`: `(Zero [9] ptr mem) => (MOVBstore [8] ptr (MOVDconst [0]) (MOVDstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_352_sound : ArmRule.Checked r_ARM64_352 := checked_zero rfl

/-- `ARM64.rules:355`: `(Zero [10] ptr mem) => (MOVHstore [8] ptr (MOVDconst [0]) (MOVDstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_355_sound : ArmRule.Checked r_ARM64_355 := checked_zero rfl

/-- `ARM64.rules:358`: `(Zero [11] ptr mem) => (MOVDstore [3] ptr (MOVDconst [0]) (MOVDstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_358_sound : ArmRule.Checked r_ARM64_358 := checked_zero rfl

/-- `ARM64.rules:361`: `(Zero [12] ptr mem) => (MOVWstore [8] ptr (MOVDconst [0]) (MOVDstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_361_sound : ArmRule.Checked r_ARM64_361 := checked_zero rfl

/-- `ARM64.rules:364`: `(Zero [13] ptr mem) => (MOVDstore [5] ptr (MOVDconst [0]) (MOVDstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_364_sound : ArmRule.Checked r_ARM64_364 := checked_zero rfl

/-- `ARM64.rules:367`: `(Zero [14] ptr mem) => (MOVDstore [6] ptr (MOVDconst [0]) (MOVDstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_367_sound : ArmRule.Checked r_ARM64_367 := checked_zero rfl

/-- `ARM64.rules:370`: `(Zero [15] ptr mem) => (MOVDstore [7] ptr (MOVDconst [0]) (MOVDstore ptr (MOVDconst [0]) mem))` -/
theorem r_ARM64_370_sound : ArmRule.Checked r_ARM64_370 := checked_zero rfl

/-- `ARM64.rules:373`: `(Zero [16] ptr mem) => (STP [0] ptr (MOVDconst [0]) (MOVDconst [0]) mem)` -/
theorem r_ARM64_373_sound : ArmRule.Checked r_ARM64_373 := checked_zero rfl

/-- `ARM64.rules:770`: `(STP [off1] {sym} (ADDconst [off2] ptr) val1 val2 mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (STP [off1+int32(off2)] {sym} ptr val1 val2 mem)` -/
theorem r_ARM64_770_sound : ArmRule.Checked r_ARM64_770 := checked_stp rfl

/-- `ARM64.rules:897`: `(STP [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val1 val2 mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (STP [off1+off2] {mergeSym(sym1,sym2)} ptr val1 val2 mem)` -/
theorem r_ARM64_897_sound : ArmRule.Checked r_ARM64_897 := checked_stp rfl

end GoFV.Proof.Low.Rules
