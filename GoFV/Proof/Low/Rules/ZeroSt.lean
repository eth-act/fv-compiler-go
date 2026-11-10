import GoFV.Proof.Low.Rules.Kit
import GoFV.Rules.Generated.ARM64

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lowering rule lemmas: `Zero [n]` to a store of `0` (`ARM64.rules:336`-`338`, `351`, `373`, `770`, `897`)

`(Zero [8] ptr mem) => (MOVDstore ptr (MOVDconst [0]) mem)` and its siblings at 1, 2 and 4 bytes,
and `(Zero [16] ptr mem) => (STP [0] ptr (MOVDconst [0]) (MOVDconst [0]) mem)`: the validator
replays the event as the store at the `Zero` and a fresh `MOVDconst [0]` term
(`LowerCheck.zeroDef`) and pairs the store with the `Zero` (`zeroLower`,
`GoFV.Proof.Low.Sim.zeroSt_lower_eval`), so these are rules on a `Zero` (`ArmRule.Mem`,
`checked_zero`). The offsets and symbols or frame variables folded into an `STP` (`770`, `897`)
are replayed as its new definition (`LowerCheck.qFold`), rules on an `STP` (`checked_stp`).
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

/-- `ARM64.rules:351`: `(Zero [8] ptr mem) => (MOVDstore ptr (MOVDconst [0]) mem)` -/
theorem r_ARM64_351_sound : ArmRule.Checked r_ARM64_351 := checked_zero rfl

/-- `ARM64.rules:373`: `(Zero [16] ptr mem) => (STP [0] ptr (MOVDconst [0]) (MOVDconst [0]) mem)` -/
theorem r_ARM64_373_sound : ArmRule.Checked r_ARM64_373 := checked_zero rfl

/-- `ARM64.rules:770`: `(STP [off1] {sym} (ADDconst [off2] ptr) val1 val2 mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (STP [off1+int32(off2)] {sym} ptr val1 val2 mem)` -/
theorem r_ARM64_770_sound : ArmRule.Checked r_ARM64_770 := checked_stp rfl

/-- `ARM64.rules:897`: `(STP [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val1 val2 mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (STP [off1+off2] {mergeSym(sym1,sym2)} ptr val1 val2 mem)` -/
theorem r_ARM64_897_sound : ArmRule.Checked r_ARM64_897 := checked_stp rfl

end GoFV.Proof.Low.Rules
