import GoFV.SSA.Op

/-! Spot checks of the generated op table against `opGen.go` (and that the metadata
functions reduce in the kernel). -/

namespace GoFVTest.OpCheck
open GoFV.SSA

example : Op.Add64.argLen = 2 ∧ Op.Add64.commutative = true ∧ Op.Add64.name = "Add64" := by decide
example : Op.Phi.argLen = -1 ∧ Op.Invalid.name = "OpInvalid" := by decide
example : Op.Const64.auxType = .Int64 ∧ Op.Addr.auxType = .Sym ∧ Op.Addr.symEffect.addr = true := by decide
example : Op.StaticCall.call = true ∧ Op.StaticCall.auxType = .CallOff := by decide
example : Op.NilCheck.nilCheck = true ∧ Op.Sub64.commutative = false := by decide
example : BlockKind.If.controls = 1 ∧ BlockKind.Plain.controls = 0 ∧ BlockKind.Invalid.name = "BlockInvalid" := by decide
example : Op.all.size = 446 ∧ BlockKind.all.size = 9 := by decide +kernel

end GoFVTest.OpCheck
