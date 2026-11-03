import GoFV.SSA.Op
import GoFV.SSA.OpARM64
import GoFV.SSA.RegARM64

/-! Spot checks of the generated op table against `opGen.go` (and that the metadata
functions reduce in the kernel). `scripts/gen-ops.sh` already compares every entry with the
pinned `opGen.go`; these pin a few values the passes rely on. -/

namespace GoFVTest.OpCheck
open GoFV.SSA

example : Op.Add64.argLen = 2 ∧ Op.Add64.commutative = true ∧ Op.Add64.name = "Add64" := by decide
example : Op.Phi.argLen = -1 ∧ Op.Invalid.name = "OpInvalid" := by decide
example : Op.Const64.auxType = .Int64 ∧ Op.Addr.auxType = .Sym ∧ Op.Addr.symEffect.addr = true := by decide
example : Op.StaticCall.call = true ∧ Op.StaticCall.auxType = .CallOff := by decide
example : Op.NilCheck.nilCheck = true ∧ Op.Sub64.commutative = false := by decide
example : BlockKind.If.controls = 1 ∧ BlockKind.Plain.controls = 0 ∧ BlockKind.Invalid.name = "BlockInvalid" := by decide
example : Op.all.size = 800 ∧ BlockKind.all.size = 34 := by decide +kernel

-- ARM64 ops: names, export spelling, flags, Go opcode numbers (opGen.go of the pin).
example : Op.ARM64ADD.name = "ADD" ∧ Op.ARM64ADD.exportName = "ARM64ADD" ∧
    Op.ARM64ADD.generic = false ∧ Op.Add64.generic = true ∧ Op.Add64.exportName = "Add64" := by decide
example : Op.ARM64CSEL.auxType = .CCop ∧ Op.ARM64CMP.argLen = 2 ∧
    Op.ARM64MOVDload.faultOnNilArg0 = true ∧ Op.ARM64MOVDload.symEffect.read = true := by decide
example : Op.ARM64LoweredNilCheck.nilCheck = true ∧ Op.ARM64LoweredZero.faultOnNilArg0 = true := by decide
example : Op.ARM64ADCSflags.goNum = 4292 ∧ Op.Add8.goNum = 6398 := by decide
example : BlockKind.ARM64EQ.name = "EQ" ∧ BlockKind.ARM64EQ.exportName = "ARM64EQ" ∧
    BlockKind.ARM64JUMPTABLE.controls = 2 ∧ BlockKind.ARM64TBZ.auxIntType = "int64" := by decide

#guard Op.all.all fun o => Op.ofGoNum? o.goNum == some o
#guard BlockKind.all.all fun k => BlockKind.ofGoNum? k.goNum == some k
#guard (Op.all.map Op.exportName).toList.eraseDups.length == Op.all.size
#guard Op.all.all fun o => o.ctorIdx < Op.all.size && Op.all[o.ctorIdx]! == o

-- Register info and the register table.
#guard Op.ARM64ADD.regInfo.inputs.map (·.idx) == [0, 1] && Op.ARM64ADD.asm == "ADD"
#guard Op.Add64.regInfo == {}
#guard ARM64.registers.size == 64 &&
  (ARM64.registers.toList.zip (List.range 64)).all fun (r, i) => r.num == i
#guard ARM64.registers[30]!.name == "SP" && ARM64.registers[63]!.name == "SB" && ARM64.linkReg == 28
#guard ARM64.gpRegMask.v1 == 335544319 && ARM64.paramFloatReg.head? == some 31

end GoFVTest.OpCheck
