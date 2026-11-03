import GoFV.Opt.Pass
import GoFV.SSA.Alloc

/-!
# addressing modes, checkLower

`addressing modes` (`addressingmodes.go:9-18`, issue #389): the arch switch admits amd64, 386
and s390x only; on arm64 the pass returns at once (ARM64 address folding is done by `lower`'s
rules).

`checkLower` (`lower.go:22-53`, issue #397): over `f.Blocks` × `b.Values`, every generic op
must be one of the residual ops Go allows (`SP`, `SPanchored`, `SB`, `InitMem`, `Arg`,
`ArgIntReg`, `ArgFloatReg`, `Phi`, `VarDef`, `VarLive`, `KeepAlive`, `Select0`, `Select1`,
`SelectN`, `Convert`, `InlMark`, `WBend`), a `MakeResult` that is its block's `Controls[0]`, or
`GetG` with `Config.hasGReg`; the first other value is fatal. The function is unchanged.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `addressingModes(f)`: identity on arm64 (the only arch the port covers). -/
def addressingModesPass : Pass := Pass.ofFunc fun env f => do
  match env.config? "arch" with
  | some #[.word "arm64"] => return f
  | _ => throw "addressing modes: only arm64 is ported"

/-- Generic ops `checkLower` accepts unconditionally (`lower.go:31-34`). -/
def CheckLower.residual : Op → Bool
  | .SP | .SPanchored | .SB | .InitMem | .Arg | .ArgIntReg | .ArgFloatReg | .Phi | .VarDef
  | .VarLive | .KeepAlive | .Select0 | .Select1 | .SelectN | .Convert | .InlMark | .WBend => true
  | _ => false

/-- `checkLower(f)`: the first value Go rejects, if any. -/
def checkLower (hasGReg : Bool) (f : Func) : Option ID := Id.run do
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      if !x.op.generic || CheckLower.residual x.op then continue
      if x.op == .MakeResult && (f.getB b).controls[0]? == some v then continue
      if x.op == .GetG && hasGReg then continue
      return some v
  return none

/-- The `checkLower` pass. -/
def checkLowerPass : Pass := Pass.ofFunc fun env f => do
  match checkLower (← env.flag "hasgreg") f with
  | none => return f
  | some v => throw s!"not lowered: v{v}, {(f.getV v).op.name}"

end GoFV.Opt
