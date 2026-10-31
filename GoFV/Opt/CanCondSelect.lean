import GoFV.SSA.Alloc
import GoFV.Rules.Helpers.Types

/-!
# `canCondSelect` (`branchelim.go:72`)

Shared by `branchelim` and `prove` (which passes `loadAddr == nil`): whether `v` may become a
`CondSelect` — not used to compute a load address, (on loong64) one argument a constant zero,
and a register-sized pointer-shaped or integer type (not a byte on amd64).
-/

namespace GoFV.SSA

/-- `v.isGenericIntConst()` (`value.go:488`), on the op. -/
def Op.isGenericIntConst : Op → Bool
  | .Const64 | .Const32 | .Const16 | .Const8 => true
  | _ => false

end GoFV.SSA

namespace GoFV.Opt

open GoFV.SSA

/-- `canCondSelect(v, arch, loadAddr)`; `inLoadAddr` is `loadAddr != nil &&
loadAddr.contains(v.ID)`, `regSize` is `Config.RegSize`. -/
def canCondSelect (tabs : Tables) (regSize : Int) (arch : String) (f : Func) (v : ID)
    (inLoadAddr : Bool) : Except String Bool := do
  if inLoadAddr then return false
  let x := f.getV v
  if arch == "loong64" then
    let zero (a : ID) : Bool := let y := f.getV a; y.op.isGenericIntConst && y.auxInt == 0
    if !zero x.args[0]! && !zero x.args[1]! then return false
  let size ← GoFV.Rules.Ty.size tabs x.type
  if size > regSize then return false
  if ← GoFV.Rules.Ty.isPtrShaped tabs x.type then return true
  if ← GoFV.Rules.Ty.isInteger tabs x.type then
    return !(arch == "amd64" && size < 2)
  return false

end GoFV.Opt
