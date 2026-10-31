import GoFV.SSA.AuxData

/-!
# `ABIConfig.ABIAnalyzeTypes` for scalar integer parameters

The subset of `abi/abiutils.go:315-347` (with `assignParam`, `tryAllocRegs`, `nextSlot`,
go1.27.3) that the runtime calls a pass creates need: parameters of integer or pointer shape
that take one integer register each (`writebarrier`'s `wbZero`/`wbMove` calls take `uintptr`s),
no results. A parameter is assigned the next integer register while there is one, with a spill
slot at the next aligned spill offset; otherwise a stack slot at the next aligned stack offset.
The spill area starts at the register-aligned end of the stack arguments.
-/

namespace GoFV.SSA.ABIAnalyze

/-- An `abi.ABIConfig` as exported (`config abi0`/`abi1`: `<intregs>:<floatregs>:<localsoffset>`)
with its `Which()`. -/
structure ABIConfig where
  which : Nat
  intRegs : Nat
  floatRegs : Nat
  offsetForLocals : Int
  deriving Inhabited, Repr

/-- Parse `<intregs>:<floatregs>:<localsoffset>`. -/
def ABIConfig.parse (which : Nat) (s : String) : Option ABIConfig :=
  match s.splitOn ":" with
  | [i, fl, o] => do
    return { which, intRegs := ← i.toNat?, floatRegs := ← fl.toNat?, offsetForLocals := ← o.toInt? }
  | _ => none

/-- `types.RoundUp(o, r)` for a power-of-two `r > 0`. -/
@[inline] def roundUp (o r : Int) : Int := (o + r - 1) / r * r

/-- `ABIAnalyzeTypes(params, nil)` where each parameter is `(type, size)` of a register-sized or
smaller integer/pointer scalar (alignment = size), `regSize` is `types.RegSize`. -/
def analyzeIntScalars (c : ABIConfig) (regSize : Int) (params : Array (TypeRef × Int)) :
    Except String CallABI := do
  let mut stackOffset := c.offsetForLocals
  let mut spillOffset : Int := 0
  let mut intUsed := 0
  let mut out : Array ABIParam := #[]
  for h : i in [0:params.size] do
    let (t, size) := params[i]
    if size ≤ 0 || size > regSize then
      throw s!"ABIAnalyzeTypes: parameter t{t} of size {size} is not a scalar register type"
    if intUsed < c.intRegs then
      let off := roundUp spillOffset size
      spillOffset := off + size
      out := out.push { out := false, index := i, type := t, name := none, regs := #[intUsed],
                        offset := off }
      intUsed := intUsed + 1
    else
      let off := roundUp stackOffset size
      stackOffset := off + size
      out := out.push { out := false, index := i, type := t, name := none, regs := #[],
                        offset := off }
  stackOffset := roundUp stackOffset regSize
  return { abi := c.which, nin := params.size, nout := 0, spillOff := roundUp stackOffset regSize,
           spillSize := roundUp spillOffset regSize, inRegs := intUsed, outRegs := 0,
           params := out }

end GoFV.SSA.ABIAnalyze
