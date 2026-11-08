import GoFV.Gen.Check11

/-!
# The genssa validator, slice G12: pointer conversions (`docs/plans/proofs3.md` §4)

`checkG12 lc ps bstart g` extends slice G11 (`GoFV/Gen/Check11.lean`) by `Convert x mem`, the
conversion between a pointer and `uintptr` (`unsafe.Pointer(u)`, `uintptr(p)`). Genssa emits no
code for it and checks that the argument and the value share a register (`ssagen/ssa.go`'s
`OpConvert` case, `GoFV/Gen/Genssa.lean`). G12 accepts it with no temporary, the argument and
the value homed in one register G1 may write, both of class 64, and the memory last.

`GoFV/Proof/Gen/G12.lean` proves what an accepted function satisfies (`g12_value`, `g12_term`,
`g12_nilPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `Convert x mem`: no temporary, `x` and the value in one register of class 64, the memory
last; no code. -/
def convKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: Convert shape"
  let (ca, ra) ← argObj lc v 0
  let (cd, rd) ← resObj lc v
  memArg lc v 1
  unless ca == 64 && cd == 64 && ra == rd do throw s!"v{v.id}: Convert registers"
  return .none

/-- What `v` emits in G12, or why it is outside the slice. -/
def vkind12 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .Convert then convKind lc v else vkind11 lc g v

/-- Slice G12 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG12 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind12 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
  unless cloFirst lc do throw "LoweredGetClosurePtr after code"
  checkFrame lc g
  checkVars lc g
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
  checkK lc kt
  let ids := ps.toList.map (·.id)
  unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
  return (tab, kt)

end GoFV.Gen.Check
