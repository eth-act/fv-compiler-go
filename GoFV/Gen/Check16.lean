import GoFV.Gen.Check15

/-!
# The genssa validator, slice G16: shifted adds (`docs/plans/proofs3.md` §4)

`checkG16 lc ps bstart g` extends slice G15 (`GoFV/Gen/Check15.lean`) by `ADDshiftLL [k] x y`,
Phase 1's `Arm64.addSh … .ll k`: `x + (y << k)`, with `ADD`'s pointer case for a pointer `x`.
Genssa emits one `ADD Rm<<k, Rn, Rd` (`genshift`, `ssa.go:141`), whose source operand is
`makeshift`'s (`ssa.go:133`): `TYPE_SHIFT` with offset `(Rm & 31) << 16 | SHIFT_LL | k << 10`
(`shiftLLA`).

G16 accepts it as G1 accepts `ADD` (`vkind`): no temporary, both arguments and the result in
registers, the result of at least 8 bits and no wider than either argument; the shift amount in
`[0, 64)` (`makeshift` rejects any other).

`GoFV/Proof/Gen/G16.lean` proves what an accepted function satisfies (`g16_value`, `g16_term`,
`g16_nilPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `makeshift`'s operand for obj register `rm` (`REG_R0 + k`, `k < 32`) shifted left by `s`:
`k << 16 | SHIFT_LL | s << 10`, written as a sum (`SHIFT_LL = 0`). -/
def shiftLLA (rm : Int) (s : Nat) : Addr :=
  { type := .SHIFT, offset := (rm - ARM64.REG_R0) * 65536 + s * 1024 }

/-- `ADDshiftLL [k] x y`: no temporary, two register arguments, a result of at least 8 bits no
wider than either argument, `0 ≤ k < 64`; one `ADD Rm<<k, Rn, Rd`. -/
def addShKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  unless 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64 do throw s!"v{v.id}: shift amount"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && c ≤ ca && c ≤ cb do throw s!"v{v.id}: arithmetic widths"
  return .prog (.ofShape
    { as := .ADD, from_ := shiftLLA rm v.auxInt.toInt.toNat, reg := rn, to := regA rd })

/-- What `v` emits in G16, or why it is outside the slice. -/
def vkind16 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .ARM64ADDshiftLL then addShKind lc v else vkind15 lc g v

/-- Slice G16 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG16 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind16 lc g, tm := cx.termG3 }
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
