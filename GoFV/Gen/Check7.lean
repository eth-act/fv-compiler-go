import GoFV.Gen.Check6

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G7: nil checks (`docs/plans/proofs3.md` §4)

`checkG7 lc ps bstart g` extends slice G6 (`GoFV/Gen/Check6.lean`) by the nil checks
(`ssa.go`'s `LoweredNilCheck` case): `LoweredNilCheck p mem`, the pointer `p` in a 64-bit
register `Rp`, emits `MOVB (Rp), R27`, a one-byte load into `REGTMP` that faults in the nil page
exactly when `runLoc`'s nil check panics (`nilFaults`, `memRoot`'s `NilCheck`). The value has no
home and a shape `LocState.write` drops (`dropTy`: lowering gives it the `void` shape; its result,
the pointer, is not kept), and `R27` is no Go register (`LocMatch` leaves it free).

`GoFV/Proof/Gen/G7.lean` proves what an accepted function satisfies (`g7_value`, `g7_term`, and
`g7_nilPanic` for the fault).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- A shape `LocState.write` drops at a value with no home: no tuple, memory or flags. -/
def dropTy : Ty → Bool
  | .tuple _ | .mem => false
  | t => !t.isFlags

/-- The Prog of a nil check of the pointer in `Rp`: `MOVB (Rp), R27`. -/
def nilShape (rp : Int) : Shape := { as := .MOVB, from_ := memA rp 0, to := regA ARM64.REGTMP }

/-- What `v` emits in G7, or why it is outside the slice. -/
def vkind7 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op != .ARM64LoweredNilCheck then vkind6 lc g v else do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && lc.home v.id == none && dropTy (lc.ty v.id) do
    throw s!"v{v.id}: nil check shape"
  let (c, rp) ← argObj lc v 0
  unless c == 64 do throw s!"v{v.id}: nil check width"
  memArg lc v 1
  return .prog (.ofShape (nilShape rp))

/-- Slice G7 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG7 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind7 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  if let some i := (List.range lc.homes.size).find? (!homeOK4 lc ·) then throw (homeErr lc i)
  checkFrame lc g
  checkVars lc g
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
  checkK lc kt
  let ids := ps.toList.map (·.id)
  unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
  return (tab, kt)

end GoFV.Gen.Check
