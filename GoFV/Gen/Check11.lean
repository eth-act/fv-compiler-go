import GoFV.Gen.Check10

/-!
# The genssa validator, slice G11: the closure context (`docs/plans/proofs3.md` §4)

`checkG11 lc ps bstart g` extends slice G10 (`GoFV/Gen/Check10.lean`) by `LoweredGetClosurePtr`
(`ssa.go`'s `ssagen.CheckLoweredGetClosurePtr` case): the closure context of the activation, which
Go's internal ABI passes in `R26` (Go register 25, `ctxReg`). Regalloc homes the value in `R26`
(its `regInfo` output), and genssa emits no code for it, only checking that it is the first value
of the entry block after the register arguments (`ArgIntReg`/`ArgFloatReg`). G11 accepts it with
no argument, homed in `R26` at a 64-bit shape, placed there (`cloFirst`): no code runs before it
but the prologue.

`GoFV/Proof/Gen/G11.lean` proves what an accepted function satisfies (`g11_value`, `g11_term`,
`g11_nilPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `LoweredGetClosurePtr`: no temporary, no argument, homed in `R26` at a 64-bit shape; no code. -/
def cloKind (lc : LocCtx) (v : Value) : Except String VKind2 :=
  if (lc.temps[v.id]?).join != none then .error s!"v{v.id}: temporary register"
  else if v.args.size == 0 && lc.home v.id == some (.reg ctxReg) && cls (lc.ty v.id) == some 64 then
    .ok .none
  else .error s!"v{v.id}: closure pointer shape"

/-- What `v` emits in G11, or why it is outside the slice. -/
def vkind11 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .ARM64LoweredGetClosurePtr then cloKind lc v else vkind10 lc g v

/-- Every `LoweredGetClosurePtr` is in the entry block after register arguments only
(`ssagen.CheckLoweredGetClosurePtr`, `ssagen/ssa.go:7831-7847`). -/
def cloFirst (lc : LocCtx) : Bool :=
  lc.ctx.f.blocks.all fun bid =>
    match lc.ctx.f.block? bid with
    | some b =>
      (b.values.toList.zipIdx).all fun (id, k) =>
        ((lc.ctx.f.value? id).map (·.op)) != some .ARM64LoweredGetClosurePtr ||
          (bid == lc.ctx.f.entry && (b.values.toList.take k).all fun w =>
            ((lc.ctx.f.value? w).map (·.op)) == some .ArgIntReg ||
              ((lc.ctx.f.value? w).map (·.op)) == some .ArgFloatReg)
    | none => true

/-- Slice G11 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG11 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind11 lc g, tm := cx.termG3 }
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
