import GoFV.Gen.Check16

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G17: the goroutine (`docs/plans/proofs3.md` §4)

`checkG17 lc ps bstart g` extends slice G16 (`GoFV/Gen/Check16.lean`) by `GetG mem`, the current
goroutine: Phase 1's `evalPure` gives the pointer to the start of the opaque global
`runtime.g` (`GoFV/SSA/Sem/Pure.lean`). On arm64 the goroutine is in the `g` register `R28`:
regalloc homes `GetG` there (`regalloc.go`, `hasGReg`) and genssa emits no code for it
(`ssagen/ssa.go`, `OpGetG`).

G17 accepts it with no temporary, its memory argument only, homed in `g` (`gReg`, Go register 26)
at a 64-bit shape; no code.

`GoFV/Proof/Gen/G17.lean` proves what an accepted function satisfies (`g17_value`, `g17_term`,
`g17_nilPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The `g` register (Go register 26, `R28`). -/
def gReg : Nat := 26

/-- `GetG mem`: no temporary, the memory its only argument, homed in `g` at a 64-bit shape; no
code. -/
def getGKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 && lc.home v.id == some (.reg gReg) && cls (lc.ty v.id) == some 64 do
    throw s!"v{v.id}: GetG shape"
  memArg lc v 0
  return .none

/-- What `v` emits in G17, or why it is outside the slice. -/
def vkind17 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .GetG then getGKind lc v else vkind16 lc g v

/-- Slice G17 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG17 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind17 lc g, tm := cx.termG3 }
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
