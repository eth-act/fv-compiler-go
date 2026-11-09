import GoFV.Gen.Check39

/-!
# The genssa validator, slice G40: `InitMem` after the entry values (`docs/plans/proofs3.md` §4)

`schedule` may place `InitMem` in a later block than the entry (next to its only use, a
`MakeResult` or a load), where G1's check rejects it (`InitMem after the entry values`). `runLoc`
runs it as anywhere: it sets the state's memory to the activation's initial memory. In a function
whose values keep the memory (`memPure`: every value is a `Phi`, an `InitMem`, a `MakeResult`
whose write changes nothing, or of a shape without a memory component), the state's memory is
the initial memory all along, so `InitMem` changes nothing and emits no code.

`checkG40 lc ps bstart g` is slice G39 (`GoFV/Gen/Check39.lean`) with, in a function with an arm64
op where `memPure` holds, `InitMem` anywhere: no temporary, no argument, no home, of shape
`mem`; no code. `GoFV/Proof/Gen/G40.lean` proves what an accepted function satisfies and that
`runLoc` keeps the memory at the initial memory (`memInit_stepLoc`, `memInit_stepTermLoc`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- A shape `LocState.write` writes no memory at: not the memory, and no memory component. -/
def memInert : Ty → Bool
  | .mem => false
  | .tuple ts => ts.all fun t => !memTy t
  | _ => true

/-- A value whose step keeps the state's memory at the initial memory (module doc). -/
def memKeep (lc : LocCtx) (u : Value) : Bool :=
  u.op == .Phi || memInert (lc.ty u.id) ||
    (u.op == .InitMem && (lc.temps[u.id]?).join == none && lc.home u.id == none &&
      memTy (lc.ty u.id)) ||
    (u.op == .MakeResult && (lc.temps[u.id]?).join == none &&
      (lc.home u.id == none || lc.home u.id == some (.results #[])) &&
      resultsTy lc u.args (lc.ty u.id) && u.args.all fun a => !memTy (lc.ty a) || lc.home a == none)

/-- Every value of the function keeps the memory at the initial memory. -/
def memPure (lc : LocCtx) : Bool :=
  (List.range lc.ctx.f.valueTab.size).all fun i => (lc.ctx.f.value? i).all (memKeep lc)

/-- `InitMem` in a function whose values keep the memory: no code. -/
def initMemKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 0 && lc.home v.id == none && memTy (lc.ty v.id) do
    throw s!"v{v.id}: InitMem shape"
  return .none

/-- What `v` emits in G40, or why it is outside the slice. -/
def vkind40 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .InitMem && memPure lc then initMemKind lc v else vkind38 lc g v

/-- G38's check with G40's value check. -/
def checkG40L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind40 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
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
  else checkNL30 lc ps bstart g

/-- Slice G40 of the genssa validator (module doc): `refsLive`, then G40's check on `liveCtx lc`. -/
def checkG40 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG40L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
