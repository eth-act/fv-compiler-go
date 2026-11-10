import GoFV.Gen.Check58
import GoFV.Gen.Check59p

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G59: float pair loads of a global or a frame variable; `Defer`
blocks (`docs/plans/proofs3.md` §4)

`checkG59 lc ps bstart g` is slice G58 (`GoFV/Gen/Check58.lean`) with, in a function with an arm64
op, the values of `Check59p.lean` (`vkind59p`: `FLDPD`/`FLDPS` with an aux, of a global or of a
`Blk.temp` frame variable), tried when G58 rejects a value. Group D is the `Defer` arm of the
shared terminator check (`Cx.term`, `GoFV/Gen/Check.lean`), which every slice's terminator check
reads. `GoFV/Proof/Gen/G59.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `v` emits in G59, or why it is outside the slice: G58's kinds, then G59's group P (`e` is
G58's reason, kept for the other values). -/
def vkind59 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind58 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind59p lc g v with
    | some r => r
    | none => .error e

/-- G58's check with G59's value check. -/
def checkG59L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind59 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless loopOK lc ps tab do throw "loop branch target"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
    if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
    unless cloFirst lc do throw "LoweredGetClosurePtr after code"
    unless spHomes48 lc do throw "a value other than SP homed in SP"
    checkFrame lc g
    checkVars49 lc g
    let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
    let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
    checkK lc kt
    let ids := ps.toList.map (·.id)
    unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
    return (tab, kt)
  else checkNL30 lc ps bstart g

/-- Slice G59 of the genssa validator (module doc): `refsLive`, then G59's check on `liveCtx lc`. -/
def checkG59 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG59L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
