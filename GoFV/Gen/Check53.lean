import GoFV.Gen.Check52
import GoFV.Gen.Check53a

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G53: `LoweredMove` (`docs/plans/proofs3.md` §4)

`checkG53 lc ps bstart g` is slice G52 (`GoFV/Gen/Check52.lean`) with, in a function with an arm64
op, the straight-line copies of `Check53a.lean` (`vkind53a`: `LoweredMove`), tried when G52 rejects
a value. `GoFV/Proof/Gen/G53.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `v` emits in G53, or why it is outside the slice: G52's kinds, then `LoweredMove` (`e` is
G52's reason, kept for the other values). -/
def vkind53 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind52 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind53a lc v with
    | some r => r
    | none => .error e

/-- G52's check with G53's value check. -/
def checkG53L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind53 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
    if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
    unless cloFirst lc do throw "LoweredGetClosurePtr after code"
    checkFrame lc g
    checkVars49 lc g
    let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
    let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
    checkK lc kt
    let ids := ps.toList.map (·.id)
    unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
    return (tab, kt)
  else checkNL30 lc ps bstart g

/-- Slice G53 of the genssa validator (module doc): `refsLive`, then G53's check on `liveCtx lc`. -/
def checkG53 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG53L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
