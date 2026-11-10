import GoFV.Gen.Check57
import GoFV.Gen.Check58a

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G58: narrow and boolean operands, wider store-release sources,
`LoweredRound*F`; G35's upper-bit table across more writes (`docs/plans/proofs3.md` §4)

`checkG58 lc ps bstart g` is slice G57 (`GoFV/Gen/Check57.lean`) with, in a function with an arm64
op, the values of `Check58a.lean` (`vkind58a`: `REV16W`/`MADDW`/`MSUBW` of narrow arguments,
boolean operands of G32's, G33's and G36's ops and `CSINC`, `STLRW`/`STLRB` of wider sources,
`LoweredRound32F`/`64F`), tried when G57 rejects a value. Group B is G35's table (`uStep35`,
`GoFV/Gen/Check35.lean`), which every slice from G35 on reads.
`GoFV/Proof/Gen/G58.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `v` emits in G58, or why it is outside the slice: G57's kinds, then G58's group A (`e` is
G57's reason, kept for the other values). -/
def vkind58 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind57 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind58a lc g v with
    | some r => r
    | none => .error e

/-- G57's check with G58's value check. -/
def checkG58L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind58 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless loopOK lc ps tab do throw "loop branch target"
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

/-- Slice G58 of the genssa validator (module doc): `refsLive`, then G58's check on `liveCtx lc`. -/
def checkG58 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG58L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
