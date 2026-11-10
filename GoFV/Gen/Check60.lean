import GoFV.Gen.Check59
import GoFV.Gen.Check56

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G60: G59 with G56's float constants (`docs/plans/proofs3.md` §4, §10)

Slices G57, G48, G58 and G59 are chained on G55, not on G56 (G55 → G57 → G48 → G58 → G59).
`checkG60 lc ps bstart g` is slice G59 (`GoFV/Gen/Check59.lean`) with G56's float constants
(`vkind56a`: `FMOVSconst`/`FMOVDconst` homed by `FMOVS`/`FMOVD $c, Fd` or, on P0', by the load of
its float constant symbol), tried before G59's kinds as `vkind56` tries it before G55's.
`GoFV/Proof/Gen/G60.lean` proves what an accepted function satisfies, given the constant symbols'
bytes in memory.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `v` emits in G60, or why it is outside the slice: a float constant by `vkind56a`, every
other value by G59's kinds. -/
def vkind60 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind56a lc g v with
  | some r => r
  | none => vkind59 lc g v

/-- G59's check with G60's value check. -/
def checkG60L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind60 lc g, tm := cx.termG3 }
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

/-- Slice G60 of the genssa validator (module doc): `refsLive`, then G60's check on `liveCtx lc`. -/
def checkG60 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG60L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
