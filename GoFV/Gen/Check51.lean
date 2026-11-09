import GoFV.Gen.Check51a
import GoFV.Gen.Check51b
import GoFV.Gen.Check51c

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G51: cheap single-instruction ops (`docs/plans/proofs3.md` §4)

`checkG51 lc ps bstart g` is slice G50 (`GoFV/Gen/Check50.lean`) with, in a function with an arm64
op, the flag and conditional ops of `Check51a.lean` (`vkind51a`: `CSNEG`, `TSTW`, `CMN`, `CMNW`,
`CMPshiftRA`), the ALU ops of `Check51b.lean` (`vkind51b`: `MVNshiftLL`, `MVNshiftRL`,
`MVNshiftRA`, `SBFIZ`, the rotates) and the boolean operands of `Check51c.lean` (`vkind51c`:
`ADD`, `SUB`, `ADDconst`, `SUBconst`, `ADDshiftLL` and the shifted adds, subtracts and logic ops
with an argument of class 1, which the earlier slices reject by its width), each tried when G50
rejects a value. `GoFV/Proof/Gen/G51.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `v` emits in G51, or why it is outside the slice: G50's kinds, then G51's ops (`e` is
G50's reason, kept for the other values). -/
def vkind51 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind50 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind51a lc v with
    | some r => r
    | none =>
      match vkind51b lc v with
      | some r => r
      | none =>
        match vkind51c lc v with
        | some r => r
        | none => .error e

/-- G50's check with G51's value check. -/
def checkG51L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind51 lc g, tm := cx.termG3 }
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

/-- Slice G51 of the genssa validator (module doc): `refsLive`, then G51's check on `liveCtx lc`. -/
def checkG51 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG51L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
