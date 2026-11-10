import GoFV.Gen.Check60
import GoFV.Gen.Check61a

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G61: the atomic read-modify-writes (`docs/plans/proofs3.md` §4)

`checkG61 lc ps bstart g` is slice G60 (`GoFV/Gen/Check60.lean`, on P0') with, in a function with an
arm64 op, the values of `Check61a.lean` (`vkind61a`: the lowered atomic exchanges, adds,
compare-and-swaps, ands and ors, their load-exclusive/store-exclusive loops and LSE forms, and
their components), tried when G60 rejects a value, and `atomOK`: each loop's `CBNZ R27` branches
to its `LDAXR`, and each compare-and-swap loop's `BNE` branches to its `CSET`.
`GoFV/Proof/Gen/G61.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `v` emits in G61, or why it is outside the slice: G60's kinds, then G61's group A (`e` is
G60's reason, kept for the other values). -/
def vkind61 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind60 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind61a lc v with
    | some r => r
    | none => .error e

/-- G60's check with G61's value check and `atomOK`. -/
def checkG61L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind61 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless loopOK lc ps tab do throw "loop branch target"
    unless atomOK lc ps tab do throw "atomic branch target"
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

/-- Slice G61 of the genssa validator (module doc): `refsLive`, then G61's check on `liveCtx lc`. -/
def checkG61 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG61L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
