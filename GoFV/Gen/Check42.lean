import GoFV.Gen.Check41

/-!
# The genssa validator, slice G42: `ANDconst` widening a narrow argument (`docs/plans/proofs3.md` §4)

`checkG42 lc ps bstart g` is slice G41 (`GoFV/Gen/Check41.lean`) with, in a function with an arm64
op, `ANDconst [k] x` (`AND $k, Rn, Rd`) whose result class `c ≥ 8` exceeds the class `ca` of `x`
when the mask reads only the low `ca` bits (`0 ≤ k < 2^ca`): only the low `ca` bits of `x`'s
register are known, and the mask clears every bit above them, so the machine's word is the whole
result (G3's `ANDconst` asks `c ≤ ca`). Go's rules emit it for `x & k` of a narrow `x` (mostly a
narrow load) at a wider type. `GoFV/Proof/Gen/G42.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `ANDconst [k] x` of class `c ≥ 8` with `0 ≤ k < 2^ca`, `ca` the class of `x` (module doc):
what it emits. -/
def andWKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 2 ^ ca do
    throw s!"v{v.id}: shift or mask widths"
  return .prog (.ofShape { as := .AND, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd })

/-- What `v` emits in G42, or why it is outside the slice: G41's kinds, then G42's `ANDconst`. -/
def vkind42 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind41 lc g v with
  | .ok kd => .ok kd
  | .error e => if v.op == .ARM64ANDconst then andWKind lc v else .error e

/-- G41's check with G42's value check. -/
def checkG42L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind42 lc g, tm := cx.termG3 }
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

/-- Slice G42 of the genssa validator (module doc): `refsLive`, then G42's check on `liveCtx lc`. -/
def checkG42 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG42L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
