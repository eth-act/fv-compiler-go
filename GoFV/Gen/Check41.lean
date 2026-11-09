import GoFV.Gen.Check40

/-!
# The genssa validator, slice G41: `CMNconst`, `CMPshiftLL`, `CMPshiftRL` (`docs/plans/proofs3.md` §4)

`checkG41 lc ps bstart g` is slice G40 (`GoFV/Gen/Check40.lean`) with, in a function with an arm64
op, the compares

* `CMNconst [k] x` (`CMN $k, Rn`): the flags of the 64-bit `ADDS` of `x` and `k`, `x` of 64 bits;
* `CMPshiftLL`, `CMPshiftRL [k] x y` (`CMP Rm SHIFT k, Rn`, G27's shifted operand `shiftA`,
  `cmpSh41?`, `0 ≤ k < 64`): the flags of the `SUBS` of `x` and `y` shifted by `k`, `x` and `y` of
  64 bits;

of the flags shape, without home or temporary. On a pointer without an integer form `runLoc` gives
their flags `Z` clear (Phase 1's `cmp1P`/`cmpSh`, `Arm64.zClear`); `GoFV/Proof/Gen/G41.lean` proves
what an accepted function satisfies under the run premise `CmpPre` (their first argument is no
such pointer, as G1's `NoBarePtr` premise for `CMP`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The shifted compares of G41 and their shift kind (0 `LSL`, 1 `LSR`, as G27's `logSh?`). -/
def cmpSh41? : Op → Option Nat
  | .ARM64CMPshiftLL => some 0 | .ARM64CMPshiftRL => some 1
  | _ => none

/-- `CMNconst [k] x` (module doc): what it emits. -/
def cmnKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 && (lc.ty v.id).isFlags && lc.home v.id == none do
    throw s!"v{v.id}: compare shape"
  let (ca, rn) ← argObj lc v 0
  unless ca == 64 do throw s!"v{v.id}: compare widths"
  return .prog (.ofShape { as := .CMN, from_ := constA v.auxInt.toInt, reg := rn })

/-- `CMPshiftLL`, `CMPshiftRL [k] x y` (module doc): what it emits. -/
def cmpShKind (lc : LocCtx) (v : Value) (typ : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && (lc.ty v.id).isFlags && lc.home v.id == none do
    throw s!"v{v.id}: compare shape"
  unless 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64 do throw s!"v{v.id}: shift amount"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  unless ca == 64 && cb == 64 do throw s!"v{v.id}: compare widths"
  return .prog (.ofShape { as := .CMP, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn })

/-- What `v` emits in G41, or why it is outside the slice. -/
def vkind41 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .ARM64CMNconst then cmnKind lc v
  else match cmpSh41? v.op with
    | some typ => cmpShKind lc v typ
    | none => vkind40 lc g v

/-- G40's check with G41's value check. -/
def checkG41L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind41 lc g, tm := cx.termG3 }
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

/-- Slice G41 of the genssa validator (module doc): `refsLive`, then G41's check on `liveCtx lc`. -/
def checkG41 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG41L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
