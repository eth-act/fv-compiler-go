import GoFV.Gen.Check25

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G26: functions with no arm64 op (`docs/plans/proofs3.md` §4)

`checkG26 lc ps bstart g` is slice G25 (`GoFV/Gen/Check25.lean`) on a function that holds an arm64
op or block kind (`Func.lowered`). It also accepts some functions that went through `lower`
but hold none: empty bodies, and functions that return their register arguments, possibly after
a register move. `runLoc` runs such a function in Phase 1's mode: values are read with
`Val.retype`, not as registers (`Val.retypeL`), so G1–G25 reject them (`not lowered`). On these
functions G26 accepts:

* `MakeResult`, `InlMark` and `Copy` as G1 does (`vkind`): no code, or a `MOVD` between
  registers; the activation values as before;
* blocks of kind `Ret` only.

The rest is G25's check, with the value check `vkindNL`.
`GoFV/Proof/Gen/G26.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `v` emits in a function with no arm64 op, or why it is outside the slice: `MakeResult`,
`InlMark` and `Copy` as in G1, the activation values as in G25. -/
def vkindNL (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .MakeResult || v.op == .InlMark || v.op == .Copy then do
    let kd ← vkind lc v
    return match kd with
      | .entry => .entry
      | .none => .none
      | .prog sh => .prog (.ofShape sh)
  else if entryOp24 v.op then vkind25 lc g v
  else throw s!"v{v.id}: op {v.op.name} in a function with no arm64 op"

/-- Every block of the function has kind `Ret`. -/
def allRet (lc : LocCtx) : Bool :=
  lc.ctx.f.blocks.toList.all fun b => (lc.ctx.f.block? b).any (·.kind == .Ret)

/-- G26 on a function with no arm64 op: G25's check with the value check `vkindNL`, and `Ret`
blocks only. -/
def checkNL (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless allRet lc do throw "not lowered: a block other than Ret"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkindNL lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
  unless movdOK lc do throw "MOVDnop/MOVDreg: upper bits unknown"
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

/-- Slice G26 of the genssa validator (module doc): G25 on a function with an arm64 op,
`checkNL` on one without. -/
def checkG26 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then checkG25 lc ps bstart g else checkNL lc ps bstart g

end GoFV.Gen.Check
