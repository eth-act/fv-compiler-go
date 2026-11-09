import GoFV.Gen.Check29

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G30: pointer conversions in functions with no arm64 op
(`docs/plans/proofs3.md` §4)

`checkG30 lc ps bstart g` is slice G29 (`GoFV/Gen/Check29.lean`) on a function that holds an arm64
op or block kind (`Func.lowered`). On one that holds none, `checkNL30` is G26's `checkNL` that also
accepts `Convert x mem` as G12 does (`convKind`): `x` and the value in one register of class 64,
the memory last; no code.

`GoFV/Proof/Gen/G30.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `v` emits in a function with no arm64 op (G30), or why it is outside the slice: `Convert`
as in G12, the rest as `vkindNL`. -/
def vkindNL30 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .Convert then convKind lc v else vkindNL lc g v

/-- G30 on a function with no arm64 op: `checkNL` with the value check `vkindNL30`. -/
def checkNL30 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless allRet lc do throw "not lowered: a block other than Ret"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkindNL30 lc g, tm := cx.termG3 }
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

/-- Slice G30 of the genssa validator (module doc): G29 on a function with an arm64 op,
`checkNL30` on one without. -/
def checkG30 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then checkG29 lc ps bstart g else checkNL30 lc ps bstart g

end GoFV.Gen.Check
