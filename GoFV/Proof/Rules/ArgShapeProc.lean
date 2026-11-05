import Lean
import GoFV.Proof.Rules.Den

/-!
# `reduceArgShapeOk`

A dsimproc for `argShapeOk` (`Den.lean`) at an op constructor, for the rule tactics
(`Tactic.lean`) and the rewrite validator's proofs (`GoFV/Proof/Pass/RewriteTermNat.lean`).
-/

namespace GoFV.Proof.Rules

open Lean Meta

/-- `argShapeOk op ty i t` at an op constructor: its arm. Unfolding `argShapeOk` by `simp`
instead generates its 64 equations and its matcher's splitter privately, once per theorem
(asynchronous elaboration): 88 s of FloatRules' 300 s of profiled time at f53b580. -/
dsimproc reduceArgShapeOk (argShapeOk _ _ _ _) := fun e => do
  unless e.isAppOfArity ``argShapeOk 4 do return .continue
  let some c := (e.getArg! 0).constName? | return .continue
  unless (← getEnv).isConstructor c do return .continue
  let some e1 ← delta? e | return .continue
  let e1 := e1.headBeta
  let some m := e1.getAppFn.constName? | return .continue
  let e2 ← whnfCore e1
  if e2.getAppFn.constName? == some m then return .continue
  return .done e2

end GoFV.Proof.Rules
