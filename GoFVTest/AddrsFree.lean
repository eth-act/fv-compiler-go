import Lean
import GoFV.Proof.Obj.EndToEnd
import GoFV.Gen.Check49
import GoFV.Gen.Check56
import GoFV.Gen.Check59
import GoFV.Gen.Check60
import GoFV.Gen.Check62
import GoFV.Gen.Check48

/-!
# The verified pipeline takes no address assignment (`docs/plans/proofs3.md` §8, item 6)

`verified_mach` holds under every admissible address assignment (`[Addrs]`), and its premise is the
verdict of `verifiedPipelineFull`. The checkers evaluate their constants at `Addrs.fixed`
(`Rules.opValC`, `Val.retypeC`, the static instances of `ruleOK`/`ruleOK1`/`blockOK1`), so the
pipeline takes no instance: the verdict `gofv-ssa-opt` computes is the premise under every instance,
the machine's among them. This module fails to build if a checker comes to read the assignment again
(an `[Addrs]` binder in the type of the pipeline, of a slice checker `GoFV.Gen.Check.checkG*` it
imports, or of `verified_mach`'s other checks: `liveCtx`, `retRegsOK`, `entryStoresOK`, `pendWins`,
`memTyL`, `needs48`, `checkObj`). So `verified_mach_atSP`'s checked premises at the machine layout
are the verdicts `gofv-ssa-opt --e2e` computes.
-/

open Lean Meta

/-- `ty` has an instance-implicit `Addrs` binder. -/
private def hasAddrsBinder (ty : Expr) : Bool := Id.run do
  let mut t := ty
  for _ in [0:256] do
    match t with
    | .forallE _ d b bi =>
      if bi == .instImplicit && d.isConstOf ``GoFV.SSA.Sem.Addrs then return true
      t := b
    | _ => return false
  return false

run_meta do
  let env ← getEnv
  let mut roots := #[``GoFV.Opt.verifiedPipeline, ``GoFV.Opt.verifiedPipelineFull,
    ``GoFV.Gen.Check.liveCtx, ``GoFV.Gen.Check.retRegsOK, ``GoFV.Gen.Check.entryStoresOK,
    ``GoFV.Gen.Check.pendWins, ``GoFV.Gen.Check.memTyL, ``GoFV.Gen.Check.needs48,
    ``GoFV.Asm.CheckObj.checkObj]
  for (n, ci) in env.constants.toList do
    if let (.str p s, .defnInfo _) := (n, ci) then
      if p == `GoFV.Gen.Check && s.startsWith "checkG" then roots := roots.push n
  unless [``GoFV.Gen.Check.checkG46, ``GoFV.Gen.Check.checkG47, ``GoFV.Gen.Check.checkG50,
      ``GoFV.Gen.Check.checkG51, ``GoFV.Gen.Check.checkG49, ``GoFV.Gen.Check.checkG52,
      ``GoFV.Gen.Check.checkG53, ``GoFV.Gen.Check.checkG54, ``GoFV.Gen.Check.checkG55,
      ``GoFV.Gen.Check.checkG56, ``GoFV.Gen.Check.checkG57, ``GoFV.Gen.Check.checkG48,
      ``GoFV.Gen.Check.checkG58, ``GoFV.Gen.Check.checkG59,
      ``GoFV.Gen.Check.checkG60, ``GoFV.Gen.Check.checkG61,
      ``GoFV.Gen.Check.checkG62].all roots.contains do
    throwError "AddrsFree: the slice checkers \
      checkG46/G47/G50/G51/G49/G52..G57/G48/G58/G59/G60/G61/G62 are not in scope"
  for n in roots do
    let some ci := env.find? n | throwError "AddrsFree: {n} not found"
    if hasAddrsBinder ci.type then
      throwError "AddrsFree: {n} takes an `Addrs` instance; the checkers must evaluate at \
        `Addrs.fixed` (docs/plans/proofs3.md §8, item 6)"
