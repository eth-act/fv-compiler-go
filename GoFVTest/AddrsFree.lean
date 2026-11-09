import Lean
import GoFV.Proof.Obj.EndToEnd

/-!
# The verified pipeline takes no address assignment (`docs/plans/proofs3.md` §8, item 6)

`verified_mach` holds under every admissible address assignment (`[Addrs]`), and its premise is
the verdict of `verifiedPipelineFull`. The checkers evaluate their constants at `Addrs.fixed`
(`Rules.opValC`, `Val.retypeC`, the static instances of `ruleOK`/`ruleOK1`/`blockOK1`), so the
pipeline takes no instance: the verdict `gofv-ssa-opt` computes is the premise under every
instance, the machine's among them. This module fails to build if a checker comes to read the
assignment again (an `[Addrs]` binder in the type of a pipeline or slice checker).
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
  let roots := #[``GoFV.Opt.verifiedPipeline, ``GoFV.Opt.verifiedPipelineFull,
    ``GoFV.Gen.Check.checkG44]
  for n in roots do
    let some ci := env.find? n | throwError "AddrsFree: {n} not found"
    if hasAddrsBinder ci.type then
      throwError "AddrsFree: {n} takes an `Addrs` instance; the checkers must evaluate at \
        `Addrs.fixed` (docs/plans/proofs3.md §8, item 6)"
