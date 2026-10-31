import GoFV.Opt.Prove.IndVar

/-!
# prove: downward counting loops (`downward_counting_loop.go`)

`maybeRewriteLoopToDownwardCountingLoop(f, v)` (`docs/PASSES.md`, prove, T1): for an induction
variable used only by its comparison and increment, with a constant start and a non-constant
end defined outside the loop header, swap start and end (`SetArg`), swap the comparison's
arguments and make `nxt` count the other way (raw argument swaps and op changes, `Uses`
unchanged).
-/

namespace GoFV.Opt.Prove

open GoFV.SSA GoFV.SSA.Analysis

/-- The rewrite of `nxt`'s op (`Add` ↔ `Sub`). -/
def flipAddSub : Op → Option Op
  | .Add8 => some .Sub8 | .Add16 => some .Sub16 | .Add32 => some .Sub32 | .Add64 => some .Sub64
  | .Sub8 => some .Add8 | .Sub16 => some .Add16 | .Sub32 => some .Add32 | .Sub64 => some .Add64
  | _ => none

/-- Swap a value's first two arguments (no `Uses` change). -/
def swapArgs01 (f : Func) (v : ID) : Func :=
  f.modV v fun x => { x with args := (x.args.set! 0 x.args[1]!).set! 1 x.args[0]! }

/-- `maybeRewriteLoopToDownwardCountingLoop(f, v)`. -/
def maybeRewriteLoopToDownwardCountingLoop (cx : Ctx) (f : Func) (v : IndVar) :
    Except String Func := do
  let ind := f.getV v.ind
  let nxt := f.getV v.nxt
  if !(ind.uses == 2 && nxt.uses == 1) then return f
  let start := f.getV v.min
  let endv := f.getV v.max
  if !start.op.isGenericIntConst then return f
  if endv.op.isGenericIntConst then return f
  if endv.block == ind.block then return f
  let check := (f.getB (f.getB v.entry).preds[0]!.b).controls[0]!
  let neededRoom := -v.step
  let neededRoom := if neededRoom < 0 && v.flags &&& indVarMinExc == 1 then neededRoom + 1
    else neededRoom
  let neededRoom := if neededRoom > 0 && v.flags &&& indVarMaxInc == 0 then neededRoom - 1
    else neededRoom
  match (f.getV check).op with
  | .Less8 | .Less16 | .Less32 | .Less64 | .Leq8 | .Leq16 | .Leq32 | .Leq64 =>
    if (safeAdd start.auxInt neededRoom (cx.bits start.type)).isNone then return f
  | op => throw s!"prove: downward counting loop: unexpected comparator {op.name}"
  let some idxEnd := (f.getV check).args.idxOf? v.max | return f
  let some idxStart := ind.args.idxOf? v.min | return f
  let (sdom, f) := f.sdom
  if !sdom.isAncestorEq endv.block ind.block then return f
  let f := f.setArg check idxEnd v.min
  let f := f.setArg v.ind idxStart v.max
  let f := swapArgs01 f check
  let f := if (f.getV v.nxt).args[0]! != v.ind then swapArgs01 f v.nxt else f
  let some op := flipAddSub (f.getV v.nxt).op | throw "prove: downward counting loop: bad nxt"
  return f.modV v.nxt fun x => { x with op }

end GoFV.Opt.Prove
