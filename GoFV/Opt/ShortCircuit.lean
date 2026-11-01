import GoFV.Opt.Pass
import GoFV.Opt.Fuse.Basic
import GoFV.Opt.Fuse.PlainCheck
import GoFV.Opt.ShortCircuitCheck
import GoFV.Opt.ShortCircuitBlockCheck
import GoFV.SSA.ConstCache
import GoFV.SSA.Edges

/-!
# shortcircuit (`shortcircuit.go`)

1. Every boolean phi argument that is the control of the `If` predecessor it comes from becomes
   `ConstBool true`/`false` (`f.ConstBool(f.Config.Types.Bool, …)`, created lazily on first
   need, in `f.Blocks` × `b.Values` × `Args` order).
2. `fuse(f, fuseTypePlain | fuseTypeShortCircuit)`: per block (backwards), `fuseBlockPlain`
   then `shortcircuitBlock`, which redirects the predecessor that supplies a constant to the
   control phi straight to the taken successor, fixing other phis of the block with one of the
   five `shortcircuitPhiPlan` shapes (`ShortCircuitBlock.lean`).

Both steps are checked: `constPhiArgsChecked` (`cpaOK`) and `shortcircuitBlockChecked`
(`scOK`, a rejected rewrite is skipped).
-/

namespace GoFV.Opt.ShortCircuit

open GoFV.SSA GoFV.Opt.Fuse

/-! ## The pass -/

/-- Step 1 (`shortcircuit.go:20-50`). `boolT` is `f.Config.Types.Bool`, `isBool` is
`t.IsBoolean()`, `sameType` is `Type.Compare == CMPeq`. -/
def constPhiArgs (isBool : TypeRef → Bool) (sameType : TypeRef → TypeRef → Bool)
    (boolT : TypeRef) (f : Func) : Func := Id.run do
  let mut f := f
  let mut ct : Option ID := none
  let mut cf : Option ID := none
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      if x.op != .Phi || !isBool x.type then continue
      for i in [0:x.args.size] do
        let a := (f.getV v).args[i]!
        let e := (f.getB b).preds[i]!
        let pb := f.getB e.b
        if pb.kind != .If || pb.controls[0]! != a then continue
        if e.i == 0 then
          if ct.isNone then
            let (f', c) := f.constBool sameType boolT true
            f := f'; ct := some c
          f := f.setArg v i ct.get!
        else
          if cf.isNone then
            let (f', c) := f.constBool sameType boolT false
            f := f'; cf := some c
          f := f.setArg v i cf.get!
  return f

/-- `constPhiArgs`, checked once on the whole function (`cpaOK`; an error if it rejects). -/
def constPhiArgsChecked (tabs : Tables) (isBool : TypeRef → Bool)
    (sameType : TypeRef → TypeRef → Bool) (boolT : TypeRef) (f : Func) : Except String Func :=
  let g := constPhiArgs isBool sameType boolT f
  if cpaOK tabs f g then .ok g else .error "shortcircuit: constPhiArgs rewrite rejected"

/-- `fuseBlockPlain(b)` (checked in place, `Fuse.Plain.fuseBlockPlainChecked`) then
`shortcircuitBlock(b)` (checked, `shortcircuitBlockChecked`: a rejected rewrite is skipped). -/
def step (tabs : Tables) (f : Func) (b : ID) : Except String (Func × Bool) := do
  let (f, c1) ← Fuse.Plain.fuseBlockPlainChecked f b
  let (f, c2) := shortcircuitBlockChecked tabs f b
  pure (f, c2 || c1)

/-- `shortcircuit(f)`: its input if it fails the slim input check `wfDomCheck` (the checkers'
proofs assume a well-formed input with a valid dominator certificate; every corpus input
passes) or if a checker rejects a rewrite (`Fuse.orInput`). -/
def shortcircuit (ce : CheckEnv) (isBool : TypeRef → Bool) (sameType : TypeRef → TypeRef → Bool)
    (boolT : TypeRef) (f : Func) : Except String Func :=
  if !wfDomOK f then .ok f else
  Fuse.orInput f do
    let f ← constPhiArgsChecked ce.tabs isBool sameType boolT f
    fuseLoop (step ce.tabs) none roundFuel f

end GoFV.Opt.ShortCircuit

namespace GoFV.Opt

open GoFV.SSA

/-- The `short circuit` pass. -/
def shortcircuitPass : Pass := Pass.ofFunc fun env f => do
  let some boolT := env.typ? "Bool" | throw "shortcircuit: no typ.Bool"
  let isBool (t : TypeRef) : Bool := (env.type? t).map (·.kind) == some .BOOL
  ShortCircuit.shortcircuit { tabs := env.tables, typs := env.typs } isBool env.typeOrder.eq boolT f

end GoFV.Opt
