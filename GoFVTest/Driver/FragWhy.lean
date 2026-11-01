import GoFV.Opt.Verified

/-!
# Why a deadcode or copyelim run is outside its fragment

`fragWhy name env f`: for a deadcode instance or `early phielim and copyelim` whose guard
(`deadGuard`, `copyGuard`) rejects `f`, the failing conditions in the guard's order, each with
the first offending value (`copyFrag`: size, `shape <op> <arg shape> ~ <value shape>` (a
`Stable` phi, `stableB`, is exempt), `copyNZ`, `acyclic`; `emptyFragB`: `empty <op> <shape>`),
followed by ` @` and the value and its type (`whyKey` drops that part). `gofv-ssa-opt --check
--verified` reports them as a histogram (`fragment conditions`) and lists examples as
`FRAGMENT` reports.
-/

namespace GoFVTest.Driver.FragWhy

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.CopyElim GoFV.Proof.Dead

/-- The constructor of a shape (sizes and element sizes dropped). -/
def shapeName : Ty → String
  | .int w => s!"int{w.bits}"
  | .bool => "bool"
  | .mem => "mem"
  | .tuple _ => "tuple"
  | .other => "other"
  | .ptr _ => "ptr"
  | .agg _ _ => "agg"
  | .blob _ => "blob"
  | .empty => "empty"
  | .opaque _ => "opaque"
  | .str => "str"
  | .slice _ => "slice"

/-- The listed values of `f` in block order. -/
def listed (f : Func) : Array ID :=
  f.blocks.foldl (fun acc bid => acc ++ (((f.block? bid).map (·.values)).getD #[])) #[]

/-- Why `copyFrag tabs f` fails (the first offending value), `none` if it holds. -/
def copyWhy (tabs : Tables) (f : Func) : Option String := Id.run do
  if !decide (f.valueTab.size ≤ f.vidLast + 1) then return some "size"
  for x in listed f do
    let some v := f.value? x | continue
    if v.op == .Copy || (v.op == .Phi && !stableB f v) then
      for a in v.args do
        match f.value? a with
        | none => return some s!"shape {v.op} undefined arg @v{x}"
        | some w =>
          if !retypeEqB (tabs.ty w.type) (tabs.ty v.type) then
            return some s!"shape {v.op} {shapeName (tabs.ty w.type)} ~ {shapeName (tabs.ty v.type)} @v{x} t{v.type}, arg v{a} t{w.type}"
    if v.op == .Copy && zeroSizeB tabs v.type then
      return some s!"copyNZ {shapeName (tabs.ty v.type)} @v{x} t{v.type}"
    if !chainEnds f.value? (f.valueTab.size + 1) x then return some s!"acyclic @v{x}"
  return none

/-- Why `emptyFragB tabs f` fails (the first zero-size tree value), `none` if it holds. -/
def emptyWhy (tabs : Tables) (f : Func) : Option String := Id.run do
  let C := GoFV.SSA.DomCert.make f
  for bid in f.blocks do
    if !C.inTree bid then continue
    let some fb := f.block? bid | continue
    for x in fb.values do
      let some v := f.value? x | continue
      if isOkTrue (zeroSizeAggregate tabs v.type) then
        return some s!"empty {v.op} {shapeName (tabs.ty v.type)} @v{x} t{v.type}"
  return none

/-- A condition without its value location. -/
def whyKey (s : String) : String := (s.splitOn " @").headD s

/-- The failing conditions of `deadFragB tabs f`, in its order. -/
def deadWhy (tabs : Tables) (f : Func) : Array String := Id.run do
  let mut out := #[]
  if !f.blocks.all (· ≤ f.bidLast) then out := out.push "bid"
  if !firstTwoB f then out := out.push "firstTwo"
  let f1' := edgesG false f
  let f1 := edgesG true f
  if let some w := copyWhy tabs f1' then out := out.push s!"copyFrag f1': {w}"
  if let some w := copyWhy tabs f1 then out := out.push s!"copyFrag f1: {w}"
  if let some w := emptyWhy tabs f1' then out := out.push s!"emptyFrag f1': {w}"
  if !(DomCert.check f1').toBool then out := out.push "domCert f1'"
  match copyelim tabs f1 with
  | .ok g => if !(DomCert.check g).toBool then out := out.push "domCert f2"
  | .error _ => pure ()
  return out

/-- The failing fragment conditions of pass `name` on `f` (empty for other passes and for
inputs in the fragment). -/
def fragWhy (name : String) (env : PassEnv) (f : Func) : Array String :=
  if name.endsWith "deadcode" then deadWhy env.tables f
  else if name == "early phielim and copyelim" then
    (#[copyWhy env.tables f |>.map (s!"copyFrag: " ++ ·),
       emptyWhy env.tables f |>.map (s!"emptyFrag: " ++ ·)]).filterMap id
  else #[]

end GoFVTest.Driver.FragWhy
