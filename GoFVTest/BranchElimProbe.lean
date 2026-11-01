import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.BranchElim

/-!
# `lake exe branchelim-probe <dir>...`: branchelim's step checker and fragment on the corpus

For every `branchelim` section (input: the previous section), runs the Lean pass with each
rewrite instrumented: counts the inputs that pass `check` (the pass's gate), the rewrites
`elimIf`/`elimIfElse` propose and the step checker (`BranchElim.stepOK`) accepts or rejects,
and the functions branchelim changes.
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.BranchElim

namespace GoFVTest.BranchElimProbe

structure Counts where
  proposed : Nat := 0
  accepted : Nat := 0
  rejected : Nat := 0

/-- `branchelim`'s rounds, counting proposed and accepted rewrites. -/
def roundsCount (c : Ctx) (f : Func) (k : Counts) : Func × Counts := Id.run do
  let mut f := f
  let mut k := k
  for _ in [0:f.blocks.size + 1] do
    let mut change := false
    for b in f.blocks do
      let r1 := (elimIf c f b).toOption.join
      let r2 := if r1.isSome then none else (elimIfElse c f b).toOption.join
      match r1.orElse fun _ => r2 with
      | some g =>
        k := { k with proposed := k.proposed + 1 }
        if stepOK f g b then
          k := { k with accepted := k.accepted + 1 }
          f := g; change := true
        else
          k := { k with rejected := k.rejected + 1 }
      | none => pure ()
    if !change then break
  return (f, k)

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut inputs := 0
  let mut checked := 0
  let mut changed := 0
  let mut k : Counts := {}
  let mut shown := 0
  for path in files do
    let .ok data ← (IO.FS.readBinFile path).toBaseIO | continue
    let e ← match parseExport data with
      | .ok e => pure e
      | .error err => do IO.eprintln s!"PARSE {path}: {err}"; continue
    let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
    let mut tables : Tables := {}
    for h : j in [0:e.sections.size] do
      let s := e.sections[j]
      let prev := tables
      tables := tables.addAll s.defs
      if s.pass.toStringLossy != "branchelim" || j == 0 then continue
      let f0 := e.sections[j-1]!.func
      inputs := inputs + 1
      let env : PassEnv :=
        { passName := "branchelim", pkg := e.pkg, funcName := e.name, abi := e.abi,
          nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs,
          typeOrder := default, tables := prev }
      let (po, f) := f0.postorder
      let .ok c := ctxOf env f po | continue
      let ce : CheckEnv := { tabs := prev, typs }
      if !checkOK ce f then continue
      checked := checked + 1
      let r0 := k.rejected
      let (g, k') := roundsCount c f k
      k := k'
      if k.rejected != r0 && shown < 20 then
        IO.println s!"REJECT {path}"
        shown := shown + 1
      if g != f then changed := changed + 1
  IO.println s!"branchelim inputs {inputs}, passing check {checked}"
  IO.println s!"rewrites proposed {k.proposed}, accepted {k.accepted}, rejected {k.rejected}"
  IO.println s!"functions changed {changed}"
  return 0

end GoFVTest.BranchElimProbe

def main (args : List String) : IO UInt32 := GoFVTest.BranchElimProbe.main args
