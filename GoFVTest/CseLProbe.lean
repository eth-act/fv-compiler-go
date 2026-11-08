import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.LoweredCSECheck

open scoped GoFV.SSA.Sem.Fixed

/-!
# `csel-probe`: does the lowered cse checker accept cse's results?

Runs `cseRw` on the input of every `lowered cse` instance of the given export files and counts
the inputs whose check passes, the inputs cse changes (substitutions, swapped commutative
arguments), and those where `CSEL.crel` (the hypothesis of `loweredCse_refinesL`) rejects the
result, with the first failing condition.
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.CSE

namespace GoFVTest.CseLProbe

def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + 1)

def opOf (f : Func) (x : ID) : String := ((f.value? x).map (·.op.name)).getD "?"

/-- The first condition of `CSEL.crel` that fails. -/
def why (tabs : Tables) (f g : Func) (rw : Array (Option ID)) : String := Id.run do
  if DomCert.cfgView g != DomCert.cfgView f then return "cfg"
  if g.ownAux != f.ownAux then return "ownAux"
  if g.lowered != f.lowered then return "lowered"
  if g.valueTab.size != f.valueTab.size then return "size"
  for bid in f.blocks do
    if !blockOK rw f g bid then return s!"block b{bid}"
  for bid in f.blocks do
    if !CSEL.auxOK f g bid then return s!"auxInt b{bid}"
  for x in List.range f.valueTab.size do
    if !valueOK rw f g x then return s!"value v{x} {opOf f x}"
  for x in List.range f.valueTab.size do
    if !CSEL.sxOK f g x then return s!"sx v{x} {opOf f x}"
  let c := DomCert.make f
  for x in List.range rw.size do
    if !CSEL.substOK tabs c rw f g x then
      let r := (rw.getD x none).getD 0
      let fx := f.getV x
      let fr := f.getV r
      let gx := g.getV x
      let gr := g.getV r
      let k :=
        if fr.op != fx.op || fr.aux != fx.aux || fr.auxInt != fx.auxInt then "opaux"
        else if !(CSEL.congr tabs f.lowered fx fr gx gr) then "congr"
        else if gx.args != gr.args then "args"
        else if !CSEL.substOp fx.op then "op"
        else "dom"
      return s!"subst-{k} v{x} {opOf f x}"
  for bid in f.blocks do
    if !schedOK true f g bid then return s!"sched b{bid}"
  return "?"

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut inst := 0
  let mut errs := 0
  let mut uncheckedIn := 0
  let mut uncheckedOut := 0
  let mut changed := 0
  let mut rejected := 0
  let mut substs := 0
  let mut swaps := 0
  let mut shown := 0
  let mut witness := 0
  let mut whys : Std.HashMap String Nat := {}
  let mut substOps : Std.HashMap String Nat := {}
  let mut swapOps : Std.HashMap String Nat := {}
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok e := parseExport data | continue
    let typs := (e.sections[0]?.bind (·.typs)).getD #[]
    let base : PassEnv :=
      { passName := "lowered cse", pkg := e.pkg, funcName := e.name, abi := e.abi
        nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs
        typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp, tables := {}
        frontend := e.frontendTables }
    let mut tables : Tables := {}
    for h : k in [0:e.sections.size] do
      let s := e.sections[k]
      let prev := tables
      tables := tables.addAll s.defs
      if k == 0 || s.pass.toStringLossy != "lowered cse" then continue
      inst := inst + 1
      let env := { base with tables := prev }
      let f := e.sections[k-1]!.func
      if (check { tabs := prev, typs } f).toBool == false then uncheckedIn := uncheckedIn + 1
      match cseCtx env with
      | .error _ => errs := errs + 1
      | .ok c =>
      match cseRw c f with
      | .error _ => errs := errs + 1
      | .ok (g, rw) =>
        if (check { tabs := prev, typs } g).toBool == false then uncheckedOut := uncheckedOut + 1
        let n := (rw.filter (·.isSome)).size
        substs := substs + n
        let mut sw := 0
        for x in List.range f.valueTab.size do
          if let (some fv, some gv) := (f.value? x, g.value? x) then
            if gv.args != fv.args.map (rep rw) then
              sw := sw + 1
              swapOps := bump swapOps fv.op.name
          if let some _ := rw.getD x none then substOps := bump substOps (opOf f x)
        swaps := swaps + sw
        if n > 0 || sw > 0 then changed := changed + 1
        if !CSEL.crel prev f g rw then
          rejected := rejected + 1
          let w := why prev f g rw
          whys := bump whys ((w.splitOn " ").head! ++ " " ++ ((w.splitOn " ").getLast!))
          if shown < 10 then
            IO.println s!"REJECT {path} {k}: {w}"
            shown := shown + 1
        else if n > 0 && witness < 5 && f.valueTab.size < 40 then
          IO.println s!"WITNESS {path} {k}: {f.valueTab.size} values, {n} substitutions"
          witness := witness + 1
  IO.println s!"lowered cse inputs {inst} (input failing check {uncheckedIn}, output failing check {uncheckedOut}, errors {errs}): cse changes {changed} ({substs} substitutions, {swaps} swapped argument pairs), checker rejects {rejected}"
  IO.println s!"rejections by first failing condition: {whys.toList}"
  IO.println s!"substitutions by op: {(substOps.toList.mergeSort (fun a b => a.2 ≥ b.2)).take 40}"
  IO.println s!"swaps by op: {swapOps.toList.mergeSort (fun a b => a.2 ≥ b.2)}"
  return 0

end GoFVTest.CseLProbe

def main (args : List String) : IO UInt32 := GoFVTest.CseLProbe.main args
