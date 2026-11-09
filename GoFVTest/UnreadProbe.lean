import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Proof.Pass.UnreadLRel

open scoped GoFV.SSA.Sem.Fixed

/-!
# `lake exe unread-probe <dir>...`: elim unread autos' fragment on the corpus

For every `elim unread autos` section (input: the previous section), runs the Lean pass on the
input and counts the sections whose input and output pass `check`, those the pass changes, and
those in `unreadLFrag` (`elimUnreadAutos_refinesL` covers them: unchanged, or accepted by the
checker `UnreadL.urel`). For changed sections the checker rejects, names the first failing
condition (an eliminated name that is forgeable, i.e. an ABIInternal `PPARAM` or an `addrconv`
`PAUTO`; a kept value outside `keptOK`, by op; …), and lists small accepted changed sections
(witness candidates).
-/

open GoFV.SSA GoFV.Opt GoFV.Proof.UnreadL

namespace GoFVTest.UnreadProbe

def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + 1)

/-- The first condition of `urel` that fails. -/
def why (tabs : Tables) (f g : Func) : String := Id.run do
  let E := names f g
  if DomCert.cfgView g != DomCert.cfgView f then return "cfg"
  if g.ownAux != f.ownAux then return "ownAux"
  if g.valueTab.size != f.valueTab.size then return "vsize"
  if g.lowered != f.lowered then return "lowered"
  if !E.all (fun n => !tabs.forgeable n) then return "forgeable name (PPARAM/addrconv)"
  if !E.all (fun n => !DAE.deferVar tabs n) then return "defer variable"
  if !f.blocks.all (blockOK f g) then return "block"
  for x in List.range f.valueTab.size do
    if !valueOK tabs f g E x then
      match f.value? x, g.value? x with
      | some fv, some gv =>
        if DSE.sameV fv gv then
          if fv.aux.any E.contains then return s!"kept value names an eliminated variable ({fv.op.name})"
          return s!"keptOK {fv.op.name}"
        if elimV fv gv then return "elim without name"
        return s!"value changed ({fv.op.name} -> {gv.op.name})"
      | _, _ => return "value missing"
  if !f.blocks.all (DSE.schedOK f g) then return "schedule roots"
  return "?"

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut secs := 0
  let mut errs := 0
  let mut checked := 0
  let mut changed := 0
  let mut frag := 0
  let mut fragChanged := 0
  let mut whys : Std.HashMap String Nat := {}
  let mut elimOpsH : Std.HashMap String Nat := {}
  let mut cands : Array (Nat × String) := #[]
  for path in files do
    let .ok data ← (IO.FS.readBinFile path).toBaseIO | continue
    let .ok e := parseExport data | continue
    let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
    let mut tables : Tables := {}
    for h : j in [0:e.sections.size] do
      let s := e.sections[j]
      let prev := tables
      tables := tables.addAll s.defs
      if s.pass.toStringLossy != "elim unread autos" || j == 0 then continue
      let f := e.sections[j-1]!.func
      secs := secs + 1
      let env : PassEnv :=
        { passName := "elim unread autos", pkg := e.pkg, funcName := e.name, abi := e.abi,
          nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs,
          typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp, tables := prev }
      let .ok out := elimUnreadAutosPass env f | errs := errs + 1; continue
      let g := out.func
      if !((check { tabs := prev, typs } f).toBool &&
          (check { tabs := out.tables, typs } g).toBool) then continue
      checked := checked + 1
      let inFrag := unreadLFrag env f
      if inFrag then frag := frag + 1
      if g == f then continue
      changed := changed + 1
      let el := (List.range f.valueTab.size).filter fun x => match f.value? x, g.value? x with
        | some fv, some gv => elimV fv gv
        | _, _ => false
      for x in el do
        if let some fv := f.value? x then elimOpsH := bump elimOpsH fv.op.name
      if inFrag then
        fragChanged := fragChanged + 1
        cands := cands.push (f.valueTab.size,
          s!"{path} section {j - 1}: {f.valueTab.size} values, {el.length} eliminated")
      else
        whys := bump whys (why prev f g)
  IO.println s!"sections {secs}, pass errors {errs}, input and output checked {checked}, changed {changed}"
  IO.println s!"unreadLFrag (of checked) {frag}; changed and accepted by urel {fragChanged} of {changed}"
  IO.println "eliminated ops (changed sections):"
  for (k, n) in elimOpsH.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  IO.println "changed sections outside the fragment (first failing condition):"
  for (k, n) in whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  IO.println "witness candidates (changed, accepted), smallest first:"
  for (_, l) in (cands.qsort (fun a b => a.1 < b.1)).extract 0 15 do
    IO.println s!"  {l}"
  return 0

end GoFVTest.UnreadProbe

def main (args : List String) : IO UInt32 := GoFVTest.UnreadProbe.main args
