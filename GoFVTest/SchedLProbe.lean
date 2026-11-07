import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.Schedule
import GoFVTest.SchedClass

/-!
# `lake exe schedl-probe [--jobs N] <dir>...`: `scheduleCheck` on the corpus

For every `schedule` section (input: the previous section), runs the Lean `schedule` on the
input and counts the sections whose input passes `check` (the hypothesis of
`schedule_refinesSchedLF`; the output's `check` is reported, not needed), those the pass changed,
and those `scheduleCheck` accepts (what `schedule_refinesSchedLF` covers), with how many of them
rely on `swapOK`'s `argPtr` (`ArgPtrsOK`) and `NilPtrsOK` cases; for the rejected ones the first
failing condition and the rejected functions by class (`GoFVTest.SchedClass`), and small accepted
witness candidates.
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ScheduleCheck GoFVTest.SchedClass

namespace GoFVTest.SchedLProbe

structure Cnt where
  secs : Nat := 0
  passErr : Nat := 0
  outUnchecked : Nat := 0
  checked : Nat := 0
  changed : Nat := 0
  accepted : Nat := 0
  acceptedChanged : Nat := 0
  /-- Accepted sections where some swap needs `swapOK`'s `argPtr` case. -/
  viaArgPtr : Nat := 0
  argPtrCands : Array (Nat × String) := #[]
  /-- Accepted sections where some swap needs `swapOK`'s `NilPtrsOK` case. -/
  viaNilPtr : Nat := 0
  /-- Accepted sections where some swap needs a memory through an `LDAR*` (`ldReach`). -/
  viaLdMem : Nat := 0
  whys : Std.HashMap String Nat := {}
  /-- An example function per rejection reason. -/
  whyEx : Std.HashMap String String := {}
  /-- Rejected functions by the classes of all their failing pairs (`pairClasses`). -/
  fnCls : Std.HashMap String Nat := {}
  fnClsEx : Std.HashMap String String := {}
  cands : Array (Nat × String) := #[]

def Cnt.merge (a b : Cnt) : Cnt :=
  { secs := a.secs + b.secs, passErr := a.passErr + b.passErr, checked := a.checked + b.checked
    outUnchecked := a.outUnchecked + b.outUnchecked
    changed := a.changed + b.changed, accepted := a.accepted + b.accepted
    acceptedChanged := a.acceptedChanged + b.acceptedChanged
    viaArgPtr := a.viaArgPtr + b.viaArgPtr, argPtrCands := a.argPtrCands ++ b.argPtrCands
    viaNilPtr := a.viaNilPtr + b.viaNilPtr, viaLdMem := a.viaLdMem + b.viaLdMem
    whys := b.whys.fold (fun m k n => m.insert k (m.getD k 0 + n)) a.whys
    whyEx := b.whyEx.fold (fun m k e => if m.contains k then m else m.insert k e) a.whyEx
    fnCls := b.fnCls.fold (fun m k n => m.insert k (m.getD k 0 + n)) a.fnCls
    fnClsEx := b.fnClsEx.fold (fun m k e => if m.contains k then m else m.insert k e) a.fnClsEx
    cands := a.cands ++ b.cands }

def listed (f : Func) : Nat :=
  f.blocks.foldl (fun n bid => n + (((f.block? bid).map (·.values.size)).getD 0)) 0

def doFile (pass : String) (path : System.FilePath) (c : Cnt) : IO Cnt := do
  let data ← IO.FS.readBinFile path
  let .ok e := parseExport data | return c
  let typs := (e.sections[0]?.bind (·.typs)).getD #[]
  let base : PassEnv :=
    { passName := pass, pkg := e.pkg, funcName := e.name, abi := e.abi
      nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs
      typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp, tables := {}
      frontend := e.frontendTables }
  let mut c := c
  let mut tables : Tables := {}
  for h : k in [0:e.sections.size] do
    let s := e.sections[k]
    let prev := tables
    tables := tables.addAll s.defs
    if k == 0 || s.pass.toStringLossy != pass then continue
    c := { c with secs := c.secs + 1 }
    let env := { base with tables := prev }
    let f := e.sections[k-1]!.func
    match schedulePass env f with
    | .error _ => c := { c with passErr := c.passErr + 1 }
    | .ok out =>
      let g := out.func
      let cf := check { tabs := prev, typs } f
      let cg := check { tabs := out.tables, typs } g
      if !cf.toBool then
        let msg := match cf with
          | .error m => ((m.splitOn ":").headD m).toList.take 60 |> String.ofList
          | .ok _ => ""
        let key := "input not checked: " ++ msg
        c := { c with whys := c.whys.insert key (c.whys.getD key 0 + 1) }
        continue
      if !cg.toBool then c := { c with outUnchecked := c.outUnchecked + 1 }
      let ch := g != f
      c := { c with checked := c.checked + 1, changed := c.changed + (if ch then 1 else 0) }
      if scheduleCheck prev f g then
        c := { c with accepted := c.accepted + 1
                      acceptedChanged := c.acceptedChanged + (if ch then 1 else 0) }
        if ch then
          c := { c with cands := c.cands.push (listed f, s!"{path} section {k - 1} -> {k}: {f.blocks.size} blocks, {listed f} values") }
        if relyArgPtrs prev f g then
          c := { c with viaArgPtr := c.viaArgPtr + 1
                        argPtrCands := c.argPtrCands.push (listed f, s!"{path} section {k - 1} -> {k}: {listed f} values") }
        if relyNilPtrs prev f g then c := { c with viaNilPtr := c.viaNilPtr + 1 }
        if relyLdMem prev f g then c := { c with viaLdMem := c.viaLdMem + 1 }
      else
        let w := why prev f g
        c := { c with whys := c.whys.insert w (c.whys.getD w 0 + 1)
                      whyEx := if c.whyEx.contains w then c.whyEx
                        else c.whyEx.insert w s!"{e.pkg}.{e.name} ({path})" }
        let fc := schedClass prev f g
        c := { c with fnCls := c.fnCls.insert fc (c.fnCls.getD fc 0 + 1)
                      fnClsEx := if c.fnClsEx.contains fc then c.fnClsEx
                        else c.fnClsEx.insert fc s!"{e.pkg}.{e.name} ({path})" }
  -- keep only the smallest candidates
  return { c with cands := (c.cands.qsort (fun a b => a.1 < b.1)).extract 0 20 }

def files (args : List String) : IO (Array System.FilePath) := do
  let mut fs := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      fs := fs ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else fs := fs.push p
  return fs.qsort (·.toString < ·.toString)

def main (args : List String) : IO UInt32 := do
  let (jobs, args) := match args with
    | "--jobs" :: n :: rest => (n.toNat?.getD 1, rest)
    | _ => (1, args)
  let fs ← files args
  let chunk := (fs.size + jobs - 1) / max jobs 1
  let mut tasks := #[]
  for j in [0:jobs] do
    let part := fs.extract (j * chunk) ((j + 1) * chunk)
    tasks := tasks.push (← IO.asTask (part.foldlM (fun c p => doFile "schedule" p c) {}))
  let mut c : Cnt := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok x => c := c.merge x
    | .error err => IO.eprintln s!"task error: {err}"; return 1
  IO.println s!"schedule: sections {c.secs}, pass errors {c.passErr}, input checked {c.checked} (output not checked {c.outUnchecked}), changed {c.changed}, scheduleCheck accepted {c.accepted} (changed {c.acceptedChanged}), rejected {c.checked - c.accepted}"
  IO.println s!"accepted through swapOK's argPtr case (ArgPtrsOK): {c.viaArgPtr}"
  IO.println s!"accepted through swapOK's NilPtrsOK case: {c.viaNilPtr}"
  IO.println s!"accepted through a memory of an LDAR* (ldReach): {c.viaLdMem}"
  for (_, l) in (c.argPtrCands.qsort (fun a b => a.1 < b.1)).extract 0 5 do
    IO.println s!"  {l}"
  IO.println "outside (first failing condition):"
  for (k, n) in c.whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
    if let some ex := c.whyEx.get? k then IO.println s!"      e.g. {ex}"
  IO.println "rejected functions by the classes of all their failing pairs:"
  for (k, n) in c.fnCls.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
    if let some ex := c.fnClsEx.get? k then IO.println s!"      e.g. {ex}"
  IO.println "witness candidates (accepted, changed), smallest first:"
  for (_, l) in (c.cands.qsort (fun a b => a.1 < b.1)).extract 0 20 do
    IO.println s!"  {l}"
  return 0

end GoFVTest.SchedLProbe

def main (args : List String) : IO UInt32 := GoFVTest.SchedLProbe.main args
