import GoFV.SSA.Parse
import GoFV.Opt.NilCheckLate
import GoFV.Opt.NilLateCheck
import GoFV.Proof.CheckFacts
import GoFVTest.Parity.Compare

open scoped GoFV.SSA.Sem.Fixed

/-!
# `lake exe nillate-probe [--jobs n] <dir>...`: `nilLateB` on the corpus

For every `late nilcheck` section (input: the previous section), runs the Lean
`nilcheckelim2Pass` on the input and counts: sections, pass errors, input/output `check`, the
sections where the pass removes a check, and those `nilLateB` (the hypothesis of
`nilcheckelim2_refinesSched`) accepts; reports the first failing condition by count (for a
removed check, why its segment fails: the op of the offending value) and small witness
candidates.
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.NilLate GoFV.Proof GoFVTest.Parity

namespace GoFVTest.NilLateProbe

/-- Why `segB` fails (mirrors `segB`). -/
def segWhy (f : Func) (rm : ID → Bool) (blk : Array ID) (p mm : ID) :
    List ID → List ID → String
  | _, [] => "no faulting value in the block"
  | avail, x :: xs =>
    if rm x then segWhy f rm blk p mm avail xs else
    match f.value? x with
    | none => "value missing"
    | some w =>
      if !argsAvailB blk avail w then s!"argument not available ({w.op.name})"
      else if faultsOnB w p mm then "ok"
      else if !safeOpB w mm then
        if w.args.any (· == p) && (w.op.faultOnNilArg0 || w.op.faultOnNilArg1) then
          s!"faulting value not accepted ({w.op.name}, auxType {repr w.op.auxType})"
        else s!"unsafe value between ({w.op.name})"
      else if x == p || x == mm then "between value is p or mm"
      else segWhy f rm blk p mm (x :: avail) xs

def blockWhy (f : Func) (rm : ID → Bool) (blk : Array ID) : List ID → List ID → Option String
  | _, [] => none
  | pre, x :: xs =>
    if rm x && !removedB f rm blk x pre xs then
      match f.value? x with
      | some v =>
        if v.op != .ARM64LoweredNilCheck then some s!"removed a non-check ({v.op.name})"
        else match v.args.toList with
          | [p, mm] => some (segWhy f rm blk p mm pre xs)
          | _ => some "check arity"
      | none => some "removed value missing"
    else blockWhy f rm blk (x :: pre) xs

def why (tabs : Tables) (f g : Func) : Option String := Id.run do
  let rs := removedSet f g
  let rm : ID → Bool := fun i => rs.getD i false
  if !shapeB f g rm then return some "shape"
  if !unusedB f rm then return some "a removed value is used"
  let cS := Ctx.makeSched tabs f
  let cT := Ctx.makeSched tabs g
  for bid in f.blocks do
    if let some b := f.block? bid then
      if let some o := (cS.sched[bid]?).join then
        if o.toList != orderOf f b then return some "source schedule is not the block order"
        if (cT.sched[bid]?).join != some ((orderOf f b).filter (!rm ·)).toArray then
          return some "target schedule is not the source's without the removed values"
        if let some r := blockWhy f rm b.values (phisOf f b) (orderOf f b) then
          return some s!"redundant: {r}"
  return none

structure Cnt where
  secs : Nat := 0
  errors : Nat := 0
  inFails : Nat := 0
  outFails : Nat := 0
  checked : Nat := 0
  changed : Nat := 0
  removed : Nat := 0
  accepted : Nat := 0
  acceptedChanged : Nat := 0
  deriving Inhabited

def Cnt.add (a b : Cnt) : Cnt :=
  { secs := a.secs + b.secs, errors := a.errors + b.errors, inFails := a.inFails + b.inFails
    outFails := a.outFails + b.outFails, checked := a.checked + b.checked
    changed := a.changed + b.changed, removed := a.removed + b.removed
    accepted := a.accepted + b.accepted, acceptedChanged := a.acceptedChanged + b.acceptedChanged }

structure Stats where
  parseErrors : Nat := 0
  bugs : Nat := 0
  cnt : Cnt := {}
  whys : Std.HashMap String Nat := {}
  examples : Std.HashMap String String := {}
  cands : Array (Nat × String) := #[]
  deriving Inhabited

def Stats.merge (a b : Stats) : Stats :=
  { parseErrors := a.parseErrors + b.parseErrors, bugs := a.bugs + b.bugs, cnt := a.cnt.add b.cnt
    whys := b.whys.fold (fun m k n => m.insert k (m.getD k 0 + n)) a.whys
    examples := b.examples.fold (fun m k e => if m.contains k then m else m.insert k e) a.examples
    cands := a.cands ++ b.cands }

def listedCount (f : Func) : Nat :=
  f.blocks.foldl (fun n bid => n + (((f.block? bid).map (·.values.size)).getD 0)) 0

def checkFile (path : System.FilePath) (st : Stats) : IO Stats := do
  let data ← IO.FS.readBinFile path
  match parseExportExt data with
  | .error _ => return { st with parseErrors := st.parseErrors + 1 }
  | .ok (e, ext) =>
    let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
    let base : PassEnv :=
      { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
        pgohot := e.pgohot, config := e.config, typs, typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
        tables := {}, frontend := e.frontendTables, ptrCache := ptrCacheFn e.ptrCache
        typeLink := typeLinkFn e.typeLink }
    let mut st := st
    let mut tables : Tables := {}
    let mut prev : Tables := {}
    for h : k in [0:e.sections.size] do
      let s := e.sections[k]
      prev := tables
      tables := tables.addAll s.defs
      if k == 0 then continue
      let name := s.pass.toStringLossy
      if name != "late nilcheck" then continue
      let env := { base with passName := name, tables := prev
                             zvar := zvarFn e.sections[k-1]!.zvar
                             dclLen := (ext.dclLen? (k-1)).getD 0 }
      let f := e.sections[k-1]!.func
      let mut c : Cnt := { secs := 1 }
      match nilcheckelim2Pass env f with
      | .error _ => c := { c with errors := 1 }
      | .ok out =>
        let g := out.func
        let ce : CheckEnv := { tabs := prev, typs }
        let okf := (check ce f).toBool
        let okg := (check ce g).toBool
        c := { c with inFails := if okf then 0 else 1, outFails := if okf && !okg then 1 else 0 }
        if okf then
          let nrm := (removedSet f g).foldl (fun n b => if b then n + 1 else n) 0
          let changed := nrm > 0
          let acc := nilLateB out.tables f g
          let w := why out.tables f g
          if acc != w.isNone then st := { st with bugs := st.bugs + 1 }
          c := { c with checked := 1, changed := if changed then 1 else 0, removed := nrm
                        accepted := if acc then 1 else 0
                        acceptedChanged := if acc && changed then 1 else 0 }
          if let some r := w then
            st := { st with whys := st.whys.insert r (st.whys.getD r 0 + 1) }
            if !st.examples.contains r then
              st := { st with examples := st.examples.insert r s!"{path} section {k - 1}" }
          if acc && changed && listedCount f < 40 then
            st := { st with cands := st.cands.push (listedCount f, s!"{path} section {k - 1} ({nrm} removed)") }
      st := { st with cnt := st.cnt.add c }
    return st

def main (args : List String) : IO UInt32 := do
  let (jobs, paths) := match args with
    | "--jobs" :: n :: rest => (max (n.toNat?.getD 1) 1, rest)
    | rest => (1, rest)
  let mut files := #[]
  for a in paths do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let tasks ← (List.range jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st : Stats := {}
    for h : i in [0:files.size] do
      if i % jobs == j then st ← checkFile files[i] st
    return st
  let mut st : Stats := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 2
  let x := st.cnt
  IO.println s!"files {files.size}, parse errors {st.parseErrors}, probe bugs {st.bugs}"
  IO.println s!"late nilcheck: sections {x.secs}, pass errors {x.errors}, input fails check {x.inFails}, output (only) fails check {x.outFails}, input checked {x.checked}, changed {x.changed} ({x.removed} checks removed), nilLateB accepts {x.accepted} (changed {x.acceptedChanged}), rejects {x.checked - x.accepted}"
  IO.println "rejections (first failing condition):"
  for (k, n) in st.whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}   e.g. {st.examples.getD k ""}"
  IO.println "witness candidates (changed, accepted), smallest first:"
  for (sz, l) in ((st.cands.qsort (fun a b => a.1 < b.1)).extract 0 16) do
    IO.println s!"  {sz} values: {l}"
  return if st.bugs == 0 then 0 else 1

end GoFVTest.NilLateProbe

def main (args : List String) : IO UInt32 := GoFVTest.NilLateProbe.main args
