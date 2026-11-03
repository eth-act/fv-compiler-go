import GoFV.SSA.Parse
import GoFV.SSA.Check
import Std.Data.HashMap

/-!
# `ssa-check`

Runs the well-formedness checker `GoFV.SSA.check` (port of `checkFunc`, issue #8) on every
section of every `*.ssa` export file below the given directories and reports how many pass,
with a histogram of the failures (messages with IDs removed) and the first failures in full.

With `--mutate`, every passing section is also corrupted in a few small ways (`mutants`) and
each corruption must be rejected with the expected message: a non-vacuity self-test.

usage: `lake exe ssa-check [--mutate] <dir|file>...`; exit status 1 if any section fails or
any mutant is accepted.
-/

open GoFV.SSA

namespace GoFVTest.SSACheck

/-- A message without value/block/type IDs and numbers, for the histogram. -/
def msgKey (msg : String) : String :=
  let isRef (w : String) : Bool :=
    let w := ((w.dropWhile (fun c => c == '(' || c == '[')).takeWhile
      (fun c => c != ',' && c != ':' && c != ')' && c != ']')).toString
    w.length ≥ 1 && ((w.startsWith "v" || w.startsWith "b" || w.startsWith "t") &&
      w.length ≥ 2 && (w.drop 1).all Char.isDigit || w.all (fun c => c.isDigit || c == '-'))
  " ".intercalate ((msg.splitOn " ").map fun w => if isRef w then "_" else w)

structure Stats where
  files : Nat := 0
  parseFailed : Nat := 0
  sections : Nat := 0
  sectionsOk : Nat := 0
  filesOk : Nat := 0
  blocks : Nat := 0
  values : Nat := 0
  shown : Nat := 0
  fails : Std.HashMap String Nat := {}
  failsByPass : Std.HashMap String Nat := {}
  /-- Mutation self-test: mutants tried, rejected with the expected message. -/
  mutants : Nat := 0
  caught : Nat := 0

/-- Replace value `v` in `f`. -/
def setValue (f : Func) (v : Value) : Func := { f with valueTab := f.valueTab.set! v.id (some v) }

/-- Replace block `b` in `f`. -/
def setBlock (f : Func) (b : Block) : Func := { f with blockTab := f.blockTab.set! b.id (some b) }

/-- Small corruptions of a well-formed `f`, each with a substring of the message the checker
must reject it with: a wrong use count, an argument outside the function, a broken reverse
edge index, and (when there is a suitable pair) a use in the entry block of a value defined in
a later block, which does not dominate it. -/
def mutants (e : CheckEnv) (f : Func) : Array (String × Func) := Id.run do
  let vals := (f.blocks.flatMap fun b => ((f.block? b).map (·.values)).getD #[]).filterMap f.value?
  let mut out := #[]
  if let some v := vals[0]? then
    out := out.push ("uses", setValue f { v with uses := v.uses + 1 })
  -- (ops whose argument types `checkValue` inspects would reject it earlier, differently)
  let typeChecked : List Op := [.LocalAddr, .Addr, .NilCheck, .Load, .Store, .CondSelect, .AddPtr]
  if let some v := vals.find? (fun v => v.args.size > 0 && !typeChecked.contains v.op) then
    out := out.push ("is missing", setValue f { v with args := v.args.set! 0 (f.valueTab.size + 7) })
  if let some b := (f.blocks.filterMap f.block?).find? (·.preds.size > 0) then
    let p := b.preds[0]!
    out := out.push ("crosslinked", setBlock f { b with preds := b.preds.set! 0 { p with i := p.i + 1 } })
  if let some entry := f.block? f.entry then
    let ws := (entry.values.filterMap f.value?).filter fun w =>
      w.op != .Phi && w.op != .Addr && w.op != .LocalAddr && w.args.size > 0 &&
        !(f.value? w.args[0]!).any (e.isMemory ·.type)
    if let some w := ws[0]? then
      if let some a0 := f.value? w.args[0]! then
        let others := (f.blocks.filter (· != f.entry)).filterMap f.block?
        if let some b := others.find? (·.preds.size > 0) then
          if let some v := (b.values.filterMap f.value?).find?
              (fun v => v.op != .Phi && v.type == a0.type) then
            out := out.push ("dominate", setValue f { w with args := w.args.set! 0 v.id })
  return out

def checkFile (mutate : Bool) (path : System.FilePath) (st : Stats) : IO Stats := do
  let data ← IO.FS.readBinFile path
  let mut st := { st with files := st.files + 1 }
  match parseExportUntil "lower" data with
  | .error e =>
    IO.eprintln s!"PARSE {path}: {e}"
    return { st with parseFailed := st.parseFailed + 1 }
  | .ok ex =>
    let typs := (ex.sections[0]?.bind (·.typs)).getD #[]
    let mut tabs : Tables := {}
    let mut allOk := true
    for s in ex.sections do
      tabs := tabs.addAll s.defs
      let f := s.func
      let env : CheckEnv := { tabs, typs }
      st := { st with
        sections := st.sections + 1,
        blocks := st.blocks + f.blocks.size,
        values := f.blocks.foldl (fun n b => n + ((f.block? b).map (·.values.size)).getD 0)
          st.values }
      match check env f with
      | .ok () =>
        st := { st with sectionsOk := st.sectionsOk + 1 }
        if mutate then
          for (want, g) in mutants env f do
            st := { st with mutants := st.mutants + 1 }
            match check env g with
            | .error msg =>
              if (msg.splitOn want).length > 1 then st := { st with caught := st.caught + 1 }
              else if st.shown < 25 then
                IO.println s!"MUTANT {path} section {s.index} ({want}): rejected as {msg}"
                st := { st with shown := st.shown + 1 }
            | .ok () =>
              if st.shown < 25 then
                IO.println s!"MUTANT {path} section {s.index} ({want}): accepted"
                st := { st with shown := st.shown + 1 }
      | .error msg =>
        allOk := false
        let k := msgKey msg
        let p := s.pass.toStringLossy
        st := { st with fails := st.fails.insert k (st.fails.getD k 0 + 1),
                        failsByPass := st.failsByPass.insert p (st.failsByPass.getD p 0 + 1) }
        if st.shown < 25 then
          IO.println s!"FAIL {path} section {s.index} ({p}): {msg}"
          st := { st with shown := st.shown + 1 }
    if allOk then st := { st with filesOk := st.filesOk + 1 }
    return st

def ssaFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "ssa")).qsort (·.toString < ·.toString)
  else return #[p]

def main (args : List String) : IO UInt32 := do
  let mutate := args.contains "--mutate"
  let paths := args.filter (· != "--mutate")
  if paths.isEmpty then
    IO.eprintln "usage: ssa-check [--mutate] <dir|file>..."
    return 2
  let t0 ← IO.monoMsNow
  let mut st : Stats := {}
  for a in paths do
    for f in ← ssaFiles a do
      st ← checkFile mutate f st
  let ms := (← IO.monoMsNow) - t0
  IO.println s!"ssa-check: {st.files} files ({st.parseFailed} unparsable, {st.filesOk} pass in \
    every section), {st.sections} sections, {st.sectionsOk} pass, \
    {st.sections - st.sectionsOk} fail; {st.blocks} blocks, {st.values} values; {ms} ms"
  if mutate then
    IO.println s!"mutants: {st.mutants}, rejected with the expected message: {st.caught}"
  if !st.fails.isEmpty then
    IO.println "failures by message:"
    for (k, n) in (st.fails.toArray.qsort (fun a b => a.2 > b.2)) do
      IO.println s!"  {n} {k}"
    IO.println "failures by pass:"
    for (k, n) in (st.failsByPass.toArray.qsort (fun a b => a.2 > b.2)) do
      IO.println s!"  {n} {k}"
  let ok := st.sections == st.sectionsOk && st.parseFailed == 0 && st.files > 0 &&
    st.mutants == st.caught
  return if ok then 0 else 1

end GoFVTest.SSACheck

def main (args : List String) : IO UInt32 := GoFVTest.SSACheck.main args
