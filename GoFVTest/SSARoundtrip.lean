import GoFV.SSA.Parse
import GoFV.SSA.Print

/-!
# `ssa-roundtrip`

Parses every `*.ssa` export file under the given directories (or files) and checks that
printing the result reproduces the file byte for byte.

usage: `lake exe ssa-roundtrip <dir|file>...`; exit status 1 if any file fails.
-/

open GoFV.SSA

namespace GoFVTest.SSARoundtrip

/-- First line where `a` and `b` differ, with both versions. -/
def firstDiff (a b : String) : String := Id.run do
  let la := a.splitOn "\n"
  let lb := b.splitOn "\n"
  for k in [0:max la.length lb.length] do
    let x := la.getD k "<eof>"
    let y := lb.getD k "<eof>"
    if x != y then return s!"line {k+1}:\n    file:    {x}\n    printed: {y}"
  return "no difference"

structure Stats where
  files : Nat := 0
  failed : Nat := 0
  bytes : Nat := 0
  sections : Nat := 0
  blocks : Nat := 0
  values : Nat := 0

def checkFile (path : System.FilePath) (st : Stats) : IO Stats := do
  let data ← IO.FS.readBinFile path
  let st := { st with files := st.files + 1, bytes := st.bytes + data.size }
  match parseExport data with
  | .error e =>
    IO.eprintln s!"FAIL {path}: parse error: {e}"
    return { st with failed := st.failed + 1 }
  | .ok e =>
    let out := printExport e
    let st := { st with
      sections := st.sections + e.sections.size,
      blocks := e.sections.foldl (fun n s => n + s.func.blocks.size) st.blocks,
      values := e.sections.foldl (fun n s =>
        s.func.blocks.foldl (fun n b => n + ((s.func.block? b).map (·.values.size)).getD 0) n)
        st.values }
    if out.toUTF8 == data then
      return st
    let orig := String.fromUTF8? data |>.getD "<not UTF-8>"
    IO.eprintln s!"FAIL {path}: printed text differs at {firstDiff orig out}"
    return { st with failed := st.failed + 1 }

def ssaFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "ssa")).qsort (·.toString < ·.toString)
  else return #[p]

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: ssa-roundtrip <dir|file>..."
    return 2
  let t0 ← IO.monoMsNow
  let mut st : Stats := {}
  for a in args do
    for f in ← ssaFiles a do
      st ← checkFile f st
  let ms := (← IO.monoMsNow) - t0
  IO.println s!"ssa-roundtrip: {st.files} files, {st.failed} failed, {st.bytes} bytes, \
    {st.sections} sections, {st.blocks} blocks, {st.values} values, {ms} ms"
  return if st.failed == 0 && st.files > 0 then 0 else 1

end GoFVTest.SSARoundtrip

def main (args : List String) : IO UInt32 := GoFVTest.SSARoundtrip.main args
