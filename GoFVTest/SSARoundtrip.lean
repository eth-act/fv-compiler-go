import GoFV.SSA.Parse
import GoFV.SSA.Print
import GoFV.SSA.GoString

/-!
# `ssa-roundtrip`

Parses every `*.ssa` export file under the given directories (or files) and checks that
printing the result reproduces the file byte for byte. When `<file>.txt` exists (written with
`GOFV_SSA_GOTEXT=1`: per section a `pass <k> "<name>"` line and Go's `f.String()`), also checks
that `ExportFile.goString` reproduces it. The export numbers types by identity, so where Go
spells a type through an alias (`byte`, `rune`, `any`) the export keeps one spelling; such
files are counted as alias-only differences (texts equal after `normAliases`).

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

/-- Spells the predeclared aliases `byte`, `rune`, `any` as `uint8`, `int32`, `interface {}`
(whole identifiers only). -/
def normAliases (s : String) : String := Id.run do
  let isId (c : Char) := c.isAlphanum || c == '_'
  let mut out := ""
  let mut cur := ""
  for c in s.toList do
    if isId c then cur := cur.push c
    else
      out := out ++ (match cur with
        | "byte" => "uint8" | "rune" => "int32" | "any" => "interface {}" | x => x)
      cur := ""
      out := out.push c
  out ++ (match cur with
    | "byte" => "uint8" | "rune" => "int32" | "any" => "interface {}" | x => x)

structure Stats where
  files : Nat := 0
  failed : Nat := 0
  bytes : Nat := 0
  sections : Nat := 0
  blocks : Nat := 0
  values : Nat := 0
  gotext : Nat := 0
  readNs : Nat := 0
  parseNs : Nat := 0
  printNs : Nat := 0
  gotextFailed : Nat := 0
  gotextAlias : Nat := 0

def checkFile (path : System.FilePath) (st : Stats) : IO Stats := do
  let t0 ← IO.monoNanosNow
  let data ← IO.FS.readBinFile path
  let t1 ← IO.monoNanosNow
  let st := { st with files := st.files + 1, bytes := st.bytes + data.size,
                      readNs := st.readNs + (t1 - t0) }
  let r ← IO.lazyPure fun _ => parseExportExt data
  let t2 ← IO.monoNanosNow
  let st := { st with parseNs := st.parseNs + (t2 - t1) }
  match r with
  | .error e =>
    IO.eprintln s!"FAIL {path}: parse error: {e}"
    return { st with failed := st.failed + 1 }
  | .ok (e, x) =>
    let out ← IO.lazyPure fun _ => printExportExt e x
    let t3 ← IO.monoNanosNow
    let st := { st with
      printNs := st.printNs + (t3 - t2),
      sections := st.sections + e.sections.size,
      blocks := e.sections.foldl (fun n s => n + s.func.blocks.size) st.blocks,
      values := e.sections.foldl (fun n s =>
        s.func.blocks.foldl (fun n b => n + ((s.func.block? b).map (·.values.size)).getD 0) n)
        st.values }
    let mut st := st
    if out.toUTF8 != data then
      let orig := String.fromUTF8? data |>.getD "<not UTF-8>"
      IO.eprintln s!"FAIL {path}: printed text differs at {firstDiff orig out}"
      st := { st with failed := st.failed + 1 }
    let txt : System.FilePath := path.toString ++ ".txt"
    if ← txt.pathExists then
      let want ← IO.FS.readBinFile txt
      let mut got := ""
      for h : k in [0:e.sections.size] do
        got := got ++ s!"pass {k} {e.sections[k].pass.quote}\n" ++ e.goString k
      st := { st with gotext := st.gotext + 1 }
      if got.toUTF8 != want then
        let orig := String.fromUTF8? want |>.getD "<not UTF-8>"
        if normAliases orig == normAliases got then
          st := { st with gotextAlias := st.gotextAlias + 1 }
        else
          IO.eprintln s!"FAIL {txt}: f.String() differs (aliases normalized) at {firstDiff (normAliases orig) (normAliases got)}"
          st := { st with gotextFailed := st.gotextFailed + 1 }
    return st

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
    {st.sections} sections, {st.blocks} blocks, {st.values} values, {ms} ms \
    (read {st.readNs / 1000000}, parse {st.parseNs / 1000000}, print {st.printNs / 1000000}); \
    f.String(): {st.gotext} files, {st.gotextAlias} differ only in alias spellings, \
    {st.gotextFailed} failed"
  return if st.failed == 0 && st.gotextFailed == 0 && st.files > 0 then 0 else 1

end GoFVTest.SSARoundtrip

def main (args : List String) : IO UInt32 := GoFVTest.SSARoundtrip.main args
