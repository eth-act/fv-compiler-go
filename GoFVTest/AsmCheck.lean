import GoFV.Asm.Parse
import GoFV.Asm.Print

/-!
# `asm-check`

Parses every `*.prog` file (`gofv-prog 1`, `docs/contracts/export.md`) under the given
directories (or files) and checks that printing the result reproduces the file byte for byte,
and that the exporter wrote no `warn` line. With `--hist FILE`, also writes the `oplook`
histogram of the assembled Progs (asm section, `Optab ≠ 0`): one line per distinct
(optab index, opcode, operand types and classes, `Scond`) with its count, most frequent first,
and a summary of the distinct optab entries and opcodes (`docs/PASSES3.md` §4 D4).

usage: `lake exe asm-check [--hist FILE] <dir|file>...`; exit status 1 if any file fails.
-/

open GoFV.Asm

namespace GoFVTest.AsmCheck

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
  warned : Nat := 0
  bytes : Nat := 0
  prog0 : Nat := 0
  asm : Nat := 0
  textBytes : Nat := 0
  hist : Std.HashMap String Nat := {}
  optabs : Std.HashMap Nat Nat := {}
  opcodes : Std.HashMap String Nat := {}

/-- `<type>:<class>` of an operand. -/
def cls (a : Addr) : String := s!"{a.type.name}:{a.cls}"

def histKey (p : Prog) : String :=
  let rest := ",".intercalate (p.rest.toList.map fun (k, a) => s!"{k}:{cls a}")
  s!"{p.optab} {p.as.name} {cls p.from_} {if p.reg != 0 then "reg" else "-"} \
    {if rest.isEmpty then "-" else rest} {cls p.to} {p.scond}"

def checkFile (path : System.FilePath) (hist : Bool) (st : Stats) : IO Stats := do
  let data ← IO.FS.readBinFile path
  let st := { st with files := st.files + 1, bytes := st.bytes + data.size }
  match parseProgFile data with
  | .error e =>
    IO.eprintln s!"FAIL {path}: parse error: {e}"
    return { st with failed := st.failed + 1 }
  | .ok f =>
    let mut st := { st with prog0 := st.prog0 + f.prog0.progs.size,
                            asm := st.asm + f.asm.progs.size,
                            textBytes := st.textBytes + f.asm.text.size }
    let out := printProgFile f
    if out.toUTF8 != data then
      let orig := String.fromUTF8? data |>.getD "<not UTF-8>"
      IO.eprintln s!"FAIL {path}: printed text differs at {firstDiff orig out}"
      st := { st with failed := st.failed + 1 }
    let ws := f.frame.warns ++ f.prog0.warns ++ f.asm.warns
    if !ws.isEmpty then
      IO.eprintln s!"WARN {path}: {ws.toList.map (·.toStringLossy)}"
      st := { st with warned := st.warned + 1 }
    if hist then
      for p in f.asm.progs do
        if p.optab != 0 then
          st := { st with
            hist := st.hist.alter (histKey p) (some <| ·.getD 0 + 1),
            optabs := st.optabs.alter p.optab (some <| ·.getD 0 + 1),
            opcodes := st.opcodes.alter p.as.name (some <| ·.getD 0 + 1) }
    return st

def progFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "prog")).qsort (·.toString < ·.toString)
  else return #[p]

def main (args : List String) : IO UInt32 := do
  let (histOut, paths) := match args with
    | "--hist" :: f :: rest => (some f, rest)
    | rest => (none, rest)
  if paths.isEmpty then
    IO.eprintln "usage: asm-check [--hist FILE] <dir|file>..."
    return 2
  let t0 ← IO.monoMsNow
  let mut st : Stats := {}
  for a in paths do
    for f in ← progFiles a do
      st ← checkFile f histOut.isSome st
  let ms := (← IO.monoMsNow) - t0
  IO.println s!"asm-check: {st.files} files, {st.failed} failed, {st.warned} with warnings, \
    {st.bytes} bytes, {st.prog0} prog0 Progs, {st.asm} asm Progs, {st.textBytes} text bytes, \
    {ms} ms"
  if let some h := histOut then
    let rows := st.hist.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
    let total := rows.foldl (· + ·.2) 0
    let mut out := s!"# oplook histogram (asm-check): {total} assembled Progs, \
      {st.optabs.size} distinct optab entries, {st.opcodes.size} distinct opcodes, \
      {rows.size} distinct shapes\n\
      # count optab opcode from reg rest to scond\n"
    for (k, c) in rows do out := out ++ s!"{c} {k}\n"
    out := out ++ "# optab entries by count: count optab\n"
    for (k, c) in st.optabs.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)) do
      out := out ++ s!"optab {c} {k}\n"
    out := out ++ "# opcodes by count: count opcode\n"
    for (k, c) in st.opcodes.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)) do
      out := out ++ s!"opcode {c} {k}\n"
    IO.FS.writeFile h out
  return if st.failed == 0 && st.warned == 0 && st.files > 0 then 0 else 1

end GoFVTest.AsmCheck

def main (args : List String) : IO UInt32 := GoFVTest.AsmCheck.main args
