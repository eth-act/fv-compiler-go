import GoFV.Asm.CheckObj
import GoFV.Asm.Flush
import GoFV.Asm.Parse

open scoped GoFV.SSA.Sem.Fixed

/-!
# `obj-check`: coverage of the assembler validator (`docs/plans/proofs3.md` §2, row D2–D5)

For every `*.prog` file under the given directories, runs the assembler port (`GoFV.Asm.flush`,
as `asm-parity`) on the `prog0` section and the validator `GoFV.Asm.CheckObj.checkObj` on the P0
Prog list, the function's register-argument spills and the port's output (text bytes,
relocations, final Prog list as the PC hint). Counts accepted functions and P0 Progs; rejections
are grouped by reason with numbers replaced by `#`. With `--accept FILE` (the accepted list of
`gen-check --table`), also counts the accepted functions among the slice's.

usage: `lake exe obj-check [--jobs N] [--accept FILE] [--table FILE] <dir|file>...`; exit status 1
on a parse or port error.
-/

open GoFV.Asm GoFV.Asm.CheckObj

namespace GoFVTest.ObjCheck

structure Stats where
  files : Nat := 0
  errors : Nat := 0
  accepted : Nat := 0
  progs : Nat := 0
  acceptedProgs : Nat := 0
  slice : Nat := 0
  sliceAccepted : Nat := 0
  reasons : Std.HashMap String (Nat × String) := {}

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, errors := a.errors + b.errors, accepted := a.accepted + b.accepted,
    progs := a.progs + b.progs, acceptedProgs := a.acceptedProgs + b.acceptedProgs,
    slice := a.slice + b.slice, sliceAccepted := a.sliceAccepted + b.sliceAccepted,
    reasons := b.reasons.fold (fun m k (n, ex) =>
      m.insert k ((m.getD k (0, ex)).1 + n, (m.getD k (0, ex)).2)) a.reasons }

/-- The reason with numbers replaced. -/
def classOf (msg : String) : String := Id.run do
  let mut out := ""
  let mut prevDigit := false
  for c in msg.toList do
    if c.isDigit then
      unless prevDigit do out := out.push '#'
      prevDigit := true
    else
      out := out.push c
      prevDigit := false
  return out.take 160 |>.toString

def Stats.reject (st : Stats) (msg ex : String) : Stats :=
  let k := classOf msg
  { st with reasons := st.reasons.insert k ((st.reasons.getD k (0, ex)).1 + 1,
      (st.reasons.getD k (0, ex)).2) }

def checkFile (slice : Std.HashSet String) (path : System.FilePath) (st : Stats) : IO Stats := do
  let st := { st with files := st.files + 1 }
  let inSlice := slice.contains path.toString
  let st := if inSlice then { st with slice := st.slice + 1 } else st
  let data ← IO.FS.readBinFile path
  match parseProgFile data with
  | .error e => return { (st.reject s!"parse: {e}" path.toString) with errors := st.errors + 1 }
  | .ok pf =>
  match flush pf with
  | .error e => return { (st.reject s!"port: {e}" path.toString) with errors := st.errors + 1 }
  | .ok out =>
  let ps := pf.prog0.progs
  let st := { st with progs := st.progs + ps.size }
  let obj : ObjIn := { text := out.st.textP, relocs := out.st.textR, progs := out.progs }
  match checkObj ps pf.prog0.fn.spills obj with
  | .ok _ =>
    let st := { st with accepted := st.accepted + 1, acceptedProgs := st.acceptedProgs + ps.size }
    return if inSlice then { st with sliceAccepted := st.sliceAccepted + 1 } else st
  | .error msg => return st.reject msg s!"{path}: {msg}"

def progFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "prog")).qsort (·.toString < ·.toString)
  else return #[p]

def pct (a b : Nat) : String :=
  if b == 0 then "-" else
  let x := a * 10000 / b
  s!"{x / 100}.{if x % 100 < 10 then "0" else ""}{x % 100}%"

def main (args : List String) : IO UInt32 := do
  let rec parse : List String → Nat × Option String × Option String × Array String →
      Option (Nat × Option String × Option String × Array String)
    | [], o => some o
    | "--jobs" :: n :: rest, (_, a, t, ps) => n.toNat?.bind fun n => parse rest (max n 1, a, t, ps)
    | "--accept" :: f :: rest, (j, _, t, ps) => parse rest (j, some f, t, ps)
    | "--table" :: f :: rest, (j, a, _, ps) => parse rest (j, a, some f, ps)
    | p :: rest, (j, a, t, ps) => parse rest (j, a, t, ps.push p)
  let some (jobs, accept, table, paths) := parse args (1, none, none, #[])
    | IO.eprintln "usage: obj-check [--jobs N] [--accept FILE] [--table FILE] <dir|file>..."; return 2
  let slice : Std.HashSet String ← match accept with
    | some f => do
      let s ← IO.FS.readFile f
      pure ((s.splitOn "\n").filterMap (fun l =>
        if l.startsWith "- " then some ((l.drop 2).takeWhile (· != ' ')).toString else none)
        |>.foldl (·.insert ·) {})
    | none => pure {}
  let mut files := #[]
  for p in paths do files := files ++ (← progFiles p)
  let tasks ← (List.range jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st : Stats := {}
    for h : i in [0:files.size] do
      if i % jobs == j then st ← checkFile slice files[i] st
    return st
  let mut st : Stats := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 1
  let mut out := s!"| functions | accepted | share | P0 Progs | in accepted functions |\n| ---: | ---: | ---: | ---: | ---: |\n"
  out := out ++ s!"| {st.files} | {st.accepted} | {pct st.accepted st.files} | {st.progs} | {st.acceptedProgs} |\n"
  if accept.isSome then
    out := out ++ s!"\nslice functions: {st.slice}, accepted: {st.sliceAccepted} ({pct st.sliceAccepted st.slice})\n"
  out := out ++ s!"\n{st.errors} parse or port errors\n\n| reason | functions | example |\n| --- | ---: | --- |\n"
  let sorted := st.reasons.toArray.qsort fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.1 < b.1)
  for (k, (c, ex)) in sorted.toList.take 200 do
    out := out ++ s!"| `{k}` | {c} | {ex.take 200} |\n"
  IO.println out
  if let some f := table then IO.FS.writeFile f out
  return if st.errors == 0 then 0 else 1

end GoFVTest.ObjCheck

def main (args : List String) : IO UInt32 := GoFVTest.ObjCheck.main args
