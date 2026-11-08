import GoFV.Gen.Genssa
import GoFV.Gen.Check20
import GoFV.Asm.Parse
import GoFV.SSA.Parse
import GoFVTest.GenIn

/-!
# `gen-check`: coverage of the genssa validator (`docs/plans/proofs3.md` §3, §4)

For every `*.prog` file under the given directories with its companion `.ssa` file, runs
`GoFV.Gen.genssa` (on the exported frame, as `gen-parity`) and the validators of slices G1
(`GoFV.Gen.Check.checkG1`), G2 (`GoFV.Gen.Check.checkG2`, with the Prog list's symbols and the
exported frame's slot operands), G3 (`GoFV.Gen.Check.checkG3`), G4 (`GoFV.Gen.Check.checkG4`), G5
(`GoFV.Gen.Check.checkG5`), G6 (`GoFV.Gen.Check.checkG6`), G7 (`GoFV.Gen.Check.checkG7`), G8
(`GoFV.Gen.Check.checkG8`), G9 (`GoFV.Gen.Check.checkG9`), G10 (`GoFV.Gen.Check.checkG10`), G11
(`GoFV.Gen.Check.checkG11`), G12 (`GoFV.Gen.Check.checkG12`), G13 (`GoFV.Gen.Check.checkG13`),
G14 (`GoFV.Gen.Check.checkG14`), G15 (`GoFV.Gen.Check.checkG15`), G16 (`GoFV.Gen.Check.checkG16`),
G17 (`GoFV.Gen.Check.checkG17`), G18 (`GoFV.Gen.Check.checkG18`), G19 (`GoFV.Gen.Check.checkG19`)
and G20 (`GoFV.Gen.Check.checkG20`), all with G2's inputs, on its P0
output and the function after `trim`, and counts the accepted functions. Rejections by the last
slice are grouped by their reason with value and block numbers removed.

usage: `lake exe gen-check [--jobs N] [--table FILE] <dir|file>...`
-/

open GoFV.SSA (ExportFile)
open GoFV.Asm
open GoFV.Gen

namespace GoFVTest.GenCheck

structure Stats where
  files : Nat := 0
  accepted : Nat := 0
  accepted2 : Nat := 0
  accepted3 : Nat := 0
  accepted4 : Nat := 0
  accepted5 : Nat := 0
  accepted6 : Nat := 0
  accepted7 : Nat := 0
  accepted8 : Nat := 0
  accepted9 : Nat := 0
  accepted10 : Nat := 0
  accepted11 : Nat := 0
  accepted12 : Nat := 0
  accepted13 : Nat := 0
  accepted14 : Nat := 0
  accepted15 : Nat := 0
  accepted16 : Nat := 0
  accepted17 : Nat := 0
  accepted18 : Nat := 0
  accepted19 : Nat := 0
  accepted20 : Nat := 0
  errors : Nat := 0
  values : Nat := 0
  acceptedValues : Nat := 0
  acceptedValues2 : Nat := 0
  acceptedValues3 : Nat := 0
  acceptedValues4 : Nat := 0
  acceptedValues5 : Nat := 0
  acceptedValues6 : Nat := 0
  acceptedValues7 : Nat := 0
  acceptedValues8 : Nat := 0
  acceptedValues9 : Nat := 0
  acceptedValues10 : Nat := 0
  acceptedValues11 : Nat := 0
  acceptedValues12 : Nat := 0
  acceptedValues13 : Nat := 0
  acceptedValues14 : Nat := 0
  acceptedValues15 : Nat := 0
  acceptedValues16 : Nat := 0
  acceptedValues17 : Nat := 0
  acceptedValues18 : Nat := 0
  acceptedValues19 : Nat := 0
  acceptedValues20 : Nat := 0
  /-- Functions by the set of reasons that reject them (sole reason: one-element set). -/
  sole : Std.HashMap String Nat := {}
  /-- Functions each reason occurs in. -/
  occurs : Std.HashMap String Nat := {}
  accept : Array String := #[]

def mergeMap (a b : Std.HashMap String Nat) : Std.HashMap String Nat :=
  b.fold (fun m k n => m.insert k (m.getD k 0 + n)) a

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, accepted := a.accepted + b.accepted,
    accepted2 := a.accepted2 + b.accepted2, accepted3 := a.accepted3 + b.accepted3,
    accepted4 := a.accepted4 + b.accepted4, accepted5 := a.accepted5 + b.accepted5,
    accepted6 := a.accepted6 + b.accepted6, accepted7 := a.accepted7 + b.accepted7,
    accepted8 := a.accepted8 + b.accepted8, accepted9 := a.accepted9 + b.accepted9,
    accepted10 := a.accepted10 + b.accepted10, accepted11 := a.accepted11 + b.accepted11,
    accepted12 := a.accepted12 + b.accepted12, accepted13 := a.accepted13 + b.accepted13,
    accepted14 := a.accepted14 + b.accepted14, accepted15 := a.accepted15 + b.accepted15,
    accepted16 := a.accepted16 + b.accepted16, accepted17 := a.accepted17 + b.accepted17,
    accepted18 := a.accepted18 + b.accepted18, accepted19 := a.accepted19 + b.accepted19,
    accepted20 := a.accepted20 + b.accepted20,
    errors := a.errors + b.errors,
    values := a.values + b.values, acceptedValues := a.acceptedValues + b.acceptedValues,
    acceptedValues2 := a.acceptedValues2 + b.acceptedValues2,
    acceptedValues3 := a.acceptedValues3 + b.acceptedValues3,
    acceptedValues4 := a.acceptedValues4 + b.acceptedValues4,
    acceptedValues5 := a.acceptedValues5 + b.acceptedValues5,
    acceptedValues6 := a.acceptedValues6 + b.acceptedValues6,
    acceptedValues7 := a.acceptedValues7 + b.acceptedValues7,
    acceptedValues8 := a.acceptedValues8 + b.acceptedValues8,
    acceptedValues9 := a.acceptedValues9 + b.acceptedValues9,
    acceptedValues10 := a.acceptedValues10 + b.acceptedValues10,
    acceptedValues11 := a.acceptedValues11 + b.acceptedValues11,
    acceptedValues12 := a.acceptedValues12 + b.acceptedValues12,
    acceptedValues13 := a.acceptedValues13 + b.acceptedValues13,
    acceptedValues14 := a.acceptedValues14 + b.acceptedValues14,
    acceptedValues15 := a.acceptedValues15 + b.acceptedValues15,
    acceptedValues16 := a.acceptedValues16 + b.acceptedValues16,
    acceptedValues17 := a.acceptedValues17 + b.acceptedValues17,
    acceptedValues18 := a.acceptedValues18 + b.acceptedValues18,
    acceptedValues19 := a.acceptedValues19 + b.acceptedValues19,
    acceptedValues20 := a.acceptedValues20 + b.acceptedValues20,
    sole := mergeMap a.sole b.sole, occurs := mergeMap a.occurs b.occurs,
    accept := a.accept ++ b.accept }

/-- Record a rejected function with its reasons. -/
def Stats.reject (st : Stats) (msgs : List String) : Stats :=
  let ks := (msgs.map classOf).eraseDups
  let occurs := ks.foldl (fun m k => m.insert k (m.getD k 0 + 1)) st.occurs
  let sole := match ks with
    | [k] => st.sole.insert k (st.sole.getD k 0 + 1)
    | _ => st.sole.insert s!"({ks.length} reasons)" (st.sole.getD s!"({ks.length} reasons)" 0 + 1)
  { st with occurs, sole }

/-- Every reason the G20 validator could give for `lc` (homes, values, block kinds, the frame;
then the run itself). -/
def reasons20 (lc : GoFV.SSA.Sem.LocCtx) (ps : Array Prog) (bstart : GoFV.SSA.ID → Option Nat)
    (g : Check.G2In) : List String := Id.run do
  let mut rs : List String := []
  unless lc.ctx.f.lowered do rs := "not lowered" :: rs
  for h : i in [0:lc.homes.size] do
    unless Check.homeOK10 lc i do rs := Check.homeErr lc i :: rs
  for bid in lc.ctx.f.blocks do
    let some b := lc.ctx.f.block? bid | continue
    for id in b.values do
      let some v := lc.ctx.f.value? id | continue
      match Check.vkind20 lc g v with
      | .error e => rs := e :: rs
      | .ok _ => pure ()
    if Check.condBr b.kind == none && Check.zeroBr b.kind == none && Check.testBr b.kind == none &&
        b.kind != .Plain && b.kind != .Ret && b.kind != .Exit then
      rs := s!"b{bid}: block kind {b.kind.name}" :: rs
  if let .error e := Check.checkFrame lc g then rs := e :: rs
  if rs.isEmpty then
    match Check.checkG20 lc ps bstart g with
    | .error e => rs := [e]
    | .ok _ => pure ()
  return rs

def checkFile (path : System.FilePath) (st : Stats) : IO Stats := do
  let st := { st with files := st.files + 1 }
  let progData ← IO.FS.readBinFile path
  let ssaData ← IO.FS.readBinFile (path.withExtension "ssa")
  let res : Except String (ExportFile × ProgFile) := do
    let (e, _) ← GoFV.SSA.parseExportExt ssaData
    let pf ← parseProgFile progData
    return (e, pf)
  match res with
  | .error e => return { (st.reject [s!"parse: {e}"]) with errors := st.errors + 1 }
  | .ok (e, pf) =>
  match Env.load e pf with
  | .error msg => return { (st.reject [s!"env: {msg}"]) with errors := st.errors + 1 }
  | .ok env =>
  let fr : FrameOut :=
    { dcl := pf.frame.dclOut, optDcl := pf.frame.optDcl, merges := pf.frame.merges,
      stksize := pf.frame.stksize, stkptrsize := pf.frame.stkptrsize,
      stkalign := pf.frame.stkalign }
  match genssa env fr with
  | .error msg => return { (st.reject [s!"genssa: {msg}"]) with errors := st.errors + 1 }
  | .ok out =>
  let ps := out.order.filterMap (out.st.progs[·]?)
  let lc := GoFV.SSA.Sem.LocCtx.make env.tabs env.f
  let nv := env.f.blocks.foldl (fun n b => n + ((env.f.block? b).map (·.values.size)).getD 0) 0
  let st := { st with values := st.values + nv }
  let bstart := fun b => (out.st.bstart[b]?).join
  let st := match Check.checkG1 lc ps bstart with
    | .ok _ => { st with accepted := st.accepted + 1, acceptedValues := st.acceptedValues + nv }
    | .error _ => st
  let g : Check.G2In :=
    { syms := out.st.syms, slotOp := slotOpOf env (Ctx.ofFrame env fr).offsets,
      stksize := fr.stksize }
  let st := match Check.checkG2 lc ps bstart g with
    | .ok _ => { st with accepted2 := st.accepted2 + 1, acceptedValues2 := st.acceptedValues2 + nv }
    | .error _ => st
  let st := match Check.checkG3 lc ps bstart g with
    | .ok _ => { st with accepted3 := st.accepted3 + 1, acceptedValues3 := st.acceptedValues3 + nv }
    | .error _ => st
  let ok4 := (Check.checkG4 lc ps bstart g).toOption.isSome
  let st := if ok4 then
      { st with accepted4 := st.accepted4 + 1, acceptedValues4 := st.acceptedValues4 + nv }
    else st
  let ok5 := (Check.checkG5 lc ps bstart g).toOption.isSome
  let st := if ok5 then
      { st with accepted5 := st.accepted5 + 1, acceptedValues5 := st.acceptedValues5 + nv }
    else st
  let ok6 := (Check.checkG6 lc ps bstart g).toOption.isSome
  let st := if ok6 then
      { st with accepted6 := st.accepted6 + 1, acceptedValues6 := st.acceptedValues6 + nv }
    else st
  let ok7 := (Check.checkG7 lc ps bstart g).toOption.isSome
  let st := if ok7 then
      { st with accepted7 := st.accepted7 + 1, acceptedValues7 := st.acceptedValues7 + nv }
    else st
  let ok8 := (Check.checkG8 lc ps bstart g).toOption.isSome
  let st := if ok8 then
      { st with accepted8 := st.accepted8 + 1, acceptedValues8 := st.acceptedValues8 + nv }
    else st
  let ok9 := (Check.checkG9 lc ps bstart g).toOption.isSome
  let st := if ok9 then
      { st with accepted9 := st.accepted9 + 1, acceptedValues9 := st.acceptedValues9 + nv }
    else st
  let ok10 := (Check.checkG10 lc ps bstart g).toOption.isSome
  let st := if ok10 then
      { st with accepted10 := st.accepted10 + 1, acceptedValues10 := st.acceptedValues10 + nv }
    else st
  let ok11 := (Check.checkG11 lc ps bstart g).toOption.isSome
  let st := if ok11 then
      { st with accepted11 := st.accepted11 + 1, acceptedValues11 := st.acceptedValues11 + nv }
    else st
  let ok12 := (Check.checkG12 lc ps bstart g).toOption.isSome
  let st := if ok12 then
      { st with accepted12 := st.accepted12 + 1, acceptedValues12 := st.acceptedValues12 + nv }
    else st
  let ok13 := (Check.checkG13 lc ps bstart g).toOption.isSome
  let st := if ok13 then
      { st with accepted13 := st.accepted13 + 1, acceptedValues13 := st.acceptedValues13 + nv }
    else st
  let ok14 := (Check.checkG14 lc ps bstart g).toOption.isSome
  let st := if ok14 then
      { st with accepted14 := st.accepted14 + 1, acceptedValues14 := st.acceptedValues14 + nv }
    else st
  let ok15 := (Check.checkG15 lc ps bstart g).toOption.isSome
  let st := if ok15 then
      { st with accepted15 := st.accepted15 + 1, acceptedValues15 := st.acceptedValues15 + nv }
    else st
  let ok16 := (Check.checkG16 lc ps bstart g).toOption.isSome
  let st := if ok16 then
      { st with accepted16 := st.accepted16 + 1, acceptedValues16 := st.acceptedValues16 + nv }
    else st
  let ok17 := (Check.checkG17 lc ps bstart g).toOption.isSome
  let st := if ok17 then
      { st with accepted17 := st.accepted17 + 1, acceptedValues17 := st.acceptedValues17 + nv }
    else st
  let ok18 := (Check.checkG18 lc ps bstart g).toOption.isSome
  let st := if ok18 then
      { st with accepted18 := st.accepted18 + 1, acceptedValues18 := st.acceptedValues18 + nv }
    else st
  let ok19 := (Check.checkG19 lc ps bstart g).toOption.isSome
  let st := if ok19 then
      { st with accepted19 := st.accepted19 + 1, acceptedValues19 := st.acceptedValues19 + nv }
    else st
  match Check.checkG20 lc ps bstart g with
  | .ok _ =>
    let tag := if ok4 then "" else if ok5 then " (G5)" else if ok6 then " (G6)"
      else if ok7 then " (G7)" else if ok8 then " (G8)" else if ok9 then " (G9)"
      else if ok10 then " (G10)" else if ok11 then " (G11)" else if ok12 then " (G12)"
      else if ok13 then " (G13)" else if ok14 then " (G14)" else if ok15 then " (G15)"
      else if ok16 then " (G16)" else if ok17 then " (G17)" else if ok18 then " (G18)"
      else if ok19 then " (G19)" else " (G20)"
    return { st with accepted20 := st.accepted20 + 1, acceptedValues20 := st.acceptedValues20 + nv,
                     accept := st.accept.push s!"{path}{tag}" }
  | .error msg =>
    let rs := reasons20 lc ps bstart g
    return st.reject (if rs.isEmpty then [msg] else rs)

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
  let rec parse : List String → Nat × Option String × Array String → Option (Nat × Option String × Array String)
    | [], o => some o
    | "--jobs" :: n :: rest, (_, t, ps) => n.toNat?.bind fun n => parse rest (max n 1, t, ps)
    | "--table" :: f :: rest, (j, _, ps) => parse rest (j, some f, ps)
    | p :: rest, (j, t, ps) => parse rest (j, t, ps.push p)
  let some (jobs, table, paths) := parse args (1, none, #[])
    | IO.eprintln "usage: gen-check [--jobs N] [--table FILE] <dir|file>..."; return 2
  let mut files := #[]
  for p in paths do files := files ++ (← progFiles p)
  let tasks ← (List.range jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st : Stats := {}
    for h : i in [0:files.size] do
      if i % jobs == j then st ← checkFile files[i] st
    return st
  let mut st : Stats := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 1
  let mut out := s!"| functions | slice | accepted | share | values | in accepted functions |\n| ---: | --- | ---: | ---: | ---: | ---: |\n"
  out := out ++ s!"| {st.files} | G1 | {st.accepted} | {pct st.accepted st.files} | {st.values} | {st.acceptedValues} |\n"
  out := out ++ s!"| {st.files} | G2 | {st.accepted2} | {pct st.accepted2 st.files} | {st.values} | {st.acceptedValues2} |\n"
  out := out ++ s!"| {st.files} | G3 | {st.accepted3} | {pct st.accepted3 st.files} | {st.values} | {st.acceptedValues3} |\n"
  out := out ++ s!"| {st.files} | G4 | {st.accepted4} | {pct st.accepted4 st.files} | {st.values} | {st.acceptedValues4} |\n"
  out := out ++ s!"| {st.files} | G5 | {st.accepted5} | {pct st.accepted5 st.files} | {st.values} | {st.acceptedValues5} |\n"
  out := out ++ s!"| {st.files} | G6 | {st.accepted6} | {pct st.accepted6 st.files} | {st.values} | {st.acceptedValues6} |\n"
  out := out ++ s!"| {st.files} | G7 | {st.accepted7} | {pct st.accepted7 st.files} | {st.values} | {st.acceptedValues7} |\n"
  out := out ++ s!"| {st.files} | G8 | {st.accepted8} | {pct st.accepted8 st.files} | {st.values} | {st.acceptedValues8} |\n"
  out := out ++ s!"| {st.files} | G9 | {st.accepted9} | {pct st.accepted9 st.files} | {st.values} | {st.acceptedValues9} |\n"
  out := out ++ s!"| {st.files} | G10 | {st.accepted10} | {pct st.accepted10 st.files} | {st.values} | {st.acceptedValues10} |\n"
  out := out ++ s!"| {st.files} | G11 | {st.accepted11} | {pct st.accepted11 st.files} | {st.values} | {st.acceptedValues11} |\n"
  out := out ++ s!"| {st.files} | G12 | {st.accepted12} | {pct st.accepted12 st.files} | {st.values} | {st.acceptedValues12} |\n"
  out := out ++ s!"| {st.files} | G13 | {st.accepted13} | {pct st.accepted13 st.files} | {st.values} | {st.acceptedValues13} |\n"
  out := out ++ s!"| {st.files} | G14 | {st.accepted14} | {pct st.accepted14 st.files} | {st.values} | {st.acceptedValues14} |\n"
  out := out ++ s!"| {st.files} | G15 | {st.accepted15} | {pct st.accepted15 st.files} | {st.values} | {st.acceptedValues15} |\n"
  out := out ++ s!"| {st.files} | G16 | {st.accepted16} | {pct st.accepted16 st.files} | {st.values} | {st.acceptedValues16} |\n"
  out := out ++ s!"| {st.files} | G17 | {st.accepted17} | {pct st.accepted17 st.files} | {st.values} | {st.acceptedValues17} |\n"
  out := out ++ s!"| {st.files} | G18 | {st.accepted18} | {pct st.accepted18 st.files} | {st.values} | {st.acceptedValues18} |\n"
  out := out ++ s!"| {st.files} | G19 | {st.accepted19} | {pct st.accepted19 st.files} | {st.values} | {st.acceptedValues19} |\n"
  out := out ++ s!"| {st.files} | G20 | {st.accepted20} | {pct st.accepted20 st.files} | {st.values} | {st.acceptedValues20} |\n"
  out := out ++ s!"\n{st.errors} parse, env or genssa errors\n"
  let sorted (m : Std.HashMap String Nat) :=
    m.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
  out := out ++ "\n| sole reason | functions |\n| --- | ---: |\n"
  for (k, c) in (sorted st.sole).toList.take 60 do out := out ++ s!"| `{k}` | {c} |\n"
  out := out ++ "\n| reason | functions it occurs in |\n| --- | ---: |\n"
  for (k, c) in (sorted st.occurs).toList.take 80 do out := out ++ s!"| `{k}` | {c} |\n"
  out := out ++ "\naccepted (G20; the first slice that accepts a function past G4 in parentheses):\n"
  for a in st.accept.qsort (· < ·) do out := out ++ s!"- {a}\n"
  IO.println out
  if let some f := table then IO.FS.writeFile f out
  return 0

end GoFVTest.GenCheck

def main (args : List String) : IO UInt32 := GoFVTest.GenCheck.main args
