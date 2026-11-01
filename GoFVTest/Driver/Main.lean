import GoFVTest.Driver.Pipeline
import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.SSA.Print

/-!
# `gofv-ssa-opt`

The Lean generic pipeline as a program (`docs/DRIVER.md`).

- `gofv-ssa-opt [--from <pass>] [--to <pass>] [--partial] <in.ssa>`: read a `gofv-ssa` file whose first
  section is the function to optimise (`ssa.Compile`'s input, or the state before pass `--from`),
  run the enabled stock passes in `compile.go` order with the registered Lean ports, and print
  to stdout a status line followed, if there is a result, by a `gofv-ssa` file with one section:
  the definitions the passes created or changed, and the function (the input of `lower`).
  Status lines: `status ok`, `status unported "<pass>"`, `status error "<pass>" "<msg>"`. On
  `unported`/`error` the result (the input of the pass that stopped the run) is only printed with
  `--partial`. `--to <pass>` stops after that pass (debugging).
- `gofv-ssa-opt --list`: one line per stock pass before `lower`: `ported|unported "<name>"`.
- `gofv-ssa-opt --check [--mixed] [--whole-file-env] [--strict] [--jobs N] [--max-report N]
  [--table FILE] <dir|file>...`:
  whole-pipeline parity over stock export files. The pipeline starts from what the driver would export (section
  0, its definitions, the type order of those types), chains the Lean results, and compares the
  state after every pass with the stock section of that pass, as the importer compares (a new
  symbol by name and ABI, map lines as sets); `--strict` compares as `pass-parity`.
-/

open GoFV.SSA GoFV.Opt GoFVTest.Parity

namespace GoFVTest.Driver

/-- `typeorder` restricted to the types defined in `tabs`: what the exporter writes for a file
that contains only those types. -/
def restrictOrder (groups : Array (Array TypeRef)) (tabs : Tables) : Array (Array TypeRef) :=
  groups.filterMap fun g =>
    let g := g.filter fun t => (tabs.type? t).isSome
    if g.isEmpty then none else some g

/-- Whether a symbol name is a generic dictionary (`..dict.`). -/
def isDict (n : GoStr) : Bool := (n.toStringLossy.splitOn "..dict.").length > 1

/-- The frontend the driver's export provides for a function whose tables are `tables`: the
tables plus what the exporter's `frontend` block adds to them — the closure of the read-only
dictionaries' `R_ADDR`/`R_WEAKADDR` relocation targets (`export_gofv.go` `frontend`). The
definitions are taken from the whole file (`ExportFile.frontendTables`), which numbers them
consistently with `tables`, with the types those symbols refer to. -/
def driverFrontend (e : ExportFile) (tables : Tables) : Tables := Id.run do
  let all := e.frontendTables
  let mut fe := tables
  let mut queue : Array AuxDef := tables.auxes.filterMap id
  let mut i := 0
  for _ in [0:queue.size + all.auxes.size + 1] do
    let some d := queue[i]? | break
    i := i + 1
    let .sym name _ kind _ _ _ _ _ relocs _ := d.kind | continue
    if kind != "SRODATA" || !isDict name then continue
    for r in relocs do
      if r.type != "R_ADDR" && r.type != "R_WEAKADDR" then continue
      let abi := some r.targetAbi.toNat
      if (PassEnv.findSym? fe r.target abi).isSome then continue
      if let some (n, td) := PassEnv.findSym? all r.target abi then
        fe := fe.add (.aux n td)
        queue := queue.push td
        -- the exporter also defines the types the symbol refers to (typeinfo, itabinfo)
        let .sym _ _ _ _ _ ti ii _ _ _ := td.kind | continue
        let mut ts := ti.toArray ++ ii.toArray
        for _ in [0:all.types.size + 1] do
          let some t := ts.back? | break
          ts := ts.pop
          if (fe.type? t).isSome then continue
          let some d := all.type? t | continue
          fe := fe.add (.type t d)
          ts := ts ++ match d.tail with
            | .none => #[]
            | .elem x | .array x _ => #[x]
            | .struct fs | .func _ _ _ fs => fs.map (·.type)
            | .tuple x y => #[x, y]
            | .results xs => xs
  return fe

/-- The pass environment of an export file's header with the given tables. As the driver's
export of a function with these tables: the type order and `typecmp` exceptions restricted to
their types, and `driverFrontend`. With `wholeFile`, the per-pass parity environment instead
(type order and frontend of the whole stock file), to tell divergences caused by the driver's
narrower view from others. -/
def baseEnv (e : ExportFile) (tables : Tables) (wholeFile : Bool := false) : PassEnv :=
  let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
  let env : PassEnv :=
    { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
      pgohot := e.pgohot, config := e.config, typs
      typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
      tables, frontend := e.frontendTables }
  if wholeFile then env else
  let fe := driverFrontend e tables
  { env with
    typeOrder := TypeOrder.ofGroups (restrictOrder e.typeOrder fe)
      (e.typeCmp.filter fun (a, b, _) => (fe.type? a).isSome && (fe.type? b).isSome)
    frontend := fe }

/-- Definitions of `b` that are new or different from `a`'s (posbase, type, aux, slot). -/
def tableDiff (a b : Tables) : Array Def := Id.run do
  let mut out := #[]
  for i in [0:b.posBases.size] do
    if let some d := b.posBase? i then
      if a.posBase? i != some d then out := out.push (.posBase i d)
  for i in [0:b.types.size] do
    if let some d := b.type? i then
      if a.type? i != some d then out := out.push (.type i d)
  for i in [0:b.auxes.size] do
    if let some d := b.aux? i then
      if a.aux? i != some d then out := out.push (.aux i d)
  for i in [0:b.slots.size] do
    if let some d := b.slot? i then
      if a.slot? i != some d then out := out.push (.slot i d)
  return out

def statusLine : Stop → String
  | .done | .halted _ => "status ok"
  | .unported p => s!"status unported {GoStr.quote p}"
  | .error p m => s!"status error {GoStr.quote p} {GoStr.quote m}"

/-- `t` with its arrays at least as long as `all`'s: passes number new objects past the end of
the tables, and the importer's tables also hold the `frontend` block's objects. -/
def padTables (t all : Tables) : Tables :=
  let pad {α} (a : Array (Option α)) (n : Nat) : Array (Option α) :=
    if a.size < n then a ++ Array.replicate (n - a.size) none else a
  { t with types := pad t.types all.types.size, auxes := pad t.auxes all.auxes.size
           slots := pad t.slots all.slots.size }

/-- Driver mode: optimise the first section of `e` from stock pass index `start`. -/
def optimise (e : ExportFile) (start : Nat) (partialOut : Bool) (stopAfter : Option String := none) :
    String := Id.run do
  let some s0 := e.sections[0]? | return "status error \"input\" \"no section\"\n"
  let tables := padTables (({} : Tables).addAll s0.defs) e.frontendTables
  -- the input is the driver's own export: its type order and frontend block are the function's
  let env := baseEnv e tables (wholeFile := true)
  let (stop, st) := (runFrom (m := Id) env { func := s0.func, tables } start
    (fun name _ => pure (stopAfter != some name)))
  let status := statusLine stop ++ "\n"
  let ok := match stop with | .done | .halted _ => true | _ => false
  if !ok && !partialOut then return status
  let sec : Section := { index := st.ran, pass := st.last, defs := tableDiff tables st.tables
                         func := st.func, typs := none, warns := #[] }
  let effects := st.effects.foldl (init := "") fun s e => match e with
    | .useIface a => s ++ s!"effect useiface a{a}\n"
  return status ++ effects ++
    printExport { e with sections := #[sec], warns := #[], typeOrder := #[], typeCmp := #[], frontend := #[] }

/-! ## `--check` -/

/-- How one function's chain ended. -/
inductive Outcome where
  /-- Every enabled pass is ported and every intermediate state equals the stock section. -/
  | full
  /-- Identical up to the first unported enabled pass. -/
  | unported (pass : String)
  /-- The state after `pass` differs from the stock section. -/
  | diverged (pass : String) (detail : String)
  /-- A Lean pass failed. -/
  | error (pass : String) (msg : String)
  | parseError (msg : String)

/-- Per stock pass: chains that ran it and of those, how many matched the stock section. -/
structure PassCount where
  runs : Nat := 0
  same : Nat := 0
  deriving Inhabited

structure Stats where
  files : Nat := 0
  full : Nat := 0
  /-- Stops at an unported pass, by pass. -/
  unported : Std.HashMap String Nat := {}
  /-- First divergences, by pass. -/
  diverged : Std.HashMap String Nat := {}
  errors : Std.HashMap String Nat := {}
  /-- `--mixed`: unported passes taken from the stock file, by pass. -/
  stockRun : Std.HashMap String Nat := {}
  parseErrors : Nat := 0
  counts : Array PassCount := Array.replicate stockPasses.size {}
  reports : Array (String × String × String) := #[]

def bumpMap (m : Std.HashMap String Nat) (k : String) (n : Nat := 1) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + n)

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, full := a.full + b.full
    unported := b.unported.fold (fun m k n => bumpMap m k n) a.unported
    diverged := b.diverged.fold (fun m k n => bumpMap m k n) a.diverged
    errors := b.errors.fold (fun m k n => bumpMap m k n) a.errors
    stockRun := b.stockRun.fold (fun m k n => bumpMap m k n) a.stockRun
    parseErrors := a.parseErrors + b.parseErrors
    counts := (a.counts.zip b.counts).map fun (x, y) => { runs := x.runs + y.runs, same := x.same + y.same }
    reports := a.reports ++ b.reports }

/-- How many times the driver runs a segment to rank the types the Lean passes create
(`driver_gofv.go` `gofvTypeRounds`). -/
def typeRounds : Nat := 3

/-- The types the Lean passes created (defined in `lean`, not in `input`), as the stock file's
definitions of the same types (equal up to their type references), with the types they refer
to: what the driver adds to the next round's export. -/
def stockTypesFor (all input lean : Tables) : Array Def := Id.run do
  let mut out : Array Def := #[]
  let mut known := input
  let strip (d : TypeDef) : TypeDef := { d with tail := .none }
  let mut queue : Array Nat := #[]
  for n in [0:lean.types.size] do
    if (input.type? n).isSome then continue
    let some d := lean.type? n | continue
    for m in [0:all.types.size] do
      if (known.type? m).isSome then continue
      if let some d' := all.type? m then
        if strip d' == strip d then queue := queue.push m; break
  for _ in [0:all.types.size + 1] do
    let some m := queue.back? | break
    queue := queue.pop
    if (known.type? m).isSome then continue
    let some d := all.type? m | continue
    known := known.add (.type m d)
    out := out.push (.type m d)
    queue := queue ++ match d.tail with
      | .none => #[]
      | .elem x | .array x _ => #[x]
      | .struct fs | .func _ _ _ fs => fs.map (·.type)
      | .tuple x y => #[x, y]
      | .results xs => xs
  return out

/-- State of the stock side while walking a file's sections. -/
structure Walk where
  k : Nat
  tables : Tables
  failure : Option (String × String) := none
  counts : Array PassCount

/-- Whole-pipeline parity of one export file. The chain starts from section 0 with its own
definitions and type order (what the driver exports) and compares the state after each Lean
pass with the stock section of that pass. With `mixed`, an unported pass is taken from the stock
file (its output section, with the tables and type order in force there) and the chain goes on
from there, as `GOFV_SSA_DRIVER_MODE=mixed` does; the unported passes met are returned. Unless
`strict`, states are compared as the importer compares them (`compare`'s `loose`). -/
def checkExport (mixed wholeFile strict : Bool) (e : ExportFile) :
    Outcome × Array PassCount × Array String := Id.run do
  let mut counts := Array.replicate stockPasses.size ({} : PassCount)
  let some s0 := e.sections[0]? | return (.parseError "no section", counts, #[])
  let mut base := ({} : Tables).addAll s0.defs
  let mut func := s0.func
  let mut k := 1
  let mut start := 0
  let mut stockRun := #[]
  for _ in [0:stockPasses.size + 1] do
    -- Type rounds (as the driver): rerun the segment with the types the Lean passes created
    -- added to its input, so that they are ranked in the type order.
    let mut tables0 := base
    let mut out : (Stop × State) × Walk := ((.done, { func, tables := base }), { k, tables := base, counts })
    for round in [0:typeRounds] do
      let t0 := tables0
      let env := baseEnv e t0 wholeFile
      let step (name : String) (st : State) : StateM Walk Bool := do
        let w ← get
        let pi := (passIndex? name).getD 0
        let bump (same : Bool) (w : Walk) : Walk :=
          { w with counts := w.counts.modify pi fun c =>
              { runs := c.runs + 1, same := c.same + (if same then 1 else 0) } }
        let some s := e.sections[w.k]? |
          set { bump false w with failure := some (name, "stock has no section for this pass") }
          return false
        if s.pass.toStringLossy != name then
          set { bump false w with failure := some (name, s!"stock section {w.k} is \"{s.pass.toStringLossy}\"") }
          return false
        let want := w.tables.addAll s.defs
        match compare t0 { func := st.func, tables := st.tables } want s (loose := !strict) with
        | none => set { bump true w with k := w.k + 1, tables := want }; return true
        | some d => set { bump false w with failure := some (name, d) }; return false
      out := (runFrom env { func, tables := t0 } start step).run { k, tables := t0, counts }
      let added := stockTypesFor e.frontendTables t0 out.1.2.tables
      if added.isEmpty || round + 1 == typeRounds then break
      tables0 := t0.addAll added
    let ((stop, _), w) := out
    counts := w.counts
    if let some (p, d) := w.failure then return (.diverged p d, counts, stockRun)
    match stop with
    | .error p m => return (.error p m, counts, stockRun)
    | .halted p => return (.diverged p "halted", counts, stockRun)
    | .unported p =>
      let some s := e.sections[w.k]? |
        return (.diverged p "stock has no section for the unported pass", counts, stockRun)
      if s.pass.toStringLossy != p then
        return (.diverged p s!"stock section {w.k} is \"{s.pass.toStringLossy}\", Lean stops at unported \"{p}\"", counts, stockRun)
      if !mixed then return (.unported p, counts, stockRun)
      stockRun := stockRun.push p
      base := w.tables.addAll s.defs
      func := s.func
      k := w.k + 1
      start := (passIndex? p).getD 0 + 1
    | .done =>
      match e.sections[w.k]? with
      | some s => return (.diverged s.pass.toStringLossy "stock runs this pass, the Lean pipeline does not", counts, stockRun)
      | none => return (.full, counts, stockRun)
  return (.diverged "?" "segment loop did not terminate", counts, stockRun)

def checkFile (mixed wholeFile strict : Bool) (maxReport : Nat) (path : System.FilePath) (st : Stats) :
    IO Stats := do
  let data ← IO.FS.readBinFile path
  let st := { st with files := st.files + 1 }
  let (o, counts, stockRun) : Outcome × Array PassCount × Array String :=
    match parseExport data with
    | .error e => (Outcome.parseError e, #[], #[])
    | .ok e => checkExport mixed wholeFile strict e
  let st := { st with stockRun := stockRun.foldl (fun m p => bumpMap m p) st.stockRun }
  let st := { st with counts := st.counts.mapIdx fun i (x : PassCount) =>
                let y := counts.getD i {}
                { runs := x.runs + y.runs, same := x.same + y.same } }
  let report (st : Stats) (kind detail : String) : Stats :=
    if (st.reports.filter (·.2.1 == kind)).size < maxReport then
      { st with reports := st.reports.push (path.toString, kind, detail) }
    else st
  match o with
  | .full => return { st with full := st.full + 1 }
  | .unported p => return { st with unported := bumpMap st.unported p }
  | .diverged p d => return report { st with diverged := bumpMap st.diverged p } s!"diverged {p}" d
  | .error p m => return report { st with errors := bumpMap st.errors p } s!"error {p}" m
  | .parseError m =>
    IO.eprintln s!"PARSE ERROR {path}: {m}"
    return { st with parseErrors := st.parseErrors + 1 }

def ssaFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "ssa")).qsort (·.toString < ·.toString)
  else return #[p]

def sortedMap (m : Std.HashMap String Nat) : Array (String × Nat) :=
  m.toArray.qsort fun a b => (passIndex? a.1).getD 999 < (passIndex? b.1).getD 999

def tableText (mixed : Bool) (st : Stats) (ms : Nat) : String := Id.run do
  let mut out := s!"files: {st.files}, parse errors: {st.parseErrors}, wall: {ms / 1000} s\n\n"
  let n (m : Std.HashMap String Nat) := m.fold (fun a _ x => a + x) 0
  if mixed then
    out := out ++ s!"mixed: unported passes taken from the stock file ({n st.stockRun} pass runs)\n"
    for (p, c) in sortedMap st.stockRun do out := out ++ s!"  - `{p}`: {c}\n"
    out := out ++ s!"- every Lean segment identical to the end: {st.full}\n"
  else
    out := out ++ s!"- whole pipeline identical (every enabled pass ported): {st.full}\n"
  out := out ++ s!"- identical up to the first unported pass: {n st.unported}\n"
  for (p, c) in sortedMap st.unported do out := out ++ s!"  - stops at `{p}`: {c}\n"
  out := out ++ s!"- first divergence: {n st.diverged}\n"
  for (p, c) in sortedMap st.diverged do
    out := out ++ s!"  - at `{p}`{if p == "sccp" then " (sccp: see its nondeterminism notes)" else ""}: {c}\n"
  out := out ++ s!"- Lean pass errors: {n st.errors}\n"
  for (p, c) in sortedMap st.errors do out := out ++ s!"  - at `{p}`: {c}\n"
  out := out ++ "\n| pass | ported | chains reaching it | identical |\n| --- | --- | ---: | ---: |\n"
  for h : i in [0:stockPasses.size] do
    let p := stockPasses[i]
    let c := st.counts[i]!
    out := out ++ s!"| {p.name} | {if (port? p.name).isSome then "yes" else "no"} | {c.runs} | {c.same} |\n"
  return out

structure Opts where
  check : Bool := false
  mixed : Bool := false
  wholeFile : Bool := false
  /-- `--strict`: compare every definition and the map lines' order (as `pass-parity`). -/
  strict : Bool := false
  list : Bool := false
  partialOut : Bool := false
  start : Option String := none
  /-- `--to <pass>`: stop after that pass (debugging). -/
  stopAfter : Option String := none
  jobs : Nat := 1
  maxReport : Nat := 10
  table : Option String := none
  paths : Array String := #[]

partial def parseArgs : List String → Opts → Except String Opts
  | [], o => pure o
  | "--check" :: rest, o => parseArgs rest { o with check := true }
  | "--mixed" :: rest, o => parseArgs rest { o with mixed := true }
  | "--whole-file-env" :: rest, o => parseArgs rest { o with wholeFile := true }
  | "--strict" :: rest, o => parseArgs rest { o with strict := true }
  | "--list" :: rest, o => parseArgs rest { o with list := true }
  | "--partial" :: rest, o => parseArgs rest { o with partialOut := true }
  | "--from" :: p :: rest, o => parseArgs rest { o with start := some p }
  | "--to" :: p :: rest, o => parseArgs rest { o with stopAfter := some p }
  | "--jobs" :: n :: rest, o => do
    let some n := n.toNat? | throw s!"--jobs {n}: not a number"
    parseArgs rest { o with jobs := max n 1 }
  | "--max-report" :: n :: rest, o => do
    let some n := n.toNat? | throw s!"--max-report {n}: not a number"
    parseArgs rest { o with maxReport := n }
  | "--table" :: p :: rest, o => parseArgs rest { o with table := some p }
  | a :: rest, o =>
    if a.startsWith "--" then throw s!"unknown option {a}"
    else parseArgs rest { o with paths := o.paths.push a }

def usage : String :=
  "usage: gofv-ssa-opt [--from <pass>] [--to <pass>] [--partial] <in.ssa>\n       gofv-ssa-opt --list\n       \
   gofv-ssa-opt --check [--mixed] [--whole-file-env] [--strict] [--jobs N] [--max-report N] [--table FILE] <dir|file>..."

def runCheck (o : Opts) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let mut files := #[]
  for p in o.paths do files := files ++ (← ssaFiles p)
  let tasks ← (List.range o.jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st : Stats := {}
    for h : i in [0:files.size] do
      if i % o.jobs == j then st ← checkFile o.mixed o.wholeFile o.strict o.maxReport files[i] st
    return st
  let mut st : Stats := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 2
  let ms := (← IO.monoMsNow) - t0
  let reports := st.reports.qsort fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 < b.1)
  let mut shown : Std.HashMap String Nat := {}
  for (file, kind, detail) in reports do
    if shown.getD kind 0 < o.maxReport then
      shown := bumpMap shown kind
      IO.println s!"{kind.toUpper}: {file}: {detail}"
  let text := tableText o.mixed st ms
  IO.print text
  if let some p := o.table then IO.FS.writeFile p text
  let bad := st.parseErrors > 0 || st.files == 0 || !st.diverged.isEmpty || !st.errors.isEmpty
  return if bad then 1 else 0

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; IO.eprintln usage; return 2
  if o.list then
    for p in stockPasses do
      IO.println s!"{if (port? p.name).isSome then "ported" else "unported"} {GoStr.quote p.name}"
    return 0
  if o.check then
    if o.paths.isEmpty then IO.eprintln usage; return 2
    return ← runCheck o
  let #[path] := o.paths | IO.eprintln usage; return 2
  let start ← match o.start with
    | none => pure 0
    | some p => match passIndex? p with
      | some i => pure i
      | none => IO.eprintln s!"--from {p}: not a stock pass before lower"; return 2
  let data ← IO.FS.readBinFile path
  match parseExport data with
  | .error e =>
    IO.println s!"status error \"parse\" {GoStr.quote e}"
    return 0
  | .ok e =>
    let out ← IO.lazyPure fun _ => optimise e start o.partialOut o.stopAfter
    (← IO.getStdout).putStr out
    return 0

end GoFVTest.Driver

def main (args : List String) : IO UInt32 := GoFVTest.Driver.main args
