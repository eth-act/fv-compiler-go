import GoFVTest.Driver.FragWhy
import GoFVTest.Driver.Pipeline
import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.SSA.Print

/-!
# `gofv-ssa-opt`

The Lean pipeline (`number lines` through `trim`) as a program (`docs/DRIVER.md`).

- `gofv-ssa-opt [--from <pass>] [--to <pass>] [--partial] <in.ssa>`: read a `gofv-ssa` file whose first
  section is the function to compile (`ssa.Compile`'s input, or the state before pass `--from`),
  run the enabled stock passes in `compile.go` order with the registered Lean ports, and print
  to stdout a status line followed, if there is a result, by a `gofv-ssa` file with one section:
  the definitions the passes created or changed, and the function (after `trim`, the input of
  `genssa`), with its `dcllen`.
  Status lines: `status ok`, `status unported "<pass>"`, `status error "<pass>" "<msg>"`. On
  `unported`/`error` the result (the input of the pass that stopped the run) is only printed with
  `--partial`. `--to <pass>` stops after that pass (debugging).
- `gofv-ssa-opt --list`: one line per stock pass: `ported|unported "<name>"`.
- `gofv-ssa-opt --check [--mixed] [--whole-file-env] [--strict] [--jobs N] [--max-report N]
  [--table FILE] <dir|file>...`:
  whole-pipeline parity over stock export files. The pipeline starts from what the driver would export (section
  0, its definitions, the type order of those types), chains the Lean results through `trim`, and
  compares the state after every pass with the stock section of that pass, as the importer
  compares (a new symbol by name and ABI, map lines as sets; the chain's `dcllen` with the
  section's); `--strict` compares as `pass-parity`.
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
        -- the exporter also defines the types the symbol refers to (typeinfo, itabinfo) and
        -- their components, transitively (field types of a struct, …). A type enters `fe`
        -- when it is pushed, so each is pushed once and `all.types.size` pops suffice.
        let .sym _ _ _ _ _ ti ii _ _ _ := td.kind | continue
        let mut ts : Array TypeRef := #[]
        for t in ti.toArray ++ ii.toArray do
          if (fe.type? t).isNone then
            if let some d := all.type? t then
              fe := fe.add (.type t d)
              ts := ts.push t
        for _ in [0:all.types.size + 1] do
          let some t := ts.back? | break
          ts := ts.pop
          let some d := fe.type? t | continue
          let comps : Array TypeRef := match d.tail with
            | .none => #[]
            | .elem x | .array x _ => #[x]
            | .struct fs | .func _ _ _ fs => fs.map (·.type)
            | .tuple x y => #[x, y]
            | .results xs => xs
          for c in comps do
            if (fe.type? c).isNone then
              if let some dc := all.type? c then
                fe := fe.add (.type c dc)
                ts := ts.push c
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
      tables, frontend := e.frontendTables, ptrCache := ptrCacheFn e.ptrCache
      typeLink := typeLinkFn e.typeLink }
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

/-- The result file of driver mode: one section `sec` (after `st.ran` passes), with its `dcllen`
when the input has one. -/
def resultText (e : ExportFile) (x : ExportExt) (sec : Section) (effects : Array Effect)
    (dclLen : Nat) : String :=
  let effects := effects.foldl (init := "") fun s e => match e with
    | .useIface a => s ++ s!"effect useiface a{a}\n"
  effects ++ printExportExt
    { e with sections := #[sec], warns := #[], typeOrder := #[], typeCmp := #[], frontend := #[] }
    { minor := x.minor, dclLen := #[(x.dclLen? 0).map fun _ => dclLen] }

/-- Driver mode: optimise the first section of `e` (format 5.1 additions `x`) from stock pass
index `start`. -/
def optimise (e : ExportFile) (x : ExportExt) (start : Nat) (partialOut : Bool)
    (stopAfter : Option String := none) : String := Id.run do
  let some s0 := e.sections[0]? | return "status error \"input\" \"no section\"\n"
  -- regalloc numbers its new autos from `dcllen` (format 5.1); the driver's own export always
  -- has it, so a missing line means a stale toolchain: fail rather than use 0.
  if (x.dclLen? 0).isNone && stopAfter.isNone then
    return "status error \"input\" \"no dcllen line (format < 5.1; rebuild the toolchain)\"\n"
  let tables := padTables (({} : Tables).addAll s0.defs) e.frontendTables
  -- the input is the driver's own export: its type order and frontend block are the function's
  let env := baseEnv e tables (wholeFile := true)
  let (stop, st) := (runFrom (m := Id) env
    (State.ofSection s0.func tables s0.zvar ((x.dclLen? 0).getD 0)) start
    (fun name _ => pure (stopAfter != some name)))
  let status := statusLine stop ++ "\n"
  let ok := match stop with | .done | .halted _ => true | _ => false
  if !ok && !partialOut then return status
  let sec : Section := { index := st.ran, pass := st.last, defs := tableDiff tables st.tables
                         func := st.func, typs := none, zvar := #[], warns := #[] }
  return status ++ resultText e x sec st.effects st.dclLen

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
  counts : Array PassCount := Array.replicate pipelinePasses.size {}
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
def checkExport (mixed wholeFile strict : Bool) (e : ExportFile) (x : ExportExt) :
    Outcome × Array PassCount × Array String := Id.run do
  let mut counts := Array.replicate pipelinePasses.size ({} : PassCount)
  let some s0 := e.sections[0]? | return (.parseError "no section", counts, #[])
  let mut base := ({} : Tables).addAll s0.defs
  let mut func := s0.func
  let mut k := 1
  let mut start := 0
  let mut stockRun := #[]
  let mut zvar := s0.zvar
  let mut dclLen := (x.dclLen? 0).getD 0
  -- regalloc numbers its new autos from `dcllen` (format 5.1): fail rather than use 0.
  if (x.dclLen? 0).isNone && e.sections.any (·.pass == "regalloc") then
    return (.error "regalloc" "no dcllen line (format < 5.1 corpus)", counts, #[])
  for _ in [0:pipelinePasses.size + 1] do
    -- Type rounds (as the driver): rerun the segment with the types the Lean passes created
    -- added to its input, so that they are ranked in the type order.
    let mut tables0 := base
    let mut out : (Stop × State) × Walk :=
      ((.done, State.ofSection func base zvar dclLen), { k, tables := base, counts })
    for round in [0:typeRounds] do
      let t0 := tables0
      let env := baseEnv e t0 wholeFile
      let step (name : String) (st : State) : StateM Walk Bool := do
        let w ← get
        let pi := (pipelineIndex? name).getD 0
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
        let d := match compare t0 { func := st.func, tables := st.tables } want s (loose := !strict) with
          | some d => some d
          | none => match x.dclLen? w.k with
            | some n => if n == st.dclLen then none else some s!"dcllen {st.dclLen}, stock {n}"
            | none => none
        match d with
        | none => set { bump true w with k := w.k + 1, tables := want }; return true
        | some d => set { bump false w with failure := some (name, d) }; return false
      out := (runFrom env (State.ofSection func t0 zvar dclLen) start step).run { k, tables := t0, counts }
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
      zvar := s.zvar
      dclLen := (x.dclLen? w.k).getD dclLen
      k := w.k + 1
      start := (pipelineIndex? p).getD 0 + 1
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
    match parseExportExt data with
    | .error e => (Outcome.parseError e, #[], #[])
    | .ok (e, x) => checkExport mixed wholeFile strict e x
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
  m.toArray.qsort fun a b => (pipelineIndex? a.1).getD 999 < (pipelineIndex? b.1).getD 999

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
  for h : i in [0:pipelinePasses.size] do
    let p := pipelinePasses[i]
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
  /-- `--verified`: the verified pipeline through `trim` (`GoFV.Opt.verifiedPipelineFull`). -/
  verified : Bool := false
  /-- `--vstats FILE` (driver mode with `--verified`): append the function's verdicts. -/
  vstats : Option String := none
  /-- `--profile` (driver mode with `--verified`): time the pipeline's pieces (stderr). -/
  profile : Bool := false
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
  | "--verified" :: rest, o => parseArgs rest { o with verified := true }
  | "--vstats" :: p :: rest, o => parseArgs rest { o with vstats := some p }
  | "--profile" :: rest, o => parseArgs rest { o with profile := true }
  | a :: rest, o =>
    if a.startsWith "--" then throw s!"unknown option {a}"
    else parseArgs rest { o with paths := o.paths.push a }

def usage : String :=
  "usage: gofv-ssa-opt [--from <pass>] [--to <pass>] [--partial] <in.ssa>\n       \
   gofv-ssa-opt --verified [--from <pass>] [--vstats FILE] [--profile] <in.ssa>\n       gofv-ssa-opt --list\n       \
   gofv-ssa-opt --check [--mixed] [--whole-file-env] [--strict] [--jobs N] [--max-report N] [--table FILE] <dir|file>...\n       \
   gofv-ssa-opt --check --verified [--whole-file-env] [--jobs N] [--max-report N] [--table FILE] <dir|file>..."

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

/-! ## `--verified` -/

open GoFV.Opt.Verified

/-- Index of pass `name` in `stockPasses ++ loweredVPasses` (the verified pipeline's passes). -/
def vIndex? (name : String) : Option Nat :=
  match passIndex? name with
  | some i => some i
  | none => (loweredVPasses.findIdx? (·.name == name)).map (stockPasses.size + ·)

/-- Whether `name` is a pass before `lower`. -/
def isGen (name : String) : Bool := (passIndex? name).isSome

/-- The first run before `lower` whose verdict is not `Verdict.ok`. -/
def firstUnverified? (st : VState) : Option (String × Verdict) :=
  st.log.find? fun (p, v) => isGen p && !v.ok

/-- The first run whose verdict is not `Verdict.ok`. -/
def firstUnverifiedFull? (st : VState) : Option (String × Verdict) := st.log.find? (!·.2.ok)

/-- The ops `Sem.evalOp` does not hand to `atomicRoot`: its explicit arms and `frameVal`'s. -/
def evalOpArms : List Op :=
  [.InitMem, .Arg, .ArgIntReg, .ArgFloatReg, .PanicBounds, .StaticLECall, .StaticCall,
   .ClosureLECall, .ClosureCall, .InterLECall, .InterCall, .GetClosurePtr, .Store, .StoreWB,
   .Move, .MoveWB, .Zero, .ZeroWB, .VarDef, .VarLive, .KeepAlive, .WBend, .NilCheck, .SP,
   .GetCallerSP, .LocalAddr, .Addr, .ConstString]

/-- `run` leaves a value of op `op` `stuck` whatever its arguments: a root (`Sem.isRoot`) that
`evalOp` hands to `atomicRoot` and that `atomicRoot` does not model (`Sem.Atomic.modelled`):
`GetG`, `TailLECall`, …. -/
def stuckOp (op : Op) : Bool :=
  Sem.isRoot op && !evalOpArms.contains op && !Sem.Atomic.modelled op

/-- `run` leaves a terminator of kind `k` `stuck` (`Sem.stepTerm`'s last arm; `Exit` is not
counted: it is reached only when a non-returning call returns). -/
def stuckKind (k : BlockKind) : Bool :=
  ![BlockKind.Plain, .First, .If, .JumpTable, .Ret, .Exit, .Defer].contains k

/-- The ops and block kinds of `f` that `run` leaves `stuck` (`stuckOp`, `stuckKind`), each once.
A refinement of `run f` says nothing about the inputs that reach one: a function containing one
is verified vacuously there. -/
def unmodelledIn (f : Func) : Array String := Id.run do
  let mut out : Array String := #[]
  for o in f.valueTab do
    if let some v := o then
      if stuckOp v.op && !out.contains v.op.name then out := out.push v.op.name
  for o in f.blockTab do
    if let some b := o then
      let k := s!"block {b.kind.name}"
      if stuckKind b.kind && !out.contains k then out := out.push k
  return out

/-- The `--vstats` fields of a verified-pipeline result (tab-separated): `verified` or
`unverified "<pass>: <verdict>"` (the first unverified run before `lower`), the number of runs
per verdict kind before `lower`, `lowered=<n>` (runs from `lower` on), and `trim=verified` or
`trim=unverified "<pass>: <verdict>"` (through `trim`, `FState.fullyVerified`). -/
def vstatsFields (fs : FState) : String :=
  let st := fs.st
  let n (p : Verdict → Bool) := (st.log.filter fun (q, v) => isGen q && p v).size
  let head := match firstUnverified? st with
    | none => "verified"
    | some (p, v) => s!"unverified {GoStr.quote s!"{p}: {v}"}"
  let full := if fs.fullyVerified then "verified" else match firstUnverifiedFull? st with
    | none => s!"unverified {GoStr.quote "not allocated"}"
    | some (p, v) => s!"unverified {GoStr.quote s!"{p}: {v}"}"
  s!"{head}\tproven={n (· == .proven)}\tidentity={n (· == .identity)}\t\
    skipped={n fun | .skipped _ => true | _ => false}\tunverified={n (!·.ok)}\t\
    lowered={(st.log.filter fun (q, _) => !isGen q).size}\ttrim={full}"

/-- Driver mode with the verified pipeline through `trim` (`GoFV.Opt.verifiedPipelineFull`):
optimise the first section of `e` (format 5.1 additions `x`) from pass index `start`. Returns
the output and the `--vstats` fields. -/
def optimiseVerified (e : ExportFile) (x : ExportExt) (start : Nat) : String × String := Id.run do
  let some s0 := e.sections[0]? | return ("status error \"input\" \"no section\"\n", "error \"input\"")
  if (x.dclLen? 0).isNone then
    return ("status error \"input\" \"no dcllen line (format < 5.1; rebuild the toolchain)\"\n",
      "error \"input\"")
  let tables := padTables (({} : Tables).addAll s0.defs) e.frontendTables
  let env := baseEnv e tables (wholeFile := true)
  match verifiedPipelineFull env s0.func start s0.zvar ((x.dclLen? 0).getD 0) with
  | .error err =>
    (s!"status error {GoStr.quote err.pass} {GoStr.quote err.msg}\n", s!"error {GoStr.quote err.pass}")
  | .ok fs =>
    let st := fs.st
    -- the importer replays regalloc's call-register caches, which the verified `regalloc` drops
    let out := if fs.layer == .loc then Regalloc.fillCallRegs env st.func st.tables else .ok st.tables
    match out with
    | .error err => (s!"status error \"regalloc\" {GoStr.quote err}\n", "error \"regalloc\"")
    | .ok tabs =>
      let sec : Section := { index := st.ran, pass := st.last, defs := tableDiff tables tabs
                             func := st.func, typs := none, zvar := #[], warns := #[] }
      ("status ok\n" ++ resultText e x sec st.effects fs.dclLen, vstatsFields fs)

/-- `k ()` and the milliseconds it took (not inlined, so the result is computed here). -/
@[noinline] def timed (k : Unit → α) : IO (α × Nat) := do
  let t ← IO.monoNanosNow
  let r ← IO.lazyPure k
  return (r, ((← IO.monoNanosNow) - t) / 1000000)

/-- `--verified --profile`: where the verified pipeline spends its time on the first section of
`e` (stderr, ms): `verifiedPipeline` (through `rewrite tern`), then per pass from `lower` on its
run, the stock port of a checked variant, `check` of the result and the theorem's guard (for
`regalloc`: `tabsAgreeL`, `RegallocCheck.certify`, `RegallocCheck.checkWith`), each timed alone;
`runPassL` then advances the chain (so each piece runs twice). -/
def profileVerified (e : ExportFile) (x : ExportExt) : IO Unit := do
  let some s0 := e.sections[0]? | IO.eprintln "profile: no section"
  let tables := padTables (({} : Tables).addAll s0.defs) e.frontendTables
  let env := baseEnv e tables (wholeFile := true)
  let (r, ms) ← timed fun _ => verifiedPipeline env s0.func 0 s0.zvar
  let .ok st := r | IO.eprintln s!"profile: verifiedPipeline: error after {ms} ms"
  IO.eprintln s!"profile: verifiedPipeline {ms} ms, {st.func.valueTab.size} values, {st.func.blocks.size} blocks, verified {st.verified}"
  let mut fs : FState :=
    { st, dclLen := (x.dclLen? 0).getD 0 + newAutos env.tables st.tables, genVerified := st.verified }
  for p in loweredVPasses do
    let penv := fs.passEnv env p.name
    let run := match p.step with | .proven run .. | .stock run => run
    let (out, tRun) ← timed fun _ => run penv fs.st.func
    let mut line := s!"{p.name}: run {tRun}"
    if let some full := p.full then
      let (so, t) ← timed fun _ => full penv fs.st.func
      line := line ++ s!", stock {t} ({so.isOk})"
    if let .ok out := out then
      let (wf, t) ← timed fun _ => outWf env p out
      line := line ++ s!", check {t} ({wf})"
      if let .proven _ _ _ guard := p.step then
        if p.name == "regalloc" then
          let (ag, t1) ← timed fun _ => LowerCheck.tabsAgreeL penv.tables out.tables fs.st.func
          let (cx, t2) ← timed fun _ => RegallocCheck.Cx.make out.tables fs.st.func out.func
          let (cert, t3) ← timed fun _ => RegallocCheck.certify cx
          let (ok, t4) ← timed fun _ => RegallocCheck.checkWith cx cert
          line := line ++ s!", tabsAgreeL {t1} ({ag}), Cx.make {t2} ({cx.krep.size}), \
            certify {t3} ({cert.ins.size}), checkWith {t4} ({ok.toBool})"
        else
          let (g, t) ← timed fun _ => guard penv fs.st.func out
          line := line ++ s!", guard {t} ({g})"
    let (r, t) ← timed fun _ => runPassL env fs p
    IO.eprintln s!"profile: {line}; runPassL {t} ms"
    match r with
    | .ok fs' => fs := fs'
    | .error err => IO.eprintln s!"profile: error {err.pass}: {err.msg}"; return
  IO.eprintln s!"profile: fully verified {fs.fullyVerified}"

/-- One function through the verified pipeline, against the stock file. -/
structure VFile where
  st : FState
  /-- The first pass whose state differs from the stock section: pass, verdict, detail. -/
  diff : Option (String × String × String)
  /-- The final state equals the last stock section (`trim`'s). -/
  same : Bool
  /-- Deadcode and copyelim runs outside their fragment: log index, pass, failing conditions
  (`FragWhy.fragWhy`). -/
  frag : Array (Nat × String × Array String) := #[]

/-- Run the verified pipeline through `trim` from section 0 of `e` (environment `env`, input
tables `t0`), comparing the state after each pass with the stock section of that pass until the
first difference (and, from `lower` on, the chain's `dcllen` with the section's), then the final
state with the last stock section. The stock tables are compared without their call-register
caches, which the verified `regalloc` drops (`GoFV.Opt.Verified.eraseCallRegs`). -/
def walkVerified (e : ExportFile) (x : ExportExt) (env : PassEnv) (t0 : Tables) (s0 : Section) :
    Except VError VFile := do
  let mut st := VState.init env s0.func s0.zvar
  let mut k := 1
  let mut want := t0
  let mut diff : Option (String × String × String) := none
  let mut frag : Array (Nat × String × Array String) := #[]
  -- the stock section `k` against the state after pass `name` (verdict `v`)
  let cmp (k : Nat) (want : Tables) (name v : String) (func : Func) (tables : Tables)
      (dcl : Option Nat) : Option (String × String × String) × Tables :=
    match e.sections[k]? with
    | none => (some (name, v, "stock has no section for this pass"), want)
    | some s =>
      if s.pass.toStringLossy != name then
        (some (name, v, s!"stock section {k} is \"{s.pass.toStringLossy}\""), want)
      else
        let want := want.addAll s.defs
        match compare t0 { func, tables } (eraseCallRegs want) s (loose := true) with
        | some d => (some (name, v, d), want)
        | none => match dcl, x.dclLen? k with
          | some n, some m => (if n == m then none else some (name, v, s!"dcllen {n}, stock {m}"), want)
          | _, _ => (none, want)
  for p in stockPasses do
    let st' ← runPass env st p
    if st'.log.size > st.log.size then
      match st'.log.back? with
      | some (_, .unverified "fragment") | some (_, .skipped "fragment") =>
        let w := FragWhy.fragWhy p.name (st.passEnv env p.name) st.func
        if !w.isEmpty then frag := frag.push (st.log.size, p.name, w)
      | _ => pure ()
      if diff.isNone then
        let v := match st'.log.back? with | some (_, v) => toString v | none => "-"
        let (d, w) := cmp k want p.name v st'.func st'.tables none
        diff := d; want := w
      k := k + 1
    st := st'
  let mut fs : FState :=
    { st, dclLen := (x.dclLen? 0).getD 0 + newAutos t0 st.tables, genVerified := st.verified }
  for p in loweredVPasses do
    let fs' ← runPassL env fs p
    if fs'.st.log.size > fs.st.log.size then
      if diff.isNone then
        let v := match fs'.st.log.back? with | some (_, v) => toString v | none => "-"
        let (d, w) := cmp k want p.name v fs'.st.func fs'.st.tables (some fs'.dclLen)
        diff := d; want := w
      k := k + 1
    fs := fs'
  if diff.isNone && k == e.sections.size then return { st := fs, diff, same := true, frag }
  if diff.isNone then
    diff := some (fs.st.last, "-", s!"{e.sections.size - k} stock sections after the last pass")
  let wantAll := (e.sections.extract 1 e.sections.size).foldl (fun t s => t.addAll s.defs) t0
  let same := match e.sections.back? with
    | some s => k == e.sections.size &&
      (compare t0 { func := fs.st.func, tables := fs.st.tables } (eraseCallRegs wantAll) s
        (loose := true)).isNone
    | none => false
  return { st := fs, diff, same, frag }

/-- The verified pipeline on one export file, with the driver's type rounds. -/
def verifiedExport (wholeFile : Bool) (e : ExportFile) (x : ExportExt) :
    Except String (Except VError VFile) := do
  let some s0 := e.sections[0]? | throw "no section"
  if (x.dclLen? 0).isNone && e.sections.any (·.pass == "regalloc") then
    throw "no dcllen line (format < 5.1 corpus)"
  let mut t0 := ({} : Tables).addAll s0.defs
  let mut res : Except VError VFile := .error ⟨"start", "no round"⟩
  for round in [0:typeRounds] do
    res := walkVerified e x (baseEnv e t0 wholeFile) t0 s0
    let .ok r := res | break
    let added := stockTypesFor e.frontendTables t0 r.st.st.tables
    if added.isEmpty || round + 1 == typeRounds then break
    t0 := t0.addAll added
  return res

/-- Per pass: runs by verdict kind, and functions whose first difference from stock is at
this pass. -/
structure VCount where
  runs : Nat := 0
  proven : Nat := 0
  identity : Nat := 0
  skipped : Nat := 0
  unverified : Nat := 0
  diverged : Nat := 0
  deriving Inhabited

def VCount.add (a b : VCount) : VCount :=
  { runs := a.runs + b.runs, proven := a.proven + b.proven, identity := a.identity + b.identity
    skipped := a.skipped + b.skipped, unverified := a.unverified + b.unverified
    diverged := a.diverged + b.diverged }

structure VStats where
  files : Nat := 0
  parseErrors : Nat := 0
  /-- Pass errors, by pass. -/
  errors : Std.HashMap String Nat := {}
  /-- Fully verified through `rewrite tern` (every run before `lower` ok). -/
  verified : Nat := 0
  /-- Fully verified through `trim` (`FState.fullyVerified`). -/
  verifiedFull : Nat := 0
  same : Nat := 0
  both : Nat := 0
  bothFull : Nat := 0
  /-- Of `verified` / `verifiedFull`: those whose input has an op or block kind `run` leaves
  `stuck` (`unmodelledIn`): verified vacuously on the inputs that reach one. -/
  vacuous : Nat := 0
  vacuousFull : Nat := 0
  /-- The vacuously verified functions (through `rewrite tern`, through `trim`) by each such op
  or block kind of their input. -/
  vacuousBy : Std.HashMap String Nat := {}
  vacuousByFull : Std.HashMap String Nat := {}
  /-- Unverified functions by their first unverified run before `lower` (`pass: verdict`). -/
  firstUnverified : Std.HashMap String Nat := {}
  /-- Functions verified through `rewrite tern` but not through `trim`, by their first unverified
  run from `lower` on. -/
  firstUnverifiedLow : Std.HashMap String Nat := {}
  /-- Skipped and unverified runs (`pass: verdict`). -/
  reasons : Std.HashMap String Nat := {}
  /-- Functions whose state first differs from stock after a pass (`pass: verdict`). -/
  diverged : Std.HashMap String Nat := {}
  counts : Array VCount := Array.replicate (stockPasses.size + loweredVPasses.size) {}
  reports : Array (String × String × String) := #[]
  /-- Deadcode/copyelim runs outside their fragment, by failing condition (`pass: condition`,
  one count per failing condition of each run). -/
  fragAll : Std.HashMap String Nat := {}
  /-- First unverified runs outside their fragment, by their failing conditions. -/
  fragFirst : Std.HashMap String Nat := {}
  /-- Functions whose only unverified runs are deadcode runs outside their fragment, by the
  failing conditions of those runs (what widening them would verify). -/
  fragOnly : Std.HashMap String Nat := {}

def VStats.merge (a b : VStats) : VStats :=
  let mm (x y : Std.HashMap String Nat) := y.fold (fun m k n => bumpMap m k n) x
  { files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors
    errors := mm a.errors b.errors, verified := a.verified + b.verified
    verifiedFull := a.verifiedFull + b.verifiedFull, same := a.same + b.same
    both := a.both + b.both, bothFull := a.bothFull + b.bothFull
    vacuous := a.vacuous + b.vacuous, vacuousFull := a.vacuousFull + b.vacuousFull
    vacuousBy := mm a.vacuousBy b.vacuousBy, vacuousByFull := mm a.vacuousByFull b.vacuousByFull
    firstUnverified := mm a.firstUnverified b.firstUnverified
    firstUnverifiedLow := mm a.firstUnverifiedLow b.firstUnverifiedLow
    reasons := mm a.reasons b.reasons, diverged := mm a.diverged b.diverged
    counts := (a.counts.zip b.counts).map fun (x, y) => x.add y
    reports := a.reports ++ b.reports, fragAll := mm a.fragAll b.fragAll
    fragFirst := mm a.fragFirst b.fragFirst, fragOnly := mm a.fragOnly b.fragOnly }

def verifiedFile (wholeFile : Bool) (maxReport : Nat) (path : System.FilePath) (st : VStats) :
    IO VStats := do
  let data ← IO.FS.readBinFile path
  let st := { st with files := st.files + 1 }
  let report (st : VStats) (kind detail : String) : VStats :=
    if (st.reports.filter (·.2.1 == kind)).size < maxReport then
      { st with reports := st.reports.push (path.toString, kind, detail) }
    else st
  match parseExportExt data >>= fun (e, x) =>
      (verifiedExport wholeFile e x).map fun r => (r, (e.sections[0]?.map (unmodelledIn ·.func)).getD #[]) with
  | .error m =>
    IO.eprintln s!"PARSE ERROR {path}: {m}"
    return { st with parseErrors := st.parseErrors + 1 }
  | .ok (.error err, _) =>
    return report { st with errors := bumpMap st.errors err.pass } s!"error {err.pass}" err.msg
  | .ok (.ok r, stuck) =>
    let mut st := st
    let log := r.st.st.log
    for (name, v) in log do
      let some i := vIndex? name | continue
      st := { st with counts := st.counts.modify i fun c => match v with
        | .proven => { c with runs := c.runs + 1, proven := c.proven + 1 }
        | .identity => { c with runs := c.runs + 1, identity := c.identity + 1 }
        | .skipped _ => { c with runs := c.runs + 1, skipped := c.skipped + 1 }
        | .unverified _ => { c with runs := c.runs + 1, unverified := c.unverified + 1 } }
      match v with
      | .skipped _ | .unverified _ => st := { st with reasons := bumpMap st.reasons s!"{name}: {v}" }
      | _ => pure ()
    let verified := r.st.genVerified
    let full := r.st.fullyVerified
    st := { st with verified := st.verified + (if verified then 1 else 0)
                    verifiedFull := st.verifiedFull + (if full then 1 else 0)
                    same := st.same + (if r.same then 1 else 0)
                    both := st.both + (if verified && r.same then 1 else 0)
                    bothFull := st.bothFull + (if full && r.same then 1 else 0) }
    if !stuck.isEmpty then
      if verified then
        st := { st with vacuous := st.vacuous + 1
                        vacuousBy := stuck.foldl (fun m k => bumpMap m k) st.vacuousBy }
      if full then
        st := { st with vacuousFull := st.vacuousFull + 1
                        vacuousByFull := stuck.foldl (fun m k => bumpMap m k) st.vacuousByFull }
    if let some (p, v) := firstUnverified? r.st.st then
      st := { st with firstUnverified := bumpMap st.firstUnverified s!"{p}: {v}" }
    else if !full then
      let k := match firstUnverifiedFull? r.st.st with
        | some (p, v) => s!"{p}: {v}"
        | none => "not allocated"
      st := { st with firstUnverifiedLow := bumpMap st.firstUnverifiedLow k }
    for (_, p, ws) in r.frag do
      for w in ws do
        let k := s!"{p}: {FragWhy.whyKey w}"
        st := report { st with fragAll := bumpMap st.fragAll k } s!"fragment {k}" w
    let bad := (List.range log.size).filter fun i => isGen log[i]!.1 && !(log[i]!.2.ok)
    if let some i := bad.head? then
      if let some (_, p, ws) := r.frag.find? (·.1 == i) then
        let ks := ws.toList.map FragWhy.whyKey
        st := { st with fragFirst := bumpMap st.fragFirst s!"{p}: {" | ".intercalate ks}" }
      if bad.all fun j => r.frag.any (·.1 == j) then
        let ws := (r.frag.filter fun (j, _) => bad.contains j).toList.flatMap fun (_, _, ws) =>
          ws.toList.map FragWhy.whyKey
        let key := " | ".intercalate (ws.eraseDups.mergeSort (· ≤ ·))
        st := { st with fragOnly := bumpMap st.fragOnly key }
    if let some (p, v, d) := r.diff then
      st := { st with diverged := bumpMap st.diverged s!"{p}: {v}" }
      if let some i := vIndex? p then
        st := { st with counts := st.counts.modify i fun c => { c with diverged := c.diverged + 1 } }
      st := report st s!"differs {p}" d
    return st

/-- Keys `<pass>: …` in pass order. -/
def sortedPassMap (m : Std.HashMap String Nat) : Array (String × Nat) :=
  let key (s : String) := (vIndex? ((s.splitOn ": ").headD s)).getD 999
  m.toArray.qsort fun a b => key a.1 < key b.1 || (key a.1 == key b.1 && a.1 < b.1)

def verifiedText (st : VStats) (ms : Nat) : String := Id.run do
  let n (m : Std.HashMap String Nat) := m.fold (fun a _ x => a + x) 0
  let fns := st.files - st.parseErrors - n st.errors
  let mut out := s!"files: {st.files}, parse errors: {st.parseErrors}, wall: {ms / 1000} s\n\n"
  out := out ++ s!"- functions through the verified pipeline: {fns} (pass errors: {n st.errors})\n"
  for (p, c) in sortedPassMap st.errors do out := out ++ s!"  - error at `{p}`: {c}\n"
  out := out ++ "\n| | through `rewrite tern` | through `trim` |\n| --- | ---: | ---: |\n"
  out := out ++ s!"| fully verified (every run proven, identity or skipped) | {st.verified} | {st.verifiedFull} |\n"
  out := out ++ s!"| … verified (vacuous: unmodelled op), input has an op or block kind `run` leaves stuck | {st.vacuous} | {st.vacuousFull} |\n"
  out := out ++ s!"| … verified, no unmodelled op | {st.verified - st.vacuous} | {st.verifiedFull - st.vacuousFull} |\n"
  out := out ++ s!"| … and identical to stock after `trim` | {st.both} | {st.bothFull} |\n\n"
  out := out ++ s!"- verified-pipeline output identical to stock after `trim` (compared as the importer): {st.same}\n"
  out := out ++ s!"- verified (vacuous: unmodelled op), by op or block kind (through `rewrite tern` / through `trim`):\n"
  let keys := (st.vacuousBy.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)).map (·.1)
  for k in keys do out := out ++ s!"  - `{k}`: {st.vacuousBy.getD k 0} / {st.vacuousByFull.getD k 0}\n"
  out := out ++ s!"- unverified functions by first unverified run before `lower`: {n st.firstUnverified}\n"
  for (k, c) in sortedPassMap st.firstUnverified do out := out ++ s!"  - `{k}`: {c}\n"
  out := out ++ s!"- verified through `rewrite tern`, not through `trim`, by first unverified run: {n st.firstUnverifiedLow}\n"
  for (k, c) in sortedPassMap st.firstUnverifiedLow do out := out ++ s!"  - `{k}`: {c}\n"
  out := out ++ s!"- functions by first difference from stock (pass: its verdict): {n st.diverged}\n"
  for (k, c) in sortedPassMap st.diverged do out := out ++ s!"  - `{k}`: {c}\n"
  out := out ++ "\n| pass | step | runs | proven | identity | skipped | unverified | first difference |\n"
  out := out ++ "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |\n"
  let rows : Array (String × String) :=
    stockPasses.map (fun p => (p.name, match p.step with | .proven .. => "proven" | .stock _ => "stock")) ++
    loweredVPasses.map fun p => (p.name, match p.step with | .proven .. => "proven" | .stock _ => "stock")
  for h : i in [0:rows.size] do
    let (name, kind) := rows[i]
    let c := st.counts[i]!
    out := out ++ s!"| {name} | {kind} | {c.runs} | {c.proven} | {c.identity} | {c.skipped} | {c.unverified} | {c.diverged} |\n"
  out := out ++ "\nSkipped and unverified runs by reason:\n\n"
  for (k, c) in sortedPassMap st.reasons do out := out ++ s!"- `{k}`: {c}\n"
  let byCount (m : Std.HashMap String Nat) := m.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
  if !st.fragAll.isEmpty then
    out := out ++ "\nDeadcode/copyelim fragment conditions failing (`FragWhy`), per run:\n\n"
    for (k, c) in sortedPassMap st.fragAll do out := out ++ s!"- `{k}`: {c}\n"
    out := out ++ "\nFirst unverified runs outside the deadcode/copyelim fragment, by failing conditions:\n\n"
    for (k, c) in byCount st.fragFirst do out := out ++ s!"- `{k}`: {c}\n"
    out := out ++ "\nFunctions unverified only by deadcode fragment failures, by failing conditions:\n\n"
    for (k, c) in byCount st.fragOnly do out := out ++ s!"- `{k}`: {c}\n"
  return out

/-- `--check --verified`: the verified pipeline over stock export files, a report (exit 1 only
for parse errors or no files). -/
def runVerifiedCheck (o : Opts) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let mut files := #[]
  for p in o.paths do files := files ++ (← ssaFiles p)
  -- a shared queue: a few functions take minutes (`prove`'s validator), so a static split
  -- would leave workers idle
  let next ← IO.mkRef 0
  let tasks ← (List.range o.jobs).toArray.mapM fun _ => IO.asTask (prio := .dedicated) do
    let mut st : VStats := {}
    for _ in [0:files.size] do
      let i ← next.modifyGet fun i => (i, i + 1)
      let some file := files[i]? | break
      let t0 ← IO.monoMsNow
      st ← verifiedFile o.wholeFile o.maxReport file st
      let ms := (← IO.monoMsNow) - t0
      if ms ≥ 60000 then IO.eprintln s!"SLOW {ms / 1000} s: {file}"
    return st
  let mut st : VStats := {}
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
  let text := verifiedText st ms
  IO.print text
  if let some p := o.table then IO.FS.writeFile p text
  return if st.parseErrors > 0 || st.files == 0 then 1 else 0

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; IO.eprintln usage; return 2
  if o.list then
    for p in pipelinePasses do
      IO.println s!"{if (port? p.name).isSome then "ported" else "unported"} {GoStr.quote p.name}"
    return 0
  if o.check then
    if o.paths.isEmpty then IO.eprintln usage; return 2
    if o.verified then return ← runVerifiedCheck o
    return ← runCheck o
  let #[path] := o.paths | IO.eprintln usage; return 2
  let start ← match o.start with
    | none => pure 0
    | some p => match pipelineIndex? p with
      | some i => pure i
      | none => IO.eprintln s!"--from {p}: not a stock pass"; return 2
  let data ← IO.FS.readBinFile path
  match parseExportExt data with
  | .error e =>
    IO.println s!"status error \"parse\" {GoStr.quote e}"
    return 0
  | .ok (e, x) =>
    if o.verified && o.profile then
      profileVerified e x
      return 0
    if o.verified then
      let (out, fields) ← IO.lazyPure fun _ => optimiseVerified e x start
      (← IO.getStdout).putStr out
      if let some p := o.vstats then
        let h ← IO.FS.Handle.mk p .append
        h.putStr s!"{GoStr.quote e.pkg}\t{GoStr.quote e.name}\t{e.abi}\t{fields}\n"
      return 0
    let out ← IO.lazyPure fun _ => optimise e x start o.partialOut o.stopAfter
    (← IO.getStdout).putStr out
    return 0

end GoFVTest.Driver

def main (args : List String) : IO UInt32 := GoFVTest.Driver.main args
