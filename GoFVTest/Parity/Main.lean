import GoFVTest.Parity.Registry
import GoFVTest.Parity.Compare
import GoFV.SSA.Parse

/-!
# `pass-parity`

Per-pass stock parity (`docs/PARITY.md`, `docs/PLAN.md` §2). For every `*.ssa` export file and
every section `k` whose pass is a selected stock pass, run the Lean port on section `k-1`'s
function with the tables in force for `k-1`, print the result and compare it byte for byte with
section `k`'s function. Definitions the pass creates or redefines must equal section `k`'s at the
same numbers. A pass with a `disabled` condition is also checked to have no section in the files
where it is disabled.

usage: `pass-parity [--pass <fn|stock name|all>]... [--jobs N] [--max-report N] [--table FILE]
<dir|file>...`; exit status 1 on any mismatch, pass error or parse error.
-/

open GoFV.SSA GoFV.Opt

namespace GoFVTest.Parity

/-- One selected stock pass instance. -/
structure Inst where
  name : String
  entry : PassEntry

/-- Per-instance counters. -/
structure Count where
  /-- Functions with at least one section of this pass. -/
  funcs : Nat := 0
  runs : Nat := 0
  same : Nat := 0
  mismatches : Nat := 0
  /-- Of the mismatches, how many were pass errors (`Except.error`). -/
  errors : Nat := 0
  /-- Files where the pass is disabled (and correctly has no section). -/
  disabled : Nat := 0
  /-- Of the matches, how many needed the map order replayed from the stock output
  (`PassEntry.replay`). -/
  replayed : Nat := 0
  ns : Nat := 0
  deriving Inhabited

def Count.add (a b : Count) : Count :=
  { funcs := a.funcs + b.funcs, runs := a.runs + b.runs, same := a.same + b.same
    mismatches := a.mismatches + b.mismatches, errors := a.errors + b.errors
    disabled := a.disabled + b.disabled, replayed := a.replayed + b.replayed, ns := a.ns + b.ns }

structure Report where
  inst : Nat
  file : String
  sec : Nat
  detail : String

structure Stats where
  files : Nat := 0
  parseErrors : Nat := 0
  counts : Array Count
  reports : Array Report := #[]

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors
    counts := (a.counts.zip b.counts).map fun (x, y) => x.add y
    reports := a.reports ++ b.reports }

def addReport (st : Stats) (maxReport : Nat) (r : Report) : Stats :=
  if (st.reports.filter (·.inst == r.inst)).size < maxReport then
    { st with reports := st.reports.push r }
  else st

def bump (st : Stats) (i : Nat) (g : Count → Count) : Stats :=
  { st with counts := st.counts.modify i g }

/-- The pseudo pass instance of `--check-renumber`. -/
def renumberCheck : String := "renumber self-check"

/-- A section's `zvar` as a lookup (`PassEnv.zvar`). -/
def zvarFn (zv : Array (ID × Nat)) : ID → Nat :=
  let m : Std.HashMap ID Nat := zv.foldl (fun m (v, c) => m.insert v c) {}
  fun i => m.getD i 0

/-- The file's `ptrcache` as a predicate (`PassEnv.ptrCache`). -/
def ptrCacheFn (ts : Array TypeRef) : TypeRef → Bool :=
  let m : Std.HashMap TypeRef Unit := ts.foldl (fun m t => m.insert t ()) {}
  fun t => m.contains t

def checkFile (insts : Array Inst) (maxReport : Nat) (path : System.FilePath) (st : Stats) :
    IO Stats := do
  let data ← IO.FS.readBinFile path
  let st := { st with files := st.files + 1 }
  match parseExport data with
  | .error e =>
    IO.eprintln s!"PARSE ERROR {path}: {e}"
    return { st with parseErrors := st.parseErrors + 1 }
  | .ok e =>
    let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
    let base : PassEnv :=
      { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
        pgohot := e.pgohot, config := e.config, typs, typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
        tables := {}, frontend := e.frontendTables, ptrCache := ptrCacheFn e.ptrCache }
    let mut st := st
    let mut seen := Array.replicate insts.size false
    let mut tables : Tables := {}
    let mut prev : Tables := {}
    let mut sec0 : Tables := {}
    for h : k in [0:e.sections.size] do
      let s := e.sections[k]
      prev := tables
      tables := tables.addAll s.defs
      if k == 0 then sec0 := tables; continue
      let name := s.pass.toStringLossy
      -- `--check-renumber`: stock output with renumbered new objects must compare equal
      if let some ri := insts.findIdx? (·.name == renumberCheck) then
        if !s.defs.isEmpty then
          let (lf, lt) := shuffledStock prev s
          if !seen[ri]! then
            seen := seen.set! ri true
            st := bump st ri fun c => { c with funcs := c.funcs + 1 }
          st := bump st ri fun c => { c with runs := c.runs + 1 }
          match compare prev { func := lf, tables := lt } tables s with
          | none => st := bump st ri fun c => { c with same := c.same + 1 }
          | some d =>
            st := bump st ri fun c => { c with mismatches := c.mismatches + 1 }
            st := addReport st maxReport ⟨ri, path.toString, k, d⟩
      for h : ii in [0:insts.size] do
        let inst := insts[ii]
        if inst.name != name then continue
        let env := { base with passName := name, tables := prev
                               zvar := zvarFn e.sections[k-1]!.zvar }
        let input := e.sections[k-1]!.func
        let t0 ← IO.monoNanosNow
        let r ← IO.lazyPure fun _ => inst.entry.run env input
        let t1 ← IO.monoNanosNow
        if !seen[ii]! then
          seen := seen.set! ii true
          st := bump st ii fun c => { c with funcs := c.funcs + 1 }
        st := bump st ii fun c => { c with runs := c.runs + 1, ns := c.ns + (t1 - t0) }
        let detail : Option String := match r with
          | .error msg => some s!"pass error: {msg}"
          | .ok out => compare prev out tables s
        -- randomized map order: retry with the order the stock output shows
        let replayed := match detail, r, inst.entry.replay with
          | some _, .ok _, some rp =>
            match rp env input s.func with
            | .ok out => (compare prev out tables s).isNone
            | .error _ => false
          | _, _, _ => false
        let detail := if replayed then none else detail
        if replayed then st := bump st ii fun c => { c with replayed := c.replayed + 1 }
        match detail with
        | none => st := bump st ii fun c => { c with same := c.same + 1 }
        | some d =>
          let isErr := match r with | .error _ => 1 | .ok _ => 0
          st := bump st ii fun c => { c with mismatches := c.mismatches + 1, errors := c.errors + isErr }
          st := addReport st maxReport ⟨ii, path.toString, k, d⟩
    -- disabled passes: no section where Go's `disabled` holds
    for h : ii in [0:insts.size] do
      let inst := insts[ii]
      match inst.entry.disabled { base with passName := inst.name, tables := sec0 } with
      | .ok false => pure ()
      | .ok true =>
        if seen[ii]! then
          st := bump st ii fun c => { c with mismatches := c.mismatches + 1 }
          st := addReport st maxReport ⟨ii, path.toString, 0, "pass is disabled but has a section"⟩
        else st := bump st ii fun c => { c with disabled := c.disabled + 1 }
      | .error msg =>
        st := bump st ii fun c => { c with mismatches := c.mismatches + 1, errors := c.errors + 1 }
        st := addReport st maxReport ⟨ii, path.toString, 0, s!"disabled check: {msg}"⟩
    return st

def ssaFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "ssa")).qsort (·.toString < ·.toString)
  else return #[p]

structure Opts where
  passes : Array String := #[]
  jobs : Nat := 1
  maxReport : Nat := 10
  table : Option String := none
  checkRenumber : Bool := false
  paths : Array String := #[]

partial def parseArgs : List String → Opts → Except String Opts
  | [], o => pure o
  | "--pass" :: p :: rest, o => parseArgs rest { o with passes := o.passes.push p }
  | "--jobs" :: n :: rest, o => do
    let some n := n.toNat? | throw s!"--jobs {n}: not a number"
    parseArgs rest { o with jobs := max n 1 }
  | "--max-report" :: n :: rest, o => do
    let some n := n.toNat? | throw s!"--max-report {n}: not a number"
    parseArgs rest { o with maxReport := n }
  | "--table" :: p :: rest, o => parseArgs rest { o with table := some p }
  | "--check-renumber" :: rest, o => parseArgs rest { o with checkRenumber := true }
  | a :: rest, o =>
    if a.startsWith "--" then throw s!"unknown option {a}"
    else parseArgs rest { o with paths := o.paths.push a }

/-- Instances selected by `--pass` (default: all), in registry order. -/
def select (sel : Array String) : Except String (Array Inst) := do
  let all := registry.flatMap fun e => e.names.map fun n => ({ name := n, entry := e } : Inst)
  if sel.isEmpty || sel.contains "all" then return all
  for p in sel do
    if !all.any (fun i => i.name == p || i.entry.fn == p) then throw s!"unknown pass {p}"
  return all.filter fun i => sel.any fun p => i.name == p || i.entry.fn == p

def pct (a b : Nat) : String :=
  if b == 0 then "-" else
  let x := a * 10000 / b
  s!"{x / 100}.{if x % 100 < 10 then "0" else ""}{x % 100}%"

def tableText (insts : Array Inst) (st : Stats) (ms : Nat) : String := Id.run do
  let mut out := s!"files: {st.files}, parse errors: {st.parseErrors}, wall: {ms / 1000} s\n\n"
  out := out ++ "| pass | fn | functions | runs | match | of which order replayed | mismatch | errors | disabled in | parity | pass time (s) |\n"
  out := out ++ "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n"
  for h : i in [0:insts.size] do
    let c := st.counts[i]!
    let inst := insts[i]
    let parity := if c.runs == 0 && c.mismatches == 0 then
        (if c.disabled > 0 then "disabled" else "-") else pct c.same c.runs
    let replayed := if inst.entry.replay.isSome then toString c.replayed else "-"
    out := out ++ s!"| {inst.name} | {inst.entry.fn} | {c.funcs} | {c.runs} | {c.same} | \
      {replayed} | {c.mismatches} | {c.errors} | {c.disabled} | {parity} | {c.ns / 1000000000}.{(c.ns / 100000000) % 10} |\n"
  return out

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  if o.paths.isEmpty then
    IO.eprintln "usage: pass-parity [--pass <fn|stock name|all>]... [--jobs N] [--max-report N] [--table FILE] [--check-renumber] <dir|file>..."
    return 2
  let insts ← match select o.passes with
    | .ok i => pure i
    | .error e => IO.eprintln e; return 2
  let insts := if o.checkRenumber then
      insts.push { name := renumberCheck,
                   entry := { fn := "renumber", names := #[], run := fun _ _ => throw "" } }
    else insts
  let t0 ← IO.monoMsNow
  let mut files := #[]
  for p in o.paths do files := files ++ (← ssaFiles p)
  let empty : Stats := { counts := Array.replicate insts.size {} }
  -- `jobs` workers, each streaming its share of the files (round robin) with constant memory
  let tasks ← (List.range o.jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st := empty
    for h : i in [0:files.size] do
      if i % o.jobs == j then st ← checkFile insts o.maxReport files[i] st
    return st
  let mut st := empty
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 2
  let ms := (← IO.monoMsNow) - t0
  let reports := st.reports.qsort fun a b => a.inst < b.inst || (a.inst == b.inst &&
    (a.file < b.file || (a.file == b.file && a.sec < b.sec)))
  let mut shown := Array.replicate insts.size 0
  for r in reports do
    if shown[r.inst]! < o.maxReport then
      shown := shown.modify r.inst (· + 1)
      IO.println s!"MISMATCH {(insts[r.inst]?.map (·.name)).getD "?"}: {r.file} section {r.sec}: {r.detail}"
  let text := tableText insts st ms
  IO.print text
  if let some p := o.table then IO.FS.writeFile p text
  let bad := st.parseErrors > 0 || st.counts.any (·.mismatches > 0) || st.files == 0
  return if bad then 1 else 0

end GoFVTest.Parity

def main (args : List String) : IO UInt32 := GoFVTest.Parity.main args
