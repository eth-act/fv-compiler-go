import GoFV.Dwarf.Debug
import GoFV.Asm.Parse
import GoFV.SSA.Parse

/-!
# `debug-parity`: Phase 3 E1 parity (`ssa.BuildFuncDebug`)

For every `*.prog` file (`gofv-prog 3`, `docs/contracts/export.md`) under the given directories
with its companion `.ssa` file (same stem), runs `GoFV.Dwarf.buildFuncDebug` on the function
after `trim` (`GoFV.Gen.Env.load`) and the exported frame after `AllocFrame` (the `frame`
section's `out` and `opt` lines), and compares the result with the `prog0` section's `dbg*`
lines:

1. `dbgentry`: `FuncDebug.EntryID`;
2. `dbgslot`: `Slots` by `SlotID` (name by its `.ssa` aux link, type by `String()` and size,
   offset);
3. `dbgvar`: `Vars` with `VarSlots`;
4. `dbgloc`: every nonempty `LocationLists[VarID]`, entries with their SSA coordinates and the
   DWARF expression bytes, exactly.

`dbgregout` (`RegOutputParams`, set by `buildssa`) and `dbgpc` (`GetPC`) are not part of
`BuildFuncDebug`. Each mismatch is reported with a class (the first differing item) and counted
per class.

usage: `lake exe debug-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>...`; exit
status 1 on any mismatch, port error or parse error.
-/

open GoFV.SSA (GoStr ExportFile SlotDef)
open GoFV.Asm
open GoFV.Gen (Env)
open GoFV.Dwarf

namespace GoFVTest.DebugParity

/-! ## Results -/

structure Report where
  file : String
  cls : String
  msg : String

structure Stats where
  files : Nat := 0
  parseErrors : Nat := 0
  match_ : Nat := 0
  slots : Nat := 0
  vars : Nat := 0
  lists : Nat := 0
  entries : Nat := 0
  synthFuncs : Nat := 0
  synthValues : Nat := 0
  classes : Std.HashMap String Nat := {}
  reports : Array Report := #[]
  perClassReports : Std.HashMap String Nat := {}

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors,
    match_ := a.match_ + b.match_, slots := a.slots + b.slots, vars := a.vars + b.vars,
    lists := a.lists + b.lists, entries := a.entries + b.entries,
    synthFuncs := a.synthFuncs + b.synthFuncs, synthValues := a.synthValues + b.synthValues,
    classes := b.classes.fold (fun m k v => m.alter k (some <| ·.getD 0 + v)) a.classes,
    reports := a.reports ++ b.reports,
    perClassReports := b.perClassReports.fold (fun m k v => m.alter k (some <| ·.getD 0 + v))
      a.perClassReports }

def Stats.record (st : Stats) (maxReport : Nat) (file cls msg : String) : Stats :=
  let n := st.perClassReports.getD cls 0
  let st := { st with classes := st.classes.alter cls (some <| ·.getD 0 + 1),
                      perClassReports := st.perClassReports.insert cls (n + 1) }
  if n < maxReport then { st with reports := st.reports.push { file, cls, msg } } else st

def errClass (stage msg : String) : String :=
  let head := (msg.splitOn ":").headD msg
  s!"{stage}:error:{head.take 60}"

/-! ## Canonical forms -/

/-- A slot: `.ssa` name aux, type `String()`, type size, offset. -/
structure CSlot where
  name : Option Nat
  type : String
  size : Option Int
  off : Int

def CSlot.str (s : CSlot) : String :=
  s!"a{s.name.map toString |>.getD "?"} {s.type}/{s.size.map toString |>.getD "?"} {s.off}"

/-- Equal names, types and offsets; sizes when both are known (`?` in either file). -/
def CSlot.eq (a b : CSlot) : Bool :=
  a.name == b.name && a.type == b.type && a.off == b.off &&
    (match a.size, b.size with | some x, some y => x == y | _, _ => true)

def hex (b : ByteArray) : String :=
  if b.size == 0 then "-" else
  String.join (b.toList.map fun x =>
    let d := fun (n : UInt8) => if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)
    s!"{d (x / 16)}{d (x % 16)}")

def entryStr (e : LocEntry) : String :=
  s!"{e.startBlock}:{e.startValue}:{e.endBlock}:{e.endValue}:{hex e.expr}"

def listStr (es : Array LocEntry) : String := ",".intercalate (es.toList.map entryStr)

/-- The first difference between two lists of one variable. -/
def listDiff (ours stock : Array LocEntry) : Option String := Id.run do
  for k in [0:max ours.size stock.size] do
    match ours[k]?, stock[k]? with
    | some a, some b =>
      if a == b then continue
      if (a.startBlock, a.startValue) != (b.startBlock, b.startValue) then return some "start"
      if (a.endBlock, a.endValue) != (b.endBlock, b.endValue) then return some "end"
      return some "expr"
    | some _, none => return some "extra-entry"
    | none, some _ => return some "missing-entry"
    | none, none => pure ()
  return none

/-! ## Comparison -/

def compare (env : Env) (pf : ProgFile) (out : DebugOut) (dbg : FuncDebug) :
    Option (String × String) := Id.run do
  let mut pnames : Std.HashMap Nat NameDef := {}
  let mut ptypes : Std.HashMap Nat TypeDef := {}
  for d in pf.frame.defs ++ pf.genin.defs ++ pf.prog0.defs do
    match d with
    | .name k nd => pnames := pnames.insert k nd
    | .type k t => ptypes := ptypes.insert k t
    | _ => pure ()
  if (out.entry : Int) != dbg.entry then
    return some ("entry", s!"port b{out.entry}, stock {dbg.entry}")
  let ourSlot := fun (s : SlotDef) =>
    let td := env.tabs.type? s.type
    { name := some s.name, type := (td.map (·.str.toStringLossy)).getD s!"t{s.type}?",
      size := td.bind (·.size), off := s.off : CSlot }
  let stockSlot := fun ((n, t, off) : Nat × Option Nat × Int) =>
    let td := t.bind (ptypes[·]?)
    { name := (pnames[n]?).bind (·.aux), type := (td.map (·.str.toStringLossy)).getD "-",
      size := td.bind (·.size), off : CSlot }
  let os := out.slots.map ourSlot
  let ss := dbg.slots.map stockSlot
  for k in [0:max os.size ss.size] do
    match os[k]?, ss[k]? with
    | some a, some b =>
      if !a.eq b then
        let what := if a.name != b.name then "name" else if a.type != b.type then "type"
          else if a.off != b.off then "off" else "size"
        return some (s!"slots:{what}", s!"slot {k}: port {a.str}, stock {b.str}")
    | some a, none => return some ("slots:extra", s!"slot {k}: port has extra {a.str}")
    | none, some b => return some ("slots:missing", s!"slot {k}: port lacks {b.str}")
    | none, none => pure ()
  let ov := (out.vars.zip out.varSlots).map fun (a, vs) => (some a, vs)
  let sv := dbg.vars.map fun (n, vs) => ((pnames[n]?).bind (·.aux), vs)
  for k in [0:max ov.size sv.size] do
    let fmt := fun ((a, vs) : Option Nat × Array Nat) =>
      s!"a{a.map toString |>.getD "?"} {vs.toList}"
    match ov[k]?, sv[k]? with
    | some a, some b =>
      if a != b then
        return some (if a.1 != b.1 then "vars:name" else "vars:slots",
          s!"var {k}: port {fmt a}, stock {fmt b}")
    | some a, none => return some ("vars:extra", s!"var {k}: port has extra {fmt a}")
    | none, some b => return some ("vars:missing", s!"var {k}: port lacks {fmt b}")
    | none, none => pure ()
  let ol : Array (Nat × Array LocEntry) := Id.run do
    let mut r := #[]
    for h : i in [0:out.lists.size] do
      if !out.lists[i].isEmpty then r := r.push (i, out.lists[i])
    return r
  for k in [0:max ol.size dbg.lists.size] do
    match ol[k]?, dbg.lists[k]? with
    | some (i, a), some (j, b) =>
      if i != j then
        let (cls, v) := if i < j then ("lists:extra-list", i) else ("lists:missing-list", j)
        return some (cls, s!"var {v}: port {listStr ((ol.find? (·.1 == v)).map (·.2) |>.getD #[])}, \
          stock {listStr ((dbg.lists.find? (·.1 == v)).map (·.2) |>.getD #[])}")
      if let some d := listDiff a b then
        return some (s!"lists:{d}", s!"var {i}:\n    port:  {listStr a}\n    stock: {listStr b}")
    | some (i, a), none => return some ("lists:extra-list", s!"var {i}: port {listStr a}")
    | none, some (j, b) => return some ("lists:missing-list", s!"var {j}: stock {listStr b}")
    | none, none => pure ()
  return none

/-! ## Driver -/

def checkFile (maxReport : Nat) (path : System.FilePath) (st : Stats) : IO Stats := do
  let file := path.toString
  let st := { st with files := st.files + 1 }
  let progData ← IO.FS.readBinFile path
  let ssaData ← IO.FS.readBinFile (path.withExtension "ssa")
  let res : Except String (ExportFile × ProgFile) := do
    let (e, _) ← GoFV.SSA.parseExportExt ssaData
    return (e, ← parseProgFile progData)
  match res with
  | .error e =>
    let st := { st with parseErrors := st.parseErrors + 1 }
    return st.record maxReport file "parse" e
  | .ok (e, pf) =>
  let some dbg := pf.prog0.dbg | return st.record maxReport file "stock:no-debuginfo" ""
  match Env.load e pf with
  | .error msg => return st.record maxReport file (errClass "env" msg) msg
  | .ok env =>
  match buildFuncDebug env (pf.frame.dclOut ++ pf.frame.optDcl) with
  | .error msg => return st.record maxReport file (errClass "port" msg) msg
  | .ok out =>
  let st := { st with slots := st.slots + dbg.slots.size, vars := st.vars + dbg.vars.size,
                      lists := st.lists + dbg.lists.size,
                      entries := st.entries + dbg.lists.foldl
                        (fun n (x : Nat × Array LocEntry) => n + x.2.size) 0,
                      synthFuncs := st.synthFuncs + (if out.synthesized.isEmpty then 0 else 1),
                      synthValues := st.synthValues + out.synthesized.size }
  match compare env pf out dbg with
  | none => return { st with match_ := st.match_ + 1 }
  | some (c, m) => return st.record maxReport file c m

def progFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "prog")).qsort (·.toString < ·.toString)
  else return #[p]

structure Opts where
  jobs : Nat := 1
  maxReport : Nat := 10
  table : Option String := none
  paths : Array String := #[]

partial def parseArgs : List String → Opts → Except String Opts
  | [], o => pure o
  | "--jobs" :: n :: rest, o => do
    let some n := n.toNat? | throw s!"--jobs {n}: not a number"
    parseArgs rest { o with jobs := max n 1 }
  | "--max-report" :: n :: rest, o => do
    let some n := n.toNat? | throw s!"--max-report {n}: not a number"
    parseArgs rest { o with maxReport := n }
  | "--table" :: f :: rest, o => parseArgs rest { o with table := some f }
  | p :: rest, o => parseArgs rest { o with paths := o.paths.push p }

def pct (a b : Nat) : String :=
  if b == 0 then "-" else
  let x := a * 10000 / b
  s!"{x / 100}.{if x % 100 < 10 then "0" else ""}{x % 100}%"

def tableText (st : Stats) (ms : Nat) : String := Id.run do
  let n := st.files
  let mut out := "| cut | functions | match | mismatch | parity |\n| --- | ---: | ---: | ---: | ---: |\n"
  out := out ++ s!"| BuildFuncDebug (E1) | {n} | {st.match_} | {n - st.match_} | {pct st.match_ n} |\n"
  out := out ++ s!"\n{st.slots} slots, {st.vars} vars, {st.lists} nonempty location lists, \
    {st.entries} entries (stock, compared functions); {st.synthValues} values synthesized by \
    PopulateABIInRegArgOps in {st.synthFuncs} functions; {st.parseErrors} parse errors, {ms} ms\n"
  let cls := st.classes.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
  if !cls.isEmpty then
    out := out ++ "\n| mismatch class | functions |\n| --- | ---: |\n"
    for (k, c) in cls do out := out ++ s!"| `{k}` | {c} |\n"
  return out

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  if o.paths.isEmpty then
    IO.eprintln "usage: debug-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>..."
    return 2
  let t0 ← IO.monoMsNow
  let mut files := #[]
  for p in o.paths do files := files ++ (← progFiles p)
  let tasks ← (List.range o.jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st : Stats := {}
    for h : i in [0:files.size] do
      if i % o.jobs == j then st ← checkFile o.maxReport files[i] st
    return st
  let mut st : Stats := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 1
  let ms := (← IO.monoMsNow) - t0
  for r in st.reports do
    IO.println s!"MISMATCH [{r.cls}] {r.file}\n  {r.msg}"
  let t := tableText st ms
  IO.println t
  if let some f := o.table then IO.FS.writeFile f t
  return if st.files > 0 && st.match_ == st.files && st.parseErrors == 0 then 0 else 1

end GoFVTest.DebugParity

def main (args : List String) : IO UInt32 := GoFVTest.DebugParity.main args
