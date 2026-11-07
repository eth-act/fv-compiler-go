import GoFV.Gen.Frame
import GoFV.Gen.Genssa
import GoFV.Asm.Parse
import GoFV.SSA.Parse

/-!
# `gen-parity`: Phase 3 I3 parity (`AllocFrame` … `defframe`)

For every `*.prog` file (`gofv-prog 2`, `docs/contracts/export.md`) under the given directories
with its companion `.ssa` file (same stem), runs the Lean ports on the function after `trim` and
the recorded frontend inputs (`GoFV.Gen.Env.load`) and compares, per function:

1. **frame** (A1, A2): `GoFV.Gen.allocFrame` against the `frame` section's `out`, `opt`,
   `merge` and `stack` lines;
2. **regargs** (A3): `GoFV.Gen.regArgsOf` against `genin`'s `f.RegArgs` (types compared by
   their `String()`);
3. **prog0** (B1–C6): `GoFV.Gen.genssa`, run on the **exported** frame (so a frame mismatch does
   not hide genssa results), against the `prog0` section: every Prog (ID, list order, every
   field; symbols by name and ABI), the `FuncInfo` records (spills, inline marks, jump tables,
   `funcaux`), `needzero`, the remaining `f.RegArgs`, and the contents (kind, size, alignment,
   attributes, bytes, relocations) of the metadata symbols as the `asm` section's `data` lines
   record them.

A function is an end-to-end match when all three match. Each mismatch is reported with a class
(the first differing item) and counted per class.

usage: `lake exe gen-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>...`; exit status
1 on any mismatch, port error or parse error.
-/

open GoFV.SSA (GoStr Pos ExportFile)
open GoFV.Asm
open GoFV.Gen

namespace GoFVTest.GenParity

/-! ## Symbols and types of the `.prog` file -/

/-- Symbol and type definitions of the whole `.prog` file (numbers are per file, definitions
valid from their section on). -/
structure ProgDefs where
  syms : Std.HashMap Nat (GoStr × Nat) := {}
  types : Std.HashMap Nat TypeDef := {}

def ProgDefs.of (pf : ProgFile) : ProgDefs := Id.run do
  let mut d : ProgDefs := {}
  for x in pf.frame.defs ++ pf.genin.defs ++ pf.prog0.defs ++ pf.asm.defs do
    match x with
    | .sym k n abi => d := { d with syms := d.syms.insert k (n, abi) }
    | .type k t => d := { d with types := d.types.insert k t }
    | _ => pure ()
  return d

/-- A symbol as (name, ABI), or `-`. -/
abbrev SymKey := Option (GoStr × Nat)

def symStr : SymKey → String
  | some (n, abi) => s!"{n.toStringLossy}<{abi}>"
  | none => "-"

/-! ## Canonical forms -/

/-- `Addr` with the symbol as (name, ABI). -/
structure CAddr where
  a : Addr
  sym : SymKey
  deriving DecidableEq

def canonAddr (sym : Nat → SymKey) (a : Addr) : CAddr :=
  { a := { a with sym := none }, sym := a.sym.bind sym }

def caddrStr (c : CAddr) : String :=
  let a := c.a
  let v := match a.val with
    | .none => "-" | .target t => s!"@{t}" | .textSize n => s!"i{n}"
    | .float b => s!"f{b}" | .str _ => "s…"
  s!"{a.type.name}/{a.reg}/{a.index}/{a.scale}/{a.name.name}/{a.cls}/{a.offset}/{symStr c.sym}/{v}"

/-- A Prog with symbols as (name, ABI) (and without its list link). -/
structure CProg where
  p : Prog
  from_ : CAddr
  rest : Array (Nat × CAddr)
  to : CAddr
  deriving DecidableEq

def canonProg (sym : Nat → SymKey) (p : Prog) : CProg :=
  { p := { p with from_ := {}, rest := #[], to := {} }, from_ := canonAddr sym p.from_,
    rest := p.rest.map fun (k, a) => (k, canonAddr sym a), to := canonAddr sym p.to }

def posStr (p : Pos) : String := s!"p{p.index}:{p.line}:{p.col}:{p.stmt}:{p.xlogue}"

def cprogStr (c : CProg) : String :=
  let p := c.p
  let rest := ",".intercalate (c.rest.toList.map fun (k, a) => s!"{k}:{caddrStr a}")
  s!"p {p.id} {p.pc} {p.as.name} {p.scond} {caddrStr c.from_} {p.reg} [{rest}] {caddrStr c.to} \
    {p.regTo2} {p.mark} {posStr p.pos} pool={p.pool} spadj={p.spadj}"

/-- The field of the first difference between two Progs. -/
def progDiffField (a b : CProg) : String :=
  if a.p.id != b.p.id then "id"
  else if a.p.as != b.p.as then "as"
  else if a.from_ != b.from_ then "from"
  else if a.p.reg != b.p.reg then "reg"
  else if a.rest != b.rest then "rest"
  else if a.to != b.to then "to"
  else if a.p.pos != b.p.pos then "pos"
  else if a.p.scond != b.p.scond then "scond"
  else if a.p.regTo2 != b.p.regTo2 then "regto2"
  else "other"

/-! ## Results -/

structure Report where
  file : String
  cls : String
  msg : String

structure Stats where
  files : Nat := 0
  parseErrors : Nat := 0
  frameMatch : Nat := 0
  regArgsMatch : Nat := 0
  prog0Match : Nat := 0
  allMatch : Nat := 0
  progs : Nat := 0
  classes : Std.HashMap String Nat := {}
  reports : Array Report := #[]
  perClassReports : Std.HashMap String Nat := {}

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors,
    frameMatch := a.frameMatch + b.frameMatch, regArgsMatch := a.regArgsMatch + b.regArgsMatch,
    prog0Match := a.prog0Match + b.prog0Match, allMatch := a.allMatch + b.allMatch,
    progs := a.progs + b.progs,
    classes := b.classes.fold (fun m k v => m.alter k (some <| ·.getD 0 + v)) a.classes,
    reports := a.reports ++ b.reports,
    perClassReports := b.perClassReports.fold (fun m k v => m.alter k (some <| ·.getD 0 + v))
      a.perClassReports }

def Stats.record (st : Stats) (maxReport : Nat) (file cls msg : String) : Stats :=
  let n := st.perClassReports.getD cls 0
  let st := { st with classes := st.classes.alter cls (some <| ·.getD 0 + 1),
                      perClassReports := st.perClassReports.insert cls (n + 1) }
  if n < maxReport then { st with reports := st.reports.push { file, cls, msg } } else st

/-- The class of a port error: the message up to the first `:` (port errors start with the
construct they do not cover). -/
def errClass (stage msg : String) : String :=
  let head := (msg.splitOn ":").headD msg
  s!"{stage}:error:{head.take 60}"

/-! ## Comparisons (`none`: equal; `some (class, message)`: the first difference) -/

def dclStr (d : DclEntry) : String :=
  s!"n{d.name} {d.off} {",".intercalate (NameFlags.table.filterMap fun (k, g, _) =>
    if g d.flags then some k else none)}"

def cmpArr {α} (cls : String) (fmt : α → String) (eq : α → α → Bool) (a b : Array α) :
    Option (String × String) := Id.run do
  for k in [0:max a.size b.size] do
    match a[k]?, b[k]? with
    | some x, some y => if !eq x y then return some (cls, s!"#{k}: port {fmt x}, stock {fmt y}")
    | some x, none => return some (cls, s!"#{k}: port has extra {fmt x}")
    | none, some y => return some (cls, s!"#{k}: port lacks {fmt y}")
    | none, none => pure ()
  return none

def cmpFrame (fr : FrameOut) (x : Frame) : Option (String × String) :=
  (cmpArr "frame:dcl" dclStr (· == ·) fr.dcl x.dclOut).orElse fun _ =>
  (cmpArr "frame:opt" dclStr (· == ·) fr.optDcl x.optDcl).orElse fun _ =>
  (cmpArr "frame:merge" (fun (l, fs) => s!"n{l} {fs.toList}") (· == ·) fr.merges x.merges).orElse
    fun _ =>
  if (fr.stksize, fr.stkptrsize, fr.stkalign) != (x.stksize, x.stkptrsize, x.stkalign) then
    some ("frame:stack", s!"port {fr.stksize} {fr.stkptrsize} {fr.stkalign}, stock \
      {x.stksize} {x.stkptrsize} {x.stkalign}")
  else none

/-- `.ssa` type text of a port `RegSpill`, `.prog` type text of an exported `RegArg`. -/
def cmpRegArgs (env : Env) (pd : ProgDefs) (ours : Array RegSpill) (stock : Array RegArg)
    (cls : String) : Option (String × String) :=
  let o := ours.map fun r =>
    (r.reg, r.off, (env.tabs.type? r.type).map (·.str.toStringLossy) |>.getD "?")
  let s := stock.map fun r =>
    (r.reg, r.off, (r.type.bind (pd.types[·]?)).map (·.str.toStringLossy) |>.getD "?")
  cmpArr cls (fun (r, o, t) => s!"{r}:{o}:{t}") (· == ·) o s

/-- Compares `genssa`'s result with the `prog0` section and the metadata symbols' contents. -/
def cmpProg0 (env : Env) (pd : ProgDefs) (out : GenOut) (pf : ProgFile) :
    Option (String × String) := Id.run do
  let st := out.st
  let ourSym : Nat → SymKey := fun k => st.syms[k]?
  let stockSym : Nat → SymKey := fun k => pd.syms[k]?
  let ours := out.order.filterMap fun id => (st.progs[id]?).map (canonProg ourSym)
  let stock := pf.prog0.progs.map (canonProg stockSym)
  for k in [0:max ours.size stock.size] do
    match ours[k]?, stock[k]? with
    | some a, some b =>
      if a != b then
        return some (s!"prog:{progDiffField a b}:{b.p.as.name}",
          s!"#{k}:\n    port:  {cprogStr a}\n    stock: {cprogStr b}")
    | some a, none => return some ("prog:extra", s!"#{k}: port has extra {cprogStr a}")
    | none, some b => return some (s!"prog:missing:{b.p.as.name}", s!"#{k}: port lacks {cprogStr b}")
    | none, none => pure ()
  let fi := pf.prog0.fn
  let spillStr := fun (c : CAddr × Int × Int × As × As) =>
    s!"{caddrStr c.1} {c.2.1} {c.2.2.1} {c.2.2.2.1.name} {c.2.2.2.2.name}"
  let canonSpill := fun (sym : Nat → SymKey) (x : Spill) =>
    (canonAddr sym x.addr, x.reg, x.reg2, x.spill, x.unspill)
  if let some r := cmpArr "funcinfo:spill" spillStr (· == ·)
      (st.spills.map (canonSpill ourSym)) (fi.spills.map (canonSpill stockSym)) then
    return some r
  if let some r := cmpArr "funcinfo:inlmark" (fun (p, k) => s!"@{p} {k}") (· == ·)
      st.inlMarks fi.inlMarks then return some r
  if let some r := cmpArr "funcinfo:jumptable" (fun (y, ts) => s!"{symStr y} {ts.toList}") (· == ·)
      (st.jumpTableSyms.map fun (y, ts) => (ourSym y, ts))
      (fi.jumpTables.map fun (y, ts) => (stockSym y, ts)) then return some r
  let a := st.aux
  let b := fi.aux
  let auxes : List (String × Option Nat × Option Nat) :=
    [("gcargs", a.gcArgs, b.gcArgs), ("gclocals", a.gcLocals, b.gcLocals),
     ("stkobj", a.stackObjects, b.stackObjects), ("opendefer", a.openCodedDeferInfo, b.openCodedDeferInfo),
     ("arginfo", a.argInfo, b.argInfo), ("argliveinfo", a.argLiveInfo, b.argLiveInfo),
     ("wrapinfo", a.wrapInfo, b.wrapInfo)]
  for (k, x, y) in auxes do
    let xs := x.bind ourSym
    let ys := y.bind stockSym
    if xs != ys then
      return some (s!"funcinfo:aux:{k}", s!"port {symStr xs}, stock {symStr ys}")
    -- contents of the metadata symbol
    if let (some xi, some yi) := (x, y) then
      let stockData := pf.asm.data.find? (·.sym == yi)
      match st.symData[xi]?, stockData with
      | some o, some d =>
        let oRel := o.relocs.map fun r => (r.off, r.siz, r.type, r.add, r.sym.bind ourSym)
        let dRel := d.relocs.map fun r => (r.off, r.siz, r.type, r.add, r.sym.bind stockSym)
        if o.data != d.data then
          return some (s!"sym:data:{k}", s!"{symStr xs}: port {o.data.size} bytes {o.data.toList.take 48}, \
            stock {d.data.size} bytes {d.data.toList.take 48}")
        if oRel != dRel then
          return some (s!"sym:relocs:{k}", s!"{symStr xs}: port {oRel.toList.map fun (o, s, t, a, y) =>
            s!"{o} {s} {t} {a} {symStr y}"}, stock {dRel.toList.map fun (o, s, t, a, y) =>
            s!"{o} {s} {t} {a} {symStr y}"}")
        if (o.kind, o.size, o.align, o.attr) != (d.kind, d.size, d.align, d.attr) then
          return some (s!"sym:header:{k}", s!"{symStr xs}: port {o.kind} {o.size} {o.align} \
            {o.attr}, stock {d.kind} {d.size} {d.align} {d.attr}")
      | none, some _ => return some (s!"sym:missing:{k}", s!"{symStr xs}: port wrote no contents")
      | _, none => pure ()
  let nz := st.dcl.filterMap fun d => if d.flags.needzero then some d.name else none
  if let some r := cmpArr "needzero" (s!"n{·}") (· == ·) nz pf.prog0.needzero then return some r
  if let some r := cmpRegArgs env pd st.regArgs pf.prog0.regArgs "regargs:after" then return some r
  return none

/-! ## Driver -/

def checkFile (maxReport : Nat) (path : System.FilePath) (st : Stats) : IO Stats := do
  let file := path.toString
  let st := { st with files := st.files + 1 }
  let ssaPath := path.withExtension "ssa"
  let progData ← IO.FS.readBinFile path
  let ssaData ← IO.FS.readBinFile ssaPath
  let res : Except String (ExportFile × ProgFile) := do
    let (e, _) ← GoFV.SSA.parseExportExt ssaData
    let pf ← parseProgFile progData
    return (e, pf)
  match res with
  | .error e =>
    let st := { st with parseErrors := st.parseErrors + 1 }
    return st.record maxReport file "parse" e
  | .ok (e, pf) =>
  let pd := ProgDefs.of pf
  match Env.load e pf with
  | .error msg => return st.record maxReport file (errClass "env" msg) msg
  | .ok env =>
  let mut st := { st with progs := st.progs + pf.prog0.progs.size }
  let mut ok := true
  -- frame
  match allocFrame env with
  | .error msg => st := st.record maxReport file (errClass "frame" msg) msg; ok := false
  | .ok fr =>
    match cmpFrame fr pf.frame with
    | none => st := { st with frameMatch := st.frameMatch + 1 }
    | some (c, m) => st := st.record maxReport file c m; ok := false
  -- regargs
  match regArgsOf env with
  | .error msg => st := st.record maxReport file (errClass "regargs" msg) msg; ok := false
  | .ok ra =>
    match cmpRegArgs env pd ra pf.genin.regArgs "regargs" with
    | none => st := { st with regArgsMatch := st.regArgsMatch + 1 }
    | some (c, m) => st := st.record maxReport file c m; ok := false
  -- prog0, on the exported frame
  let fr : FrameOut :=
    { dcl := pf.frame.dclOut, optDcl := pf.frame.optDcl, merges := pf.frame.merges,
      stksize := pf.frame.stksize, stkptrsize := pf.frame.stkptrsize,
      stkalign := pf.frame.stkalign }
  match genssa env fr with
  | .error msg => st := st.record maxReport file (errClass "genssa" msg) msg; ok := false
  | .ok out =>
    match cmpProg0 env pd out pf with
    | none => st := { st with prog0Match := st.prog0Match + 1 }
    | some (c, m) => st := st.record maxReport file c m; ok := false
  if ok then st := { st with allMatch := st.allMatch + 1 }
  return st

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
  let mut out := s!"| cut | functions | match | mismatch | parity |\n| --- | ---: | ---: | ---: | ---: |\n"
  for (k, m) in [("frame (A1, A2)", st.frameMatch), ("f.RegArgs (A3)", st.regArgsMatch),
                 ("prog0 (B1–C6)", st.prog0Match), ("end to end", st.allMatch)] do
    out := out ++ s!"| {k} | {n} | {m} | {n - m} | {pct m n} |\n"
  out := out ++ s!"\n{st.progs} prog0 Progs, {st.parseErrors} parse errors, {ms} ms\n"
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
    IO.eprintln "usage: gen-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>..."
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
  return if st.files > 0 && st.allMatch == st.files && st.parseErrors == 0 then 0 else 1

end GoFVTest.GenParity

def main (args : List String) : IO UInt32 := GoFVTest.GenParity.main args
