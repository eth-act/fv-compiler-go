import GoFV.Asm.Flush
import GoFV.Asm.Parse
import GoFV.Dwarf.Lines
import GoFV.Dwarf.Die
import GoFV.Dwarf.Info

/-!
# `dwarf-parity`: Phase 3 I5 parity of a function's DWARF (E2)

For every `*.prog` file (`gofv-prog 3`, `docs/contracts/export.md`) under the given
directories whose `dwarf` section has a `dwfn` line (`populateDWARF` ran), runs the ports of
`populateDWARF`'s steps on the recorded inputs and compares their output with what the section
records:

1. **lines**: `generateDebugLinesSymbol` (`GoFV.Dwarf.generateDebugLinesSymbol`) on the `asm`
   section's final Prog list, the position bases' file numbers and the text size;
2. **info**, **loc**, **ranges**, **absfn**: the DIE writer (`GoFV.Dwarf.putFunc`:
   `PutAbstractFunc`/`PutConcreteFunc`/`PutDefaultFunc` with the location lists of
   `PutLocationListDwarf5` and the DWARF 5 range lists) on the section's `dwarf.FnState`
   records (variables, scopes, inlined calls), the `prog0` section's `BuildFuncDebug` lists
   and `GetPC` (block start of the entry block 0, `FuncEnd` the text size, else the PC after
   assembly of the Prog `dbgpc` names: its `asm` PC, or its `prog0` PC when the assembler
   dropped it, as `obj.Prog.Pc` keeps it). The info symbol starts with the `R_USETYPE`
   relocations `dwarfgen.Info` adds before the DIEs; these rows take them from the recorded
   symbol (its leading zero-size `R_USETYPE` relocations at offset 0);
3. **fixups**: the child-DIE references (`RecordDclReference`) and the abstract function's
   child DIE offsets (`RecordChildDieOffsets`);
4. **Info records (E2)**: `dwarfgen.Info` (`GoFV.Dwarf.info`) on the file: its variables,
   scopes and inlined calls equal the section's `var`, `scope` and `inlcall` records (`==`), and
   its `R_USETYPE` relocations the recorded info symbol's leading ones;
5. **Info → DIE chain**: the DIE writer and the line writer on `info`'s records, with `info`'s
   `R_USETYPE` relocations as the info symbol's start; every DWARF symbol and the fixups are
   compared as in 1–3.

Each symbol is compared by kind, size, alignment, attributes, `P` and `R` in order (symbols by
number: every symbol the writers reference is one of the file's). "End to end" counts the
functions on which every row matches.

usage: `lake exe dwarf-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>...`;
exit status 1 on any mismatch, port error or parse error.
-/

open GoFV.SSA (GoStr Pos)
open GoFV.Asm
open GoFV.Dwarf

namespace GoFVTest.DwarfParity

structure Report where
  file : String
  cls : String
  msg : String

structure Stats where
  files : Nat := 0
  parseErrors : Nat := 0
  /-- Functions whose `populateDWARF` ran. -/
  withDwarf : Nat := 0
  lines : Nat := 0
  info : Nat := 0
  loc : Nat := 0
  ranges : Nat := 0
  absfn : Nat := 0
  fixups : Nat := 0
  /-- `dwarfgen.Info`'s records equal the recorded ones. -/
  e2 : Nat := 0
  /-- Every DWARF symbol and the fixups match when written from `dwarfgen.Info`'s records. -/
  chain : Nat := 0
  allMatch : Nat := 0
  bytes : Nat := 0
  classes : Std.HashMap String Nat := {}
  reports : Array Report := #[]

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors,
    withDwarf := a.withDwarf + b.withDwarf, lines := a.lines + b.lines, info := a.info + b.info,
    loc := a.loc + b.loc, ranges := a.ranges + b.ranges, absfn := a.absfn + b.absfn,
    fixups := a.fixups + b.fixups, e2 := a.e2 + b.e2, chain := a.chain + b.chain,
    allMatch := a.allMatch + b.allMatch, bytes := a.bytes + b.bytes,
    classes := b.classes.fold (fun m k v => m.alter k (some <| ·.getD 0 + v)) a.classes,
    reports := a.reports ++ b.reports }

def Stats.record (st : Stats) (maxReport : Nat) (file cls msg : String) : Stats :=
  let n := st.classes.getD cls 0
  let st := { st with classes := st.classes.insert cls (n + 1) }
  if n < maxReport then { st with reports := st.reports.push { file, cls, msg } } else st

def hexStr (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let h := Nat.toDigits 16 x.toNat
    String.ofList (if h.length < 2 then '0' :: h else h))

/-- The first differing byte offset. -/
def firstDiff (a b : ByteArray) : Option Nat := Id.run do
  for k in [0:max a.size b.size] do
    if a[k]? != b[k]? then return some k
  return none

def relocStr (r : Reloc) : String :=
  s!"{r.off} {r.siz} {r.type} {r.add} {(r.sym.map (s!"y{·}")).getD "-"}"

/-- The kind, alignment and attributes the writers' symbols have: `dwarfSym` creates the
anonymous info, loc, ranges and line symbols with their kinds; `SetPrecursorFunc` makes the
abstract function `SDWARFABSFCN` with `AttrDuplicateOK`. -/
def symHeader (fn : DwFn) (y : Nat) : String × Int × Nat :=
  if y == fn.info then ("SDWARFFCN", 0, 0)
  else if some y == fn.loc then ("SDWARFLOC", 0, 0)
  else if y == fn.ranges then ("SDWARFRANGE", 0, 0)
  else if y == fn.lines then ("SDWARFLINES", 0, 0)
  else ("SDWARFABSFCN", 0, Obj.AttrDuplicateOK.toNat)

/-- Compares the port's symbol `y` with its `data` line. -/
def cmpSym (fn : DwFn) (st : DwSt) (d : SymData) : Option String := Id.run do
  let ours := (st.syms[d.sym]?).getD {}
  let (kind, align, attr) := symHeader fn d.sym
  if (kind, align, attr) != (d.kind, d.align, d.attr) then
    return some s!"header: port {kind} {align} {attr}, stock {d.kind} {d.align} {d.attr}"
  if d.size != d.data.size then return some s!"stock size {d.size} != P size {d.data.size}"
  if let some k := firstDiff ours.data d.data then
    return some s!"size port {ours.data.size} stock {d.data.size}; first diff at {k}: port \
      {hexStr (ours.data.extract k (k + 16))}, stock {hexStr (d.data.extract k (k + 16))}"
  for k in [0:max ours.relocs.size d.relocs.size] do
    match ours.relocs[k]?, d.relocs[k]? with
    | some a, some b => if a != b then return some s!"reloc #{k}: port {relocStr a}, stock {relocStr b}"
    | some a, none => return some s!"reloc #{k}: port has extra {relocStr a}"
    | none, some b => return some s!"reloc #{k}: port lacks {relocStr b}"
    | none, none => pure ()
  return none

/-- `FuncDebug.GetPC` after assembly. -/
def getPC (pf : ProgFile) (dbg : Option FuncDebug) (asmPC : Std.HashMap Nat Int) (b v : Int) :
    Except String Int := do
  if v == -30000 then return pf.asm.textSize
  let some d := dbg | throw "GetPC: no FuncDebug"
  if v == -10000 && b == d.entry then return 0
  let some (_, _, id) := d.pcs.find? fun (b', v', _) => b' == b && v' == v
    | throw s!"GetPC({b}, {v}): not in dbgpc"
  match asmPC[id]? with
  | some pc => return pc
  | none =>
    match pf.prog0.progs.find? (·.id == id) with
    | some p => return p.pc
    | none => throw s!"GetPC({b}, {v}): Prog {id} in neither section"

/-! ## `dwarf.Var`, `dwarf.Scope`, `dwarf.InlCall` comparison -/

def listStr : VarList → String
  | .none => "-"
  | .var k => s!"v{k}"
  | .entries es => s!"e[{es.size}]"

def varStr (v : DwVar) : String :=
  s!"{v.scope} {v.name.quote} tag={v.tag} loclist={v.withLoclist} ret={v.isReturnValue} \
    inlformal={v.isInlFormal} dict={v.dictIndex} off={v.stackOffset} type={v.type} \
    {v.declFile.quote}:{v.declLine}:{v.declCol} inl={v.inlIndex} child={v.childIndex} \
    abstract={v.isInAbstract} closure={v.closureOffset} list={listStr v.list}"

/-- The names of the fields in which two variables differ. -/
def varDiff (a b : DwVar) : List String :=
  [("scope", a.scope == b.scope), ("name", a.name == b.name), ("tag", a.tag == b.tag),
   ("withLoclist", a.withLoclist == b.withLoclist),
   ("isReturnValue", a.isReturnValue == b.isReturnValue),
   ("isInlFormal", a.isInlFormal == b.isInlFormal), ("dictIndex", a.dictIndex == b.dictIndex),
   ("stackOffset", a.stackOffset == b.stackOffset), ("type", a.type == b.type),
   ("declFile", a.declFile == b.declFile), ("declLine", a.declLine == b.declLine),
   ("declCol", a.declCol == b.declCol), ("inlIndex", a.inlIndex == b.inlIndex),
   ("childIndex", a.childIndex == b.childIndex), ("isInAbstract", a.isInAbstract == b.isInAbstract),
   ("closureOffset", a.closureOffset == b.closureOffset), ("list", a.list == b.list)].filterMap
    fun (k, ok) => if ok then none else some k

def scopeStr (s : DwScope) : String := s!"parent={s.parent} ranges={s.ranges} vars={s.vars}"

def callStr (c : DwInlCall) : String :=
  s!"ii={c.inlIndex} call={c.callFile}:{c.callLine} abs={c.absFun} children={c.children} \
    root={c.root} ranges={c.ranges} vars={c.vars}"

def callDiff (a b : DwInlCall) : List String :=
  [("inlIndex", a.inlIndex == b.inlIndex), ("callPos", a.callFile == b.callFile && a.callLine == b.callLine),
   ("absFun", a.absFun == b.absFun), ("children", a.children == b.children),
   ("root", a.root == b.root), ("ranges", a.ranges == b.ranges), ("vars", a.vars == b.vars)].filterMap
    fun (k, ok) => if ok then none else some k

/-- The first difference between `dwarfgen.Info`'s records and the recorded ones, as (class,
message). -/
def cmpInfo (dw : Dwarf) (stockUseType : Array Reloc) (out : InfoOut) : Option (String × String) := Id.run do
  if out.useType != stockUseType then
    return some ("e2:usetype", s!"port {out.useType.map relocStr}, stock {stockUseType.map relocStr}")
  for k in [0:max out.vars.size dw.vars.size] do
    match out.vars[k]?, dw.vars[k]? with
    | some a, some b =>
      if !(a == b) then
        return some (s!"e2:var:{(varDiff a b).headD "?"}", s!"var {k}: port {varStr a}, stock {varStr b}")
    | some a, none => return some ("e2:var:extra", s!"var {k}: port has extra {varStr a}")
    | none, some b => return some ("e2:var:missing", s!"var {k}: port lacks {varStr b}")
    | none, none => pure ()
  for k in [0:max out.scopes.size dw.scopes.size] do
    match out.scopes[k]?, dw.scopes[k]? with
    | some a, some b =>
      if !(a == b) then
        let f := if a.parent != b.parent then "parent" else if a.ranges != b.ranges then "ranges" else "vars"
        return some (s!"e2:scope:{f}", s!"scope {k}: port {scopeStr a}, stock {scopeStr b}")
    | some a, none => return some ("e2:scope:extra", s!"scope {k}: port has extra {scopeStr a}")
    | none, some b => return some ("e2:scope:missing", s!"scope {k}: port lacks {scopeStr b}")
    | none, none => pure ()
  for k in [0:max out.inlCalls.size dw.inlCalls.size] do
    match out.inlCalls[k]?, dw.inlCalls[k]? with
    | some a, some b =>
      if !(a == b) then
        return some (s!"e2:inlcall:{(callDiff a b).headD "?"}", s!"inlcall {k}: port {callStr a}, stock {callStr b}")
    | some a, none => return some ("e2:inlcall:extra", s!"inlcall {k}: port has extra {callStr a}")
    | none, some b => return some ("e2:inlcall:missing", s!"inlcall {k}: port lacks {callStr b}")
    | none, none => pure ()
  return none

/-! ## Driver -/

/-- The per-file inputs of the writers. -/
structure Inputs where
  pf : ProgFile
  fn : DwFn
  ctx : AsmCtxt
  asmPC : Std.HashMap Nat Int

/-- Runs `putFunc` and `generateDebugLinesSymbol` with `dw` as the `dwarf.FnState` records and
`useType` as the info symbol's leading relocations. -/
def runWriters (i : Inputs) (dw : Dwarf) (useType : Array Reloc) : Except String DwSt := do
  let pf := i.pf
  let fileLine (p : Pos) : Except String (Int × Int) :=
    ((getFileIndexAndLine p).run i.ctx |>.run' default)
  let dbg := pf.prog0.dbg
  let varList (k : Nat) : Except String (Array LocEntry) :=
    match dbg.bind fun d => (d.lists.find? (·.1 == k)).map (·.2) with
    | some l => pure l
    | none => throw s!"no location list for VarID {k}"
  let dctx : DieCtx := { dw, fn := i.fn, textSym := pf.asm.fn.sym, textSize := pf.asm.textSize,
                         varList, getPC := getPC pf dbg i.asmPC }
  let init : DwSt := { syms := ({} : Std.HashMap Nat DSym).insert i.fn.info { relocs := useType } }
  let run : DwM Unit := do
    putFunc dctx
    generateDebugLinesSymbol pf.asm.fn.sym i.fn.lines pf.asm.progs pf.asm.textSize fileLine
  let ((), out) ← run.run init
  return out

/-- Compares the writers' symbols and fixups with the recorded ones: (role, mismatch) per role
(`none`: match). -/
def cmpOut (i : Inputs) (out : DwSt) : Array (String × Option String) := Id.run do
  let fn := i.fn
  let dw := i.pf.dwarf
  let roles : List (String × Option Nat) :=
    [("lines", some fn.lines), ("info", some fn.info), ("loc", fn.loc), ("ranges", some fn.ranges),
     ("absfn", fn.absfn)]
  let mut res := #[]
  for (role, y) in roles do
    let r : Option String := match y with
      | none => none
      | some y => match dw.data.find? (·.sym == y) with
        | some d => cmpSym fn out d
        | none => some "no data line"
    res := res.push (role, r)
  let refsOk := out.dieRefs == dw.dieRefs
  let offsOk := out.dieOffs == dw.dieOffs
  let fix := if refsOk && offsOk then none
    else some s!"port {out.dieRefs} {out.dieOffs}, stock {dw.dieRefs} {dw.dieOffs}"
  res := res.push ((if refsOk then "dieoff" else "dieref"), fix)
  return res

/-- The class of a port error: its first two `:`-separated parts (e.g. `Info: AbsFuncDwarfSym`). -/
def errClass (pfx e : String) : String :=
  s!"{pfx}error:{(":".intercalate ((e.splitOn ":").take 2)).take 60}"

def checkFile (maxReport : Nat) (path : System.FilePath) (st : Stats) : IO Stats := do
  let file := path.toString
  let st := { st with files := st.files + 1 }
  let data ← IO.FS.readBinFile path
  match parseProgFile data with
  | .error e => return { st with parseErrors := st.parseErrors + 1 }.record maxReport file "parse" e
  | .ok pf =>
  let some fn := pf.dwarf.fn | return st
  let st := { st with withDwarf := st.withDwarf + 1,
                      bytes := st.bytes + pf.dwarf.data.foldl (· + ·.data.size) 0 }
  let ctx ← match AsmCtxt.ofFile pf with
    | .ok c => pure c
    | .error e => return st.record maxReport file "error:ctxt" e
  let ctx := (pf.asm.defs ++ pf.dwarf.defs).foldl (init := ctx) fun c d => match d with
    | .posBase i b fi e => { c with posBases := c.posBases.insert i (b, fi), posExt := c.posExt.insert i e }
    | .inl k x => { c with inls := c.inls.insert k x }
    | _ => c
  let inp : Inputs := { pf, fn, ctx, asmPC := pf.asm.progs.foldl (fun m p => m.insert p.id p.pc) {} }
  -- dwarfgen.Info's R_USETYPE relocations as recorded: the info symbol's leading ones.
  let stockInfo := pf.dwarf.data.find? (·.sym == fn.info)
  let stockUseType := ((stockInfo.map (·.relocs)).getD #[]).toList.takeWhile
    (fun r => r.type == "R_USETYPE" && r.off == 0 && r.siz == 0) |>.toArray
  let mut st := st
  let mut ok := true
  -- Rows 1-3: the writers on the recorded records.
  match runWriters inp pf.dwarf stockUseType with
  | .error e => st := st.record maxReport file (errClass "" e) e; ok := false
  | .ok out =>
    for (role, r) in cmpOut inp out do
      match r with
      | none =>
        st := match role with
          | "lines" => { st with lines := st.lines + 1 }
          | "info" => { st with info := st.info + 1 }
          | "loc" => { st with loc := st.loc + 1 }
          | "ranges" => { st with ranges := st.ranges + 1 }
          | "absfn" => { st with absfn := st.absfn + 1 }
          | _ => { st with fixups := st.fixups + 1 }
      | some m => st := st.record maxReport file role m; ok := false
  -- Rows 4-5: dwarfgen.Info, then the writers on its records.
  match info pf with
  | .error e => st := st.record maxReport file (errClass "e2:" e) e; ok := false
  | .ok out =>
    match cmpInfo pf.dwarf stockUseType out with
    | none => st := { st with e2 := st.e2 + 1 }
    | some (cls, m) => st := st.record maxReport file cls m; ok := false
    let dw := { pf.dwarf with vars := out.vars, scopes := out.scopes, inlCalls := out.inlCalls }
    match runWriters inp dw out.useType with
    | .error e => st := st.record maxReport file (errClass "chain:" e) e; ok := false
    | .ok w =>
      let bad := (cmpOut inp w).filterMap fun (role, r) => r.map (role, ·)
      match bad[0]? with
      | none => st := { st with chain := st.chain + 1 }
      | some (role, m) => st := st.record maxReport file s!"chain:{role}" m; ok := false
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
  let n := st.withDwarf
  let mut out := s!"| symbol | functions | match | mismatch | parity |\n| --- | ---: | ---: | ---: | ---: |\n"
  for (k, m) in [("debug lines", st.lines), ("debug info", st.info), ("location lists", st.loc),
                 ("range lists", st.ranges), ("abstract function", st.absfn),
                 ("child-DIE fixups", st.fixups), ("Info records (E2)", st.e2),
                 ("Info → DIE chain", st.chain), ("end to end", st.allMatch)] do
    out := out ++ s!"| {k} | {n} | {m} | {n - m} | {pct m n} |\n"
  out := out ++ s!"\n{st.files} files, {st.withDwarf} with DWARF, {st.bytes} DWARF bytes, \
    {st.parseErrors} parse errors, {ms} ms\n"
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
    IO.eprintln "usage: dwarf-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>..."
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
  return if st.files > 0 && st.allMatch == st.withDwarf && st.parseErrors == 0 && st.classes.isEmpty
    then 0 else 1

end GoFVTest.DwarfParity

def main (args : List String) : IO UInt32 := GoFVTest.DwarfParity.main args
