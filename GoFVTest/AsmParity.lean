import GoFV.Asm.Flush
import GoFV.Asm.Parse

/-!
# `asm-parity`: Phase 3 I4 parity (`Flushplist`: linkpatch … linkpcln)

For every `*.prog` file (`gofv-prog 2`, `docs/contracts/export.md`) under the given directories,
runs `GoFV.Asm.flush` on the `prog0` section (P0) and compares the result with the `asm`
section (M), per function:

1. **progs**: the final Prog list (ID, order and every field: `Pc`, `Spadj`, `Isize`, `Optab`,
   `Pool`, `As`, `Scond`, `From`/`Reg`/`RestArgs`/`To` with cached classes, `RegTo2`, `Mark`,
   position; symbols by name and ABI);
2. **funcinfo**: the text symbol's `FuncInfo` (`Args`, `Locals`, `FuncID`, `FuncFlag`,
   `StartLine`, attributes, spills, inline marks, jump tables, funcaux symbols);
3. **text**: `Size`, `Align`, `P` (the first differing word is reported with the Prog at its PC)
   and `R` in append order;
4. **pcln**: the contents of pcsp, pcfile, pcline, pcinline and of every pcdata slot (the
   symbols are anonymous), the funcdata slots (symbols by name), `UsedFiles` and the local
   inlining tree;
5. **data**: the contents of the symbols the assembler writes besides the text and pc-value
   tables: `$`-constants (by name) and jump tables.

A function is an end-to-end match when all five match. Each mismatch is reported with a class
(the first differing item) and counted per class. A difference whose cause is outside the port
is classed `explained:<class>`, counts as a match of its cut, and the function as an
end-to-end match "with explained differences" (separate row); the classes are documented in
`docs/PARITY.md` ("Assembler parity"). The only one: `explained:text:reloc:pre-flush-markers`,
the frontend's zero-size marker relocations (`R_USEIFACE`, `R_USEIFACEMETHOD`,
`R_USENAMEDMETHOD`, `R_USEGENERICIFACEMETHOD`) that are on `LSym.R` before `Flushplist` and that
the export's `prog0` section does not record; the assembler's relocations must follow them
exactly.

usage: `lake exe asm-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>...`; exit status
1 on any mismatch, port error or parse error.
-/

open GoFV.SSA (GoStr Pos)
open GoFV.Asm

namespace GoFVTest.AsmParity

/-- A symbol as (name, ABI), or `-`. -/
abbrev SymKey := Option (GoStr × Nat)

def symStr : SymKey → String
  | some (n, abi) => s!"{n.toStringLossy}<{abi}>"
  | none => "-"

/-- Symbols of the whole `.prog` file by number. -/
def fileSyms (pf : ProgFile) : Std.HashMap Nat (GoStr × Nat) := Id.run do
  let mut m := {}
  for x in pf.frame.defs ++ pf.genin.defs ++ pf.prog0.defs ++ pf.asm.defs do
    if let .sym k n abi := x then m := m.insert k (n, abi)
  return m

/-! ## Canonical forms -/

structure CAddr where
  a : Addr
  sym : SymKey
  deriving DecidableEq

def canonAddr (sym : Nat → SymKey) (a : Addr) : CAddr :=
  { a := { a with sym := none }, sym := a.sym.bind sym }

def caddrStr (c : CAddr) : String :=
  let a := c.a
  let v := match a.val with
    | .none => "-" | .target t => s!"@{t}" | .nilTarget => "@?" | .textSize n => s!"i{n}"
    | .float b => s!"f{b}" | .str _ => "s…"
  s!"{a.type.name}/{a.reg}/{a.index}/{a.scale}/{a.name.name}/{a.cls}/{a.offset}/{symStr c.sym}/{v}"

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
  s!"p {p.id} pc={p.pc} spadj={p.spadj} isize={p.isize} optab={p.optab} pool={p.pool} \
    {p.as.name} {p.scond} {caddrStr c.from_} {p.reg} [{rest}] {caddrStr c.to} {p.regTo2} \
    mark={p.mark} {posStr p.pos}"

/-- The field of the first difference between two Progs. -/
def progDiffField (a b : CProg) : String :=
  if a.p.id != b.p.id then "id"
  else if a.p.as != b.p.as then "as"
  else if a.p.pc != b.p.pc then "pc"
  else if a.p.optab != b.p.optab then "optab"
  else if a.from_.a.cls != b.from_.a.cls || a.to.a.cls != b.to.a.cls ||
      (a.rest.map (·.2.a.cls)) != (b.rest.map (·.2.a.cls)) then "class"
  else if a.from_ != b.from_ then "from"
  else if a.p.reg != b.p.reg then "reg"
  else if a.rest != b.rest then "rest"
  else if a.to != b.to then "to"
  else if a.p.scond != b.p.scond then "scond"
  else if a.p.regTo2 != b.p.regTo2 then "regto2"
  else if a.p.spadj != b.p.spadj then "spadj"
  else if a.p.pool != b.p.pool then "pool"
  else if a.p.mark != b.p.mark then "mark"
  else if a.p.isize != b.p.isize then "isize"
  else if a.p.pos != b.p.pos then "pos"
  else "other"

/-- Contents of a data symbol without its identity: kind, size, alignment, attributes, bytes,
relocations (symbols by name). -/
structure CData where
  kind : String
  size : Int
  align : Int
  attr : Nat
  data : Array UInt8
  relocs : Array (Int × Nat × String × Int × SymKey)
  deriving BEq

def canonData (sym : Nat → SymKey) (d : SymData) : CData :=
  { kind := d.kind, size := d.size, align := d.align, attr := d.attr, data := d.data.data,
    relocs := d.relocs.map fun r => (r.off, r.siz, r.type, r.add, r.sym.bind sym) }

def hexStr (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let h := Nat.toDigits 16 x.toNat
    String.ofList (if h.length < 2 then '0' :: h else h))

def cdataStr (c : CData) : String :=
  let rs := c.relocs.toList.map fun (o, s, t, a, y) => s!"{o} {s} {t} {a} {symStr y}"
  s!"{c.kind} {c.size} {c.align} {c.attr} {hexStr ⟨c.data.extract 0 64⟩}{if c.data.size > 64 then "…" else ""} relocs {rs}"

/-! ## Results -/

structure Report where
  file : String
  cls : String
  msg : String

structure Stats where
  files : Nat := 0
  parseErrors : Nat := 0
  progsMatch : Nat := 0
  fnMatch : Nat := 0
  textMatch : Nat := 0
  pclnMatch : Nat := 0
  dataMatch : Nat := 0
  allMatch : Nat := 0
  /-- End-to-end matches with only explained differences. -/
  explainedMatch : Nat := 0
  progs : Nat := 0
  textBytes : Nat := 0
  classes : Std.HashMap String Nat := {}
  reports : Array Report := #[]
  perClassReports : Std.HashMap String Nat := {}

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors,
    progsMatch := a.progsMatch + b.progsMatch, fnMatch := a.fnMatch + b.fnMatch,
    textMatch := a.textMatch + b.textMatch, pclnMatch := a.pclnMatch + b.pclnMatch,
    dataMatch := a.dataMatch + b.dataMatch, allMatch := a.allMatch + b.allMatch,
    explainedMatch := a.explainedMatch + b.explainedMatch,
    progs := a.progs + b.progs, textBytes := a.textBytes + b.textBytes,
    classes := b.classes.fold (fun m k v => m.alter k (some <| ·.getD 0 + v)) a.classes,
    reports := a.reports ++ b.reports,
    perClassReports := b.perClassReports.fold (fun m k v => m.alter k (some <| ·.getD 0 + v))
      a.perClassReports }

def Stats.record (st : Stats) (maxReport : Nat) (file cls msg : String) : Stats :=
  let n := st.perClassReports.getD cls 0
  let st := { st with classes := st.classes.alter cls (some <| ·.getD 0 + 1),
                      perClassReports := st.perClassReports.insert cls (n + 1) }
  if n < maxReport then { st with reports := st.reports.push { file, cls, msg } } else st

def errClass (msg : String) : String :=
  let head := (msg.splitOn ":").headD msg
  s!"error:{head.take 60}"

def cmpArr {α} (cls : String) (fmt : α → String) (eq : α → α → Bool) (a b : Array α) :
    Option (String × String) := Id.run do
  for k in [0:max a.size b.size] do
    match a[k]?, b[k]? with
    | some x, some y => if !eq x y then return some (cls, s!"#{k}: port {fmt x}, stock {fmt y}")
    | some x, none => return some (cls, s!"#{k}: port has extra {fmt x}")
    | none, some y => return some (cls, s!"#{k}: port lacks {fmt y}")
    | none, none => pure ()
  return none

/-! ## Comparisons (`none`: equal; `some (class, message)`: the first difference) -/

structure Cmp where
  ours : Nat → SymKey
  stock : Nat → SymKey
  out : FlushOut
  pf : ProgFile

def Cmp.progs (c : Cmp) : Option (String × String) := Id.run do
  let ours := c.out.progs.map (canonProg c.ours)
  let stock := c.pf.asm.progs.map (canonProg c.stock)
  for k in [0:max ours.size stock.size] do
    match ours[k]?, stock[k]? with
    | some a, some b =>
      if a != b then
        return some (s!"prog:{progDiffField a b}:{b.p.as.name}",
          s!"#{k}:\n    port:  {cprogStr a}\n    stock: {cprogStr b}")
    | some a, none => return some ("prog:extra", s!"#{k}: port has extra {cprogStr a}")
    | none, some b => return some (s!"prog:missing:{b.p.as.name}", s!"#{k}: port lacks {cprogStr b}")
    | none, none => pure ()
  return none

def Cmp.fn (c : Cmp) : Option (String × String) := Id.run do
  let a := c.out.fn
  let b := c.pf.asm.fn
  if c.ours a.sym != c.stock b.sym then
    return some ("fn:sym", s!"port {symStr (c.ours a.sym)}, stock {symStr (c.stock b.sym)}")
  let hdr (x : FuncInfo) := (x.args, x.locals, x.funcID, x.funcFlag, x.startLine, x.attr)
  if hdr a != hdr b then
    let fld := if a.args != b.args then "args" else if a.locals != b.locals then "locals"
      else if a.funcFlag != b.funcFlag then "funcflag" else if a.attr != b.attr then "attr"
      else "header"
    return some (s!"fn:{fld}", s!"port {hdr a}, stock {hdr b}")
  let spill (sym : Nat → SymKey) (x : Spill) := (canonAddr sym x.addr, x.reg, x.reg2, x.spill, x.unspill)
  let spillStr := fun (x : CAddr × Int × Int × As × As) =>
    s!"{caddrStr x.1} {x.2.1} {x.2.2.1} {x.2.2.2.1.name} {x.2.2.2.2.name}"
  if let some r := cmpArr "fn:spill" spillStr (· == ·) (a.spills.map (spill c.ours))
      (b.spills.map (spill c.stock)) then return some r
  if let some r := cmpArr "fn:inlmark" (fun (p, k) => s!"@{p} {k}") (· == ·) a.inlMarks b.inlMarks then
    return some r
  if let some r := cmpArr "fn:jumptable" (fun (y, ts) => s!"{symStr y} {ts.toList}") (· == ·)
      (a.jumpTables.map fun (y, ts) => (c.ours y, ts))
      (b.jumpTables.map fun (y, ts) => (c.stock y, ts)) then return some r
  let auxes (x : FuncAux) (sym : Nat → SymKey) : List SymKey :=
    [x.gcArgs, x.gcLocals, x.stackObjects, x.openCodedDeferInfo, x.argInfo, x.argLiveInfo,
     x.wrapInfo].map (·.bind sym)
  if auxes a.aux c.ours != auxes b.aux c.stock then
    return some ("fn:funcaux", s!"port {(auxes a.aux c.ours).map symStr}, stock {(auxes b.aux c.stock).map symStr}")
  return none

/-- Relocation types the frontend puts on a function's `LSym.R` before assembly. -/
def preFlushMarker (t : String) : Bool :=
  t == "R_USEIFACE" || t == "R_USEIFACEMETHOD" || t == "R_USENAMEDMETHOD" ||
  t == "R_USEGENERICIFACEMETHOD"

/-- The first differing 4-byte word of two byte arrays. -/
def firstDiff (a b : ByteArray) : Option Nat := Id.run do
  for k in [0:max a.size b.size] do
    if a[k]? != b[k]? then return some (k / 4 * 4)
  return none

def word (b : ByteArray) (off : Nat) : String :=
  hexStr (b.extract off (off + 4))

def Cmp.text (c : Cmp) : Option (String × String) := Id.run do
  let s := c.out.st
  let x := c.pf.asm
  if s.textSize != x.textSize then
    return some ("text:size", s!"port {s.textSize}, stock {x.textSize}")
  if s.textAlign != x.textAlign then
    return some ("text:align", s!"port {s.textAlign}, stock {x.textAlign}")
  if let some off := firstDiff s.textP x.text then
    -- the stock Prog at that PC (last Prog with pc ≤ off that has code)
    let atp := x.progs.foldl (fun acc p => if p.pc ≤ (off : Int) && p.optab != 0 then some p else acc) none
    let asName := (atp.map (·.as.name)).getD "?"
    let ty := ((atp.bind fun p => optabAt? p.optab).map (·.type_)).getD (-1)
    return some (s!"text:bytes:{asName}:case{ty}", s!"at {off}: port {word s.textP off}, stock {word x.text off}; \
      stock Prog {(atp.map (cprogStr ∘ canonProg c.stock)).getD "-"}")
  let rel (sym : Nat → SymKey) (r : Reloc) := (r.off, r.siz, r.type, r.add, r.sym.bind sym)
  let ours := s.textR.map (rel c.ours)
  let stock := x.relocs.map (rel c.stock)
  let fmt := fun ((o, s, t, a, y) : Int × Nat × String × Int × SymKey) => s!"{o} {s} {t} {a} {symStr y}"
  match cmpArr "text:reloc" fmt (· == ·) ours stock with
  | none => none
  | some r =>
    -- The frontend's marker relocations (`reflectdata.MarkTypeUsedInInterface`,
    -- `MarkUsedIfaceMethod`, `walk` for `MethodByName`) are on `LSym.R` before `Flushplist`
    -- appends the assembler's, and `prog0` does not record `LSym.R`.
    let k := stock.size - ours.size
    if stock.size ≥ ours.size && stock.extract k stock.size == ours &&
        (stock.extract 0 k).all fun (_, siz, t, _, _) => siz == 0 && preFlushMarker t then
      some ("explained:text:reloc:pre-flush-markers", s!"{k} marker relocations before the \
        assembler's: {(stock.extract 0 k).toList.map fmt}")
    else some r

def Cmp.dataOf (c : Cmp) (ours : Bool) (y : Option Nat) : Option CData :=
  y.bind fun k =>
    if ours then (c.out.st.symData[k]?).map (canonData c.ours)
    else (c.pf.asm.data.find? (·.sym == k)).map (canonData c.stock)

def Cmp.pcln (c : Cmp) : Option (String × String) := Id.run do
  let a := c.out.st.pcln
  let b := c.pf.asm.pcln
  let opt := fun (o : Option CData) => (o.map cdataStr).getD "nil"
  for (k, x, y) in [("pcsp", a.pcsp, b.pcsp), ("pcfile", a.pcfile, b.pcfile),
                    ("pcline", a.pcline, b.pcline), ("pcinline", a.pcinline, b.pcinline)] do
    let dx := c.dataOf true x
    let dy := c.dataOf false y
    if dx != dy then return some (s!"pcln:{k}", s!"port {opt dx}, stock {opt dy}")
  if let some r := cmpArr "pcln:pcdata" opt (· == ·) (a.pcdata.map (c.dataOf true))
      (b.pcdata.map (c.dataOf false)) then return some r
  if let some r := cmpArr "pcln:funcdata" symStr (· == ·) (a.funcdata.map (·.bind c.ours))
      (b.funcdata.map (·.bind c.stock)) then return some r
  let uf := c.out.st.usedFiles.qsort (· < ·)
  if uf != c.pf.asm.usedFiles then
    return some ("pcln:usedfiles", s!"port {uf}, stock {c.pf.asm.usedFiles}")
  let node (sym : Nat → SymKey) (n : InlNode) := (n.parent, n.pos, n.func.bind sym, n.name, n.parentPC)
  cmpArr "pcln:inltree" (fun (p, pos, f, nm, pc) => s!"{p} {posStr pos} {symStr f} {nm.toStringLossy} {pc}")
    (· == ·) (c.out.st.inlTree.map (node c.ours)) (c.pf.asm.inlTree.map (node c.stock))

/-- `$`-constants by name and jump tables. -/
def Cmp.data (c : Cmp) : Option (String × String) := Id.run do
  let isConst (k : SymKey) := match k with
    | some (n, _) => n.bytes[0]? == some 36  -- '$'
    | none => false
  let jt (fn : FuncInfo) (sym : Nat → SymKey) : List SymKey := fn.jumpTables.toList.map (sym ·.1)
  let stockKeys := (c.pf.asm.data.map fun d => c.stock d.sym).toList.filter fun k =>
    isConst k || (jt c.pf.asm.fn c.stock).contains k
  let ourKeys := (c.out.st.symData.toList.map fun (k, _) => c.ours k).filter fun k =>
    isConst k || (jt c.out.fn c.ours).contains k
  for k in ourKeys do
    if !stockKeys.contains k then return some ("data:extra", s!"port wrote {symStr k}")
  for k in stockKeys do
    let dy := (c.pf.asm.data.find? (c.stock ·.sym == k)).map (canonData c.stock)
    let dx := (c.out.st.symData.toList.find? (c.ours ·.1 == k)).map fun (_, d) => canonData c.ours d
    if dx != dy then
      return some (s!"data:{if isConst k then "const" else "jumptable"}", s!"{symStr k}: port \
        {(dx.map cdataStr).getD "none"}, stock {(dy.map cdataStr).getD "none"}")
  return none

/-! ## Driver -/

def checkFile (maxReport : Nat) (path : System.FilePath) (st : Stats) : IO Stats := do
  let file := path.toString
  let st := { st with files := st.files + 1 }
  let data ← IO.FS.readBinFile path
  match parseProgFile data with
  | .error e =>
    let st := { st with parseErrors := st.parseErrors + 1 }
    return st.record maxReport file "parse" e
  | .ok pf =>
  let st := { st with progs := st.progs + pf.asm.progs.size, textBytes := st.textBytes + pf.asm.text.size }
  match flush pf with
  | .error msg => return st.record maxReport file (errClass msg) msg
  | .ok out =>
  let fsyms := fileSyms pf
  let c : Cmp := { ours := fun k => out.st.syms[k]?, stock := fun k => fsyms[k]?, out, pf }
  let mut st := st
  let mut ok := true
  let mut exact := true
  for (sel, get) in [(0, c.progs), (1, c.fn), (2, c.text), (3, c.pcln), (4, c.data)] do
    let mut res := get
    if let some (cls, m) := get then
      if cls.startsWith "explained:" then
        st := st.record maxReport file cls m
        exact := false
        res := none
    match res with
    | none =>
      st := match sel with
        | 0 => { st with progsMatch := st.progsMatch + 1 }
        | 1 => { st with fnMatch := st.fnMatch + 1 }
        | 2 => { st with textMatch := st.textMatch + 1 }
        | 3 => { st with pclnMatch := st.pclnMatch + 1 }
        | _ => { st with dataMatch := st.dataMatch + 1 }
    | some (cls, m) => st := st.record maxReport file cls m; ok := false
  if ok then
    st := if exact then { st with allMatch := st.allMatch + 1 }
      else { st with explainedMatch := st.explainedMatch + 1 }
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
  for (k, m) in [("Prog list (D2–D6)", st.progsMatch), ("FuncInfo", st.fnMatch),
                 ("text P/R (D4, D5)", st.textMatch), ("pc tables, funcdata (D7)", st.pclnMatch),
                 ("constants, jump tables", st.dataMatch), ("end to end, exact", st.allMatch),
                 ("end to end, exact or explained", st.allMatch + st.explainedMatch)] do
    out := out ++ s!"| {k} | {n} | {m} | {n - m} | {pct m n} |\n"
  out := out ++ s!"\n{st.progs} asm Progs, {st.textBytes} text bytes, {st.parseErrors} parse errors, {ms} ms\n"
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
    IO.eprintln "usage: asm-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>..."
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
  return if st.files > 0 && st.allMatch + st.explainedMatch == st.files && st.parseErrors == 0
    then 0 else 1

end GoFVTest.AsmParity

def main (args : List String) : IO UInt32 := GoFVTest.AsmParity.main args
