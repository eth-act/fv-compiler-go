import GoFV.Asm.Prog
import GoFV.SSA.Parse

/-!
# Parser of the `gofv-prog 3` format

Parses a `.prog` file (`docs/contracts/export.md`, "gofv-prog 3") into a `ProgFile`. Like the
`gofv-ssa` parser (`GoFV.SSA.Parse`, whose lexer and word parsers it reuses) it is strict: it
accepts exactly the canonical text `GoFV.Asm.Print` produces, so `print ∘ parse` is the identity
on every file it accepts.
-/

namespace GoFV.Asm.Parse

open GoFV.SSA (GoStr Pos PosBase Token)
open GoFV.SSA.Parse

/-! ## Words -/

/-- `_` (a hole in a list, or the zero `Addr`). -/
def isHole (s : Sl) : Bool := s.size == 1 && s.get 0 == 95

def asTable : Std.HashMap ByteArray As :=
  As.all.foldl (fun m a => m.insert a.name.toUTF8 a) {}

def asW (s : Sl) : Except String As :=
  match asTable[s.data.extract s.start s.stop]? with
  | some a => pure a
  | none => throw s!"unknown opcode {s}"

def addrTypeW (s : Sl) : Except String AddrType :=
  match AddrType.all.find? (fun t => s.eqStr t.name) with
  | some t => pure t
  | none => throw s!"unknown Addr type {s}"

def addrNameW (s : Sl) : Except String AddrName :=
  match AddrName.all.find? (fun t => s.eqStr t.name) with
  | some t => pure t
  | none => throw s!"unknown Addr name {s}"

/-- `@<id>`. -/
def targetW (s : Sl) : Except String Nat := refW '@' s

/-- `@<id>` or `-`. -/
def optTargetW (s : Sl) : Except String (Option Nat) := optRefW '@' s

/-- Lower-case hex bytes, `-` for none (empty). -/
def bytesW (s : Sl) : Except String ByteArray := do
  if s.size == 0 then throw "empty hex"
  match ← hexW s with
  | some b => if b.isEmpty then throw "empty hex" else pure b
  | none => pure .empty

/-- `Addr.Val`: `-`, `@<id>`, `i<int32>`, `f<bits hex>`, `s<bytes hex>`. -/
def valW (s : Sl) : Except String AddrVal := do
  if s.isDash then return .none
  if s.size == 0 then throw "empty Addr value"
  match s.get 0 with
  | 64 => return .target (← natW (s.drop 1))
  | 105 => return .textSize (← intW (s.drop 1))
  | 102 => return .float (← hex64W (s.drop 1))
  | 115 =>
    match ← hexW (s.drop 1) with
    | some b => return .str b
    | none => throw s!"bad string value {s}"
  | _ => throw s!"bad Addr value {s}"

/-- `<TYPE>/<reg>/<index>/<scale>/<NAME>/<class>/<offset>/<y|->/<val>`, or `_` for the zero
`Addr` (which has no other spelling). -/
def addrW (s : Sl) : Except String Addr := do
  if isHole s then return {}
  let ps ← partsW s '/' 9
  let a : Addr := {
    type := ← addrTypeW ps[0]!, reg := ← intW ps[1]!, index := ← intW ps[2]!,
    scale := ← intW ps[3]!, name := ← addrNameW ps[4]!, cls := ← intW ps[5]!,
    offset := ← intW ps[6]!, sym := ← optRefW 'y' ps[7]!, val := ← valW ps[8]! }
  if a == {} then throw "the zero Addr is written _"
  return a

/-- `<pos>:<addr>` (a `RestArgs` entry). -/
def restW (s : Sl) : Except String (Nat × Addr) := do
  match s.split2 58 with
  | some (a, b) => return (← natW a, ← addrW b)
  | none => throw s!"bad RestArgs entry {s}"

/-- `y<n>` or `_` (list entry). -/
def symHoleW (s : Sl) : Except String (Option Nat) :=
  if isHole s then pure none else some <$> refW 'y' s

/-- `?`, `-` (no bytes) or hex bytes. -/
def maskW (s : Sl) : Except String (Option ByteArray) := do
  if s.size == 1 && s.get 0 == 63 then return none
  return some (← bytesW s)

/-- `0`, `1` or `?`. -/
def optBoolW (s : Sl) : Except String (Option Bool) :=
  if s.size == 1 && s.get 0 == 63 then pure none else some <$> boolW s

/-- Lower-case hex number. -/
def hexNatW (s : Sl) : Except String Nat := do return (← hex64W s).toNat

/-! ## Lines -/

def defTags : List String := ["type", "name", "sym", "posbase", "inl"]

def defLine : L Def := do
  match ← peekTag with
  | some "type" => line "type" do
    let n ← w (refW 't')
    let size ← w optIntW
    let align ← w optIntW
    let ptrdata ← w optIntW
    let hasPtr ← w optBoolW
    let ptrMask ← w maskW
    let s ← str
    return .type n { size, align, ptrdata, hasPtr, ptrMask, str := s }
  | some "name" => line "name" do
    let n ← w (refW 'n')
    let s ← str
    let cls ← wordStr
    let t ← w (optRefW 't')
    let esc ← w natW
    let linkName ← str
    let linkAbi ← w natW
    let aux ← w (optRefW 'a')
    return .name n { sym := s, cls, type := t, esc, linkName, linkAbi, aux }
  | some "sym" => line "sym" do
    let n ← w (refW 'y')
    let s ← str
    return .sym n s (← w natW)
  | some "posbase" => line "posbase" do
    let i ← w (refW 'p')
    let file ← str
    let l ← w intW
    let c ← w intW
    let inl ← w intW
    let fi ← w optIntW
    return .posBase i { file, line := l, col := c, inl } fi
  | some "inl" => line "inl" do
    let k ← w (refW 'i')
    let parent ← w (optRefW 'i')
    let pos ← w posW
    let func ← w (optRefW 'y')
    return .inl k { parent, pos, func, name := ← str }
  | t => throw s!"expected a definition, got {t}"

def defs : L (Array Def) := do
  let mut out := #[]
  for _ in [0:(← read).lines.size] do
    match ← peekTag with
    | some t => if defTags.contains t then out := out.push (← defLine) else break
    | none => break
  return out

/-- Zero or more lines with tag `t`. -/
def many {α} (t : String) (p : F α) : L (Array α) := do
  let mut out := #[]
  for _ in [0:(← read).lines.size] do
    if ← tagIs t then out := out.push (← line t p) else break
  return out

def warnsEnd : L (Array GoStr) := do
  let ws ← many "warn" str
  line "end" (pure ())
  return ws

def progLine : F Prog := do
  let id ← w natW
  let pc ← w intW
  let spadj ← w intW
  let isize ← w natW
  let optab ← w natW
  let pool ← w optTargetW
  let as ← w asW
  let scond ← w natW
  let from_ ← w addrW
  let reg ← w intW
  let rest ← w (listW restW)
  let to ← w addrW
  let regTo2 ← w intW
  let mark ← w natW
  let pos ← w posW
  return { id, pc, spadj, isize, optab, pool, as, scond, from_, reg, rest, to, regTo2, mark, pos }

def relocLine : F Reloc := do
  let off ← w intW
  let siz ← w natW
  let type ← wordStr
  let add ← w intW
  return { off, siz, type, add, sym := ← w (optRefW 'y') }

def relocs (n : Nat) : L (Array Reloc) := do
  let mut out := #[]
  for _ in [0:n] do
    out := out.push (← line "reloc" relocLine)
  return out

def dataLines : L (Array SymData) := do
  let mut data := #[]
  for _ in [0:(← read).lines.size] do
    unless ← tagIs "data" do break
    let (sym, kind, size, align, attr, bytes, nr) ← line "data" do
      return (← w (refW 'y'), ← wordStr, ← w intW, ← w intW, ← w hexNatW, ← w bytesW, ← w natW)
    data := data.push { sym, kind, size, align, attr, data := bytes, relocs := ← relocs nr }
  return data

def textLine : F TextInfo := do
  return { sym := ← w (refW 'y'), args := ← w intW, locals := ← w intW, funcID := ← w natW,
           funcFlag := ← w natW, startLine := ← w intW, attr := ← w hexNatW }

def funcInfo : L FuncInfo := do
  let t ← line "fn" textLine
  let spills ← many "spill" do
    return { addr := ← w addrW, reg := ← w intW, reg2 := ← w intW, spill := ← w asW,
             unspill := ← w asW }
  let inlMarks ← many "inlmark" do return (← w targetW, ← w intW)
  let jumpTables ← many "jumptable" do return (← w (refW 'y'), ← w (listW targetW))
  let aux ← line "funcaux" do
    let o := w (optRefW 'y')
    return { gcArgs := ← o, gcLocals := ← o, stackObjects := ← o, openCodedDeferInfo := ← o,
             argInfo := ← o, argLiveInfo := ← o, wrapInfo := ← o }
  return { sym := t.sym, args := t.args, locals := t.locals, funcID := t.funcID,
           funcFlag := t.funcFlag, startLine := t.startLine, attr := t.attr, spills, inlMarks,
           jumpTables, aux }

def dclLine : F DclEntry := do
  return { name := ← w (refW 'n'), off := ← w intW, flags := ← w (flagsW NameFlags.table) }

def frame : L Frame := do
  line "frame" (pure ())
  let defs ← defs
  let dclIn ← many "in" dclLine
  let dclOut ← many "out" dclLine
  let optDcl ← many "opt" dclLine
  let merges ← many "merge" do return (← w (refW 'n'), ← w (listW (refW 'n')))
  let (stksize, stkptrsize, stkalign) ← line "stack" do return (← w intW, ← w intW, ← w intW)
  let warns ← warnsEnd
  return { defs, dclIn, dclOut, optDcl, merges, stksize, stkptrsize, stkalign, warns }

def regArgsW : F (Array RegArg) := w (listW fun s => do
  let ps ← partsW s ':' 3
  return { reg := ← intW ps[0]!, off := ← intW ps[1]!, type := ← optRefW 't' ps[2]! })

def genin : L GenIn := do
  line "genin" (pure ())
  let defs ← defs
  let (fnPos, hasDefer, openDeferDisallowed) ← line "curfn" do
    return (← w posW, ← w boolW, ← w boolW)
  let wrapped ← if ← tagIs "wrapped" then
      some <$> line "wrapped" (do return (← str, ← w natW))
    else pure none
  let openDefer ← if ← tagIs "opendefer" then
      some <$> line "opendefer" (do return (← w (refW 'n'), ← w (listW (refW 'n'))))
    else pure none
  let regArgs ← line "regargs" regArgsW
  let text ← line "text" textLine
  let warns ← warnsEnd
  return { defs, fnPos, hasDefer, openDeferDisallowed, wrapped, openDefer, regArgs, text, warns }

/-- `text <size> <align> <bytes> <nrelocs>` and its `reloc` lines: the text symbol's `Size`,
`Align`, `P`, `R`. -/
def textSym : L (Int × Int × ByteArray × Array Reloc) := do
  let (size, align, bytes, nr) ← line "text" do
    return (← w intW, ← w intW, ← w bytesW, ← w natW)
  return (size, align, bytes, ← relocs nr)

/-- `<sb>:<sv>:<eb>:<ev>:<expr hex|->`. -/
def locEntryW (s : Sl) : Except String LocEntry := do
  let ps ← partsW s ':' 5
  return { startBlock := ← intW ps[0]!, startValue := ← intW ps[1]!, endBlock := ← intW ps[2]!,
           endValue := ← intW ps[3]!, expr := ((← hexW ps[4]!).getD .empty) }

/-- `<a>:<b>` integer pairs, comma list. -/
def pairsW (s : Sl) : Except String (Array (Int × Int)) := listW (fun x => do
  let ps ← partsW x ':' 2
  return (← intW ps[0]!, ← intW ps[1]!)) s

/-- The `dbg*` lines of `prog0`: `BuildFuncDebug`'s result. -/
def funcDebug : L (Option FuncDebug) := do
  let entry ← line "dbgentry" (w fun x => if x.isDash then pure none else some <$> intW x)
  let some entry := entry | return none
  let mut slots := #[]
  for _ in [0:(← read).lines.size] do
    unless ← tagIs "dbgslot" do break
    let k := slots.size
    slots := slots.push (← line "dbgslot" do
      let i ← w natW
      if i != k then throw s!"dbgslot index {i}, expected {k}"
      return (← w (refW 'n'), ← w (optRefW 't'), ← w intW))
  let mut vars := #[]
  for _ in [0:(← read).lines.size] do
    unless ← tagIs "dbgvar" do break
    let k := vars.size
    vars := vars.push (← line "dbgvar" do
      let i ← w natW
      if i != k then throw s!"dbgvar index {i}, expected {k}"
      return (← w (refW 'n'), ← w (listW natW)))
  let lists ← many "dbgloc" do return (← w natW, ← w (listW locEntryW))
  let regOutputParams ← line "dbgregout" (w (listW (refW 'n')))
  let pcs ← line "dbgpc" (w (listW fun x => do
    let ps ← partsW x ':' 3
    return (← intW ps[0]!, ← intW ps[1]!, ← natW ps[2]!)))
  return some { entry, slots, vars, lists, regOutputParams, pcs }

def prog0 : L Prog0 := do
  line "prog0" (pure ())
  let defs ← defs
  let progs ← many "p" progLine
  let fn ← funcInfo
  let needzero ← line "needzero" (w (listW (refW 'n')))
  let regArgs ← line "regargs" regArgsW
  let (textSize, textAlign, text, relocs) ← textSym
  let symAlign ← line "symalign" (w (listW fun s => do
    let ps ← partsW s ':' 2
    return (← refW 'y' ps[0]!, ← intW ps[1]!)))
  let dbg ← funcDebug
  let warns ← warnsEnd
  return { defs, progs, fn, needzero, regArgs, textSize, textAlign, text, relocs, symAlign, dbg,
           warns }

def asm : L Asm := do
  line "asm" (pure ())
  let defs ← defs
  let progs ← many "p" progLine
  let fn ← funcInfo
  let (textSize, textAlign, text, textRelocs) ← textSym
  let pcln ← line "pcln" do
    let o := w (optRefW 'y')
    return { pcsp := ← o, pcfile := ← o, pcline := ← o, pcinline := ← o,
             pcdata := ← w (listW symHoleW), funcdata := ← w (listW symHoleW) }
  let usedFiles ← line "usedfiles" (w (listW natW))
  let mut inlTree := #[]
  for _ in [0:(← read).lines.size] do
    unless ← tagIs "inltree" do break
    let k := inlTree.size
    inlTree := inlTree.push (← line "inltree" do
      let i ← w natW
      if i != k then throw s!"inltree index {i}, expected {k}"
      return { parent := ← w intW, pos := ← w posW, func := ← w (optRefW 'y'), name := ← str,
               parentPC := ← w intW })
  let data ← dataLines
  let warns ← warnsEnd
  return { defs, progs, fn, textSize, textAlign, text, relocs := textRelocs, pcln, usedFiles,
           inlTree, data,
           warns }

/-- `<FileIndex>:<RelLine>`. -/
def fileLineW (s : Sl) : Except String (Int × Nat) := do
  let ps ← partsW s ':' 2
  return (← intW ps[0]!, ← natW ps[1]!)

/-- A `var` line's location list: `-`, `v<VarID>` or `e<entries>`. -/
def varListW (s : Sl) : Except String VarList := do
  if s.isDash then return .none
  if s.size > 0 && s.get 0 == 'v'.toUInt8 then return .var (← natW (s.drop 1))
  if s.size > 0 && s.get 0 == 'e'.toUInt8 then return .entries (← listW locEntryW (s.drop 1))
  throw s!"bad location list {s}"

def dwVarLine : F DwVar := do
  return { scope := ← w intW, name := ← str, tag := ← w natW, withLoclist := ← w boolW,
           isReturnValue := ← w boolW, isInlFormal := ← w boolW, dictIndex := ← w natW,
           stackOffset := ← w intW, type := ← w (optRefW 'y'), declFile := ← str,
           declLine := ← w natW, declCol := ← w natW, inlIndex := ← w intW,
           childIndex := ← w intW, isInAbstract := ← w boolW, closureOffset := ← w intW,
           list := ← w varListW }

def dwarf : L Dwarf := do
  line "dwarf" (pure ())
  let defs ← defs
  let fn ← if ← tagIs "dwfn" then some <$> line "dwfn" (do
      let info ← w (refW 'y')
      let loc ← w (optRefW 'y')
      let ranges ← w (refW 'y')
      let absfn ← w (optRefW 'y')
      let lines ← w (refW 'y')
      let name ← str
      let (startFile, startLine) ← w fileLineW
      return { info, loc, ranges, absfn, lines, name, startFile, startLine,
               external := ← w boolW, wrapper := ← w boolW, useBASEntries := ← w boolW,
               dwTextCount := ← w natW })
    else pure none
  let mut scopes := #[]
  for _ in [0:(← read).lines.size] do
    unless ← tagIs "scope" do break
    let k := scopes.size
    let (parent, ranges) ← line "scope" do
      let i ← w natW
      if i != k then throw s!"scope index {i}, expected {k}"
      return (← w intW, ← w pairsW)
    scopes := scopes.push { parent, ranges, vars := ← many "var" dwVarLine }
  let mut inlCalls := #[]
  for _ in [0:(← read).lines.size] do
    unless ← tagIs "inlcall" do break
    let k := inlCalls.size
    let c ← line "inlcall" do
      let i ← w natW
      if i != k then throw s!"inlcall index {i}, expected {k}"
      let inlIndex ← w intW
      let (callFile, callLine) ← w fileLineW
      return ({ inlIndex, callFile, callLine, absFun := ← w (optRefW 'y'),
                children := ← w (listW natW), root := ← w boolW, ranges := ← w pairsW,
                vars := #[] } : DwInlCall)
    inlCalls := inlCalls.push { c with vars := ← many "var" dwVarLine }
  let dieRefs ← many "dieref" do
    return (← w (refW 'y'), ← w natW, ← w (refW 'y'), ← w intW)
  let dieOffs ← if ← tagIs "dieoff" then some <$> line "dieoff" (do
      return (← w (refW 'y'), ← w pairsW))
    else pure none
  let data ← dataLines
  let warns ← warnsEnd
  return { defs, fn, scopes, inlCalls, dieRefs, dieOffs, data, warns }

def file : L ProgFile := do
  line "gofv-prog" do
    let v ← wordStr
    if v != "3" then throw s!"unsupported gofv-prog version {v}"
  let pkg ← line "pkg" str
  let (name, abi) ← line "func" do return (← str, ← w natW)
  let config ← many "config" do
    let k ← wordStr
    let v ← rest
    match v with
    | #[t] => return (k, t)
    | _ => throw "config: expected one value"
  let frame ← frame
  let genin ← genin
  let prog0 ← prog0
  let asm ← asm
  let dwarf ← dwarf
  line "eof" (pure ())
  if (← get) != (← read).lines.size then throw s!"line {(← get) + 1}: data after eof"
  return { pkg, name, abi, config, frame, genin, prog0, asm, dwarf }

end Parse

/-- Parses a `gofv-prog 3` file. -/
def parseProgFile (data : ByteArray) : Except String ProgFile := do
  let ls ← GoFV.SSA.Parse.lines data
  match (Parse.file ⟨data, ls⟩).run 0 with
  | .ok f _ => pure f
  | .error e _ => throw e

end GoFV.Asm
