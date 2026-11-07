import Std.Data.HashMap
import Std.Data.HashSet
import GoFV.Asm.Prog
import GoFV.Asm.ObjConst
import GoFV.Dwarf.Const
import GoFV.Dwarf.Sym

/-!
# `dwarfgen.Info` (`docs/PASSES3.md` E2)

An exact port of `dwarfgen.Info` as `(*obj.Link).populateDWARF` calls it (the info symbol is
anonymous, so `isODCLFUNC` holds), from `cmd/compile/internal/dwarfgen`:

* `dwarf.go`: `Info`, `declPos`, `createDwarfVars`, `createConservativeVar`,
  `sortDeclsAndVars` (`sort.Stable` by the signature's parameter order), `preInliningDcls`,
  `createSimpleVar`, `createComplexVar` (with `ssagen.StackOffset`, `pgen.go`),
  `createHeapDerefLocationList`, `shouldEmitDwarfVar(Safe)` (with `ssa.IsVarWantedForDebug`),
  `closureOffset`;
* `scope.go`: `findScope` (`sort.Search` with `xposBefore`, `src.Pos.Before`),
  `assembleScopes`, `scopeVariables`, `scopePCs`, `compactScopes`, with `dwarf.Scope.AppendRange`,
  `UnifyRanges` and `dwarf.MergeRanges` (`cmd/internal/dwarf/dwarf.go`);
* `dwinl.go`: `assembleInlines` (both Prog walks, the variables grouped by inlining index, child
  indices from `makePreinlineDclMap`, `IsInAbstract`), `makePreinlineDclMap`, `insertInlCall`,
  `posInlIndex`, `addRange`, `unifyCallRanges`, and `checkInlCall` as a check.

Inputs, all from the `.prog` file (`docs/contracts/export.md`, "gofv-prog 3", "DWARF"): the
`dwarf` section's `dw*` lines (`fn.Dcl`, the closure offsets, scope marks and parents, the
signature's parameter names, the pre-inlining `Inl.Dcl` with each function's abstract-function
symbol, the names' facts), `prog0`'s `FuncDebug`, `Autot` and marker relocations (`R_USEIFACE`),
the `frame` section's `OptDcl`, the `asm` section's final Prog list and text size, the position
bases and the inlining tree. Symbols are looked up by name among the file's `sym` definitions
(ABI 0): `go:info.<TypeSymName>` (`Var.Type`) and `type:<TypeSymName>` (`R_USETYPE`).

`src.Pos` (`cmd/internal/src/pos.go`): `InnermostPos(xpos)` is `PosTable.Pos(xpos)`, the base of
the position's index (nil for 0) with the same `lico`; `RelFilename` is the base's `Filename()`,
`RelLine`/`RelCol` are relative to the base's own position `b.Pos()` (`uint` arithmetic), and
`Before` compares `b.Pos().RelFilename()` then the `lico`.

linux/arm64 only (`FixedFrameSize` 8, `PtrSize` 8, frame pointer on). Paths the corpus does not
take fail with an error naming them: another architecture, DWARF 4, `-N`, no location lists,
`GenDwarfInl` other than 2, `TSSA`-typed variables, names whose `TypeSymName` the export did not
compute.

The result has the shapes of the `dwarf` section's records: every distinct variable once, the
scopes' first in scope order, then those only in inlined calls (`InlVars` as `Info` leaves them,
before the DIE writer sorts them), and the `R_USETYPE` relocations `Info` appends to the info
symbol, in order.
-/

namespace GoFV.Dwarf

open GoFV.Asm
open GoFV.SSA (GoStr Pos PosBase Token)

/-- `dwarfgen.Info`'s result: the `dwarf.Scope`s, the `dwarf.InlCalls` and their variables
(numbered as the `dwarf` section numbers them), and the `R_USETYPE` relocations of the info
symbol. -/
structure InfoOut where
  vars : Array DwVar
  scopes : Array DwScope
  inlCalls : Array DwInlCall
  useType : Array Reloc
  deriving Inhabited

namespace Info

/-- Go's string `<` on bytes. -/
private def bytesLt (a b : ByteArray) : Bool := Id.run do
  let m := min a.size b.size
  for i in [0:m] do
    if a[i]! < b[i]! then return true
    if a[i]! > b[i]! then return false
  return a.size < b.size

/-- Go's `uint(x)` (64-bit). -/
private def uint (x : Int) : Nat := (x % (2 ^ 64 : Int)).toNat

/-- Go's `int32(x)`. -/
private def int32 (x : Int) : Int := x.toInt32.toInt

/-- `ctxt.Arch.FixedFrameSize` for arm64. -/
private def fixedFrameSize : Int := 8

/-- `localAutoOffset` / the `PAUTO` case of `ssagen.StackOffset`: `FixedFrameSize != 0` on arm64,
and the frame pointer slot (`buildcfg.FramePointerEnabled`) takes `PtrSize`. -/
private def localAutoOffset (off : Int) : Int := off - 8

private def infoPrefix : GoStr := .ofString "go:info."
private def typePrefix : GoStr := .ofString "type:"
private def itabPrefix : ByteArray := "go:itab.".toUTF8

private def hasPrefix (s : ByteArray) (p : ByteArray) : Bool :=
  s.size ≥ p.size && s.extract 0 p.size == p

/-- `sort.Stable` by a key with a strict order `lt`: decorate with the index and sort. -/
private def stableSortBy {α β : Type} [Inhabited α] (xs : Array α) (key : α → β)
    (lt : β → β → Bool) : Array α :=
  let d := (xs.zipIdx).qsort fun (a, i) (b, j) =>
    lt (key a) (key b) || (!lt (key b) (key a) && i < j)
  d.map (·.1)

/-- The file's definitions and `Info`'s derived inputs. -/
structure Env where
  pf : ProgFile
  names : Std.HashMap Nat NameDef
  types : Std.HashMap Nat TypeDef
  /-- ABI 0 symbols by name. -/
  symByName : Std.HashMap GoStr Nat
  symName : Std.HashMap Nat GoStr
  bases : Std.HashMap Nat (PosBase × Option Int × PosBaseExt)
  inls : Std.HashMap Nat InlDef
  facts : Std.HashMap Nat DwName
  /-- Frame offsets and `IsOutputParamInRegisters` of the frame section's `Dcl` (for slot
  names without a `dwname` line). -/
  frame : Std.HashMap Nat (Int × Bool)
  /-- `dwprecursor`: function symbol ↦ (abstract-function symbol, pre-inlining `Inl.Dcl`). -/
  precursors : Std.HashMap Nat (Nat × Array Nat)
  /-- `closureVars` (`nil` unless `fn.Needctxt()`). -/
  closureVars : Std.HashMap Nat Int
  dbg : Option FuncDebug
  /-- `varIDMap`: name ↦ `VarID` (the last one for a name listed twice). -/
  varIDMap : Std.HashMap Nat Nat
  /-- The `VarID`s with a nonempty location list. -/
  lists : Std.HashSet Nat
  fnsym : Nat
  wasInlined : Bool
  regabi : Bool
  textSize : Int

namespace Env

def name (e : Env) (n : Nat) : Except String NameDef :=
  match e.names[n]? with
  | some d => pure d
  | none => throw s!"Info: no name definition n{n}"

def fact (e : Env) (n : Nat) : Except String DwName :=
  match e.facts[n]? with
  | some d => pure d
  | none => throw s!"Info: no dwname line for n{n}"

/-- `types.TypeSymName(n.Type())`. -/
def typeSymName (e : Env) (n : Nat) : Except String GoStr := do
  let f ← e.fact n
  if f.tssa then throw s!"Info: n{n} has a TSSA type (not ported)"
  match f.typeSym with
  | some s => pure s
  | none => throw s!"Info: n{n}: TypeSymName not exported (type size unknown)"

/-- `ctxt.Lookup(name)` of a symbol the output references: the file's ABI 0 definition. -/
def lookup (e : Env) (s : GoStr) : Except String Nat :=
  match e.symByName[s]? with
  | some y => pure y
  | none => throw s!"Info: symbol {s.quote} not defined in the file"

def symNameOf (e : Env) (y : Nat) : Except String GoStr :=
  match e.symName[y]? with
  | some s => pure s
  | none => throw s!"Info: no symbol definition y{y}"

/-- `n.FrameOffset()` and `n.IsOutputParamInRegisters()`. -/
def frameOf (e : Env) (n : Nat) : Except String (Int × Bool) :=
  match e.facts[n]? with
  | some f => pure (f.frameOffset, f.outregs)
  | none => match e.frame[n]? with
    | some x => pure x
    | none => throw s!"Info: no frame offset for n{n}"

/-- The base of `PosTable.Pos(xpos)` (nil for index 0). -/
def base (e : Env) (x : Pos) : Except String (Option (PosBase × Option Int × PosBaseExt)) :=
  if x.index == 0 then pure none
  else match e.bases[x.index]? with
    | some b => pure (some b)
    | none => throw s!"Info: no position base p{x.index}"

/-- `RelFilename()`, `RelLine()`, `RelCol()` of `InnermostPos(xpos)` (`src/pos.go:86-116`). -/
def relPos (e : Env) (x : Pos) : Except String (GoStr × Nat × Nat) := do
  match ← e.base x with
  | none => pure (.ofString "", 0, 0)
  | some (b, _, ext) =>
    let line := if b.line == 0 then 0 else uint (b.line + ((x.line : Int) - ext.posLine))
    let col :=
      if b.col == 0 then 0
      else if x.line == ext.posLine then uint (b.col + ((x.col : Int) - ext.posCol))
      else x.col
    pure (ext.filename, line, col)

/-- `posInlIndex` (`dwinl.go`). -/
def posInlIndex (e : Env) (x : Pos) : Except String Int := do
  match ← e.base x with
  | some (b, _, _) => pure (if b.inl ≥ 0 then b.inl else -1)
  | none => pure (-1)

/-- `xposBefore(p, q)`: `PosTable.Pos(p).Before(PosTable.Pos(q))`, by `p.Filename()` (the base's
own position's `RelFilename()`, `""` for nil) and then the `lico`. -/
def xposBefore (e : Env) (p q : Pos) : Except String Bool := do
  let fname (x : Pos) : Except String ByteArray := do
    match ← e.base x with
    | some (_, _, ext) => pure ext.posFilename.bytes
    | none => pure .empty
  let n ← fname p
  let m ← fname q
  return bytesLt n m || (n == m && p.lico < q.lico)

/-- `findScope(marks, pos)` with `sort.Search`'s bisection. -/
def findScope (e : Env) (marks : Array (Pos × Nat)) (pos : Pos) : Except String Nat := do
  let mut i := 0
  let mut j := marks.size
  let mut fuel := marks.size + 1
  while i < j && fuel > 0 do
    fuel := fuel - 1
    let h := (i + j) / 2
    if !(← e.xposBefore pos marks[h]!.1) then i := h + 1 else j := h
  if i == 0 then return 0
  return marks[i - 1]!.2

/-- `declPos(n)`: `n.Canonical().Pos()`. -/
def declPos (e : Env) (n : Nat) : Except String Pos := do
  let f ← e.fact n
  match f.canonical with
  | some c => return (← e.fact c).pos
  | none => return f.pos

/-- `shouldEmitDwarfVarSafe`. -/
def shouldEmitSafe (e : Env) (n : Nat) : Except String Bool := do
  let d ← e.name n
  let f ← e.fact n
  -- ssa.IsVarWantedForDebug
  let s := d.sym.bytes
  let s := if s.size > 0 && s[0]! == '&'.toUInt8 then s.extract 1 s.size else s
  let wanted := if s.size > 0 && s[0]! == '#'.toUInt8 then hasPrefix s "#yield".toUTF8 else true
  return wanted && d.sym.bytes != "_".toUTF8 && !f.untyped

/-- `shouldEmitDwarfVar`. -/
def shouldEmit (e : Env) (n : Nat) : Except String Bool := do
  if (← e.fact n).autotmp then return false
  e.shouldEmitSafe n

/-- `ssagen.StackOffset(slot)` (`pgen.go`). -/
def stackOffset (e : Env) (slot : Nat × Option Nat × Int) : Except String Int := do
  let (n, _, soff) := slot
  let off ← match (← e.name n).cls with
    | "PPARAM" | "PPARAMOUT" => do
      let (o, outregs) ← e.frameOf n
      pure (if outregs then localAutoOffset o else o + fixedFrameSize)
    | "PAUTO" => do pure (localAutoOffset (← e.frameOf n).1)
    | _ => pure 0
  return int32 (off + soff)

/-- The inlining index and tag adjustments of the `createXxxVar` functions
(`base.Flag.GenDwarfInl > 1`, checked to be 2). -/
def inlInfo (e : Env) (f : DwName) (tag : Nat) : Except String (Int × Nat) := do
  if f.inlFormal || f.inlLocal then
    let ii ← e.posInlIndex f.pos
    return (ii + 1, if f.inlFormal then DW_TAG_formal_parameter else tag)
  return (0, tag)

/-- `preInliningDcls(fnsym)`. -/
def preInliningDcls (e : Env) (sym : Nat) : Except String (Array Nat) := do
  let some (_, ns) := e.precursors[sym]?
    | throw s!"Info: preInliningDcls: no dwprecursor for y{sym}"
  let mut r := #[]
  for n in ns do
    let s := (← e.name n).sym.bytes
    if s.size == 0 then throw s!"Info: preInliningDcls: n{n} has an empty name"
    if s[0]! == '.'.toUInt8 || !(← e.shouldEmitSafe n) then continue
    r := r.push n
  return r

/-- `DwFixups.AbsFuncDwarfSym(fnsym)`. -/
def absFunc (e : Env) (sym : Nat) : Except String Nat :=
  match e.precursors[sym]? with
  | some (a, _) => pure a
  | none => throw s!"Info: AbsFuncDwarfSym: no dwprecursor for y{sym}"

end Env

/-- `Autot` by symbol name (`RecordAutoType` inserts, the `createXxxVar` functions delete). -/
abbrev M := StateT (Std.HashSet GoStr) (Except String)

/-- `createSimpleVar`. -/
def createSimpleVar (e : Env) (n : Nat) : M DwVar := do
  let d ← e.name n
  let f ← e.fact n
  let (tag, offs) ← match d.cls with
    | "PAUTO" => pure (DW_TAG_variable, localAutoOffset f.frameOffset)
    | "PPARAM" | "PPARAMOUT" =>
      pure (DW_TAG_formal_parameter,
        if f.outregs then localAutoOffset f.frameOffset else f.frameOffset + fixedFrameSize)
    | c => throw s!"Info: createSimpleVar unexpected class {c} for n{n}"
  let tsn ← e.typeSymName n
  let ty ← e.lookup (infoPrefix ++ tsn)
  modify (·.erase (typePrefix ++ tsn))
  let (inlIndex, tag) ← e.inlInfo f tag
  let (declFile, declLine, declCol) ← e.relPos (← e.declPos n)
  return { scope := 0, name := d.sym, tag, withLoclist := false,
           isReturnValue := d.cls == "PPARAMOUT", isInlFormal := f.inlFormal,
           dictIndex := f.dictIndex, stackOffset := int32 offs, type := some ty, declFile,
           declLine, declCol, inlIndex, childIndex := -1, isInAbstract := false,
           closureOffset := e.closureVars.getD n 0, list := .none }

/-- `createComplexVar` (`none`: not an auto or parameter). -/
def createComplexVar (e : Env) (dbg : FuncDebug) (vid : Nat) : M (Option DwVar) := do
  let some (n, slots) := dbg.vars[vid]? | throw s!"Info: no FuncDebug variable {vid}"
  let d ← e.name n
  let f ← e.fact n
  let tag? : Option Nat := match d.cls with
    | "PAUTO" => some DW_TAG_variable
    | "PPARAM" | "PPARAMOUT" => some DW_TAG_formal_parameter
    | _ => none
  let some tag := tag? | return none
  let tsn ← e.typeSymName n
  modify (·.erase (typePrefix ++ tsn))
  let ty ← e.lookup (infoPrefix ++ tsn)
  let (inlIndex, tag) ← e.inlInfo f tag
  let (declFile, declLine, declCol) ← e.relPos f.pos
  let some s0 := slots[0]? | throw s!"Info: FuncDebug variable {vid} has no slots"
  let some slot := dbg.slots[s0]? | throw s!"Info: no FuncDebug slot {s0}"
  let off ← e.stackOffset slot
  return some { scope := 0, name := d.sym, tag, withLoclist := true,
                isReturnValue := d.cls == "PPARAMOUT", isInlFormal := f.inlFormal,
                dictIndex := f.dictIndex, stackOffset := off, type := some ty, declFile,
                declLine, declCol, inlIndex, childIndex := -1, isInAbstract := false,
                closureOffset := e.closureVars.getD n 0,
                list := if e.lists.contains vid then .var vid else .none }

/-- `createHeapDerefLocationList(n, entryID)`: `DW_OP_fbreg <Heapaddr offset> DW_OP_deref` over
the whole function. -/
def heapDerefList (e : Env) (heapaddr : Nat) (entry : Int) : Except String (Array LocEntry) := do
  let off := localAutoOffset (← e.frameOf heapaddr).1
  let expr := (DwM.appendSleb128 (ByteArray.empty.push DW_OP_fbreg.toUInt8) off).push
    DW_OP_deref.toUInt8
  return #[{ startBlock := entry, startValue := -10000, endBlock := entry, endValue := -30000,
             expr }]

/-- `createConservativeVar`. -/
def createConservativeVar (e : Env) (n : Nat) : M DwVar := do
  let d ← e.name n
  let f ← e.fact n
  let tsn ← e.typeSymName n
  let ty ← e.lookup (infoPrefix ++ tsn)
  let tag := if d.cls == "PPARAM" || d.cls == "PPARAMOUT" then DW_TAG_formal_parameter
    else DW_TAG_variable
  let (inlIndex, tag) ← e.inlInfo f tag
  let (declFile, declLine, declCol) ← e.relPos f.pos
  let list ← match d.esc == 2, f.heapaddr with
    | true, some h => do
      let some dbg := e.dbg
        | throw s!"Info: createConservativeVar: heap variable n{n} without FuncDebug"
      pure (VarList.entries (← heapDerefList e h dbg.entry))
    | _, _ => pure VarList.none
  modify (·.insert (typePrefix ++ tsn))
  return { scope := 0, name := d.sym, tag, withLoclist := true,
           isReturnValue := d.cls == "PPARAMOUT", isInlFormal := false,
           dictIndex := f.dictIndex, stackOffset := int32 f.frameOffset, type := some ty, declFile,
           declLine, declCol, inlIndex, childIndex := -1, isInAbstract := false,
           closureOffset := e.closureVars.getD n 0, list }

/-- `markVarSeen`. -/
private def markVarSeen (dbg : FuncDebug) (seen : Std.HashSet Nat) (n vid : Nat) :
    Except String (Std.HashSet Nat) := do
  let mut seen := seen.insert n
  for s in (dbg.vars[vid]?.map (·.2)).getD #[] do
    let some (m, _, _) := dbg.slots[s]? | throw s!"Info: no FuncDebug slot {s}"
    seen := seen.insert m
  return seen

/-- `createDwarfVars(fnsym, true, fn, apDecls, closureVars)` with `sortDeclsAndVars`. -/
def createDwarfVars (e : Env) (apDecls : Array Nat) : M (Array Nat × Array DwVar) := do
  let mut vars : Array DwVar := #[]
  let mut decls : Array Nat := #[]
  let mut seen : Std.HashSet Nat := {}
  for n in apDecls do
    unless (← e.shouldEmit n) do continue
    if let some dbg := e.dbg then
      if let some vid := e.varIDMap[n]? then
        let r ← createComplexVar e dbg vid
        if let some v := r then
          decls := decls.push n
          vars := vars.push v
          seen ← markVarSeen dbg seen n vid
          continue
    seen := seen.insert n
    decls := decls.push n
    vars := vars.push (← createSimpleVar e n)
  if let some dbg := e.dbg then
    -- SSA-tracked variables not in apDecls.
    for h : i in [0:dbg.vars.size] do
      let n := dbg.vars[i].1
      if seen.contains n then continue
      unless (← e.shouldEmit n) do continue
      let r ← createComplexVar e dbg i
      if let some v := r then
        decls := decls.push n
        vars := vars.push v
        seen ← markVarSeen dbg seen n i
    -- Zero-sized variables the stackframe pass eliminated.
    for ent in e.pf.frame.optDcl do
      let n := ent.name
      if seen.contains n then continue
      let d ← e.name n
      if d.cls != "PAUTO" then continue
      let some t := d.type | throw s!"Info: OptDcl n{n} has no type"
      let some td := e.types[t]? | throw s!"Info: no type definition t{t}"
      let some size := td.size | throw s!"Info: OptDcl n{n}: type size unknown"
      if size == 0 then
        decls := decls.push n
        let v ← createSimpleVar e n
        vars := vars.push { v with stackOffset := 0 }
        let tsn ← e.typeSymName n
        modify (·.insert (typePrefix ++ tsn))
        seen := seen.insert n
  let dcl ← if e.wasInlined then e.preInliningDcls e.fnsym
    else match e.dbg with
      | none => pure apDecls
      | some dbg => do
        let mut dcl := apDecls
        for n in dbg.regOutputParams do
          let d ← e.name n
          let s := d.sym.bytes
          let s := if s.size > 0 && s[0]! == '&'.toUInt8 then s.extract 1 s.size else s
          if s.size > 0 && s[0]! == '#'.toUInt8 && !hasPrefix s "#yield".toUTF8 then continue
          if d.cls != "PPARAMOUT" || !(← e.fact n).outregs then
            throw s!"Info: invalid ir.Name n{n} on debugInfo.RegOutputParams list"
          dcl := dcl.push n
        pure dcl
  for n in dcl do
    if seen.contains n then continue
    unless (← e.shouldEmit n) do continue
    seen := seen.insert n
    if let some dbg := e.dbg then
      if let some vid := e.varIDMap[n]? then
        let r ← createComplexVar e dbg vid
        if let some v := r then
          decls := decls.push n
          vars := vars.push v
          continue
    let d ← e.name n
    if d.cls == "PPARAM" then
      let some canSSA := (← e.fact n).canSSA | throw s!"Info: CanSSA of n{n} unknown"
      if !canSSA then
        decls := decls.push n
        vars := vars.push (← createSimpleVar e n)
        continue
    decls := decls.push n
    vars := vars.push (← createConservativeVar e n)
  -- sortDeclsAndVars: parameters first, in signature order (sort.Stable).
  let mut paramOrder : Std.HashMap Nat Nat := {}
  let mut idx := 1
  for p in e.pf.dwarf.params do
    if let some n := p then
      paramOrder := paramOrder.insert n idx
      idx := idx + 1
  let inf := idx  -- larger than every parameter's order
  let sorted := stableSortBy (decls.zip vars) (fun (n, _) => paramOrder.getD n inf)
    (· < ·)
  return (sorted.map (·.1), sorted.map (·.2))

/-- `dwarf.Scope.AppendRange`. -/
def appendRange (rs : Array (Int × Int)) (s t : Int) : Array (Int × Int) :=
  if t ≤ s then rs
  else match rs.back? with
    | some (a, b) => if b == s then rs.pop.push (a, t) else rs.push (s, t)
    | none => rs.push (s, t)

/-- `dwarf.MergeRanges(in1, in2)`. -/
def mergeRanges (in1 in2 : Array (Int × Int)) : Array (Int × Int) := Id.run do
  let mut out : Array (Int × Int) := #[]
  let mut i := 0
  let mut j := 0
  for _ in [0:in1.size + in2.size] do
    let mut cur := (0, 0)
    if i < in2.size && j < in1.size then
      if in2[i]!.1 < in1[j]!.1 then
        cur := in2[i]!
        i := i + 1
      else
        cur := in1[j]!
        j := j + 1
    else if i < in2.size then
      cur := in2[i]!
      i := i + 1
    else
      cur := in1[j]!
      j := j + 1
    match out.back? with
    | some (a, b) => if cur.1 ≤ b then out := out.pop.push (a, cur.2) else out := out.push cur
    | none => out := out.push cur
  return out

/-- Scopes being assembled: parent, ranges, variables (indices into the sorted variables). -/
structure Scope where
  parent : Int := 0
  ranges : Array (Int × Int) := #[]
  vars : Array Nat := #[]
  deriving Inhabited

/-- `assembleScopes` (`scopeVariables` sorts the variables in place; `assembleInlines` sees
them sorted): the sorted variables and the scopes. -/
def assembleScopes (e : Env) (vars : Array DwVar) (varScopes : Array Nat) :
    Except String (Array DwVar × Array Scope) := do
  let dw := e.pf.dwarf
  let mut scopes : Array Scope := #[{}]
  for p in dw.parents do scopes := scopes.push { parent := p }
  -- scopeVariables
  let pairs := vars.zip varScopes
  let sorted := if e.regabi then stableSortBy pairs (·.2) (· < ·)
    else stableSortBy pairs (fun (v, s) => (s, v.stackOffset))
      (fun (s, o) (s', o') => s < s' || (s == s' && o < o'))
  let vars := sorted.map (·.1)
  let vs := sorted.map (·.2)
  let setVars (scopes : Array Scope) (s i0 i : Nat) : Except String (Array Scope) := do
    if s ≥ scopes.size then throw s!"Info: scope {s} out of range"
    return scopes.modify s fun sc => { sc with vars := (List.range' i0 (i - i0)).toArray }
  let mut i0 := 0
  for i in [0:vars.size] do
    if vs[i]! == vs[i0]! then continue
    scopes ← setVars scopes vs[i0]! i0 i
    i0 := i
  if i0 < vars.size then scopes ← setVars scopes vs[i0]! i0 vars.size
  -- scopePCs
  if !dw.marks.isEmpty then
    let progs := e.pf.asm.progs
    let some first := progs[0]? | throw "Info: no Progs"
    let mut p0 := first
    let mut scope ← e.findScope dw.marks p0.pos
    for p in progs do
      if p.pos == p0.pos then continue
      if scope ≥ scopes.size then throw s!"Info: scope {scope} out of range"
      scopes := scopes.modify scope fun sc => { sc with ranges := appendRange sc.ranges p0.pc p.pc }
      p0 := p
      scope ← e.findScope dw.marks p0.pos
    if p0.pc < e.textSize then
      if scope ≥ scopes.size then throw s!"Info: scope {scope} out of range"
      scopes := scopes.modify scope fun sc =>
        { sc with ranges := appendRange sc.ranges p0.pc e.textSize }
  -- compactScopes
  for k in [0:scopes.size - 1] do
    let i := scopes.size - 1 - k
    let s := scopes[i]!
    if s.parent < 0 || s.parent.toNat ≥ scopes.size then
      throw s!"Info: scope parent {s.parent} out of range"
    scopes := scopes.modify s.parent.toNat fun p => { p with ranges := mergeRanges p.ranges s.ranges }
  return (vars, scopes)

/-- `insertInlCall`: the call index of global inlining index `ii`, adding it (after its
parents) if new. -/
partial def insertInlCall (e : Env) (calls : Array DwInlCall) (imap : Std.HashMap Nat Nat)
    (ii : Nat) : Except String (Array DwInlCall × Std.HashMap Nat Nat × Nat) := do
  if let some k := imap[ii]? then return (calls, imap, k)
  let some node := e.inls[ii]? | throw s!"Info: no inlining tree node {ii}"
  let (calls, imap, par) ← match node.parent with
    | some p => do
      let (c, m, k) ← insertInlCall e calls imap p
      pure (c, m, some k)
    | none => pure (calls, imap, none)
  let some f := node.func | throw s!"Info: inlining tree node {ii} has no function"
  let callFile ← match ← e.base node.pos with
    | some (_, some fi, _) => pure fi
    | _ => throw s!"Info: CallPos of inlining tree node {ii} has no file index"
  let (_, callLine, _) ← e.relPos node.pos
  let absFun ← e.absFunc f
  let ic : DwInlCall := { inlIndex := ii, callFile, callLine, absFun := some absFun,
                          children := #[], root := par.isNone, ranges := #[], vars := #[] }
  let idx := calls.size
  let calls := calls.push ic
  let imap := imap.insert ii idx
  let calls := match par with
    | some p => calls.modify p fun c => { c with children := c.children.push idx }
    | none => calls
  return (calls, imap, idx)

/-- `unifyCallRanges`. -/
partial def unifyCallRanges (calls : Array DwInlCall) (idx : Nat) : Array DwInlCall := Id.run do
  let mut calls := calls
  for c in calls[idx]!.children do
    calls := unifyCallRanges calls c
    let r := calls[c]!.ranges
    calls := calls.modify idx fun ic => { ic with ranges := mergeRanges ic.ranges r }
  return calls

/-- `checkInlCall`: the ranges of call `idx` lie within its parent's (the function's extent
for a root). -/
partial def checkInlCall (calls : Array DwInlCall) (size : Int) (idx : Nat) (parent : Option Nat) :
    Except String Unit := do
  let ic := calls[idx]!
  let par := match parent with
    | some p => calls[p]!.ranges
    | none => #[(0, size)]
  for (s, t) in ic.ranges do
    unless (par.any fun (a, b) => s ≥ a && t ≤ b) do
      throw s!"Info: malformed inlined routine range: call {idx} range [{s},{t}) not contained in {par}"
  for k in ic.children do checkInlCall calls size k (some idx)

/-- `assembleInlines(fnsym, dwVars)`: the inlined calls (variables by index into `vars`) and
the variables with their child indices and `IsInAbstract`. -/
def assembleInlines (e : Env) (vars : Array DwVar) :
    Except String (Array DwVar × Array DwInlCall) := do
  let progs := e.pf.asm.progs
  let mut calls : Array DwInlCall := #[]
  let mut imap : Std.HashMap Nat Nat := {}
  let mut prevpos := Pos.none
  for p in progs do
    if p.pos == prevpos then continue
    let ii ← e.posInlIndex p.pos
    if ii ≥ 0 then
      let (c, m, _) ← insertInlCall e calls imap ii.toNat
      calls := c
      imap := m
    prevpos := p.pos
  -- Partition the variables by inlining index (keys in first-seen order).
  let mut vmap : Std.HashMap Int (Array Nat) := {}
  let mut keys : Array Int := #[]
  for h : k in [0:vars.size] do
    let v := vars[k]
    if !vmap.contains v.inlIndex then keys := keys.push v.inlIndex
    vmap := vmap.insert v.inlIndex ((vmap.getD v.inlIndex #[]).push k)
    if v.inlIndex == 0 then continue
    let ii := (v.inlIndex - 1).toNat
    let mut idx := 0
    if let some x := imap[ii]? then
      idx := x
    else
      -- A var produced by the inliner with no remaining Prog: add a call.
      let (c, m, x) ← insertInlCall e calls imap ii
      calls := c
      imap := m
      idx := x
    calls := calls.modify idx fun c => { c with vars := c.vars.push k }
  -- Child indices.
  let mut vars := vars
  for ii in keys do
    let sl := vmap.getD ii #[]
    if ii == 0 && !e.wasInlined then
      for h : j in [0:sl.size] do
        vars := vars.modify sl[j] fun v => { v with childIndex := j }
      continue
    let sym ← if ii == 0 then pure e.fnsym
      else match e.inls[(ii - 1).toNat]? with
        | some nd => match nd.func with
          | some f => pure f
          | none => throw s!"Info: InlinedFunction({ii - 1}): node has no function"
        | none => throw s!"Info: InlinedFunction({ii - 1}): no inlining tree node"
    -- makePreinlineDclMap
    let dcl ← e.preInliningDcls sym
    let mut m : Std.HashMap (GoStr × GoStr × Nat × Nat) Nat := {}
    for h : i in [0:dcl.size] do
      let n := dcl[i]
      let (file, line, col) ← e.relPos (← e.fact n).pos
      let vp := ((← e.name n).sym, file, line, col)
      if m.contains vp then continue
      m := m.insert vp i
    let mut synthCount := m.size
    for k in sl do
      let v := vars[k]!
      let synthesized := hasPrefix v.name.bytes "~".toUTF8 || v.name.bytes == "_".toUTF8
      match m[(v.name, v.declFile, v.declLine, v.declCol)]? with
      | some idx => vars := vars.set! k { v with childIndex := idx, isInAbstract := !synthesized }
      | none =>
        vars := vars.set! k { v with childIndex := synthCount }
        synthCount := synthCount + 1
  -- PC ranges.
  let addRange (calls : Array DwInlCall) (s t : Int) (ii : Int) : Except String (Array DwInlCall) := do
    if ii == -1 || s == t then return calls
    let some idx := imap[ii.toNat]? | throw s!"Info: can't find inlIndex {ii} in imap for prog at {s}"
    return calls.modify idx fun c => { c with ranges := c.ranges.push (s, t) }
  let mut start : Int := -1
  let mut curii : Int := -1
  for h : i in [0:progs.size] do
    let p := progs[i]
    if i > 0 && p.pos == progs[i - 1]!.pos then continue
    let ii ← e.posInlIndex p.pos
    if ii == curii then continue
    if start != -1 then calls ← addRange calls start p.pc curii
    start := p.pc
    curii := ii
  if start != -1 then calls ← addRange calls start e.textSize curii
  for k in [0:calls.size] do
    if calls[k]!.root then calls := unifyCallRanges calls k
  for k in [0:calls.size] do
    if calls[k]!.root then checkInlCall calls e.textSize k none
  return (vars, calls)

private def configWord (pf : ProgFile) (k : String) : Option String :=
  match pf.config.find? (·.1 == k) with
  | some (_, .word w) => some w
  | some (_, .str s) => some s.toStringLossy
  | none => none

/-- The environment of a file: definitions of every section, the derived maps, and the checks
of the configuration `Info` is ported for. -/
def Env.ofFile (pf : ProgFile) : Except String Env := do
  let need (k v : String) : Except String Unit :=
    if configWord pf k == some v then pure ()
    else throw s!"Info: config {k} = {configWord pf k}, only {v} is ported"
  need "arch" "arm64"
  need "flagN" "0"
  need "optimize" "1"
  need "locationlists" "1"
  need "gendwarfinl" "2"
  let exps := ((configWord pf "experiments").getD "").splitOn ","
  unless exps.contains "dwarf5" do throw "Info: DWARF 4 (no dwarf5 experiment) is not ported"
  let defs := pf.frame.defs ++ pf.genin.defs ++ pf.prog0.defs ++ pf.asm.defs ++ pf.dwarf.defs
  let mut names : Std.HashMap Nat NameDef := {}
  let mut types : Std.HashMap Nat TypeDef := {}
  let mut symByName : Std.HashMap GoStr Nat := {}
  let mut symName : Std.HashMap Nat GoStr := {}
  let mut bases : Std.HashMap Nat (PosBase × Option Int × PosBaseExt) := {}
  let mut inls : Std.HashMap Nat InlDef := {}
  for d in defs do
    match d with
    | .name n x => names := names.insert n x
    | .type n x => types := types.insert n x
    | .sym n s abi =>
      symName := symName.insert n s
      if abi == 0 then symByName := symByName.insert s n
    | .posBase i b fi x => bases := bases.insert i (b, fi, x)
    | .inl k x => inls := inls.insert k x
  let dw := pf.dwarf
  let facts := dw.names.foldl (fun m f => m.insert f.name f) {}
  let frame := (pf.frame.dclOut ++ pf.frame.optDcl).foldl
    (fun m (d : DclEntry) => m.insert d.name (d.off, d.flags.outregs)) {}
  let precursors := dw.precursors.foldl (fun m (s, a, ns) => m.insert s (a, ns)) {}
  let closureVars := if dw.needctxt then dw.closure.foldl (fun m (n, o) => m.insert n o) {}
    else {}
  let dbg := pf.prog0.dbg
  let (varIDMap, lists) := match dbg with
    | some d =>
      ((d.vars.zipIdx).foldl (fun m ((n, _), i) => m.insert n i) {},
       d.lists.foldl (fun s (k, es) => if es.isEmpty then s else s.insert k) {})
    | none => ({}, {})
  let wasInlined := pf.asm.fn.attr &&& Obj.AttrWasInlined.toNat != 0
  return { pf, names, types, symByName, symName, bases, inls, facts, frame, precursors,
           closureVars, dbg, varIDMap, lists, fnsym := pf.asm.fn.sym, wasInlined,
           regabi := pf.abi != 0, textSize := pf.asm.textSize }

end Info

open Info in
/-- `dwarfgen.Info(ctxt, fnsym, infosym, curfn)` for `populateDWARF` (anonymous `infosym`). -/
def info (pf : GoFV.Asm.ProgFile) : Except String InfoOut := do
  let e ← Env.ofFile pf
  let dw := pf.dwarf
  if dw.fn.isNone then throw "Info: populateDWARF did not run (no dwfn line)"
  -- Autot before Info, by name.
  let mut autot : Std.HashSet GoStr := {}
  for y in pf.prog0.autot do autot := autot.insert (← e.symNameOf y)
  -- apdecls (isODCLFUNC).
  let mut apdecls : Array Nat := #[]
  for n in dw.dcl do
    let f ← e.fact n
    if !f.oname then continue
    let cls := (← e.name n).cls
    if cls == "PAUTO" then
      if !f.used then throw s!"Info: debuginfo unused node n{n} (AllocFrame should truncate Dcl)"
    else if cls != "PPARAM" && cls != "PPARAMOUT" then continue
    unless (← e.shouldEmit n) do continue
    apdecls := apdecls.push n
    autot := autot.insert (typePrefix ++ (← e.typeSymName n))
  let ((decls, vars), autotOut) ← (createDwarfVars e apdecls).run autot
  -- R_USETYPE relocations: Autot and the non-itab R_USEIFACE targets, by name, once each.
  let mut typesyms : Array GoStr := autotOut.toArray
  for r in pf.prog0.relocs do
    if r.type == "R_USEIFACE" then
      let some y := r.sym | throw "Info: R_USEIFACE without a symbol"
      let s ← e.symNameOf y
      if !hasPrefix s.bytes itabPrefix then typesyms := typesyms.push s
  let sortedSyms := typesyms.qsort fun a b => bytesLt a.bytes b.bytes
  let mut useType : Array Reloc := #[]
  let mut last : Option GoStr := none
  for s in sortedSyms do
    if last == some s then continue
    last := some s
    useType := useType.push { off := 0, siz := 0, type := "R_USETYPE", add := 0,
                              sym := some (← e.lookup s) }
  -- Scopes and inlined calls.
  let mut varScopes : Array Nat := #[]
  for d in decls do varScopes := varScopes.push (← e.findScope dw.marks (← e.declPos d))
  let (vars, scopes) ← assembleScopes e vars varScopes
  let (vars, calls) ← assembleInlines e vars
  -- Number the variables as the dwarf section does: the scopes' first, then the calls'.
  let mut vix : Std.HashMap Nat Nat := {}
  let mut outVars : Array DwVar := #[]
  let mut outScopes : Array DwScope := #[]
  for sc in scopes do
    let mut rs := #[]
    for k in sc.vars do
      match vix[k]? with
      | some j => rs := rs.push j
      | none =>
        vix := vix.insert k outVars.size
        rs := rs.push outVars.size
        outVars := outVars.push vars[k]!
    outScopes := outScopes.push { parent := sc.parent, ranges := sc.ranges, vars := rs }
  let mut outCalls : Array DwInlCall := #[]
  for c in calls do
    let mut rs := #[]
    for k in c.vars do
      match vix[k]? with
      | some j => rs := rs.push j
      | none =>
        vix := vix.insert k outVars.size
        rs := rs.push outVars.size
        outVars := outVars.push vars[k]!
    outCalls := outCalls.push { c with vars := rs }
  return { vars := outVars, scopes := outScopes, inlCalls := outCalls, useType }

end GoFV.Dwarf
