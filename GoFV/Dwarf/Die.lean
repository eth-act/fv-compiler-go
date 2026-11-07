import Std.Data.HashSet
import GoFV.Dwarf.Const
import GoFV.Dwarf.Sym
import GoFV.Util.PdqSort

/-!
# DWARF subprogram DIEs (`cmd/internal/dwarf/dwarf.go`; `docs/PASSES3.md` E2)

`populateDWARF`'s DIE part (`cmd/internal/obj/dwarf.go`, without `generateDebugLinesSymbol`):
`PutAbstractFunc` then `PutConcreteFunc` when the function has an abstract function symbol,
else `PutDefaultFunc`, writing the info, location list, range list and abstract function
symbols of `dwfn` with the `dwarf.Context` of `Sym.lean`. Ported with their write order:
`putattr` (all forms but the linker-only `DW_CLS_GO_TYPEREF` address), `PutRngListRanges`,
`isEmptyInlinedCall`, `inlChildren`, `inlinedVarTable`, `putPrunedScopes`, `putparamtypes`,
`putscope`, `concreteVar`, `putAbstractVar`, `putvar` (`putvarAbbrev`, `putAbstractVarAbbrev`
of `putvarabbrevgen.go`), `putInlinedFunc`, `emitHiLoPc`, and `ssa.FuncDebug.PutLocationListDwarf5`
(the `PutLocationList` closures of `dwarfgen`).

Only the DWARF 5 branches exist (`buildcfg.Experiment.Dwarf5` is on in the corpus: range lists
are `DW_RLE` lists, inlined calls and lexical blocks always use the ranges abbrevs, low/high PC
are `addrx`/`udata`, location lists are `DW_LLE` lists); on linux `DW_FORM_udata_pseudo` is
`DW_FORM_udata`.

Shared state that the Go code mutates in place is threaded through `DieSt`:
`isEmptyInlinedCall` sets `InlIndex := -2` in the call array (later `inlChildren` calls see
it), `putInlinedFunc` sorts the call's `InlVars` in place, and `putPrunedScopes` stores
`dictIndexToOffset` in the `FnState`. Variables are the indices of the dwarf section's `var`
lines (Go compares `*dwarf.Var` by identity). The sorts by `ChildIndex` are `slices.SortFunc`
(pdqsort, not stable: `GoFV.Util.PdqSort.sortBy`, same comparisons and swaps as Go), so equal
`ChildIndex`es would land as in Go; quick-v10 has none (`assembleInlines` numbers each group's
variables distinctly; 12,722 sorts of two or more variables, 98 of more than 12).

`putattr`'s error results are dropped by most Go callers (`putvar`, `putAbstractVar`,
`PutAbstractFunc`, …): a nil reference or an unsupported form then writes nothing and the
writer goes on. The port does the same; Go's panics (type assertions on the attribute data,
`AddSectionOffset`, `concreteVar`'s default case) and the errors `populateDWARF` reports
(`Diag`) fail.
-/

namespace GoFV.Dwarf

open GoFV.Asm

structure DieCtx where
  dw : GoFV.Asm.Dwarf        -- the dwarf section records
  fn : GoFV.Asm.DwFn         -- dw.fn
  textSym : Nat              -- FnState.StartPC (the text symbol's number)
  textSize : Int             -- FnState.Size (the asm section's text size)
  varList : Nat → Except String (Array GoFV.Asm.LocEntry)  -- FuncDebug.LocationLists[VarID]
  getPC : Int → Int → Except String Int                    -- FuncDebug.GetPC(block, value)

/-- The `data any` argument of `putattr`: nil (or an integer, which no used form reads), a
string, a byte slice, or a symbol. -/
inductive AttrData where
  | nil
  | str (s : ByteArray)
  | bytes (b : ByteArray)
  | sym (s : Nat)

/-- A symbol or nil (`dwarf.Sym`). -/
def AttrData.ofSym : Option Nat → AttrData
  | some s => .sym s
  | none => .nil

/-- What the writer mutates besides the symbols: the inlined calls (`InlIndex`, `InlVars`
order) and `FnState.dictIndexToOffset`. -/
structure DieSt where
  calls : Array DwInlCall
  dictIndexToOffset : Option (Array Int) := none
  deriving Inhabited

abbrev DieM := StateT DieSt DwM

instance {α} : Inhabited (DieM α) := ⟨throw "DieM: unreachable"⟩

namespace Die

variable (c : DieCtx)

def var (k : Nat) : DieM DwVar :=
  match c.dw.vars[k]? with
  | some v => pure v
  | none => throw s!"dwarf var {k} out of range"

def call (k : Nat) : DieM DwInlCall := do
  match (← get).calls[k]? with
  | some ic => pure ic
  | none => throw s!"inlined call {k} out of range"

/-- `putattr(ctxt, s, abbrev, form, cls, value, data)`. Go's error returns (unsupported form,
nil reference) write nothing; callers drop them. -/
def putattr (s : Nat) (_abbrev form cls : Nat) (value : Int) (data : AttrData) : DieM Unit := do
  let blockData (n : Int) : DieM ByteArray := match data with
    | .bytes b =>
      if n.toNat ≤ b.size then pure (b.extract 0 n.toNat)
      else throw s!"putattr: block slice [:{n}] of {b.size} bytes"
    | _ => throw "putattr: block data is not a []byte"
  if form == DW_FORM_addr then
    match data with
    | .nil => if value == 0 then DwM.addInt s 8 0 else
        if cls == DW_CLS_GO_TYPEREF then throw "AddSectionOffset: should be used only in the linker"
        else DwM.addAddress s none value
    | .sym r =>
      if cls == DW_CLS_GO_TYPEREF then throw "AddSectionOffset: should be used only in the linker"
      else DwM.addAddress s (some r) value
    | _ => throw "putattr: DW_FORM_addr data is not a symbol"
  else if form == DW_FORM_block1 then
    if cls == DW_CLS_ADDRESS then
      DwM.addInt s 1 (1 + 8)
      DwM.addInt s 1 DW_OP_addr
      match data with
      | .sym r => DwM.addAddress s (some r) 0
      | .nil => DwM.addAddress s none 0
      | _ => throw "putattr: DW_CLS_ADDRESS data is not a symbol"
    else
      let value := value % 256
      DwM.addInt s 1 value
      DwM.addBytes s (← blockData value)
  else if form == DW_FORM_block2 then
    let value := value % 65536
    DwM.addInt s 2 value
    DwM.addBytes s (← blockData value)
  else if form == DW_FORM_block4 then
    let value := value % 4294967296
    DwM.addInt s 4 value
    DwM.addBytes s (← blockData value)
  else if form == DW_FORM_block then
    DwM.uleb128put s value
    DwM.addBytes s (← blockData value)
  else if form == DW_FORM_data1 then DwM.addInt s 1 value
  else if form == DW_FORM_data2 then DwM.addInt s 2 value
  else if form == DW_FORM_data4 then
    if cls == DW_CLS_PTR then
      match data with
      | .sym r => DwM.addDWARFAddrSectionOffset s r value
      | _ => throw "AddDWARFAddrSectionOffset: data is not a symbol"
    else DwM.addInt s 4 value
  else if form == DW_FORM_data8 then DwM.addInt s 8 value
  else if form == DW_FORM_sdata then DwM.sleb128put s value
  else if form == DW_FORM_udata then DwM.uleb128put s value
  else if form == DW_FORM_string then
    match data with
    | .str str =>
      DwM.addString s str
      for _ in [str.size:value.toNat] do DwM.addInt s 1 0
    | _ => throw "putattr: DW_FORM_string data is not a string"
  else if form == DW_FORM_flag then
    DwM.addInt s 1 (if value != 0 then 1 else 0)
  else if form == DW_FORM_ref_addr || form == DW_FORM_sec_offset then
    match data with
    | .nil => pure ()  -- "dwarf: null reference", dropped by the callers
    | .sym r => DwM.addDWARFAddrSectionOffset s r value
    | _ => throw "AddDWARFAddrSectionOffset: data is not a symbol"
  else if form == DW_FORM_addrx then
    match data with
    | .sym r => DwM.writeDwTxtAddrx s r (c.fn.dwTextCount * 2)
    | _ => throw "AddIndirectTextRef: data is not a symbol"
  else pure ()  -- "dwarf: unsupported attribute form", dropped by the callers

/-- `PutRngListRanges(ctxt, sym, base, ranges)`. -/
def putRngListRanges (sym base : Nat) (ranges : Array (Int × Int)) : DieM Unit := do
  DwM.addInt sym 1 DW_RLE_base_addressx
  DwM.writeDwTxtAddrx sym base (c.fn.dwTextCount * 2)
  for (st, en) in ranges do
    DwM.addInt sym 1 DW_RLE_offset_pair
    DwM.uleb128put sym st
    DwM.uleb128put sym en
  DwM.addInt sym 1 DW_RLE_end_of_list

/-- `FnState.PutRanges` (DWARF 5): a range list in `s.Ranges` based at `s.StartPC`. -/
def putRanges (ranges : Array (Int × Int)) : DieM Unit :=
  putRngListRanges c c.fn.ranges c.textSym ranges

/-- `isEmptyInlinedCall(slot, calls)`: marks empty calls with `InlIndex = -2`. -/
partial def isEmptyInlinedCall (slot : Nat) : DieM Bool := do
  let ic ← call slot
  if ic.inlIndex == -2 then return true
  let mut live := false
  for k in ic.children do
    if !(← isEmptyInlinedCall k) then live := true
  if ic.ranges.size > 0 then live := true
  if !live then
    modify fun st => { st with calls := st.calls.modify slot fun ic => { ic with inlIndex := -2 } }
  return !live

/-- `inlChildren(slot, calls)`: `none` is slot -1 (the root calls). -/
def inlChildren (slot : Option Nat) : DieM (Array Nat) := do
  let mut kids := #[]
  match slot with
  | some slot =>
    for k in (← call slot).children do
      if !(← isEmptyInlinedCall k) then kids := kids.push k
  | none =>
    for k in [0:(← get).calls.size] do
      if (← call k).root then
        if !(← isEmptyInlinedCall k) then kids := kids.push k
  return kids

/-- `inlinedVarTable(inlcalls)`: the variables of the inlined calls. -/
def inlinedVarTable : DieM (Std.HashSet Nat) := do
  return (← get).calls.foldl (fun m ic => ic.vars.foldl (·.insert ·) m) {}

/-- `slices.SortFunc(vars, byChildIndexCmp)`. -/
def sortByChildIndex (vars : Array Nat) : Array Nat :=
  GoFV.Util.PdqSort.sortBy (fun a b => (c.dw.vars[a]!).childIndex < (c.dw.vars[b]!).childIndex) vars

/-- `dwarfFileIndex(pos)`. -/
def dwarfFileIndex (fileIndex : Int) : Int := 1 + fileIndex

/-- `concreteVar(fnabbrev, v)`. -/
def concreteVar (fnabbrev : Nat) (v : DwVar) : DieM Bool :=
  if fnabbrev == DW_ABRV_FUNCTION || fnabbrev == DW_ABRV_WRAPPER then pure false
  else if fnabbrev == DW_ABRV_FUNCTION_CONCRETE || fnabbrev == DW_ABRV_WRAPPER_CONCRETE then
    pure v.isInAbstract
  else if fnabbrev == DW_ABRV_INLINED_SUBROUTINE || fnabbrev == DW_ABRV_INLINED_SUBROUTINE_RANGES then
    pure true
  else throw "concreteVar: should never happen"

/-- `putAbstractVarAbbrev(v)`. -/
def putAbstractVarAbbrev (v : DwVar) : Nat :=
  if v.tag == DW_TAG_variable then DW_ABRV_PUTVAR_START + 0 else DW_ABRV_PUTVAR_START + 1

/-- `putvarAbbrev(v, concrete, withLoclist)`. -/
def putvarAbbrev (v : DwVar) (concrete withLoclist : Bool) : Nat :=
  let pick (a b : Nat) := DW_ABRV_PUTVAR_START + if withLoclist then a else b
  if v.tag == DW_TAG_variable then
    if concrete then pick 2 3
    else if v.closureOffset > 0 then pick 4 5
    else pick 6 7
  else
    if concrete then pick 8 9
    else if v.closureOffset > 0 then pick 10 11
    else pick 12 13

/-- `putAbstractVar(ctxt, info, v)`. -/
def putAbstractVar (info : Nat) (v : DwVar) : DieM Unit := do
  let abv := putAbstractVarAbbrev v
  DwM.uleb128put info abv
  putattr c info abv DW_FORM_string DW_CLS_STRING v.name.size (.str v.name.bytes)
  if v.tag == DW_TAG_formal_parameter then
    putattr c info abv DW_FORM_flag DW_CLS_FLAG (if v.isReturnValue then 1 else 0) .nil
  if v.tag == DW_TAG_variable then
    putattr c info abv DW_FORM_udata DW_CLS_CONSTANT v.declLine .nil
  putattr c info abv DW_FORM_ref_addr DW_CLS_REFERENCE 0 (.ofSym v.type)

/-- The entries `v.PutLocationList` writes (`none`: the closure is nil). -/
def varEntries (v : DwVar) : DieM (Option (Array LocEntry)) :=
  match v.list with
  | .none => pure none
  | .var k => some <$> liftExcept (c.varList k)
  | .entries es => pure (some es)
where
  liftExcept {α} : Except String α → DieM α
    | .ok a => pure a
    | .error e => throw e

/-- `FuncDebug.PutLocationListDwarf5(entries, ctxt, listSym, startPC)`. -/
def putLocationListDwarf5 (entries : Array LocEntry) (listSym startPC : Nat) : DieM Unit := do
  let getPC (b v : Int) : DieM Int := match c.getPC b v with
    | .ok pc => pure pc
    | .error e => throw e
  DwM.addInt listSym 1 DW_LLE_base_addressx
  DwM.writeDwTxtAddrx listSym startPC (c.fn.dwTextCount * 2)
  for e in entries do
    let pcBegin ← getPC e.startBlock e.startValue
    let pcEnd ← getPC e.endBlock e.endValue
    DwM.addInt listSym 1 DW_LLE_offset_pair
    DwM.addBytes listSym (DwM.appendUleb128 .empty (pcBegin % (2 ^ 64 : Nat)).toNat)
    DwM.addBytes listSym (DwM.appendUleb128 .empty (pcEnd % (2 ^ 64 : Nat)).toNat)
    DwM.addBytes listSym (DwM.appendUleb128 .empty e.expr.size)
    DwM.addBytes listSym e.expr
  DwM.addInt listSym 1 DW_LLE_end_of_list

/-- `putvar(ctxt, s, v, absfn, fnabbrev, inlIndex, encbuf)` (`inlIndex` only reaches
`RecordDclReference`, whose fixup the export records without it). -/
def putvar (k : Nat) (absfn : Option Nat) (fnabbrev : Nat) : DieM Unit := do
  let v ← var c k
  let info := c.fn.info
  let concrete ← concreteVar fnabbrev v
  let dio := (← get).dictIndexToOffset
  let hasParametricType := !concrete && v.dictIndex > 0 &&
    (match dio with
     | some d => d[v.dictIndex - 1]?.getD 0 != 0
     | none => false)
  let entries ← varEntries c v
  let withLoclist := v.withLoclist && entries.isSome
  let abv := putvarAbbrev v concrete withLoclist
  DwM.uleb128put info abv
  if concrete then
    putattr c info abv DW_FORM_ref_addr DW_CLS_REFERENCE 0 (.ofSym absfn)
    let some to := absfn | throw "RecordDclReference: nil abstract function"
    DwM.recordDclReference info to v.childIndex
  else
    putattr c info abv DW_FORM_string DW_CLS_STRING v.name.size (.str v.name.bytes)
    if v.tag == DW_TAG_formal_parameter then
      putattr c info abv DW_FORM_flag DW_CLS_FLAG (if v.isReturnValue then 1 else 0) .nil
    putattr c info abv DW_FORM_udata DW_CLS_CONSTANT v.declLine .nil
    if hasParametricType then
      let off := (dio.getD #[])[v.dictIndex - 1]!
      putattr c info abv DW_FORM_ref_addr DW_CLS_REFERENCE off (.sym info)
    else
      putattr c info abv DW_FORM_ref_addr DW_CLS_REFERENCE 0 (.ofSym v.type)
    if v.closureOffset > 0 then
      putattr c info abv DW_FORM_udata DW_CLS_CONSTANT v.closureOffset .nil
  match withLoclist, entries with
  | true, some es =>
    let some loc := c.fn.loc | throw "putvar: location list without a loc symbol"
    putattr c info abv DW_FORM_sec_offset DW_CLS_PTR (← DwM.size loc) (.sym loc)
    putLocationListDwarf5 c es loc c.textSym
  | _, _ =>
    let loc : ByteArray :=
      if v.withLoclist then .empty
      else if v.stackOffset == 0 then ByteArray.mk #[DW_OP_call_frame_cfa.toUInt8]
      else DwM.appendSleb128 (ByteArray.mk #[DW_OP_fbreg.toUInt8]) v.stackOffset
    putattr c info abv DW_FORM_block1 DW_CLS_BLOCK loc.size (.bytes loc)

/-- `putparamtypes(ctxt, s, scopes, fnabbrev)`. -/
def putparamtypes (scopes : Array DwScope) (fnabbrev : Nat) : DieM (Option (Array Int)) := do
  if fnabbrev == DW_ABRV_FUNCTION_CONCRETE then return none
  let mut maxDictIndex := 0
  for sc in scopes do
    for k in sc.vars do
      let v ← var c k
      if v.dictIndex > maxDictIndex then maxDictIndex := v.dictIndex
  if maxDictIndex == 0 then return none
  let info := c.fn.info
  let mut d : Array Int := Array.replicate maxDictIndex 0
  for sc in scopes do
    for k in sc.vars do
      let v ← var c k
      if v.dictIndex == 0 || d[v.dictIndex - 1]! != 0 then continue
      d := d.set! (v.dictIndex - 1) (← DwM.size info)
      DwM.uleb128put info DW_ABRV_DICT_INDEX
      let n := s!".param{v.dictIndex - 1}".toUTF8
      putattr c info DW_ABRV_DICT_INDEX DW_FORM_string DW_CLS_STRING n.size (.str n)
      putattr c info DW_ABRV_DICT_INDEX DW_FORM_ref_addr DW_CLS_REFERENCE 0 (.ofSym v.type)
      putattr c info DW_ABRV_DICT_INDEX DW_FORM_udata DW_CLS_CONSTANT (v.dictIndex - 1) .nil
  return some d

/-- `putscope(ctxt, s, scopes, curscope, fnabbrev, encbuf)`. -/
partial def putscope (scopes : Array DwScope) (curscope : Nat) (fnabbrev : Nat) : DieM Nat := do
  let info := c.fn.info
  for k in scopes[curscope]!.vars do
    putvar c k c.fn.absfn fnabbrev
  let this := curscope
  let mut curscope := curscope + 1
  while curscope < scopes.size do
    let scope := scopes[curscope]!
    if scope.parent != this then return curscope
    if scope.vars.size == 0 then
      curscope ← putscope scopes curscope fnabbrev
      continue
    DwM.uleb128put info DW_ABRV_LEXICAL_BLOCK_RANGES
    putattr c info DW_ABRV_LEXICAL_BLOCK_RANGES DW_FORM_sec_offset DW_CLS_PTR
      (← DwM.size c.fn.ranges) (.sym c.fn.ranges)
    putRanges c scope.ranges
    curscope ← putscope scopes curscope fnabbrev
    DwM.uleb128put info 0
  return curscope

/-- `putPrunedScopes(ctxt, s, fnabbrev)`. -/
def putPrunedScopes (fnabbrev : Nat) : DieM Unit := do
  if c.dw.scopes.size == 0 then return
  let pvars ← inlinedVarTable
  let scopes := c.dw.scopes.map fun sc =>
    { sc with vars := sortByChildIndex c (sc.vars.filter (!pvars.contains ·)) }
  let d ← putparamtypes c scopes fnabbrev
  modify fun st => { st with dictIndexToOffset := d }
  if (← putscope c scopes 0 fnabbrev) < scopes.size then throw "multiple toplevel scopes"

/-- `emitHiLoPc(ctxt, abbrev, fns, st, en)` (DWARF 5). -/
def emitHiLoPc (abv : Nat) (st en : Int) : DieM Unit := do
  putattr c c.fn.info abv DW_FORM_addrx DW_CLS_CONSTANT st (.sym c.textSym)
  putattr c c.fn.info abv DW_FORM_udata DW_CLS_CONSTANT en .nil

/-- `putInlinedFunc(ctxt, s, callIdx)`. -/
partial def putInlinedFunc (callIdx : Nat) : DieM Unit := do
  let info := c.fn.info
  let ic ← call callIdx
  let callee := ic.absFun
  let abv := DW_ABRV_INLINED_SUBROUTINE_RANGES
  DwM.uleb128put info abv
  putattr c info abv DW_FORM_ref_addr DW_CLS_REFERENCE 0 (.ofSym callee)
  putattr c info abv DW_FORM_sec_offset DW_CLS_PTR (← DwM.size c.fn.ranges) (.sym c.fn.ranges)
  putRanges c ic.ranges
  putattr c info abv DW_FORM_data4 DW_CLS_CONSTANT (dwarfFileIndex ic.callFile) .nil
  -- expandPseudoForm(DW_FORM_udata_pseudo) on linux
  putattr c info abv DW_FORM_udata DW_CLS_CONSTANT ic.callLine .nil
  -- the sort is in place: the call array's InlVars share the slice
  let vars := sortByChildIndex c ic.vars
  modify fun st => { st with calls := st.calls.modify callIdx fun ic => { ic with vars } }
  for k in vars do
    if !(← var c k).isInAbstract then continue
    putvar c k callee abv
  for sib in ← inlChildren (some callIdx) do
    putInlinedFunc sib
  DwM.uleb128put info 0

/-- `strings.HasPrefix(name, `"".`)`. -/
def unqualified (name : GoFV.SSA.GoStr) : Bool :=
  name.bytes.size ≥ 3 && name.bytes[0]! == 0x22 && name.bytes[1]! == 0x22 && name.bytes[2]! == 0x2e

/-- `PutAbstractFunc(ctxt, s)`: writes `s.Absfn`. -/
def putAbstractFunc (absfn : Nat) : DieM Unit := do
  let abv := DW_ABRV_FUNCTION_ABSTRACT
  DwM.uleb128put absfn abv
  let fullname := c.fn.name
  if unqualified fullname then throw s!"unqualified symbol name: {fullname.quoteInto ""}"
  putattr c absfn abv DW_FORM_string DW_CLS_STRING fullname.size (.str fullname.bytes)
  putattr c absfn abv DW_FORM_data1 DW_CLS_CONSTANT DW_INL_inlined .nil
  putattr c absfn abv DW_FORM_udata DW_CLS_CONSTANT c.fn.startLine .nil
  putattr c absfn abv DW_FORM_flag DW_CLS_FLAG (if c.fn.external then 1 else 0) .nil
  let mut flattened : Array Nat := #[]
  let mut offsets : Array Int := #[]
  if c.dw.scopes.size > 0 then
    let pvars ← inlinedVarTable
    for sc in c.dw.scopes do
      for k in sc.vars do
        if pvars.contains k || !(← var c k).isInAbstract then continue
        flattened := flattened.push k
    if flattened.size > 0 then
      flattened := sortByChildIndex c flattened
      for k in flattened do
        offsets := offsets.push (← DwM.size absfn)
        putAbstractVar c absfn (← var c k)
  let mut offs := #[]
  for k in flattened, o in offsets do
    offs := offs.push ((← var c k).childIndex, o)
  DwM.recordChildDieOffsets absfn offs
  DwM.uleb128put absfn 0

/-- `PutConcreteFunc(ctxt, s, isWrapper, fncount)` (`fncount` is unused). -/
def putConcreteFunc (absfn : Nat) (isWrapper : Bool) : DieM Unit := do
  let info := c.fn.info
  let abv := if isWrapper then DW_ABRV_WRAPPER_CONCRETE else DW_ABRV_FUNCTION_CONCRETE
  DwM.uleb128put info abv
  putattr c info abv DW_FORM_ref_addr DW_CLS_REFERENCE 0 (.sym absfn)
  emitHiLoPc c abv 0 c.textSize
  putattr c info abv DW_FORM_block1 DW_CLS_BLOCK 1 (.bytes (ByteArray.mk #[DW_OP_call_frame_cfa.toUInt8]))
  if isWrapper then putattr c info abv DW_FORM_flag DW_CLS_FLAG 1 .nil
  putPrunedScopes c abv
  for sib in ← inlChildren none do
    putInlinedFunc c sib
  DwM.uleb128put info 0

/-- `PutDefaultFunc(ctxt, s, isWrapper)`. -/
def putDefaultFunc (isWrapper : Bool) : DieM Unit := do
  let info := c.fn.info
  let abv := if isWrapper then DW_ABRV_WRAPPER else DW_ABRV_FUNCTION
  DwM.uleb128put info abv
  let name := c.fn.name
  if unqualified name then throw s!"unqualified symbol name: {name.quoteInto ""}"
  putattr c info DW_ABRV_FUNCTION DW_FORM_string DW_CLS_STRING name.size (.str name.bytes)
  emitHiLoPc c abv 0 c.textSize
  putattr c info abv DW_FORM_block1 DW_CLS_BLOCK 1 (.bytes (ByteArray.mk #[DW_OP_call_frame_cfa.toUInt8]))
  if isWrapper then
    putattr c info abv DW_FORM_flag DW_CLS_FLAG 1 .nil
  else
    putattr c info abv DW_FORM_data4 DW_CLS_CONSTANT (dwarfFileIndex c.fn.startFile) .nil
    putattr c info abv DW_FORM_udata DW_CLS_CONSTANT c.fn.startLine .nil
    putattr c info abv DW_FORM_flag DW_CLS_FLAG (if c.fn.external then 1 else 0) .nil
  putPrunedScopes c abv
  for sib in ← inlChildren none do
    putInlinedFunc c sib
  DwM.uleb128put info 0

/-- Every variable, call child and scope index of the records is in range (the port then
indexes them without checks). -/
def checkIndices : Except String Unit := do
  let nv := c.dw.vars.size
  let nc := c.dw.inlCalls.size
  for sc in c.dw.scopes do
    for k in sc.vars do
      unless k < nv do throw s!"scope var {k} out of range"
  for ic in c.dw.inlCalls do
    for k in ic.vars do
      unless k < nv do throw s!"inlined call var {k} out of range"
    for k in ic.children do
      unless k < nc do throw s!"inlined call child {k} out of range"

end Die

/-- populateDWARF's DIE part: writes dw.fn's info, loc, ranges and absfn symbols. -/
def putFunc (c : DieCtx) : DwM Unit := do
  match Die.checkIndices c with
  | .ok () => pure ()
  | .error e => throw e
  let run : DieM Unit := match c.fn.absfn with
    | some absfn => do
      Die.putAbstractFunc c absfn
      Die.putConcreteFunc c absfn c.fn.wrapper
    | none => Die.putDefaultFunc c c.fn.wrapper
  discard <| run.run { calls := c.dw.inlCalls }

end GoFV.Dwarf
