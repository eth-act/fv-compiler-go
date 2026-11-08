import GoFV.Gen.Genssa
import GoFV.Asm.Flush
import GoFV.Asm.Parse
import GoFV.Asm.Print
import GoFV.Dwarf.Debug
import GoFV.Dwarf.Info
import GoFV.Dwarf.Die
import GoFV.Dwarf.Lines
import GoFV.SSA.Parse

/-!
# The driver's back end: `AllocFrame` through `populateDWARF` (`docs/DRIVER.md`, mode `full3`)

`chain` runs the Phase 3 ports on one function, each on the previous one's result: the frame
layout (`GoFV.Gen.allocFrame`), `genssa` with `defframe` (`GoFV.Gen.genssa`), `BuildFuncDebug`
(`GoFV.Dwarf.buildFuncDebug`), `Flushplist` (`GoFV.Asm.flush`), `dwarfgen.Info`
(`GoFV.Dwarf.info`) and the DWARF writers (`putFunc`, `generateDebugLinesSymbol`). Its input is
the function after `trim` (a `gofv-ssa` file whose last section is `trim`) and a driver input
file (`gofv-prog 3 in`, `GoFV.Asm.parseProgInput`): the definitions of a `.prog` file and the
inputs of these steps, none of their results. Where a recorded input is a result of an earlier
step (the `dwarf` section's `dwdcl` list and the `dwname` frame offsets and `used` flags, which
`populateDWARF` reads after `AllocFrame`), the chain replaces it by its own result.

Symbols: the chain numbers symbols as the input file does (all sections' `sym` definitions);
symbols `genssa` interns that the file does not define get numbers past the file's largest
(`SymTab`), and the assembler's new symbols (constants, pc-value tables) numbers past those.

`BackOut` is what the compiler installs or checks (`docs/DRIVER.md`): the text symbol's
`FuncInfo` header and funcaux symbols, `Size`, `Align`, `P` and `R`, the pc tables, funcdata,
`UsedFiles`, the local inlining tree, the contents of the data symbols the ports write
(pc-value tables, metadata symbols, constants, jump tables) and the function's DWARF symbols
with the child-DIE fixups. `printBack` writes it for the compiler; `checkFile` compares it with
the stock results of a full `.prog` file (`gofv-ssa-opt --back-check`).
-/

namespace GoFVTest.Driver.Back

open GoFV.SSA (GoStr Pos ExportFile ID)
open GoFV.Asm
open GoFV.Dwarf

/-! ## Symbols -/

/-- The chain's symbols: number → (name, ABI), named symbols by (name, ABI) (first number). -/
structure SymTab where
  syms : Std.HashMap Nat (GoStr × Nat) := {}
  idx : Std.HashMap (GoStr × Nat) Nat := {}
  next : Nat := 1
  /-- `sym` definitions of the numbers past the input file's. -/
  newDefs : Array Def := #[]

def SymTab.ofDefs (ds : Array Def) : SymTab := Id.run do
  let mut t : SymTab := {}
  for d in ds do
    if let .sym k nm abi := d then
      t := { t with syms := t.syms.insert k (nm, abi), next := max t.next (k + 1) }
      if !nm.bytes.isEmpty && !t.idx.contains (nm, abi) then t := { t with idx := t.idx.insert (nm, abi) k }
  return t

/-- The number of a named symbol, or a new number (always new for an anonymous one). -/
def SymTab.intern (t : SymTab) (nm : GoStr) (abi : Nat) : SymTab × Nat :=
  match (if nm.bytes.isEmpty then none else t.idx[(nm, abi)]?) with
  | some k => (t, k)
  | none =>
    let k := t.next
    ({ syms := t.syms.insert k (nm, abi),
       idx := if nm.bytes.isEmpty then t.idx else t.idx.insert (nm, abi) k,
       next := k + 1, newDefs := t.newDefs.push (.sym k nm abi) }, k)

def Addr.mapSym (f : Nat → Nat) (a : Addr) : Addr := { a with sym := a.sym.map f }

def Prog.mapSym (f : Nat → Nat) (p : Prog) : Prog :=
  { p with from_ := Addr.mapSym f p.from_, rest := p.rest.map fun (k, a) => (k, Addr.mapSym f a),
           to := Addr.mapSym f p.to }

def FuncAux.mapSym (f : Nat → Nat) (a : FuncAux) : FuncAux :=
  { gcArgs := a.gcArgs.map f, gcLocals := a.gcLocals.map f, stackObjects := a.stackObjects.map f,
    openCodedDeferInfo := a.openCodedDeferInfo.map f, argInfo := a.argInfo.map f,
    argLiveInfo := a.argLiveInfo.map f, wrapInfo := a.wrapInfo.map f }

/-- Every definition of a file (all sections). -/
def allDefs (pf : ProgFile) : Array Def :=
  pf.frame.defs ++ pf.genin.defs ++ pf.prog0.defs ++ pf.asm.defs ++ pf.dwarf.defs

/-! ## The result -/

/-- The DWARF part of the result: the symbols `populateDWARF` writes (the `dwfn` roles), the
child-DIE references and offsets, and the symbols' contents. -/
structure DwOut where
  fn : DwFn
  dieRefs : Array (Nat × Nat × Nat × Int)
  dieOffs : Option (Nat × Array (Int × Int))
  data : Array SymData
  deriving Inhabited

structure BackOut where
  /-- Symbol names by number. -/
  syms : Std.HashMap Nat (GoStr × Nat)
  fn : FuncInfo
  textSize : Int
  textAlign : Int
  text : ByteArray
  relocs : Array Reloc
  pcln : Pcln
  usedFiles : Array Nat
  inlTree : Array InlNode
  data : Array SymData
  dwarf : Option DwOut
  deriving Inhabited

/-- The kind, alignment and attributes of the DWARF symbols (`dwarfSym`; `SetPrecursorFunc`
makes the abstract function `SDWARFABSFCN` with `AttrDuplicateOK`). -/
def dwHeader (fn : DwFn) (y : Nat) : String × Int × Nat :=
  if y == fn.info then ("SDWARFFCN", 0, 0)
  else if some y == fn.loc then ("SDWARFLOC", 0, 0)
  else if y == fn.ranges then ("SDWARFRANGE", 0, 0)
  else if y == fn.lines then ("SDWARFLINES", 0, 0)
  else ("SDWARFABSFCN", 0, Obj.AttrDuplicateOK.toNat)

/-! ## The chain -/

/-- `FuncDebug.GetPC` after assembly (`ssagen/ssa.go:7366-7383`): block starts and
`valueToProgAfter` give a Prog, whose PC is its assembled one, or its `genssa` PC when the
assembler dropped it (`obj.Prog.Pc` keeps it). -/
def getPC (f : GoFV.SSA.Func) (gst : GoFV.Gen.GenState) (entry : ID) (asmPC : Std.HashMap Nat Int)
    (textSize : Int) (b v : Int) : Except String Int := do
  let pcOf (id : Nat) : Except String Int :=
    match asmPC[id]? with
    | some pc => pure pc
    | none => match gst.progs[id]? with
      | some p => pure p.pc
      | none => throw s!"GetPC: Prog {id} unknown"
  if v == -30000 then return textSize
  if v == -10000 then
    if b == entry then return 0
    let some id := (gst.bstart[b.toNat]?).join | throw s!"GetPC({b}, BlockStart): no block start"
    return ← pcOf id
  let v ← if v == -20000 then do
      let some blk := f.block? b.toNat | throw s!"GetPC({b}, BlockEnd): no block"
      let some last := blk.values.back? | throw s!"GetPC({b}, BlockEnd): empty block"
      pure last
    else pure v.toNat
  let some id := gst.progAfter[v]? | throw s!"GetPC({b}, {v}): no valueToProgAfter"
  pcOf id

/-- The chain's frame and genssa (A1–C6) with genssa's symbol numbers mapped to the input file's:
`tab` holds the file's symbols and the new ones, `gmap[k]` is the file number of genssa's `k`. -/
structure GenP0 where
  fr : GoFV.Gen.FrameOut
  gout : GoFV.Gen.GenOut
  tab : SymTab
  gmap : Array Nat

/-- The file number of genssa's symbol `k`. -/
def GenP0.gm (g : GenP0) (k : Nat) : Nat := g.gmap[k]?.getD k

/-- The frame layout (`allocFrame`) and `genssa` on it for a loaded environment and the driver
input file (`pin`) it was loaded with; symbols numbered as `chain` does. -/
def genP0 (env : GoFV.Gen.Env) (pin : ProgFile) : Except String GenP0 := do
  -- A1, A2: the frame.
  let fr ← (GoFV.Gen.allocFrame env).mapError (s!"frame: {·}")
  -- B1-C6: genssa on that frame.
  let gout ← (GoFV.Gen.genssa env fr).mapError (s!"genssa: {·}")
  -- Symbols: genssa's numbers to the file's.
  let mut tab := SymTab.ofDefs (allDefs pin)
  let mut gmap : Array Nat := #[]
  for (nm, abi) in gout.st.syms do
    let (t, k) := tab.intern nm abi
    tab := t
    gmap := gmap.push k
  return { fr, gout, tab, gmap }

/-- The file `Flushplist` reads: `pin` with the chain's frame and its P0 section (genssa's
Progs, function info and `needzero`, in the file's symbol numbers; the debug info `dbg`). -/
def GenP0.progFile (g : GenP0) (pin : ProgFile) (dbg : Option FuncDebug) : ProgFile :=
  let gst := g.gout.st
  let gm := g.gm
  let progs := g.gout.order.filterMap fun id => (gst.progs[id]?).map (Prog.mapSym gm)
  let t := pin.genin.text
  let fn0 : FuncInfo :=
    { sym := t.sym, args := t.args, locals := t.locals, funcID := t.funcID, funcFlag := t.funcFlag,
      startLine := t.startLine, attr := t.attr,
      spills := gst.spills.map fun x => { x with addr := Addr.mapSym gm x.addr },
      inlMarks := gst.inlMarks, jumpTables := gst.jumpTableSyms.map fun (y, ts) => (gm y, ts),
      aux := FuncAux.mapSym gm gst.aux }
  let p0 : Prog0 :=
    { pin.prog0 with defs := allDefs pin ++ g.tab.newDefs, progs, fn := fn0,
                     needzero := gst.dcl.filterMap fun d => if d.flags.needzero then some d.name else none,
                     regArgs := #[], dbg }
  let fr := g.fr
  let frame : Frame :=
    { pin.frame with dclOut := fr.dcl, optDcl := fr.optDcl, merges := fr.merges,
                     stksize := fr.stksize, stkptrsize := fr.stkptrsize, stkalign := fr.stkalign }
  { pin with frame, prog0 := p0 }

/-- Runs the chain on the function after `trim` (`e`) and a driver input file (`pin`). -/
def chain (e : ExportFile) (pin : ProgFile) : Except String BackOut := do
  let env ← (GoFV.Gen.Env.load e pin).mapError (s!"env: {·}")
  let g ← genP0 env pin
  let fr := g.fr
  let gst := g.gout.st
  let tab := g.tab
  let gm := g.gm
  let defs := allDefs pin
  -- E1: BuildFuncDebug on the frame (`Flag_locationlists`; DebugInfo set by buildssa).
  let auxToN : Std.HashMap Nat Nat := defs.foldl (init := {}) fun m d => match d with
    | .name k nd => match nd.aux with
      | some a => if m.contains a then m else m.insert a k
      | none => m
    | _ => m
  let dbgOut ← match pin.prog0.dbg with
    | none => pure none
    | some _ => some <$> (buildFuncDebug env (fr.dcl ++ fr.optDcl)).mapError (s!"BuildFuncDebug: {·}")
  let nameOf (a : Nat) : Except String Nat :=
    match auxToN[a]? with
    | some k => pure k
    | none => throw s!"BuildFuncDebug: aux a{a} has no name in the input file"
  let dbg ← match pin.prog0.dbg, dbgOut with
    | some d, some o => do
      let slots ← o.slots.mapM fun sl => do return (← nameOf sl.name, (none : Option Nat), sl.off)
      let vars ← (o.vars.zip o.varSlots).mapM fun (a, ss) => do return (← nameOf a, ss)
      let mut lists := #[]
      for h : k in [0:o.lists.size] do
        if !o.lists[k].isEmpty then lists := lists.push (k, o.lists[k])
      pure (some { d with entry := (o.entry : Int), slots, vars, lists, pcs := #[] } : Option FuncDebug)
    | _, _ => pure none
  -- P0: the prog0 section of the chain's file.
  let pf1 := g.progFile pin dbg
  -- D1-D7: Flushplist.
  let fo ← (flush pf1).mapError (s!"Flushplist: {·}")
  let st := fo.st
  -- The assembler's new symbols.
  let mut asmDefs : Array Def := #[]
  for h : k in [tab.next:st.syms.size] do
    let (nm, abi) := st.syms[k]
    asmDefs := asmDefs.push (.sym k nm abi)
  let mut syms := tab.syms
  for h : k in [tab.next:st.syms.size] do syms := syms.insert k st.syms[k]
  -- Metadata symbols genssa wrote.
  let mut data : Std.HashMap Nat SymData := {}
  for (k, o) in gst.symData.toList do
    let y := gm k
    data := data.insert y
      { sym := y, kind := o.kind, size := o.size, align := o.align, attr := o.attr, data := o.data,
        relocs := o.relocs.map fun r =>
          { off := r.off, siz := r.siz, type := r.type, add := r.add, sym := r.sym.map gm } }
  for (k, d) in st.symData.toList do data := data.insert k d
  let dataArr := (data.toArray.qsort (·.1 < ·.1)).map (·.2)
  let asm : Asm :=
    { defs := asmDefs, progs := fo.progs, fn := fo.fn, textSize := st.textSize,
      textAlign := st.textAlign, text := st.textP, relocs := st.textR, pcln := st.pcln,
      usedFiles := st.usedFiles.qsort (· < ·), inlTree := st.inlTree, data := dataArr, warns := #[] }
  let out : BackOut :=
    { syms, fn := fo.fn, textSize := st.textSize, textAlign := st.textAlign, text := st.textP,
      relocs := st.textR, pcln := st.pcln, usedFiles := asm.usedFiles, inlTree := st.inlTree,
      data := dataArr, dwarf := none }
  -- E2: populateDWARF.
  let some dwfn := pin.dwarf.fn | return out
  let frameOf : Std.HashMap Nat DclEntry := (fr.dcl ++ fr.optDcl).foldl (fun m d => m.insert d.name d) {}
  let names := pin.dwarf.names.map fun x => match frameOf[x.name]? with
    | some d => { x with frameOffset := d.off, used := d.flags.used, outregs := d.flags.outregs }
    | none => x
  let dw0 : Dwarf := { pin.dwarf with dcl := fr.dcl.map (·.name), names }
  let pf2 : ProgFile := { pf1 with asm, dwarf := dw0 }
  let io ← (info pf2).mapError (s!"Info: {·}")
  let dw : Dwarf := { dw0 with vars := io.vars, scopes := io.scopes, inlCalls := io.inlCalls }
  let ctx ← (AsmCtxt.ofFile pf2).mapError (s!"DWARF: {·}")
  let fileLine (p : Pos) : Except String (Int × Int) := ((getFileIndexAndLine p).run ctx |>.run' default)
  let asmPC : Std.HashMap Nat Int := fo.progs.foldl (fun m p => m.insert p.id p.pc) {}
  let entry : ID := (dbgOut.map (·.entry)).getD 0
  let varList (k : Nat) : Except String (Array LocEntry) :=
    match dbgOut.bind fun o => o.lists[k]? with
    | some l => pure l
    | none => throw s!"no location list for VarID {k}"
  let dctx : DieCtx := { dw, fn := dwfn, textSym := fo.fn.sym, textSize := st.textSize, varList,
                         getPC := getPC env.f gst entry asmPC st.textSize }
  let init : DwSt := { syms := ({} : Std.HashMap Nat DSym).insert dwfn.info { relocs := io.useType } }
  let run : DwM Unit := do
    putFunc dctx
    generateDebugLinesSymbol fo.fn.sym dwfn.lines fo.progs st.textSize fileLine
  let ((), ds) ← (run.run init).mapError (s!"DWARF: {·}")
  let roles := [some dwfn.info, dwfn.loc, some dwfn.ranges, some dwfn.lines, dwfn.absfn].filterMap id
  let mut dwData : Array SymData := #[]
  for y in roles do
    let d := (ds.syms[y]?).getD {}
    let (kind, align, attr) := dwHeader dwfn y
    dwData := dwData.push { sym := y, kind, size := d.data.size, align, attr, data := d.data,
                            relocs := d.relocs }
  return { out with dwarf := some { fn := dwfn, dieRefs := ds.dieRefs, dieOffs := ds.dieOffs,
                                    data := dwData } }

/-! ## Output -/

section Print
open GoFV.SSA.Print

/-- `y<k>`, or, with `byName`, the symbol's quoted name and ABI (named symbols) or role. -/
structure Refs where
  byName : Bool
  syms : Std.HashMap Nat (GoStr × Nat)
  roles : Std.HashMap Nat String

def Refs.y (r : Refs) (k : Nat) : W Unit :=
  if !r.byName then ref 'y' k
  else match r.syms[k]? with
    | some (nm, abi) =>
      if nm.bytes.isEmpty then s ((r.roles[k]?).getD s!"anon{k}") else do q nm; s s!"<{abi}>"
    | none => s s!"?{k}"

def Refs.opt (r : Refs) : Option Nat → W Unit
  | some k => r.y k
  | none => s "-"

def Refs.hole (r : Refs) : Option Nat → W Unit
  | some k => r.y k
  | none => s "_"

def pReloc (r : Refs) (x : Reloc) : W Unit := do
  s "reloc "; i x.off; sp; n x.siz; sp; s x.type; sp; i x.add; sp; r.opt x.sym; nl

def pData (r : Refs) (d : SymData) : W Unit := do
  s "data "; r.y d.sym; sp; s d.kind; sp; i d.size; sp; i d.align; sp; Print.hexNat d.attr; sp
  Print.bytes d.data; sp; n d.relocs.size; nl
  for x in d.relocs do pReloc r x

/-- The result lines (after `status ok`), in the order the compiler checks them. -/
def body (r : Refs) (o : BackOut) : W Unit := do
  let f := o.fn
  s "fn "; r.y f.sym; sp; i f.args; sp; i f.locals; sp; n f.funcID; sp; n f.funcFlag; sp
  i f.startLine; sp; Print.hexNat f.attr; nl
  let a := f.aux
  s "funcaux "; r.opt a.gcArgs; sp; r.opt a.gcLocals; sp; r.opt a.stackObjects; sp
  r.opt a.openCodedDeferInfo; sp; r.opt a.argInfo; sp; r.opt a.argLiveInfo; sp; r.opt a.wrapInfo; nl
  s "text "; i o.textSize; sp; i o.textAlign; sp; Print.bytes o.text; sp; n o.relocs.size; nl
  for x in o.relocs do pReloc r x
  let c := o.pcln
  s "pcln "; r.opt c.pcsp; sp; r.opt c.pcfile; sp; r.opt c.pcline; sp; r.opt c.pcinline; sp
  list r.hole c.pcdata; sp; list r.hole c.funcdata; nl
  s "usedfiles "; list n o.usedFiles; nl
  for h : k in [0:o.inlTree.size] do
    let x := o.inlTree[k]
    s "inltree "; n k; sp; i x.parent; sp; pos x.pos; sp; r.opt x.func; sp; q x.name; sp
    i x.parentPC; nl
  for d in o.data do pData r d
  if let some w := o.dwarf then
    let fn := w.fn
    s "dwsyms "; r.y fn.info; sp; r.opt fn.loc; sp; r.y fn.ranges; sp; r.opt fn.absfn; sp
    r.y fn.lines; nl
    for (y, ridx, tgt, dcl) in w.dieRefs do
      s "dieref "; r.y y; sp; n ridx; sp; r.y tgt; sp; i dcl; nl
    if let some (y, offs) := w.dieOffs then s "dieoff "; r.y y; sp; Print.pairs offs; nl
    for d in w.data do pData r d

/-- The symbols the result lines reference, ascending. -/
def BackOut.refs (o : BackOut) : Array Nat := Id.run do
  let mut ks : Std.HashSet Nat := {}
  let add (m : Std.HashSet Nat) (k : Option Nat) := match k with | some k => m.insert k | none => m
  let f := o.fn
  ks := ks.insert f.sym
  for k in [f.aux.gcArgs, f.aux.gcLocals, f.aux.stackObjects, f.aux.openCodedDeferInfo,
            f.aux.argInfo, f.aux.argLiveInfo, f.aux.wrapInfo] do ks := add ks k
  for x in o.relocs do ks := add ks x.sym
  let c := o.pcln
  for k in [c.pcsp, c.pcfile, c.pcline, c.pcinline] ++ c.pcdata.toList ++ c.funcdata.toList do
    ks := add ks k
  for x in o.inlTree do ks := add ks x.func
  let mut ds := o.data
  if let some w := o.dwarf then
    ds := ds ++ w.data
    for k in [some w.fn.info, w.fn.loc, some w.fn.ranges, w.fn.absfn, some w.fn.lines] do
      ks := add ks k
    for (y, _, tgt, _) in w.dieRefs do ks := (ks.insert y).insert tgt
    if let some (y, _) := w.dieOffs then ks := ks.insert y
  for d in ds do
    ks := ks.insert d.sym
    for x in d.relocs do ks := add ks x.sym
  return ks.toArray.qsort (· < ·)

/-- The compiler's input: `sym` lines for every referenced symbol, then the result lines and
`eof`. -/
def printBack (o : BackOut) : String :=
  let r : Refs := { byName := false, syms := o.syms, roles := {} }
  let w : W Unit := do
    for k in o.refs do
      let (nm, abi) := (o.syms[k]?).getD (⟨.empty⟩, 0)
      s "sym "; ref 'y' k; sp; q nm; sp; n abi; nl
    body r o
    s "eof\n"
  (w.run "").2

end Print

/-! ## Checking against a full `.prog` file -/

/-- The input view of a full `.prog` file: what `parseProgInput` gives for the driver input
file the compiler writes for it. -/
def inputView (pf : ProgFile) : ProgFile :=
  { pf with
    frame := { pf.frame with dclOut := #[], optDcl := #[], merges := #[], stksize := 0,
                             stkptrsize := 0, stkalign := 0, warns := #[] }
    genin := { pf.genin with warns := #[] }
    prog0 := { pf.prog0 with progs := #[], fn := default, needzero := #[], regArgs := #[],
                             dbg := pf.prog0.dbg.map fun d =>
                               { entry := 0, slots := #[], vars := #[], lists := #[],
                                 regOutputParams := d.regOutputParams, pcs := #[] },
                             warns := #[] }
    asm := { defs := pf.asm.defs, progs := #[], fn := default, textSize := 0, textAlign := 0,
             text := .empty, relocs := #[], pcln := ⟨none, none, none, none, #[], #[]⟩,
             usedFiles := #[], inlTree := #[], data := #[], warns := #[] }
    dwarf := { pf.dwarf with vars := #[], scopes := #[], inlCalls := #[], dieRefs := #[],
                             dieOffs := none, data := #[], warns := #[] } }

/-- The stock result of a full `.prog` file, as `chain` gives it: the `asm` section, the
metadata symbols' contents and the `dwarf` section's symbols and fixups. -/
def stockBack (pf : ProgFile) : BackOut :=
  let syms : Std.HashMap Nat (GoStr × Nat) := (allDefs pf).foldl (init := {}) fun m d => match d with
    | .sym k nm abi => m.insert k (nm, abi)
    | _ => m
  let a := pf.asm
  let dwarf := pf.dwarf.fn.map fun fn =>
    { fn, dieRefs := pf.dwarf.dieRefs, dieOffs := pf.dwarf.dieOffs, data := pf.dwarf.data }
  { syms, fn := a.fn, textSize := a.textSize, textAlign := a.textAlign, text := a.text,
    relocs := a.relocs, pcln := a.pcln, usedFiles := a.usedFiles, inlTree := a.inlTree,
    data := a.data, dwarf }

/-- The roles of the anonymous symbols (pc-value tables, DWARF symbols). -/
def roles (o : BackOut) : Std.HashMap Nat String := Id.run do
  let mut m : Std.HashMap Nat String := {}
  let c := o.pcln
  for (k, nm) in [(c.pcsp, "pcsp"), (c.pcfile, "pcfile"), (c.pcline, "pcline"), (c.pcinline, "pcinline")] do
    if let some k := k then m := m.insert k nm
  for h : j in [0:c.pcdata.size] do
    if let some k := c.pcdata[j] then m := m.insert k s!"pcdata{j}"
  if let some w := o.dwarf then
    m := m.insert w.fn.info "info"
    if let some k := w.fn.loc then m := m.insert k "loc"
    m := m.insert w.fn.ranges "ranges"
    m := m.insert w.fn.lines "lines"
  return m

/-- `o` written with symbols by name or role, its data lines sorted by symbol and limited to
the stock `asm` section's kinds (`own`: the symbols the `asm` section writes the contents of,
by name or role). -/
def canonText (o : BackOut) (own : Std.HashSet String) : Array String := Id.run do
  let r : Refs := { byName := true, syms := o.syms, roles := roles o }
  let key (k : Nat) : String := ((r.y k).run "").2
  let ds := (o.data.filter fun d => own.contains (key d.sym)).qsort fun a b => key a.sym < key b.sym
  let text := ((body r { o with data := ds }).run "").2
  return (text.splitOn "\n").toArray

/-- Compares the chain on `pf`'s input view with `pf`'s stock results: the first differing
line, if any. -/
def checkProg (e : ExportFile) (pf : ProgFile) : Except String (Option (String × String)) := do
  let ours ← chain e (inputView pf)
  let stock := stockBack pf
  let rs : Refs := { byName := true, syms := stock.syms, roles := roles stock }
  let own : Std.HashSet String := stock.data.foldl (fun m d => m.insert ((rs.y d.sym).run "").2) {}
  let a := canonText ours own
  let b := canonText stock own
  for k in [0:max a.size b.size] do
    if a[k]? != b[k]? then
      return some ((a[k]?).getD "<none>", (b[k]?).getD "<none>")
  return none

/-! ## Driver mode and corpus check -/

/-- The separator of the two inputs of `--back` on one stream: the `gofv-ssa` file ends with
`eof`, the driver input file starts with its header (strings are quoted, so a raw newline only
ends a line). -/
def inputHeader : ByteArray := "\ngofv-prog 3 in\n".toUTF8

/-- Splits `--back`'s input into the `gofv-ssa` file and the driver input file. -/
def splitInput (data : ByteArray) : Except String (ByteArray × ByteArray) := do
  let h := inputHeader
  for k in [0:data.size] do
    if k + h.size ≤ data.size && data[k]! == h[0]! && data.extract k (k + h.size) == h then
      return (data.extract 0 (k + 1), data.extract (k + 1) data.size)
  throw "no gofv-prog 3 in header"

/-- `gofv-ssa-opt --back <file>`: the chain on a `gofv-ssa` file (last section `trim`)
followed by a driver input file; `status ok` and `printBack`, or
`status error "<stage>" "<msg>"`. -/
def runBack (data : ByteArray) : String :=
  let res : Except (String × String) BackOut := do
    let (ssa, prog) ← (splitInput data).mapError ("parse", ·)
    let (e, _) ← (GoFV.SSA.parseExportExt ssa).mapError ("parse", ·)
    let pin ← (parseProgInput prog).mapError ("parse", ·)
    (chain e pin).mapError fun m => ((m.splitOn ":").headD "chain", m)
  match res with
  | .ok o => "status ok\n" ++ printBack o
  | .error (stage, m) => s!"status error {GoStr.quote stage} {GoStr.quote m}\n"

structure CheckStats where
  files : Nat := 0
  match_ : Nat := 0
  errors : Std.HashMap String Nat := {}
  diffs : Std.HashMap String Nat := {}
  reports : Array String := #[]

def CheckStats.merge (a b : CheckStats) : CheckStats :=
  let add := fun (m n : Std.HashMap String Nat) => n.fold (fun m k v => m.alter k (some <| ·.getD 0 + v)) m
  { files := a.files + b.files, match_ := a.match_ + b.match_, errors := add a.errors b.errors,
    diffs := add a.diffs b.diffs, reports := a.reports ++ b.reports }

def CheckStats.note (st : CheckStats) (maxReport : Nat) (kind : String) (cls file msg : String) :
    CheckStats :=
  let m := if kind == "error" then st.errors else st.diffs
  let c := m.getD cls 0
  let m := m.insert cls (c + 1)
  let st := if kind == "error" then { st with errors := m } else { st with diffs := m }
  if c < maxReport then { st with reports := st.reports.push s!"{kind.toUpper} [{cls}] {file}\n  {msg}" }
  else st

/-- One `.prog` file of `--back-check`. -/
def checkFile (maxReport : Nat) (path : System.FilePath) (st : CheckStats) : IO CheckStats := do
  let st := { st with files := st.files + 1 }
  let file := path.toString
  let progData ← IO.FS.readBinFile path
  let ssaData ← IO.FS.readBinFile (path.withExtension "ssa")
  let res : Except String (Option (String × String)) := do
    let (e, _) ← GoFV.SSA.parseExportExt ssaData
    let pf ← parseProgFile progData
    checkProg e pf
  match res with
  | .ok none => return { st with match_ := st.match_ + 1 }
  | .ok (some (a, b)) =>
    let cls := (a.splitOn " ").headD "?"
    return st.note maxReport "diff" cls file s!"port:  {a.take 300}\n  stock: {b.take 300}"
  | .error m =>
    return st.note maxReport "error" ((":".intercalate ((m.splitOn ":").take 2)).take 60).toString file m

/-- `gofv-ssa-opt --back-check [--jobs N] [--max-report N] [--table FILE] <dir|file>...`: the
chain on the input view of every `.prog` file (with its `.ssa` file) against the file's stock
results. Exit status 1 unless every function matches. -/
def runBackCheck (jobs maxReport : Nat) (table : Option String) (paths : Array String) :
    IO UInt32 := do
  let t0 ← IO.monoMsNow
  let mut files := #[]
  for p in paths do
    let p : System.FilePath := p
    if ← p.isDir then
      let fs ← p.walkDir
      files := files ++ (fs.filter (·.extension == some "prog")).qsort (·.toString < ·.toString)
    else files := files.push p
  let tasks ← (List.range jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st : CheckStats := {}
    for h : i in [0:files.size] do
      if i % jobs == j then st ← checkFile maxReport files[i] st
    return st
  let mut st : CheckStats := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 1
  let ms := (← IO.monoMsNow) - t0
  for r in st.reports do IO.println r
  let pctS := if st.files == 0 then "-" else s!"{st.match_ * 100 / st.files}%"
  let mut out := s!"| chain (AllocFrame … populateDWARF) | functions | match | mismatch | parity |\n\
    | --- | ---: | ---: | ---: | ---: |\n| end to end | {st.files} | {st.match_} | \
    {st.files - st.match_} | {pctS} |\n\n{ms} ms\n"
  for (kind, m) in [("difference (first differing line)", st.diffs), ("port error", st.errors)] do
    if m.isEmpty then continue
    out := out ++ s!"\n| {kind} | functions |\n| --- | ---: |\n"
    for (k, c) in m.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)) do
      out := out ++ s!"| `{k}` | {c} |\n"
  IO.println out
  if let some f := table then IO.FS.writeFile f out
  return if st.files > 0 && st.match_ == st.files then 0 else 1

end GoFVTest.Driver.Back
