import GoFVTest.SemDiff
import GoFV.SSA.Sem.Hooks
import GoFV.Asm.Parse
import Lean.Data.PersistentHashMap

open scoped GoFV.SSA.Sem.Fixed

/-!
# `mach-difftest`: whole functions under `runMach` against native execution (issue #552)

`docs/plans/semantics3.md` §9 step 3. The functions of `tools/semdiff/prog` (the sem-difftest
set), exported with their `gofv-prog` files, are linked into one machine image: each function's
asm-section text (the stock bytes) at its own address with the relocations applied as the linker
would, the constant symbols of the asm sections' `data` lines and the Phase 1 global image
(`globalImage`: type descriptors, strings, closures, …) at linked addresses, and the runtime
entry points at addresses with no code, where `runMach`'s hooks (`GoFV/SSA/Sem/Hooks.lean`,
`RtInfo.hooks`) take over. A call `<func>\t<arg>…` of `calls.txt` is built as in `sem-difftest`
(`buildArgs`: the arguments' bytes and the heap memory they point to), injected (`ι`: heap block
`n` at `(n + 1)·2^40`, the allocator table in the runtime's memory), placed in the ABI registers
and stack slots of the function's own ABI assignment, and run from the function's entry with
`X30` a return address outside the code. The outcome is printed like `sem-difftest`'s
(`returned <results> || <arguments read back>`, `panicked <message>`) and compared with
`native.txt` (`tools/semdiff/prog` under `qemu-aarch64-static`).

**Execution.** The run is `runMach`'s loop (`GoFV.Arm64.step` for words, `rtHook` for runtime
entry points) with the machine memory kept in a persistent map and the register files in arrays:
after each step the bytes the instruction may have stored (its effective addresses) are copied
from the step's memory into the map, after each hook its writes. Every call whose run takes at
most `--check-steps` steps (default 200) is run a second time with the definition itself,
`runMach R.hooks code ret fuel s0`, and the two outcomes must print the same (`definition
check`), so the loop is checked to be `runMach`. (The definition's memory and registers are
closures that nest once per write, which makes long runs quadratic: the threshold keeps the
check to a few minutes.) The summary counts the runtime entry points the runs called (`hooks`).

**Selection.** Functions whose code (or a program function it calls) calls the defer machinery
(`runtime.deferproc*`, `deferreturn`, `gorecover`), which the hooks do not model (§6), are
excluded and counted.

usage: `mach-difftest <export dir> <calls> <native> [--check-steps N] [--fuel N]`. Exit status 1
on a mismatch of a selected call.
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Arm64 GoFV.Asm

namespace GoFVTest.MachDiff

def _root_.BitVec.toUInt64 (a : BitVec 64) : UInt64 := UInt64.ofBitVec a

/-! ## Address plan

All below `2^40`, where no heap block is, and away from round numbers: a word of memory that
holds an address inside a window is read back as a pointer (`Layout.pullBytes`), so the windows
should not sit where the test's integers (edge values, powers of two) fall. Code, entry points
and data are within `ADRP`'s ±4 GB and the entry points within `BL`'s ±128 MB of the code. -/

def TEXT0 : Nat := 0x53a5c0000
def HOOK0 : Nat := TEXT0 + 0x4000000
def RET0 : BitVec 64 := BitVec.ofNat 64 (HOOK0 + 0x3ff0000)
def DATA0 : Nat := 0x56b7d0000
def GADDR : BitVec 64 := 0x57c3e1000
def RTADDR : BitVec 64 := 0x57d4f2000
def WBUF : BitVec 64 := 0x57e5a3000
/-- The stack region `[STACK_LO, STACK_HI)`: the goroutine starts with 8 KB and `morestack`
grows it in place. -/
def STACK_LO : Nat := 0xe5d3000000
def STACK_HI : Nat := STACK_LO + 0x1000000
/-- The part of the stack a runtime entry point can see (`Layout`'s window `gofv:stack`). -/
def STACK_WINDOW : Nat := 0x10000
def stackBlk : Blk := .global "gofv:stack"

def align (n a : Nat) : Nat := (n + a - 1) / a * a

/-! ## The program -/

/-- A program function: its export, its link address, its relocated text. -/
structure Fn where
  stem : String
  name : String
  prog : ProgFile
  tabs : Tables
  f : Func
  base : Nat
  text : ByteArray := ByteArray.empty
  /-- `sym y<k>` names of the prog file. -/
  syms : Std.HashMap Nat String
  deriving Inhabited

/-- Machine memory as a persistent map (absent bytes are 0). -/
abbrev PMem := Lean.PersistentHashMap UInt64 UInt8

/-- The linked program. -/
structure Program where
  fns : Array Fn
  byName : Std.HashMap String Nat
  /-- Address of each named symbol. -/
  addr : Std.HashMap String Nat
  /-- Address of each anonymous data symbol `(function index, y<k>)`. -/
  anon : Std.HashMap (Nat × Nat) Nat
  entries : Std.HashMap Nat String
  /-- Initial memory (text, data symbols, global images). -/
  init : PMem
  code : Std.HashMap Nat (BitVec 32)
  env : Env
  rt : RtInfo

def defsOf (p : ProgFile) : Array GoFV.Asm.Def :=
  p.frame.defs ++ p.genin.defs ++ p.prog0.defs ++ p.asm.defs

def symNames (p : ProgFile) : Std.HashMap Nat String :=
  (defsOf p).foldl (fun m d => match d with
    | .sym n name _ => m.insert n name.toStringLossy
    | _ => m) {}

/-- The callee names of a function's text relocations. -/
def calleesOf (fn : Fn) : List String :=
  fn.prog.asm.relocs.toList.filterMap fun r =>
    if r.type == "R_CALLARM64" || r.type == "RelocType(-32759)" then
      r.sym.bind fn.syms.get? else none

def deferNames : List String :=
  ["runtime.deferproc", "runtime.deferprocStack", "runtime.deferreturn", "runtime.gorecover"]

/-- Functions that reach the defer machinery through direct calls. -/
def deferReach (fns : Array Fn) (byName : Std.HashMap String Nat) : Std.HashSet String := Id.run do
  let mut bad : Std.HashSet String := {}
  for _ in [0:fns.size + 1] do
    let mut changed := false
    for fn in fns do
      if bad.contains fn.name then continue
      if (calleesOf fn).any fun c => deferNames.contains c || bad.contains c then
        bad := bad.insert fn.name
        changed := true
    if !changed then break
  let _ := byName
  return bad

def getW (t : ByteArray) (o : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((t[o]!).toNat + (t[o+1]!).toNat * 256 + (t[o+2]!).toNat * 65536 +
    (t[o+3]!).toNat * 16777216)

def putW (t : ByteArray) (o : Nat) (w : BitVec 32) : ByteArray := Id.run do
  let mut t := t
  for j in [0:4] do t := t.set! (o + j) (w.toNat / 256 ^ j % 256).toUInt8
  t

def setBits (w : BitVec 32) (lo len : Nat) (v : Nat) : BitVec 32 :=
  let m : BitVec 32 := BitVec.ofNat 32 ((2 ^ len - 1) * 2 ^ lo)
  (w &&& ~~~m) ||| BitVec.ofNat 32 ((v % 2 ^ len) * 2 ^ lo)

/-- Apply the text relocations (`R_CALLARM64`, `R_ADDRARM64`, `R_ARM64_PCREL_LDST*`) with
symbol addresses `symAddr`; other relocation types with bytes are an error. -/
def relocate (text : ByteArray) (base : Nat) (rs : Array GoFV.Asm.Reloc) (symAddr : Nat → Option Nat) :
    Except String ByteArray := do
  let mut t := text
  for r in rs do
    if r.siz == 0 then continue
    let o := r.off.toNat
    let some n := r.sym | throw s!"relocation {r.type} without a symbol"
    let some sa := symAddr n | throw s!"relocation {r.type}: symbol y{n} has no address"
    let target : BitVec 64 := BitVec.ofNat 64 sa + BitVec.ofInt 64 r.add
    let pc : BitVec 64 := BitVec.ofNat 64 (base + o)
    let adrp (w : BitVec 32) : BitVec 32 :=
      let pages := ((target >>> 12) - (pc >>> 12)).toNat
      setBits (setBits w 29 2 pages) 5 19 (pages / 4)
    if r.type == "R_CALLARM64" || r.type == "RelocType(-32759)" then
      t := putW t o (setBits (getW t o) 0 26 ((target - pc) >>> 2).toNat)
    else if r.type == "R_ADDRARM64" then
      t := putW t o (adrp (getW t o))
      t := putW t (o + 4) (setBits (getW t (o + 4)) 10 12 (target.toNat % 4096))
    else if r.type.startsWith "R_ARM64_PCREL_LDST" then
      let sc := match (r.type.drop 18).toString with
        | "8" => 0 | "16" => 1 | "32" => 2 | "64" => 3 | _ => 0
      t := putW t o (adrp (getW t o))
      t := putW t (o + 4) (setBits (getW t (o + 4)) 10 12 (target.toNat % 4096 / 2 ^ sc))
    else throw s!"relocation type {r.type}"
  return t

/-- The bytes of a Phase 1 allocation at its linked address (`ι` on globals only). -/
def imageBytes (addrOf : String → Option Nat) (a : Alloc) : Array UInt8 :=
  a.data.map fun b => match b with
    | .b x => x.toNat.toUInt8
    | .frag p i =>
      match p.blk with
      | .global s => match addrOf s with
        | some base => ((BitVec.ofNat 64 base + p.off).extractLsb' (8 * (i % 8)) 8).toNat.toUInt8
        | none => 0
      | _ => 0
    | .poison => 0

/-- Link the functions of an export directory. -/
def link (dir : String) : IO (Except String Program) := do
  let progs := (← (System.FilePath.mk dir).walkDir).filter (·.extension == some "prog")
  let progs := progs.qsort (·.toString < ·.toString)
  let mut fns : Array Fn := #[]
  let mut globals : Std.HashMap String Alloc := {}
  let mut gorder : Array String := #[]
  let mut next := TEXT0
  for p in progs do
    let some stem := p.fileStem | continue
    let ssa := p.withExtension "ssa"
    let .ok pf := parseProgFile (← IO.FS.readBinFile p) | return .error s!"{p}: parse error"
    let .ok e := parseExport (← IO.FS.readBinFile ssa) | return .error s!"{ssa}: parse error"
    let some last := e.sections.back? | continue
    for (k, a) in globalImage e do
      if !globals.contains k then
        globals := globals.insert k a
        gorder := gorder.push k
    let name := pf.pkg.toStringLossy ++ "." ++ pf.name.toStringLossy
    fns := fns.push { stem, name, prog := pf, tabs := e.tablesAt (e.sections.size - 1),
                      f := last.func, base := next, syms := symNames pf }
    next := align (next + pf.asm.text.size + 64) 64
  let byName : Std.HashMap String Nat :=
    (List.range fns.size).foldl (fun m i => m.insert fns[i]!.name i) {}
  -- data symbols of the asm sections, the global image, runtime entry points
  let mut addr : Std.HashMap String Nat := {}
  let mut anon : Std.HashMap (Nat × Nat) Nat := {}
  let mut windows : Array Window := #[]
  let mut init : Array (Nat × UInt8) := #[]
  let mut dataNext := DATA0
  for fn in fns do
    addr := addr.insert fn.name fn.base
    windows := windows.push { blk := .global fn.name, base := BitVec.ofNat 64 fn.base,
                              size := fn.prog.asm.text.size, data := false, writable := false }
  -- a program function's symbol is its code, not a data block (closures point to it)
  gorder := gorder.filter fun k => !byName.contains k
  for k in gorder do
    let a := globals[k]!
    addr := addr.insert k dataNext
    windows := windows.push { blk := .global k, base := BitVec.ofNat 64 dataNext,
                              size := a.data.size, data := true, writable := a.writable }
    dataNext := align (dataNext + a.data.size + 16) 64
  -- asm-section data symbols (constants, jump tables, pc tables)
  let mut dataSyms : Array (Nat × Nat × SymData) := #[]
  for i in [0:fns.size] do
    let fn := fns[i]!
    for d in fn.prog.asm.data do
      let nm := (fn.syms.get? d.sym).getD ""
      if nm != "" && addr.contains nm then continue
      if nm == "" then anon := anon.insert (i, d.sym) dataNext
      else addr := addr.insert nm dataNext
      dataSyms := dataSyms.push (dataNext, i, d)
      dataNext := align (dataNext + d.data.size + 16) 64
  -- the runtime's data the contracts return pointers to: `runtime.zerobase` (every zero-sized
  -- allocation, `Runtime.alloc`)
  if !addr.contains "runtime.zerobase" then
    addr := addr.insert "runtime.zerobase" dataNext
    windows := windows.push { blk := .global "runtime.zerobase", base := BitVec.ofNat 64 dataNext,
                              size := 8, data := true }
    dataNext := align (dataNext + 8 + 16) 64
  -- every other referenced name: a runtime entry point
  let mut hookNext := HOOK0
  let mut entries : Std.HashMap Nat String := {}
  let mut refd : Array String := #[]
  for fn in fns do
    for r in fn.prog.asm.relocs do
      if let some n := r.sym then refd := refd.push ((fn.syms.get? n).getD "")
  for k in gorder do
    for b in globals[k]!.data do
      if let .frag ⟨.global s, _⟩ _ := b then refd := refd.push s
  for nm in refd do
    if nm == "" || addr.contains nm then continue
    addr := addr.insert nm hookNext
    entries := entries.insert hookNext nm
    windows := windows.push { blk := .global nm, base := BitVec.ofNat 64 hookNext, size := 8,
                              data := false, writable := false }
    hookNext := hookNext + 16
  windows := windows.push { blk := stackBlk, base := BitVec.ofNat 64 (STACK_HI - STACK_WINDOW),
                            size := STACK_WINDOW, data := true }
  let addrOf (s : String) : Option Nat := addr.get? s
  -- images
  for k in gorder do
    let base := addr[k]!
    let bs := imageBytes addrOf globals[k]!
    for j in [0:bs.size] do init := init.push (base + j, bs[j]!)
  -- data symbols with their R_ADDR relocations
  for (base, i, d) in dataSyms do
    let fn := fns[i]!
    let mut bs := d.data
    for r in d.relocs do
      if r.type == "R_ADDR" && r.siz == 8 then
        let ta := r.sym.bind fun n => match fn.syms.get? n with
          | some "" | none => anon.get? (i, n)
          | some nm => addr.get? nm
        if let some ta := ta then
          let v := (BitVec.ofNat 64 ta + BitVec.ofInt 64 r.add).toNat
          for j in [0:8] do bs := bs.set! (r.off.toNat + j) (v / 256 ^ j % 256).toUInt8
    for j in [0:bs.size] do init := init.push (base + j, bs[j]!)
  -- text
  let mut code : Std.HashMap Nat (BitVec 32) := {}
  for i in [0:fns.size] do
    let fn := fns[i]!
    let symAddr (n : Nat) : Option Nat := match fn.syms.get? n with
      | some "" | none => anon.get? (i, n)
      | some nm => addr.get? nm
    match relocate fn.prog.asm.text fn.base fn.prog.asm.relocs symAddr with
    | .error e => return .error s!"{fn.stem}: {e}"
    | .ok t =>
      fns := fns.set! i { fn with text := t }
      for j in [0:t.size] do init := init.push (fn.base + j, t[j]!)
      for k in [0:t.size / 4] do code := code.insert (fn.base + 4 * k) (getW t (4 * k))
  let env : Env := { Env.runtime with globals := gorder.toList.map fun k => (k, globals[k]!) }
  let layout := Layout.make windows RTADDR
  let funcs := fns.map fun fn =>
    let calls : Std.HashMap String (List ABIParam) :=
      fn.tabs.auxes.foldl (fun m o => match o with
        | some { kind := .call (some s) (some abi), .. } =>
          match fn.tabs.aux? s with
          | some { kind := .sym nm .., .. } => m.insert nm.toStringLossy abi.params.toList
          | _ => m
        | _ => m) {}
    let pb := match fn.prog.asm.pcln.pcdata[4]? with
      | some (some y) => match (fn.prog.asm.data.find? (·.sym == y)) with
        | some d => d.data
        | none => ByteArray.empty
      | _ => ByteArray.empty
    let _ := ()
    ({ name := fn.name, entry := BitVec.ofNat 64 fn.base, size := fn.prog.asm.text.size,
       callABI := fun nm => (calls.get? nm).map (fn.tabs, ·), panicBounds := pb } : CodeInfo)
  let rt : RtInfo := { layout, funcs, entry? := fun a => entries.get? a.toNat, env, wbuf := WBUF }
  let pm := init.foldl (fun pm (a, b) => pm.insert a.toUInt64 b) ({} : PMem)
  return .ok { fns, byName, addr, anon, entries, init := pm, code, env, rt }

/-! ## Machine memory as a persistent map -/

def memOf (pm : PMem) : Memory := fun a =>
  match pm.find? a.toUInt64 with
  | some b => BitVec.ofNat 8 b.toNat
  | none => 0

def PMem.writeWord (pm : PMem) (a : Nat) (x : Nat) : PMem := Id.run do
  let mut pm := pm
  for i in [0:8] do pm := pm.insert (a + i).toUInt64 (x / 256 ^ i % 256).toUInt8
  pm

/-- The bytes an instruction may store, from the state before it (its effective addresses). -/
def storeRange (s : MState) : Insn → Option (BitVec 64 × Nat)
  | .ldst size vec opc mode rn _ =>
    let n := accessBytes size vec opc
    if !vec && size = 3 && opc = 2 then none
    else if (if vec then opc.getLsbD 0 else opc != 0) then none
    else some ((s.amode mode rn n).1, n)
  | .ldstPair opc vec mode ld imm7 _ rn _ =>
    if ld then none else
    let n := if vec then 4 * 2 ^ opc.toNat else (if opc.getLsbD 1 then 8 else 4)
    let base := s.rXsp rn
    let off := imm7.signExtend 64 * BitVec.ofNat 64 n
    some (if mode = 1 then base else base + off, 2 * n)
  | .ldstExcl _ _ ld _ _ rn _ => if ld then none else some (s.rXsp rn, 8)
  | .cas _ _ _ _ rn _ => some (s.rXsp rn, 8)
  | .atomic _ _ _ _ _ _ rn _ => some (s.rXsp rn, 8)
  | _ => none

/-- `s` with its memory `pm` and its register files read into arrays (the same functions;
`exec` writes registers by closure, which would otherwise nest once per write). -/
def flatten (s : MState) (pm : PMem) : MState :=
  let xs : Array (BitVec 64) := (List.range 32).toArray.map fun i => s.x (BitVec.ofNat 5 i)
  let vs : Array (BitVec 128) := (List.range 32).toArray.map fun i => s.v (BitVec.ofNat 5 i)
  { s with x := fun i => xs[i.toNat]!, v := fun i => vs[i.toNat]!, mem := memOf pm }

/-- `runMach`'s loop with the memory in `pm`: the outcome, the runtime entry points the run
called (in order), the step count. -/
partial def runLoop (P : Program) (fuel : Nat) (s : MState) (pm : PMem) :
    MOutcome × Array String × Nat := Id.run do
  let code : Code := fun a => P.code.get? a.toNat
  let mut s := s
  let mut pm := pm
  let mut hs : Array String := #[]
  for k in [0:fuel] do
    if s.pc = RET0 then return (.returned s, hs, k)
    match code s.pc with
    | some w =>
      match step code s with
      | .ok s' =>
        let mut pm' := pm
        if let some i := decode w then
          if let some (a, n) := storeRange s i then
            for j in [0:n] do
              let x := a + BitVec.ofNat 64 j
              pm' := pm'.insert x.toUInt64 (s'.mem x).toNat.toUInt8
        pm := pm'
        s := flatten s' pm
      | .error f => return (.ofFault s f, hs, k)
    | none =>
      hs := hs.push ((P.entries.get? s.pc.toNat).getD "?")
      match rtHook P.rt s with
      | some (.ret s' ws) =>
        for (a, x) in ws do pm := pm.insert a.toUInt64 x.toNat.toUInt8
        s := flatten s' pm
      | some (.panicked e s' ws) =>
        for (a, x) in ws do pm := pm.insert a.toUInt64 x.toNat.toUInt8
        return (.panicked e { s' with mem := memOf pm }, hs, k)
      | some (.stuck msg) => return (.stuck msg, hs, k)
      | none => return (.stuck s!"no code and no hook at {s.pc.toHex}", hs, k)
  return (.outOfFuel, hs, fuel)

/-! ## Calls -/

/-- The initial machine state of a call of `fn` on the argument images `imgs` (heap memory
`mem`), its function's own ABI assignments `params`. -/
def entryState (P : Program) (fn : Fn) (params : List ABIParam) (imgs : Array (Array Byte))
    (mem : Mem) : Except String (MState × PMem) := do
  let L := P.rt.layout
  let mut pm : PMem := P.init
  -- g: stack bounds and the stack guard (an 8 KB initial stack)
  let g := GADDR.toNat
  pm := pm.writeWord g STACK_LO
  pm := pm.writeWord (g + 8) STACK_HI
  pm := pm.writeWord (g + 16) (STACK_HI - 8192 + stackGuard)
  -- the allocator table and the arguments' heap blocks
  pm := pm.writeWord RTADDR.toNat mem.nextHeap
  for (b, a) in mem.blocks do
    match b with
    | .heap n => pm := pm.writeWord (RTADDR.toNat + 8 + 8 * n) a.data.size
    | _ => throw "argument memory with a non-heap block"
  let s0 : MState := { x := fun i => garbage (100 + i.toNat), sp := BitVec.ofNat 64 (STACK_HI - 4096),
                       v := fun i => (garbage (200 + i.toNat)).setWidth 128,
                       nzcv := GoFV.SSA.Sem.Flags.ofNZCV 0b0101, pc := BitVec.ofNat 64 fn.base,
                       mem := memOf pm }
  for (b, a) in mem.blocks do
    if let .heap n := b then
      for j in [0:a.data.size] do
        match L.pushByte s0 a.data[j]! with
        | some x => pm := pm.insert (heapBase n + BitVec.ofNat 64 j).toUInt64 x.toNat.toUInt8
        | none => pure ()
  let mut s := { s0 with mem := memOf pm }
  let ins := params.filter (!·.out)
  if ins.length != imgs.size then throw s!"{imgs.size} arguments for {ins.length} parameters"
  for (p, bs) in ins.zip imgs.toList do
    let t := fn.tabs.ty p.type
    if p.regs.isEmpty then
      let a := s.sp + BitVec.ofInt 64 p.offset
      for j in [0:bs.size] do
        match L.pushByte s bs[j]! with
        | some x => pm := pm.insert (a + BitVec.ofNat 64 j).toUInt64 x.toNat.toUInt8
        | none => pure ()
      s := { s with mem := memOf pm }
    else
      s := ((leaves t).zip p.regs.toList).foldl (fun s ((o, lt), r) =>
        setAbiReg s r (L.wordOf s (bs.extract o (o + lt.size)))) s
  -- MachEntry: X30 the return address, R28 g, R29 = SP - 8 (the frame-pointer chain)
  s := { s with x := fun i => if i = 30 then RET0 else if i = 28 then GADDR
                    else if i = 29 then s.sp - 8 else s.x i }
  return (s, pm)

/-- The final Phase 1 memory a printed outcome reads: the blocks reachable from the results'
and the arguments' bytes. -/
def finalMem (L : Layout) (s : MState) (roots : List (Array Byte)) : Mem :=
  L.pull s (roots.foldl (fun acc bs => L.pointees s bs ++ acc) [])

/-- Print an outcome as `sem-difftest` does. -/
def render (P : Program) (fn : Fn) (l : SemDiff.Loaded) (params : List ABIParam)
    (imgs : Array (Array Byte)) (s0 : MState) : MOutcome → String
  | .returned s =>
    let L := P.rt.layout
    if s.sp != s0.sp || s.x 28 != s0.x 28 || s.x 29 != s0.x 29 then
      s!"stuck: return without MachRet (SP {s0.sp.toHex} → {s.sp.toHex}, R28 {(s0.x 28).toHex} → \
        {(s.x 28).toHex}, R29 {(s0.x 29).toHex} → {(s.x 29).toHex})"
    else
    let outs := params.filter (·.out)
    let rbytes := outs.map fun p =>
      let t := fn.tabs.ty p.type
      if p.regs.isEmpty then L.pullBytes s (s.sp + BitVec.ofInt 64 p.offset) t.size
      else ((leaves t).zip p.regs.toList).foldl
        (fun buf ((o, lt), r) => putBytes buf o (L.regBytes (abiReg s r) lt))
        (Array.replicate t.size Byte.poison)
    let m := finalMem L s (rbytes ++ imgs.toList)
    let rsT := (rbytes.zip l.results.toList).map fun (bs, t) =>
      SemDiff.renderBytes fn.tabs m 8 t bs 0
    let asT := (imgs.toList.zip l.params.toList).map fun (bs, t) =>
      SemDiff.renderBytes fn.tabs m 8 t bs 0
    "\t".intercalate ("returned" :: rsT ++ "||" :: asT) ++
      (if outs.length == l.results.size then "" else s!"\t<{outs.length} results>")
  | .panicked e _ => "panicked " ++ e.message
  | .stuck msg => "stuck: " ++ msg
  | .outOfFuel => "outOfFuel"

structure Stats where
  calls : Nat := 0
  selected : Nat := 0
  excluded : Nat := 0
  agree : Nat := 0
  bad : Nat := 0
  checked : Nat := 0
  checkAgree : Nat := 0
  steps : Nat := 0
  /-- Calls of each runtime entry point (hooks). -/
  hooks : Std.HashMap String Nat := {}
  outcomes : Std.HashMap String Nat := {}

def main (args : List String) : IO UInt32 := do
  let rec opts : List String → Nat × Nat × List String
    | "--check-steps" :: n :: rest => let (_, f, r) := opts rest; (n.toNat!, f, r)
    | "--fuel" :: n :: rest => let (c, _, r) := opts rest; (c, n.toNat!, r)
    | a :: rest => let (c, f, r) := opts rest; (c, f, a :: r)
    | [] => (200, 50000000, [])
  let (checkSteps, fuel, pos) := opts args
  let [dir, callsFile, nativeFile] := pos
    | IO.eprintln "usage: mach-difftest <export dir> <calls> <native> [--check-steps N] [--fuel N]"; return 2
  let P ← match ← link dir with
    | .ok P => pure P
    | .error e => IO.eprintln s!"mach-difftest: link: {e}"; return 1
  let excl := deferReach P.fns P.byName
  let calls := (← IO.FS.lines callsFile).filter (· ≠ "")
  let native := (← IO.FS.lines nativeFile).filter (· ≠ "")
  if calls.size != native.size then
    IO.eprintln s!"{calls.size} calls but {native.size} native results"; return 1
  let mut cache : Std.HashMap String SemDiff.Loaded := {}
  let mut st : Stats := {}
  let mut exclFns : Std.HashSet String := {}
  let mut selFns : Std.HashSet String := {}
  for h : i in [0:calls.size] do
    let call := calls[i]
    let toks := call.splitOn "\t"
    let fname := toks.headD ""
    st := { st with calls := st.calls + 1 }
    let want := match native[i]!.splitOn " -> " with
      | [c, o] => if c == call then o else s!"<native line {i} is for {c}>"
      | _ => s!"<bad native line {i}>"
    let some fi := P.byName.get? ("main." ++ fname)
      | IO.println s!"MISMATCH {call}: function not linked"; st := { st with bad := st.bad + 1 }; continue
    let fn := P.fns[fi]!
    if excl.contains fn.name then
      st := { st with excluded := st.excluded + 1 }
      exclFns := exclFns.insert fname
      continue
    selFns := selFns.insert fname
    st := { st with selected := st.selected + 1 }
    let l ← match cache[fname]? with
      | some l => pure l
      | none =>
        match ← SemDiff.load (SemDiff.funcPath dir fname) with
        | .ok l => pure l
        | .error e => IO.println s!"MISMATCH {call}: {e}"; st := { st with bad := st.bad + 1 }; continue
    cache := cache.insert fname l
    let params := (abiParams fn.tabs fn.f).toList
    let got ← match SemDiff.buildArgs fn.tabs l.params toks.tail with
      | .error e => pure s!"stuck: bad arguments: {e}"
      | .ok (imgs, mem) =>
        match entryState P fn params imgs mem with
        | .error e => pure s!"stuck: entry: {e}"
        | .ok (s0, pm) =>
          let t0 ← IO.monoMsNow
          let (o, hs, k) := runLoop P fuel s0 pm
          st := { st with steps := st.steps + k,
                          hooks := hs.foldl (fun m h => m.insert h (m.getD h 0 + 1)) st.hooks }
          let r := render P fn l params imgs s0 o
          let t1 ← IO.monoMsNow
          if t1 - t0 > 2000 then IO.eprintln s!"slow: {t1 - t0} ms, {k} steps: {call}"
          if k ≤ checkSteps then
            let code : Code := fun a => P.code.get? a.toNat
            let o' := runMach P.rt.hooks code RET0 (k + 1) s0
            let r' := render P fn l params imgs s0 o'
            st := { st with checked := st.checked + 1 }
            if r' == r then st := { st with checkAgree := st.checkAgree + 1 }
            else IO.println s!"DEFINITION {call}: runMach {r'}, loop {r}"
          pure r
    let kind := ((got.splitOn "\t").headD "").splitOn " " |>.headD ""
    st := { st with outcomes := st.outcomes.insert kind (st.outcomes.getD kind 0 + 1) }
    if got == want then st := { st with agree := st.agree + 1 }
    else
      IO.println s!"MISMATCH {call}: machine {got}, native {want}"
      st := { st with bad := st.bad + 1 }
  let kinds := st.outcomes.toList.map (fun (k, n) => s!"{k} {n}")
  IO.println s!"mach-difftest: {P.fns.size} functions linked; {st.calls} calls of \
    {selFns.size + exclFns.size} functions; {exclFns.size} functions ({st.excluded} calls) excluded \
    (defer machinery); {st.selected} calls of {selFns.size} functions run under runMach \
    ({", ".intercalate kinds}), {st.steps} machine steps; native agrees on {st.agree}, \
    {st.bad} mismatches; definition check: {st.checkAgree} of {st.checked} runs of at most \
    {checkSteps} steps agree with runMach itself"
  IO.println s!"excluded: {", ".intercalate (exclFns.toList.mergeSort (· ≤ ·))}"
  let hk := st.hooks.toList.mergeSort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
  IO.println s!"hooks: {", ".intercalate (hk.map fun (h, n) => s!"{h} {n}")}"
  return if st.bad == 0 && st.checkAgree == st.checked && st.selected > 0 then 0 else 1

end GoFVTest.MachDiff

def main (args : List String) : IO UInt32 := GoFVTest.MachDiff.main args
