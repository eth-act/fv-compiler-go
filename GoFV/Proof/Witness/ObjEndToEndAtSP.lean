import GoFV.Proof.Obj.EndToEndAtSP
import GoFV.Proof.Witness.GenG49Mach
import GoFV.Proof.Witness.ObjEndToEnd

/-!
# Non-vacuity witness: generic SSA to machine words at the machine layout (`verified_mach_atSP`)

`runtime.secret_getStack`'s ABI0 wrapper (`GenG49Mach`: `std/std/runtime/secret_getStack,0.ssa`
and `.prog` of quick-v10), which calls `runtime/secret.getStack` (ABIInternal, results in `R0`,
`R1`) and stores the two results into its stack results `~r0`, `~r1` (`Blk.local` blocks 3 and 4
of activation 0, `NAME_PARAM` 0 and 8): its generic SSA input (the export's first section, in the
pass environment `gofv-ssa-opt --verified` builds, `ObjEndToEnd.baseEnv`) goes through
`verifiedPipelineFull` (`fullyVerified`) to the allocated function. At `Addrs.fixed` no activation
of it is a `G49Env` (`fixedNone`, by `g49Env_fixed_apart`): `verified_mach` holds of it there only
vacuously. `verified_mach_atSP` applies with every premise discharged:

* the Progs are the stock `.prog` file's (`pf.prog0`, the Progs genssa's port reproduces; P0' is
  the identity: no float constant), numbered by the assembler's `flush` (`g`: `GenG49Mach.g` with
  the `flush` symbol table), so that `checkG60` (`refsLive`, `checkG60L` on `liveCtx` of the
  pipeline's output), `retRegsOK`, `entryStoresOK` (no pending window) and `checkObj` (the port's
  words, 16-byte frame, no stack check) accept the same list; every symbol at `symS = 0x8000`,
  within `CALL`'s range of the code at `ObjG7.base`;
* the environment `env` is the Phase 1 test environment `plRunEnv` with `runtime/secret.getStack`
  returning `0x11` and `0x22` and the memory unchanged (`getStackC`); its `VPre` facts hold at the
  machine layout `AM = Addrs.atSP (baseSP g L sp0)` (`env_vpre`); the generic `run` returns
  `[0x11, 0x22]`;
* the machine: the hook `H` returns to `X30` with `X0 = 0x11`, `X1 = 0x22` and everything else
  kept (`HookMap`: `hookMap_H`; the callee contract `CallSpec` at every `LocMatch`ed state of an
  activation extending `envAtSP g L (E0 lc)`: `callSpecH`, whose `AddrAgree` holds since `ιSP`
  places every block with a base, `addrAgree_ext`); the caller enters at `ObjG7.base` with
  `SP = 0x7fff0010`, `LR = 0x40`, `g = 0x9000` and a zero memory (`MachEntry`, `EntryEnv`);
  `E0 lc` is a `G28Env` at `Addrs.fixed` (`g28Env`), and the run's first state `sI` (after the
  entry values `SP`, `InitMem`) is `EntryMatch`ed under `envAtSP`, whose `ιSP` puts the results'
  blocks at `SP + 24` and `SP + 32` (`memInjI`); `RunPre` holds with the call's contracts at
  `sI`, the only state the run reaches before the call (`lreach_start`), every other op simple
  (`runPreH`).

`verified_mach_atSP` then gives the `runLoc` refinement and a `runMach` of the linked words that
returns to the caller's `0x40` (`MachRet`, `ResultRel`); the body returns the memory `memF`
(`runLoopLoc_mono`), whose injection into the returned machine memory puts the 64-bit words
`0x11` and `0x22` at the caller's `SP + 8` and `SP + 16` (`resultWord`). By compiled evaluation (`native_decide`,
listed in `scripts/axioms-allowlist.txt`; `obj_facts`, `e2e_facts`): the export parses, the
pipeline is `fullyVerified`, the validators accept, the run returns, and the states and tables
are as stated.
-/

namespace GoFV.Proof.Witness.ObjEndToEndAtSP

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Verified GoFV.Gen.Check GoFV.Arm64 GoFV.Asm
open GoFV.Asm.CheckObj
open GoFV.Proof.Gen GoFV.Proof.Obj GoFV.Proof.Pipeline GoFV.Proof.PipelineFull
open GoFV.Proof (OutcomeRefines enterListLoc)
open GoFV.Proof.Witness (plRunEnv plRunEnv_mono plRunEnv_frameSafe plRunEnv_allocNonNil
  plRunEnv_wbPre plRunEnv_tempOblivious plRunEnv_keeps plRunEnv_allocZero plRunEnv_growLen
  plRunEnv_initAvoids withWbHelpers noActB noArgPtrB noNilPtrB)
open GoFV.Proof.Witness.ObjFrame (isOk getOk eq_getOk)
open GoFV.Proof.Witness.ObjEndToEnd (baseEnv padTables isRetG)
open GoFV.Proof.Witness.ObjWhole (isPoison gAddr1 gAddr2)

/-! ## The generic input -/

/-- The parsed export of the wrapper. -/
def exIn : Except String (ExportFile × ExportExt) := parseExportExt GenG49Mach.fSsa.toUTF8

def file : ExportFile :=
  match exIn with
  | .ok x => x.1
  | .error _ => default

def ext : ExportExt :=
  match exIn with
  | .ok x => x.2
  | .error _ => default

/-- The first section: the input of `number lines`. -/
def sec0 : Section := (file.sections[0]?).getD default

def penv : PassEnv := baseEnv file (padTables (({} : Tables).addAll sec0.defs) file.frontendTables)

/-- The generic SSA input. -/
def f0 : Func := sec0.func

def dcl : Nat := (ext.dclLen? 0).getD 0

/-! ## The callee -/

/-- The results of `runtime/secret.getStack`. -/
def r0 : BitVec 64 := 0x11
def r1 : BitVec 64 := 0x22

/-- `runtime/secret.getStack`: returns `0x11` and `0x22`, the memory unchanged. -/
def getStackC : Contract := fun _ _ m => .returned [.i64 r0, .i64 r1] m

/-- `plRunEnv` with `runtime/secret.getStack`. -/
def env : Env :=
  { plRunEnv with
    extern := fun n => if n = "runtime/secret.getStack" then some getStackC else plRunEnv.extern n }

/-- The machine after the callee: back at `X30` with `X0 = 0x11`, `X1 = 0x22`. -/
def hkS (s : MState) : MState :=
  { s with pc := s.x 30, x := fun k => if k = 0 then r0 else if k = 1 then r1 else s.x k }

/-- The callee hook: `hkS` at every call. -/
def H : Hooks := ⟨fun s => some (.ret (hkS s))⟩

/-! ## The Progs and the assembled words -/

/-- The stock `.prog` file. -/
def pf : ProgFile :=
  match parseProgFile GenG49Mach.fProg.toUTF8 with
  | .ok x => x
  | .error _ => default

/-- Its P0 Progs, numbered by the assembler. -/
def ps : Array Prog := pf.prog0.progs

/-- `checkG60`'s input: `GenG49Mach.g` with the symbols numbered as the assembler's `flush`. -/
def g : G2In :=
  match flush pf with
  | .ok fo => { GenG49Mach.g with syms := fo.st.syms }
  | .error _ => GenG49Mach.g

def bs : ID → Option Nat := GenG49Mach.bs

def tab : PcTab := GenG49Mach.tab

def objIn : Except String (Array Spill × ObjIn) := ObjG7.objOf GenG49Mach.fProg

def spills : Array Spill :=
  match objIn with
  | .ok x => x.1
  | .error _ => #[]

def obj : ObjIn :=
  match objIn with
  | .ok x => x.2
  | .error _ => ⟨ByteArray.empty, #[], #[]⟩

/-- Where every symbol is linked: below the Progs, within `CALL`'s range of the code. -/
def symS : BitVec 64 := 0x8000

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, the 16-byte frame with 8 bytes of extra
space `checkObj` gives, every symbol at `symS`. -/
def L : Link := Link.byId (fun _ => symS) GenG2.text 16 8 ps.toList

/-- What `checkObj` returns. -/
def otab : Tab := getOk (checkObj ps spills obj)

/-- The linked code. -/
def code : Code := getOk (linkCode ObjG7.base (fun _ => symS) obj.text obj.relocs.toList)

/-! ## The activation -/

def sp0 : BitVec 64 := 0x7fff0000

/-- `ι` at `Addrs.fixed`: the nil block at 0, `plRunEnv`'s globals at `gAddr1`, `gAddr2`, the
other globals at `symS`, every block with a fixed base at it. -/
def ιF : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global n =>
    if n = "main.g" then some gAddr1 else if n = "runtime.writeBarrier" then some gAddr2
    else some symS
  | b => (Blk.fixedBase? b).map (BitVec.ofNat 64)

/-- The activation of `runLoc`'s context `lc`: framed, `SP = 0x7fff0000` in the body, `g =
0x9000`, the caller's `LR = 0x40` and `FP = SP + 8`. -/
def E0 (lc : LocCtx) : MatchEnv :=
  { lc, ι := ιF, sp := sp0, slot := fun _ => none, g := 0x9000, lr := 0x40, fp := sp0 + 8,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The machine at the function's entry: `SP = 0x7fff0010`, `R29 = SP - 8`, `LR = 0x40`, a zero
memory. -/
def s0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then sp0 + 8 else if k = 30 then 0x40
      else 0,
    sp := sp0 + 16, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩, pc := ObjG7.base,
    mem := fun _ => 0 }

/-- The machine layout: activation 0's `local` blocks at their frame operands from `sp0`. -/
abbrev AM : Addrs := Addrs.atSP (baseSP g L sp0)

/-- The injection of `envAtSP g L (E0 lc)`. -/
abbrev ιM : Blk → Option (BitVec 64) := ιSP g L sp0 ιF

/-- The frame memory of `runLoc`'s first state: `plRunEnv`'s globals, the outgoing-arguments
area (24 bytes), the two results. -/
def memI : Mem :=
  { blocks := #[(.global "main.g", { data := Array.replicate 8 (.b 0) }),
      (.global "runtime.writeBarrier", { data := Array.replicate 4 (.b 0), writable := false }),
      (.outargs 0, { data := Array.replicate 24 .poison }),
      (.local 0 3, { data := Array.replicate 8 .poison }),
      (.local 0 4, { data := Array.replicate 8 .poison })] }

/-- The memory at the return: `memI` with the results `0x11` and `0x22` stored. -/
def memF : Mem :=
  { blocks := #[(.global "main.g", { data := Array.replicate 8 (.b 0) }),
      (.global "runtime.writeBarrier", { data := Array.replicate 4 (.b 0), writable := false }),
      (.outargs 0, { data := Array.replicate 24 .poison }),
      (.local 0 3, { data := #[.b 0x11, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] }),
      (.local 0 4, { data := #[.b 0x22, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] })] }

/-! ## Checks -/

/-- Block `b1` of `lc`. -/
def blkOf (lc : LocCtx) : Block := (lc.ctx.f.block? 1).getD default

/-- The call `v7` of `lc`. -/
def v7Of (lc : LocCtx) : Value := (lc.ctx.f.value? 7).getD default

/-- The tables `checkG60L` gives on `lc`. -/
def ktOf (lc : LocCtx) : KTab := (getOk (checkG60L lc ps bs g)).2

def isInt64 : Val → Bool
  | .int .w64 _ => true
  | _ => false

/-- `SP` (register 30) holds a 64-bit integer, every other register `poison`; no flags, no slot,
the frame memory. -/
def sIIs (s : LocState) : Bool :=
  (List.range s.regs.size).all (fun r =>
      match s.regs[r]? with
      | some v => if r = 30 then isInt64 v else isPoison v
      | none => true) &&
    isPoison s.flags && s.slots.isEmpty &&
    match s.mem with
    | .mem m => decide (m = memI)
    | _ => false

/-- The register holds the 64-bit integer `x`. -/
def isI64 (x : BitVec 64) : Option Val → Bool
  | some (.int .w64 y) => y == x
  | _ => false

theorem isI64_spec {x : BitVec 64} {o : Option Val} (h : isI64 x o = true) :
    o = some (.int .w64 x) := by
  unfold isI64 at h
  split at h
  · simp only [beq_iff_eq] at h
    subst h
    rfl
  · cases h

/-- After the call: `R0 = 0x11`, `R1 = 0x22`, the frame memory. -/
def sCallIs (s : LocState) : Bool :=
  isI64 r0 s.regs[0]? && isI64 r1 s.regs[1]? &&
    match s.mem with
    | .mem m => decide (m = memI)
    | _ => false

/-- The call `v` has no register argument and its results in `R0`, `R1`, by `callRegs` and by
`callRegsZ`. -/
def callFacts (lc : LocCtx) (v : Value) : Bool :=
  match callOf? lc.ctx.tabs v.aux with
  | some (_, _, c) =>
    (callRegs c).toOption == some ([], [0, 1]) &&
      (callRegsZ lc.ctx.tabs c).toOption == some ([], [0, 1])
  | none => false

/-- No symbol of the wrapper is one of `plRunEnv`'s globals. -/
def symsOut : Bool :=
  g.syms.all fun x => x.1.toStringLossy != "main.g" && x.1.toStringLossy != "runtime.writeBarrier"

/-- What compiled evaluation checks of the machine side and the layout: `checkObj` accepts with
the 16-byte frame (8 bytes of extra space) and no stack check, the code links, `0x40` and `symS`
have no code and are no P0 address nor `endP`, the Prog IDs are below `2^32`, no `CALL (Rn)`, the
P0 address of the entry's value 2 maps to the body's start, `memI`'s keys are distinct, the
results' operands are `NAME_PARAM` 0 and 8 at `SP + 24` and `SP + 32`. -/
def objFacts : Bool :=
  isOk (checkObj ps spills obj) && otab.autosize == 16 && otab.extrasize == 8 &&
    otab.check.isNone && isOk (linkCode ObjG7.base (fun _ => symS) obj.text obj.relocs.toList) &&
    decide (obj.text.size ≤ 2 ^ 64) && code 0x40 == none && code symS == none &&
    ps.toList.all (fun p => addrP GenG2.text p.id != symS && addrP GenG2.text p.id != 0x40 &&
      decide (p.id < 2 ^ 32)) &&
    symS != endP GenG2.text ps.toList && (0x40 : BitVec 64) != endP GenG2.text ps.toList &&
    ObjEnv.map otab ps L ObjG7.base (pcOfTab GenG2.text ps.toList tab 1 2) ==
      ObjG7.base + BitVec.ofNat 64 (otab.offs[0]!) &&
    ObjG7.noICall ps && decide ((memI.blocks.toList.map (·.1)).Nodup) && symsOut &&
    varOp g 3 == some (.PARAM, 0) && varOp g 4 == some (.PARAM, 8) &&
    frameOff L .PARAM 0 == 24 && frameOff L .PARAM 8 == 32

theorem obj_facts : objFacts = true := by
  native_decide

/-- What compiled evaluation checks of a `runLoc` context `lc` with no instance: `checkG60L`
accepts the Progs with `tab`, `retRegsOK` the return (no register result), the accessed frame
variables are the results (aux 4 and 3, `Blk.local`), no home slot; the entry `b1`
has nine values, the third the static call `v7` (`callFacts`); `R30` has class 64 after the entry
values, no upper-bit fact is carried; simple ops after the call (`simpleFrom`); `entryStoresOK`
holds with no pending window; `memTyL`. -/
def lcFactsC (lc : LocCtx) : Bool :=
  isOk (checkG60L lc ps bs g) && (getOk (checkG60L lc ps bs g)).1 == tab &&
    retRegsOK lc (ktOf lc) && ownOutRegs lc == [] &&
    accessedVars lc == [4, 3] && lc.ctx.tabs.forgeable 3 && lc.ctx.tabs.forgeable 4 &&
    (homeSlots lc).isEmpty && lc.ctx.f.entry == 1 && lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (blkOf lc).values.size == 9 && (blkOf lc).values[2]? == some 7 &&
    (lc.ctx.f.value? 7).isSome && (v7Of lc).op == .ARM64CALLstatic && callFacts lc (v7Of lc) &&
    (kAt lc (ktOf lc) 1 (blkOf lc) 2).get 30 == some 64 && simpleFrom lc.ctx.f 1 3 &&
    (uL35 lc [] (blkOf lc) 2).isEmpty && entryStoresOK lc g 2 && (pendWins lc g).isEmpty &&
    memTyL lc && (constRo (symNames g)).isEmpty

/-! ## At `Addrs.fixed`: the activation without the variables' places -/

section Fixed

open scoped GoFV.SSA.Sem.Fixed

theorem addrAgreeF : AddrAgree ιF := by
  intro b n a hb ha _
  have hb' : Blk.fixedBase? b = some n := hb
  cases b with
  | nil =>
    simp only [ιF, Option.some.injEq] at ha
    simp only [Blk.fixedBase?, Option.some.injEq] at hb'
    subst ha hb'
    rfl
  | global s => simp [Blk.fixedBase?] at hb'
  | wbuf => simp [Blk.fixedBase?] at hb'
  | heap k =>
    simp only [ιF, hb', Option.map_some, Option.some.injEq] at ha
    exact ha.symm
  | «local» a k =>
    simp only [ιF, hb', Option.map_some, Option.some.injEq] at ha
    exact ha.symm
  | temp a k =>
    simp only [ιF, hb', Option.map_some, Option.some.injEq] at ha
    exact ha.symm
  | outargs a =>
    simp only [ιF, hb', Option.map_some, Option.some.injEq] at ha
    exact ha.symm

theorem prog_addr_ne {qs : List Prog} {az ez : Int} {p : Prog} (hid : p.id < 2 ^ 32)
    (hp : p ∈ qs) {a : BitVec 64}
    (ha : a.toNat < 0x10000 ∨ 0x10000 + 4 * 2 ^ 32 ≤ a.toNat) (ha' : a.toNat < 2 ^ 64) :
    (Link.byId (fun _ => symS) GenG2.text az ez qs).addr p.id ≠ some a := by
  intro h
  rw [addr_byId hp] at h
  have := congrArg BitVec.toNat (Option.some.inj h)
  simp [GenG2.text, BitVec.toNat_add] at this
  omega

/-- `E0 lc` is an activation of the wrapper at `Addrs.fixed` without the variables' places
(`G28Env`), with the return address `endP`. -/
theorem g28Env {lc : LocCtx} (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32)
    (hav : accessedVars lc = [4, 3]) (hf3 : lc.ctx.tabs.forgeable 3 = true)
    (hf4 : lc.ctx.tabs.forgeable 4 = true) (hsl : (homeSlots lc).isEmpty = true)
    (hso : symsOut = true) (hend : symS ≠ endP GenG2.text ps.toList) :
    G28Env lc g L ps (endP L.text ps.toList) tab (E0 lc) := by
  have h2 : G2Env lc g L ps 0 tab (E0 lc) :=
    { lcEq := rfl
      link := rfl
      pcOf := rfl
      retOut := fun p hp => prog_addr_ne (hlt p hp) hp (by simp) (by simp)
      addr := addrAgreeF
      glob := fun y name abi hy => by
        have h := (Array.all_eq_true_iff_forall_mem.1 hso) _ (Array.mem_of_getElem? hy)
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
        simp only [E0, ιF, h.1, h.2, ↓reduceIte]
        rfl
      syms := by
        intro y
        have hs : L.sym y = symS := rfl
        rw [hs]
        refine ⟨by decide, fun p hp => ?_⟩
        exact prog_addr_ne (hlt p hp) hp (Or.inl (by decide)) (by decide)
      calls := fun h => by cases h
      slot := fun k hk => by simp [List.isEmpty_iff.1 hsl] at hk
      extra := by show 0 ≤ (8 : Int); decide
      frame := ⟨by show 4096 + 8 ≤ sp0.toNat; decide,
        by show sp0.toNat + 8 ≤ 2 ^ 64; decide, fun k off h => by cases h⟩ }
  exact
    { env :=
      { env :=
        { env :=
          { env := ObjG7.g2Env_endP h2 (ObjG7.retOut_endP hlt) (fun _ => hend)
            vars := by
              intro x hx o _ hf
              rw [hav] at hx
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl
              · rw [hf4] at hf; cases hf
              · rw [hf3] at hf; cases hf }
          wbs := fun h => by cases h }
        icalls := fun h => by cases h }
      memeqs := fun h => by cases h }

/-- At `Addrs.fixed`, no activation of the wrapper is a `G49Env`: its results' `local` blocks
would sit 8 bytes apart, `Blk.fixedBase?` puts them `2^24` apart. -/
theorem fixedNone {lc : LocCtx} (hav : accessedVars lc = [4, 3])
    (h3 : varOp g 3 = some (.PARAM, 0)) (h4 : varOp g 4 = some (.PARAM, 8))
    (hf3 : lc.ctx.tabs.forgeable 3 = true) (hf4 : lc.ctx.tabs.forgeable 4 = true)
    (L' : Link) (ps' : Array Prog) (ret : BitVec 64) (tab' : PcTab) (E' : MatchEnv) :
    ¬ G49Env lc g L' ps' ret tab' E' := by
  intro hE
  refine g49Env_fixed_apart hE (x := 4) (y := 3) (by simp [hav]) (by simp [hav]) h4 h3
    (.inr rfl) (.inr rfl) hf4 hf3 ?_
  simp only [frameOff]
  omega

end Fixed

/-! ## At the machine layout -/

section AtSP

attribute [local instance] AM

/-- The outcome returns no register result with the memory `memF`. -/
def isRetF : Outcome → Bool
  | .returned [] m => decide (m = memF)
  | _ => false

theorem isRetF_spec {o : Outcome} (h : isRetF o = true) : o = .returned [] memF := by
  unfold isRetF at h
  split at h
  · simp only [decide_eq_true_eq] at h
    subst h
    rfl
  · cases h

/-- What compiled evaluation checks of `runLoc` on `lc` at the machine layout: the entry values
run from `runLoc`'s first state (no argument, the empty memory) to `sI` (`sIIs`), and the call
`v7` from `sI` to `R0 = 0x11`, `R1 = 0x22` and the frame memory (`sCallIs`); the body returns
`memF` (`isRetF`). -/
def lcFactsR (lc : LocCtx) : Bool :=
  GenG1.okThen (enterListLoc env lc (locInit env lc [] {}) ((blkOf lc).values.toList.take 2))
    (fun sI => sIIs sI && GenG1.okThen (stepLoc env lc sI (v7Of lc)) sCallIs) &&
    isRetF (runLoopLoc env lc 10 (locInit env lc [] {}) lc.ctx.f.entry)

/-- The outcome returns `[0x11, 0x22]`. -/
def isRet2 : Outcome → Bool
  | .returned [.int .w64 a, .int .w64 b] _ => a == r0 && b == r1
  | _ => false

theorem isRet2_spec {o : Outcome} (h : isRet2 o = true) :
    ∃ m, o = .returned [.i64 r0, .i64 r1] m := by
  unfold isRet2 at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, rfl⟩
  · cases h

def isOOF : Outcome → Bool
  | .outOfFuel => true
  | _ => false

theorem isOOF_spec {o : Outcome} (h : isOOF o = true) : o = .outOfFuel := by
  unfold isOOF at h
  split at h
  · rfl
  · cases h

/-- `runLF` and `runL` of `f` run alike on no argument and the empty memory: out of fuel with none,
returning the same two integers and memory with one unit. -/
def sameRun (tabs : Tables) (f : Func) : Bool :=
  isOOF (GoFV.Proof.runLF env tabs f [] {} 0) && isOOF (runL env tabs f [] {} 0) &&
    match GoFV.Proof.runLF env tabs f [] {} 1, runL env tabs f [] {} 1 with
    | .returned [.int .w64 a, .int .w64 b] m, .returned [.int .w64 a', .int .w64 b'] m' =>
      a == a' && b == b' && decide (m = m')
    | _, _ => false

/-- `sameRun` gives `NoNilFault` (`runLF_mono`, `runL_mono`). -/
theorem sameRun_spec {tabs : Tables} {f : Func} (h : sameRun tabs f = true) :
    GoFV.Proof.NoNilFault tabs f env [] {} := by
  simp only [sameRun, Bool.and_eq_true] at h
  obtain ⟨⟨h0F, h0L⟩, h1⟩ := h
  have e1 : GoFV.Proof.runLF env tabs f [] {} 1 = runL env tabs f [] {} 1 ∧
      (runL env tabs f [] {} 1).Defined := by
    split at h1
    · rename_i a b m a' b' m' hF hL
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h1
      rw [hF, hL]
      exact ⟨rfl, trivial⟩
    · cases h1
  intro fuel
  cases fuel with
  | zero => rw [isOOF_spec h0F, isOOF_spec h0L]
  | succ n =>
    rw [GoFV.Proof.runLF_mono (by omega : 1 ≤ n + 1) (e1.1 ▸ e1.2),
      GoFV.Proof.runL_mono (by omega : 1 ≤ n + 1) e1.2, e1.1]

/-- What compiled evaluation checks: the export parses, the pipeline is `fullyVerified` with
`schedule` inputs that run as `runL` (`sameRun`), free of pointer-shaped parameter pieces and
checked pointers,
`refsLive` holds of its output and `lcFactsC`, `lcFactsR` of `liveCtx` of it, the generic `run`
returns `[0x11, 0x22]`, and the input has no dictionary parameter and no read-only symbol. -/
def e2eFacts : Bool :=
  ((verifiedPipelineFull penv f0 0 sec0.zvar dcl).toOption.map fun r =>
      r.fullyVerified &&
        r.nnf.all (fun x => sameRun x.1 x.2 && noArgPtrB x.1 x.2 && noNilPtrB x.1 x.2) &&
        refsLive (LocCtx.make r.st.tables r.st.func) &&
        lcFactsC (liveCtx (LocCtx.make r.st.tables r.st.func)) &&
        lcFactsR (liveCtx (LocCtx.make r.st.tables r.st.func))) == some true &&
    isRet2 (GoFV.SSA.run env penv.tables f0 [] {} 5) &&
    (NilCheck.dictParams penv.tables f0).isEmpty && (pipelineRo penv f0).isEmpty

theorem e2e_facts : e2eFacts = true := by
  native_decide

/-! ## The injection -/

/-- `ιM` places every block but the write-barrier buffer. -/
theorem ιM_total (b : Blk) (hb : b ≠ .wbuf) : ∃ a, ιM b = some a := by
  cases b with
  | «local» a k =>
    simp only [ιM, ιSP]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  | wbuf => exact absurd rfl hb
  | global n =>
    simp only [ιM, ιSP, ιF]
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  | nil => exact ⟨_, rfl⟩
  | heap _ => exact ⟨_, rfl⟩
  | temp _ _ => exact ⟨_, rfl⟩
  | outargs _ => exact ⟨_, rfl⟩

theorem addrAgreeM : AddrAgree ιM := addrAgree_atSP addrAgreeF

/-- Every activation extending `envAtSP g L (E0 lc)` meets `AddrAgree`: `ιM` already places every
block with a base. -/
theorem addrAgree_ext {lc : LocCtx} {E : MatchEnv} (hx : (envAtSP g L (E0 lc)).Extends E) :
    AddrAgree E.ι := by
  intro b n a hb ha hnt
  have hw : b ≠ .wbuf := by
    rintro rfl
    have h : baseM (baseSP g L sp0) Blk.wbuf = some n := hb
    simp [baseM, Blk.fixedBase?] at h
  obtain ⟨a0, h0⟩ := ιM_total b hw
  have h1 := hx.2 b a0 h0
  rw [h1] at ha
  rw [← Option.some.inj ha]
  exact addrAgreeM b n a0 hb h0 hnt

theorem ιM_l3 (h3 : varOp g 3 = some (.PARAM, 0)) (ho : frameOff L .PARAM 0 = 24) :
    ιM (.local 0 3) = some (sp0 + BitVec.ofInt 64 24) := by
  show ιSP g L sp0 ιF (.local 0 3) = _
  rw [ιSP_local0 h3, ho]

theorem ιM_l4 (h4 : varOp g 4 = some (.PARAM, 8)) (ho : frameOff L .PARAM 8 = 32) :
    ιM (.local 0 4) = some (sp0 + BitVec.ofInt 64 32) := by
  show ιSP g L sp0 ιF (.local 0 4) = _
  rw [ιSP_local0 h4, ho]

/-- `memI` injected into the zero memory: the globals at `gAddr1`, `gAddr2`, the
outgoing-arguments area at `2^62`, the results at `SP + 24` and `SP + 32`. -/
theorem memInjI (hm3 : ιM (.local 0 3) = some (sp0 + BitVec.ofInt 64 24))
    (hm4 : ιM (.local 0 4) = some (sp0 + BitVec.ofInt 64 32)) :
    MemInj ιM memI (fun _ => 0) where
  nil := rfl
  mapped := by
    intro b al h
    simp only [memI, List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, rfl, fun _ => by decide, by decide⟩
    · exact ⟨_, rfl, fun _ => by decide, by decide⟩
    · exact ⟨_, rfl, fun _ => by decide, by decide⟩
    · exact ⟨_, hm3, fun _ => by decide, by decide⟩
    · exact ⟨_, hm4, fun _ => by decide, by decide⟩
  inj := by
    intro b al b' al' a a' h h' hne ha ha'
    simp only [memI, List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h h'
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (try rw [hm3] at ha) <;> (try rw [hm4] at ha) <;> (try rw [hm3] at ha') <;>
    (try rw [hm4] at ha') <;>
    first | exact absurd rfl hne | (cases ha; cases ha'; decide)
  bytes := by
    refine ⟨fun _ _ => False, ?_⟩
    intro b al a h ha
    simp only [memI, List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h
    refine ⟨fun _ h => h.elim, fun _ _ h => h.elim, fun i hi _ => ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [Array.getElem_replicate, ByteRel]

/-- `memI`'s keys are distinct and its blocks lie apart from the saved `LR`/`FP` words. -/
theorem sepI {lc : LocCtx} (hk : (memI.blocks.toList.map (·.1)).Nodup)
    (hm3 : ιM (.local 0 3) = some (sp0 + BitVec.ofInt 64 24))
    (hm4 : ιM (.local 0 4) = some (sp0 + BitVec.ofInt 64 32)) :
    KeysNodup memI ∧ SepFrom ιM (StkAt (envAtSP g L (E0 lc))) memI := by
  refine ⟨hk, fun b al a h ha y hy => ?_⟩
  rcases hy with ⟨-, h1, h2⟩ | ⟨k, off, h, -⟩
  · have e1 : (envAtSP g L (E0 lc)).sp.toNat = 0x7fff0000 := rfl
    rw [e1] at h1 h2
    simp only [memI, List.mem_toArray, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
      or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (try rw [hm3] at ha) <;> (try rw [hm4] at ha) <;> cases ha <;>
    · rintro ⟨h3, h4⟩
      simp [sp0, gAddr1, gAddr2] at h3 h4
      omega
  · cases h

/-! ## The checks as propositions -/

theorem sIIs_spec {s : LocState} (h : sIIs s = true) :
    (∀ r v, s.regs[r]? = some v → (r = 30 → ∃ x, v = .int .w64 x) ∧ (r ≠ 30 → v = .poison)) ∧
      s.flags = .poison ∧ s.slots = [] ∧ s.mem = .mem memI := by
  simp only [sIIs, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.isEmpty_iff] at h
  obtain ⟨⟨⟨hr, hf⟩, hs⟩, hm⟩ := h
  refine ⟨fun r v hv => ?_, ?_, hs, ?_⟩
  · have hlt := (Array.getElem?_eq_some_iff.1 hv).1
    have := hr r hlt
    rw [hv] at this
    constructor
    · rintro rfl
      simp only [↓reduceIte, isInt64] at this
      split at this
      · exact ⟨_, rfl⟩
      · cases this
    · intro h0
      simp only [h0, ↓reduceIte, isPoison] at this
      split at this
      · rfl
      · cases this
  · unfold isPoison at hf
    split at hf
    · assumption
    · cases hf
  · split at hm
    · simp only [decide_eq_true_eq] at hm
      subst hm; assumption
    · cases hm

theorem sCallIs_spec {s : LocState} (h : sCallIs s = true) :
    s.regs[0]? = some (.int .w64 r0) ∧ s.regs[1]? = some (.int .w64 r1) ∧ s.mem = .mem memI := by
  simp only [sCallIs, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1⟩, hm⟩ := h
  refine ⟨isI64_spec h0, isI64_spec h1, ?_⟩
  split at hm
  · simp only [decide_eq_true_eq] at hm
    subst hm; assumption
  · cases hm

/-- The checks of `lcFactsC` as propositions. -/
theorem lcC_spec {lc : LocCtx} (h : lcFactsC lc = true) :
    checkG60L lc ps bs g = .ok (tab, ktOf lc) ∧ retRegsOK lc (ktOf lc) = true ∧
    ownOutRegs lc = [] ∧ accessedVars lc = [4, 3] ∧ lc.ctx.tabs.forgeable 3 = true ∧
    lc.ctx.tabs.forgeable 4 = true ∧ (homeSlots lc).isEmpty = true ∧ lc.ctx.f.entry = 1 ∧
    1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some (blkOf lc) ∧
    (blkOf lc).values.size = 9 ∧ (blkOf lc).values[2]? = some 7 ∧
    lc.ctx.f.value? 7 = some (v7Of lc) ∧ (v7Of lc).op = .ARM64CALLstatic ∧
    callFacts lc (v7Of lc) = true ∧ (kAt lc (ktOf lc) 1 (blkOf lc) 2).get 30 = some 64 ∧
    simpleFrom lc.ctx.f 1 3 = true ∧ uL35 lc [] (blkOf lc) 2 = [] ∧
    entryStoresOK lc g 2 = true ∧ pendWins lc g = [] ∧ memTyL lc = true ∧
    constRo (symNames g) = [] := by
  simp only [lcFactsC, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23⟩ := h
  have hc : checkG60L lc ps bs g = .ok (tab, ktOf lc) := by
    rw [← h2]
    exact eq_getOk h1
  have hb : lc.ctx.f.block? 1 = some (blkOf lc) := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h11
    simp [blkOf, hb]
  have hv : lc.ctx.f.value? 7 = some (v7Of lc) := by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h14
    simp [v7Of, hv]
  exact ⟨hc, h3, h4, h5, h6, h7, h8, h9, h10, hb, h12, h13, hv, h15, h16, h17, h18,
    List.isEmpty_iff.1 h19, h20, List.isEmpty_iff.1 h21, h22, List.isEmpty_iff.1 h23⟩

/-! ## The callee -/

/-- **The callee contract of `H`**: from any state at the callee, it returns to `X30` with the
results in `X0`, `X1` and nothing else changed; the memory `mm` stays injected by `E.ι`. -/
theorem callSpecH {E : MatchEnv} (hA : AddrAgree E.ι) {ins outs : List Nat} {args : List Val}
    {mm : Mem} {s' : LocState} {m₁ : MState} (hout : outs = [0, 1])
    (h0 : s'.regs[0]? = some (.int .w64 r0)) (h1 : s'.regs[1]? = some (.int .w64 r1))
    (hm : s'.mem = .mem mm) : CallSpec H E ins outs args mm s' m₁ := by
  intro _ _ hinj hk hsep
  refine ⟨E.ι, hkS m₁, mm, rfl, fun _ _ h => h, hA, rfl, rfl, rfl, rfl, fun _ _ => rfl, hm,
    hinj, hk, hsep, ?_⟩
  subst hout
  intro r hr x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h0] at hx
    cases hx
    refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
    simp only [objX?] at hk
    cases hk
    exact Or.inl rfl
  · rw [h1] at hx
    cases hx
    refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
    simp only [objX?] at hk
    cases hk
    exact Or.inl rfl

/-- The callee contracts `CallOK` and `CallOKZ` of `H` at the call `v`, from a state with the
frame memory to one with the results in `R0`, `R1` and the frame memory. -/
theorem callOKH {lc : LocCtx} {E : MatchEnv} {s s' : LocState} {v : Value} {m : MState}
    (hA : AddrAgree E.ι) (hcf : callFacts lc v = true) (hsm : s.mem = .mem memI)
    (h0 : s'.regs[0]? = some (.int .w64 r0)) (h1 : s'.regs[1]? = some (.int .w64 r1))
    (hm : s'.mem = .mem memI) :
    CallOK H E g L lc s s' v m ∧ CallOKZ H E g L lc s s' v m := by
  unfold callFacts at hcf
  split at hcf
  · rename_i n a c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hcf
    refine ⟨?_, ?_⟩
    · intro _ name abi cabi ins outs y args mm m₁ hc' hcr _ _ _ hs _ _ _ _ _ _
      rw [hc] at hc'
      cases hc'
      rw [hcr] at hcf
      have hout : outs = [0, 1] := by
        have := hcf.1
        simp only [Except.toOption, Option.some.injEq, Prod.mk.injEq] at this
        exact this.2
      rw [hsm] at hs
      cases hs
      exact callSpecH hA hout h0 h1 hm
    · intro _ name abi cabi ins outs hc' hcr y args mm m₁ _ _ _ hs _ _ _ _ _ _
      rw [hc] at hc'
      cases hc'
      rw [hcr] at hcf
      have hout : outs = [0, 1] := by
        have := hcf.2
        simp only [Except.toOption, Option.some.injEq, Prod.mk.injEq] at this
        exact this.2
      rw [hsm] at hs
      cases hs
      exact callSpecH hA hout h0 h1 hm
  · cases hcf

/-- `H` treats related states alike (`HookMap`). -/
theorem hookMap_H {L' : Link} {ps' : List Prog} {f : BitVec 64 → BitVec 64} :
    HookMap H L' ps' f := by
  intro s t s' hR _ hx hc
  simp only [H, Option.some.injEq, HookOut.ret.injEq] at hc
  subst hc
  refine ⟨hkS t, rfl, ?_, hx⟩
  exact
    { x := fun k h27 h30 => by
        simp only [hkS]
        by_cases h0 : k = 0
        · simp [h0]
        · by_cases h1 : k = 1
          · simp [h1]
          · simp only [h0, h1, ↓reduceIte]
            exact hR.x k h27 h30
      x30 := hR.x30
      sp := hR.sp
      v := hR.v
      nzcv := hR.nzcv
      mem := hR.mem
      pc := hR.x30 }

/-! ## The run's premises -/

theorem g54Pre_call {lc : LocCtx} {s : LocState} {v : Value} (hop : v.op = .ARM64CALLstatic) :
    G54Pre lc s v := by
  have hne : ∀ o : Op, o ≠ .ARM64CALLstatic → v.op ≠ o := fun o h h' => h (h'.symm.trans hop)
  have h46 : G46Pre lc s v := by
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩
    · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
    · intro _ _ _ hl; rw [hop] at hl; cases hl
    · intro h; exact absurd h (hne _ (by decide))
    · intro h; exact absurd h (hne _ (by decide))
    · intro h; exact absurd h (hne _ (by decide))
    · intro h; exact absurd h (hne _ (by decide))
    · intro _ _ _ _ hl; rw [hop] at hl; cases hl
    · intro _ _ hl; rw [hop] at hl; cases hl
    · intro h; rcases h with h | h | h <;> exact absurd h (hne _ (by decide))
    · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
    · intro _ _ hl; rw [hop] at hl; cases hl
    · intro _ _ _ hl; rw [hop] at hl; simp [fp2Of] at hl
    · intro _ _ _ _ hl; rw [hop] at hl; simp [fp3Of] at hl
  refine ⟨⟨⟨⟨h46, fun _ _ _ _ hp => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩, fun h => ?_⟩,
    fun h => ?_, fun h => ?_⟩
  · rw [hop] at hp; cases hp
  · rcases h with h | h <;> exact absurd h (hne _ (by decide))
  all_goals exact absurd h (hne _ (by decide))

/-- The blocks of a function `simpleFrom` accepts. -/
theorem simpleFrom_blk {f : Func} {b0 : ID} {i0 : Nat} (h : simpleFrom f b0 i0 = true) :
    ∀ b blk, f.block? b = some blk →
      blk.kind ≠ .ARM64Z ∧ blk.kind ≠ .ARM64NZ ∧ (∀ e ∈ blk.succs.toList, e.b ≠ b0) ∧
      ∀ i id v, blk.values[i]? = some id → f.value? id = some v →
        (b = b0 ∧ i < i0) ∨ simpleOp v.op = true := by
  have hall := List.all_eq_true.1 h
  intro b blk hb
  have hlt : b < f.blockTab.size := by
    have hb' : (f.blockTab[b]?).join = some blk := hb
    cases h' : f.blockTab[b]? with
    | none => rw [h'] at hb'; cases hb'
    | some _ => exact (Array.getElem?_eq_some_iff.1 h').1
  have := hall b (List.mem_range.2 hlt)
  rw [hb] at this
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Array.all_eq_true_iff_forall_mem,
    List.all_eq_true, List.mem_range] at this
  obtain ⟨⟨⟨hz, hnz⟩, hs⟩, hv⟩ := this
  refine ⟨hz, hnz, fun e he => by simpa using hs e (by simpa using he), ?_⟩
  intro i id v hi hval
  have hlt' : i < blk.values.size := (Array.getElem?_eq_some_iff.1 hi).1
  have := hv i hlt'
  rw [hi] at this
  simp only [Option.bind_some, hval, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  exact this

/-- A run from value `i0 > 0` of a block no edge enters is at its start state when back at
`(b0, i0)`. -/
theorem lreach_start {env' : Env} {lc : LocCtx} {b0 : ID} {i0 : Nat} {s0' : LocState}
    (hi0 : 0 < i0)
    (hno : ∀ b' blk', lc.ctx.f.block? b' = some blk' → ∀ e ∈ blk'.succs.toList, e.b ≠ b0)
    {b : ID} {i : Nat} {s : LocState} (h : LReach env' lc b0 i0 s0' b i s) :
    b = b0 → i = i0 → s = s0' := by
  induction h with
  | refl => intro _ _; rfl
  | val hr _ _ _ _ _ =>
    intro hb hi
    rcases lreach_cases hr with ⟨-, h⟩ | ⟨b', blk', e, hb', he, heb⟩
    · omega
    · exact absurd (heb.trans hb) (hno b' blk' hb' e he)
  | term _ _ _ _ => intro _ hi; omega

/-- **`RunPre` of the wrapper**: the call `v7` (value 2 of `b1`) at `sI`, the only state the run
reaches there, with the contracts `hcall`; every other value a simple op. -/
theorem runPreH {lc : LocCtx} {E0' : MatchEnv} {blk : Block} {sI : LocState} {v : Value}
    {ret : BitVec 64} (hsim : simpleFrom lc.ctx.f 1 3 = true) (hb : lc.ctx.f.block? 1 = some blk)
    (hi2 : blk.values[2]? = some 7) (hv : lc.ctx.f.value? 7 = some v)
    (hop : v.op = .ARM64CALLstatic)
    (hcall : ∀ s', stepLoc env lc sI v = .ok s' → ∀ E m, E0'.Extends E → LocMatch E sI 1 2 m →
      CallOK H E g L lc sI s' v m ∧ CallOKZ H E g L lc sI s' v m) :
    RunPre env H lc g L ret E0' 1 2 sI := by
  have hblk := simpleFrom_blk hsim
  have hno : ∀ b' blk', lc.ctx.f.block? b' = some blk' → ∀ e ∈ blk'.succs.toList, e.b ≠ 1 :=
    fun b' blk' h => (hblk b' blk' h).2.2.1
  intro b i s blk' hr hb'
  obtain ⟨hz, hnz, -, hv'⟩ := hblk b blk' hb'
  have hpos : b = 1 → 2 ≤ i := by
    rcases lreach_cases hr with ⟨-, h⟩ | ⟨b', blk'', e, hb'', he, rfl⟩
    · exact fun _ => h
    · exact fun h => absurd h (hno b' blk'' hb'' e he)
  refine ⟨fun id v' hi hval => ?_, fun _ hk => ?_⟩
  · rcases hv' i id v' hi hval with ⟨h1, h2⟩ | hs
    · have hi' : i = 2 := by have := hpos h1; omega
      subst h1 hi'
      have hsI := lreach_start (by decide) hno hr rfl rfl
      subst hsI
      rw [hb] at hb'
      cases hb'
      rw [hi2] at hi
      cases hi
      rw [hv] at hval
      cases hval
      refine ⟨.inl (by rw [hop]; rfl), fun s' hs => ⟨g54Pre_call hop, fun E m hx hm => ?_⟩⟩
      obtain ⟨hc, hcz⟩ := hcall s' hs E m hx hm
      refine ⟨hc, hcz, ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · intro n _ _ _ _ _ _ _ _ _ hn
        rw [hop] at hn
        cases hn
      all_goals rw [hop] at h; cases h
    · have hs' := hs
      simp only [simpleOp, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hs'
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hc⟩, hic⟩, hwb⟩, hcl⟩, hen⟩, -⟩,
        -⟩, hgg⟩, hme⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs'
      refine ⟨.inl (by simp [entryOp24, hen]), fun s' _ => ⟨g54Pre_simple hs s, fun E m _ _ =>
        ⟨fun h => absurd h hc, fun h => absurd h hc, ?_, fun h => absurd h hwb,
          fun h => absurd h hcl, fun h => absurd h hgg, fun h => absurd h hme⟩⟩⟩
      intro n _ _ _ _ _ _ _ _ _ hn
      rw [hic] at hn
      cases hn
  · rcases hk with hk | hk
    · exact absurd hk hz
    · exact absurd hk hnz

/-! ## The environment's `VPre` at the machine layout -/

theorem env_extern {name : String} {c : Contract} (h : env.extern name = some c) :
    (name = "runtime/secret.getStack" ∧ c = getStackC) ∨ plRunEnv.extern name = some c := by
  simp only [env] at h
  split at h
  · exact .inl ⟨‹_›, (Option.some.inj h).symm⟩
  · exact .inr h

theorem getStackC_avoids (U : Blk → Prop) : ∀ v ∈ [Val.i64 r0, Val.i64 r1], v.Avoids U := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> simp [Val.Avoids]

theorem env_mono : env.Mono := fun name c hc => by
  rcases env_extern hc with ⟨-, rfl⟩ | hc
  · intro _ _ _ _ _ _ _ _ _ _ hm
    exact .returned (RefinesList.refl _) hm
  · exact plRunEnv_mono name c hc

theorem env_frameSafe : env.FrameSafe := fun name c hc => by
  rcases env_extern hc with ⟨-, rfl⟩ | hc
  · intro U _ _ _ _ _ _ _ hm hmm
    exact ⟨rfl, getStackC_avoids U, hm, hmm⟩
  · exact plRunEnv_frameSafe name c hc

theorem env_tempOblivious : env.TempOblivious := fun name c hc => by
  rcases env_extern hc with ⟨-, rfl⟩ | hc
  · intro X _ _ _ _ _ _ _ hm hmm
    exact ⟨rfl, getStackC_avoids _, hm, hmm⟩
  · exact plRunEnv_tempOblivious name c hc

theorem env_keeps {R : Mem → Mem → Prop} (hR : ∀ m, R m m) :
    ∀ name c, env.extern name = some c → c.Keeps R := fun name c hc => by
  rcases env_extern hc with ⟨-, rfl⟩ | hc
  · intro _ _ m rs m' h
    cases h
    refine ⟨hR m, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · exact plRunEnv_keeps hR name c hc

theorem env_memOps : env.MemOps :=
  ⟨fun _ h => by simp [env, plRunEnv, withWbHelpers, Env.p1] at h,
    fun _ h => by simp [env, plRunEnv, withWbHelpers, Env.p1] at h⟩

theorem env_allocNonNil : env.AllocNonNil := fun name c hm hc => by
  rcases env_extern hc with ⟨rfl, -⟩ | hc
  · exact absurd hm (by decide +kernel)
  · exact plRunEnv_allocNonNil name c hm hc

theorem env_allocZero : env.AllocZero := fun name c hm hc => by
  rcases env_extern hc with ⟨rfl, -⟩ | hc
  · exact absurd hm (by decide +kernel)
  · simp only [plRunEnv, withWbHelpers] at hc
    split at hc
    · next hn => rcases hn with rfl | rfl <;> exact absurd hm (by decide +kernel)
    · exact Env.p1_allocZero name c hm hc

theorem env_growLen : env.GrowLen := fun name c hn hc => by
  rcases env_extern hc with ⟨rfl, -⟩ | hc
  · rcases hn with h | h <;> exact absurd h (by decide)
  · exact plRunEnv_growLen name c hn hc

theorem env_ifaceEq (eq : List String × List String) : env.IfaceEq eq := fun name c hc s hs => by
  rcases env_extern hc with ⟨rfl, -⟩ | hc
  · rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
  · simp only [plRunEnv, withWbHelpers] at hc
    split at hc
    · next hn' =>
      rcases hn' with rfl | rfl <;> rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)
    · exact Env.p1_ifaceEq eq name c hc s hs

theorem env_wbPre : GoFV.Proof.WB.WbPre env [] {} := by
  obtain ⟨h1, h2, h3a, h3b, h3c, h3d⟩ := plRunEnv_wbPre
  refine ⟨h1, ?_, ?_, ?_, h3c, h3d⟩
  · intro name c hc args clo m ha hcl hm
    rcases env_extern hc with ⟨-, rfl⟩ | hc
    · refine ⟨hm, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact fun _ h => by cases h
    · exact h2 name c hc args clo m ha hcl hm
  · show (if "runtime.wbZero" = "runtime/secret.getStack" then some getStackC
      else plRunEnv.extern "runtime.wbZero") = _
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    exact h3a
  · show (if "runtime.wbMove" = "runtime/secret.getStack" then some getStackC
      else plRunEnv.extern "runtime.wbMove") = _
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))]
    exact h3b

/-- **`VPre` of `env`** on no argument and the empty memory, at the machine layout. -/
theorem env_vpre {k : List Nat} {ro : List (String × Alloc)} (hk : k = []) (hro : ro = [])
    (eq : List String × List String) : VPre k ro eq env [] {} :=
  ⟨env_mono, env_frameSafe, plRunEnv_initAvoids, env_allocNonNil, by rw [hk]; exact DictArgs.nil [],
    env_wbPre, env_tempOblivious, env_memOps,
    by rw [hro]; exact RoImage.nil (env := env) (env_keeps Mem.KeepsRo.refl) {},
    env_keeps Mem.KeepsFrame.refl, env_allocZero, env_growLen, env_ifaceEq eq⟩

/-! ## The machine side -/

/-- `ObjEnv` of the wrapper: framed (16 bytes, 8 of extra space), every symbol at `symS`. -/
theorem objEnvW (hc : checkObj ps spills obj = .ok otab) (haz : otab.autosize = 16)
    (hez : otab.extrasize = 8)
    (hl : linkCode ObjG7.base (fun _ => symS) obj.text obj.relocs.toList = .ok code)
    (hsz : obj.text.size ≤ 2 ^ 64) (hret : code 0x40 = none) (hsym : code symS = none)
    (hnp : ∀ p ∈ ps.toList, addrP GenG2.text p.id ≠ symS)
    (hend : symS ≠ endP GenG2.text ps.toList) :
    ObjEnv ps spills obj otab L ObjG7.base code (s0.x 30) where
  check := hc
  link := by rw [haz, hez]; rfl
  linked := hl
  size := hsz
  ret := hret
  syms _ := ⟨hsym, show symS ≠ (0x40 : BitVec 64) by decide, fun ⟨p, hp, h⟩ => hnp p hp h, hend⟩

/-- The checks of `objFacts` as propositions. -/
theorem obj_spec :
    ObjEnv ps spills obj otab L ObjG7.base code (s0.x 30) ∧ otab.autosize = 16 ∧
    otab.check = none ∧ code 0x40 = none ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧
    ¬ IsProgAddr GenG2.text ps.toList 0x40 ∧ (0x40 : BitVec 64) ≠ endP GenG2.text ps.toList ∧
    symS ≠ endP GenG2.text ps.toList ∧
    ObjEnv.map otab ps L ObjG7.base (pcOfTab GenG2.text ps.toList tab 1 2) =
      ObjG7.base + BitVec.ofNat 64 (otab.offs[0]!) ∧
    ObjG7.noICall ps = true ∧ (memI.blocks.toList.map (·.1)).Nodup ∧ symsOut = true ∧
    varOp g 3 = some (.PARAM, 0) ∧ varOp g 4 = some (.PARAM, 8) ∧
    frameOff L .PARAM 0 = 24 ∧ frameOff L .PARAM 8 = 32 := by
  have hf := obj_facts
  simp only [objFacts, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    decide_eq_true_eq, Option.isNone_iff_eq_none, and_assoc] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := hf
  refine ⟨objEnvW (eq_getOk h1) h2 h3 (eq_getOk h5) h6 h7 h8 (fun p hp => (h9 p hp).1) h10,
    h2, h4, h7, fun p hp => (h9 p hp).2.2, fun ⟨p, hp, h⟩ => (h9 p hp).2.1 h, h11, h10, h12, h13,
    h14, h15, h16, h17, h18, h19⟩

/-! ## The results on the caller's stack -/

/-- A result block with `x` in its low byte holds no pointer word. -/
theorem ptrNone {x : BitVec 8} (hx : x = 0x11 ∨ x = 0x22) (o : Nat) :
    ptrWordAt? #[.b x, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] o = none := by
  unfold ptrWordAt?
  split
  · rename_i h
    have : o = 0 := by simp at h; omega
    subst this
    clear h
    rcases hx with rfl | rfl <;> decide
  · rfl

/-- Eight bytes related to `x` and seven zero bytes, no pointer word: the 64-bit word `x`. -/
theorem word_of_bytes {ι : Blk → Option (BitVec 64)} {W : Nat → Prop} {x : BitVec 8}
    {mm : Memory} {a : BitVec 64} (hnw : ∀ o, ¬ W o)
    (h : BytesRel ι W #[.b x, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] mm a) :
    readMem mm a 8 = x.setWidth 64 := by
  have hb : ∀ i (hi : i < 8),
      ByteRel ι ((#[.b x, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] : Array Byte)[i]'(by
        simpa using hi)) (mm (a + BitVec.ofNat 64 i)) :=
    fun i hi => h.2.2 i (by simpa using hi) (fun o ho => absurd ho (hnw o))
  have b0 := hb 0 (by decide)
  have b1 := hb 1 (by decide)
  have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide)
  have b4 := hb 4 (by decide)
  have b5 := hb 5 (by decide)
  have b6 := hb 6 (by decide)
  have b7 := hb 7 (by decide)
  simp only [ByteRel, List.getElem_toArray] at b0 b1 b2 b3 b4 b5 b6 b7
  simp only [readMem, BitVec.add_assoc]
  simp at b0 b1 b2 b3 b4 b5 b6 b7 ⊢
  rw [← b0, ← b1, ← b2, ← b3, ← b4, ← b5, ← b6, ← b7]
  apply BitVec.eq_of_toNat_eq
  simp
  rw [BitVec.toNat_append]
  simp
  omega

/-- A result block of `memF` injected at `a`: its 64-bit word there. -/
theorem resultWord {ι : Blk → Option (BitVec 64)} {mm : Memory} {k : Nat} {x : BitVec 8}
    (hx : x = 0x11 ∨ x = 0x22) {a : BitVec 64}
    (hk : (Blk.local 0 k, ({ data := #[.b x, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] } : Alloc))
      ∈ memF.blocks) (hι : ι (.local 0 k) = some a) (h : MemInj ι memF mm) :
    readMem mm a 8 = x.setWidth 64 := by
  obtain ⟨W, hW⟩ := h.bytes
  have hb := hW _ _ a hk hι
  refine word_of_bytes (fun o ho => ?_) hb
  obtain ⟨p, hp, -⟩ := hb.1 o ho
  rw [ptrNone hx o] at hp
  cases hp

/-! ## The witness -/

/-- **Non-vacuity of `verified_mach_atSP`** on `runtime.secret_getStack`'s ABI0 wrapper: the
verified pipeline returns a `fullyVerified` state, the generic `run` (in `env`, at the machine
layout `AM`) returns `[0x11, 0x22]`; at `Addrs.fixed` no activation of the pipeline's output is a
`G49Env` (so `verified_mach` holds of it there only vacuously); and `verified_mach_atSP` applies
with every premise discharged: a `runLoc` of the allocated function refines the `run`, it is
`finish` of its body's defined outcome, and when the body returns, `runMach` of the linked words
(the callee by the hook `H`) from the function's entry returns to the caller's `0x40` (`MachRet`)
with the memory related (`ResultRel`, no register result: the results are on the stack). -/
theorem verified_mach_atSP_witness :
    ∃ r, verifiedPipelineFull penv f0 0 sec0.zvar dcl = .ok r ∧ r.fullyVerified = true ∧
      (∃ m, GoFV.SSA.run env penv.tables f0 [] {} 5 = .returned [.i64 r0, .i64 r1] m) ∧
      (∀ L' ps' ret tab' E', ¬ @G49Env Addrs.fixed (liveCtx (LocCtx.make r.st.tables r.st.func))
        g L' ps' ret tab' E') ∧
      ∃ fuel', OutcomeRefines 0 (GoFV.SSA.run env penv.tables f0 [] {} 5)
          (runLoc env r.st.tables r.st.func [] {} fuel') ∧
        ∃ raw, runLoopLoc env (liveCtx (LocCtx.make r.st.tables r.st.func)) fuel'
            (locInit env (liveCtx (LocCtx.make r.st.tables r.st.func)) [] {})
            (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.f.entry = raw ∧
          runLoc env r.st.tables r.st.func [] {} fuel' =
            finish env (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.outs
              (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.defers
              (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.act raw ∧
          raw.Defined ∧
          (∀ rs mm, raw = .returned rs mm →
            ∃ E t' n, (envAtSP g L (E0 (liveCtx (LocCtx.make r.st.tables r.st.func)))).Extends E ∧
              runMach H code 0x40 n s0 = .returned t' ∧ MachRet s0 t' ∧ ResultRel E [] rs mm t') ∧
          ∃ E t' n, (envAtSP g L (E0 (liveCtx (LocCtx.make r.st.tables r.st.func)))).Extends E ∧
            runMach H code 0x40 n s0 = .returned t' ∧ MachRet s0 t' ∧
            readMem t'.mem (s0.sp + 8) 8 = r0 ∧ readMem t'.mem (s0.sp + 16) 8 = r1 := by
  have hf := e2e_facts
  simp only [e2eFacts, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hf
  obtain ⟨⟨⟨hp, hrun⟩, hdict⟩, hro⟩ := hf
  obtain ⟨hO, haz, hnone, hret40, hlt, hnp40, hne40, hend, hpcF, hni, hkeys, hso, h3, h4, ho0,
    ho8⟩ := obj_spec
  cases hpe : verifiedPipelineFull penv f0 0 sec0.zvar dcl with
  | error e => rw [hpe] at hp; cases hp
  | ok r =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true] at hp
    obtain ⟨⟨⟨⟨hv, hn⟩, hrl⟩, hC⟩, hR⟩ := hp
    obtain ⟨hcL, hrok, houts, hav, hf3, hf4, hsl, hentry, hbm, hb1, hsz, hi2, hv7, hop, hcf, hk30,
      hsim, hu, hes, -, hmt, hcr⟩ := lcC_spec hC
    simp only [lcFactsR, Bool.and_eq_true] at hR
    obtain ⟨hR, hFin⟩ := hR
    obtain ⟨sI, hsI, hR'⟩ := GenG1.okThen_spec hR
    simp only [Bool.and_eq_true] at hR'
    obtain ⟨hsIIs, hst⟩ := hR'
    obtain ⟨s', hs', hcallIs⟩ := GenG1.okThen_spec hst
    obtain ⟨hregs, hflags, hslots, hmem⟩ := sIIs_spec hsIIs
    obtain ⟨hr0, hr1, hmem'⟩ := sCallIs_spec hcallIs
    have hx2 : ∀ x ∈ r.nnf,
        (sameRun x.1 x.2 = true ∧ noArgPtrB x.1 x.2 = true) ∧ noNilPtrB x.1 x.2 = true :=
      fun x hx => by
        have := List.all_eq_true.1 hn x hx
        simpa only [Bool.and_eq_true] using this
    have hnn : ∀ x ∈ r.nnf, GoFV.Proof.NoNilFault x.1 x.2 env [] {} := fun x hx =>
      sameRun_spec (hx2 x hx).1.1
    have hap : ∀ x ∈ r.nnf, GoFV.Proof.ArgPtrsOK x.1 x.2 env [] {} := fun x hx =>
      argPtrsOK_of_none (hx2 x hx).1.2 env [] {}
    have hnp : ∀ x ∈ r.nnf, GoFV.Proof.NilPtrsOK x.1 x.2 env [] {} := fun x hx =>
      nilPtrsOK_of_none (hx2 x hx).2 env [] {}
    obtain ⟨m0, hrun0⟩ := isRet2_spec hrun
    have hd : (GoFV.SSA.run env penv.tables f0 [] {} 5).Defined := by
      rw [hrun0]; trivial
    have hc60 : checkG60 (LocCtx.make r.st.tables r.st.func) ps bs g = .ok (tab, ktOf
        (liveCtx (LocCtx.make r.st.tables r.st.func))) := by
      simpa [checkG60, hrl] using hcL
    have hm3 := ιM_l3 h3 ho0
    have hm4 := ιM_l4 h4 ho8
    have hE := g28Env (lc := liveCtx (LocCtx.make r.st.tables r.st.func)) hlt hav hf3 hf4 hsl hso
      hend
    have hEE : EntryEnv (envAtSP g L (E0 (liveCtx (LocCtx.make r.st.tables r.st.func)))) L
        ps.toList otab.autosize s0 :=
      { sp := by
          rw [haz]
          show sp0 + BitVec.ofInt 64 16 = sp0 + 16
          decide
        g := rfl
        lr := rfl
        fp := rfl
        fp0 := by decide
        framed := by rw [haz]; rfl
        lrOut := ⟨hnp40, hne40⟩ }
    have hME : MachEntry code ObjG7.base 24 s0 :=
      { pc := rfl, spAlign := by decide, room := by decide, lrOutside := hret40,
        gOutside := by decide, fp := by decide }
    have hent : EntryMatch (envAtSP g L (E0 (liveCtx (LocCtx.make r.st.tables r.st.func))))
        (InWins L (E0 (liveCtx (LocCtx.make r.st.tables r.st.func))).sp
          (pendWins (liveCtx (LocCtx.make r.st.tables r.st.func)) g)) sI s0 :=
      { regs := fun r v hv => by
          by_cases h30 : r = 30
          · subst h30
            exact ⟨fun q hq => by simp [objX?] at hq, fun q hq => by simp [objV?] at hq⟩
          · rw [(hregs r v hv).2 h30]
            exact ⟨fun _ _ => ⟨fun _ => rfl, trivial⟩, fun _ _ => trivial⟩
        flags := hflags
        slots := hslots
        mem := ⟨memI, hmem, fun _ => 0, memInjI hm3 hm4, fun _ _ => rfl⟩ }
    have hinv : G3Inv (envAtSP g L (E0 (liveCtx (LocCtx.make r.st.tables r.st.func))))
        (liveCtx (LocCtx.make r.st.tables r.st.func))
        (kAt (liveCtx (LocCtx.make r.st.tables r.st.func))
          (ktOf (liveCtx (LocCtx.make r.st.tables r.st.func)))
          (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.f.entry
          (blkOf (liveCtx (LocCtx.make r.st.tables r.st.func))) 2) sI :=
      { core := by
          refine ⟨fun r v c _ hv hc => ?_, memI, hmem, sepI hkeys hm3 hm4⟩
          by_cases h30 : r = 30
          · subst h30
            obtain ⟨x, rfl⟩ := (hregs 30 v hv).1 rfl
            rw [hentry, hk30] at hc
            cases hc
            rfl
          · rw [(hregs r v hv).2 h30]
            trivial
        slots := by intro k v h; rw [hslots] at h; cases h }
    have hRP : RunPre env H (liveCtx (LocCtx.make r.st.tables r.st.func)) g L
        (endP L.text ps.toList) (envAtSP g L (E0 (liveCtx (LocCtx.make r.st.tables r.st.func))))
        1 2 sI :=
      runPreH hsim hb1 hi2 hv7 hop fun s'' hs E m hx _ => by
        rw [hs'] at hs
        cases hs
        exact callOKH (addrAgree_ext hx) hcf hmem hr0 hr1 hmem'
    rw [← hentry] at hb1 hbm hRP hpcF
    obtain ⟨fuel', href, raw, hraw, hfin, hdef, hret, -⟩ :=
      verified_mach_atSP (A := AM) (g := g) (L := L)
        (E0 := E0 (liveCtx (LocCtx.make r.st.tables r.st.func))) rfl hpe hv
        (env_vpre hdict hro _) hnn hap hnp hd rfl hc60 hO hookMap_H
        (ObjG7.noICall_spec hni L) hrok hME (by rw [haz]; decide) (by decide)
        (fun _ _ _ h => by rw [hnone] at h; cases h) (fun _ _ _ h => by rw [hnone] at h; cases h)
        hE hEE hb1 hbm (by rw [hsz]; decide) hsI hes hent
        (fun _ _ _ h => by rw [hnone] at h; cases h) hinv hu hpcF hRP (fun _ => hmt)
        (by rw [hcr]; intro n a h; cases h)
    rw [houts] at hret
    have hF := isRetF_spec hFin
    have hrawF : raw = .returned [] memF := by
      rw [← hraw]
      rcases Nat.le_total fuel' 10 with h | h
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
        rw [hk] at hF
        rw [← GoFV.Proof.runLoopLoc_mono env _ fuel' k _ _ (by rw [hraw]; exact hdef)]
        exact hF
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [GoFV.Proof.runLoopLoc_mono env _ 10 k _ _ (by rw [hF]; trivial)]
        exact hF
    obtain ⟨E, t', n, hx, hrm, hX, hRes⟩ := hret [] memF hrawF
    have e3 : s0.sp + 8 = sp0 + BitVec.ofInt 64 24 := by decide
    have e4 : s0.sp + 16 = sp0 + BitVec.ofInt 64 32 := by decide
    refine ⟨r, rfl, hv, ⟨m0, hrun0⟩, fixedNone hav h3 h4 hf3 hf4, fuel', href, raw, hraw, hfin,
      hdef, hret, E, t', n, hx, hrm, hX, ?_, ?_⟩
    · rw [e3, resultWord (Or.inl rfl) (by simp [memF]) (hx.2 _ _ hm3) hRes.mem]
      decide
    · rw [e4, resultWord (Or.inr rfl) (by simp [memF]) (hx.2 _ _ hm4) hRes.mem]
      decide

end AtSP

end GoFV.Proof.Witness.ObjEndToEndAtSP

