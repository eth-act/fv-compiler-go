import GoFVTest.Driver.Back
import GoFVTest.GenIn
import GoFV.Gen.Entry62
import GoFV.Gen.Check64
import GoFV.Gen.MemTyL
import GoFV.Asm.ConstLoad
import GoFV.Gen.Results
import GoFV.Asm.CheckObj

/-!
# `gofv-ssa-opt --check --verified --e2e`: end-to-end coverage (`docs/DRIVER.md`)

`GoFV.Proof.Obj.verified_mach` applies to a function when the verified pipeline is
`fullyVerified`, `checkG64` (the latest genssa slice, its loops' branch targets included,
`loopOK`) accepts genssa's Progs with `progedit`'s float constant loads (P0', `p0Prime`: the
constant symbols numbered as `internConsts` adds them to G2's symbols, which must be the numbers
the assembler's `flush` gives them, else the function is rejected) against
the pipeline's own output (`LocCtx.make` of its tables and function) with class tables `kt`,
`memTyL` holds of `liveCtx` of that context (the context `checkG64` runs `checkG64L` on),
`entryStoresOK` holds of it
at its entry values' end (`entryLen`: the entry stores cover the windows of the
register-assigned parameters the function accesses), `argsOK` holds of it there (the incoming
stack arguments' `Arg`s before `entryLen` and, in a function with one, no pending window and no
morestack spill), `retRegsOK` holds of them on that context
(every `Ret` block returns its results in their ABI registers),
`checkObj` accepts the assembler's output on those same Progs (P0'). `back` runs this back end on
a function after `trim` and its tables:

- `Env.load` on the export with its last (`trim`) section's function replaced by the given one
  (homes and temporary registers from its `f.low`), and the given tables;
- the frame layout (`allocFrame`) and `genssa` on it, its Progs in the input file's symbol
  numbers (`Back.genP0`, as the driver's back end `Back.chain`);
- `checkG64` on P0' with G2's inputs of that frame (the symbols by the file's numbers and the
  constant symbols, `GenCheck.slotOpOf`, the frame size), `memTyL`, `entryStoresOK` and `argsOK`
  (with the object's morestack spills) on `liveCtx` at `entryLen`, and `retRegsOK` on `liveCtx`
  and its class tables;
- `Flushplist` (`GoFV.Asm.flush`) on the file with genssa's Progs (`GenP0.progFile`) and
  `checkObj` on P0', their register-argument spills and the port's text, relocations and Progs;
  when an entry value before `entryLen` writes `R26` (`ctxtBefore`; a closure's
  `LoweredGetClosurePtr`, which `entryLen` counts), the morestack tail must call
  `runtime.morestack`, which keeps it (`morestackCtxtWhy`: the context `verified_mach`'s
  `MorestackOK` premise takes, `ctxtBefore lc k`);
- end to end, also `entryVacuous` at `entryLen`: no entry value after it (else `RunPre` cannot
  hold) and every closure pointer before it (`cloBefore`, so `cloOK_of_cloBefore` discharges the
  trusted `CloOK` along the run of the top-level activation, whose closure context is
  `env.closure`, #705).

Inputs taken from the stock `.prog` file: only its input view (`Back.inputView`, what the
driver input file holds, no stock result): the definitions (names, types, symbols), the
config, `Dcl` when `AllocFrame` starts with its flags, the `genin` section (the text symbol's
header and function info) and the definitions the assembler reads. For the pipeline's output
the `Dcl` is its own (`ownFrame`): the frontend's declarations, then the autos the pipeline
created. The frame, the Progs and the object are the ports' own. The pipeline runs as
`--check --verified` runs it (`verifiedExport`).

As a cross-check, `back` also runs on the stock `trim` function with the whole file's tables
(as `gen-check`, but with the ports' frame and the file's symbol numbers).
-/

namespace GoFVTest.Driver.E2E

open GoFV.SSA (ExportFile Tables Func GoStr)
open GoFV.SSA.Sem (LocCtx)
open GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Gen.Check (checkG64 liveCtx G2In retRegsOK ownOutRegs entryLen entryStoresOK memTyL
  memTyLWhy accessedVars varOp needs48
  entryStoresWhy pendWins argsOK argsBefore noArg ctxtBefore)

/-- **The tail's context** (the checked fact behind `MorestackOK`'s context, #708): when an entry
value before `k` writes `R26` (`ctxtBefore lc k`), the morestack tail of `checkObj`'s table must
call `runtime.morestack` (symbol table `syms`), which keeps `R26` (`runtime/asm_arm64.s:449`,
`:269`), not `runtime.morestack_noctxt`, which zeroes it (`:493-502`); the assembler calls the
former in a function with `NEEDCTXT` (`cmd/internal/obj/arm64/obj7.go:283-289`). `none`: holds. -/
def morestackCtxtWhy (lc : LocCtx) (k : Nat) (syms : Array (GoStr × Nat)) (o : ObjIn)
    (tab : Tab) : Option String :=
  match tab.check with
  | some (_, tail, _) =>
    if !ctxtBefore lc k then none else
    match tailCall o.text o.relocs.toList tail with
    | some (n, _) =>
      let name := (syms[n]?.map (·.1.toStringLossy)).getD "?"
      if name == "runtime.morestack" then none
      else some s!"tail: R26 written before the entry's end, but the tail calls {name}"
    | none => some "tail: no call"
  | none => none

open GoFVTest.Driver.Back (genP0 GenP0 inputView)
open GoFVTest.GenCheck (slotOpOf classOf)

open GoFV.Gen.Check (kAt KTab cls retBlockOK retArgOK memTy fTy) in
/-- Why `retRegsOK lc kt` fails: the first failing condition of the first block `retBlockOK`
rejects. -/
def retWhy (lc : LocCtx) (kt : KTab) : String := Id.run do
  let outs := ownOutRegs lc
  for bid in lc.ctx.f.blocks.toList do
    let some blk := lc.ctx.f.block? bid | continue
    if retBlockOK lc kt outs bid blk then continue
    let [c] := blk.controls.toList | return "Ret: not one control"
    let some v := lc.ctx.f.value? c | return "Ret: no control value"
    if v.op != .MakeResult then return s!"Ret: control {repr v.op}"
    let .tuple ts := lc.ty c | return "Ret: MakeResult shape"
    let args := v.args.toList
    if args.length != outs.length + 1 || ts.length != args.length then
      return s!"Ret: {args.length - 1} results, {outs.length} result registers"
    let K := kAt lc kt bid blk blk.values.size
    for ((a, t), r) in (args.zip ts).zip outs do
      if retArgOK lc K a t r then continue
      if 16 ≤ r && r < 31 || 47 ≤ r then return s!"result register {r}"
      if lc.home a != some (.reg r) then
        return s!"result not homed in its register: {repr (lc.home a)}"
      match cls (lc.ty a), cls t with
      | some c, some c' =>
        if K.get r != some c then return s!"result class {c}, class at the Ret {K.get r}"
        if r < 16 then return s!"result of class {c} read at class {c'}"
        if !fTy (lc.ty a) || !fTy t then
          return s!"floating-point result shape {repr (lc.ty a)} read at {repr t}"
        return s!"floating-point result of class {c} read at class {c'}"
      | none, _ => return s!"result shape {repr (lc.ty a)}"
      | _, none => return s!"MakeResult component shape {repr t}"
    return "Ret: memory"
  return "accepted"

/-- Why `argsOK lc g spills k` fails (`k = entryLen lc`). -/
def argsWhy (lc : LocCtx) (g : G2In) (spills : List GoFV.Asm.Spill) (k : Nat) : String :=
  if !argsBefore lc k then "Arg after the entry values, or an edge to the entry block"
  else if noArg lc then "accepted"
  else if !(pendWins lc g).isEmpty then "Arg with a pending register-parameter window"
  else if !spills.isEmpty then "Arg with morestack spills"
  else "accepted"

open GoFV.SSA (Op Value) in
open GoFV.Gen.Check (entryOp24 cloBefore) in
/-- **Vacuity at the entry** (every `verified_mach` variant), and `CloOK` at the top-level
activation:

- `"closure pointer after the start"`: a `LoweredGetClosurePtr` at or after `k`, or an edge to
  the entry block (`cloBefore lc k` fails): `cloOK_of_cloBefore` does not discharge the trusted
  `CloOK` along the run, so the function is not counted end to end (`checkG11`'s `cloFirst` puts
  the closure pointer among the entry values, which `entryLen` counts);
- `"entry value after the start"`: the run from `(entry, k)` reaches, through the entry block's
  values from `k` that step without a panic or that make the run stuck (`Defined` then fails: no
  value here panics), an `ArgIntReg`/`ArgFloatReg` (or an `InitMem` of an unlowered function) at
  or after `k`, where `RunPre` (`RunPreM`, `RunPreS`) cannot hold (`entryOp24 v.op = false ∨
  (InitMem ∧ lowered)`).

The values passed on the way are those that cannot panic: the entry values, spills,
`VarDef`/`VarLive`/`InlMark`, `Copy`, `MOVDconst` and `ZERO`. A load off the closure pointer is no
reason (#705): the top-level run's closure pointer is the closure context `env.closure`, and
`G3Pre`/`G4Pre` ask it to point to valid bytes as they ask of any other pointer. `none`: neither.
-/
def entryVacuous (lc : LocCtx) (k : Nat) : Option String :=
  if !cloBefore lc k then some "closure pointer after the start" else
  match lc.ctx.f.block? lc.ctx.f.entry with
  | none => none
  | some blk =>
    let vals := (blk.values.toList.drop k).filterMap lc.ctx.f.value?
    let safe (op : Op) : Bool :=
      op == .SP || op == .SB || op == .InitMem ||
        op == .StoreReg || op == .VarDef || op == .VarLive || op == .InlMark || op == .Copy ||
        op == .ARM64MOVDconst || op == .ARM64ZERO
    let rec go : List Value → Option String
      | [] => none
      | v :: vs =>
        if entryOp24 v.op && !(v.op == .InitMem && lc.ctx.f.lowered) then
          some "entry value after the start"
        else if safe v.op then go vs
        else none
    go vals

/-- The validators' verdicts on one function (`none`: accepted). -/
structure Res where
  /-- `checkG64`'s rejection (also P0' numbering and, with a float constant load, `memTyL`). -/
  gen : Option String
  /-- `entryStoresOK`'s rejection (`none` also when `checkG64` rejects: not run). -/
  entry : Option String
  /-- `argsOK`'s rejection (`none` also when `checkG64` rejects: not run). -/
  args : Option String := none
  /-- `checkG64` accepted and the function has a pending window (`pendWins`). -/
  pend : Bool
  /-- `retRegsOK`'s rejection (`none` also when `checkG64` rejects: not run). -/
  ret : Option String
  obj : Option String
  /-- The frame layout's `stksize` and `stkptrsize`. -/
  frame : Int × Int
  /-- The function needs G48's mode (`needs48` of `liveCtx`): `verified_mach_S` covers it, else
  `verified_mach`. -/
  n48 : Bool := false
  /-- The distinct frame operands of the accessed `Blk.local` frame variables (forgeable, with a
  `NAME_AUTO`/`NAME_PARAM` operand). At `Addrs.fixed` no activation is a `G49Env` with two or more
  of them (`g49Env_fixed_apart`), nor, in G48's mode, with one (`g49Env_fixed_outSP`: `SP` is
  pinned to `outargs 0`'s fixed base `2^62`, the variable to `2^62 + x·2^24`, which no operand
  within the stack-variable limit reaches): there `verified_mach_fixed`/`verified_mach_S_fixed`
  hold only vacuously; `verified_mach_atSP`/`verified_mach_S_atSP` cover them. -/
  locals : Nat := 0
  /-- `entryVacuous` at `entryLen` (`none` also when `checkG64` rejects): `RunPre` cannot hold,
  so every `verified_mach` variant holds of the function only vacuously, or a closure pointer runs
  after the start (`cloBefore` fails), so `CloOK` is not discharged. -/
  vac : Option String := none

/-- Accepted by all five: `verified_mach`'s back-end premises hold. -/
def Res.all (r : Res) : Bool :=
  r.gen.isNone && r.entry.isNone && r.args.isNone && r.ret.isNone && r.obj.isNone

/-- End to end: the back-end premises hold and the function is not vacuous at the entry
(`entryVacuous`), so some `verified_mach` variant applies to it non-vacuously (those vacuous at
`Addrs.fixed` only are covered by the `_atSP` variants). -/
def Res.e2e (r : Res) : Bool := r.all && r.vac.isNone

/-- The `.prog` type for a new auto of `.ssa` type `st`: a `type` definition of the file with
the same string, size, alignment and pointer data, else one made from `st` when it has no
pointer words or is one pointer word (`PTR`, `UNSAFEPTR`, `MAP`, `CHAN`, `FUNC`: the shapes of
`regalloc`'s spill slots and of `SplitSlot`'s pieces). -/
def progTypeFor (types : Array (Nat × GoFV.Asm.TypeDef)) (t : GoFV.SSA.TypeRef)
    (st : GoFV.SSA.TypeDef) : Except String (Sum Nat GoFV.Asm.TypeDef) := do
  let same (d : GoFV.Asm.TypeDef) :=
    d.str == st.str && d.size == st.size && d.align == st.align && d.ptrdata == st.ptrdata
  if let some (k, _) := types.find? (same ·.2) then return .inl k
  let made (mask : ByteArray) : GoFV.Asm.TypeDef :=
    { size := st.size, align := st.align, ptrdata := st.ptrdata, hasPtr := some st.flags.hasptr,
      ptrMask := some mask, str := st.str }
  if st.ptrdata == some 0 && !st.flags.hasptr then return .inr (made .empty)
  if st.size == some 8 && st.ptrdata == some 8 && st.flags.hasptr &&
      [GoFV.SSA.TypeKind.PTR, .UNSAFEPTR, .MAP, .CHAN, .FUNC].contains st.kind then
    return .inr (made (ByteArray.mk #[1]))
  throw s!"new auto: type t{t} ({st.str.toStringLossy}) has no .prog type"

/-- `AllocFrame`'s input for the pipeline's own output (tables `tabs`, input tables `t0`):
`curfn.Dcl` is the frontend's declarations, the first `dcl0` (`dcllen` of section 0) entries
of the stock `frame` input, followed by the autos the passes created (`fe.SplitSlot`,
`f.NewLocal`), each appended to `Dcl` when created. Those of the pipeline are the `name` aux
values `tabs` defines and `t0` does not (`VerifiedFull.newAutos`), in number order (creation
order); their definitions are made from the aux values (class, escape, flags, `FrameOffset`;
`Linksym` in the file's package). The stock passes' autos (the stock input after `dcl0`) are
left out and lose their link to an aux number, which in `tabs` may name another object. `dcl`:
the pipeline's `len(curfn.Dcl)` after `trim`, a cross-check. Also returns `back`'s `links`. -/
def ownFrame (pin : ProgFile) (t0 tabs : Tables) (dcl0 dcl : Nat) :
    Except String (ProgFile × Array (Nat × GoFV.SSA.AuxRef × GoFV.SSA.TypeRef)) := do
  let din := pin.frame.dclIn
  if din.size < dcl0 then throw s!"frame: {din.size} Dcl entries, dcllen {dcl0}"
  let stockNew : Std.HashSet Nat := (din.extract dcl0 din.size).foldl (·.insert ·.name) {}
  let unlink (d : Def) : Def := match d with
    | .name k nd => if stockNew.contains k then .name k { nd with aux := none } else d
    | d => d
  let defs := pin.frame.defs.map unlink
  let gdefs := pin.genin.defs.map unlink
  let mut types : Array (Nat × GoFV.Asm.TypeDef) := #[]
  let mut nextT := 0
  let mut nextN := 0
  for d in defs ++ gdefs do
    match d with
    | .type k t => types := types.push (k, t); nextT := max nextT (k + 1)
    | .name k _ => nextN := max nextN (k + 1)
    | _ => pure ()
  let mut tyOf : Std.HashMap GoFV.SSA.TypeRef Nat := {}
  let mut added : Array Def := #[]
  let mut dclNew : Array DclEntry := #[]
  let mut links : Array (Nat × GoFV.SSA.AuxRef × GoFV.SSA.TypeRef) := #[]
  for h : i in [0:tabs.auxes.size] do
    if (t0.aux? i).isSome then continue
    let some { kind := .name sym cls t off esc fl _, .. } := tabs.auxes[i] | continue
    let pt ← match tyOf[t]? with
      | some k => pure k
      | none =>
        let some st := tabs.type? t | throw s!"new auto a{i}: type t{t} not defined"
        let k ← match ← progTypeFor types t st with
          | .inl k => pure k
          | .inr td =>
            added := added.push (.type nextT td)
            types := types.push (nextT, td)
            nextT := nextT + 1
            pure (nextT - 1)
        tyOf := tyOf.insert t k
        pure k
    added := added.push (.name nextN
      { sym, cls := cls.name, type := some pt, esc, linkName := pin.pkg ++ GoStr.ofString "." ++ sym,
        linkAbi := 0, aux := some i })
    links := links.push (nextN, i, t)
    dclNew := dclNew.push
      { name := nextN, off,
        flags := { used := fl.used, addrtaken := fl.addrtaken, opendeferslot := fl.opendeferslot,
                   nonmergeable := fl.nonmergeable, autotmp := fl.autotmp } }
    nextN := nextN + 1
  if dcl0 + dclNew.size != dcl then
    throw s!"frame: dcllen {dcl0} + {dclNew.size} new autos, but the pipeline's dcllen is {dcl}"
  let pin := { pin with
    frame := { pin.frame with defs := defs ++ added, dclIn := din.extract 0 dcl0 ++ dclNew }
    genin := { pin.genin with defs := gdefs } }
  return (pin, links)

/-- The back end on `f` (tables `tabs`) as the function after `trim` of the export `e`, with the
driver input file `pin`: a load or port error, or the validators' verdicts. `links`: names of
`pin` (`ownFrame`) linked to aux values of `tabs` rather than of the stock file's tables
(`Env.load` checks the links against the latter), with their `.ssa` types. -/
def back (e : ExportFile) (pin : ProgFile)
    (links : Array (Nat × GoFV.SSA.AuxRef × GoFV.SSA.TypeRef))
    (tabs : Tables) (f : Func) : Except String Res := do
  let some sec := e.sections.back? | throw "env: no section"
  let e := { e with sections := e.sections.pop.push { sec with func := f } }
  let own : Std.HashSet Nat := links.foldl (·.insert ·.1) {}
  let unlink (d : Def) : Def := match d with
    | .name k nd => if own.contains k then .name k { nd with aux := none } else d
    | d => d
  let pinL := { pin with frame := { pin.frame with defs := pin.frame.defs.map unlink } }
  let env ← (GoFV.Gen.Env.load e pinL).mapError (s!"env: {·}")
  let env := { env with
    tabs
    auxName := links.foldl (fun m (k, a, _) => m.insert a k) env.auxName
    names := links.foldl (init := env.names) fun ns (k, a, t) =>
      ns.modify k (·.map fun x => { x with d := { x.d with aux := some a }, ssaType := some t }) }
  let g ← genP0 env pin
  let pf := g.progFile pin none
  let ps := pf.prog0.progs
  let syms : Array (GoStr × Nat) :=
    (List.range g.tab.next).toArray.map fun k => (g.tab.syms[k]?).getD default
  let bstart := fun b => (g.gout.st.bstart[b]?).join
  let lc := LocCtx.make tabs f
  let llc := liveCtx lc
  let fo ← (flush pf).mapError (s!"Flushplist: {·}")
  -- P0': numbered by `internConsts` for the validator, by the assembler's `flush` for `checkObj`
  let (syms', ps') ← (p0PrimeSyms syms ps).mapError (s!"P0': {·}")
  let psF ← (p0Prime (fun n => fo.st.symIdx[(GoStr.ofString n, Obj.ABI0.toNat)]?) ps).mapError
    (s!"P0': {·}")
  let gin : G2In :=
    { syms := syms', slotOp := slotOpOf env (GoFV.Gen.Ctx.ofFrame env g.fr).offsets,
      stksize := g.fr.stksize }
  let spills := pf.prog0.fn.spills
  let (gen, entry, args, pend, ret, vac) :=
    if (ps'.map (·.from_.sym)) != (psF.map (·.from_.sym)) then
      (some "P0': a constant symbol numbered otherwise than by the assembler", none, none, false,
        none, none)
    else if !(GoFV.SSA.Sem.constRo (GoFV.Gen.Check.symNames gin)).isEmpty && !memTyL llc then
      (some s!"memTyL: {memTyLWhy llc}", none, none, false, none, none)
    else match checkG64 lc ps' bstart gin with
    | .ok (_, kt) =>
      let k := entryLen llc
      (none, (if entryStoresOK llc gin k then none else some (entryStoresWhy llc gin k)),
        (if argsOK llc gin spills.toList k then none else some (argsWhy llc gin spills.toList k)),
        !(pendWins llc gin).isEmpty,
        (if retRegsOK llc kt then none else some (retWhy llc kt)), entryVacuous llc k)
    | .error m => (some m, none, none, false, none, none)
  let ops := ((accessedVars llc).filterMap fun x =>
    if llc.ctx.tabs.forgeable x then match varOp gin x with
      | some (nc, o) => if nc == .AUTO || nc == .PARAM then some (nc == .AUTO, o) else none
      | none => none
    else none).eraseDups
  let o : ObjIn := { text := fo.st.textP, relocs := fo.st.textR, progs := fo.progs }
  let obj := match checkObj psF spills o with
    | .ok t => morestackCtxtWhy llc (entryLen llc) fo.st.syms o t
    | .error m => some m
  return { gen, entry, args, pend, ret, obj, frame := (g.fr.stksize, g.fr.stkptrsize),
           n48 := needs48 llc, locals := ops.length, vac }

/-- Reasons by class (numbers replaced): count and an example (`file: message`). -/
abbrev Why := Std.HashMap String (Nat × String)

def Why.note (w : Why) (msg ex : String) : Why :=
  let k := (classOf msg).take 160 |>.toString
  let (n, x) := w.getD k (0, ex)
  w.insert k (n + 1, x)

def Why.merge (a b : Why) : Why :=
  b.fold (fun m k (n, ex) => let (c, x) := m.getD k (0, ex); m.insert k (c + n, x)) a

/-- Counts of `back`'s verdicts. -/
structure Counts where
  ran : Nat := 0
  /-- `checkG64` alone. -/
  g64 : Nat := 0
  /-- `checkG64` ∧ `entryStoresOK` ∧ `argsOK`. -/
  gen : Nat := 0
  /-- `checkG64` accepts, `entryStoresOK` rejects. -/
  entryRej : Nat := 0
  /-- `checkG64` and `entryStoresOK` accept, `argsOK` rejects. -/
  argsRej : Nat := 0
  /-- `checkG64` accepts and the function has a pending window. -/
  pend : Nat := 0
  /-- End to end with a pending window (the entry stores run). -/
  pendAll : Nat := 0
  /-- `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK`. -/
  ret : Nat := 0
  obj : Nat := 0
  /-- `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `checkObj`. -/
  genObj : Nat := 0
  /-- `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK` ∧ `checkObj` (`Res.all`: the
  back-end premises hold). -/
  prem : Nat := 0
  /-- … and vacuous at the entry (`entryVacuous`, every variant). -/
  vac : Nat := 0
  /-- End to end (`Res.e2e`: the premises hold, not vacuous at the entry). -/
  all : Nat := 0
  /-- End to end and `needs48 = false` (`verified_mach`), and of those with two or more `locals`
  (vacuous at `Addrs.fixed`). -/
  allF : Nat := 0
  allFVac : Nat := 0
  /-- End to end and `needs48 = true` (`verified_mach_S`), and of those with a `local` (vacuous at
  `Addrs.fixed`). -/
  allS : Nat := 0
  allSVac : Nat := 0
  errWhy : Why := {}
  genWhy : Why := {}
  entryWhy : Why := {}
  argsWhy : Why := {}
  retWhy : Why := {}
  objWhy : Why := {}
  /-- `checkObj`'s rejections of the functions `checkG64`, `entryStoresOK`, `argsOK` and
  `retRegsOK` accept: what keeps them from end to end. -/
  e2eObjWhy : Why := {}
  /-- `entryVacuous`'s reasons of the functions whose premises hold. -/
  vacWhy : Why := {}

def Counts.merge (a b : Counts) : Counts :=
  { ran := a.ran + b.ran, g64 := a.g64 + b.g64, gen := a.gen + b.gen,
    entryRej := a.entryRej + b.entryRej, argsRej := a.argsRej + b.argsRej, pend := a.pend + b.pend,
    pendAll := a.pendAll + b.pendAll,
    ret := a.ret + b.ret, obj := a.obj + b.obj,
    genObj := a.genObj + b.genObj, prem := a.prem + b.prem, vac := a.vac + b.vac,
    all := a.all + b.all, allF := a.allF + b.allF,
    allFVac := a.allFVac + b.allFVac, allS := a.allS + b.allS, allSVac := a.allSVac + b.allSVac,
    errWhy := a.errWhy.merge b.errWhy, genWhy := a.genWhy.merge b.genWhy,
    entryWhy := a.entryWhy.merge b.entryWhy, argsWhy := a.argsWhy.merge b.argsWhy,
    retWhy := a.retWhy.merge b.retWhy, objWhy := a.objWhy.merge b.objWhy,
    e2eObjWhy := a.e2eObjWhy.merge b.e2eObjWhy, vacWhy := a.vacWhy.merge b.vacWhy }

def Counts.add (c : Counts) (path : String) (res : Except String Res) : Counts :=
  let ex (m : String) := s!"{path}: {m}"
  match res with
  | .error m => { c with errWhy := c.errWhy.note m (ex m) }
  | .ok r =>
    let one (b : Bool) := if b then 1 else 0
    let ge := r.gen.isNone && r.entry.isNone && r.args.isNone
    let c := { c with ran := c.ran + 1, g64 := c.g64 + one r.gen.isNone, gen := c.gen + one ge,
                      entryRej := c.entryRej + one (r.gen.isNone && r.entry.isSome),
                      argsRej := c.argsRej + one (r.gen.isNone && r.entry.isNone && r.args.isSome),
                      pend := c.pend + one r.pend, pendAll := c.pendAll + one (r.e2e && r.pend),
                      ret := c.ret + one (ge && r.ret.isNone),
                      obj := c.obj + one r.obj.isNone,
                      genObj := c.genObj + one (ge && r.obj.isNone),
                      prem := c.prem + one r.all,
                      vac := c.vac + one (r.all && r.vac.isSome),
                      all := c.all + one r.e2e,
                      allF := c.allF + one (r.e2e && !r.n48),
                      allFVac := c.allFVac + one (r.e2e && !r.n48 && 2 ≤ r.locals),
                      allS := c.allS + one (r.e2e && r.n48),
                      allSVac := c.allSVac + one (r.e2e && r.n48 && 1 ≤ r.locals) }
    let c := match r.all, r.vac with
      | true, some m => { c with vacWhy := c.vacWhy.note m (ex m) }
      | _, _ => c
    let c := match r.gen with | some m => { c with genWhy := c.genWhy.note m (ex m) } | none => c
    let c := match r.entry with
      | some m => { c with entryWhy := c.entryWhy.note m (ex m) } | none => c
    let c := match r.args with
      | some m => { c with argsWhy := c.argsWhy.note m (ex m) } | none => c
    let c := match r.ret with | some m => { c with retWhy := c.retWhy.note m (ex m) } | none => c
    let c := match r.obj with | some m => { c with objWhy := c.objWhy.note m (ex m) } | none => c
    match r.gen, r.entry, r.args, r.ret, r.obj with
    | none, none, none, none, some m => { c with e2eObjWhy := c.e2eObjWhy.note m (ex m) }
    | _, _, _, _, _ => c

structure Stats where
  files : Nat := 0
  /-- Unparsable `.ssa` or `.prog` files, missing `.prog` files, no `dcllen`. -/
  parseErrors : Nat := 0
  /-- Pass errors of the verified pipeline. -/
  passErrors : Nat := 0
  /-- `fullyVerified` (through `trim`). -/
  full : Nat := 0
  /-- … and the pipeline's output identical to stock after `trim` (`VFile.same`). -/
  fullSame : Nat := 0
  /-- `back` on the pipeline's output of the fully verified functions. -/
  ours : Counts := {}
  /-- End to end, and the pipeline's output identical to stock. -/
  allSame : Nat := 0
  /-- The cross-check: `back` on the stock `trim` function (every parsed function). -/
  stockFns : Nat := 0
  stock : Counts := {}
  /-- The end-to-end accepted files. -/
  accept : Array String := #[]
  /-- Fully verified, output identical to stock and genssa ran: the frame (`ownFrame`) has the
  stock `.prog`'s `stksize` and `stkptrsize` (`frameSame`) or not (`frameDiff`, an example). -/
  frameSame : Nat := 0
  frameDiff : Nat := 0
  frameDiffEx : String := ""

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors,
    passErrors := a.passErrors + b.passErrors, full := a.full + b.full,
    fullSame := a.fullSame + b.fullSame, ours := a.ours.merge b.ours,
    allSame := a.allSame + b.allSame, stockFns := a.stockFns + b.stockFns,
    stock := a.stock.merge b.stock, accept := a.accept ++ b.accept,
    frameSame := a.frameSame + b.frameSame, frameDiff := a.frameDiff + b.frameDiff,
    frameDiffEx := if a.frameDiffEx.isEmpty then b.frameDiffEx else a.frameDiffEx }

/-- Records the cross-check on the stock `trim` function. -/
def Stats.addStock (st : Stats) (path : String) (res : Except String Res) : Stats :=
  { st with stockFns := st.stockFns + 1, stock := st.stock.add path res }

/-- Records a fully verified function (`same`: its output is identical to stock; `stockFrame`:
the stock `.prog`'s `stksize` and `stkptrsize`) and `back` on the pipeline's output. -/
def Stats.addFull (st : Stats) (path : String) (same : Bool) (stockFrame : Int × Int)
    (res : Except String Res) : Stats :=
  let st := { st with full := st.full + 1, fullSame := st.fullSame + (if same then 1 else 0),
                      ours := st.ours.add path res }
  match res with
  | .ok r =>
    let st := if !same then st
      else if r.frame == stockFrame then { st with frameSame := st.frameSame + 1 }
      else { st with frameDiff := st.frameDiff + 1,
                     frameDiffEx := if st.frameDiffEx.isEmpty then
                       s!"{path}: {r.frame} (stock {stockFrame})" else st.frameDiffEx }
    if r.e2e then
      { st with allSame := st.allSame + (if same then 1 else 0), accept := st.accept.push path }
    else st
  | .error _ => st

def pct (a b : Nat) : String :=
  if b == 0 then "-" else
  let x := a * 10000 / b
  s!"{x / 100}.{if x % 100 < 10 then "0" else ""}{x % 100}%"

def whyTable (title : String) (w : Why) (top : Nat) : String := Id.run do
  if w.isEmpty then return ""
  let mut out := s!"\n{title}\n\n| reason | functions | example |\n| --- | ---: | --- |\n"
  let sorted := w.toArray.qsort fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.1 < b.1)
  for (k, (c, ex)) in sorted.toList.take top do
    out := out ++ s!"| `{k}` | {c} | {(ex.take 200).toString.replace "|" "\\|"} |\n"
  return out

/-- The report. -/
def Stats.text (st : Stats) (ms : Nat) : String := Id.run do
  let o := st.ours
  let s := st.stock
  let row (name : String) (a b : Option Nat) : String :=
    let cell (x : Option Nat) := match x with
      | some n => s!"{n} | {pct n st.files}"
      | none => "- | -"
    s!"| {name} | {cell a} | {cell b} |\n"
  let mut out := s!"files: {st.files}, parse errors: {st.parseErrors}, pass errors: \
    {st.passErrors}, wall: {ms / 1000} s\n\n"
  out := out ++ "| functions | pipeline output | share | stock `trim` (cross-check) | share |\n\
    | --- | ---: | ---: | ---: | ---: |\n"
  out := out ++ row "fully verified (Phase 2, through `trim`)" (some st.full) none
  out := out ++ row "… genssa and `Flushplist` ran" (some o.ran) (some s.ran)
  out := out ++ row "… ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK`" (some o.gen) (some s.gen)
  out := out ++ row "… ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK`" (some o.ret)
    (some s.ret)
  out := out ++ row "… ∧ `checkObj`" (some o.obj) (some s.obj)
  out := out ++ row "… ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `checkObj`" (some o.genObj)
    (some s.genObj)
  out := out ++ row ("… ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK` ∧ `checkObj` " ++
    "(the premises hold)") (some o.prem) (some s.prem)
  out := out ++ row ("… of them vacuous or with `CloOK` not discharged (`entryVacuous`, every " ++
    "variant)") (some o.vac) (some s.vac)
  out := out ++ row "**… premises hold, not vacuous (end to end, `verified_mach`)**" (some o.all)
    (some s.all)
  out := out ++ row "… end to end, pipeline output identical to stock after `trim`" (some st.allSame) none
  out := out ++ row "fully verified, pipeline output identical to stock" (some st.fullSame) none
  out := out ++ s!"\nThe stock column runs the same back end on the stock `trim` function with the \
    whole file's tables, on all {st.stockFns} parsed functions (not only the fully verified).\n"
  out := out ++ s!"\nEntry stores (pipeline output; stock): `checkG64` accepts {o.g64}; {s.g64}; \
    {o.pend}; {s.pend} of them have a pending window (a register-assigned parameter in a \
    `Blk.local` block); `entryStoresOK` rejects {o.entryRej}; {s.entryRej}; end to end with a \
    pending window: {o.pendAll}; {s.pendAll}.\n"
  out := out ++ s!"\nIncoming stack arguments (pipeline output; stock): `argsOK` rejects \
    {o.argsRej}; {s.argsRej} of the functions `checkG64` and `entryStoresOK` accept.\n"
  out := out ++ s!"\nBy mode (pipeline output; stock): end to end under `verified_mach` \
    (`needs48 = false`) {o.allF}; {s.allF}, of which vacuous at `Addrs.fixed` (two or more \
    `Blk.local` operands, `g49Env_fixed_apart`) {o.allFVac}; {s.allFVac}; under `verified_mach_S` \
    (G48's mode, `needs48 = true`) {o.allS}; {s.allS}, of which vacuous at `Addrs.fixed` (a \
    `Blk.local` access, `g49Env_fixed_outSP`) {o.allSVac}; {s.allSVac}. The `_atSP` variants hold \
    of all of them non-vacuously.\n"
  out := out ++ s!"\nVacuous at the entry (pipeline output; stock), of the functions whose premises \
    hold, not counted end to end: {o.vac}; {s.vac} (`entryVacuous`: an entry value after the \
    start `entryLen`, where `RunPre` cannot hold of the run under any variant, or a closure \
    pointer after it, `cloBefore`, where `cloOK_of_cloBefore` does not discharge `CloOK`).\n"
  out := out ++ s!"\nFrame (`ownFrame`, `AllocFrame` on the pipeline's own `Dcl`) of the fully \
    verified functions whose output is identical to stock: stock `stksize`/`stkptrsize` \
    {st.frameSame}, other {st.frameDiff}{if st.frameDiffEx.isEmpty then "" else s!" ({st.frameDiffEx})"}.\n"
  out := out ++ whyTable "Back-end errors among the fully verified:" o.errWhy 30
  out := out ++ whyTable "`checkG64` rejections among the fully verified (first reason):" o.genWhy 40
  out := out ++ whyTable "`entryStoresOK` rejections among the fully verified accepted by `checkG64`:"
    o.entryWhy 10
  out := out ++ whyTable ("`argsOK` rejections among the fully verified accepted by `checkG64` " ++
    "and `entryStoresOK`:") o.argsWhy 10
  out := out ++ whyTable ("`retRegsOK` rejections among the fully verified accepted by " ++
    "`checkG64`:") o.retWhy 10
  out := out ++ whyTable "`checkObj` rejections among the fully verified:" o.objWhy 40
  out := out ++ whyTable ("`checkObj` rejections among the fully verified accepted by `checkG64`, " ++
    "`entryStoresOK`, `argsOK` and `retRegsOK`:") o.e2eObjWhy 40
  out := out ++ whyTable ("Vacuous at the entry among the fully verified whose premises hold " ++
    "(`entryVacuous`):") o.vacWhy 10
  out := out ++ whyTable "Back-end errors on the stock `trim` function:" s.errWhy 20
  return out

end GoFVTest.Driver.E2E
