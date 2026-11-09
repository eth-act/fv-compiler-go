import GoFVTest.Driver.Back
import GoFVTest.GenIn
import GoFV.Gen.Check40
import GoFV.Gen.Results
import GoFV.Asm.CheckObj

/-!
# `gofv-ssa-opt --check --verified --e2e`: end-to-end coverage (`docs/DRIVER.md`)

`GoFV.Proof.Obj.verified_mach` applies to a function when the verified pipeline is
`fullyVerified`, `checkG40` (the latest merged genssa slice) accepts genssa's P0 Progs against
the pipeline's own output (`LocCtx.make` of its tables and function) with class tables `kt`,
`retRegsOK` holds of them on `liveCtx` of that context (the context `checkG40` runs `checkG40L`
on; every `Ret` block returns its results in their ABI registers),
`checkObj` accepts the assembler's output on those same Progs. `back` runs this back end on a
function after `trim` and its tables:

- `Env.load` on the export with its last (`trim`) section's function replaced by the given one
  (homes and temporary registers from its `f.low`), and the given tables;
- the frame layout (`allocFrame`) and `genssa` on it, its Progs in the input file's symbol
  numbers (`Back.genP0`, as the driver's back end `Back.chain`);
- `checkG40` with G2's inputs of that frame (the symbols by the file's numbers,
  `GenCheck.slotOpOf`, the frame size), and `retRegsOK` on `liveCtx` and its class tables;
- `Flushplist` (`GoFV.Asm.flush`) on the file with those Progs (`GenP0.progFile`) and `checkObj`
  on the same Progs, their register-argument spills and the port's text, relocations and Progs.

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
open GoFV.Gen.Check (checkG40 liveCtx G2In retRegsOK ownOutRegs)
open GoFVTest.Driver.Back (genP0 GenP0 inputView)
open GoFVTest.GenCheck (slotOpOf classOf)

open GoFV.Gen.Check (kAt KTab cls retBlockOK retArgOK memTy) in
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
      if r ≥ 16 then return "floating-point result"
      if lc.home a != some (.reg r) then
        return s!"result not homed in its register: {repr (lc.home a)}"
      match cls (lc.ty a), cls t with
      | some c, some c' =>
        if c < c' then return s!"result of class {c} read at class {c'}"
        return s!"result class {c}, class at the Ret {K.get r}"
      | none, _ => return s!"result shape {repr (lc.ty a)}"
      | _, none => return s!"MakeResult component shape {repr t}"
    return "Ret: memory"
  return "accepted"

/-- The validators' verdicts on one function (`none`: accepted). -/
structure Res where
  gen : Option String
  /-- `retRegsOK`'s rejection (`none` also when `checkG40` rejects: not run). -/
  ret : Option String
  obj : Option String
  /-- The frame layout's `stksize` and `stkptrsize`. -/
  frame : Int × Int

/-- Accepted by all three: `verified_mach`'s back-end premises hold. -/
def Res.all (r : Res) : Bool :=
  r.gen.isNone && r.ret.isNone && r.obj.isNone

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
  let gin : G2In :=
    { syms, slotOp := slotOpOf env (GoFV.Gen.Ctx.ofFrame env g.fr).offsets,
      stksize := g.fr.stksize }
  let bstart := fun b => (g.gout.st.bstart[b]?).join
  let lc := LocCtx.make tabs f
  let (gen, ret) := match checkG40 lc ps bstart gin with
    | .ok (_, kt) =>
      (none, if retRegsOK (liveCtx lc) kt then none else some (retWhy (liveCtx lc) kt))
    | .error m => (some m, none)
  let fo ← (flush pf).mapError (s!"Flushplist: {·}")
  let o : ObjIn := { text := fo.st.textP, relocs := fo.st.textR, progs := fo.progs }
  let obj := match checkObj ps pf.prog0.fn.spills o with
    | .ok _ => none
    | .error m => some m
  return { gen, ret, obj, frame := (g.fr.stksize, g.fr.stkptrsize) }

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
  gen : Nat := 0
  /-- `checkG40` ∧ `retRegsOK`. -/
  ret : Nat := 0
  obj : Nat := 0
  /-- `checkG40` ∧ `checkObj`. -/
  genObj : Nat := 0
  /-- `checkG40` ∧ `retRegsOK` ∧ `checkObj` (`Res.all`, end to end). -/
  all : Nat := 0
  errWhy : Why := {}
  genWhy : Why := {}
  retWhy : Why := {}
  objWhy : Why := {}

def Counts.merge (a b : Counts) : Counts :=
  { ran := a.ran + b.ran, gen := a.gen + b.gen, ret := a.ret + b.ret, obj := a.obj + b.obj,
    genObj := a.genObj + b.genObj, all := a.all + b.all,
    errWhy := a.errWhy.merge b.errWhy, genWhy := a.genWhy.merge b.genWhy,
    retWhy := a.retWhy.merge b.retWhy, objWhy := a.objWhy.merge b.objWhy }

def Counts.add (c : Counts) (path : String) (res : Except String Res) : Counts :=
  let ex (m : String) := s!"{path}: {m}"
  match res with
  | .error m => { c with errWhy := c.errWhy.note m (ex m) }
  | .ok r =>
    let one (b : Bool) := if b then 1 else 0
    let c := { c with ran := c.ran + 1, gen := c.gen + one r.gen.isNone,
                      ret := c.ret + one (r.gen.isNone && r.ret.isNone),
                      obj := c.obj + one r.obj.isNone,
                      genObj := c.genObj + one (r.gen.isNone && r.obj.isNone),
                      all := c.all + one r.all }
    let c := match r.gen with | some m => { c with genWhy := c.genWhy.note m (ex m) } | none => c
    let c := match r.ret with | some m => { c with retWhy := c.retWhy.note m (ex m) } | none => c
    match r.obj with | some m => { c with objWhy := c.objWhy.note m (ex m) } | none => c

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
    if r.all then
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
  out := out ++ row "… ∧ `checkG40`" (some o.gen) (some s.gen)
  out := out ++ row "… ∧ `checkG40` ∧ `retRegsOK`" (some o.ret) (some s.ret)
  out := out ++ row "… ∧ `checkObj`" (some o.obj) (some s.obj)
  out := out ++ row "… ∧ `checkG40` ∧ `checkObj`" (some o.genObj) (some s.genObj)
  out := out ++ row "**… ∧ `checkG40` ∧ `retRegsOK` ∧ `checkObj` (end to end, `verified_mach`)**"
    (some o.all) (some s.all)
  out := out ++ row "… end to end, pipeline output identical to stock after `trim`" (some st.allSame) none
  out := out ++ row "fully verified, pipeline output identical to stock" (some st.fullSame) none
  out := out ++ s!"\nThe stock column runs the same back end on the stock `trim` function with the \
    whole file's tables, on all {st.stockFns} parsed functions (not only the fully verified).\n"
  out := out ++ s!"\nFrame (`ownFrame`, `AllocFrame` on the pipeline's own `Dcl`) of the fully \
    verified functions whose output is identical to stock: stock `stksize`/`stkptrsize` \
    {st.frameSame}, other {st.frameDiff}{if st.frameDiffEx.isEmpty then "" else s!" ({st.frameDiffEx})"}.\n"
  out := out ++ whyTable "Back-end errors among the fully verified:" o.errWhy 30
  out := out ++ whyTable "`checkG40` rejections among the fully verified (first reason):" o.genWhy 40
  out := out ++ whyTable "`retRegsOK` rejections among the fully verified accepted by `checkG40`:" o.retWhy 10
  out := out ++ whyTable "`checkObj` rejections among the fully verified:" o.objWhy 40
  out := out ++ whyTable "Back-end errors on the stock `trim` function:" s.errWhy 20
  return out

end GoFVTest.Driver.E2E
