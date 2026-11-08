import GoFVTest.Driver.Back
import GoFVTest.GenIn
import GoFV.Gen.Check18
import GoFV.Gen.Results
import GoFV.Asm.CheckObj

/-!
# `gofv-ssa-opt --check --verified --e2e`: end-to-end coverage (`docs/DRIVER.md`)

`GoFV.Proof.Obj.verified_mach_ret` applies to a function when the verified pipeline is
`fullyVerified`, `checkG18` accepts genssa's P0 Progs against the pipeline's own output
(`LocCtx.make` of its tables and function) with class tables `kt`, `retRegsOK` holds of them
(every `Ret` block returns its results in their ABI registers), and `checkObj` accepts the
assembler's output on those same Progs. `back` runs this back end on a function after `trim`
and its tables:

- `Env.load` on the export with its last (`trim`) section's function replaced by the given one
  (homes and temporary registers from its `f.low`), and the given tables;
- the frame layout (`allocFrame`) and `genssa` on it, its Progs in the input file's symbol
  numbers (`Back.genP0`, as the driver's back end `Back.chain`);
- `checkG18` with G2's inputs of that frame (the symbols by the file's numbers,
  `GenCheck.slotOpOf`, the frame size), and `retRegsOK` on its class tables;
- `Flushplist` (`GoFV.Asm.flush`) on the file with those Progs (`GenP0.progFile`) and `checkObj`
  on the same Progs, their register-argument spills and the port's text, relocations and Progs.

Inputs taken from the stock `.prog` file: only its input view (`Back.inputView`, what the
driver input file holds, no stock result): the definitions (names, types, symbols), the
config, `Dcl` when `AllocFrame` starts with its flags, the `genin` section (the text symbol's
header and function info) and the definitions the assembler reads. The frame, the Progs and the
object are the ports' own. The pipeline runs as `--check --verified` runs it (`verifiedExport`).

As a cross-check, `back` also runs on the stock `trim` function with the whole file's tables
(as `gen-check`, but with the ports' frame and the file's symbol numbers).
-/

namespace GoFVTest.Driver.E2E

open GoFV.SSA (ExportFile Tables Func GoStr)
open GoFV.SSA.Sem (LocCtx)
open GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Gen.Check (checkG18 G2In retRegsOK ownOutRegs)
open GoFVTest.Driver.Back (genP0 GenP0 inputView)
open GoFVTest.GenCheck (slotOpOf classOf)

/-- The validators' verdicts on one function (`none`: accepted). -/
structure Res where
  g18 : Option String
  /-- `retRegsOK`'s rejection (`none` also when `checkG18` rejects: not run). -/
  ret : Option String
  obj : Option String

/-- Accepted by all three: `verified_mach_ret`'s back-end premises hold. -/
def Res.all (r : Res) : Bool := r.g18.isNone && r.ret.isNone && r.obj.isNone

/-- The back end on `f` (tables `tabs`) as the function after `trim` of the export `e`, with the
driver input file `pin`: a load or port error, or the validators' verdicts. -/
def back (e : ExportFile) (pin : ProgFile) (tabs : Tables) (f : Func) : Except String Res := do
  let some sec := e.sections.back? | throw "env: no section"
  let e := { e with sections := e.sections.pop.push { sec with func := f } }
  let env ← (GoFV.Gen.Env.load e pin).mapError (s!"env: {·}")
  let env := { env with tabs }
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
  let (g18, ret) := match checkG18 lc ps bstart gin with
    | .ok (_, kt) =>
      (none, if retRegsOK lc kt then none
        else if (ownOutRegs lc).isNone then some "a result on the stack"
        else some "a Ret block's results not in their ABI registers")
    | .error m => (some m, none)
  let fo ← (flush pf).mapError (s!"Flushplist: {·}")
  let o : ObjIn := { text := fo.st.textP, relocs := fo.st.textR, progs := fo.progs }
  let obj := match checkObj ps pf.prog0.fn.spills o with
    | .ok _ => none
    | .error m => some m
  return { g18, ret, obj }

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
  g18 : Nat := 0
  /-- `checkG18` ∧ `retRegsOK`. -/
  ret : Nat := 0
  obj : Nat := 0
  /-- `checkG18` ∧ `checkObj`. -/
  g18obj : Nat := 0
  /-- `checkG18` ∧ `retRegsOK` ∧ `checkObj`. -/
  all : Nat := 0
  errWhy : Why := {}
  g18Why : Why := {}
  retWhy : Why := {}
  objWhy : Why := {}

def Counts.merge (a b : Counts) : Counts :=
  { ran := a.ran + b.ran, g18 := a.g18 + b.g18, ret := a.ret + b.ret, obj := a.obj + b.obj,
    g18obj := a.g18obj + b.g18obj, all := a.all + b.all, errWhy := a.errWhy.merge b.errWhy,
    g18Why := a.g18Why.merge b.g18Why, retWhy := a.retWhy.merge b.retWhy,
    objWhy := a.objWhy.merge b.objWhy }

def Counts.add (c : Counts) (path : String) (res : Except String Res) : Counts :=
  let ex (m : String) := s!"{path}: {m}"
  match res with
  | .error m => { c with errWhy := c.errWhy.note m (ex m) }
  | .ok r =>
    let one (b : Bool) := if b then 1 else 0
    let c := { c with ran := c.ran + 1, g18 := c.g18 + one r.g18.isNone,
                      ret := c.ret + one (r.g18.isNone && r.ret.isNone),
                      obj := c.obj + one r.obj.isNone,
                      g18obj := c.g18obj + one (r.g18.isNone && r.obj.isNone),
                      all := c.all + one r.all }
    let c := match r.g18 with | some m => { c with g18Why := c.g18Why.note m (ex m) } | none => c
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

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors,
    passErrors := a.passErrors + b.passErrors, full := a.full + b.full,
    fullSame := a.fullSame + b.fullSame, ours := a.ours.merge b.ours,
    allSame := a.allSame + b.allSame, stockFns := a.stockFns + b.stockFns,
    stock := a.stock.merge b.stock, accept := a.accept ++ b.accept }

/-- Records the cross-check on the stock `trim` function. -/
def Stats.addStock (st : Stats) (path : String) (res : Except String Res) : Stats :=
  { st with stockFns := st.stockFns + 1, stock := st.stock.add path res }

/-- Records a fully verified function (`same`: its output is identical to stock) and `back` on
the pipeline's output. -/
def Stats.addFull (st : Stats) (path : String) (same : Bool) (res : Except String Res) : Stats :=
  let st := { st with full := st.full + 1, fullSame := st.fullSame + (if same then 1 else 0),
                      ours := st.ours.add path res }
  match res with
  | .ok r =>
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
  out := out ++ row "… ∧ `checkG18`" (some o.g18) (some s.g18)
  out := out ++ row "… ∧ `checkG18` ∧ `retRegsOK`" (some o.ret) (some s.ret)
  out := out ++ row "… ∧ `checkObj`" (some o.obj) (some s.obj)
  out := out ++ row "… ∧ `checkG18` ∧ `checkObj`" (some o.g18obj) (some s.g18obj)
  out := out ++ row "**… ∧ `checkG18` ∧ `retRegsOK` ∧ `checkObj` (end to end, `verified_mach_ret`)**"
    (some o.all) (some s.all)
  out := out ++ row "… end to end, pipeline output identical to stock after `trim`" (some st.allSame) none
  out := out ++ row "fully verified, pipeline output identical to stock" (some st.fullSame) none
  out := out ++ s!"\nThe stock column runs the same back end on the stock `trim` function with the \
    whole file's tables, on all {st.stockFns} parsed functions (not only the fully verified).\n"
  out := out ++ whyTable "Back-end errors among the fully verified:" o.errWhy 30
  out := out ++ whyTable "`checkG18` rejections among the fully verified (first reason):" o.g18Why 40
  out := out ++ whyTable "`retRegsOK` rejections among the fully verified accepted by `checkG18`:" o.retWhy 10
  out := out ++ whyTable "`checkObj` rejections among the fully verified:" o.objWhy 40
  out := out ++ whyTable "Back-end errors on the stock `trim` function:" s.errWhy 20
  return out

end GoFVTest.Driver.E2E
