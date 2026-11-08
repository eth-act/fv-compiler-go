import GoFVTest.Driver.Back
import GoFVTest.GenIn
import GoFV.Gen.Check18
import GoFV.Asm.CheckObj

/-!
# `gofv-ssa-opt --check --verified --e2e`: end-to-end coverage (`docs/DRIVER.md`)

`GoFV.Proof.Obj.verified_mach_ret` applies to a function when the verified pipeline is
`fullyVerified`, `checkG18` accepts genssa's P0 Progs against the pipeline's own output
(`LocCtx.make` of its tables and function), and `checkObj` accepts the assembler's output on
those same Progs. `back` runs this back end on a function after `trim` and its tables:

- `Env.load` on the export with its last (`trim`) section's function replaced by the given one
  (homes and temporary registers from its `f.low`), and the given tables;
- the frame layout (`allocFrame`) and `genssa` on it, its Progs in the input file's symbol
  numbers (`Back.genP0`, as the driver's back end `Back.chain`);
- `checkG18` with G2's inputs of that frame (the symbols by the file's numbers,
  `GenCheck.slotOpOf`, the frame size);
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
open GoFV.Gen.Check (checkG18 G2In)
open GoFVTest.Driver.Back (genP0 GenP0 inputView)
open GoFVTest.GenCheck (slotOpOf classOf)

/-- The back end on `f` (tables `tabs`) as the function after `trim` of the export `e`, with the
driver input file `pin`: a load or port error, or the rejections of `checkG18` and `checkObj`
(`none`: accepted). -/
def back (e : ExportFile) (pin : ProgFile) (tabs : Tables) (f : Func) :
    Except String (Option String × Option String) := do
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
  let r18 := match checkG18 (LocCtx.make tabs f) ps bstart gin with
    | .ok _ => none
    | .error m => some m
  let fo ← (flush pf).mapError (s!"Flushplist: {·}")
  let o : ObjIn := { text := fo.st.textP, relocs := fo.st.textR, progs := fo.progs }
  let rObj := match checkObj ps pf.prog0.fn.spills o with
    | .ok _ => none
    | .error m => some m
  return (r18, rObj)

/-- Reasons by class (numbers replaced): count and an example (`file: message`). -/
abbrev Why := Std.HashMap String (Nat × String)

def Why.note (w : Why) (msg ex : String) : Why :=
  let k := (classOf msg).take 160 |>.toString
  let (n, x) := w.getD k (0, ex)
  w.insert k (n + 1, x)

def Why.merge (a b : Why) : Why :=
  b.fold (fun m k (n, ex) => let (c, x) := m.getD k (0, ex); m.insert k (c + n, x)) a

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
  /-- … back end ran (no load or port error). -/
  ran : Nat := 0
  /-- … `checkG18` accepts. -/
  g18 : Nat := 0
  /-- … `checkObj` accepts. -/
  obj : Nat := 0
  /-- … both: `verified_mach_ret` applies. -/
  e2e : Nat := 0
  e2eSame : Nat := 0
  errWhy : Why := {}
  g18Why : Why := {}
  objWhy : Why := {}
  /-- The cross-check on the stock `trim` function (every parsed function). -/
  stockFns : Nat := 0
  stockRan : Nat := 0
  stock18 : Nat := 0
  stockObj : Nat := 0
  stockBoth : Nat := 0
  stockErrWhy : Why := {}
  /-- The end-to-end accepted files. -/
  accept : Array String := #[]

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors,
    passErrors := a.passErrors + b.passErrors, full := a.full + b.full,
    fullSame := a.fullSame + b.fullSame, ran := a.ran + b.ran, g18 := a.g18 + b.g18,
    obj := a.obj + b.obj, e2e := a.e2e + b.e2e, e2eSame := a.e2eSame + b.e2eSame,
    errWhy := a.errWhy.merge b.errWhy, g18Why := a.g18Why.merge b.g18Why,
    objWhy := a.objWhy.merge b.objWhy, stockFns := a.stockFns + b.stockFns,
    stockRan := a.stockRan + b.stockRan, stock18 := a.stock18 + b.stock18,
    stockObj := a.stockObj + b.stockObj, stockBoth := a.stockBoth + b.stockBoth,
    stockErrWhy := a.stockErrWhy.merge b.stockErrWhy, accept := a.accept ++ b.accept }

/-- Records the cross-check on the stock `trim` function. -/
def Stats.addStock (st : Stats) (path : String)
    (res : Except String (Option String × Option String)) : Stats :=
  let st := { st with stockFns := st.stockFns + 1 }
  match res with
  | .error m => { st with stockErrWhy := st.stockErrWhy.note m s!"{path}: {m}" }
  | .ok (r18, rObj) =>
    { st with stockRan := st.stockRan + 1,
              stock18 := st.stock18 + (if r18.isNone then 1 else 0),
              stockObj := st.stockObj + (if rObj.isNone then 1 else 0),
              stockBoth := st.stockBoth + (if r18.isNone && rObj.isNone then 1 else 0) }

/-- Records a fully verified function (`same`: its output is identical to stock) and `back` on
the pipeline's output. -/
def Stats.addFull (st : Stats) (path : String) (same : Bool)
    (res : Except String (Option String × Option String)) : Stats :=
  let st := { st with full := st.full + 1, fullSame := st.fullSame + (if same then 1 else 0) }
  match res with
  | .error m => { st with errWhy := st.errWhy.note m s!"{path}: {m}" }
  | .ok (r18, rObj) =>
    let st := { st with ran := st.ran + 1 }
    let st := match r18 with
      | none => { st with g18 := st.g18 + 1 }
      | some m => { st with g18Why := st.g18Why.note m s!"{path}: {m}" }
    let st := match rObj with
      | none => { st with obj := st.obj + 1 }
      | some m => { st with objWhy := st.objWhy.note m s!"{path}: {m}" }
    if r18.isNone && rObj.isNone then
      { st with e2e := st.e2e + 1, e2eSame := st.e2eSame + (if same then 1 else 0),
                accept := st.accept.push path }
    else st

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
  let fns := st.files - st.parseErrors
  let mut out := s!"files: {st.files}, parse errors: {st.parseErrors}, pass errors: \
    {st.passErrors}, wall: {ms / 1000} s\n\n"
  out := out ++ "| functions | count | share of files |\n| --- | ---: | ---: |\n"
  out := out ++ s!"| files | {st.files} | |\n"
  out := out ++ s!"| fully verified (Phase 2, through `trim`) | {st.full} | {pct st.full st.files} |\n"
  out := out ++ s!"| … genssa and `Flushplist` ran on the pipeline's output | {st.ran} | {pct st.ran st.files} |\n"
  out := out ++ s!"| … ∧ `checkG18` | {st.g18} | {pct st.g18 st.files} |\n"
  out := out ++ s!"| … ∧ `checkObj` | {st.obj} | {pct st.obj st.files} |\n"
  out := out ++ s!"| **… ∧ `checkG18` ∧ `checkObj` (end to end, `verified_mach_ret`)** | **{st.e2e}** | **{pct st.e2e st.files}** |\n"
  out := out ++ s!"| … end to end, pipeline output identical to stock after `trim` | {st.e2eSame} | {pct st.e2eSame st.files} |\n"
  out := out ++ s!"| fully verified, pipeline output identical to stock | {st.fullSame} | {pct st.fullSame st.files} |\n"
  out := out ++ s!"\nCross-check, the same back end on the stock `trim` function (whole-file tables), \
    {st.stockFns} functions: ran {st.stockRan}, `checkG18` {st.stock18} ({pct st.stock18 fns}), \
    `checkObj` {st.stockObj} ({pct st.stockObj fns}), both {st.stockBoth} ({pct st.stockBoth fns}).\n"
  out := out ++ whyTable "Back-end errors among the fully verified:" st.errWhy 30
  out := out ++ whyTable "`checkG18` rejections among the fully verified (first reason):" st.g18Why 40
  out := out ++ whyTable "`checkObj` rejections among the fully verified:" st.objWhy 40
  out := out ++ whyTable "Back-end errors on the stock `trim` function:" st.stockErrWhy 20
  return out

end GoFVTest.Driver.E2E
