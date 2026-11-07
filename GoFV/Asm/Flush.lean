import GoFV.Asm.Obj7
import GoFV.Asm.Span7
import GoFV.Asm.Pcln
import Std.Data.HashSet

/-!
# `Flushplist` for one compiled function (`plist.go:24-178`; `docs/PASSES3.md` D1)

`flush` runs the I4 ports on the `prog0` section of a `gofv-prog 2` file (P0, the Prog list
after `genssa`/`defframe`) in `Flushplist`'s order: the list is cut at `TEXT` with every `AEND`
dropped, then `linkpatch` with `progedit` and `preprocess` (`GoFV.Asm.Obj7`), `span7`
(`GoFV.Asm.Span7`), `MarkUnsafePoints` with `isUnsafePoint`/`isRestartable` (which `span7`
calls between encoding and the jump-table words; neither reads what the other writes), and
`linkpcln` (`GoFV.Asm.Pcln`), then the `Compile` tail's `weakenGlobalMapInitRelocs`.
`populateDWARF` (I5) and `fieldtrack` (`Experiment.FieldTrack` is off) are not ported.

Prog IDs: the input keeps its IDs; Progs allocated here are renumbered in list order from one
past the largest input ID, and a Prog referenced but not in the list (or the typed-nil target
of an infinite `JMP` loop) gets the next ID when first referenced in printing order, as the
exporter numbers them (`docs/contracts/export.md`, "Progs").
-/

namespace GoFV.Asm

open GoFV.SSA (GoStr Pos Token)
open AsmM

/-- The read-only context of a `.prog` file: its configuration and the definitions of the
sections before `asm` (position bases, inlining tree). -/
def AsmCtxt.ofFile (pf : ProgFile) : Except String AsmCtxt := do
  let cfg (k : String) : Option Token := (pf.config.find? (·.1 == k)).map (·.2)
  let flag (k : String) (dflt : Bool) : Except String Bool :=
    match cfg k with
    | none => pure dflt
    | some (.word "0") => pure false
    | some (.word "1") => pure true
    | some _ => throw s!"config {k}: not 0/1"
  let maymorestack ← match cfg "maymorestack" with
    | none => pure ""
    | some (.str s) => pure s.toStringLossy
    | some _ => throw "config maymorestack: not a string"
  let mut c : AsmCtxt :=
    { pkgpath := pf.pkg.toStringLossy,
      compilingRuntime := ← flag "compilingruntime" false,
      flagDynlink := ← flag "flagdynlink" false,
      flagOptimize := ← flag "optimize" true,
      maymorestack }
  for d in pf.frame.defs ++ pf.genin.defs ++ pf.prog0.defs do
    match d with
    | .posBase i b fi => c := { c with posBases := c.posBases.insert i (b, fi) }
    | .inl k x => c := { c with inls := c.inls.insert k x }
    | _ => pure ()
  return c

/-- The state `Flushplist` starts from: the `prog0` Progs by ID, linked in list order from
`TEXT` without the `AEND` placeholders, the symbols of the sections before `asm`, and the text
symbol's `FuncInfo`. Jump-table symbols start as `makeJumpTableSym` leaves them (`Sxxx`,
`AttrStatic`, `ssa/rewrite.go:2486-2491`). -/
def AsmSt.ofProg0 (pf : ProgFile) : Except String AsmSt := do
  let ps := pf.prog0.progs
  let some text := ps[0]? | throw "prog0: empty Prog list"
  if text.as != .TEXT then throw "prog0: the list does not start with TEXT"
  let maxId := ps.foldl (fun m p => max m p.id) 0
  let mut progs : Array Prog := (Array.range (maxId + 1)).map AsmM.zeroProg
  for p in ps do
    progs := progs.set! p.id p
  let mut link : Array (Option Nat) := Array.replicate (maxId + 1) none
  let mut last := text.id
  for p in ps.extract 1 ps.size do
    if p.as == .END then continue
    if p.as == .TEXT then throw "prog0: second TEXT"
    if p.as == .FUNCDATA then
      if let some y := p.to.sym then
        let nm := (pf.prog0.defs ++ pf.genin.defs).findSome? fun
          | .sym k n _ => if k == y then some n.toStringLossy else none
          | _ => none
        if nm == some "go_args_stackmap" || nm == some "no_pointers_stackmap" then
          throw s!"Flushplist: FUNCDATA {nm.getD ""} (assembly only)"
    link := link.set! last (some p.id)
    last := p.id
  let mut syms : Array (GoStr × Nat) := #[]
  let mut symIdx : Std.HashMap (GoStr × Nat) Nat := {}
  for d in pf.frame.defs ++ pf.genin.defs ++ pf.prog0.defs do
    if let .sym k n abi := d then
      while syms.size ≤ k do syms := syms.push (⟨.empty⟩, 0)
      syms := syms.set! k (n, abi)
      if !n.bytes.isEmpty && !symIdx.contains (n, abi) then symIdx := symIdx.insert (n, abi) k
  let mut symData : Std.HashMap Nat SymData := {}
  for (y, _) in pf.prog0.fn.jumpTables do
    symData := symData.insert y
      { sym := y, kind := "Sxxx", size := 0, align := 0, attr := Obj.AttrStatic.toNat,
        data := .empty, relocs := #[] }
  return { progs, link, text := text.id, firstNew := maxId + 1, syms, symIdx, symData,
           fn := pf.prog0.fn }

/-- `weakenGlobalMapInitRelocs` (`ssagen/pgen.go:331-336,359-378`): in the package init
function (`AttrPkgInit`; `-d=wrapglobalmapctl` is not set in the corpus), every relocation to
an outlined global map initialiser gets the `R_WEAK` bit. The initialisers registered by
`RegisterMapInitLsym` (`gc/compile.go:105-111`) are the package's `map.init.<n>` functions
(`staticinit/sched.go:1165`), whose symbols are the init function's package prefix followed by
`.map.init.<n>`. The type keeps its other bits, so `RelocType.String()` prints the number. -/
def weakenGlobalMapInitRelocs : AsmM Unit := do
  unless ← textAttr Obj.AttrPkgInit do return
  let (fnName, _) ← symName (← get).fn.sym
  let fnName := fnName.toStringLossy
  unless fnName.endsWith ".init" do return
  let pfx := fnName.dropRight 5 ++ ".map.init."
  let isMapInit (n : String) : Bool :=
    n.startsWith pfx && (n.drop pfx.length).all Char.isDigit && n.length > pfx.length
  let rs ← (← get).textR.mapM fun r => do
    let some y := r.sym | return r
    let (n, _) ← symName y
    if !isMapInit n.toStringLossy then return r
    let some t := Obj.relocTypeNum r.type | fail s!"weakenGlobalMapInitRelocs: relocation type {r.type}"
    -- int16(t | R_WEAK) for 0 < t < 2^15
    return { r with type := s!"RelocType({t + Obj.R_WEAK})" }
  modify fun s => { s with textR := rs }

/-- `Flushplist`'s per-function steps and the `Compile` tail. -/
def flushSteps : AsmM Unit := do
  linkpatch
  preprocess
  span7
  markUnsafePoints isUnsafePoint isRestartable
  linkpcln
  weakenGlobalMapInitRelocs

/-- Renumbers the Progs allocated by the assembler in list order (from `firstNew`) and gives a
referenced Prog outside the list (or the typed-nil target) the next ID at its first reference
in printing order (`p` line: the Prog, `Pool`, `From`, `RestArgs`, `To`). Returns the Progs of
the list in order and the inline marks and jump tables with renumbered references. -/
def renumber (s : AsmSt) : Array Prog × FuncInfo := Id.run do
  let order := (listOrder.run {} |>.run s |>.toOption.map (·.1)).getD #[]
  let inList : Std.HashSet Nat := order.foldl (·.insert ·) {}
  let mut ids : Std.HashMap Nat Nat := {}
  let mut next := s.firstNew
  for id in order do
    if id < s.firstNew then ids := ids.insert id id
    else
      ids := ids.insert id next
      next := next + 1
  -- references outside the list, in printing order
  let mut nilId : Option Nat := none
  let mut out : Array Prog := #[]
  for id in order do
    let p := s.progs[id]!
    let mut refs : Array (Option Nat) := #[p.pool]
    for a in #[p.from_] ++ p.rest.map (·.2) ++ #[p.to] do
      match a.val with
      | .target t => refs := refs.push (some t)
      | .nilTarget => refs := refs.push none
      | _ => pure ()
    for r in refs do
      match r with
      | some t =>
        if !ids.contains t then
          ids := ids.insert t (if t < s.firstNew && !inList.contains t then t else next)
          if !(t < s.firstNew && !inList.contains t) then next := next + 1
      | none =>
        if nilId.isNone then
          nilId := some next
          next := next + 1
    out := out.push p
  let mapId (t : Nat) : Nat := ids.getD t t
  let mapAddr (a : Addr) : Addr :=
    match a.val with
    | .target t => { a with val := .target (mapId t) }
    | .nilTarget => { a with val := .target (nilId.getD 0) }
    | _ => a
  let progs := out.map fun p =>
    { p with id := mapId p.id, pool := p.pool.map mapId, from_ := mapAddr p.from_,
             rest := p.rest.map fun (k, a) => (k, mapAddr a), to := mapAddr p.to }
  let fn := { s.fn with inlMarks := s.fn.inlMarks.map fun (p, k) => (mapId p, k),
                        jumpTables := s.fn.jumpTables.map fun (y, ts) => (y, ts.map mapId) }
  return (progs, fn)

/-- The result of `flush`: the final state, the Prog list in order (renumbered) and the text
symbol's `FuncInfo` with renumbered references. -/
structure FlushOut where
  st : AsmSt
  progs : Array Prog
  fn : FuncInfo
  deriving Inhabited

/-- `Flushplist` on the function of a `.prog` file, from its `prog0` section. `symAlign` gives
`LSym.Align` of input symbols (by number) that the export does not record (default: unknown,
0, as for symbols of other packages). -/
def flush (pf : ProgFile) (symAlign : Std.HashMap Nat Int := {}) : Except String FlushOut := do
  let ctx ← AsmCtxt.ofFile pf
  let st ← AsmSt.ofProg0 pf
  let st := { st with symAlign := symAlign }
  let ((), st) ← (flushSteps.run ctx).run st
  let (progs, fn) := renumber st
  return { st, progs, fn }

end GoFV.Asm
