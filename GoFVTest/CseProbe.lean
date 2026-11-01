import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.CSE

/-!
# `cse-probe`: does cse's checker ever reject?

Runs `cseRw` on the input of every `generic cse` instance of the given export files and counts
the inputs cse changes, those where `CSE.crel` rejects the result (a rejection costs parity)
with the first failing condition, and those outside `cse_refines`' fragment (`CSE.inFrag`:
a `Load` merge through different memory arguments that `memEnd` does not re-derive), with the
reason per such merge.
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.CSE

namespace GoFVTest.CseProbe

def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + 1)

/-- The first condition of `crel tabs strict` that fails. -/
def why (tabs : Tables) (strict : Bool) (f g : Func) (rw : Array (Option ID)) : String := Id.run do
  if DomCert.cfgView g != DomCert.cfgView f then return "cfg"
  if g.ownAux != f.ownAux then return "ownAux"
  if g.valueTab.size != f.valueTab.size then return "size"
  for bid in f.blocks do
    if !blockOK rw f g bid then return s!"block b{bid}"
  for x in List.range f.valueTab.size do
    if !valueOK rw f g x then
      return s!"value v{x} {((f.value? x).map (·.op.name)).getD "?"}"
  let c := DomCert.make f
  for x in List.range rw.size do
    if !substOK tabs strict c rw f g x then
      return s!"subst v{x} {((f.value? x).map (·.op.name)).getD "?"}"
  for bid in f.blocks do
    if !schedOK f g bid then return s!"sched b{bid}"
  return "?"

/-- Why a `Load` merge `x ↦ r` with different memory arguments fails `loadOK`. -/
def whyLoad (tabs : Tables) (rw : Array (Option ID)) (f : Func) (fx fr : Value) : String :=
  match fx.args[0]?, fr.args[0]?, fx.args[1]?, fr.args[1]? with
  | some p, some p', some m, some m' =>
    if rep rw p != rep rw p' then "ptr-differs"
    else if memEnd tabs f p fx.type m != memEnd tabs f p fx.type m' then "memEnd-differs"
    else if !((rw.getD m none).isNone && (rw.getD m' none).isNone) then "mem-replaced"
    else "ok"
  | _, _, _, _ => "arity"

/-- The kind of `r`'s memory argument when `x` and `r` share a block. -/
def memKind (f : Func) (fx fr : Value) : String :=
  if fx.block != fr.block then "other-block" else
  match fr.args[1]? >>= f.value? with
  | none => "none"
  | some m =>
    if m.block != fx.block then "mem-outside"
    else if m.op == .Phi then "mem-phi"
    else if Sem.prio m.op == 2 then "mem-root"
    else if m.op == .SelectN && (m.args[0]? >>= f.value?).any (Sem.prio ·.op == 2) then
      "mem-selectn-root"
    else s!"mem-{m.op.name}"

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut inst := 0
  let mut errs := 0
  let mut changed := 0
  let mut rejected := 0
  let mut outFrag := 0
  let mut unchecked := 0
  let mut substs := 0
  let mut shown := 0
  let mut whys : Std.HashMap String Nat := {}
  let mut fragWhys : Std.HashMap String Nat := {}
  let mut loadWhys : Std.HashMap String Nat := {}
  let mut memKinds : Std.HashMap String Nat := {}
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok e := parseExport data | continue
    let typs := (e.sections[0]?.bind (·.typs)).getD #[]
    let base : PassEnv :=
      { passName := "generic cse", pkg := e.pkg, funcName := e.name, abi := e.abi
        nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs
        typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp, tables := {}
        frontend := e.frontendTables }
    let mut tables : Tables := {}
    for h : k in [0:e.sections.size] do
      let s := e.sections[k]
      let prev := tables
      tables := tables.addAll s.defs
      if k == 0 || s.pass.toStringLossy != "generic cse" then continue
      inst := inst + 1
      let env := { base with tables := prev }
      let f := e.sections[k-1]!.func
      if (check { tabs := prev, typs } f).toBool == false then unchecked := unchecked + 1
      let some mem := env.typ? "Mem" | errs := errs + 1; continue
      let some #[.word ps] := env.config? "ptrsize" | errs := errs + 1; continue
      let some ptrSize := ps.toInt? | errs := errs + 1; continue
      let c : CSE.Ctx :=
        { tabs := prev, order := env.typeOrder, isMem := prev.isMemory mem, ptrSize }
      match cseRw c f with
      | .error _ => errs := errs + 1
      | .ok (g, rw) =>
        let n := (rw.filter (·.isSome)).size
        substs := substs + n
        if n > 0 then changed := changed + 1
        for x in List.range rw.size do
          if let some r := rw.getD x none then
            if let (some fx, some fr, some gx, some gr) :=
                (f.value? x, f.value? r, g.value? x, g.value? r) then
              if fx.op == .Load && gx.args != gr.args then
                let w := whyLoad prev rw f fx fr
                loadWhys := bump loadWhys w
                if w == "ok" then memKinds := bump memKinds (memKind f fx fr)
        if !crel prev false f g rw then
          rejected := rejected + 1
          let w := why prev false f g rw
          whys := bump whys ((w.splitOn " ").head! ++ " " ++ ((w.splitOn " ").getLast!))
          if shown < 10 then
            IO.println s!"REJECT {path} {k}: {w}"
            shown := shown + 1
        else if !crel prev true f g rw then
          outFrag := outFrag + 1
          let w := why prev true f g rw
          fragWhys := bump fragWhys ((w.splitOn " ").head! ++ " " ++ ((w.splitOn " ").getLast!))
  IO.println s!"generic cse inputs {inst} (failing check {unchecked}, errors {errs}): cse changes {changed} ({substs} substitutions), checker rejects {rejected}, outside the fragment {outFrag}"
  IO.println s!"rejections by first failing condition: {whys.toList}"
  IO.println s!"outside the fragment by first failing condition: {fragWhys.toList}"
  IO.println s!"Load merges through different memory, by loadOK outcome: {loadWhys.toList}"
  IO.println s!"loadOK merges by the representative's memory argument: {memKinds.toList}"
  return 0

end GoFVTest.CseProbe

def main (args : List String) : IO UInt32 := GoFVTest.CseProbe.main args
