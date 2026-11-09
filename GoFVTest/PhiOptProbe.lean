import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.PhiOptCheck

open scoped GoFV.SSA.Sem.Fixed

/-!
# `phiopt-probe`: does phiopt's checker ever reject?

Runs `phiopt` on every section of the given export files whose input passes `check` and
counts the sections it changes and those where `PhiOpt.prel` rejects the result (first failing
condition), separately for the inputs of the `phiopt` pass (a rejection there costs parity);
also counts the rewritten `Phi`s by form and lists the smallest accepted changed inputs
(witness candidates).
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.PhiOpt

namespace GoFVTest.PhiOptProbe

/-- Why a rewritten `Phi` is not accepted. -/
def explain (tabs : Tables) (f g : Func) (fv gv : Value) : String := Id.run do
  let b := fv.block
  let arms := fv.args.toList.map fun a => ((f.value? a).map fun u => s!"v{a}:{u.op.name}[{u.auxInt}]").getD "?"
  let c := gv.args[0]?.getD 0
  let cv := (g.value? c).map (·.op.name)
  let facts := (facts f b c)
  let av := gv.args.toList.map fun a => s!"v{a}:{avail f b a}"
  return s!"{gv.op.name} args {av} arms {arms} c-op {cv} facts {facts} preds {((f.block? b).map (·.preds.size))}"

/-- The first condition of `prel` that fails. -/
def why (tabs : Tables) (f g : Func) : String := Id.run do
  if DomCert.cfgView g != DomCert.cfgView f then return "cfg"
  if g.ownAux != f.ownAux then return "ownAux"
  if !(f.valueTab.size ≤ g.valueTab.size) then return "size"
  for bid in f.blocks do
    if !blockOK f g bid then return s!"block b{bid}"
  for x in List.range f.valueTab.size do
    if !valueOK tabs f g x then
      if let (some fv, some gv) := (f.value? x, g.value? x) then
        return s!"value v{x} {explain tabs f g fv gv}"
      return s!"value v{x} ?"
  return "?"

def main (args : List String) : IO UInt32 := do
  let instOnly := args.head? == some "--inst"
  let args := if instOnly then args.tail else args
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut secs := 0
  let mut changed := 0
  let mut rejected := 0
  let mut inst := 0
  let mut instChanged := 0
  let mut instRejected := 0
  let mut errs := 0
  let mut shown := 0
  let mut whys : Std.HashMap String Nat := {}
  let mut forms : Std.HashMap String Nat := {}
  let mut cands : Array (Nat × Nat × String) := #[]
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok ex := parseExport data | continue
    let typs := (ex.sections[0]?.bind (·.typs)).getD #[]
    let some u8 := (typs.find? (·.1 == "UInt8")).map (·.2) | continue
    let mut tabs : Tables := {}
    for h : j in [0:ex.sections.size] do
      let s := ex.sections[j]
      tabs := tabs.addAll s.defs
      let f := s.func
      let isInst := (ex.sections[j + 1]?.map (·.pass.toStringLossy)) == some "phiopt"
      if instOnly && !isInst then continue
      if (check { tabs, typs } f).toBool == false then continue
      secs := secs + 1
      if isInst then inst := inst + 1
      let .ok g := phiopt tabs u8 f | errs := errs + 1; continue
      if g != f then
        changed := changed + 1
        if isInst then
          instChanged := instChanged + 1
          let mut fs : Array String := #[]
          for x in List.range f.valueTab.size do
            if let (some fv, some gv) := (f.value? x, g.value? x) then
              if fv.op == .Phi && gv.op != .Phi then
                let k := s!"{gv.op.name}" ++
                  (if gv.op == .OrB || gv.op == .AndB then
                    s!"/{((gv.args[1]?.bind f.value?).map (·.op.name)).getD "?"}" else "")
                forms := forms.insert k (forms.getD k 0 + 1)
                fs := fs.push s!"v{x}:{k}"
          if prel tabs f g then
            let nv := f.blocks.foldl (fun n b => n + ((f.block? b).map (·.values.size)).getD 0) 0
            cands := cands.push (nv, f.blocks.size, s!"{path} {s.index} {fs.toList}")
      if !prel tabs f g then
        rejected := rejected + 1
        if isInst then instRejected := instRejected + 1
        let w := why tabs f g
        let key := (w.splitOn " ").head!
        whys := whys.insert key (whys.getD key 0 + 1)
        if isInst || shown < 5 then
          IO.println s!"REJECT {path} {s.index} ({s.pass.toStringLossy}): {w}"
          shown := shown + 1
  IO.println s!"sections {secs}: phiopt changes {changed}, checker rejects {rejected}, errors {errs}"
  IO.println s!"phiopt inputs {inst}: phiopt changes {instChanged}, rejects {instRejected}"
  IO.println s!"rejections by first failing condition: {whys.toList}"
  IO.println s!"rewritten phis at phiopt inputs by form: {forms.toList}"
  IO.println "witness candidates (accepted phiopt inputs; values, blocks), smallest first:"
  for (nv, nb, s) in (cands.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).toList.take 15 do
    IO.println s!"  {nv} {nb} {s}"
  return 0

end GoFVTest.PhiOptProbe

def main (args : List String) : IO UInt32 := GoFVTest.PhiOptProbe.main args
