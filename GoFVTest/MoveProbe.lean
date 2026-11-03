import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.Tighten
import GoFV.Opt.TupleSelectors
import GoFV.Opt.Licm
import GoFV.Proof.Pass.LicmL
import GoFVTest.Parity.Compare

/-!
# `lake exe move-probe [--jobs N] <dir|file>...`: the value-motion validator on the corpus

For every section of `tighten`, `phi tighten`, `tighten tuple selectors` and `loop invariant`
(input: the previous section), runs the Lean pass on the input and counts the sections, those
whose input and output pass `check`, those the pass changed, and those `moveB` accepts (for
`loop invariant`, the hypotheses of `licm_refinesL`: `unhoist f g` passes `check`,
`critRelB f (unhoist f g)` and `moveB (unhoist f g) g`); reports the first failing condition
by count and small witness candidates (changed and accepted).
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.MoveL GoFVTest.Parity

namespace GoFVTest.MoveProbe

/-- The passes of the probe: stock name, port. -/
def passes : Array (String × Pass) :=
  #[("tighten", tightenPass), ("phi tighten", phiTightenPass),
    ("tighten tuple selectors", tightenTupleSelectorsPass), ("loop invariant", licmPass)]

/-- The first failing condition of `moveWith`, `none` if it accepts. -/
def why (ok : Array Bool) (f g : Func) : Option String := Id.run do
  if g.entry != f.entry then return some "entry"
  if g.blocks != f.blocks then return some "blocks"
  if g.ownAux != f.ownAux then return some "ownAux"
  if g.lowered != f.lowered then return some "lowered"
  if !certValid ok f g then return some "certValid"
  for b in f.blocks do
    let (some fb, some gb) := (f.block? b, g.block? b) | return some "block missing"
    if gb.kind != fb.kind then return some "kind"
    if gb.auxInt != fb.auxInt then return some "auxInt"
    if gb.succs != fb.succs then return some "succs"
    if gb.preds != fb.preds then return some "preds"
    if gb.controls != fb.controls then return some "controls"
    if !gb.controls.all (okAt ok) then return some "control not related"
    for x in gb.values do
      if !valueOK ok g fb x then
        let gv := g.getV x
        let k := if gv.op == .Phi then "phi" else if fb.values.contains x then "in place" else "moved"
        return some s!"value ({k}, {gv.op.exportName}, ok {okAt ok x})"
    match schedule g gb, schedule f fb with
    | some oT, some oS =>
      if !orderOK ok f g oT.toList oS.toList then
        let bad := oS.toList.find? fun r => mayPanic f r && !(okAt ok r && oT.toList.contains r &&
          (before oT.toList r).all fun x => !nonTotal g x || (before oS.toList r).contains x)
        let detail := match bad with
          | some r =>
            let xs := (before oT.toList r).filter fun x => nonTotal g x && !(before oS.toList r).contains x
            s!"v{r}:{(f.getV r).op.exportName} ok {okAt ok r} inT {oT.toList.contains r} early {xs.map fun x => s!"v{x}:{(g.getV x).op.exportName}"}"
          | none => "?"
        return some s!"panic order: {detail}"
    | _, _ => return some "schedule"
  return none

structure Cnt where
  secs : Nat := 0
  errors : Nat := 0
  inFails : Nat := 0
  outFails : Nat := 0
  checked : Nat := 0
  changed : Nat := 0
  accepted : Nat := 0
  acceptedChanged : Nat := 0
  deriving Inhabited

def Cnt.add (a b : Cnt) : Cnt :=
  { secs := a.secs + b.secs, errors := a.errors + b.errors, inFails := a.inFails + b.inFails
    outFails := a.outFails + b.outFails, checked := a.checked + b.checked
    changed := a.changed + b.changed, accepted := a.accepted + b.accepted
    acceptedChanged := a.acceptedChanged + b.acceptedChanged }

structure Stats where
  cnt : Array Cnt := Array.replicate passes.size {}
  whys : Std.HashMap String Nat := {}
  examples : Std.HashMap String String := {}
  cands : Array (String × Nat × String) := #[]
  parseErrors : Nat := 0
  bugs : Nat := 0

def Stats.merge (a b : Stats) : Stats :=
  { cnt := (a.cnt.zip b.cnt).map fun (x, y) => x.add y
    whys := b.whys.fold (fun m k n => m.insert k (m.getD k 0 + n)) a.whys
    examples := b.examples.fold (fun m k e => if m.contains k then m else m.insert k e) a.examples
    cands := a.cands ++ b.cands
    parseErrors := a.parseErrors + b.parseErrors, bugs := a.bugs + b.bugs }

def listedCount (f : Func) : Nat :=
  f.blocks.foldl (fun n bid => n + (((f.block? bid).map (·.values.size)).getD 0)) 0

def checkFile (path : System.FilePath) (st : Stats) : IO Stats := do
  let data ← IO.FS.readBinFile path
  match parseExportExt data with
  | .error _ => return { st with parseErrors := st.parseErrors + 1 }
  | .ok (e, ext) =>
    let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
    let base : PassEnv :=
      { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
        pgohot := e.pgohot, config := e.config, typs, typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
        tables := {}, frontend := e.frontendTables, ptrCache := ptrCacheFn e.ptrCache
        typeLink := typeLinkFn e.typeLink }
    let mut st := st
    let mut tables : Tables := {}
    let mut prev : Tables := {}
    for h : k in [0:e.sections.size] do
      let s := e.sections[k]
      prev := tables
      tables := tables.addAll s.defs
      if k == 0 then continue
      let name := s.pass.toStringLossy
      let some pi := passes.findIdx? (·.1 == name) | continue
      let env := { base with passName := name, tables := prev
                             zvar := zvarFn e.sections[k-1]!.zvar
                             dclLen := (ext.dclLen? (k-1)).getD 0 }
      let f := e.sections[k-1]!.func
      let mut c : Cnt := { secs := 1 }
      match passes[pi]!.2 env f with
      | .error _ => c := { c with errors := 1 }
      | .ok out =>
        let g := out.func
        let ce : CheckEnv := { tabs := prev, typs }
        let okf := (check ce f).toBool
        let okg := (check ce g).toBool
        c := { c with inFails := if okf then 0 else 1, outFails := if okf && !okg then 1 else 0 }
        if okf && okg then
          let changed := g.blockTab != f.blockTab || g.valueTab != f.valueTab
          let licm := name == "loop invariant"
          let f0 := if licm then unhoist f g else f
          let ok := okCert f0 g
          -- loop invariant: `f` to `unhoist f g` by `critRelB`, then `moveB`
          let pre : Option String :=
            if !licm then none
            else if !(check ce f0).toBool then some "unhoist fails check"
            else if !GoFV.Proof.Crit.critRelB f f0 then some "critRelB"
            else none
          let w := pre <|> why ok f0 g
          let acc := (!licm || ((check ce f0).toBool && GoFV.Proof.Crit.critRelB f f0)) &&
            moveWith ok f0 g
          if acc != w.isNone then st := { st with bugs := st.bugs + 1 }
          c := { c with checked := 1, changed := if changed then 1 else 0
                        accepted := if acc then 1 else 0
                        acceptedChanged := if acc && changed then 1 else 0 }
          if let some r := w then
            let key := s!"{name}: {r}"
            st := { st with whys := st.whys.insert key (st.whys.getD key 0 + 1) }
            if !st.examples.contains key then
              st := { st with examples := st.examples.insert key s!"{path} section {k - 1}" }
          if acc && changed && listedCount f < 40 then
            st := { st with cands := st.cands.push (name, listedCount f, s!"{path} section {k - 1}") }
      st := { st with cnt := st.cnt.modify pi (·.add c) }
    return st

def main (args : List String) : IO UInt32 := do
  let (jobs, paths) := match args with
    | "--jobs" :: n :: rest => (max (n.toNat?.getD 1) 1, rest)
    | rest => (1, rest)
  let mut files := #[]
  for a in paths do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let tasks ← (List.range jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st : Stats := {}
    for h : i in [0:files.size] do
      if i % jobs == j then st ← checkFile files[i] st
    return st
  let mut st : Stats := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 2
  IO.println s!"files {files.size}, parse errors {st.parseErrors}, probe bugs {st.bugs}"
  for h : i in [0:passes.size] do
    let x := st.cnt[i]!
    IO.println s!"{passes[i].1}: sections {x.secs}, pass errors {x.errors}, input fails check {x.inFails}, output (only) fails check {x.outFails}, both checked {x.checked}, changed {x.changed}, moveB accepts {x.accepted} (changed {x.acceptedChanged}), rejects {x.checked - x.accepted}"
  IO.println "rejections (first failing condition):"
  for (k, n) in st.whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}   e.g. {st.examples.getD k ""}"
  IO.println "witness candidates (changed, accepted), smallest first:"
  for (n, sz, l) in ((st.cands.qsort (fun a b => a.2.1 < b.2.1)).extract 0 24) do
    IO.println s!"  {n}: {sz} values: {l}"
  return 0

end GoFVTest.MoveProbe

def main (args : List String) : IO UInt32 := GoFVTest.MoveProbe.main args
