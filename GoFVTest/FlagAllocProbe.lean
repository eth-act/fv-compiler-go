import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.FlagAlloc
import GoFV.Proof.Pass.FlagAllocLCheck
import GoFVTest.Parity.Compare

open scoped GoFV.SSA.Sem.Fixed

/-!
# `lake exe flagalloc-probe [--jobs N] <dir|file>...`: the flagalloc validator on the corpus

For every `flagalloc` section (input: the previous section), runs the Lean pass on the input and
counts the sections, those whose input and output pass `check`, those the pass changed, and
those `flagAllocB` accepts; reports the first failing condition by count and small witness
candidates (changed and accepted).
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Proof GoFV.Proof.FlagAllocL
  GoFVTest.Parity

namespace GoFVTest.FlagAllocProbe

def opName (f : Func) (x : ID) : String := ((f.value? x).map (·.op.exportName)).getD "?"

/-- The first failing condition of `walkB` (mirrors it). -/
def walkWhy (dc : Cert) (f g : Func) (cert : Array (Option ID)) (b : ID) (fb gb : Block) :
    List ID → List ID → List ID → List (ID × ID) → Option String
  | z :: LF, LG, P, C =>
    if !gb.values.contains z then
      if !remOK f z then some s!"removed not pure ({opName f z})"
      else if !topoOK f (z :: LF) z then some "f order not a schedule"
      else walkWhy dc f g cert b fb gb LF LG (z :: P) C
    else
      match LG with
      | [] => some "g ends early"
      | x :: LG' =>
        if fb.values.contains x then
          if x != z then some "kept order"
          else if !keptOK f g C x then some s!"kept value not related ({opName f x})"
          else if !topoOK f (z :: LF) z then some "f order not a schedule"
          else walkWhy dc f g cert b fb gb LF LG' (z :: P) C
        else
          match cert.getD x none with
          | some o =>
            if !cloneOK dc f g b P C x o then some s!"clone ({opName g x})"
            else walkWhy dc f g cert b fb gb (z :: LF) LG' P ((x, o) :: C)
          | none => some s!"clone without original ({opName g x})"
  | [], x :: LG', P, C =>
    if fb.values.contains x then some "g kept value after f's end"
    else match cert.getD x none with
      | some o =>
        if !cloneOK dc f g b P C x o then some s!"end clone ({opName g x})"
        else walkWhy dc f g cert b fb gb [] LG' P ((x, o) :: C)
      | none => some s!"end clone without original ({opName g x})"
  | [], [], _, C => if ctrlsOK f g fb gb C then none else some "controls"
termination_by LF LG => LF.length + LG.length

/-- The first failing condition of `flagAllocWith`, `none` if it accepts. -/
def why (tabs : Tables) (cert : Array (Option ID)) (f g : Func) : Option String := Id.run do
  if g.entry != f.entry then return some "entry"
  if g.blocks != f.blocks then return some "blocks"
  if g.ownAux != f.ownAux then return some "ownAux"
  if g.lowered != f.lowered then return some "lowered"
  let dc := make f
  for b in f.blocks do
    let (some fb, some gb) := (f.block? b, g.block? b) | return some "block missing"
    if !ownB g b gb then return some "g block not well formed (ownB)"
    if gb.kind != fb.kind then return some "kind"
    if gb.auxInt != fb.auxInt then return some "auxInt"
    if gb.succs != fb.succs then return some "succs"
    if gb.preds != fb.preds then return some "preds"
    if !phisOK f g fb gb then return some "phis"
    let LF := fb.values.filter (!isPhiIn f ·)
    let LG := gb.values.filter (!isPhiIn g ·)
    let oF := schedOrder f (Ctx.makeL tabs f).tys fb
    if schedOrder g (Ctx.makeL tabs g).tys gb != some LG then return some "g order not a schedule"
    if !(oF == none || oF == some LF) then return some "f schedOrder"
    if let some r := walkWhy dc f g cert b fb gb LF.toList LG.toList [] [] then return some r
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
  clones : Nat := 0
  deriving Inhabited

def Cnt.add (a b : Cnt) : Cnt :=
  { secs := a.secs + b.secs, errors := a.errors + b.errors, inFails := a.inFails + b.inFails
    outFails := a.outFails + b.outFails, checked := a.checked + b.checked
    changed := a.changed + b.changed, accepted := a.accepted + b.accepted
    acceptedChanged := a.acceptedChanged + b.acceptedChanged, clones := a.clones + b.clones }

structure Stats where
  cnt : Cnt := {}
  whys : Std.HashMap String Nat := {}
  examples : Std.HashMap String String := {}
  cloneOps : Std.HashMap String Nat := {}
  cands : Array (Nat × String) := #[]
  parseErrors : Nat := 0
  bugs : Nat := 0

def Stats.merge (a b : Stats) : Stats :=
  { cnt := a.cnt.add b.cnt
    whys := b.whys.fold (fun m k n => m.insert k (m.getD k 0 + n)) a.whys
    examples := b.examples.fold (fun m k e => if m.contains k then m else m.insert k e) a.examples
    cloneOps := b.cloneOps.fold (fun m k n => m.insert k (m.getD k 0 + n)) a.cloneOps
    cands := a.cands ++ b.cands
    parseErrors := a.parseErrors + b.parseErrors, bugs := a.bugs + b.bugs }

def listedCount (f : Func) : Nat :=
  f.blocks.foldl (fun n bid => n + (((f.block? bid).map (·.values.size)).getD 0)) 0

/-- The clones of `g` (values of a block not in `f`'s), by op. -/
def clonesOf (f g : Func) : Array String := Id.run do
  let mut r := #[]
  for b in g.blocks do
    let (some fb, some gb) := (f.block? b, g.block? b) | continue
    for x in gb.values do
      if !fb.values.contains x then r := r.push (opName g x)
  return r

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
      if name != "flagalloc" then continue
      let env := { base with passName := name, tables := prev
                             zvar := zvarFn e.sections[k-1]!.zvar
                             dclLen := (ext.dclLen? (k-1)).getD 0 }
      let f := e.sections[k-1]!.func
      let mut c : Cnt := { secs := 1 }
      match flagallocPass env f with
      | .error _ => c := { c with errors := 1 }
      | .ok out =>
        let g := out.func
        let ce : CheckEnv := { tabs := prev, typs }
        let okf := (check ce f).toBool
        let okg := (check ce g).toBool
        c := { c with inFails := if okf then 0 else 1, outFails := if okf && !okg then 1 else 0 }
        if okf then
          let changed := g.blockTab != f.blockTab || g.valueTab != f.valueTab
          let cert := origCert f g
          let acc := flagAllocWith out.tables cert f g
          let w := why out.tables cert f g
          if acc != w.isNone then st := { st with bugs := st.bugs + 1 }
          let cl := clonesOf f g
          for op in cl do st := { st with cloneOps := st.cloneOps.insert op (st.cloneOps.getD op 0 + 1) }
          c := { c with checked := 1, changed := if changed then 1 else 0
                        accepted := if acc then 1 else 0
                        acceptedChanged := if acc && changed then 1 else 0, clones := cl.size }
          if let some r := w then
            st := { st with whys := st.whys.insert r (st.whys.getD r 0 + 1) }
            if !st.examples.contains r then
              st := { st with examples := st.examples.insert r s!"{path} section {k - 1}" }
          if acc && cl.size > 0 && listedCount f < 40 then
            st := { st with cands := st.cands.push (listedCount f, s!"{path} section {k - 1} ({cl.size} clones)") }
      st := { st with cnt := st.cnt.add c }
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
  let x := st.cnt
  IO.println s!"flagalloc: sections {x.secs}, pass errors {x.errors}, input fails check {x.inFails}, output (only) fails check {x.outFails} (not needed), input checked {x.checked}, changed {x.changed}, flagAllocB accepts {x.accepted} (changed {x.acceptedChanged}), rejects {x.checked - x.accepted}, clones {x.clones}"
  IO.println "clone ops:"
  for (k, n) in st.cloneOps.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  IO.println "rejections (first failing condition):"
  for (k, n) in st.whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}   e.g. {st.examples.getD k ""}"
  IO.println "witness candidates (accepted, with clones), smallest first:"
  for (sz, l) in ((st.cands.qsort (fun a b => a.1 < b.1)).extract 0 24) do
    IO.println s!"  {sz} values: {l}"
  return 0

end GoFVTest.FlagAllocProbe

def main (args : List String) : IO UInt32 := GoFVTest.FlagAllocProbe.main args
