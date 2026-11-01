import GoFVTest.Parity.Registry
import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.Opt.ExpandCallsCheck
import GoFV.Opt.TabsAgree

/-!
# `expand-calls-probe`

For every corpus section whose pass is `expand calls`, run the Lean pass on the previous
section's function and tables and count whether its output is in the fragment of
`GoFV.Proof.EC.expandCalls_refines`: `ECCheck.ecCheck out.tables f out.func` and
`tabsAgree prev out.tables f`. Rejections print the first failing condition (per class of
source value).

usage: `expand-calls-probe [--jobs N] <dir|file>...`
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ECCheck

namespace GoFVTest.ExpandCallsProbe

/-- The class name of source value `u`. -/
def className (f g : Func) (u w : Value) : String :=
  if (callOpMap u.op).isSome then s!"call {u.op.name}"
  else if u.op == .MakeResult then "result"
  else if u.op == .SelectN && u.args.size == 1 && converted f u.args[0]! then "select"
  else if u.op == .Arg && !identOK f g u w then "arg"
  else s!"ident {u.op.name}→{w.op.name}"

/-- Why `piecesOK` fails. -/
partial def piecesWhy (tabs : Tables) (sh : Array Ty) (f g : Func) :
    List ABIParam → List ID → List ID → String
  | [], [], [] => "ok"
  | p :: ps, a :: as, pcs =>
    let t := tabs.ty p.type
    let paths := leafPaths t
    if !eqE (shapeOf sh f a) t then
      let op := ((f.value? a).map (·.op.name)).getD "?"
      s!"arg shape ({op}) {repr (erase (shapeOf sh f a))} vs {repr (erase t)}"
    else if paths.length > pcs.length then "too few pieces"
    else if !(paths.zip (pcs.take paths.length)).all (fun (π, q) => chainOK sh g (isNewB f) π.reverse q a) then
      match g.value? a with
      | some aw => if aw.op == .IMake then "chain (IMake shortcut)" else s!"chain (arg {aw.op.name})"
      | none => "chain"
    else piecesWhy tabs sh f g ps as (pcs.drop paths.length)
  | [], _, _ => "extra args/pieces"
  | _, [], _ => "missing args"

/-- Why the call class fails. -/
def callWhy (tabs : Tables) (sh : Array Ty) (f g : Func) (u w : Value) : String :=
  match callOpMap u.op, callABI? tabs u.aux with
  | some (op, k), some abi =>
    let ins := insOf abi
    let outs := outsOf abi
    let n := u.args.size
    if !(w.op == op) then "op"
    else if !regParamsOK tabs abi.params.toList then
      if abi.params.toList.any (·.regs.isEmpty) then "stack param"
      else if abi.params.toList.any (fun p => !GoFV.Proof.ABI.wf (tabs.ty p.type)) then "param shape not wf"
      else "regs ≠ leaves"
    else if !piecesOK tabs sh f g ins (u.args.extract k (n - 1)).toList
        (w.args.extract k (w.args.size - 1)).toList then
      s!"pieces: {piecesWhy tabs sh f g ins (u.args.extract k (n - 1)).toList
        (w.args.extract k (w.args.size - 1)).toList}"
    else if !tupleOf (outs.map (tabs.ty ·.type)) (valueTy sh (some u)) then "source tuple type"
    else if !regTupleOf (leafTys tabs outs) (valueTy sh (some w)) then "register types"
    else "other"
  | _, none => "no ABI"
  | _, _ => "?"

def valueWhy (tabs : Tables) (sh : Array Ty) (f g : Func) (x : ID) : String :=
  match f.value? x, g.value? x with
  | some u, some w =>
    let c := className f g u w
    if c.startsWith "call" then s!"{c}: {callWhy tabs sh f g u w}"
    else if c == "result" then
      let outs := ownOuts tabs f
      let n := u.args.size
      if !piecesOK tabs sh f g outs (u.args.extract 0 (n - 1)).toList
          (w.args.extract 0 (w.args.size - 1)).toList then
        s!"result: pieces: {piecesWhy tabs sh f g outs (u.args.extract 0 (n - 1)).toList
          (w.args.extract 0 (w.args.size - 1)).toList}"
      else "result: types"
    else c
  | _, _ => "absent"

def blockWhy (tabs : Tables) (sh : Array Ty) (f g : Func) (bid : ID) : String := Id.run do
  let some fb := f.block? bid | return "no source block"
  let some gb := g.block? bid | return "no target block"
  if gb.kind != fb.kind || gb.controls != fb.controls then return "kind/controls"
  if !fb.values.all (fun x => gb.values.contains x) then return "source value moved/removed"
  for x in fb.values do
    if let some u := f.value? x then
      if u.op != .Phi && !valueOK tabs sh f g x then return valueWhy tabs sh f g x
  let nodeG : ID → Bool := fun x => gb.values.contains x &&
    match g.value? x with
    | some w => w.op != .Phi
    | none => false
  for x in fb.values do
    if converted f x then
      if let some u := f.value? x then
        if !u.args.all (fun a => imkArgOK sh g nodeG (gb.values.size + 1) a x) then
          return "IMake arg not held"
  if !((fb.kind != .If && fb.kind != .JumpTable) || fb.controls.all (fun c => !special f g c)) then
    return "converted control"
  match schedule f fb, schedule g gb with
  | some of, some og =>
    if of.toList.filter (npOf f fb) != og.toList.filter (npOf f fb) then return "schedule"
  | _, _ => return "no schedule"
  for z in gb.values do
    if let some w := g.value? z then
      if isNewB f z && !newEvalB tabs g w then return s!"new op {w.op.name}"
      if !w.args.all (fun a => !isNewB f a || gb.values.contains a || (valsOf g g.entry).contains a) then
        return if isNewB f z then "new arg in other block" else "new arg of source value in other block"
  for x in gb.values do
    if let some w := g.value? x then
      if w.op == .Phi then
        if !(fb.values.contains x && match f.value? x with
            | some u => sameV u w
            | none => false) then return "phi changed"
  for x in fb.values do
    if let some u := f.value? x then
      if u.op == .Phi && u.args.any (special f g) then return "phi of converted"
  return "feeds"

def why (tabs : Tables) (f g : Func) : String := Id.run do
  let sh := typeShapes tabs
  let outs := ownOuts tabs f
  if DomCert.cfgView g != DomCert.cfgView f then return "cfg"
  if g.ownAux != f.ownAux then return "ownAux"
  if !regParamsOK tabs outs then
    return if outs.any (·.regs.isEmpty) then "own: stack result" else "own: result shape"
  for b in f.blocks do
    if !blockOK tabs sh f g b then return blockWhy tabs sh f g b
  return "?"

structure Stats where
  files : Nat := 0
  parseErrors : Nat := 0
  sections : Nat := 0
  passErrors : Nat := 0
  ok : Nat := 0
  tabsFail : Nat := 0
  whys : Array (String × Nat) := #[]
  examples : Array (String × String) := #[]

def Stats.addWhy (st : Stats) (key ex : String) : Stats :=
  match st.whys.findIdx? (·.1 == key) with
  | some i => { st with whys := st.whys.modify i fun (k, n) => (k, n + 1) }
  | none => { st with whys := st.whys.push (key, 1), examples := st.examples.push (key, ex) }

def Stats.merge (a b : Stats) : Stats := Id.run do
  let mut st := { a with files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors
                         sections := a.sections + b.sections, passErrors := a.passErrors + b.passErrors
                         ok := a.ok + b.ok, tabsFail := a.tabsFail + b.tabsFail }
  for (k, n) in b.whys do
    st := match st.whys.findIdx? (·.1 == k) with
      | some i => { st with whys := st.whys.modify i fun (k, m) => (k, m + n) }
      | none => { st with whys := st.whys.push (k, n) }
  for (k, ex) in b.examples do
    if (st.examples.findIdx? (·.1 == k)).isNone then st := { st with examples := st.examples.push (k, ex) }
  return st

def checkFile (path : System.FilePath) (st : Stats) : IO Stats := do
  let data ← IO.FS.readBinFile path
  let st := { st with files := st.files + 1 }
  match parseExport data with
  | .error _ => return { st with parseErrors := st.parseErrors + 1 }
  | .ok e =>
    let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
    let base : PassEnv :=
      { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
        pgohot := e.pgohot, config := e.config, typs
        typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
        tables := {}, frontend := e.frontendTables
        ptrCache := GoFVTest.Parity.ptrCacheFn e.ptrCache }
    let mut st := st
    let mut tables : Tables := {}
    let mut prev : Tables := {}
    for h : k in [0:e.sections.size] do
      let s := e.sections[k]
      prev := tables
      tables := tables.addAll s.defs
      if k == 0 then continue
      if s.pass.toStringLossy != "expand calls" then continue
      let env := { base with passName := "expand calls", tables := prev
                             zvar := GoFVTest.Parity.zvarFn e.sections[k-1]!.zvar }
      let f := e.sections[k-1]!.func
      st := { st with sections := st.sections + 1 }
      match expandCallsPass env f with
      | .error _ => st := { st with passErrors := st.passErrors + 1 }
      | .ok out =>
        if !tabsAgree prev out.tables f then st := { st with tabsFail := st.tabsFail + 1 }
        else if ecCheck out.tables f out.func then st := { st with ok := st.ok + 1 }
        else
          let w := why out.tables f out.func
          st := st.addWhy w s!"{path} section {k}"
    return st

def ssaFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "ssa")).qsort (·.toString < ·.toString)
  else return #[p]

partial def parseArgs : List String → Nat × Array String → Nat × Array String
  | [], o => o
  | "--jobs" :: n :: rest, (_, ps) => parseArgs rest (max (n.toNat?.getD 1) 1, ps)
  | a :: rest, (j, ps) => parseArgs rest (j, ps.push a)

def main (args : List String) : IO UInt32 := do
  let (jobs, paths) := parseArgs args (1, #[])
  let mut files := #[]
  for p in paths do files := files ++ (← ssaFiles p)
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
  IO.println s!"files {st.files}, parse errors {st.parseErrors}"
  IO.println s!"expand calls sections {st.sections}, pass errors {st.passErrors}, tabsAgree fails {st.tabsFail}, accepted {st.ok}, rejected {st.sections - st.passErrors - st.tabsFail - st.ok}"
  let whys := st.whys.qsort fun x y => x.2 > y.2
  for (k, n) in whys do IO.println s!"REJECT {n}: {k}"
  for (k, ex) in st.examples.qsort (fun a b => a.1 < b.1) do IO.println s!"EXAMPLE {k}: {ex}"
  return 0

end GoFVTest.ExpandCallsProbe

def main (args : List String) : IO UInt32 := GoFVTest.ExpandCallsProbe.main args
