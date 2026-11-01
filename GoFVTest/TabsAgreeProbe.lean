import GoFVTest.Parity.Registry
import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.Opt.TabsAgree

/-!
# `tabs-agree-probe`

For every corpus section whose pass is `expand calls`, `decompose user` or `decompose builtin`,
run the registered Lean pass on the previous section's function and tables and count whether
`GoFV.Opt.tabsAgree prev out.tables f` holds (the source runs the same in the extended tables,
`GoFV.Proof.run_tabsAgree`) and whether `GoFV.Opt.tabsAgreeMod` (extra frame temporaries
allowed, `GoFV.Proof.run_tabsAgreeMod`) does. The stock output tables (the tables in force for
section `k`) are counted too, as are the sections whose function keeps its values and blocks
(only the tables change). `tabsAgreeMod` failures print the first failing condition.

usage: `tabs-agree-probe [--jobs N] <dir|file>...`
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

namespace GoFVTest.TabsAgreeProbe

/-- The first condition of `tabsAgreeMod tabs tabs' f` that fails (for the report). -/
def whyMod (tabs tabs' : Tables) (f : Func) : String := Id.run do
  let ps := abiParams tabs f
  let params := (ps.filter (!·.out)).map (·.name)
  let ls := frameLocals tabs params
  let ls' := frameLocals tabs' params
  if (abiParams tabs' f).toList != ps.toList then return "abiParams"
  for p in ps do
    if !Ty.beq (tabs'.ty p.type) (tabs.ty p.type) then return s!"abiParam type t{p.type}"
  if ls'.toList.filter (fun l => (tabs.aux? l.1).isSome) != ls.toList then
    return "frameLocals (old entries changed)"
  for l in ls' do
    if (tabs.aux? l.1).isNone && tabs'.forgeable l.1 then
      let k := match tabs'.aux? l.1 with
        | some { kind := .name _ cls _ _ _ fl _, .. } => s!"{repr cls}{if fl.addrtaken then " addrtaken" else ""}"
        | _ => "?"
      return s!"forgeable extra ({k})"
  for l in ls do
    if tabs'.forgeable l.1 != tabs.forgeable l.1 then return s!"forgeable a{l.1}"
  if outargsSize tabs' != outargsSize tabs then
    return s!"outargsSize {outargsSize tabs} -> {outargsSize tabs'}"
  let sh := typeShapes tabs
  let sh' := typeShapes tabs'
  for o in f.valueTab do
    if !Ty.beq (valueTy sh' o) (valueTy sh o) then
      return s!"value type"
    if !valueAuxAgree tabs tabs' o then
      let a := (o.bind (·.aux)).getD 0
      let part :=
        if tabs'.aux? a != tabs.aux? a then "aux"
        else if tabs'.callee? a != tabs.callee? a then "callee"
        else if !Ty.beq (auxTy tabs' (some a)) (auxTy tabs (some a)) then "auxTy"
        else "abi types"
      return s!"value aux: {part}"
  return "?"

/-- The extra frame variables of `tabs'` come after every frame variable of `tabs`. -/
def extrasSuffix (tabs tabs' : Tables) (f : Func) : Bool :=
  let ps := abiParams tabs f
  let params := (ps.filter (!·.out)).map (·.name)
  let ls' := (frameLocals tabs' params).toList
  let olds := ls'.filter fun l => (tabs.aux? l.1).isSome
  ls'.take olds.length == olds

/-- Per-pass counters. -/
structure Cnt where
  sections : Nat := 0
  passErrors : Nat := 0
  /-- `tabsAgree` against the Lean pass's output tables, against the stock tables. -/
  agree : Nat := 0
  agreeStock : Nat := 0
  /-- `tabsAgreeMod` against the Lean output tables, against the stock tables. -/
  mod : Nat := 0
  modStock : Nat := 0
  /-- Sections whose function keeps `valueTab`, `blockTab`, `blocks` and `entry` (only the
  tables change), and among them those where `tabsAgreeMod` holds. -/
  same : Nat := 0
  sameMod : Nat := 0
  /-- `tabsAgreeMod` holds but not `tabsAgree`, extras interleaved (not a suffix). -/
  interleaved : Nat := 0
  deriving Inhabited

def Cnt.add (a b : Cnt) : Cnt :=
  { sections := a.sections + b.sections, passErrors := a.passErrors + b.passErrors
    agree := a.agree + b.agree, agreeStock := a.agreeStock + b.agreeStock
    mod := a.mod + b.mod, modStock := a.modStock + b.modStock
    same := a.same + b.same, sameMod := a.sameMod + b.sameMod
    interleaved := a.interleaved + b.interleaved }

structure Stats where
  files : Nat := 0
  parseErrors : Nat := 0
  counts : Array (String × Cnt) := #[]
  /-- Failure reasons (pass, which tables, first failing condition) with counts. -/
  whys : Array (String × Nat) := #[]
  examples : Array String := #[]

def passes : Array String := #["expand calls", "decompose user", "decompose builtin"]

def Stats.bump (st : Stats) (i : Nat) (g : Cnt → Cnt) : Stats :=
  { st with counts := st.counts.modify i fun (n, c) => (n, g c) }

def Stats.addWhy (st : Stats) (key ex : String) : Stats :=
  let whys := match st.whys.findIdx? (·.1 == key) with
    | some i => st.whys.modify i fun (k, n) => (k, n + 1)
    | none => st.whys.push (key, 1)
  let examples := if (st.whys.findIdx? (·.1 == key)).isNone then st.examples.push ex
    else st.examples
  { st with whys, examples }

def Stats.merge (a b : Stats) : Stats := Id.run do
  let mut st := { a with files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors
                         examples := a.examples ++ b.examples
                         counts := (a.counts.zip b.counts).map fun ((n, x), (_, y)) => (n, x.add y) }
  for (k, n) in b.whys do
    st := match st.whys.findIdx? (·.1 == k) with
      | some i => { st with whys := st.whys.modify i fun (k, m) => (k, m + n) }
      | none => { st with whys := st.whys.push (k, n) }
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
      let name := s.pass.toStringLossy
      let some pi := passes.findIdx? (· == name) | continue
      let some entry := GoFVTest.Parity.registry.find? (·.names.contains name) | continue
      let env := { base with passName := name, tables := prev
                             zvar := GoFVTest.Parity.zvarFn e.sections[k-1]!.zvar }
      let f := e.sections[k-1]!.func
      st := st.bump pi fun c => { c with sections := c.sections + 1 }
      -- stock output tables
      if tabsAgree prev tables f then st := st.bump pi fun c => { c with agreeStock := c.agreeStock + 1 }
      if tabsAgreeMod prev tables f then st := st.bump pi fun c => { c with modStock := c.modStock + 1 }
      match entry.run env f with
      | .error _ => st := st.bump pi fun c => { c with passErrors := c.passErrors + 1 }
      | .ok out =>
        let g := out.func
        let same := g.valueTab == f.valueTab && g.blockTab == f.blockTab &&
          g.blocks == f.blocks && g.entry == f.entry
        let ag := tabsAgree prev out.tables f
        let md := tabsAgreeMod prev out.tables f
        if ag then st := st.bump pi fun c => { c with agree := c.agree + 1 }
        if md then st := st.bump pi fun c => { c with mod := c.mod + 1 }
        if same then st := st.bump pi fun c => { c with same := c.same + 1 }
        if same && md then st := st.bump pi fun c => { c with sameMod := c.sameMod + 1 }
        if md && !ag && !extrasSuffix prev out.tables f then
          st := st.bump pi fun c => { c with interleaved := c.interleaved + 1 }
        if !md then
          let w := whyMod prev out.tables f
          st := st.addWhy s!"{name} mod: {w}" s!"{name} mod {path} section {k}: {w}"
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
  let empty : Stats := { counts := passes.map fun n => (n, {}) }
  let tasks ← (List.range jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st := empty
    for h : i in [0:files.size] do
      if i % jobs == j then st ← checkFile files[i] st
    return st
  let mut st := empty
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 2
  IO.println s!"files {st.files}, parse errors {st.parseErrors}"
  IO.println "| pass | sections | pass errors | tabsAgree (Lean tables) | tabsAgreeMod (Lean tables) | tabsAgree (stock) | tabsAgreeMod (stock) | function unchanged | unchanged + tabsAgreeMod | mod-only, extras interleaved |"
  IO.println "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"
  for (n, c) in st.counts do
    IO.println s!"| {n} | {c.sections} | {c.passErrors} | {c.agree} | {c.mod} | {c.agreeStock} | {c.modStock} | {c.same} | {c.sameMod} | {c.interleaved} |"
  let whys := st.whys.qsort fun x y => x.2 > y.2
  for (k, n) in whys do IO.println s!"FAIL {n}: {k}"
  for ex in st.examples.qsort (· < ·) |>.extract 0 40 do IO.println s!"EXAMPLE {ex}"
  return 0

end GoFVTest.TabsAgreeProbe

def main (args : List String) : IO UInt32 := GoFVTest.TabsAgreeProbe.main args
