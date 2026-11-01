import GoFVTest.Parity.Registry
import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.Opt.TabsAgree

/-!
# `tabs-agree-probe`

For every corpus section whose pass is `expand calls`, `decompose user` or `decompose builtin`,
run the registered Lean pass on the previous section's function and tables and count whether
`GoFV.Opt.tabsAgree prev out.tables f` holds (the source runs the same in the extended tables,
`GoFV.Proof.run_tabsAgree`). The stock output tables (the tables in force for section `k`) are
counted too. Failures print the first failing condition.

usage: `tabs-agree-probe [--jobs N] <dir|file>...`
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

namespace GoFVTest.TabsAgreeProbe

/-- The first condition of `tabsAgree tabs tabs' f` that fails (for the report). -/
def why (tabs tabs' : Tables) (f : Func) : String := Id.run do
  let ps := abiParams tabs f
  let params := (ps.filter (!·.out)).map (·.name)
  let ls := frameLocals tabs params
  if (abiParams tabs' f).toList != ps.toList then return "abiParams"
  for p in ps do
    if !Ty.beq (tabs'.ty p.type) (tabs.ty p.type) then return s!"abiParam type t{p.type}"
  let ls' := frameLocals tabs' params
  if ls'.toList != ls.toList then
    let extra := ls'.toList.filter (!ls.toList.contains ·)
    let gone := ls.toList.filter (!ls'.toList.contains ·)
    let fmtL (l : AuxRef × Nat × Option Nat) : String :=
      let k := match tabs'.aux? l.1 with
        | some { kind := .name s cls .., .. } => s!"{s.toStringLossy}:{repr cls}"
        | _ => "?"
      s!"a{l.1}({k},{l.2.1})"
    return s!"frameLocals +{extra.map fmtL} -{gone.map fmtL}"
  for l in ls do
    if tabs'.forgeable l.1 != tabs.forgeable l.1 then return s!"forgeable a{l.1}"
  if outargsSize tabs' != outargsSize tabs then
    return s!"outargsSize {outargsSize tabs} -> {outargsSize tabs'}"
  let sh := typeShapes tabs
  let sh' := typeShapes tabs'
  for o in f.valueTab do
    if !Ty.beq (valueTy sh' o) (valueTy sh o) then
      return s!"value type v{(o.map (·.id)).getD 0}"
    if !valueAuxAgree tabs tabs' o then
      let a := (o.bind (·.aux)).getD 0
      let part :=
        if tabs'.aux? a != tabs.aux? a then "aux"
        else if tabs'.callee? a != tabs.callee? a then "callee"
        else if !Ty.beq (auxTy tabs' (some a)) (auxTy tabs (some a)) then "auxTy"
        else "abi types"
      return s!"v{(o.map (·.id)).getD 0} aux a{a}: {part}"
  return "?"

structure Stats where
  files : Nat := 0
  parseErrors : Nat := 0
  /-- Per pass name: sections, pass errors, agree (Lean output tables), fail, agree (stock
  tables), fail. -/
  counts : Array (String × Nat × Nat × Nat × Nat × Nat × Nat) := #[]
  /-- Failure reasons (pass, which tables, first failing condition) with counts. -/
  whys : Array (String × Nat) := #[]
  examples : Array String := #[]

def passes : Array String := #["expand calls", "decompose user", "decompose builtin"]

def Stats.bump (st : Stats) (i : Nat) (g : Nat × Nat × Nat × Nat × Nat × Nat →
    Nat × Nat × Nat × Nat × Nat × Nat) : Stats :=
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
                         counts := (a.counts.zip b.counts).map fun ((n, x), (_, y)) =>
                           (n, x.1 + y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2.1 + y.2.2.2.1,
                             x.2.2.2.2.1 + y.2.2.2.2.1, x.2.2.2.2.2 + y.2.2.2.2.2) }
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
      st := st.bump pi fun (n, er, a, b, c, d) => (n + 1, er, a, b, c, d)
      -- stock output tables
      if tabsAgree prev tables f then st := st.bump pi fun (n, er, a, b, c, d) => (n, er, a, b, c + 1, d)
      else
        st := st.bump pi fun (n, er, a, b, c, d) => (n, er, a, b, c, d + 1)
        let w := why prev tables f
        st := st.addWhy s!"{name} stock: {w}" s!"{name} stock {path} section {k}: {w}"
      match entry.run env f with
      | .error _ => st := st.bump pi fun (n, er, a, b, c, d) => (n, er + 1, a, b, c, d)
      | .ok out =>
        if tabsAgree prev out.tables f then
          st := st.bump pi fun (n, er, a, b, c, d) => (n, er, a + 1, b, c, d)
        else
          st := st.bump pi fun (n, er, a, b, c, d) => (n, er, a, b + 1, c, d)
          let w := why prev out.tables f
          st := st.addWhy s!"{name} lean: {w}" s!"{name} lean {path} section {k}: {w}"
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
  let empty : Stats := { counts := passes.map fun n => (n, 0, 0, 0, 0, 0, 0) }
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
  IO.println "| pass | sections | pass errors | agree (Lean tables) | fail | agree (stock tables) | fail |"
  IO.println "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"
  for (n, c, er, a, b, sa, sb) in st.counts do
    IO.println s!"| {n} | {c} | {er} | {a} | {b} | {sa} | {sb} |"
  let whys := st.whys.qsort fun x y => x.2 > y.2
  for (k, n) in whys do IO.println s!"FAIL {n}: {k}"
  for ex in st.examples.qsort (· < ·) |>.extract 0 40 do IO.println s!"EXAMPLE {ex}"
  return 0

end GoFVTest.TabsAgreeProbe

def main (args : List String) : IO UInt32 := GoFVTest.TabsAgreeProbe.main args
