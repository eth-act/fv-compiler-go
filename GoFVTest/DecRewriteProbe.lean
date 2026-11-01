import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.Opt.Decompose
import GoFV.Opt.RewriteCheck
import GoFV.Rules.Proven

/-!
# `dec-rewrite-probe`: the dec rules of "decompose builtin" and the rewrite validator (#17)

For every `decompose builtin` section of the given export files: the rewrite step of
`postExpandCallsDecomposePass` alone (input: the function after `decomposeUser` and the builtin
phi splits, `Decompose.lean:229`; output: `rewritePass decTable false`), run with its log under
three rule tables — all dec rules, the dec rules with a merged lemma (`GoFV.Rules.Proven.dec`),
none — and for each table:

- `fire`: sections where some rule fired;
- `acc`: `RewriteCheck.accepts` holds for the step (the validator `checkedRewrite` uses);
- `par`: the whole pass with this table is at stock;
- `chk`: the whole pass with the checked step (the step's result if accepted, else its input)
  is at stock.

Per dec rule (`file:line Op`): firings, and for the full table the first condition of
`RewriteCheck.ruleOK` that fails at each firing (replayed as `firedKeys` of `rule-fire-probe`,
without the copy-argument checks).

usage: `dec-rewrite-probe [--jobs N] <dir|file>...`
-/

open GoFV.SSA GoFV.Opt GoFV.Rules GoFV.Opt.RewriteCheck GoFV.Proof.Rules

namespace GoFVTest.DecRewriteProbe

def key (r : Rule) : String := s!"{r.loc.file}:{r.loc.line} {r.op.name}"

def restrict (s : RuleSet) (keep : Rule → Bool) : RuleSet :=
  { s with values := s.values.map fun (o, rs) => (o, rs.filter keep) }

def provenKeys : List String :=
  Proven.dec.values.foldl (fun acc (_, rs) => acc ++ rs.map key) []

/-- The ptr-class dec rules (`docs/proofs/rules.md`, "Dec rules"): projections of `Make` ops
and pointer-shaped identities. -/
def ptrLines : List Nat :=
  [13, 14, 42, 43, 58, 59, 60, 61, 82, 83, 102, 103, 104, 106, 115, 116, 119, 120, 125, 126, 127]

/-- Variant name and table. -/
def variants : Array (String × Interp.Table) :=
  #[("all", Decompose.decTable),
    ("ptr", Interp.Table.ofRuleSet (restrict Generated.Dec.ruleSet fun r => ptrLines.contains r.loc.line)),
    ("proven", Interp.Table.ofRuleSet Proven.dec),
    ("none", Interp.Table.ofRuleSet (restrict Generated.Dec.ruleSet fun _ => false))]

/-- The first failing condition of `ruleOK tabs M r v defs`. -/
def why (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value) : String :=
  if makeSelShape r && makeSelOK tabs M v defs then "ok" else
  if makeSelShape r && !Pat.arityOk r.pat then "makeSelOK" else
  if !Pat.arityOk r.pat then "arity" else
  if !patOK r.pat then "patOK" else
  match M.get? v with
  | none => "no def"
  | some x =>
    if !termOp x.op then "top not a term op" else
    let res := (choices (Pat.commutes r.pat)).map fun sw =>
      match matchPat M r.pat [] v sw with
      | none => "no match (term ops, fixed arity)"
      | some (I, _) =>
        let e := env tabs M I
        let vtys := r.vars.map (·.ty)
        let σ := sigmaT tabs e r.pat
        let nodes := match r.result, defs with
          | .build ns, _ :: us => ns.zip us
          | _, _ => []
        let or := oracle vtys tabs nodes
        let ev := evalE vtys σ or e (Pat.denT tabs e [] r.pat)
        if !I.tail.all (·.2 != v) then "cyclic" else
        if !consOK ev σ e I [] r.pat then "cons" else
        if !wfOK e [] r.pat then "wf" else
        if !(match r.cond with
          | some c => match ev c with | .bool true => true | _ => false
          | none => true) then "cond" else
        let shapes := if r.op == .ITab || r.op == .IData then
          let k := if r.op == .ITab then 0 else 1
          let argOp := ((M.get? (I.at [k, 0])).map (·.op.name)).getD "?"
          s!" {reprStr (e.ty [])} <- {reprStr (e.ty [0])} <- {reprStr (e.ty [k, 0])} {argOp}"
          else ""
        if !(match r.pat with
          | .op o _ _ _ _ _ _ _ => topAll o e
          | _ => false) then "topAll" ++ shapes else
        if !Pat.argsOK e.ty [] r.pat then "argsOK" ++ shapes else
        if !leavesOK M I [] r.pat then "leavesOK" else
        if !resultOK tabs M ev or σ I r x defs then
          (if r.block.isSome then "resultOK (@b block)" else "resultOK") else
        if !nodes.all (fun (n, u) => frameNodeOK tabs ev e r.pat n u) then "frameNodeOK" else
        if !condFrameOK tabs e I r.pat r.cond then "condFrameOK" else "ok"
    if res.contains "ok" then "ok" else res.headD "no choice"

structure Stats where
  files : Nat := 0
  sections : Nat := 0
  errors : Nat := 0
  /-- Per variant: fire, acc, par, chk. -/
  counts : Array (Nat × Nat × Nat × Nat) := variants.map fun _ => (0, 0, 0, 0)
  /-- Per variant: the step's output is the full dec table's and the validator accepts it. -/
  repro : Array Nat := variants.map fun _ => 0
  /-- Sections whose full rewrite step extends the tables. -/
  tabsChanged : Nat := 0
  /-- Per rule key: firings (full table) and `ruleOK` outcomes. -/
  fires : Std.HashMap String Nat := {}
  whys : Std.HashMap (String × String) Nat := {}

def Stats.merge (a b : Stats) : Stats := Id.run do
  let mut st := { a with files := a.files + b.files, sections := a.sections + b.sections
                         errors := a.errors + b.errors
                         repro := (a.repro.zip b.repro).map fun (x, y) => x + y
                         tabsChanged := a.tabsChanged + b.tabsChanged
                         counts := (a.counts.zip b.counts).map fun ((p, q, r, s), (p', q', r', s')) =>
                           (p + p', q + q', r + r', s + s') }
  for (k, n) in b.fires do st := { st with fires := st.fires.insert k (st.fires.getD k 0 + n) }
  for (k, n) in b.whys do st := { st with whys := st.whys.insert k (st.whys.getD k 0 + n) }
  return st

/-- Rule events of the log with their keys and `why`, replayed on the input's definitions. -/
def ruleWhys (tabs : Tables) (t : Interp.Table) (f : Func) (log : Array RwEvent) :
    Array (String × String) := Id.run do
  let mut M : Defs := f.valueTab
  let mut out := #[]
  for ev in log do
    match ev with
    | .rule v i _ defs =>
      if let some x := M.get? v then
        if let some cr := (t.values[x.op.ctorIdx]?).bind (·[i]?) then
          out := out.push (key cr.rule, why tabs M cr.rule v defs.toList)
      M := defs.foldl (fun M u => M.put u.id u) M
    | .copyArg v i src =>
      if let some x := M.get? v then
        if h : i < x.args.size then M := M.put v { x with args := x.args.set i src }
    | .phielim v d => M := M.put v d
    | _ => pure ()
  return out

def checkFile (path : System.FilePath) (st : Stats) : IO Stats := do
  let data ← IO.FS.readBinFile path
  let st := { st with files := st.files + 1 }
  let .ok e := parseExport data | return st
  let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
  let base : PassEnv :=
    { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
      pgohot := e.pgohot, config := e.config, typs
      typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
      tables := {}, frontend := e.frontendTables
      ptrCache := GoFVTest.Parity.ptrCacheFn e.ptrCache }
  let mut st := st
  let mut tables : Tables := {}
  for h : k in [0:e.sections.size] do
    let s := e.sections[k]
    let prev := tables
    tables := tables.addAll s.defs
    if k == 0 then continue
    if s.pass.toStringLossy != "decompose builtin" then continue
    st := { st with sections := st.sections + 1 }
    let env := { base with passName := "decompose builtin", tables := prev
                           zvar := GoFVTest.Parity.zvarFn e.sections[k-1]!.zvar }
    let f := e.sections[k-1]!.func
    let pre : Except String (Decompose.Ctx × Decompose.St) := do
      let c ← Decompose.ctxOf env
      let s0 ← Decompose.ofFunc env.tables f
      let s1 ← Decompose.runM c (do Decompose.decomposeUser; Decompose.forEachPhi Decompose.decomposeBuiltinPhi) s0
      return (c, s1)
    let .ok (c, s1) := pre | st := { st with errors := st.errors + 1 }; continue
    let env' := { env with tables := s1.tabs }
    let finishWith (out : PassOut) : Option String :=
      match (do
        let s2 ← Decompose.runM c Decompose.builtinNames { s1 with f := out.func, tabs := out.tables }
        Decompose.finish env s2) with
      | .ok o => GoFVTest.Parity.compare prev o tables s
      | .error err => some err
    let mut full? : Option Func := none
    for h : i in [0:variants.size] do
      let (_, t) := variants[i]
      match rewriteRun t false true env' s1.f with
      | .error _ => st := { st with errors := st.errors + 1 }
      | .ok (out, n, log) =>
        let acc := accepts env' t s1.f out log
        let par := (finishWith out).isNone
        let chk := (finishWith (if acc then out else { func := s1.f, tables := s1.tabs })).isNone
        if i == 0 then
          full? := some out.func
          if out.tables.types.size != s1.tabs.types.size || out.tables.auxes.size != s1.tabs.auxes.size then
            st := { st with tabsChanged := st.tabsChanged + 1 }
        let rep := acc && full? == some out.func
        let b (x : Bool) : Nat := if x then 1 else 0
        st := { st with counts := st.counts.modify i fun (p, q, r, s) =>
          (p + b (n > 0), q + b acc, r + b par, s + b chk)
                        repro := st.repro.modify i (· + b rep) }
        for (kk, w) in ruleWhys s1.tabs t s1.f log do
          if i == 0 then st := { st with fires := st.fires.insert kk (st.fires.getD kk 0 + 1) }
          let kv := (s!"{variants[i].1} {kk}", w)
          st := { st with whys := st.whys.insert kv (st.whys.getD kv 0 + 1) }
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
  IO.println s!"files {st.files}, decompose builtin sections {st.sections}, errors {st.errors}, proven dec rules {provenKeys.length}"
  IO.println s!"full rewrite step extends the tables in {st.tabsChanged} sections"
  IO.println "| table | rules fired | step accepted | full step reproduced and accepted | pass at stock | checked pass at stock |"
  IO.println "| --- | --: | --: | --: | --: | --: |"
  for h : i in [0:variants.size] do
    let (p, q, r, s) := st.counts[i]!
    IO.println s!"| {variants[i].1} | {p} | {q} | {st.repro[i]!} | {r} | {s} |"
  for (k, n) in st.fires.toList.mergeSort (fun a b => a.2 ≥ b.2) do
    IO.println s!"RULE\t{k}\t{provenKeys.contains k}\t{n}"
  for ((k, w), n) in st.whys.toList.mergeSort (fun a b => a.2 ≥ b.2) do
    IO.println s!"WHY\t{k}\t{w}\t{n}"
  return 0

end GoFVTest.DecRewriteProbe

def main (args : List String) : IO UInt32 := GoFVTest.DecRewriteProbe.main args
