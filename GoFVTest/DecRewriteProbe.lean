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
  if loadSelShape r then (if loadSelOK tabs M v defs then "ok" else
    match M.get? v with
    | some x =>
      let ys := ((x.args[0]?).bind M.get?).map fun y => s!"{y.op.name}:{reprStr (tabs.ty y.type)}"
      s!"loadSelOK v:{reprStr (tabs.ty x.type)} ai {x.auxInt} of {ys} defs {defs.length}"
    | none => "loadSelOK") else
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
          | .op o _ _ _ _ _ _ _ => topAll o e || makeTop o (e.ty [])
          | _ => false) then "topAll" ++ shapes else
        if !Pat.argsOK e.ty [] r.pat then "argsOK" ++ shapes else
        if !leavesOK M I [] r.pat then
          let ls := I.filterMap fun (p, w) => (M.get? w).map fun x =>
            if p.length < 2 then "" else s!"{x.op.name}:{reprStr (tabs.ty x.type)}"
          s!"leavesOK {ls.filter (· != "")}" else
        if !resultOK tabs M ev or σ I r x defs then
          (if r.block.isSome then "resultOK (@b block)" else "resultOK") else
        if !nodes.all (fun (n, u) => frameNodeOK tabs ev e r.pat n u) then "frameNodeOK" else
        if !condFrameOK tabs ev e I r.pat r.cond (GoFV.Proof.Rules.sameLeaves r) then "condFrameOK" else "ok"
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
  /-- Sections whose proven-table step is not the full step accepted, by class: `REJ <first
  failing validator check>` or `DIFF <unproven rules of the full step's log>`. -/
  classes : Std.HashMap String Nat := {}

def Stats.merge (a b : Stats) : Stats := Id.run do
  let mut st := { a with files := a.files + b.files, sections := a.sections + b.sections
                         errors := a.errors + b.errors
                         repro := (a.repro.zip b.repro).map fun (x, y) => x + y
                         tabsChanged := a.tabsChanged + b.tabsChanged
                         counts := (a.counts.zip b.counts).map fun ((p, q, r, s), (p', q', r', s')) =>
                           (p + p', q + q', r + r', s + s') }
  for (k, n) in b.fires do st := { st with fires := st.fires.insert k (st.fires.getD k 0 + n) }
  for (k, n) in b.whys do st := { st with whys := st.whys.insert k (st.whys.getD k 0 + n) }
  for (k, n) in b.classes do st := { st with classes := st.classes.insert k (st.classes.getD k 0 + n) }
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
    | .phielim v d _ => M := M.put v d
    | _ => pure ()
  return out

/-- The first event `replay` rejects (mirrors `RewriteCheck.replay`), else the replayed state. -/
def replayWhy (tabs : Tables) (t : Interp.Table) (f : Func) :
    Defs → BMap → List RwEvent → Except String (Defs × BMap)
  | M, B, [] => .ok (M, B)
  | M, B, .rule v i _ defs :: evs =>
    match M.get? v with
    | none => .error "rule: no def"
    | some x =>
      match (t.values[x.op.ctorIdx]?).bind (·[i]?) with
      | none =>
        if structLoadOK tabs M v defs.toList then
          replayWhy tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
        else .error s!"structLoadOK {x.op.name}"
      | some cr =>
        if makeSelShape cr.rule && makeSelOK tabs M v defs.toList then
          replayWhy tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
        else if loadSelShape cr.rule then
          if loadSelOK tabs M v defs.toList then
            replayWhy tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
          else .error s!"rule {key cr.rule}: loadSelOK"
        else if imsShape cr.rule then
          if imsOK tabs M v defs.toList then
            replayWhy tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
          else .error s!"rule {key cr.rule}: imsOK"
        else if ruleOK tabs M cr.rule v defs.toList then
          replayWhy tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
        else .error s!"rule {key cr.rule}: {why tabs M cr.rule v defs.toList}"
  | M, B, .copyArg v i src :: evs =>
    match M.get? v with
    | none => .error "copyArg: no def"
    | some x =>
      if h : i < x.args.size then
        if copyReach tabs M M.size x.args[i] src then
          replayWhy tabs t f (M.put v { x with args := x.args.set i src }) B evs
        else
          let src' := ((M.get? src).map (·.op.name)).getD "?"
          let old := ((M.get? x.args[i]).map (·.op.name)).getD "?"
          .error s!"copyArg {x.op.name}[{i}]: {old} -> {src'}"
      else .error "copyArg: index"
  | M, B, .control b i c :: evs =>
    match bstate f B b with
    | none => .error "control: no block"
    | some st =>
      if h : i < st.ctrls.size then
        if copyReach tabs M M.size st.ctrls[i] c then
          replayWhy tabs t f M ((b, { st with ctrls := st.ctrls.set i c }) :: B) evs
        else .error "control: copyReach"
      else .error "control: index"
  | _, _, .phielim .. :: _ => .error "phielim"
  | _, _, .snap .. :: _ => .error "snap"
  | _, _, .blockRule .. :: _ => .error "blockRule"

/-- The first value of `g` that `finalOK` rejects. -/
def finalWhy (tabs : Tables) (f g : Func) (M : Defs) (B : BMap) : String := Id.run do
  let n := M.size
  for b in g.blocks do
    match bstate f B b, f.block? b, g.block? b with
    | some st, some fb, some gb =>
      if !(gb.kind == st.kind) then return "finalOK: block kind"
      if !(if st.swapped then fb.succs.size == 2 && gb.succs == swapS fb.succs
          else gb.succs == fb.succs) then return "finalOK: succs"
      if !(gb.controls.size == st.ctrls.size &&
          (st.ctrls.toList.zip gb.controls.toList).all (fun (c, c') => copyReach tabs M n c c')) then
        return "finalOK: controls"
      for x in gb.values do
        match M.get? x, g.value? x with
        | some m, some u =>
          if !(u.id == x && m.id == x && u.op == m.op && u.type == m.type && u.auxInt == m.auxInt &&
              u.aux == m.aux && u.args.size == m.args.size) then
            return s!"finalOK: fields {m.op.name} -> {u.op.name}"
          if !(m.args.toList.zip u.args.toList).all (fun (a, a') => copyReach tabs M n a a') then
            let ops := u.args.toList.map fun a => ((g.value? a).map (·.op.name)).getD "?"
            return s!"finalOK: args of {u.op.name} {ops}"
        | none, some u => return s!"finalOK: new value {u.op.name}"
        | _, _ => return "finalOK: missing value"
    | _, _, _ => return "finalOK: block"
  return "finalOK: ?"

/-- The first check of `RewriteCheck.accepts` (without nil-check eliminations, forwardings and
struct-store splits, which the dec table does not have) that fails. -/
def rejectWhy (env : PassEnv) (t : Interp.Table) (f : Func) (out : PassOut) (log : Array RwEvent) :
    String :=
  if !tabsAgree env.tables out.tables f then "tabsAgree" else
  let tabs := out.tables
  let g := out.func
  if !atomsOK f g then "atomsOK" else
  if !closedOK f then "closedOK input" else
  if !closedOK g then "closedOK output" else
  match replayWhy tabs t f f.valueTab [] log.toList with
  | .error e => e
  | .ok (M, B) => if finalOK tabs f g M B then "ok" else finalWhy tabs f g M B

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
    let mut fullKeys : List String := []
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
        let whys := ruleWhys out.tables t s1.f log
        if i == 0 then fullKeys := (whys.toList.map (·.1)).eraseDups
        if i == 2 && !rep then
          let un := (fullKeys.filter (!provenKeys.contains ·)).mergeSort (· ≤ ·)
          let cls := if !acc then s!"REJ {rejectWhy env' t s1.f out log}" else s!"DIFF {un}"
          if acc then
            for k in un do
              st := { st with classes := st.classes.insert s!"DIFFRULE {k}" (st.classes.getD s!"DIFFRULE {k}" 0 + 1) }
          st := { st with classes := st.classes.insert cls (st.classes.getD cls 0 + 1) }
        for (kk, w) in whys do
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
  for (k, n) in st.classes.toList.mergeSort (fun a b => a.2 ≥ b.2) do
    IO.println s!"CLASS\t{k}\t{n}"
  return 0

end GoFVTest.DecRewriteProbe

def main (args : List String) : IO UInt32 := GoFVTest.DecRewriteProbe.main args
