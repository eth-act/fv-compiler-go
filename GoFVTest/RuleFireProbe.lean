import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.Opt.Opt

/-!
# `rule-fire-probe`: which unproven rules keep the proven-only passes from stock (#69, #113)

For every `opt`/`middle opt`/`late opt`/`divisible`/`divmod` section of the given export files,
runs the full rewrite pass with its log, the proven-only pass (`GoFV.Rules.Proven`) and the
checked proven-only pass (as `opt-proven-probe`). Per rule (`file:line Op`, block rules as
`file:line block <Kind>`): its firings in the full passes, and

- `sole`: functions not at stock under the proven-only passes whose sections off stock fire
  exactly one unproven rule in the full pass, this one;
- `unblocks`: functions not at stock under the proven-only passes that reach stock (every
  rewrite section) when this rule alone is added to the proven rules (tried for every unproven
  rule of a function with at most two).

Usage: `rule-fire-probe [--jobs N] <dir|file>...` (`N` workers, round robin over the files).
Output: a summary line, one TSV row per rule (`RULE key proven firings sole unblocks`), then per
function, sorted: `OFF rules path` (off stock under the proven-only passes; the unproven rules,
comma-separated), `SOLE rule function`, `VONLY path` (validator the only obstacle).
-/

open GoFV.SSA GoFV.Opt GoFVTest.Parity GoFV.Rules

namespace GoFVTest.RuleFireProbe

def key (r : Rule) : String := s!"{r.loc.file}:{r.loc.line} {r.op.name}"

def blockKey (r : BlockRule) : String := s!"{r.loc.file}:{r.loc.line} block {r.kind.name}"

def keysOf (s : RuleSet) : List String :=
  s.values.foldl (fun acc (_, rs) => acc ++ rs.map key) [] ++
    s.blocks.foldl (fun acc (_, rs) => acc ++ rs.map blockKey) [] ++
    (s.nilChecks ++ s.loads ++ s.structLoads ++ s.structStores ++ s.segs ++ s.phiSels).map key

/-- The rules proven as generated, value and block rules and the per-instance validated ones
(nil-check eliminations, forwardings, struct loads and stores, segments, phi selections). -/
def provenKeys : Std.HashSet String :=
  (keysOf Proven.generic ++ keysOf Proven.divisible ++ keysOf Proven.divmod).foldl
    (fun s k => s.insert k) {}

/-- Pass name, full rule set, proven rule set, full table, proven table. -/
def variants : List (String × RuleSet × RuleSet × Interp.Table × Interp.Table) :=
  [("opt", Generated.Generic.ruleSet, Proven.generic, genericTable, genericProvenTable),
   ("middle opt", Generated.Generic.ruleSet, Proven.generic, genericTable, genericProvenTable),
   ("late opt", Generated.Generic.ruleSet, Proven.generic, genericTable, genericProvenTable),
   ("divisible", Generated.Divisible.ruleSet, Proven.divisible, divisibleTable,
     divisibleProvenTable),
   ("divmod", Generated.Divmod.ruleSet, Proven.divmod, divmodTable, divmodProvenTable)]

/-- The proven set `p` (its value and block rules and its
per-instance validated tables) with the rule `extra` of the full set `s` added as a value or block
rule, in `s`'s matching order. -/
def withExtra (s p : RuleSet) (extra : String) : Interp.Table :=
  Interp.Table.ofRuleSet
    { p with
      values := s.values.map fun (o, rs) =>
        (o, rs.filterMap fun r =>
          if key r == extra then some r else (p.rulesOf o).find? (key · == key r))
      blocks := s.blocks.map fun (k, rs) =>
        (k, rs.filterMap fun r =>
          if blockKey r == extra then some r
          else (p.blockRulesOf k).find? (blockKey · == blockKey r)) }

def zvarFn (zv : Array (ID × Nat)) : ID → Nat :=
  let m : Std.HashMap ID Nat := zv.foldl (fun m (v, c) => m.insert v c) {}
  fun i => m.getD i 0

def ptrCacheFn (ts : Array TypeRef) : TypeRef → Bool :=
  let m : Std.HashMap TypeRef Unit := ts.foldl (fun m t => m.insert t ()) {}
  fun t => m.contains t

/-- The rules a log fired, replayed on the input's definitions (a rule is found from the op of
the value it fired at). -/
def firedKeys (t : Interp.Table) (f : Func) (log : Array RwEvent) : Array String := Id.run do
  let mut M : RewriteCheck.Defs := f.valueTab
  let mut out := #[]
  let mut kinds : Std.HashMap ID BlockKind := {}
  for ev in log do
    match ev with
    | .rule v i _ defs =>
      if let some x := M.get? v then
        if let some cr := (t.values[x.op.ctorIdx]?).bind (·[i]?) then out := out.push (key cr.rule)
      M := defs.foldl (fun M u => M.put u.id u) M
    | .copyArg v i src =>
      if let some x := M.get? v then
        if h : i < x.args.size then M := M.put v { x with args := x.args.set i src }
    | .phielim v d _ => M := M.put v d
    | .blockRule b i _ =>
      let k? := (kinds.get? b).orElse fun _ => (f.block? b).map (·.kind)
      if let some k := k? then
        if let some r := (t.blocks[k.ctorIdx]?).bind (·[i]?) then
          out := out.push (blockKey r)
          kinds := kinds.insert b r.newKind
    | _ => pure ()
  return out

structure St where
  fires : Std.HashMap String Nat := {}
  sole : Std.HashMap String Nat := {}
  unblocks : Std.HashMap String Nat := {}
  tables : Std.HashMap (String × String) Interp.Table := {}
  fns : Nat := 0
  provenAll : Nat := 0
  checkedAll : Nat := 0
  validatorOnly : Nat := 0
  /-- Functions off stock under the proven-only passes, by number of unproven rules fired on
  their sections off stock (0, 1, 2, 3 or more). -/
  byCount : Array Nat := #[0, 0, 0, 0]
  /-- The `OFF`/`SOLE`/`VONLY` lines, printed at the end. -/
  lines : Array String := #[]

def addCounts (a b : Std.HashMap String Nat) : Std.HashMap String Nat :=
  b.fold (fun m k n => m.insert k (m.getD k 0 + n)) a

/-- Two workers' counts together (the table caches are dropped). -/
def St.merge (a b : St) : St :=
  { fires := addCounts a.fires b.fires, sole := addCounts a.sole b.sole
    unblocks := addCounts a.unblocks b.unblocks, fns := a.fns + b.fns
    provenAll := a.provenAll + b.provenAll, checkedAll := a.checkedAll + b.checkedAll
    validatorOnly := a.validatorOnly + b.validatorOnly
    byCount := a.byCount.zipWith (· + ·) b.byCount, lines := a.lines ++ b.lines }

/-- One rewrite section: its environment, input, stock section, previous and current tables. -/
structure Sec where
  name : String
  set : RuleSet
  pset : RuleSet
  env : PassEnv
  input : Func
  stock : Section
  prev : Tables
  want : Tables

def atStock (t : Interp.Table) (s : Sec) : Bool :=
  match GoFV.Rules.rewritePassFired t true s.env s.input with
  | .ok (out, _) => (compare s.prev out s.want s.stock).isNone
  | .error _ => false

def checkFile (path : System.FilePath) (st : St) : IO St := do
  let data ← IO.FS.readBinFile path
  let .ok e := parseExport data | return st
  let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
  let base : PassEnv :=
    { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
      pgohot := e.pgohot, config := e.config, typs
      typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
      tables := {}, frontend := e.frontendTables, ptrCache := ptrCacheFn e.ptrCache }
  let mut st := st
  let mut any := false
  let mut provenAll := true
  let mut checkedAll := true
  -- sections off stock under the proven-only pass, with the unproven rules the full pass fired
  let mut off : Array Sec := #[]
  let mut unproven : Array String := #[]
  let mut tables : Tables := {}
  for h : k in [0:e.sections.size] do
    let s := e.sections[k]
    let prev := tables
    tables := tables.addAll s.defs
    if k == 0 then continue
    let name := s.pass.toStringLossy
    let some (_, set, pset, full, proven) := variants.find? (·.1 == name) | continue
    any := true
    let env := { base with passName := name, tables := prev, zvar := zvarFn e.sections[k-1]!.zvar }
    let input := e.sections[k-1]!.func
    let sec : Sec := { name, set, pset, env, input, stock := s, prev, want := tables }
    let mut fired : Array String := #[]
    match GoFV.Rules.rewriteRun full true true env input with
    | .ok (_, _, log) =>
      fired := firedKeys full input log
      for kk in fired do st := { st with fires := st.fires.insert kk (st.fires.getD kk 0 + 1) }
    | .error _ => pure ()
    let pOK := atStock proven sec
    if !pOK then
      provenAll := false
      off := off.push sec
      for kk in fired do
        if !provenKeys.contains kk && !unproven.contains kk then unproven := unproven.push kk
    match checkedRewrite proven env input with
    | .ok co => if (compare prev co tables s).isSome then checkedAll := false
    | .error _ => checkedAll := false
  if !any then return st
  st := { st with fns := st.fns + 1 }
  if provenAll then st := { st with provenAll := st.provenAll + 1 }
  if checkedAll then st := { st with checkedAll := st.checkedAll + 1 }
  if provenAll && !checkedAll then
    st := { st with validatorOnly := st.validatorOnly + 1, lines := st.lines.push s!"VONLY\t{path}" }
  if !provenAll then
    let i := min unproven.size 3
    st := { st with byCount := st.byCount.modify i (· + 1)
                    lines := st.lines.push s!"OFF\t{",".intercalate unproven.toList}\t{path}" }
    if unproven.size == 1 then
      let r := unproven[0]!
      st := { st with sole := st.sole.insert r (st.sole.getD r 0 + 1)
                      lines := st.lines.push s!"SOLE\t{r}\t{e.pkg}.{e.name}" }
    if unproven.size ≤ 2 then
      for r in unproven do
        let mut all := true
        for sec in off do
          let t ← match st.tables.get? (sec.name, r) with
            | some t => pure t
            | none =>
              let t := withExtra sec.set sec.pset r
              st := { st with tables := st.tables.insert (sec.name, r) t }
              pure t
          if !atStock t sec then all := false; break
        if all then st := { st with unblocks := st.unblocks.insert r (st.unblocks.getD r 0 + 1) }
  return st

partial def parseArgs : List String → Nat × Array String → Nat × Array String
  | [], o => o
  | "--jobs" :: n :: rest, (_, ps) => parseArgs rest (max (n.toNat?.getD 1) 1, ps)
  | a :: rest, (j, ps) => parseArgs rest (j, ps.push a)

def main (args : List String) : IO UInt32 := do
  let (jobs, paths) := parseArgs args (1, #[])
  let mut files := #[]
  for a in paths do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  files := files.qsort (·.toString < ·.toString)
  let tasks ← (List.range jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st : St := {}
    for h : i in [0:files.size] do
      if i % jobs == j then st ← checkFile files[i] st
    return st
  let mut st : St := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 2
  IO.println s!"SUMMARY functions {st.fns} proven-only-at-stock {st.provenAll} checked-at-stock {st.checkedAll} validator-only {st.validatorOnly} off-stock-by-unproven-count {st.byCount}"
  for (k, n) in st.fires.toList do
    IO.println s!"RULE\t{k}\t{provenKeys.contains k}\t{n}\t{st.sole.getD k 0}\t{st.unblocks.getD k 0}"
  for l in st.lines.qsort (· < ·) do IO.println l
  return 0

end GoFVTest.RuleFireProbe

def main (args : List String) : IO UInt32 := GoFVTest.RuleFireProbe.main args
