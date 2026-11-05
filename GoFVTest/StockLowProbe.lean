import GoFV.SSA.Parse
import GoFV.Opt.Lower
import GoFV.Opt.Pair

/-!
# `lake exe stocklow-probe [--jobs N] <dir>...`: what `late lower` and `pair` change

For every `late lower` section (input: the previous section), runs the Lean `late lower` with its
rewrite log and counts the sections it changes and, per `ARM64latelower.rules` rule (by source
line), the sections where it fires; for every `pair` section, the sections `pair` changes and the
ops of the values it adds (`LDP*`, `STP*`, selectors, copies), split into sections that only pair
loads within a block and the rest.
-/

open GoFV.SSA GoFV.Opt GoFV.Rules

namespace GoFVTest.StockLowProbe

structure Cnt where
  llSecs : Nat := 0
  llErr : Nat := 0
  llChanged : Nat := 0
  llRules : Std.HashMap String Nat := {}
  llSets : Std.HashMap String Nat := {}
  prSecs : Nat := 0
  prErr : Nat := 0
  prChanged : Nat := 0
  prKinds : Std.HashMap String Nat := {}

def bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + 1)

def Cnt.merge (a b : Cnt) : Cnt :=
  let mg (x y : Std.HashMap String Nat) := y.fold (fun m k n => m.insert k (m.getD k 0 + n)) x
  { llSecs := a.llSecs + b.llSecs, llErr := a.llErr + b.llErr
    llChanged := a.llChanged + b.llChanged, llRules := mg a.llRules b.llRules
    llSets := mg a.llSets b.llSets, prSecs := a.prSecs + b.prSecs, prErr := a.prErr + b.prErr
    prChanged := a.prChanged + b.prChanged, prKinds := mg a.prKinds b.prKinds }

/-- The source lines of the rules the log fired (replaying the ops to index the table's rows). -/
def firedRules (t : Interp.Table) (f : Func) (log : Array RwEvent) : Array String := Id.run do
  let mut cur : Std.HashMap ID Op := {}
  for o in f.valueTab do
    if let some v := o then cur := cur.insert v.id v.op
  let mut r : Array String := #[]
  for e in log do
    match e with
    | .rule v idx _ defs =>
      let op := cur.getD v .Invalid
      let row := t.values[op.ctorIdx]?.getD #[]
      let nm := match row[idx]? with
        | some cr => s!"{cr.rule.loc.line} {op.name}"
        | none => s!"? {op.name}[{idx}]"
      if !r.contains nm then r := r.push nm
      for d in defs do cur := cur.insert d.id d.op
    | .phielim v d _ => cur := cur.insert v d.op
    | _ => pure ()
  return r

/-- How `pair` changed `f` into `g`: the ops of the added values, and the op changes of kept
values (a load that became a selector or copy, a store a pair store or copy). -/
def pairKind (f g : Func) : String := Id.run do
  let mut added : Array String := #[]
  let mut changed : Array String := #[]
  for o in g.valueTab do
    if let some v := o then
      match f.value? v.id with
      | none => if !added.contains v.op.name then added := added.push v.op.name
      | some u =>
        if u.op != v.op then
          let k := s!"{u.op.name}->{v.op.name}"
          if !changed.contains k then changed := changed.push k
  return s!"added {added.qsort (· < ·)} changed {changed.qsort (· < ·)}"

def doFile (path : System.FilePath) (c : Cnt) : IO Cnt := do
  let data ← IO.FS.readBinFile path
  let .ok e := parseExport data | return c
  let typs := (e.sections[0]?.bind (·.typs)).getD #[]
  let base : PassEnv :=
    { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi
      nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs
      typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp, tables := {}
      frontend := e.frontendTables }
  let mut c := c
  let mut tables : Tables := {}
  for h : k in [0:e.sections.size] do
    let s := e.sections[k]
    let prev := tables
    tables := tables.addAll s.defs
    if k == 0 then continue
    let name := s.pass.toStringLossy
    let f := e.sections[k-1]!.func
    let env := { base with passName := name, tables := prev }
    if name == "late lower" then
      c := { c with llSecs := c.llSecs + 1 }
      match rewriteRun lateLowerTable true true env f with
      | .error _ => c := { c with llErr := c.llErr + 1 }
      | .ok (out, _, log) =>
        if out.func.valueTab != f.valueTab || out.func.blockTab != f.blockTab then
          let rs := (firedRules lateLowerTable f log).qsort (· < ·)
          c := { c with llChanged := c.llChanged + 1, llSets := bump c.llSets s!"{rs}" }
          for r in rs do c := { c with llRules := bump c.llRules r }
    else if name == "pair" then
      c := { c with prSecs := c.prSecs + 1 }
      match pairPass env f with
      | .error _ => c := { c with prErr := c.prErr + 1 }
      | .ok out =>
        if out.func.valueTab != f.valueTab || out.func.blockTab != f.blockTab then
          c := { c with prChanged := c.prChanged + 1, prKinds := bump c.prKinds (pairKind f out.func) }
  return c

def files (args : List String) : IO (Array System.FilePath) := do
  let mut fs := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      fs := fs ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else fs := fs.push p
  return fs.qsort (·.toString < ·.toString)

def sorted (m : Std.HashMap String Nat) : Array (String × Nat) :=
  m.toList.toArray.qsort (fun a b => a.2 > b.2)

def main (args : List String) : IO UInt32 := do
  let (jobs, args) := match args with
    | "--jobs" :: n :: rest => (n.toNat?.getD 1, rest)
    | _ => (1, args)
  let fs ← files args
  let chunk := (fs.size + jobs - 1) / max jobs 1
  let mut tasks := #[]
  for j in [0:jobs] do
    let part := fs.extract (j * chunk) ((j + 1) * chunk)
    tasks := tasks.push (← IO.asTask (part.foldlM (fun c p => doFile p c) {}))
  let mut c : Cnt := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok x => c := c.merge x
    | .error err => IO.eprintln s!"task error: {err}"; return 1
  IO.println s!"late lower: sections {c.llSecs}, errors {c.llErr}, changed {c.llChanged}"
  IO.println "rules (ARM64latelower.rules line, sections where fired):"
  for (k, n) in sorted c.llRules do IO.println s!"  {n} {k}"
  IO.println "rule sets (sections):"
  for (k, n) in (sorted c.llSets).extract 0 40 do IO.println s!"  {n} {k}"
  IO.println s!"pair: sections {c.prSecs}, errors {c.prErr}, changed {c.prChanged}"
  for (k, n) in (sorted c.prKinds).extract 0 40 do IO.println s!"  {n} {k}"
  return 0

end GoFVTest.StockLowProbe

def main (args : List String) : IO UInt32 := GoFVTest.StockLowProbe.main args
