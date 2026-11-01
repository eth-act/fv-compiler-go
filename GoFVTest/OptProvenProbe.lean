import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.Opt.Opt

/-!
# `opt-proven-probe`: what the proven-only rewrite passes cost (issue #113)

For every `opt`/`middle opt`/`late opt`/`divisible`/`divmod` section of the given export files,
runs the full pass and its proven-only variant (`GoFV.Opt.optProven`, …: only rules with a merged
`Rule.Sound` lemma fire) on the section's input and reports, per stock pass name: instances,
stock parity of each variant, instances where the proven-only variant changes nothing, the rules
fired by each variant, the share of the full pass's firings the proven-only variant keeps, and
the number of values (listed in blocks) of the stock and proven-only outputs.
-/

open GoFV.SSA GoFV.Opt GoFVTest.Parity

namespace GoFVTest.OptProvenProbe

structure Count where
  runs : Nat := 0
  fullSame : Nat := 0
  provenSame : Nat := 0
  provenNoop : Nat := 0
  errors : Nat := 0
  firedFull : Nat := 0
  firedProven : Nat := 0
  vStock : Nat := 0
  vProven : Nat := 0

def numValues (f : Func) : Nat :=
  f.blocks.foldl (fun n b => n + ((f.block? b).map (·.values.size)).getD 0) 0

def variants : List (String × GoFV.Rules.Interp.Table × GoFV.Rules.Interp.Table) :=
  [("opt", genericTable, genericProvenTable), ("middle opt", genericTable, genericProvenTable),
   ("late opt", genericTable, genericProvenTable),
   ("divisible", divisibleTable, divisibleProvenTable), ("divmod", divmodTable, divmodProvenTable)]

def zvarFn (zv : Array (ID × Nat)) : ID → Nat :=
  let m : Std.HashMap ID Nat := zv.foldl (fun m (v, c) => m.insert v c) {}
  fun i => m.getD i 0

def ptrCacheFn (ts : Array TypeRef) : TypeRef → Bool :=
  let m : Std.HashMap TypeRef Unit := ts.foldl (fun m t => m.insert t ()) {}
  fun t => m.contains t

def checkFile (path : System.FilePath) (st : Std.HashMap String Count) :
    IO (Std.HashMap String Count) := do
  let data ← IO.FS.readBinFile path
  let .ok e := parseExport data | return st
  let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
  let base : PassEnv :=
    { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
      pgohot := e.pgohot, config := e.config, typs
      typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
      tables := {}, frontend := e.frontendTables, ptrCache := ptrCacheFn e.ptrCache }
  let mut st := st
  let mut tables : Tables := {}
  for h : k in [0:e.sections.size] do
    let s := e.sections[k]
    let prev := tables
    tables := tables.addAll s.defs
    if k == 0 then continue
    let name := s.pass.toStringLossy
    let some (_, full, proven) := variants.find? (·.1 == name) | continue
    let env := { base with passName := name, tables := prev, zvar := zvarFn e.sections[k-1]!.zvar }
    let input := e.sections[k-1]!.func
    let mut c := st.getD name {}
    c := { c with runs := c.runs + 1, vStock := c.vStock + numValues s.func }
    match GoFV.Rules.rewritePassFired full true env input with
    | .ok (out, n) =>
      c := { c with firedFull := c.firedFull + n }
      if (compare prev out tables s).isNone then c := { c with fullSame := c.fullSame + 1 }
    | .error _ => c := { c with errors := c.errors + 1 }
    match GoFV.Rules.rewritePassFired proven true env input with
    | .ok (out, n) =>
      c := { c with vProven := c.vProven + numValues out.func, firedProven := c.firedProven + n }
      if (compare prev out tables s).isNone then c := { c with provenSame := c.provenSame + 1 }
      if out.func == input then c := { c with provenNoop := c.provenNoop + 1 }
    | .error _ => c := { c with errors := c.errors + 1 }
    st := st.insert name c
  return st

def pct (a b : Nat) : String :=
  if b == 0 then "-" else
  let x := (a * 10000 + b / 2) / b
  s!"{x / 100}.{if x % 100 < 10 then "0" else ""}{x % 100}%"

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut st : Std.HashMap String Count := {}
  for path in files.qsort (·.toString < ·.toString) do
    st ← checkFile path st
  IO.println "| Pass | Runs | Full parity | Proven-only parity | Proven-only no-op | Rules fired (full) | Rules fired (proven-only) | Firings kept | Values stock | Values proven-only | Errors |"
  IO.println "| --- | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: |"
  for (name, _, _) in variants do
    let c := st.getD name {}
    IO.println s!"| {name} | {c.runs} | {pct c.fullSame c.runs} | {pct c.provenSame c.runs} | {pct c.provenNoop c.runs} | {c.firedFull} | {c.firedProven} | {pct c.firedProven c.firedFull} | {c.vStock} | {c.vProven} | {c.errors} |"
  return 0

end GoFVTest.OptProvenProbe

def main (args : List String) : IO UInt32 := GoFVTest.OptProvenProbe.main args
