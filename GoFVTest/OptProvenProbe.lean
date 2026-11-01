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
  checkedSame : Nat := 0
  rejected : Nat := 0

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

open GoFV.Rules GoFV.Proof.Rules RewriteCheck in
/-- Which part of `ruleOK` fails (diagnostics). -/
def ruleWhy (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value) : String :=
  if !Pat.arityOk r.pat then "arity" else
  match M.get? v with
  | none => "no value"
  | some x =>
    if !termOp x.op then "not a term op" else
    let rs := (choices (Pat.commutes r.pat)).map fun sw =>
      match matchPat M r.pat [] v sw with
      | none => "nomatch"
      | some (I, _) =>
        let e := env tabs M I
        let vtys := r.vars.map (fun (x : Var) => x.ty)
        let σ := sigma e r.pat
        let nodes := match r.result, defs with
          | .build ns, _ :: us => ns.zip us
          | _, _ => []
        let or := oracle vtys tabs nodes
        let ev := evalE vtys σ or e (Pat.den e [] r.pat)
        if !consOK ev σ e I [] r.pat then "cons"
        else if !wfOK e [] r.pat then "wf"
        else if !(match r.cond with
          | some c => match ev c with | .bool true => true | _ => false
          | none => true) then "cond"
        else if !(match r.pat with
          | .op o _ _ _ _ _ _ _ => natShape o (e.ty [])
          | _ => false) then "natShape"
        else if !leavesOK tabs M I [] r.pat then
          let bad := I.filterMap fun (pw : Path × ID) => match M.get? pw.2 with
            | some x => if tabs.ty x.type matches .other then some x.op.name else none
            | none => none
          s!"leaves {bad}"
        else if !resultOK tabs M ev or σ I r x defs then "result"
        else "ok"
    s!"{r.loc.file}:{r.loc.line} {rs}"

open GoFV.Rules RewriteCheck in
def why (tabs : Tables) (t : Interp.Table) (f g : Func) (log : Array RwEvent) : String := Id.run do
  if !atomsOK f g then return "atoms"
  let mut M : Defs := f.valueTab
  for ev in log do
    match ev with
    | .rule v i _ defs =>
      match M.get? v with
      | none => return s!"rule at missing v{v}"
      | some x =>
        match (t.values[x.op.ctorIdx]?).bind (·[i]?) with
        | none => return "no rule"
        | some cr =>
          if ruleOK tabs M cr.rule v defs.toList then M := defs.foldl (fun M u => M.put u.id u) M
          else return s!"rule v{v}: {ruleWhy tabs M cr.rule v defs.toList}"
    | .phielim .. => return "phielim"
    | .blockRule .. => return "blockRule"
    | _ => pure ()
  if !finalOK tabs f g M then
    for b in g.blocks do
      let (some fb, some gb) := (f.block? b, g.block? b) | return s!"final: block b{b}"
      for (c, c') in fb.controls.toList.zip gb.controls.toList do
        if !copyReach tabs M M.size c c' then return s!"final: control b{b} v{c}->v{c'}"
      for x in gb.values do
        match M.get? x, g.value? x with
        | some m, some u =>
          if !(u.op == m.op && u.type == m.type && u.auxInt == m.auxInt && u.aux == m.aux) then
            return s!"final: v{x} fields {m.op.name}->{u.op.name}"
          for (a, a') in m.args.toList.zip u.args.toList do
            if !copyReach tabs M M.size a a' then
              return s!"final: v{x} {u.op.name} arg v{a}({((M.get? a).map (·.op.name)).getD "-"})->v{a'}"
        | _, _ => return s!"final: v{x} missing"
    return "final"
  return "?"

/-- Per stock pass name the counts; `fns`/`fnsChecked`: functions (export files) with a rewrite
section, and those whose every rewrite section the checked variant reproduces. -/
def checkFile (path : System.FilePath) (st : Std.HashMap String Count × Nat × Nat) :
    IO (Std.HashMap String Count × Nat × Nat) := do
  let (st, fns, fnsChecked) := st
  let data ← IO.FS.readBinFile path
  let .ok e := parseExport data | return (st, fns, fnsChecked)
  let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
  let base : PassEnv :=
    { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
      pgohot := e.pgohot, config := e.config, typs
      typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
      tables := {}, frontend := e.frontendTables, ptrCache := ptrCacheFn e.ptrCache }
  let mut st := st
  let mut any := false
  let mut allChecked := true
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
    any := true
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
    match GoFV.Rules.rewriteRun proven true true env input with
    | .ok (out, _, log) =>
      let ok := RewriteCheck.validate prev proven input out.func log
      if !ok && !(out.func == input) then
        c := { c with rejected := c.rejected + 1 }
        IO.println s!"REJECT {name} {path}: {why prev proven input out.func log}"
      let cf := if ok then out.func else input
      if (compare prev { func := cf, tables := prev } tables s).isNone then
        c := { c with checkedSame := c.checkedSame + 1 }
      else allChecked := false
    | .error _ =>
      c := { c with errors := c.errors + 1 }
      allChecked := false
    st := st.insert name c
  return (st, if any then fns + 1 else fns, if any && allChecked then fnsChecked + 1 else fnsChecked)

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
  let mut acc : Std.HashMap String Count × Nat × Nat := ({}, 0, 0)
  for path in files.qsort (·.toString < ·.toString) do
    acc ← checkFile path acc
  let (st, fns, fnsChecked) := acc
  IO.println s!"Functions with a rewrite section: {fns}; every rewrite section at the stock result under the checked proven-only passes: {fnsChecked} ({pct fnsChecked fns})"
  IO.println "| Pass | Runs | Full parity | Proven-only parity | Proven-only no-op | Rules fired (full) | Rules fired (proven-only) | Firings kept | Values stock | Values proven-only | Validator rejects | Checked parity | Errors |"
  IO.println "| --- | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: |"
  for (name, _, _) in variants do
    let c := st.getD name {}
    IO.println s!"| {name} | {c.runs} | {pct c.fullSame c.runs} | {pct c.provenSame c.runs} | {pct c.provenNoop c.runs} | {c.firedFull} | {c.firedProven} | {pct c.firedProven c.firedFull} | {c.vStock} | {c.vProven} | {c.rejected} | {pct c.checkedSame c.runs} | {c.errors} |"
  return 0

end GoFVTest.OptProvenProbe

def main (args : List String) : IO UInt32 := GoFVTest.OptProvenProbe.main args
