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
  fallback : Nat := 0

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
          | .op o _ _ _ _ _ _ _ => topAll o e
          | _ => false) then "top"
        else if !Pat.argsOK e.ty [] r.pat then "args"
        else if !leavesOK M I [] r.pat then "leaves"
        else if !resultOK tabs M ev or σ I r x defs then "result"
        else if !nodes.all (fun (n, u) => frameNodeOK tabs e r.pat n u) then "frame"
        else if !condFrameOK tabs e r.pat r.cond then "condFrame"
        else "ok"
    s!"{r.loc.file}:{r.loc.line} {rs}"

open GoFV.Rules RewriteCheck in
def why (tabs : Tables) (t : Interp.Table) (f g : Func) (log : Array RwEvent) : String := Id.run do
  if !atomsOK f g then return "atoms"
  let mut M : Defs := f.valueTab
  let mut B : BMap := []
  for ev in log do
    match ev with
    | .rule v i _ defs =>
      match M.get? v with
      | none => return s!"rule at missing v{v}"
      | some x =>
        match (t.values[x.op.ctorIdx]?).bind (·[i]?) with
        | none =>
          if structLoadOK tabs M v defs.toList then M := defs.foldl (fun M u => M.put u.id u) M
          else return s!"v{v}: no rule of the row, not a struct-load expansion: {x.op.name}<{repr (tabs.ty x.type)}> ({defs.size} defs)"
        | some cr =>
          if (GoFV.Proof.Rules.makeSelShape cr.rule && makeSelOK tabs M v defs.toList) ||
              ruleOK tabs M cr.rule v defs.toList then
            M := defs.foldl (fun M u => M.put u.id u) M
          else return s!"rule v{v}: {ruleWhy tabs M cr.rule v defs.toList}"
    | .copyArg v i src =>
      match M.get? v with
      | none => return s!"copyArg at missing v{v}"
      | some x =>
        if h : i < x.args.size then
          if copyReach tabs M M.size x.args[i] src then
            M := M.put v { x with args := x.args.set i src }
          else
            let d := fun (a : ID) => match M.get? a with
              | some u => s!"v{a}:{u.op.name}<{repr (tabs.ty u.type)}>({u.args.toList})"
              | none => s!"v{a}?"
            return s!"copyArg v{v}:{x.op.name} {i}: {d x.args[i]} does not reach {d src}"
        else return s!"copyArg v{v} {i}: no argument"
    | .control b i c =>
      match bstate f B b with
      | none => return s!"control at missing b{b}"
      | some st =>
        if h : i < st.ctrls.size then
          if copyReach tabs M M.size st.ctrls[i] c then
            B := (b, { st with ctrls := st.ctrls.set i c }) :: B
          else return s!"control b{b} {i}: v{st.ctrls[i]} does not reach v{c}"
        else return s!"control b{b} {i}: no control"
    | .phielim .. => return "phielim"
    | .blockRule b i nc =>
      match bstate f B b with
      | none => return s!"blockRule at missing b{b}"
      | some st =>
        if ((f.block? b).map (·.succs.size)) != some 2 then return s!"blockRule b{b}: successors" else
        match (t.blocks[st.kind.ctorIdx]?).bind (·[i]?) with
        | none => return "no block rule"
        | some br =>
          match blockOK tabs M br st nc with
          | some (defs, st') =>
            M := defs.foldl (fun M u => M.put u.id u) M
            B := (b, st') :: B
          | none => return s!"blockRule b{b} {br.loc.file}:{br.loc.line}"
  if !finalOK tabs f g M B then
    for b in g.blocks do
      let (some st, some fb, some gb) := (bstate f B b, f.block? b, g.block? b)
        | return s!"final: block b{b}"
      if gb.kind != st.kind then return s!"final: b{b} kind"
      if !(if st.swapped then fb.succs.size == 2 && gb.succs == swapS fb.succs
           else gb.succs == fb.succs) then return s!"final: b{b} succs"
      if gb.controls.size != st.ctrls.size then return s!"final: b{b} controls"
      for (c, c') in st.ctrls.toList.zip gb.controls.toList do
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

/-- A value's term, `d` levels deep (diagnostics). -/
def desc (tabs : Tables) (f : Func) : Nat → ID → String
  | 0, a => s!"v{a}"
  | d + 1, a =>
    match f.value? a with
    | some u =>
      let args := u.args.toList.map (desc tabs f d)
      s!"v{a}:{u.op.name}<{repr (tabs.ty u.type)}>[{u.auxInt}]\{{(u.aux.map (fun x => s!"{x}")).getD ""}}({", ".intercalate args})"
    | none => s!"v{a}?"

/-- The first value nilcheckelim's checker (`NilCheck.nrel true`) rejects (diagnostics). -/
def nilWhy (tabs : Tables) (f g : Func) : String := Id.run do
  let c := DomCert.make f
  if !(DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
      g.valueTab.size == f.valueTab.size) then return "nrel: cfg/ownAux/size"
  if !f.blocks.all (NilCheck.blockOK f g) then return "nrel: blockOK"
  for x in List.range f.valueTab.size do
    if !NilCheck.valueOK true tabs c f g x then
      match f.value? x with
      | some fv =>
        let p := fv.args[0]?.getD 0
        let seed := NilCheck.safePtr true tabs f f.valueTab.size p
        let mc := match f.value? p with
          | some pv => match pv.args[0]? with
            | some cc => s!" mallocCall={NilCheck.mallocCall tabs f cc} callee={(((f.value? cc).bind (·.aux)).bind tabs.callee?)}"
            | none => ""
          | none => ""
        return s!"nrel: v{x} {fv.op.name} seed={seed}{mc}: {desc tabs f 3 p}"
      | none => return s!"nrel: v{x} missing"
  return "nrel: sched"

open GoFV.Rules RewriteCheck in
/-- Which part of `fwdOK` fails for the `Load` `u` forwarded to `x`, at the first `Store` of its
chain that stores `x` (diagnostics). -/
def fwdOKWhy (tabs : Tables) (f : Func) (u : Value) (x : ID) : String := Id.run do
  if u.op != .Load then return s!"not a Load ({u.op.name})"
  if u.args.size != 2 then return "Load arity"
  let t := tabs.ty u.type
  let p := u.args[0]!
  let mut m := u.args[1]!
  for d in [0:8] do
    let some s := f.value? m | return s!"mem v{m} missing"
    if s.op == .Copy && s.args.size == 1 then
      m := s.args[0]!
      continue
    if !(s.op == .Store || s.op == .StoreWB) then return s!"depth {d}: mem is {s.op.name}"
    if s.args.size != 3 then return "Store arity"
    if s.args[1]! == x then
      let some xv := f.value? x | return s!"x v{x} missing"
      if !samePtrB tabs f p s.args[0]! then
        return s!"depth {d}: ptr {desc tabs f 3 p} vs {desc tabs f 3 s.args[0]!}"
      if !fwdStoreTy t (Sem.auxTy tabs s.aux) then
        return s!"depth {d}: store type {repr t} vs {repr (Sem.auxTy tabs s.aux)}"
      if !fwdTyEq t (tabs.ty xv.type) then
        return s!"depth {d}: x type {repr t} vs {repr (tabs.ty xv.type)}"
      return "?"
    if !disjointB tabs f p t.size s.args[0]! (Sem.auxTy tabs s.aux).size then
      return s!"depth {d}: not disjoint {desc tabs f 3 p} vs {desc tabs f 3 s.args[0]!}; stored {desc tabs f 2 s.args[1]!} != {desc tabs f 2 x}"
    m := s.args[2]!
  return "chain too long"

open GoFV.Rules RewriteCheck in
/-- Which part of `ssSplit?` fails for the split `Store` `x` (diagnostics). -/
def ssSplitWhy (tabs : Tables) (f g : Func) (x : ID) : String :=
  match f.value? x, g.value? x with
  | some fv, some gv =>
    match fv.args.toList, Sem.auxTy tabs fv.aux, gv.args.toList with
    | [dst, sm, mem], .agg fs n, [last] =>
      match f.value? (copyEnd tabs f.valueTab f.valueTab.size sm) with
      | some smv =>
        let r := ssWalk g fs.length last
        if smv.op != .StructMake then s!"stored {smv.op.name}"
        else if !Sem.Ty.beq (tabs.ty smv.type) (.agg fs n) then "StructMake shape"
        else if !(layoutsOK n fs && fs.all (·.1 < n)) then "layout"
        else if smv.args.size != fs.length then "arity"
        else if !(gv.op == .Copy && gv.type == fv.type) then "copy"
        else if !(r.1.length == fs.length && last == (r.1.getLast?.map (·.2)).getD r.2) then
          s!"walk ({fs.length} fields) {desc tabs g 2 last}"
        else if !ssStart tabs f g fv.block mem r.2 then
          s!"chain start {desc tabs f 2 mem} vs {desc tabs g 2 r.2}"
        else match (List.range fs.length).find? (fun k => !ssLink tabs f g fv.block dst fs smv.args r.1 r.2 k) with
          | some k => s!"field {k} of {fs.length}"
          | none => "ok"
      | none => "no StructMake"
    | _, _, _ => "store shape"
  | _, _ => "missing"

open GoFV.Rules RewriteCheck in
/-- Which part of `ssRel`/`check` fails for the split function `f'` of `f`, if any. -/
def ssRelWhy (env : PassEnv) (tabs : Tables) (f f' : Func) : Option String := Id.run do
  for z in List.range f.valueTab.size do
    match f.value? z, f'.value? z with
    | some u, some w =>
      if !ssSame u w && (ssSplit? tabs f f' z).isNone then
        return some s!"v{z} {ssSplitWhy tabs f f' z}"
    | some _, none => return some s!"v{z} missing"
    | none, _ => pure ()
  if !ssRel tabs f f' then return some "rel"
  if let .error e := check { tabs := tabs, typs := env.typs } f' then return some s!"check {e}"
  return none

open GoFV.Rules RewriteCheck in
/-- Which part of `fwdRel`/`check` fails for the forwarded function `f'` of `f`, if any. -/
def fwdRelWhy (env : PassEnv) (tabs : Tables) (f f' : Func) : Option String := Id.run do
  if !atomsOK f f' then return some "atoms"
  if !closedOK f' then return some "closed"
  if !fwdRankOK f (fwdRank f) then return some "rank"
  for z in List.range f.valueTab.size do
    if !fwdRepOK tabs f f' z then
      match f.value? z, f'.value? z with
      | some u, some w =>
        if w.op == .Copy && w.args.size == 1 then
          return some s!"v{z} {fwdOKWhy tabs f u (w.args[0]?.getD 0)}"
        else return some s!"v{z} rep {u.op.name}->{w.op.name}"
      | _, _ => return some s!"v{z} rep"
  if !fwdRel tabs f f' then return some "rel"
  if !checkOK { tabs := tabs, typs := env.typs } f' then return some "check"
  return none

open GoFV.Rules RewriteCheck in
/-- Which layer of `RewriteCheck.layersOK` fails (`f0` the pass's input; diagnostics). -/
def layersWhy (env : PassEnv) (tabs : Tables) (t : Interp.Table) (f0 g : Func) :
    List Layer → Func → Array RwEvent → String
  | [], f, log => why tabs t f g log
  | L :: Ls, f, log =>
    let (f', log') := L.pre t tabs f log
    if log'.size == log.size then layersWhy env tabs t f0 g Ls f log else
    let k := log.size - log'.size
    let r : Option String := match L with
      | .nil sel =>
        let pre := s!"nil{if sel then "₁" else "₂"}({k})"
        if !NilCheck.nrel true tabs f f' then some s!"{pre}: {nilWhy tabs f f'}"
        else if NilCheck.dictParams tabs f != NilCheck.dictParams env.tables f0 then
          some s!"{pre}: dictionary parameters differ between the tables"
        else if !RewriteCheck.layerOK env t tabs f0 L f log f' then some s!"{pre}: check"
        else none
      | .fwd sel => (fwdRelWhy env tabs f f').map (s!"fwd{if sel then "₁" else "₂"}({k}): " ++ ·)
      | .sl =>
        if RewriteCheck.layerOK env t tabs f0 L f log f' then none
        else if let .error e := check { tabs := tabs, typs := env.typs } f' then
          some s!"sl({k}): check {e}"
        else some s!"sl({k}): {why tabs t f f' (slTaken t tabs f log)}"
      | .ss => (ssRelWhy env tabs f f').map (s!"ss({k}): " ++ ·)
    match r with
    | some s => s
    | none =>
      let pre := match L with
        | .nil sel => s!"nil{if sel then "₁" else "₂"}({k})"
        | .fwd sel => s!"fwd{if sel then "₁" else "₂"}({k})"
        | .sl => s!"sl({k})"
        | .ss => s!"ss({k})"
      s!"{pre} → {layersWhy env tabs t f0 g Ls f' log'}"

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
  -- every section's proven-only (unchecked) result at stock, and the checked failures' reasons
  let mut allProven := true
  let mut blockers : Array String := #[]
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
    let mut provenSec := false
    match GoFV.Rules.rewritePassFired proven true env input with
    | .ok (out, n) =>
      c := { c with vProven := c.vProven + numValues out.func, firedProven := c.firedProven + n }
      if (compare prev out tables s).isNone then
        c := { c with provenSame := c.provenSame + 1 }
        provenSec := true
      if out.func == input then c := { c with provenNoop := c.provenNoop + 1 }
    | .error _ => c := { c with errors := c.errors + 1 }
    if !provenSec then allProven := false
    match GoFV.Rules.rewriteRun proven true true env input with
    | .ok (out, _, log) =>
      let ok := RewriteCheck.accepts env proven input out log
      let co : PassOut := match checkedRewrite proven env input with
        | .ok co => co
        | .error _ => { func := input, tables := prev }
      if !ok && !(out.func == input) then
        -- `checkedRewrite`'s fallbacks (without forwardings, then without struct-store
        -- splits, then without nil-check eliminations): rejected, or accepted
        let t' := { proven with loads := #[] }
        let t'' := { t' with structStores := #[] }
        let t''' := { t'' with nilChecks := #[] }
        let fbOf (t' : GoFV.Rules.Interp.Table) : Option String :=
          match GoFV.Rules.rewriteRun t' true true env input with
          | .ok (o2, _, log2) =>
            if RewriteCheck.accepts env t' input o2 log2 || o2.func == input then none else
            some (if !tabsAgree prev o2.tables input then "tables"
              else layersWhy env o2.tables t' input o2.func RewriteCheck.layers input log2)
          | .error e => some s!"error {e}"
        let fb := if proven.loads.isEmpty then some "" else fbOf t'
        let fb := if fb.isSome && !proven.structStores.isEmpty then fbOf t'' else fb
        let fb := if fb.isSome && !proven.nilChecks.isEmpty then fbOf t''' else fb
        if fb.isSome then c := { c with rejected := c.rejected + 1 }
        else c := { c with fallback := c.fallback + 1 }
        let reason := if !tabsAgree prev out.tables input then
            "tables: the input tells the result's tables from its own (tabsAgree)"
          else layersWhy env out.tables proven input out.func RewriteCheck.layers input log
        IO.println s!"{if fb.isSome then "REJECT" else "FALLBACK"} {name} {path}: {reason}"
        if provenSec then blockers := blockers.push s!"{name}: {reason.take 160}"
        if let some r2 := fb then
          if !r2.isEmpty then IO.println s!"  without forwardings: {r2}"
      if (compare prev co tables s).isNone then
        c := { c with checkedSame := c.checkedSame + 1 }
      else allChecked := false
    | .error _ =>
      c := { c with errors := c.errors + 1 }
      allChecked := false
    st := st.insert name c
  if any && allProven && !allChecked then
    IO.println s!"BLOCKED {path}: {" || ".intercalate blockers.toList}"
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
  IO.println "| Pass | Runs | Full parity | Proven-only parity | Proven-only no-op | Rules fired (full) | Rules fired (proven-only) | Firings kept | Values stock | Values proven-only | Validator rejects | Forwarding fallbacks | Checked parity | Errors |"
  IO.println "| --- | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: |"
  for (name, _, _) in variants do
    let c := st.getD name {}
    IO.println s!"| {name} | {c.runs} | {pct c.fullSame c.runs} | {pct c.provenSame c.runs} | {pct c.provenNoop c.runs} | {c.firedFull} | {c.firedProven} | {pct c.firedProven c.firedFull} | {c.vStock} | {c.vProven} | {c.rejected} | {c.fallback} | {pct c.checkedSame c.runs} | {c.errors} |"
  return 0

end GoFVTest.OptProvenProbe

def main (args : List String) : IO UInt32 := GoFVTest.OptProvenProbe.main args
