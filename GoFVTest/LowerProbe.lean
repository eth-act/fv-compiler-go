import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.Opt.Lower
import GoFV.Opt.RewriteCheck
import GoFV.Opt.LowerCheck
import GoFV.Opt.LowerChecked

/-!
# `lower-probe`: which `ARM64.rules` rules `lower` fires (issue #385)

For every `lower` section of the given export files, runs `lower` (`GoFV.Opt.lower`'s table) with
its log and records, per function, the rules it fires (`ARM64:<line> <Op>`, block rules
`ARM64:<line> block <Kind>`). Output: one `RULE key firings functions` row per rule (by
firings), then `GREEDY k key covered` rows: rules added greedily by the number of functions whose
fired rules all lie in the set so far (the order in which proving rules makes the checked lower
reproduce stock on whole functions).

Usage: `lower-probe [--jobs N] <dir|file>...`.
-/

open GoFV.SSA GoFV.Opt GoFV.Rules

namespace GoFVTest.LowerProbe

def key (r : Rule) : String := s!"{r.loc.file}:{r.loc.line} {r.op.name}"

def blockKey (r : BlockRule) : String := s!"{r.loc.file}:{r.loc.line} block {r.kind.name}"

/-- The keys of the rules a log fires, replaying ops and block kinds only. -/
def firedKeys (t : Interp.Table) (f : Func) (log : Array RwEvent) : Array String := Id.run do
  let mut M : GoFV.Opt.RewriteCheck.Defs := f.valueTab
  let mut K : Std.HashMap ID BlockKind := {}
  let mut out : Array String := #[]
  for ev in log do
    match ev with
    | .rule v i _ defs =>
      match M.get? v with
      | none => pure ()
      | some x =>
        match ((t.values[x.op.ctorIdx]?).bind (·[i]?) : Option Interp.CRule) with
        | none => out := out.push s!"? {x.op.name}"
        | some cr =>
          out := out.push (key cr.rule)
          if defs.isEmpty then
            match cr.rule.result with
            | .setOp o => M := M.put v { x with op := o }
            | .copy _ => M := M.put v { x with op := .Copy }
            | _ => pure ()
          else M := defs.foldl (fun M u => M.put u.id u) M
    | .blockRule b i _ =>
      let k := (K.get? b).getD (((f.block? b).map (·.kind)).getD .Plain)
      match ((t.blocks[k.ctorIdx]?).bind (·[i]?) : Option BlockRule) with
      | none => out := out.push s!"? block {k.name}"
      | some br =>
        out := out.push (blockKey br)
        K := K.insert b br.newKind
    | _ => pure ()
  return out

def ptrCacheFn (ts : Array TypeRef) : TypeRef → Bool :=
  let m : Std.HashMap TypeRef Unit := ts.foldl (fun m t => m.insert t ()) {}
  fun t => m.contains t


open GoFV.Opt.LowerCheck GoFV.Opt.RewriteCheck GoFV.Proof.Low GoFV.Proof.Rules in
/-- Which check of `ruleOK1` fails, per commutation choice (diagnostics). -/
def ruleWhyL (tabs : Tables) (M : Defs) (r0 : Rule) (v : ID) (defs : List Value) : String :=
  match M.get? v with
  | none => "no value"
  | some x =>
    if !termVL tabs x then "not a term" else
    let rs := (choices (Pat.commutes r0.pat)).map fun sw =>
      let r := Rule.swapC r0 sw
      if !(Pat.arityOk r.pat && patOK r.pat) then "arity/patOK" else
      match matchPatL tabs M r.pat [] v with
      | none => "nomatch"
      | some I =>
        let e := envL tabs M I
        let vtys := r.vars.map (·.ty)
        let σ := sigmaL tabs e r.pat
        let nodes := match r.result, defs with
          | .build ns, _ :: us => ns.zip us
          | _, _ => []
        let or := oracleL vtys tabs ((r.cond.map (negAtoms false)).getD []) nodes
        let ev := evalE vtys σ or e (Pat.denL tabs e [] r.pat)
        if !(I.tail.all (·.2 != v)) then "cyclic"
        else if !consOK ev σ e I [] r.pat then "cons"
        else if !wfOK e [] r.pat then "wf"
        else if !(match r.cond with
          | some c => match ev c with | .bool true => true | _ => false
          | none => true) then "cond"
        else if !Pat.argsOK e.ty [] r.pat then "args"
        else if !Pat.topOKL (e.ty []) r.pat then s!"top {repr (e.ty [])}"
        else if !Pat.argsOKL e.ty [] r.pat then "argsL"
        else if !resFitsL (e.ty []) r.result then s!"fits {repr (e.ty [])}"
        else if !leavesOK M I [] r.pat then "leaves"
        else if !resultOKL tabs M e r.pat ev or σ I r x defs then
          s!"result defs={defs.map fun u => (u.id, u.op.name, u.args.toList, u.type)} x={(x.id, x.type)}"
        else "ok"
    s!"{rs}"

open GoFV.Opt.LowerCheck GoFV.Opt.RewriteCheck GoFV.Proof.Low in
/-- Why `validateL` rejects (diagnostics). -/
def whyL (tabs : Tables) (t : Interp.Table) (f g : Func) (log : Array RwEvent) : String := Id.run do
  if !g.lowered then return "not lowered"
  if !(f.lowered || shapesOK tabs f) then return "shapes"
  if !atomsOKL tabs f g then
    for b in f.blocks do
      match f.block? b, g.block? b with
      | some fb, some gb =>
        for x in atomsOfL tabs g gb do
          match f.value? x, g.value? x with
          | some u, some w => if !atomPair tabs u w then return s!"atoms: {u.op.name} -> {w.op.name} v{x}"
          | none, some w => return s!"atoms: new atom {w.op.name} v{x}"
          | _, _ => return s!"atoms: v{x}?"
        for x in atomsOfL tabs f fb do
          if !(atomsOfL tabs g gb).contains x && !((f.value? x).any (dropAtom ·.op)) then
            return s!"atoms: dropped {((f.value? x).map (·.op.name)).getD "?"} v{x}"
      | _, _ => pure ()
    return "atoms: order"
  if !closedOK f || !closedOK g then return "closed"
  let mut M : Defs := f.valueTab
  let mut B : BMapL := []
  for ev in log do
    match ev with
    | .rule v i _ defs =>
      match M.get? v with
      | none => return s!"rule at missing v{v}"
      | some x =>
        match ((t.values[x.op.ctorIdx]?).bind (·[i]?) : Option Interp.CRule) with
        | none => return "no rule"
        | some cr =>
          match cr.rule.result with
          | .setOp _ =>
            match setOpDef tabs M cr.rule v with
            | some x' => M := M.put v x'
            | none => return s!"setOp {key cr.rule}"
          | _ =>
            if ruleOKL tabs M cr.rule v defs.toList then M := defs.foldl (fun M u => M.put u.id u) M
            else match atomDef tabs M v defs.toList with
              | some (u, none) => M := M.put v u
              | some (u, some s) => M := (M.put s.id s).put v u
              | none => return s!"rule {key cr.rule} v{v} {ruleWhyL tabs M cr.rule v defs.toList}"
    | .copyArg v i src =>
      match M.get? v with
      | none => return "copyArg missing"
      | some x =>
        if h : i < x.args.size then
          if copyReachL tabs M M.size x.args[i] src then M := M.put v { x with args := x.args.set i src }
        else return "copyArg idx"
    | .control b i c =>
      match bstateL f B b with
      | none => return "control missing"
      | some st =>
        if h : i < st.ctrls.size then
          if copyReachL tabs M M.size st.ctrls[i] c then B := (b, { st with ctrls := st.ctrls.set i c }) :: B
          else return s!"control b{b}"
        else return "control idx"
    | .phielim .. => return "phielim"
    | .snap .. => return "snap"
    | .blockRule b i nc =>
      match bstateL f B b with
      | none => return "blockRule missing"
      | some st =>
        match ((t.blocks[st.kind.ctorIdx]?).bind (·[i]?) : Option BlockRule) with
        | none => return "no block rule"
        | some br =>
          match blockOKL tabs M br st nc with
          | some st' => B := (b, st') :: B
          | none => return s!"blockRule {blockKey br}"
  if !finalOKL tabs f g M B then
    let L := liveMarksL tabs g
    if !liveOKL tabs g L then return "final: live"
    for b in g.blocks do
      let (some st, some fb, some gb) := (bstateL f B b, f.block? b, g.block? b) | return "final: block"
      if gb.kind != st.kind then return s!"final: kind {gb.kind.name} vs {st.kind.name}"
      if gb.auxInt != st.auxInt then return "final: auxInt"
      for x in gb.values do
        match M.get? x, g.value? x with
        | some m, some u =>
          if !(u.op == m.op && u.type == m.type && u.auxInt == m.auxInt && u.aux == m.aux) then
            if !(termVL tabs u && L[x]? != some true) then
              return s!"final: v{x} fields {m.op.name}->{u.op.name}"
          else
            for (a, a') in m.args.toList.zip u.args.toList do
              if !copyReachL tabs M M.size a a' && !(termVL tabs u && L[x]? != some true) then
                let d := fun (y : ID) => ((M.get? y).map (·.op.name)).getD "-"
                return s!"final: v{x} {u.op.name} arg v{a}({d a})->v{a'}({d a'})"
        | _, _ => return s!"final: v{x} missing"
      if !((st.ctrls.toList.zip gb.controls.toList).all (fun (c, c') => copyReachL tabs M M.size c c')) then
        return "final: controls"
    return "final: succs"
  return "ok"

structure St where
  firings : Std.HashMap String Nat := {}
  fns : Array (Array String) := #[]
  errors : Nat := 0
  accepted : Nat := 0
  checkedSame : Nat := 0
  checkedProven : Nat := 0
  why : Std.HashMap String Nat := {}

def St.merge (a b : St) : St :=
  { firings := b.firings.fold (fun m k n => m.insert k (m.getD k 0 + n)) a.firings
    fns := a.fns ++ b.fns, errors := a.errors + b.errors, accepted := a.accepted + b.accepted, checkedSame := a.checkedSame + b.checkedSame, checkedProven := a.checkedProven + b.checkedProven
    why := b.why.fold (fun m k n => m.insert k (m.getD k 0 + n)) a.why }

def checkFile (path : System.FilePath) (S : St) : IO St := do
  let data ← IO.FS.readBinFile path
  let .ok e := parseExport data | return S
  let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
  let base : PassEnv :=
    { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
      pgohot := e.pgohot, config := e.config, typs
      typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
      tables := {}, frontend := e.frontendTables, ptrCache := ptrCacheFn e.ptrCache }
  let mut S := S
  let mut tables : Tables := {}
  for h : k in [0:e.sections.size] do
    let s := e.sections[k]
    let prev := tables
    tables := tables.addAll s.defs
    if k == 0 || s.pass.toStringLossy != "lower" then continue
    let env := { base with passName := "lower", tables := prev }
    -- the checked lower against stock
    let full := (← IO.getEnv "LOWER_PROBE_FULL").isSome
    let tbl := if full then lowerTable else lowerProvenTable
    match GoFV.Opt.LowerCheck.checkedLowerWith tbl env (GoFV.Opt.FmaContract.contractAll e.sections[k-1]!.func) with
    | .ok co =>
      if (GoFVTest.Parity.compare prev co tables s).isNone then
        S := { S with checkedSame := S.checkedSame + 1
                      checkedProven := if co.func == e.sections[k-1]!.func then S.checkedProven else S.checkedProven + 1 }
      else if (← IO.getEnv "LOWER_PROBE_MISS").isSome then
        let fc := GoFV.Opt.FmaContract.contractAll e.sections[k-1]!.func
        match rewriteRun tbl true true env fc with
        | .ok (o2, _, log2) =>
          IO.println s!"MISS\t{whyL o2.tables tbl fc o2.func log2}\t{path}"
        | .error _ => pure ()
    | .error _ => pure ()
    match rewriteRun lowerTable true true env e.sections[k-1]!.func with
    | .ok (out, _, log) =>
      let w := whyL out.tables lowerTable e.sections[k-1]!.func out.func log
      let w := if w == "ok" then
          (match check { tabs := out.tables, typs := env.typs } out.func with
            | .ok () => "ok"
            | .error m => s!"check out: {m.take 50}") else w
      let w := if w == "ok" && !tabsAgree prev out.tables e.sections[k-1]!.func then "tabsAgree" else w
      if !(w.startsWith "atoms" || w == "ok" || w == "not lowered") then IO.println s!"FAIL\t{w}\t{path}"
      let w := if w.startsWith "rule" || w.startsWith "setOp" || w.startsWith "blockRule" || w.startsWith "atoms" || w.startsWith "final" then (w.splitOn " v").head! else w
      S := { S with why := S.why.insert w (S.why.getD w 0 + 1), accepted := if w == "ok" then S.accepted + 1 else S.accepted }
      let ks := firedKeys lowerTable e.sections[k-1]!.func log
      let mut fs : Std.HashSet String := {}
      for x in ks do
        S := { S with firings := S.firings.insert x (S.firings.getD x 0 + 1) }
        fs := fs.insert x
      S := { S with fns := S.fns.push fs.toArray }
    | .error _ => S := { S with errors := S.errors + 1 }
  return S

partial def parseArgs : List String → Nat × Array String → Nat × Array String
  | [], o => o
  | "--jobs" :: n :: rest, (_, ps) => parseArgs rest (max (n.toNat?.getD 1) 1, ps)
  | a :: rest, (j, ps) => parseArgs rest (j, ps.push a)

def main (args : List String) : IO UInt32 := do
  let (jobs, paths) := parseArgs args (1, #[])
  let mut files := #[]
  for a in paths do
    let p : System.FilePath := a
    if ← p.isDir then files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  files := files.qsort (·.toString < ·.toString)
  let tasks ← (List.range jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st : St := {}
    for h : i in [0:files.size] do
      if i % jobs == j then st ← checkFile files[i] st
    return st
  let mut acc : St := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => acc := acc.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 2
  -- functions per rule
  let mut nfn : Std.HashMap String Nat := {}
  for fs in acc.fns do
    for x in fs do nfn := nfn.insert x (nfn.getD x 0 + 1)
  IO.println s!"functions {acc.fns.size} errors {acc.errors} without firings {(acc.fns.filter (·.isEmpty)).size} validator accepts (full table) {acc.accepted}"
  IO.println s!"checked lower (proven rules) at stock: {acc.checkedSame} of {acc.fns.size}, of which proven (not the input): {acc.checkedProven}"
  for (k, n) in acc.why.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"WHY\t{n}\t{k}"
  for (k, n) in acc.firings.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"RULE\t{k}\t{n}\t{nfn.getD k 0}"
  -- greedy cover
  let mut S : Std.HashSet String := {}
  let mut pending := acc.fns.filter (!·.isEmpty)
  let mut covered := (acc.fns.filter (·.isEmpty)).size
  let mut step := 0
  while !pending.isEmpty && step < 400 do
    -- the rule whose addition completes the most functions; ties: most functions missing only it
    -- or few others (by the number of pending functions that fire it)
    let mut gain : Std.HashMap String Nat := {}
    let mut freq : Std.HashMap String Nat := {}
    for fs in pending do
      let miss := fs.filter (!S.contains ·)
      if miss.size == 1 then gain := gain.insert miss[0]! (gain.getD miss[0]! 0 + 1)
      for x in miss do freq := freq.insert x (freq.getD x 0 + 1)
    let best := if gain.isEmpty then
        (freq.toArray.qsort (fun a b => a.2 > b.2))[0]?
      else (gain.toArray.qsort (fun a b => a.2 > b.2))[0]?
    match best with
    | none => break
    | some (k, _) =>
      S := S.insert k
      let (done, rest) := pending.partition (·.all S.contains)
      covered := covered + done.size
      pending := rest
      step := step + 1
      IO.println s!"GREEDY\t{step}\t{k}\t{covered}"
  return 0

end GoFVTest.LowerProbe

def main (args : List String) : IO UInt32 := GoFVTest.LowerProbe.main args
