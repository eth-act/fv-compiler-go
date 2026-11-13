import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.Opt.Opt

open scoped GoFV.SSA.Sem.Fixed

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
          | .op o _ _ _ _ _ _ _ => topAll o e || makeTop o (e.ty [])
          | _ => false) then "top"
        else if !Pat.argsOK e.ty [] r.pat then "args"
        else if !leavesOK M I [] r.pat then "leaves"
        else if !resultOK tabs M ev or σ I r x defs then "result"
        else if !nodes.all (fun (n, u) => frameNodeOK tabs ev e r.pat n u) then "frame"
        else if !condFrameOK tabs ev e I r.pat r.cond (GoFV.Proof.Rules.sameLeaves r) then "condFrame"
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
    | .snap .. => return "snap"
    | .blockRule b i nc _ =>
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
            return s!"final: v{x} fields {m.op.name}->{u.op.name} ⟨types {m.type}/{u.type} auxInt {m.auxInt}/{u.auxInt} aux {m.aux.isSome}/{u.aux.isSome}⟩"
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

/-- The first value copyelim's relation checker (`CopyCheck.copyOK`) rejects (diagnostics). -/
def phiWhy (tabs : Tables) (f g : Func) : String := Id.run do
  if !(DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
      g.valueTab.size == f.valueTab.size) then return "copy: cfg/ownAux/size"
  for b in f.blocks do
    let some fb := f.block? b | continue
    for x in fb.values do
      if !CopyCheck.copyValueOK tabs f g x then
        let zs := match f.value? x with
          | some fv => match zeroSizeAggregate tabs fv.type with | .ok true => " zero-size" | _ => ""
          | none => ""
        return s!"copy: v{x}{zs} {desc tabs f 3 x} → {desc tabs g 2 x}"
  return "copy: blocks"

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
    match fv.args.toList, (Sem.auxTy tabs fv.aux).asAgg with
    | [dst, sm, mem], .agg fs n =>
      match f.value? (copyEnd tabs f.valueTab f.valueTab.size sm) with
      | some smv =>
        let copy := gv.op == .Copy
        let last := if copy then gv.args[0]?.getD 0 else x
        let r := ssWalk g fs.length last
        if !ssMakeOp smv.op then s!"stored {desc tabs f 2 smv.id}"
        else if !Sem.Ty.beq (tabs.ty smv.type).asAgg (.agg fs n) then "Make shape"
        else if !(layoutsOK n fs && fs.all (·.1 < n)) then "layout"
        else if smv.args.size != fs.length then "arity"
        else if !(gv.type == fv.type && (copy || (gv.op == .Store && 0 < fs.length))) then
          s!"copy {desc tabs g 2 x}"
        else if !(r.1.length == fs.length && last == (r.1.getLast?.map (·.2)).getD r.2) then
          s!"walk ({fs.length} fields) {desc tabs g 2 last}"
        else if !copyReach tabs f.valueTab f.valueTab.size mem r.2 then
          s!"chain start {desc tabs f 2 mem} vs {desc tabs g 2 r.2}"
        else match (List.range fs.length).find? (fun k => !ssLink tabs f g fv.block dst x fs smv.args r.1 r.2 k) with
          | some k =>
            let ps : List (ID × ID) := r.1
            let detail : String := match fs[k]?, smv.args[k]?, ps[k]? with
              | some (o, t), some a, some (p, s) =>
                let prev : ID := if k = 0 then r.2 else match ps[k - 1]? with
                  | some q => q.2
                  | none => 0
                match f.value? a, g.value? s with
                | some (av : Value), some (sv : Value) =>
                  if !ssFieldOK (tabs.ty av.type) t then
                    s!"field type {repr (tabs.ty av.type)} vs {repr t}: {desc tabs f 2 a}"
                  else if !((f.value? s).isNone || (s == x && k + 1 == r.1.length)) then "store not fresh"
                  else if !(sv.op == Op.Store && sv.block == fv.block && sv.args.size == 3) then
                    s!"store {desc tabs g 1 s}"
                  else if sv.args[0]! != p || sv.args[2]! != prev then "chain"
                  else if !copyReach tabs f.valueTab f.valueTab.size a sv.args[1]! then
                    s!"stored {desc tabs f 2 a} vs {desc tabs g 2 sv.args[1]!}"
                  else if !Sem.Ty.beq (Sem.auxTy tabs sv.aux) t then
                    s!"store type {repr (Sem.auxTy tabs sv.aux)} vs {repr t}"
                  else if !ssPtrOK tabs f g fv.block dst p o then
                    s!"ptr {desc tabs g 2 p} dst {desc tabs f 2 dst} off {o}"
                  else "?"
                | _, _ => "missing"
              | _, _, _ => "index"
            s!"field {k} of {fs.length}: {detail}"
          | none => "ok"
      | none => "no Make"
    | _, _ => s!"store shape {desc tabs f 2 x}"
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
/-- The values of `h` from `a` down the last arguments (diagnostics). -/
def memChain (h : Func) : Nat → ID → List String
  | 0, _ => []
  | k + 1, a => match h.value? a with
    | some v => s!"v{a}:{v.op.name}" :: memChain h k (lastArg v)
    | none => [s!"v{a}:-"]

open GoFV.Rules RewriteCheck in
/-- Which part of `moveSeg?` fails for the `Move` `x` (diagnostics). -/
def moveSegWhy (tabs : Tables) (f g : Func) (x : ID) (fv gv : Value) : String :=
  match fv.op, fv.args.toList with
  | .Move, [d, p, m] =>
    let mc := copyEnd tabs f.valueTab f.valueTab.size m
    let (ns, m0) := freshChain f g 5 (lastArg gv)
    match ns.getLast?, storesC tabs f ns.length (underVarDef f mc) with
    | some z', some (fs, z1) =>
      let z := copyEnd tabs f.valueTab f.valueTab.size z1
      match f.value? z, g.value? z' with
      | some zv, some zv' =>
        let n := fv.auxInt
        let gs := x :: ns.dropLast
        if gv.op != .Store then "anchor op"
        else if m0 != mc then s!"mem {desc tabs f 2 mc} vs {desc tabs g 2 m0}"
        else if !(zv.op == .Zero && zv.args.size == 2 && zv.auxInt == n) then
          s!"zero {desc tabs f 1 z}"
        else if !samePtr tabs f zv.args[0]! p then
          s!"zero ptr {desc tabs f 3 zv.args[0]!} vs {desc tabs f 3 p}"
        else if !(zv'.op == .Zero && zv'.args == #[d, mc] && zv'.auxInt == n && zv'.type == zv.type)
          then s!"fresh zero {desc tabs g 2 z'}"
        else match (fs.zip gs).find? (fun (a, b) => match f.value? a, g.value? b with
            | some sa, some sb => !moveStoreOK tabs f g p d n fv.block sa sb
            | _, _ => true) with
          | some (a, b) => s!"store {desc tabs f 3 a} vs {desc tabs g 3 b} \
              (offFrom {(f.value? a).bind fun sa => offFrom tabs f p 4 sa.args[0]!}, \
              block {(f.value? a).map (·.block)}/{(g.value? b).map (·.block)}/{fv.block}, \
              fresh {(g.value? b).map fun sb => (f.value? sb.args[0]!).isNone}, n {n})"
          | none => "?"
      | _, _ => "missing zero"
    | none, _ => s!"no fresh chain from {desc tabs g 2 (lastArg gv)}"
    | _, none =>
      s!"no stores of {ns.length} under {memChain f 7 (underVarDef f mc)} (g {memChain g 7 (lastArg gv)})"
  | _, _ => "not a Move"

open GoFV.Rules RewriteCheck in
/-- Which part of `tileSeg?` fails for the `Move` `x` (diagnostics). -/
def tileSegWhy (tabs : Tables) (f g : Func) (x : ID) (fv gv : Value) : String :=
  match fv.op, fv.args.toList with
  | .Move, [d, p, m] =>
    let mc := copyEnd tabs f.valueTab f.valueTab.size m
    let (ns, m0) := freshChain f g 5 (lastArg gv)
    match storesC tabs f (ns.length + 1) (underVarDef f mc) with
    | some (fs, _) =>
      let n := fv.auxInt
      let gs := x :: ns
      if gv.op != .Store then "anchor op"
      else if m0 != mc then s!"mem {desc tabs f 2 mc} vs {desc tabs g 2 m0}"
      else match (fs.zip gs).find? (fun (a, b) => match f.value? a, g.value? b with
          | some sa, some sb => !moveStoreOK tabs f g p d n fv.block sa sb
          | _, _ => true) with
        | some (a, b) => s!"store {desc tabs f 3 a} vs {desc tabs g 3 b} \
            (offFrom {(f.value? a).bind fun sa => offFrom tabs f p 4 sa.args[0]!})"
        | none => s!"tiles {storeShapes tabs g gs.reverse} n {n}"
    | none =>
      s!"no stores of {ns.length + 1} under {memChain f 7 (underVarDef f mc)} (g {memChain g 7 (lastArg gv)})"
  | _, _ => "not a Move"

open GoFV.Rules RewriteCheck in
/-- Which part of `callSeg?` fails for the `SelectN` `fv` (diagnostics). -/
def callSegWhy (tabs : Tables) (f g : Func) (fv gv : Value) : String :=
  match fv.args.toList with
  | [c] =>
    match f.value? c with
    | some cv =>
      let args := cv.args.toList
      let n := if args.length ≥ 3 then args[args.length - 2]! else 0
      s!"aux {fv.auxInt} block {cv.block == fv.block} args {args.length} \
        simple {MemCall.simpleCall tabs cv (args.length - 1)} \
        g {gv.op.name}{gv.args.toList} f {args} size {constSize tabs f n gv.auxInt} \
        {desc tabs f 4 n}"
    | none => "no call"
  | _ => "arity"

open GoFV.Rules RewriteCheck in
/-- Which part of `segRel`/`check` fails for the segment-rewritten function `f'` of `f`, if any. -/
def segRelWhy (env : PassEnv) (tabs : Tables) (f f' : Func) : Option String := Id.run do
  for z in List.range f.valueTab.size do
    match f.value? z, f'.value? z with
    | some u, some w =>
      if !ssSame u w && (segOK tabs f f' z).isNone then
        return some s!"v{z} {u.op.name}→{w.op.name}: no segment (chain \
          {(chainSeg? tabs f f' z u w).isSome}, call {(callSeg? tabs f f' u w).isSome}, \
          move {(moveSeg? tabs f f' z u w).isSome}, tile {(tileSeg? tabs f f' z u w).isSome}){if u.op == .Move then
            " ⟨" ++ moveSegWhy tabs f f' z u w ++ "⟩ ⟨tile: " ++ tileSegWhy tabs f f' z u w ++ "⟩" else if u.op == .SelectN then
            " ⟨" ++ callSegWhy tabs f f' u w ++ "⟩" else ""}"
    | _, _ => pure ()
  if !segRel tabs f f' then return some "rel"
  if let .error e := check { tabs := tabs, typs := env.typs } f' then return some s!"check {e}"
  if !RewriteCheck.roSegsOK tabs (RewriteCheck.roSyms env.tables f) f f' then
    let bad := f.blocks.foldl (init := (#[] : Array String)) fun acc b =>
      (WBCheck.vals f b).foldl (init := acc) fun acc x => match f.value? x with
        | some v => if WBCheck.memFree (tabs.ty v.type) || WBCheck.memOpOK v.op then acc
          else acc.push s!"{v.op.name}:{repr (tabs.ty v.type)}"
        | none => acc
    let ro := RewriteCheck.roSyms env.tables f
    let movs := (RewriteCheck.segList (RewriteCheck.segArr tabs f f')).filter fun s =>
      (f.value? s.1).any (·.op == .Move) && (f'.value? s.1).any (·.op == .Zero)
    let srcs := movs.map fun s => match f.value? s.1 with
      | some fv => match fv.args.toList with
        | [_, s, _] => match f.value? s with
          | some sv => s!"v{s} {sv.op.name} {WBCheck.symName? tabs sv.aux} \
              roSym {(RewriteCheck.roSym? tabs sv.aux).map (fun (e : String × Sem.Alloc) => e.1)} \
              inRo {(WBCheck.symName? tabs sv.aux).map fun n => ro.any (·.1 == n)} \
              ok {RewriteCheck.roSrcOK tabs ro f fv}"
          | none => "src?"
        | _ => "arity"
      | none => "?"
    return some s!"ro memTyOK {WBCheck.memTyOK tabs f} bad {bad.toList.eraseDups} srcs {srcs}"
  return none

open GoFV.Rules RewriteCheck in
/-- Which part of `fwdMoveRep` fails for the `Load` `u` of `f` that became `w` in `g`
(diagnostics). -/
def fwdMoveWhy (tabs : Tables) (f g : Func) (u w : Value) : String := Id.run do
  let y := w.args[0]!
  if !listedB g y then return "move: top not listed"
  let some top := g.value? y | return "move: top missing"
  if top.args.size != 2 then return "move: top arity"
  if !listedB g top.args[0]! then return "move: OffPtr not listed"
  let some offp := g.value? top.args[0]! | return "move: OffPtr missing"
  if !(top.op == .Load && top.type == u.type) then return s!"move: top {top.op.name}"
  if !(offp.op == .OffPtr && offp.args.size == 1 && isPtrTy (tabs.ty offp.type)) then
    return s!"move: offp {offp.op.name} {repr (tabs.ty offp.type)}"
  if !(decide (0 ≤ offp.auxInt.toInt) && decide (0 < (tabs.ty u.type).size)) then
    return s!"move: offset {offp.auxInt.toInt} size {(tabs.ty u.type).size}"
  let some mv := f.value? u.args[1]! | return "move: mem missing"
  if !(mv.op == .Move && mv.args.size == 3) then return s!"move: mem {mv.op.name}"
  if !(top.args[1]! == mv.args[2]! && offp.args[0]! == mv.args[1]!) then
    let cr := fun (a b : ID) => copyReach tabs f.valueTab f.valueTab.size a b
    return s!"move: args mem {top.args[1]! == mv.args[2]!}/{cr mv.args[2]! top.args[1]!}/{cr top.args[1]! mv.args[2]!} src {offp.args[0]! == mv.args[1]!}/{cr mv.args[1]! offp.args[0]!}/{cr offp.args[0]! mv.args[1]!}: {desc tabs f 2 mv.args[1]!} vs {desc tabs g 2 offp.args[0]!}"
  if !decide (offp.auxInt.toInt.toNat + (tabs.ty u.type).size ≤ mv.auxInt.toInt.toNat) then
    return s!"move: range {offp.auxInt.toInt}+{(tabs.ty u.type).size} > {mv.auxInt.toInt}"
  return s!"move: ptr {desc tabs f 3 u.args[0]!} vs {desc tabs f 3 mv.args[0]!} + {offp.auxInt.toInt}"

open GoFV.Rules RewriteCheck in
/-- Why `dropOK` fails for the memory root `u` of `f` dropped to `w` of `g` (diagnostics). -/
def dropWhy (tabs : Tables) (f g : Func) (u w : Value) : String :=
  if w.op != .Copy || w.args.size != 1 then s!"{w.op.name}"
  else if u.op == .Store then
    if !memReach tabs f g u.args[2]! w.args[0]! then
      s!"arg v{w.args[0]!} vs mem v{u.args[2]!}"
    else if (Sem.auxTy tabs u.aux).size == 0 then "ok?"
    else if !zeroConst tabs f u.args[1]! then s!"value {desc tabs f 2 u.args[1]!}"
    else s!"chain {desc tabs f 3 u.args[2]!} at {desc tabs f 3 u.args[0]!}"
  else if !memReach tabs f g u.args[1]! w.args[0]! then
    s!"arg v{w.args[0]!} vs mem v{u.args[1]!}"
  else s!"zero {desc tabs f 3 w.args[0]!} at {desc tabs f 3 u.args[0]!}"

open GoFV.Rules GoFV.Proof.Rules RewriteCheck in
/-- Which part of `psRel` fails (diagnostics). -/
def psWhy (tabs : Tables) (f g : Func) : String := Id.run do
  if DomCert.cfgView g != DomCert.cfgView f then return "cfg"
  if g.ownAux != f.ownAux then return "ownAux"
  if g.valueTab.size != f.valueTab.size then return "size"
  for z in List.range f.valueTab.size do
    match f.value? z, g.value? z with
    | none, none => pure ()
    | some fv, some gv =>
      if !(ssSame fv gv || psOK tabs f g z) then
        let sub : String := match psSel fv.op, fv.args[0]?, gv.args[0]? with
          | some k, some p, some x =>
            match f.value? p, f.value? x with
            | some pv, some xv =>
              let ms := pv.args.toList.map fun m => (f.value? m).map fun mv =>
                (mv.op == .SliceMake, mv.args.size == 3 && (mv.args[k]?).any (psComp tabs f · x),
                  isSliceTy (tabs.ty mv.type))
              s!"k={k} phi={pv.op.name} entry={pv.block == f.entry} listed={(f.block? pv.block).any (·.values.contains p)} pslice={isSliceTy (tabs.ty pv.type)} xint={isInt64Ty (tabs.ty xv.type)} xblk={xv.block != pv.block} anc={(DomCert.make f).anc xv.block pv.block} ms={ms} gop={gv.op.name} vint={isInt64Ty (tabs.ty fv.type)}"
            | _, _ => "missing p/x"
          | _, _, _ => s!"sel {fv.op.name}->{gv.op.name}"
        return s!"v{z}: {sub}; f: {desc tabs f 4 z}; g-arg: {desc tabs g 3 (gv.args[0]?.getD 0)}"
    | _, _ => return s!"v{z} presence"
  for b in f.blocks do
    match f.block? b, g.block? b with
    | some fb, some gb =>
      if !(gb.kind == fb.kind && gb.controls == fb.controls && gb.values == fb.values) then
        return s!"b{b} block"
      if Sem.schedule g gb != Sem.schedule f fb then
        return s!"b{b} schedule f={Sem.schedule f fb} g={Sem.schedule g gb}"
    | _, _ => return s!"b{b} missing"
  return "?"

open GoFV.Rules RewriteCheck in
/-- Why `pnRel f g` fails (diagnostics). -/
def pnWhy (tabs : Tables) (f g : Func) : String := Id.run do
  if DomCert.cfgView g != DomCert.cfgView f then return "cfg"
  if g.ownAux != f.ownAux then return "ownAux"
  if g.valueTab.size < f.valueTab.size then return "size"
  for z in List.range g.valueTab.size do
    match f.value? z, g.value? z with
    | none, none => pure ()
    | some fv, some gv =>
      if !(ssSame fv gv || pnOK tabs f g z) then
        return s!"v{z}: {fv.op.name}->{gv.op.name}; f: {desc tabs f 3 z}; g: {desc tabs g 3 z}"
    | none, some _ => if !pnFresh tabs f g z then return s!"v{z}: not a fresh Phi"
    | some _, none => return s!"v{z} dropped"
  for b in f.blocks do
    match f.block? b, g.block? b with
    | some fb, some gb =>
      if !(gb.kind == fb.kind && gb.controls == fb.controls) then return s!"b{b} block"
      if gb.values.toList.filter (fun z => (f.value? z).isSome) != fb.values.toList then
        return s!"b{b} values"
      match Sem.schedule f fb, Sem.schedule g gb with
      | some of, some og =>
        if og.toList.filter (fun z => !pnOK tabs f g z) != of.toList then
          return s!"b{b} schedule f={of} g={og}"
      | _, _ => return s!"b{b} no schedule"
    | _, _ => return s!"b{b} missing"
  return "?"

open GoFV.Rules RewriteCheck in
/-- Why `fixedOK` rejects the fixed load `u` → `w` (issue #69). -/
def fixedWhy (tabs : Tables) (ro : List (String × Sem.Alloc)) (f : Func) (u w : Value) : String :=
  let b := (ptrBase tabs f 8 u.args[0]!).1
  match baseBlk? tabs f b with
  | some (.global n) =>
    match ro.find? (·.1 == n) with
    | none => s!"fixed: symbol not read-only"
    | some e =>
      let ty := tabs.ty u.type
      match fixedSrc n e.2 ty (ptrBase tabs f 8 u.args[0]!).2,
          GoFV.Proof.Rules.opValC tabs w.op ty w.auxInt w.aux [] with
      | some src, some r =>
        let tgt := r.retypeC ty
        if !fixedEq src tgt then s!"fixed: value {w.op.name} <{src.render} vs {tgt.render}>"
        else if !WBCheck.memTyOK tabs f then "fixed: memTy"
        else "fixed: ?"
      | none, _ => "fixed: frame pointer in the symbol"
      | _, none => "fixed: value has a frame pointer"
  | _ => s!"fixed: base {((f.value? b).map (·.op.name)).getD "?"}"

open GoFV.Rules RewriteCheck in
/-- Which part of `fwdRel`/`check` fails for the forwarded function `f'` of `f` (read-only symbols
`ro`, descriptor symbols `eq`), if any. -/
def fwdRelWhy (env : PassEnv) (tabs : Tables) (ro : List (String × Sem.Alloc))
    (eq : List String × List String) (f f' : Func) : Option String := Id.run do
  if !atomsXOK f f' true then return some "atoms"
  if !closedOK f' then return some "closed"
  if !fwdRankOK f (fwdRank f) then return some "rank"
  for z in List.range f.valueTab.size do
    if !fwdRepOK tabs ro eq f f' z then
      match f.value? z, f'.value? z with
      | some u, some w =>
        if u.op == .Store || u.op == .Zero then return some s!"v{z} drop {dropWhy tabs f f' u w}"
        if u.op == .StaticLECall then
          let d := (eqDescW tabs f 8 u.args[0]!).bind (eqSymName? tabs)
          let ok := fun (b : Bool) => if b then "1" else "0"
          return some s!"v{z} eqcall: w {w.op.name}/{w.args.size} sig {ok (eqCallSig tabs u)} desc {d.getD "-"} {desc tabs f 3 u.args[0]!} listed {ok (d.any (eqList tabs eq u).contains)} ok {ok (eqCallOK tabs eq f f' u w)}"
        if u.op == .SelectN then
          return some s!"v{z} selMR: w {w.op.name}/{w.args.size} of {desc tabs f 1 u.args[0]!}"
        if u.op == .SliceLen then
          let s? := f.value? u.args[0]!
          let c := (s?.map (·.args[0]!)).getD 0
          let ok := fun (b : Bool) => if b then "1" else "0"
          return some s!"v{z} grow: w {w.op.name}/{w.args.size} sel {ok (s?.any (·.op == .SelectN))} sliceTy {ok (s?.any (tabs.ty ·.type matches .slice _))} call {ok ((f.value? c).any (growV tabs))} {desc tabs f 1 c} arg {ok ((f.value? c).any (·.args[1]! == w.args[0]!))}"
        if w.op == .Copy && w.args.size == 1 then
          if (f.value? u.args[1]!).any (·.op == .Move) then
            return some s!"v{z} {fwdMoveWhy tabs f f' u w}"
          return some s!"v{z} {fwdOKWhy tabs f u (w.args[0]?.getD 0)}"
        else if u.op == .Load && (w.op == .Addr || w.op == .Const32 || w.op == .Const8 ||
            w.op == .Const64) then
          return some s!"v{z} {fixedWhy tabs ro f u w}"
        else if u.op == .Move && w.op == .Move && u.args.size == 3 && w.args.size == 3 then
          let cr := fun (a b : ID) => copyReach tabs f.valueTab f.valueTab.size a b
          let op := fun (a : ID) => ((f.value? a).map (·.op.name)).getD "?"
          return some s!"v{z} rep Move->Move dst {cr u.args[0]! w.args[0]!} src {cr u.args[1]! w.args[1]!} mem {cr u.args[2]! w.args[2]!} umem {op u.args[2]!} wmem {op w.args[2]!}"
        else return some s!"v{z} rep {u.op.name}->{w.op.name}"
      | _, _ => return some s!"v{z} rep"
  if !fwdRel tabs ro eq f f' then return some (if dcUsesOK tabs eq f f' then "rel" else "dcUses")
  if !fwdRoOK tabs ro f then return some "ro"
  if !checkOK { tabs := tabs, typs := env.typs } f' then return some "check"
  return none

open GoFV.Rules RewriteCheck in
/-- Which layer of `RewriteCheck.layersOK` fails (`f0` the pass's input; diagnostics). -/
def layersWhy (env : PassEnv) (tabs : Tables) (t : Interp.Table) (f0 g : Func) :
    List Layer → Func → Array RwEvent → String
  | [], f, log => why tabs t f g log
  | L :: Ls, f, log =>
    let (f', log') := L.pre t tabs f log
    if RewriteCheck.sameLog log'.toList log.toList then layersWhy env tabs t f0 g Ls f log else
    let k := log.size - log'.size
    let r : Option String := match L with
      | .nil sel =>
        let pre := s!"nil{if sel then "₁" else "₂"}({k})"
        if !NilCheck.nrel true tabs f f' then some s!"{pre}: {nilWhy tabs f f'}"
        else if NilCheck.dictParams tabs f != NilCheck.dictParams env.tables f0 then
          some s!"{pre}: dictionary parameters differ between the tables"
        else if !RewriteCheck.layerOK env t tabs f0 L f log f' then some s!"{pre}: check"
        else none
      | .fwd sel => (fwdRelWhy env tabs (roPass env.tables env.frontend f0)
          (eqPass env.tables env.frontend) f f').map
        (s!"fwd{if sel then "₁" else "₂"}({k}): " ++ ·)
      | .sl =>
        if RewriteCheck.layerOK env t tabs f0 L f log f' then none
        else if let .error e := check { tabs := tabs, typs := env.typs } f' then
          some s!"sl({k}): check {e}"
        else some s!"sl({k}): {why tabs t f f' (slTaken t tabs f log)}"
      | .ss => (ssRelWhy env tabs f f').map (s!"ss({k}): " ++ ·)
      | .seg sel => (segRelWhy env tabs f f').map
        (s!"seg{if sel then "₁" else "₂"}({k}): " ++ ·)
      | .ps =>
        if RewriteCheck.layerOK env t tabs f0 L f log f' then none
        else if !psRel tabs f f' then some s!"ps({k}): psRel {psWhy tabs f f'}"
        else some s!"ps({k}): check"
      | .pc =>
        if RewriteCheck.layerOK env t tabs f0 L f log f' then none
        else if !pcRel tabs f f' then some s!"pc({k}): pcRel"
        else some s!"pc({k}): check"
      | .pn =>
        if RewriteCheck.layerOK env t tabs f0 L f log f' then none
        else if !pnRel tabs f f' then some s!"pn({k}): pnRel {pnWhy tabs f f'}"
        else some s!"pn({k}): check"
      | .ld =>
        if RewriteCheck.layerOK env t tabs f0 L f log f' then none
        else some s!"ld({k}): {why tabs t f f' (ldTaken t tabs f log)}"
    match r with
    | some s => s
    | none =>
      let pre := match L with
        | .nil sel => s!"nil{if sel then "₁" else "₂"}({k})"
        | .fwd sel => s!"fwd{if sel then "₁" else "₂"}({k})"
        | .sl => s!"sl({k})"
        | .ss => s!"ss({k})"
        | .seg sel => s!"seg{if sel then "₁" else "₂"}({k})"
        | .ps => s!"ps({k})"
        | .pc => s!"pc({k})"
        | .pn => s!"pn({k})"
        | .ld => s!"ld({k})"
      s!"{pre} → {layersWhy env tabs t f0 g Ls f' log'}"

open GoFV.Rules RewriteCheck in
/-- Which segment of `RewriteCheck.segsOK` fails (diagnostics; `k`: phi eliminations so far). -/
def segsWhy (env : PassEnv) (tabs : Tables) (t : Interp.Table) (f0 g : Func) (k : Nat) :
    Func → Array RwEvent → List RwEvent → String
  | f, seg, [] => layersWhy env tabs t f0 g layers f seg
  | f, seg, .phielim v d pre :: evs =>
    let ce : CheckEnv := { tabs := tabs, typs := env.typs }
    let h := dropInvalid pre
    let h' := phiElim h v d.args[0]!
    let pk := s!"phielim#{k} v{v}"
    if !layersOK env t f0 { func := h, tables := tabs } layers f seg then
      s!"{pk}: {layersWhy env tabs t f0 h layers f seg}"
    else if let .error e := check ce h then s!"{pk}: check pre {e}"
    else if !CopyCheck.copyOK tabs h h' then s!"{pk}: {phiWhy tabs h h'}"
    else if let .error e := check ce h' then s!"{pk}: check post {e}"
    else s!"{pk} → {segsWhy env tabs t f0 g (k + 1) h' #[] evs}"
  | f, seg, .snap pre :: evs =>
    let h := dropInvalid pre
    let pk := s!"snap#{k}"
    if !layersOK env t f0 { func := h, tables := tabs } layers f seg then
      s!"{pk}: {layersWhy env tabs t f0 h layers f seg}"
    else if let .error e := check { tabs := tabs, typs := env.typs } h then s!"{pk}: check {e}"
    else s!"{pk} → {segsWhy env tabs t f0 g (k + 1) h #[] evs}"
  | f, seg, ev :: evs => segsWhy env tabs t f0 g k f (seg.push ev) evs

/-- Per stock pass name the counts; `fns`/`fnsChecked`: functions (export files) with a rewrite
section, and those whose every rewrite section the checked variant reproduces; `out`: per file
its report lines (`REJECT`, `FALLBACK`, `BLOCKED`). -/
structure St where
  counts : Std.HashMap String Count := {}
  fns : Nat := 0
  fnsChecked : Nat := 0
  out : Array (String × Array String) := #[]

def Count.merge (a b : Count) : Count :=
  { runs := a.runs + b.runs, fullSame := a.fullSame + b.fullSame
    provenSame := a.provenSame + b.provenSame, provenNoop := a.provenNoop + b.provenNoop
    errors := a.errors + b.errors, firedFull := a.firedFull + b.firedFull
    firedProven := a.firedProven + b.firedProven, vStock := a.vStock + b.vStock
    vProven := a.vProven + b.vProven, checkedSame := a.checkedSame + b.checkedSame
    rejected := a.rejected + b.rejected, fallback := a.fallback + b.fallback }

/-- Two workers' results together. -/
def St.merge (a b : St) : St :=
  { counts := b.counts.fold (fun m k c => m.insert k ((m.getD k {}).merge c)) a.counts
    fns := a.fns + b.fns, fnsChecked := a.fnsChecked + b.fnsChecked, out := a.out ++ b.out }

def checkFile (path : System.FilePath) (S : St) : IO St := do
  let data ← IO.FS.readBinFile path
  let .ok e := parseExport data | return S
  let st := S.counts
  let mut rep : Array String := #[]
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
        -- `checkedRewrite`'s fallbacks (without `Phi` selections, then without segment rules,
        -- then without forwardings, then without struct-store splits, then without nil-check
        -- eliminations): rejected, or accepted
        let tp := { proven with phiSels := #[] }
        let t0 := { tp with segs := #[] }
        let t' := { t0 with loads := #[] }
        let t'' := { t' with structStores := #[] }
        let t''' := { t'' with nilChecks := #[] }
        let fbOf (t' : GoFV.Rules.Interp.Table) : Option String :=
          match GoFV.Rules.rewriteRun t' true true env input with
          | .ok (o2, _, log2) =>
            if RewriteCheck.accepts env t' input o2 log2 || o2.func == input then none else
            some (if !tabsAgree prev o2.tables input then "tables"
              else segsWhy env o2.tables t' input o2.func 0 input #[] log2.toList)
          | .error e => some s!"error {e}"
        let fb := if proven.phiSels.isEmpty then some "" else fbOf tp
        let fb := if fb.isSome && !proven.segs.isEmpty then fbOf t0 else fb
        let fb := if fb.isSome && !proven.loads.isEmpty then fbOf t' else fb
        let fb := if fb.isSome && !proven.structStores.isEmpty then fbOf t'' else fb
        let fb := if fb.isSome && !proven.nilChecks.isEmpty then fbOf t''' else fb
        if fb.isSome then c := { c with rejected := c.rejected + 1 }
        else c := { c with fallback := c.fallback + 1 }
        let reason := if !tabsAgree prev out.tables input then
            "tables: the input tells the result's tables from its own (tabsAgree)"
          else segsWhy env out.tables proven input out.func 0 input #[] log.toList
        rep := rep.push s!"{if fb.isSome then "REJECT" else "FALLBACK"} {name} {path}: {reason}"
        if provenSec then blockers := blockers.push s!"{name}: {reason.take 160}"
        if let some r2 := fb then
          if !r2.isEmpty then rep := rep.push s!"  without forwardings: {r2}"
      if (compare prev co tables s).isNone then
        c := { c with checkedSame := c.checkedSame + 1 }
      else allChecked := false
    | .error _ =>
      c := { c with errors := c.errors + 1 }
      allChecked := false
    st := st.insert name c
  if any && allProven && !allChecked then
    rep := rep.push s!"BLOCKED {path}: {" || ".intercalate blockers.toList}"
  return { counts := st, fns := if any then S.fns + 1 else S.fns
           fnsChecked := if any && allChecked then S.fnsChecked + 1 else S.fnsChecked
           out := if rep.isEmpty then S.out else S.out.push (path.toString, rep) }

def pct (a b : Nat) : String :=
  if b == 0 then "-" else
  let x := (a * 10000 + b / 2) / b
  s!"{x / 100}.{if x % 100 < 10 then "0" else ""}{x % 100}%"

partial def parseArgs : List String → Nat × Array String → Nat × Array String
  | [], o => o
  | "--jobs" :: n :: rest, (_, ps) => parseArgs rest (max (n.toNat?.getD 1) 1, ps)
  | a :: rest, (j, ps) => parseArgs rest (j, ps.push a)

/-- `opt-proven-probe [--jobs N] <dir|file>...`: `N` workers, round robin over the files; the
report lines per file in file order, then the table. -/
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
  let mut acc : St := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => acc := acc.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 2
  for (_, ls) in acc.out.qsort (·.1 < ·.1) do
    for l in ls do IO.println l
  let (st, fns, fnsChecked) := (acc.counts, acc.fns, acc.fnsChecked)
  IO.println s!"Functions with a rewrite section: {fns}; every rewrite section at the stock result under the checked proven-only passes: {fnsChecked} ({pct fnsChecked fns})"
  IO.println "| Pass | Runs | Full parity | Proven-only parity | Proven-only no-op | Rules fired (full) | Rules fired (proven-only) | Firings kept | Values stock | Values proven-only | Validator rejects | Forwarding fallbacks | Checked parity | Errors |"
  IO.println "| --- | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: | --: |"
  for (name, _, _) in variants do
    let c := st.getD name {}
    IO.println s!"| {name} | {c.runs} | {pct c.fullSame c.runs} | {pct c.provenSame c.runs} | {pct c.provenNoop c.runs} | {c.firedFull} | {c.firedProven} | {pct c.firedProven c.firedFull} | {c.vStock} | {c.vProven} | {c.rejected} | {c.fallback} | {pct c.checkedSame c.runs} | {c.errors} |"
  return 0

end GoFVTest.OptProvenProbe

def main (args : List String) : IO UInt32 := GoFVTest.OptProvenProbe.main args
