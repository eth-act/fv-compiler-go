import GoFVTest.Parity.Registry
import GoFVTest.Parity.Compare
import GoFV.SSA.Parse
import GoFV.Opt.DecomposeCheck
import GoFV.Opt.TabsAgree

/-!
# `decompose-probe`

For every corpus section whose pass is `decompose user` or `decompose builtin`, run the phi
stage (`Decompose.phiStage`) on the previous section's function and tables and count whether
`DecPhiCheck.decPhiCheck` accepts it (in the phi stage's tables), whether those tables agree
with the input's (`tabsAgree`), and how many sections split no phi. For `decompose user` also
the pass output itself (`decPhiCheck out.tables f out.func`); for `decompose builtin` how many
sections the dec rules change after the phi stage. Rejections print the first failing
condition.

usage: `decompose-probe [--jobs N] <dir|file>...`
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ECCheck GoFV.Opt.DecPhiCheck

namespace GoFVTest.DecomposeProbe

def newWhy (sh : Array Ty) (f g : Func) (m : Array (Option Mean)) (fb : Block) (w : Value) :
    String :=
  match meanAt m w.id with
  | none => s!"new {w.op.name}: no meaning"
  | some (s, π) =>
    if π.isEmpty then s!"new {w.op.name}: empty path"
    else if !Ty.beq (shapeOf sh g w.id) (meanTy sh f s π) then s!"new {w.op.name}: shape"
    else if !fb.values.contains s then s!"new {w.op.name}: block"
    else if w.op == .Phi then
      match f.value? s with
      | some u =>
        if u.op != .Phi then "new Phi: base not a phi"
        else if w.args.size != u.args.size then "new Phi: arity"
        else if !(w.args.toList.zip u.args.toList).all (fun (c, a) => meanIs m c a π) then
          "new Phi: arg meaning"
        else "new Phi: arg shape ≠ phi shape"
      | none => "new Phi: no base"
    else s!"new {w.op.name}: class"

def srcWhy (m : Array (Option Mean)) (u w : Value) : String :=
  if w.block != u.block then "source moved"
  else if !meanIs m u.id u.id [] then "source meaning"
  else if u.op != .Phi then s!"changed {u.op.name}→{w.op.name}"
  else if w.type != u.type then "split phi: type"
  else if isMake w.op then "split phi: Make args"
  else if w.op == .Empty then "split phi: Empty shape"
  else s!"split phi: {w.op.name}"

def blockWhy (sh : Array Ty) (f g : Func) (m : Array (Option Mean)) (bid : ID) : String := Id.run do
  let some fb := f.block? bid | return "no source block"
  let some gb := g.block? bid | return "no target block"
  if gb.kind != fb.kind || gb.controls != fb.controls then return "kind/controls"
  if !fb.values.all (fun x => gb.values.contains x) then return "source value moved/removed"
  for z in gb.values do
    match g.value? z with
    | none => return "unlisted value"
    | some w =>
      if w.id != z then return "value id"
      match f.value? z with
      | some u =>
        if !fb.values.contains z then return "source value in other block"
        if !srcOK sh g m u w then return srcWhy m u w
      | none => if !newOK sh f g m fb w then return newWhy sh f g m fb w
  match schedule f fb, schedule g gb with
  | some of, some og =>
    if of.toList.filter (npOf f fb) != og.toList.filter (npOf f fb) then return "schedule"
  | _, _ => return "no schedule"
  return "?"

def why (tabs : Tables) (f g : Func) : String := Id.run do
  let sh := typeShapes tabs
  let m := meanOf sh f g
  if DomCert.cfgView g != DomCert.cfgView f then return "cfg"
  if g.ownAux != f.ownAux then return "ownAux"
  for b in f.blocks do
    if !blockOK sh f g m b then return blockWhy sh f g m b
  return "?"

/-- Per pass: sections, stage errors, unchanged, accepted, rejected, tabsAgree fails, accepted
on the pass output (user) / dec rules changed something (builtin), pass errors. -/
structure Counts where
  sections : Nat := 0
  stageErrors : Nat := 0
  unchanged : Nat := 0
  ok : Nat := 0
  rejected : Nat := 0
  tabsFail : Nat := 0
  outOk : Nat := 0
  passErrors : Nat := 0
  /-- In the proof's fragment (`decUserOK`/`decBuiltinOK` of the pass output). -/
  frag : Nat := 0
  deriving Inhabited

/-- Why value `x` of `f` is not a split in `g` (`RewriteCheck.ssSplit?`), by class. -/
def splitWhy (tabs : Tables) (f g : Func) (x : ID) : String := Id.run do
  let some fv := f.value? x | return "no fv"
  let some gv := g.value? x | return "no gv"
  match fv.args.toList, (Sem.auxTy tabs fv.aux).asAgg with
  | [dst, sm, mem], .agg fs n =>
    let some smv := f.value? (RewriteCheck.copyEnd tabs f.valueTab f.valueTab.size sm) |
      return "no Make"
    let copy := gv.op == .Copy
    let last := if copy then gv.args[0]?.getD 0 else x
    let r := RewriteCheck.ssWalk g fs.length last
    if !(RewriteCheck.ssMakeOp smv.op) then return s!"stored {smv.op.name}"
    if !Ty.beq (tabs.ty smv.type).asAgg (.agg fs n) then return "Make shape"
    if !(RewriteCheck.layoutsOK n fs && fs.all (·.1 < n) && smv.args.size == fs.length) then
      return "layout"
    if !(gv.id == x && gv.type == fv.type && gv.block == fv.block) then return "target header"
    if !(r.1.length == fs.length && last == (r.1.getLast?.map (·.2)).getD r.2) then return "walk"
    if !RewriteCheck.copyReach tabs f.valueTab f.valueTab.size mem r.2 then return "start"
    for k in List.range fs.length do
      if !RewriteCheck.ssLink tabs f g fv.block dst x fs smv.args r.1 r.2 k then
        let (o, t) := fs[k]!
        let a := smv.args[k]!
        let (p, s) := r.1[k]!
        let some av := f.value? a | return "link: arg"
        let some sv := g.value? s | return "link: store"
        if !RewriteCheck.ssFieldOK (tabs.ty av.type) t then
          let e := (f.value? (RewriteCheck.copyEnd tabs f.valueTab f.valueTab.size a)).map
            fun w => s!"{w.op.name}{(w.args[0]?.bind f.value?).map (fun x => s!"({x.op.name} {repr (tabs.ty x.type)})")}"
          return s!"link: field {repr t} arg {repr (tabs.ty av.type)} {e}"
        if !Ty.beq (Sem.auxTy tabs sv.aux) t then return "link: store shape"
        if !RewriteCheck.ssPtrOK tabs f g fv.block dst p o then return "link: pointer"
        let prev := if k = 0 then r.2 else (r.1[k - 1]?.map (·.2)).getD 0
        if !((f.value? s).isNone || (s == x && k + 1 == r.1.length)) then return "link: not fresh"
        if sv.op != .Store then return s!"link: op {sv.op.name}"
        if sv.block != fv.block then return "link: block"
        if !(sv.args.size == 3 && sv.args[0]! == p && sv.args[2]! == prev) then return "link: args"
        if !RewriteCheck.copyReach tabs f.valueTab f.valueTab.size a sv.args[1]! then
          let sa := (g.value? sv.args[1]!).map (·.op.name)
          return s!"link: stored value {(av.op.name)} vs {sa}"
        return "link: other"
    return "?"
  | _, t => return s!"shape {(repr t).pretty.take 20}"

/-- Why `ssRel f g` fails: the first changed, unsplit value of `f`. -/
def ssWhy (tabs : Tables) (f g : Func) : String := Id.run do
  for x in [0:f.valueTab.size] do
    match f.value? x, g.value? x with
    | some u, some w =>
      if !RewriteCheck.ssSame u w && (RewriteCheck.ssSplit? tabs f g x).isNone then
        return splitWhy tabs f g x
    | _, _ => pure ()
  return "global"

/-- The first event of `log` the strict replay rejects (the lax one of `validate` skips it), by
class. -/
def replayWhy (tabs : Tables) (t : GoFV.Rules.Interp.Table) (f : Func)
    (log : Array GoFV.Rules.RwEvent) : String := Id.run do
  for i in [0:log.size] do
    if (RewriteCheck.replay tabs t f false f.valueTab [] (log.toList.take (i + 1))).isNone then
      let M := match RewriteCheck.replay tabs t f false f.valueTab [] (log.toList.take i) with
        | some (M, _) => M
        | none => f.valueTab
      let some ev := log[i]? | return "?"
      return match ev with
        | GoFV.Rules.RwEvent.rule v j _ _ =>
          match M.get? v with
          | some x =>
            let r := (t.values[x.op.ctorIdx]?).bind (·[j]?)
            let loc := match r with
              | some cr => s!"{cr.rule.loc.1}:{cr.rule.loc.2}"
              | none => if x.op == Op.Store then "store split" else s!"#{j}"
            let extra := if x.op == Op.ITab || x.op == Op.SlicePtr || x.op == Op.StringPtr then
                match x.args[0]? >>= M.get? with
                | some a =>
                  let a0 := (a.args[0]? >>= M.get?)
                  s!" ty {(repr (tabs.ty x.type)).pretty.take 30} arg {a.op.name} arg0 " ++
                    s!"{(a0.map (·.op.name)).getD "-"} {(a0.map fun a0 => (repr (tabs.ty a0.type)).pretty.take 30).getD ""}"
                | none => " noarg"
              else ""
            s!"rule {x.op.name} {loc}{extra}"
          | none => "rule on missing value"
        | .copyArg .. => "copyArg"
        | .control .. => "control"
        | .phielim .. => "phielim"
        | .snap .. => "snap"
        | .blockRule .. => "blockRule"
  return "?"

/-- The first failing conjunct of `RewriteCheck.validate`. -/
def validateWhy (tabs : Tables) (t : GoFV.Rules.Interp.Table) (f g : Func)
    (log : Array GoFV.Rules.RwEvent) : String :=
  if !RewriteCheck.atomsOK f g then "atomsOK"
  else if !RewriteCheck.closedOK f then "closedOK f"
  else if !RewriteCheck.closedOK g then "closedOK g"
  else match RewriteCheck.replay tabs t f true f.valueTab [] log.toList with
    | some (M, B) =>
      if RewriteCheck.finalOK tabs f g M B then "?"
      else if (RewriteCheck.replay tabs t f false f.valueTab [] log.toList).isSome then "finalOK"
      else s!"finalOK: skipped {replayWhy tabs t f log}"
    | none => s!"replay: {replayWhy tabs t f log}"

/-- The first layer of `RewriteCheck.layersOK` that fails (`ld`, `ss`, or the final
`validate`), as `RewriteCheck.layersOK` walks `Ls`. -/
def layersWhy (env : PassEnv) (t : GoFV.Rules.Interp.Table) (f0 : Func) (out : PassOut) :
    List RewriteCheck.Layer → Func → Array GoFV.Rules.RwEvent → String
  | [], f, log =>
    if RewriteCheck.validate out.tables t f out.func log then "?"
    else s!"validate: {validateWhy out.tables t f out.func log}"
  | L :: Ls, f, log =>
    let name := match L with
      | .nil _ => "nil" | .fwd _ => "fwd" | .sl => "sl" | .ss => "ss" | .ld => "ld" | .seg _ => "seg" | .ps => "ps"
      | .pc => "pc"
    match L.pre t out.tables f log with
    | (f', log') =>
      if RewriteCheck.sameLog log'.toList log.toList then layersWhy env t f0 out Ls f log
      else if !RewriteCheck.layerOK env t out.tables f0 L f log f' then
        match L with
        | .ld =>
          let ev := RewriteCheck.ldTaken t out.tables f log
          if RewriteCheck.validate out.tables t f f' ev then "layer ld: check"
          else s!"layer ld: {validateWhy out.tables t f f' ev}"
        | .ss =>
          if RewriteCheck.ssRel out.tables f f' then "layer ss: check"
          else s!"layer ss: {ssWhy out.tables f f'}"
        | _ => s!"layer {name}"
      else layersWhy env t f0 out Ls f' log'

/-- The location `file:line` of the rule of event `.rule v i …` of table `t` on definitions `M`. -/
def ruleLoc (t : GoFV.Rules.Interp.Table) (M : RewriteCheck.Defs) (v i : Nat) : String :=
  match M.get? v with
  | none => "?"
  | some x =>
    let row := (t.values[x.op.ctorIdx]?).getD #[]
    match row[i]? with
    | some cr => s!"{cr.rule.loc.1}:{cr.rule.loc.2}"
    | none =>
      if x.op == Op.Store then
        match t.structStores[i - row.size]? with
        | some cr => s!"{cr.rule.loc.1}:{cr.rule.loc.2}"
        | none => s!"Store #{i}"
      else s!"{x.op.name} #{i}"

/-- Why the proven dec rules' rewrite differs from the pass: the first rule of the full dec
table's run on `g1` that the proven table lacks. -/
def unprovenWhy (env : PassEnv) (t1 : Tables) (g1 : Func) : String := Id.run do
  let .ok (_, _, log) := GoFV.Rules.rewriteRun Decompose.decTable false true { env with tables := t1 } g1
    | return "full rewrite error"
  let proven := Decompose.decProvenTable
  let provenLocs : List String :=
    (proven.values.toList.flatMap fun row => row.toList.map fun cr => s!"{cr.rule.loc.1}:{cr.rule.loc.2}") ++
      proven.structStores.toList.map fun cr => s!"{cr.rule.loc.1}:{cr.rule.loc.2}"
  let mut M : RewriteCheck.Defs := g1.valueTab
  for ev in log do
    match ev with
    | .rule v i _ defs =>
      let loc := ruleLoc Decompose.decTable M v i
      if !provenLocs.contains loc then
        let op := ((RewriteCheck.Defs.get? M v).map (·.op.name)).getD "?"
        return s!"unproven {op} {loc}"
      M := defs.foldl (fun M u => RewriteCheck.Defs.put M u.id u) M
    | _ => pure ()
  return "no unproven rule"

/-- Which segment of `Decompose.decSegsOK` fails (`k`: phi eliminations so far). -/
def segWhy (env : PassEnv) (T : Tables) (f0 g2 : Func) :
    Nat → Func → Array GoFV.Rules.RwEvent → List GoFV.Rules.RwEvent → String
  | k, f, seg, [] =>
    let pre := if k == 0 then "" else s!"phielim seg {k}: "
    pre ++ layersWhy env Decompose.decProvenTable f0 { func := g2, tables := T } RewriteCheck.decLayers f seg
  | k, f, seg, .phielim v d p :: evs =>
    let ce := Decompose.decCheckEnv env T
    let h := RewriteCheck.dropInvalid p
    let h' := RewriteCheck.phiElim h v d.args[0]!
    if !RewriteCheck.layersOK env Decompose.decProvenTable f0 { func := h, tables := T }
        RewriteCheck.decLayers f seg then
      s!"phielim seg {k}: " ++
        layersWhy env Decompose.decProvenTable f0 { func := h, tables := T } RewriteCheck.decLayers f seg
    else if !checkOK ce h then s!"phielim {k}: check pre"
    else if !CopyCheck.copyOK T h h' then
      let bad := (h.blocks.toList.filterMap h.block?).flatMap (·.values.toList) |>.find?
        fun x => !CopyCheck.copyValueOK T h h' x
      match bad.bind h'.value? with
      | some gv =>
        let arg := (gv.args[0]?.bind h'.value?).map fun w => s!"{w.op.name} {repr (T.ty w.type)}"
        s!"phielim {k}: copyOK {gv.op.name} {repr (T.ty gv.type)} of {arg}"
      | none => s!"phielim {k}: copyOK"
    else if !checkOK ce h' then s!"phielim {k}: check elim"
    else segWhy env T f0 g2 (k + 1) h' #[] evs
  | k, f, seg, ev :: evs => segWhy env T f0 g2 k f (seg.push ev) evs

/-- The first failing conjunct of `decBuiltinOK`. -/
def builtinWhy (env : PassEnv) (f : Func) (out : PassOut) : String :=
  match Decompose.phiStage env true f with
  | .error _ => "phi stage error"
  | .ok (t1, g1) =>
    match GoFV.Rules.rewriteRun Decompose.decProvenTable false true { env with tables := t1 } g1 with
    | .error _ => "proven rewrite error"
    | .ok (o2, _, log) =>
      let T := out.tables
      let ce := Decompose.decCheckEnv env T
      if !tabsAgreeMod env.tables T f then "tabsAgreeMod"
      else if !decPhiCheck T f g1 then "decPhiCheck in output tables"
      else if !(check ce g1).isOk then "check phi stage"
      else if !(check ce o2.func).isOk then "check proven rewrite"
      else if !Decompose.decRewriteOK env T g1 o2.func log then
        segWhy env T g1 o2.func 0 g1 #[] log.toList
      else if !Decompose.sameCode o2.func out.func then
        s!"proven rewrite ≠ pass output: {unprovenWhy env t1 g1}"
      else "?"

def Counts.add (a b : Counts) : Counts :=
  { sections := a.sections + b.sections, stageErrors := a.stageErrors + b.stageErrors
    unchanged := a.unchanged + b.unchanged, ok := a.ok + b.ok, rejected := a.rejected + b.rejected
    tabsFail := a.tabsFail + b.tabsFail, outOk := a.outOk + b.outOk
    passErrors := a.passErrors + b.passErrors, frag := a.frag + b.frag }

structure Stats where
  files : Nat := 0
  parseErrors : Nat := 0
  user : Counts := {}
  builtin : Counts := {}
  splitPhis : Nat := 0
  whys : Array (String × Nat) := #[]
  examples : Array (String × String) := #[]

def Stats.addWhy (st : Stats) (key ex : String) : Stats :=
  match st.whys.findIdx? (·.1 == key) with
  | some i => { st with whys := st.whys.modify i fun (k, n) => (k, n + 1) }
  | none => { st with whys := st.whys.push (key, 1), examples := st.examples.push (key, ex) }

def Stats.merge (a b : Stats) : Stats := Id.run do
  let mut st := { a with files := a.files + b.files, parseErrors := a.parseErrors + b.parseErrors
                         user := a.user.add b.user, builtin := a.builtin.add b.builtin
                         splitPhis := a.splitPhis + b.splitPhis }
  for (k, n) in b.whys do
    st := match st.whys.findIdx? (·.1 == k) with
      | some i => { st with whys := st.whys.modify i fun (k, m) => (k, m + n) }
      | none => { st with whys := st.whys.push (k, n) }
  for (k, ex) in b.examples do
    if (st.examples.findIdx? (·.1 == k)).isNone then st := { st with examples := st.examples.push (k, ex) }
  return st

/-- Source `Phi`s that the stage changed. -/
def splitCount (f g : Func) : Nat :=
  f.valueTab.foldl (fun n o => match o with
    | some u => if u.op == .Phi && (g.value? u.id).map (·.op) != some .Phi then n + 1 else n
    | none => n) 0

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
      let builtin := name == "decompose builtin"
      if name != "decompose user" && !builtin then continue
      let env := { base with passName := name, tables := prev
                             zvar := GoFVTest.Parity.zvarFn e.sections[k-1]!.zvar }
      let f := e.sections[k-1]!.func
      let mut c : Counts := { sections := 1 }
      match Decompose.phiStage env builtin f with
      | .error _ => c := { c with stageErrors := 1 }
      | .ok (tabs', g) =>
        st := { st with splitPhis := st.splitPhis + splitCount f g }
        if g.valueTab == f.valueTab then c := { c with unchanged := 1 }
        if !tabsAgree prev tabs' f then c := { c with tabsFail := 1 }
        if decPhiCheck tabs' f g then c := { c with ok := 1 }
        else
          c := { c with rejected := 1 }
          let w := why tabs' f g
          st := st.addWhy s!"{name}: {w}" s!"{path} section {k}"
        if builtin then
          match Decompose.postExpandCallsDecomposePass env f with
          | .error _ => c := { c with passErrors := 1 }
          | .ok out =>
            if out.func.valueTab != g.valueTab then c := { c with outOk := 1 }
            if Decompose.decBuiltinOK env f out then c := { c with frag := 1 }
            else st := st.addWhy s!"{name} (fragment): {builtinWhy env f out}" s!"{path} section {k}"
        else
          match Decompose.decomposeUserPass env f with
          | .error _ => c := { c with passErrors := 1 }
          | .ok out =>
            if decPhiCheck out.tables f out.func then c := { c with outOk := 1 }
            else st := st.addWhy s!"{name} (pass output): {why out.tables f out.func}" s!"{path} section {k}"
            if Decompose.decUserOK env f out then c := { c with frag := 1 }
            else if !tabsAgreeMod env.tables out.tables f then
              st := st.addWhy s!"{name} (fragment): tabsAgreeMod" s!"{path} section {k}"
      st := if builtin then { st with builtin := st.builtin.add c } else { st with user := st.user.add c }
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

def report (name extra : String) (c : Counts) : String :=
  s!"{name}: sections {c.sections}, stage errors {c.stageErrors}, no phi split {c.unchanged}, " ++
    s!"accepted {c.ok}, rejected {c.rejected}, tabsAgree fails {c.tabsFail}, {extra} {c.outOk}, " ++
    s!"pass errors {c.passErrors}, in the proof's fragment (pass output checked) {c.frag}"

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
  IO.println s!"files {st.files}, parse errors {st.parseErrors}, split phis {st.splitPhis}"
  IO.println (report "decompose user (phi stage)" "pass output accepted" st.user)
  IO.println (report "decompose builtin (phi stage)" "dec rules change values" st.builtin)
  let whys := st.whys.qsort fun x y => x.2 > y.2
  for (k, n) in whys do IO.println s!"REJECT {n}: {k}"
  for (k, ex) in st.examples.qsort (fun a b => a.1 < b.1) do IO.println s!"EXAMPLE {k}: {ex}"
  return 0

end GoFVTest.DecomposeProbe

def main (args : List String) : IO UInt32 := GoFVTest.DecomposeProbe.main args
