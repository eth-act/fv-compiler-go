import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.Schedule
import GoFV.Opt.ScheduleCheck

/-!
# `lake exe schedl-probe [--jobs N] <dir>...`: `scheduleCheck` on the corpus

For every `schedule` section (input: the previous section), runs the Lean `schedule` on the
input and counts the sections whose input passes `check` (the hypothesis of
`schedule_refinesSchedLF`; the output's `check` is reported, not needed), those the pass changed,
and those `scheduleCheck` accepts (what `schedule_refinesSchedLF` covers); for the rejected ones
the first failing condition, and small accepted witness candidates.
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ScheduleCheck

namespace GoFVTest.SchedLProbe

structure Cnt where
  secs : Nat := 0
  passErr : Nat := 0
  outUnchecked : Nat := 0
  checked : Nat := 0
  changed : Nat := 0
  accepted : Nat := 0
  acceptedChanged : Nat := 0
  whys : Std.HashMap String Nat := {}
  cands : Array (Nat × String) := #[]

def Cnt.merge (a b : Cnt) : Cnt :=
  { secs := a.secs + b.secs, passErr := a.passErr + b.passErr, checked := a.checked + b.checked
    outUnchecked := a.outUnchecked + b.outUnchecked
    changed := a.changed + b.changed, accepted := a.accepted + b.accepted
    acceptedChanged := a.acceptedChanged + b.acceptedChanged
    whys := b.whys.fold (fun m k n => m.insert k (m.getD k 0 + n)) a.whys
    cands := a.cands ++ b.cands }

def clsName : Cls → String
  | .safe => "safe" | .load => "load" | .nil => "nil" | .other => "other"

def opName (tabs : Tables) (f : Func) (x : ID) : String :=
  match f.value? x with
  | some v => s!"{v.op.name}/{clsName (cls tabs v)}{if mayPanic tabs v then "" else "/nopanic"}"
  | none => "none"

/-- The first failing condition of `scheduleCheck tabs f g`. -/
def why (tabs : Tables) (f g : Func) : String := Id.run do
  if g.entry != f.entry then return "entry"
  if g.ownAux != f.ownAux then return "ownAux"
  if g.lowered != f.lowered then return "lowered"
  if g.valueTab.size != f.valueTab.size then return "valueTab size"
  if g.blockTab.size != f.blockTab.size then return "blockTab size"
  for id in List.range f.valueTab.size do
    if !valueOK f g id then
      match f.value? id, g.value? id with
      | some fv, some gv =>
        if gv.args != fv.args.map (rep f) then return s!"value args {fv.op.name}"
        if !(fv.op.nilCheck || gv.type == fv.type) then return s!"value type {fv.op.name}"
        return s!"value other {fv.op.name}"
      | _, _ => return "value presence"
  for b in List.range f.blockTab.size do
    if !blockOK f g b then
      match f.block? b, g.block? b with
      | some fb, some gb =>
        if gb.controls != fb.controls.map (rep f) then return "block controls"
        if !gb.values.toList.isPerm (fb.values.toList.filter (!isSPA f ·)) then
          return "block values perm"
        return "block other"
      | _, _ => return "block presence"
  if !usesOK tabs f then
    let tys := (Ctx.makeL tabs f).tys
    for o in f.valueTab do
      if let some u := o then
        for k in List.range u.args.size do
          let a := u.args[k]!
          if !useOK tabs tys f (some u) k a then
            let p := rep f a
            if isSPA f a then return s!"use of SPanchored by {u.op.name} (arg {k}, rep {opName tabs f p})"
            if isNC f p then return "use: nil check chain"
            return s!"use: nil check type ({repr (tys[a]?.getD .other)} vs {repr (tys[p]?.getD .other)})"
    return "uses (control)"
  let sS := (Ctx.makeL tabs f).sched
  let sT := (Ctx.makeSched tabs g).sched
  for b in List.range f.blockTab.size do
    if (f.block? b).isNone then continue
    match sS[b]?.join, sT[b]?.join with
    | some oS, some oT =>
      if let some gb := g.block? b then
        if oT.toList != gb.values.toList.filter (!isPhi g ·) then return "target order: not the block's non-Phis"
        if !topoB g oT.toList then return "target order: not topological"
      else return "block presence (orders)"
      if !orderOK tabs f f.valueTab.size oS oT then
        let pS := posFill oS.toList 0 (Array.replicate f.valueTab.size 0)
        let ns := oT.filter (mayFail tabs f)
        for l in List.range ns.size do
          for k in List.range l do
            let x := ns[l]!
            let y := ns[k]!
            if pS[x]! < pS[y]! && !swapOK tabs f x y then
              let sameMem := match f.value? x, f.value? y with
                | some vx, some vy => s!"{vx.args.back? == vy.args.back?}, same ptr {vx.args[0]? == vy.args[0]?}, y ptr {(vy.args[0]?.bind f.value?).map (fun (u : Value) => u.op.name)} x base {(vx.args[0]?.bind f.value?).map (fun (u : Value) => u.op.name)}"
                | _, _ => "?"
              return s!"order: src {opName tabs f x} before {opName tabs f y} (same mem {sameMem})"
        return "order ?"
    | none, _ => return "no runL order"
    | _, none => return "no runSched order"
  return "accepted"

def listed (f : Func) : Nat :=
  f.blocks.foldl (fun n bid => n + (((f.block? bid).map (·.values.size)).getD 0)) 0

def doFile (pass : String) (path : System.FilePath) (c : Cnt) : IO Cnt := do
  let data ← IO.FS.readBinFile path
  let .ok e := parseExport data | return c
  let typs := (e.sections[0]?.bind (·.typs)).getD #[]
  let base : PassEnv :=
    { passName := pass, pkg := e.pkg, funcName := e.name, abi := e.abi
      nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs
      typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp, tables := {}
      frontend := e.frontendTables }
  let mut c := c
  let mut tables : Tables := {}
  for h : k in [0:e.sections.size] do
    let s := e.sections[k]
    let prev := tables
    tables := tables.addAll s.defs
    if k == 0 || s.pass.toStringLossy != pass then continue
    c := { c with secs := c.secs + 1 }
    let env := { base with tables := prev }
    let f := e.sections[k-1]!.func
    match schedulePass env f with
    | .error _ => c := { c with passErr := c.passErr + 1 }
    | .ok out =>
      let g := out.func
      let cf := check { tabs := prev, typs } f
      let cg := check { tabs := out.tables, typs } g
      if !cf.toBool then
        let msg := match cf with
          | .error m => ((m.splitOn ":").headD m).toList.take 60 |> String.ofList
          | .ok _ => ""
        let key := "input not checked: " ++ msg
        c := { c with whys := c.whys.insert key (c.whys.getD key 0 + 1) }
        continue
      if !cg.toBool then c := { c with outUnchecked := c.outUnchecked + 1 }
      let ch := g != f
      c := { c with checked := c.checked + 1, changed := c.changed + (if ch then 1 else 0) }
      if scheduleCheck prev f g then
        c := { c with accepted := c.accepted + 1
                      acceptedChanged := c.acceptedChanged + (if ch then 1 else 0) }
        if ch then
          c := { c with cands := c.cands.push (listed f, s!"{path} section {k - 1} -> {k}: {f.blocks.size} blocks, {listed f} values") }
      else
        let w := why prev f g
        c := { c with whys := c.whys.insert w (c.whys.getD w 0 + 1) }
  -- keep only the smallest candidates
  return { c with cands := (c.cands.qsort (fun a b => a.1 < b.1)).extract 0 20 }

def files (args : List String) : IO (Array System.FilePath) := do
  let mut fs := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      fs := fs ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else fs := fs.push p
  return fs.qsort (·.toString < ·.toString)

def main (args : List String) : IO UInt32 := do
  let (jobs, args) := match args with
    | "--jobs" :: n :: rest => (n.toNat?.getD 1, rest)
    | _ => (1, args)
  let fs ← files args
  let chunk := (fs.size + jobs - 1) / max jobs 1
  let mut tasks := #[]
  for j in [0:jobs] do
    let part := fs.extract (j * chunk) ((j + 1) * chunk)
    tasks := tasks.push (← IO.asTask (part.foldlM (fun c p => doFile "schedule" p c) {}))
  let mut c : Cnt := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok x => c := c.merge x
    | .error err => IO.eprintln s!"task error: {err}"; return 1
  IO.println s!"schedule: sections {c.secs}, pass errors {c.passErr}, input checked {c.checked} (output not checked {c.outUnchecked}), changed {c.changed}, scheduleCheck accepted {c.accepted} (changed {c.acceptedChanged}), rejected {c.checked - c.accepted}"
  IO.println "outside (first failing condition):"
  for (k, n) in c.whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  IO.println "witness candidates (accepted, changed), smallest first:"
  for (_, l) in (c.cands.qsort (fun a b => a.1 < b.1)).extract 0 20 do
    IO.println s!"  {l}"
  return 0

end GoFVTest.SchedLProbe

def main (args : List String) : IO UInt32 := GoFVTest.SchedLProbe.main args
