import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.Critical
import GoFV.Proof.Pass.CriticalL

open scoped GoFV.SSA.Sem.Fixed

/-!
# `lake exe critical-probe <dir>...`: critical's checker on the corpus

For every section produced by `critical` (input: the previous section), runs the Lean `critical`
on the input and counts the sections whose input and output pass `check`, those the pass changed
(more blocks) and those `GoFV.Proof.Crit.critRelB` accepts, i.e. those `critical_refinesL` covers;
lists the rejections by the first failing condition of `critRelB` and small witness candidates
(accepted, an edge split).
-/

open GoFV.SSA GoFV.Opt GoFV.Proof.Crit

namespace GoFVTest.CriticalProbe

/-- The first failing condition of `critRelB f g` (`none` if it accepts). -/
def why (f g : Func) : Option String := Id.run do
  if g.entry != f.entry then return some "entry"
  if g.ownAux != f.ownAux then return some "ownAux"
  if g.valueTab.size != f.valueTab.size then return some "vsize"
  if g.lowered != f.lowered then return some "lowered"
  for x in List.range (max f.valueTab.size g.valueTab.size) do
    if (g.value? x).map eraseA != (f.value? x).map eraseA then return some "value"
  for bid in List.range f.blockTab.size do
    match f.block? bid with
    | none => pure ()
    | some fb =>
      match g.block? bid with
      | none => return some "block missing"
      | some gb =>
        if gb.kind != fb.kind then return some "block kind"
        if gb.controls != fb.controls then return some "block controls"
        if gb.values != fb.values then return some "block values"
        if gb.auxInt != fb.auxInt then return some "block auxInt"
        if gb.id != fb.id then return some "block id"
        for k in List.range fb.succs.size do
          match fb.succs[k]?, gb.succs[k]? with
          | some e, some e' =>
            if !edgeOKB f g e e' then
              -- follow the splitters from `e'` as `reachB` does
              let mut cur := e'
              for _ in [0:g.blockTab.size + 1] do
                if cur.b == e.b then break
                match g.block? cur.b with
                | some db =>
                  if db.id == cur.b && db.kind == .Plain && db.values.isEmpty then
                    match db.succs[0]? with
                    | some n => cur := n
                    | none => break
                  else break
                | none => break
              if cur.b == e.b then return some "edge: phi args"
              return some "edge: splitters do not lead to the block"
          | _, _ => return some "edge: successor missing"
  if !phiArgsB f g f.entry 0 0 then return some "entry phis"
  return none

structure Cnt where
  secs : Nat := 0
  ran : Nat := 0
  inChecked : Nat := 0
  checked : Nat := 0
  changed : Nat := 0
  accepted : Nat := 0
  acceptedChanged : Nat := 0
  deriving Inhabited

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut c : Cnt := {}
  let mut whys : Std.HashMap String Nat := {}
  let mut rejs : Array String := #[]
  let mut cands : Array (Nat × String) := #[]
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok ex := parseExport data | continue
    let typs := (ex.sections[0]?.bind (·.typs)).getD #[]
    let mut tables : Tables := {}
    let mut prev : Tables := {}
    for h : k in [0:ex.sections.size] do
      let s := ex.sections[k]
      prev := tables
      tables := tables.addAll s.defs
      if k == 0 then continue
      if s.pass.toStringLossy != "critical" then continue
      let f := ex.sections[k-1]!.func
      c := { c with secs := c.secs + 1 }
      match critical f with
      | .error _ => pure ()
      | .ok g =>
        c := { c with ran := c.ran + 1 }
        let okf := (check { tabs := prev, typs } f).toBool
        let okg := (check { tabs := tables, typs } g).toBool
        if okf then c := { c with inChecked := c.inChecked + 1 }
        if okf && okg then
          let acc := critRelB f g
          let w := why f g
          if acc != w.isNone then
            IO.eprintln s!"probe bug: why disagrees with critRelB on {path} section {k - 1}"
            return 2
          let chg := g.blocks.size > f.blocks.size
          c := { c with checked := c.checked + 1, changed := c.changed + (if chg then 1 else 0),
                        accepted := c.accepted + (if acc then 1 else 0),
                        acceptedChanged := c.acceptedChanged + (if acc && chg then 1 else 0) }
          if let some r := w then
            whys := whys.insert r (whys.getD r 0 + 1)
            if rejs.size < 20 then rejs := rejs.push s!"{path} section {k - 1}: {r}"
          if acc && chg then
            let nv := f.blocks.foldl (fun n bid => n + (((f.block? bid).map (·.values.size)).getD 0)) 0
            cands := cands.push (nv, s!"{path} section {k - 1}: {f.blocks.size} blocks, {nv} values -> {g.blocks.size} blocks")
  IO.println s!"critical: sections {c.secs}, Lean pass ok {c.ran}, input checked {c.inChecked}, both checked {c.checked}, changed {c.changed}, critRelB accepted {c.accepted} (changed {c.acceptedChanged}), rejected {c.checked - c.accepted}"
  IO.println "rejections (first failing condition):"
  for (k, n) in whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  for r in rejs do
    IO.println s!"  {r}"
  IO.println "witness candidates (accepted, an edge split), smallest first:"
  for (_, l) in (cands.qsort (fun a b => a.1 < b.1)).extract 0 20 do
    IO.println s!"  {l}"
  return 0

end GoFVTest.CriticalProbe

def main (args : List String) : IO UInt32 := GoFVTest.CriticalProbe.main args
