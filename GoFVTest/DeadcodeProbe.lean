import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.Deadcode
import GoFV.Proof.Pass.DeadcodePass

/-!
# `lake exe deadcode-probe <dir>...`: deadcode's fragment on the corpus

For every section produced by a deadcode instance (input: the previous section), runs the Lean
`deadcode` on the input and counts the sections whose input and output pass `check` and whose
input is in `GoFV.Proof.Dead.DeadFrag` (`deadRelB`, the general `Chained` condition, no
`NilCheck`), and in its decidable sufficient condition `deadFragB`; reports the first failing
condition of `deadRelB` by pass instance, and lists small witness candidates (in the fragment,
a block and a value removed).
-/

open GoFV.SSA GoFV.Opt GoFV.Proof.Dead

namespace GoFVTest.DeadcodeProbe

/-- In every kept block, consecutive priority-2 roots of the schedule are dependency-chained
(so every two are: the general `Chained` condition). -/
def chainedGen (f : Func) (B : Array ID) : Bool := Id.run do
  for bid in B do
    let some b := f.block? bid | continue
    let some o := GoFV.SSA.Sem.schedule f b | continue
    let inb : Std.HashSet ID := Std.HashSet.ofList o.toList
    let mut prev : Option ID := none
    for r in o do
      let some rv := f.value? r | continue
      if GoFV.SSA.Sem.prio rv.op != 2 then continue
      if let some p := prev then
        let mut seen : Std.HashSet ID := {}
        let mut stack := #[r]
        let mut found := false
        while !stack.isEmpty do
          let some x := stack.back? | break
          stack := stack.pop
          for a in ((f.value? x).map (·.args)).getD #[] do
            if a == p then found := true
            if inb.contains a && !seen.contains a then
              seen := seen.insert a
              stack := stack.push a
        if !found then return false
      prev := some r
  return true

/-- The first condition of `deadRelB` that fails (for the report). -/
def why (f g : Func) : String := Id.run do
  if g.entry != f.entry || g.ownAux != f.ownAux || g.valueTab.size != f.valueTab.size then
    return "shape"
  for bid in g.blocks do
    let some gb := g.block? bid | return "no gb"
    let some fb := f.block? bid | return "no fb"
    if !f.blocks.contains bid then return "block not in f"
    if !kindRelB fb.kind gb.kind then return "kind"
    if gb.controls != fb.controls then return "controls"
    if !gb.values.all (fb.values.contains ·) then return "values"
    for k in [0:fb.succs.size] do
      if fb.kind == .First && k != 0 then continue
      match fb.succs[k]?, gb.succs[k]? with
      | some e, some e' =>
        if e'.b != e.b then return "edge target"
        if !phiArgsB f g e.b e.i e'.i then return "phi args"
      | _, _ => return "edge missing"
    for x in gb.values do
      match g.value? x, f.value? x with
      | some gv, some fv =>
        if gv.type != fv.type then return "type"
        if (gv.op == .Phi) != (fv.op == .Phi) then return s!"{fv.op.name} -> {gv.op.name}"
        if gv.op != .Phi && (gv.op != fv.op || gv.aux != fv.aux || gv.auxInt != fv.auxInt) then
          return s!"{fv.op.name} -> {gv.op.name}"
        if gv.op != .Phi && gv.args != fv.args then return "args"
      | some _, none => return "no fv"
      | none, _ => pure ()
    for x in fb.values do
      if gb.values.contains x then continue
      if let some fv := f.value? x then
        if panickingB fv.op then return s!"dropped {fv.op.name}"
  return "?"

def listedCount (f : Func) : Nat :=
  f.blocks.foldl (fun n bid => n + (((f.block? bid).map (·.values.size)).getD 0)) 0

structure Cnt where
  secs : Nat := 0
  checked : Nat := 0
  rel : Nat := 0
  chained : Nat := 0
  noNil : Nat := 0
  frag : Nat := 0
  fragB : Nat := 0
  blocksRemoved : Nat := 0
  valuesRemoved : Nat := 0
  fragBlocks : Nat := 0
  fragValues : Nat := 0
  deriving Inhabited

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut c : Cnt := {}
  let mut byPass : Std.HashMap String Cnt := {}
  let mut whys : Std.HashMap String Nat := {}
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
      let name := s.pass.toStringLossy
      if !(name.endsWith "deadcode") then continue
      let f := ex.sections[k-1]!.func
      let mut pc := byPass.getD name {}
      c := { c with secs := c.secs + 1 }
      pc := { pc with secs := pc.secs + 1 }
      match deadcode prev f with
      | .error _ => pure ()
      | .ok g =>
        let okf := (check { tabs := prev, typs } f).toBool
        let okg := (check { tabs := tables, typs } g).toBool
        if okf && okg then
          let rel := deadRelB f g
          let ch := chainedGen f g.blocks
          let nn := noNilB f
          let frag := rel && ch && nn
          let fragB := deadFragB prev f
          let bRem := g.blocks.size < f.blocks.size
          let vRem := listedCount g < listedCount f
          let upd (x : Cnt) : Cnt :=
            { x with checked := x.checked + 1, rel := x.rel + (if rel then 1 else 0),
                     chained := x.chained + (if ch then 1 else 0),
                     noNil := x.noNil + (if nn then 1 else 0),
                     frag := x.frag + (if frag then 1 else 0),
                     fragB := x.fragB + (if fragB then 1 else 0),
                     blocksRemoved := x.blocksRemoved + (if bRem then 1 else 0),
                     valuesRemoved := x.valuesRemoved + (if vRem then 1 else 0),
                     fragBlocks := x.fragBlocks + (if frag && bRem then 1 else 0),
                     fragValues := x.fragValues + (if frag && vRem then 1 else 0) }
          c := upd c
          pc := upd pc
          if !rel then
            let key := s!"{name}: {why f g}"
            whys := whys.insert key (whys.getD key 0 + 1)
          if fragB && bRem && vRem then
            cands := cands.push (listedCount f, s!"{path} section {k - 1} -> {k} ({name}): {f.blocks.size} blocks, {listedCount f} values -> {g.blocks.size} blocks, {listedCount g} values")
      byPass := byPass.insert name pc
  let fmt (n : String) (x : Cnt) : String :=
    s!"{n}: sections {x.secs}, both checked {x.checked}, DeadRel {x.rel}, Chained {x.chained}, no NilCheck {x.noNil}, DeadFrag {x.frag}, deadFragB {x.fragB}; blocks removed {x.blocksRemoved} (in DeadFrag {x.fragBlocks}), values removed {x.valuesRemoved} (in DeadFrag {x.fragValues})"
  IO.println (fmt "all" c)
  for (n, x) in byPass.toList do
    IO.println (fmt n x)
  IO.println "DeadRel failures (first failing condition):"
  for (k, n) in whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  IO.println "witness candidates (deadFragB, a block and a value removed), smallest first:"
  for (_, l) in (cands.qsort (fun a b => a.1 < b.1)).extract 0 20 do
    IO.println s!"  {l}"
  return 0

end GoFVTest.DeadcodeProbe

def main (args : List String) : IO UInt32 := GoFVTest.DeadcodeProbe.main args
