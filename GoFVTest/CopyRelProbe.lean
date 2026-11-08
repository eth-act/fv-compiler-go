import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.CopyElim
import GoFV.SSA.Sem.Run
import GoFV.Proof.Pass.CopyFrag
import Std.Data.HashSet

open scoped GoFV.SSA.Sem.Fixed

open GoFV.SSA GoFV.Opt GoFV.SSA.DomCert
deriving instance BEq for GoFV.SSA.Sem.Ty

namespace GoFVTest.CopyRelProbe

def argRel (g : Func) (fa w : ID) : Bool :=
  fa == w || ((g.value? fa).any fun u => u.op == .Copy && u.args == #[w])

/-- The copyelim relation on tree blocks; `none` if it holds, else the reason. -/
def copyRel (tabs : Tables) (f g : Func) : Option String × Nat × Nat := Id.run do
  let c := make f
  let mut unk := 0
  let mut emp := 0
  if g.blocks != f.blocks || g.entry != f.entry || g.valueTab.size != f.valueTab.size then
    return (some "shape", 0, 0)
  for bid in f.blocks do
    if !c.inTree bid then continue
    let some fb := f.block? bid | return (some "fb", 0, 0)
    let some gb := g.block? bid | return (some "gb", 0, 0)
    if fb.kind != gb.kind || fb.succs != gb.succs || fb.preds != gb.preds || fb.values != gb.values
      || fb.controls.size != gb.controls.size then return (some s!"block b{bid}", 0, 0)
    for (fc, gc) in fb.controls.zip gb.controls do
      if !argRel g fc gc then return (some s!"control b{bid}", 0, 0)
    for x in fb.values do
      let some fv := f.value? x | return (some "fv", 0, 0)
      let some gv := g.value? x | return (some "gv", 0, 0)
      if fv.block != gv.block || fv.type != gv.type then return (some s!"v{x} block/type", 0, 0)
      if gv.op == .Unknown && fv.op != .Unknown then unk := unk + 1; continue
      if gv.op == .Empty && fv.op != .Empty then emp := emp + 1; continue
      if fv.op == gv.op then
        if fv.aux != gv.aux || fv.auxInt != gv.auxInt || fv.args.size != gv.args.size then
          return (some s!"v{x} same-op fields", 0, 0)
        for (fa, ga) in fv.args.zip gv.args do
          if !argRel g fa ga then return (some s!"v{x} arg v{fa} -> v{ga}", 0, 0)
      else if fv.op == .Phi && gv.op == .Copy && gv.args.size == 1 then
        let w := gv.args[0]!
        if !fv.args.all (fun a => argRel g a w || a == x) then return (some s!"phi v{x}", 0, 0)
        if (make f).anc (blockOf g w) bid && blockOf g w != bid then pure ()
        else return (some s!"phi v{x} copy of v{w} not strictly dominating", 0, 0)
      else return (some s!"v{x} op {fv.op.name} -> {gv.op.name}", 0, 0)
      if gv.op == .Copy then
        let w := gv.args[0]!
        match g.value? w with
        | some wv => if !GoFV.Proof.CopyElim.retypeEqB (tabs.ty wv.type) (tabs.ty gv.type) then return (some s!"copy shape v{x}", 0, 0)
        | none => return (some s!"copy arg v{w}", 0, 0)
  return (none, unk, emp)

/-- In every tree block, consecutive roots of the schedule are dependency-chained. -/
def rootsChained (f : Func) : Bool := Id.run do
  let c := make f
  for bid in f.blocks do
    if !c.inTree bid then continue
    let some b := f.block? bid | continue
    let some o := GoFV.SSA.Sem.schedule f b | continue
    let inb : Std.HashSet ID := Std.HashSet.ofList (o.toList)
    let mut prev : Option ID := none
    for r in o do
      let some rv := f.value? r | continue
      if GoFV.SSA.Sem.prio rv.op == 0 then continue
      if let some p := prev then
        -- does r depend (transitively, within the block) on p?
        let mut seen : Std.HashSet ID := {}
        let mut stack := #[r]
        let mut found := false
        for _ in [0:o.size + 1] do
          let some x := stack.back? | break
          stack := stack.pop
          for a in ((f.value? x).map (·.args)).getD #[] do
            if a == p then found := true
            if inb.contains a && !seen.contains a then
              seen := seen.insert a
              stack := stack.push a
          -- the loop bound is only fuel; continue until the stack empties
        let mut stack2 := stack
        while !stack2.isEmpty do
          let some x := stack2.back? | break
          stack2 := stack2.pop
          for a in ((f.value? x).map (·.args)).getD #[] do
            if a == p then found := true
            if inb.contains a && !seen.contains a then
              seen := seen.insert a
              stack2 := stack2.push a
        if !found then return false
      prev := some r
  return true

/-- The first condition of `copyFrag` that `f` fails (for the report). -/
def fragWhy (tabs : Tables) (f : Func) : String := Id.run do
  if f.valueTab.size > f.vidLast + 1 then return "size"
  for bid in f.blocks do
    let some b := f.block? bid | continue
    for x in b.values do
      let some v := f.value? x | continue
      if (v.op == .Copy || v.op == .Phi) && !v.args.all (fun a => (f.value? a).any fun w =>
          GoFV.Proof.CopyElim.retypeEqB (tabs.ty w.type) (tabs.ty v.type)) then
        return s!"shape {v.op.name}"
      if v.op == .Copy && GoFV.Proof.CopyElim.zeroSizeB tabs v.type then return "zero-size copy"
      if !GoFV.Proof.CopyElim.chainEnds f.value? (f.valueTab.size + 1) x then return "copy cycle"
  return "?"

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut secs := 0
  let mut ok := 0
  let mut bad := 0
  let mut gfail := 0
  let mut unk := 0
  let mut emp := 0
  let mut errs := 0
  let mut shown := 0
  let mut unchained := 0
  let mut frag := 0
  let mut shownFrag := 0
  let mut fragWhys : Std.HashMap String Nat := {}
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok ex := parseExport data | continue
    let typs := (ex.sections[0]?.bind (·.typs)).getD #[]
    let mut tabs : Tables := {}
    for s in ex.sections do
      tabs := tabs.addAll s.defs
      let f := s.func
      let env : CheckEnv := { tabs, typs }
      if (check env f).toBool == false then continue
      secs := secs + 1
      if GoFV.Proof.CopyElim.copyFrag tabs f then frag := frag + 1
      else
        let why := fragWhy tabs f
        let key := s!"{why} after {s.pass.toStringLossy}"
        fragWhys := fragWhys.insert key (fragWhys.getD key 0 + 1)
        if shownFrag < 10 then
          IO.println s!"NOFRAG {path} {s.index} ({s.pass.toStringLossy}): {why}"
          shownFrag := shownFrag + 1
      match copyelim tabs f with
      | .error _ => errs := errs + 1
      | .ok g =>
        if (check env g).toBool == false then
          gfail := gfail + 1
          if shown < 10 then
            IO.println s!"GFAIL {path} {s.index}: {match check env g with | .error m => m | _ => ""}"
            shown := shown + 1
        let (r, u, e) := copyRel tabs f g
        if !rootsChained f then unchained := unchained + 1
        unk := unk + u
        emp := emp + e
        match r with
        | none => ok := ok + 1
        | some msg =>
          bad := bad + 1
          if shown < 30 then
            IO.println s!"BAD {path} {s.index} ({s.pass.toStringLossy}): {msg}"
            shown := shown + 1
  IO.println s!"sections {secs}: CopyFrag {frag}, rel ok {ok}, bad {bad}, check(g) fails {gfail}, errors {errs}; tree Unknown {unk}, Empty {emp}; roots not chained {unchained}"
  IO.println s!"CopyFrag failures by first failing condition: {fragWhys.toList}"
  return 0

end GoFVTest.CopyRelProbe

def main (args : List String) : IO UInt32 := GoFVTest.CopyRelProbe.main args
