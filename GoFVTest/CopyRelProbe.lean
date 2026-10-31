import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.CopyElim

open GoFV.SSA GoFV.Opt GoFV.SSA.DomCert

namespace GoFVTest.CopyRelProbe

def argRel (g : Func) (fa w : ID) : Bool :=
  fa == w || ((g.value? fa).any fun u => u.op == .Copy && u.args == #[w])

/-- The copyelim relation on tree blocks; `none` if it holds, else the reason. -/
def copyRel (f g : Func) : Option String × Nat × Nat := Id.run do
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
  return (none, unk, emp)

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
      match copyelim tabs f with
      | .error _ => errs := errs + 1
      | .ok g =>
        if (check env g).toBool == false then
          gfail := gfail + 1
          if shown < 10 then
            IO.println s!"GFAIL {path} {s.index}: {match check env g with | .error m => m | _ => ""}"
            shown := shown + 1
        let (r, u, e) := copyRel f g
        unk := unk + u
        emp := emp + e
        match r with
        | none => ok := ok + 1
        | some msg =>
          bad := bad + 1
          if shown < 30 then
            IO.println s!"BAD {path} {s.index} ({s.pass.toStringLossy}): {msg}"
            shown := shown + 1
  IO.println s!"sections {secs}: rel ok {ok}, bad {bad}, check(g) fails {gfail}, errors {errs}; tree Unknown {unk}, Empty {emp}"
  return 0

end GoFVTest.CopyRelProbe

def main (args : List String) : IO UInt32 := GoFVTest.CopyRelProbe.main args
