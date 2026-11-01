import GoFV.SSA.Parse
import GoFV.Opt.Fuse
import GoFV.Opt.Fuse.PlainCheck
import GoFV.Opt.ShortCircuit

/-!
# `lake exe fuse-probe <dir>...`: the checked fuse steps on the corpus

For every `early fuse`, `late fuse` and `short circuit` section (input: the previous section),
replays the pass and, at every `fuseBlockPlain` that fires, runs the step checker
(`Fuse.Plain.stepOK`): counts accepted and rejected rewrites and the run lengths.
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.Fuse

namespace GoFVTest.FuseProbe

structure Counts where
  runs : Nat := 0
  len2 : Nat := 0
  len3 : Nat := 0
  len4 : Nat := 0
  accepted : Nat := 0
  rejected : Nat := 0
  shown : Array String := #[]
  deriving Inhabited

def analyze (ce : CheckEnv) (name : String) (f : Func) (b : ID) (k : Counts) : Counts := Id.run do
  let some run := plainRun f b | return k
  let (g, ch) := fuseBlockPlain f b
  if !ch then return k
  let mut k := { k with runs := k.runs + 1 }
  if run.length == 2 then k := { k with len2 := k.len2 + 1 }
  else if run.length == 3 then k := { k with len3 := k.len3 + 1 }
  else k := { k with len4 := k.len4 + 1 }
  if Plain.stepOK ce f g b then k := { k with accepted := k.accepted + 1 }
  else
    k := { k with rejected := k.rejected + 1 }
    if k.shown.size < 10 then k := { k with shown := k.shown.push s!"{name} run {run}" }
  return k

/-- One backwards sweep with `step`, which also gets the counts. -/
def sweep (step : Func → ID → Counts → Except String (Func × Bool × Counts)) (f : Func)
    (k : Counts) : Except String (Func × Bool × Counts) := do
  let blocks := f.blocks
  let mut f := f
  let mut ch := false
  let mut k := k
  for i in [0:blocks.size] do
    let (f', c, k') ← step f blocks[blocks.size - 1 - i]! k
    f := f'; k := k'; ch := c || ch
  return (f, ch, k)

def loop (step : Func → ID → Counts → Except String (Func × Bool × Counts))
    (final : Option (Func → Except String (Func × Bool))) : Nat → Func → Counts →
    Except String (Func × Counts)
  | 0, _, _ => throw "round bound"
  | n + 1, f, k => do
    let (f, ch, k) ← sweep step f k
    let (f, ch) ← match final with
      | some g => do let (f, c) ← g f; pure (f, c || ch)
      | none => pure (f, ch)
    if ch then loop step final n f.invalidateCFG k else return (f, k)

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut ks : Array (String × Counts) :=
    #[("early fuse", {}), ("late fuse", {}), ("short circuit", {})]
  let mut errs := 0
  for path in files do
    let .ok data ← (IO.FS.readBinFile path).toBaseIO | continue
    let .ok e := parseExport data | continue
    let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
    let mut tables : Tables := {}
    for h : j in [0:e.sections.size] do
      let s := e.sections[j]
      let prev := tables
      tables := tables.addAll s.defs
      let pass := s.pass.toStringLossy
      let some idx := ks.findIdx? (·.1 == pass) | continue
      if j == 0 then continue
      let f0 := e.sections[j-1]!.func
      let env : PassEnv :=
        { passName := pass, pkg := e.pkg, funcName := e.name, abi := e.abi,
          nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs,
          typeOrder := default, tables := prev }
      let k := ks[idx]!.2
      let ce : CheckEnv := { tabs := prev, typs }
      let name := s!"{path}"
      let r : Except String (Func × Counts) := do
        let tv ← typeView env
        match pass with
        | "early fuse" =>
          loop (fun f b k => do
            let (f, c1) := fuseComparisons tv.isMem canOptIntInRange f b
            let (f, c2) := fuseComparisons tv.isMem canOptSingleBitDifference f b
            let (f, c3) := fuseComparisons tv.isMem canOptNanCheck f b
            let k := analyze ce name f b k
            let (f, c4) := fuseBlockPlain f b
            pure (f, c1 || c2 || c3 || c4, k)) none roundFuel f0 k
        | "late fuse" =>
          let pv ← Prove.Prover.ofEnv env
          loop (fun f b k => do
            let (f, c1) ← fuseBlockIf tv f b
            let k := analyze ce name f b k
            let (f, c2) := fuseBlockPlain f b
            pure (f, c1 || c2, k)) (some (fuseBranchRedirect pv)) roundFuel f0 k
        | _ =>
          let some boolT := env.typ? "Bool" | throw "no Bool"
          let isBool (t : TypeRef) : Bool := (env.type? t).map (·.kind) == some .BOOL
          let f1 := ShortCircuit.constPhiArgs isBool env.typeOrder.eq boolT f0
          loop (fun f b k => do
            let k := analyze ce name f b k
            let (f, c1) := fuseBlockPlain f b
            let (f, c2) := ShortCircuit.shortcircuitBlock f b
            pure (f, c2 || c1, k)) none roundFuel f1 k
      match r with
      | .ok (_, k') => ks := ks.set! idx (pass, k')
      | .error _ => errs := errs + 1
  for (p, k) in ks do
    IO.println s!"{p}: plain fusions {k.runs} (run length 2: {k.len2}, 3: {k.len3}, ≥4: {k.len4}); accepted {k.accepted}, rejected {k.rejected}"
    for s in k.shown do IO.println s!"  REJECT {s}"
  IO.println s!"errors {errs}"
  return 0

end GoFVTest.FuseProbe

def main (args : List String) : IO UInt32 := GoFVTest.FuseProbe.main args
