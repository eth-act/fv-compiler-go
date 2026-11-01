import GoFV.SSA.Parse
import GoFV.Opt.Fuse
import GoFV.Opt.Fuse.PlainCheck
import GoFV.Opt.Fuse.ComparisonsCheck
import GoFV.Opt.Fuse.IfCheck
import GoFV.Opt.Fuse.BranchRedirectCheck
import GoFV.Opt.ShortCircuit
import GoFV.Opt.SpecSafe

/-!
# `lake exe fuse-probe <dir>...`: the checked fuse steps on the corpus

For every `early fuse`, `late fuse` and `short circuit` section (input: the previous section),
replays the pass and, at every `fuseBlockPlain` that fires, runs the step checker
(`Fuse.Plain.snapOf`, then `postOK` on the result): counts accepted and rejected rewrites and
the run lengths. In late fuse, every `fuseBlockIf` rewrite is also run through its checker
(`IfC.stepOK`; `if: CHECK accepted/rejected`, with the first failing part of a rejection) and
its shape counted (`analyzeIf`); every `fuseBranchRedirect` redirect is classified by how its
infeasibility follows from the two controls (`classifyRedirect`: the same control, a syntactic
complement, a comparison of one variable with constants, or `other`).
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
  /-- comparison fusions (early fuse) -/
  cmps : Nat := 0
  /-- … whose shared successor has a `Phi` with different arguments along `p`'s and `b`'s edges -/
  cmpPhiDiffer : Nat := 0
  /-- … whose shared successor has a `Phi` -/
  cmpSPhi : Nat := 0
  /-- … where a `Phi` of the shared successor becomes a `Copy` -/
  cmpPhiCopy : Nat := 0
  /-- … where some value of `b` is not speculation-safe (`specSafeOp`) -/
  cmpUnsafe : Nat := 0
  /-- … where the shared successor is `p` -/
  cmpSIsP : Nat := 0
  /-- … where the new value's ID is beyond the input's value table -/
  cmpNewBeyond : Nat := 0
  /-- comparison fusions the step checker (`Cmp.stepOK`) rejects -/
  cmpRejected : Nat := 0
  /-- fuseBlockIf shape statistics (name, count) -/
  ifStats : Array (String × Nat) := #[]
  shown : Array String := #[]
  deriving Inhabited

def Counts.bump (k : Counts) (s : String) (n : Nat := 1) : Counts :=
  match k.ifStats.findIdx? (·.1 == s) with
  | some i => { k with ifStats := k.ifStats.modify i fun (a, c) => (a, c + n) }
  | none => { k with ifStats := k.ifStats.push (s, n) }

def isRootOp (op : Op) : Bool := Sem.isRoot op

/-- The checked fuseBlockIf step on one rewrite: accepted, or the first failing part. -/
def checkIf (tv : TypeView) (name : String) (f g : Func) (b : ID)
    (k : Counts) : Counts := Id.run do
  if IfC.stepOK tv f g b then return k.bump "CHECK accepted"
  let k := k.bump "CHECK rejected"
  let some s := IfC.siteOf tv f b | return k.bump "reject: no site"
  let R := IfC.Site.resetOf f g
  let why :=
    if !(f.blocks.contains s.b && f.blocks.contains s.ss && s.ss != s.b && s.j0 != s.j1) then "shape basics"
    else if !(s.sideOK f s.arm0 s.e0 s.j0) then
      s!"side 0: arm0 {s.arm0} e0 {s.e0.b},{s.e0.i} ss {s.ss} j0 {s.j0} preds {(f.getB s.e0.b).preds.toList.map fun e => (e.b, e.i)} kind {(f.getB s.e0.b).kind.name} vals {(f.getB s.e0.b).values.toList.map fun x => (x, (f.getV x).op.name)} g-kind {(g.getB s.e0.b).kind.name} g-vals {(g.getB s.e0.b).values.toList.map fun x => (x, (g.getV x).op.name)}"
    else if !(s.sideOK f s.arm1 s.e1 s.j1) then "side 1"
    else if !(s.phisOK f R) then "phis"
    else if !(s.shapeOK f R) then "shape"
    else if !(g.entry == f.entry && g.ownAux == f.ownAux && g.valueTab.size == f.valueTab.size && g.blocks == f.blocks) then "globals"
    else if !(R.all (IfC.Site.resetOK f g)) then "resetOK"
    else if !(!s.unlinked f || s.arm0.all fun a => (valsOf f a).all (IfC.Site.invalidIn g)) then
      s!"arm0 not reset: arm0 {s.arm0} arm1 {s.arm1} ss {s.ss} " ++
        toString ((s.arm0.map (valsOf f)).getD #[] |>.toList.map fun x =>
          (x, (f.getV x).op.name, (f.getV x).uses, (f.getV x).type, (g.getV x).op.name, (g.getV x).block))
    else if !((List.range f.valueTab.size).all (s.valueOK f g R)) then "valueOK"
    else if !((List.range f.valueTab.size).all (s.blkOK f g)) then "blkOK"
    else "blockOK"
  let k := k.bump s!"reject: {why}"
  if k.shown.size < 10 then return { k with shown := k.shown.push s!"{name} b{b}: {why}" }
  return k

/-- Shape of a fuseBlockIf rewrite of `f` into `g` at `b`. -/
def analyzeIf (tv : TypeView) (name : String) (f g : Func) (b : ID) (k : Counts) : Counts := Id.run do
  let mut k := k.bump "fires"
  let bb := f.getB b
  let plainEmpty (s : ID) : Bool := (f.getB s).kind == .Plain && isEmpty tv f s
  let e0 := bb.succs[0]!
  let (s0, ss0, i0) :=
    if !plainEmpty e0.b then (b, e0.b, e0.i)
    else let e := (f.getB e0.b).succs[0]!; (e0.b, e.b, e.i)
  let e1 := bb.succs[1]!
  let (s1, ss1, i1) :=
    if !plainEmpty e1.b then (b, e1.b, e1.i)
    else let e := (f.getB e1.b).succs[0]!; (e1.b, e.b, e.i)
  -- the general shape: side 0 is `s0` (arm, or b: direct) into `ss` at `i0`, side 1 likewise
  let (s0, ss, i0, s1, i1) :=
    if ss0 == ss1 then (s0, ss0, i0, s1, i1)
    else if s0 == ss1 then (b, ss1, e0.i, s1, i1)
    else (s0, ss0, i0, b, e1.i)
  if ss0 != ss1 then k := k.bump "weird (ss0 != ss1)"
  if e0.b == e1.b then k := k.bump "e0.b == e1.b"
  if e0.b == e1.b && s0 != b then k := k.bump "e0.b == e1.b with arms"
  if s0 == s1 && s0 != b then k := k.bump "s0 == s1 arm"
  if s0 == b then k := k.bump "side0 direct"
  if s1 == b then k := k.bump "side1 direct"
  if s0 == b && s1 == b then k := k.bump "both direct"
  if s0 != b && (f.getB s0).preds != #[⟨b, 0⟩] then k := k.bump "s0 preds != [b,0]"
  if s1 != b && (f.getB s1).preds != #[⟨b, 1⟩] then k := k.bump "s1 preds != [b,1]"
  if s0 != b && (g.getB s0).kind == .Invalid then k := k.bump "s0 unlinked"
  if s0 != b && (f.getB s0).values.size > 0 then k := k.bump "s0 has values"
  if s1 != b && (f.getB s1).values.size > 0 then k := k.bump "s1 has values"
  if s1 != b && (f.getB s1).values.any (fun v => !specSafeOp (f.getV v).op) then
    k := k.bump "s1 value not specSafe"
  if s0 != b && (f.getB s0).values.any (fun v => (g.getV v).op != .Invalid) then
    k := k.bump "s0 value not reset"
  if ss == b then k := k.bump "ss == b"
  if ss == s0 || ss == s1 then k := k.bump "ss is an arm"
  if ss == f.entry then k := k.bump "ss is entry"
  if (f.getB ss).preds.size - 1 == i0 then k := k.bump "ss j0 is last"
  -- arm values read outside the arms
  let armVal (a : ID) : Bool := (s0 != b && (f.getB s0).values.contains a) ||
    (s1 != b && (f.getB s1).values.contains a)
  let mut armRead := false
  for h : i in [0:f.valueTab.size] do
    match f.valueTab[i] with
    | some y => if !armVal i && f.blocks.contains y.block && y.args.any armVal then armRead := true
    | none => pure ()
  for bid in f.blocks do
    if (f.getB bid).controls.any armVal then armRead := true
  if armRead then k := k.bump "arm value read outside arms"
  -- ss phis
  let mut differ := false
  let mut toCopy := false
  let mut argBad := false
  for v in (f.getB ss).values do
    let x := f.getV v
    if x.op == .Phi then
      if x.args[i0]? != x.args[i1]? then differ := true
      if (g.getV v).op != .Phi then toCopy := true
      if let some a := x.args[i0]? then
        let ab := (f.getV a).block
        if (ab == s0 && s0 != b) || (ab == s1 && s1 != b) || (g.getV a).op == .Invalid then
          argBad := true
  if differ then k := k.bump "ss phi args differ"
  if toCopy then k := k.bump "ss phi -> non-phi"
  if argBad then k := k.bump "ss phi arg in s0/s1/R"
  -- other phis changing
  let mut anyPhiCopy := false
  for h : i in [0:f.valueTab.size] do
    match f.valueTab[i], g.valueTab[i]? with
    | some x, some (some y) => if x.op == .Phi && y.op != .Phi && y.op != .Invalid then anyPhiCopy := true
    | _, _ => pure ()
  if anyPhiCopy then k := k.bump "some phi -> copy"
  -- reset set
  let mut R : Array ID := #[]
  for h : i in [0:f.valueTab.size] do
    match f.valueTab[i], g.valueTab[i]? with
    | some x, some (some y) => if x.op != .Invalid && y.op == .Invalid then R := R.push i
    | _, _ => pure ()
  k := k.bump "reset values" R.size
  if R.size == 0 then k := k.bump "no reset"
  let mut outside := false
  let mut phiR := false
  let mut rootR := false
  let mut ssR := false
  for r in R do
    let x := f.getV r
    if x.block != b && x.block != s0 then outside := true
    if x.op == .Phi then phiR := true
    if x.op == .Phi && x.block == ss then ssR := true
    if isRootOp x.op then rootR := true
  if outside then k := k.bump "reset outside b/s0"
  if phiR then k := k.bump "reset phi"
  if ssR then k := k.bump "reset phi in ss"
  if rootR then k := k.bump "reset root"
  if s1 != b && (f.getB s1).values.any (fun v => (f.getV v).args.any (R.contains ·)) then
    k := k.bump "s1 value reads R"
  if s1 != b && (f.getB s1).values.any (fun v => R.contains v) then
    k := k.bump "s1 value in R"
  if (f.getB b).values.any (fun v => (f.getV v).op == .Phi && R.contains v) then
    k := k.bump "b phi in R"
  -- unread R in g
  let mut readR := false
  for h : i in [0:g.valueTab.size] do
    match g.valueTab[i] with
    | some y => if y.op != .Invalid && y.args.any (R.contains ·) then readR := true
    | none => pure ()
  for h : i in [0:g.blockTab.size] do
    match g.blockTab[i] with
    | some B => if B.controls.any (R.contains ·) then readR := true
    | none => pure ()
  if readR then k := k.bump "R read in g"
  -- the control
  let c := bb.controls[0]!
  if !R.contains c then k := k.bump "control not reset"
  if (f.getV c).block != b then k := k.bump "control outside b"
  k := k.bump "f values" f.valueTab.size
  return k

def analyze (name : String) (f : Func) (b : ID) (k : Counts) : Counts := Id.run do
  let some run := plainRun f b | return k
  let (g, ch) := fuseBlockPlain f b
  if !ch then return k
  let mut k := { k with runs := k.runs + 1 }
  if run.length == 2 then k := { k with len2 := k.len2 + 1 }
  else if run.length == 3 then k := { k with len3 := k.len3 + 1 }
  else k := { k with len4 := k.len4 + 1 }
  let ok := match Plain.snapOf f b with
    | some s => Plain.postOK s g
    | none => false
  if ok then k := { k with accepted := k.accepted + 1 }
  else
    k := { k with rejected := k.rejected + 1 }
    if k.shown.size < 10 then k := { k with shown := k.shown.push s!"{name} run {run}" }
  return k

/-- A comparison fusion at `b` (it fired, `g` the result): the shapes the proof relies on. -/
def analyzeCmp (name : String) (f g : Func) (b : ID) (k : Counts) : Counts := Id.run do
  let bb := f.getB b
  let p := bb.preds[0]!.b
  let pb := f.getB p
  let mut k := { k with cmps := k.cmps + 1 }
  if !Cmp.stepOK f g b then
    k := { k with cmpRejected := k.cmpRejected + 1 }
    if k.shown.size < 10 then k := { k with shown := k.shown.push s!"{name} cmp rejected b{b}" }
  if bb.values.any (fun v => !specSafeOp (f.getV v).op) then k := { k with cmpUnsafe := k.cmpUnsafe + 1 }
  let nv := (g.getB b).controls[0]!
  if nv ≥ f.valueTab.size then k := { k with cmpNewBeyond := k.cmpNewBeyond + 1 }
  for i in [0:2] do
    if pb.succs[i]!.b != bb.succs[i]!.b then continue
    let s := pb.succs[i]!.b
    let jp := pb.succs[i]!.i
    let jb := bb.succs[i]!.i
    if s == p then k := { k with cmpSIsP := k.cmpSIsP + 1 }
    let phis := (f.getB s).values.filter fun v => (f.getV v).op == .Phi
    if !phis.isEmpty then k := { k with cmpSPhi := k.cmpSPhi + 1 }
    if phis.any (fun v => (g.getV v).op != .Phi) then k := { k with cmpPhiCopy := k.cmpPhiCopy + 1 }
    let differ := phis.any fun v =>
      let x := f.getV v
      x.args[jp]? != x.args[jb]?
    if differ then
      k := { k with cmpPhiDiffer := k.cmpPhiDiffer + 1 }
      if k.shown.size < 10 then k := { k with shown := k.shown.push s!"{name} cmp b{b} p{p} s{s}" }
    break
  return k

/-- Comparison family and width suffix of an op name (`Less64U` → ("Less", "64U")). -/
def cmpFam (op : Op) : Option (String × String) :=
  let n := op.name
  if n.startsWith "Neq" then some ("Neq", (n.drop 3).toString)
  else if n.startsWith "Eq" then some ("Eq", (n.drop 2).toString)
  else if n.startsWith "Less" then some ("Less", (n.drop 4).toString)
  else if n.startsWith "Leq" then some ("Leq", (n.drop 3).toString)
  else none

def isConstOp (op : Op) : Bool := op.name.startsWith "Const"

/-- How a redirect's infeasibility is decided by `p`'s control `cp` (taken along `p`'s branch)
and `b`'s control `cb`: a small syntactic decision, or `other` (needs prove's facts table). -/
def classifyRedirect (f : Func) (cp cb : ID) : String := Id.run do
  let vp := f.getV cp
  let vb := f.getV cb
  if cp == cb then return "same control"
  if vb.op == .Not && vb.args[0]? == some cp then return "b = Not p"
  if vp.op == .Not && vp.args[0]? == some cb then return "p = Not b"
  if vb.op == .ConstBool then return "b ConstBool"
  if vb.op == vp.op && vb.args == vp.args then return "same op+args"
  match cmpFam vp.op, cmpFam vb.op with
  | some (fp, wp), some (fb, wb) =>
    if wp != wb then return s!"cmp width differs {vp.op.name}/{vb.op.name}"
    let sameArgs := vb.args == vp.args
    let swapped := vb.args == vp.args.reverse
    if (fp == "Eq" && fb == "Neq" || fp == "Neq" && fb == "Eq") && (sameArgs || swapped) then
      return "Eq/Neq complement"
    if (fp == "Eq" && fb == "Eq" || fp == "Neq" && fb == "Neq") && swapped then
      return "Eq/Neq swapped"
    if (fp == "Less" && fb == "Leq" || fp == "Leq" && fb == "Less") && swapped then
      return "Less/Leq complement"
    if fp == fb && swapped then return "same cmp swapped"
    let shared := vp.args.any (vb.args.contains ·)
    let constOther := (vp.args ++ vb.args).any fun a => isConstOp (f.getV a).op
    if shared && constOther then return s!"cmp same var vs const {fp}/{fb}"
    if shared then return s!"cmp shared arg {fp}/{fb}"
    return s!"cmp unrelated {fp}/{fb}"
  | _, _ => return s!"other {vp.op.name}/{vb.op.name}"

/-- Shape facts of a redirect the checker relies on. -/
def redirectShape (f : Func) (b : ID) (k out : Nat) (kc : Counts) : Counts := Id.run do
  let mut kc := kc
  let bb := f.getB b
  let pk := bb.preds[k]!
  let ctl := bb.controls[0]!
  let cv := f.getV ctl
  let child := bb.succs[out]!.b
  if cv.block == b then kc := kc.bump "shape: ctl in b"
  if cv.block == b && cv.op == .Phi then kc := kc.bump "shape: ctl Phi in b"
  if cv.block == b && !RewriteCheck.termOp cv.op then kc := kc.bump "shape: ctl in b not term"
  if cv.block == b && cv.args.contains ctl then kc := kc.bump "shape: ctl reads itself"
  if bb.values.any (fun v => (f.getV v).op == .Phi) then kc := kc.bump "shape: b has Phi"
  if child == f.entry then kc := kc.bump "shape: child is entry"
  if child == pk.b then kc := kc.bump "shape: child = p"
  if (f.getB pk.b).succs.size != 2 then kc := kc.bump "shape: p succs != 2"
  if (f.getB pk.b).controls.size != 1 then kc := kc.bump "shape: p controls != 1"
  -- b's values read outside b's control
  let mut read := false
  for h : i in [0:f.valueTab.size] do
    match f.valueTab[i] with
    | some y => if f.blocks.contains y.block && y.args.any (bb.values.contains ·) then read := true
    | none => pure ()
  for bid in f.blocks do
    if bid != b && (f.getB bid).controls.any (bb.values.contains ·) then read := true
  if read then kc := kc.bump "shape: b value read elsewhere"
  let ai := bb.succs[out]!.i
  if (f.getB child).values.any (fun v => let x := f.getV v; x.op == .Phi &&
      (x.args[ai]?.any (bb.values.contains ·))) then kc := kc.bump "shape: child phi reads b value"
  return kc

/-- `fuseBranchRedirect` replayed, classifying every redirect and running the validator's
decision on it (`Redir.decideOK`). -/
def redirectProbe (tabs : Tables) (name : String) (pv : Prove.Prover) (f : Func) (k : Counts) :
    Except String (Func × Bool × Counts) := do
  let mut ft := (Prove.FactsTable.new pv.cx f).checkpoint
  let mut f := f
  let mut changed := false
  let mut k := k
  let blocks := f.blocks
  for idx in [0:blocks.size] do
    let b := blocks[blocks.size - 1 - idx]!
    let bb := f.getB b
    if bb.kind != .If then continue
    let ctl := f.getV bb.controls[0]!
    if (ctl.block != b && bb.values.size != 0) ||
        ((bb.values.size != 1 || ctl.uses != 1) && ctl.block == b) then continue
    let n := bb.preds.size
    let mut i := 0
    for _ in [0:2 * n + 2] do
      if i < (f.getB b).preds.size then
        let pk := (f.getB b).preds[i]!
        match tryPredOut pv f ft b i with
        | (ft', some out) =>
          let cp := (f.getB pk.b).controls[0]!
          let cb := (f.getB b).controls[0]!
          k := (k.bump "REDIRECT").bump s!"redirect: {classifyRedirect f cp cb}"
          let g := redirect f b i out
          if Redir.stepOK tabs f g b i out then
            k := k.bump "redirect VALIDATOR accepted"
          else
            let st := Redir.siteOf f b i out
            let why :=
              if !st.shapeOK f then "shape"
              else if !st.unreadOK f then "unread"
              else if !Redir.decideOK tabs f st.cp (st.pi == 0) st.ctl (st.out == 0) then
                let A := Redir.asmX tabs f st.cp st.ctl (st.pi == 0)
                if !(ProveCheck.decides f.value? tabs A Redir.fuel Redir.fuel st.ctl (st.out == 0) ||
                    Redir.eqDisjoint tabs f A st.ctl (st.out == 0)) then "decision"
                else "topo"
              else if !st.valTabOK f g then "values"
              else if ![st.b, st.p, st.child, st.q].all (st.blockOK f g) then "blocks"
              else "tables"
            k := (k.bump "redirect VALIDATOR rejected").bump
              s!"redirect rejected ({why}): {classifyRedirect f cp cb}"
            if k.shown.size < 40 then
              let msg := s!"{name} b{b} p{pk.b} ({why}): {(f.getV cp).op.name}{(f.getV cp).args} / {(f.getV cb).op.name}{(f.getV cb).args} pv {pk.i == 0} v {out == 0}"
              k := { k with shown := k.shown.push msg }
          k := redirectShape f b i out k
          ft := ft'; f := redirect f b i out; changed := true
        | (ft', none) => ft := ft'; i := i + 1
    if (f.getB b).preds.size == 0 && b != f.entry then
      f := f.modB b fun x => { x with kind := .Invalid }
  if let some e := ft.err then throw e
  return (f, changed, k)

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
    (final : Option (Func → Counts → Except String (Func × Bool × Counts))) : Nat → Func →
    Counts → Except String (Func × Counts)
  | 0, _, _ => throw "round bound"
  | n + 1, f, k => do
    let (f, ch, k) ← sweep step f k
    let (f, ch, k) ← match final with
      | some g => do let (f, c, k) ← g f k; pure (f, c || ch, k)
      | none => pure (f, ch, k)
    if ch then loop step final n f.invalidateCFG k else return (f, k)

/-- `fuse-probe [--late] <dir|file>...`; `--late` replays late fuse only. -/
def main (args : List String) : IO UInt32 := do
  let lateOnly := args.contains "--late"
  let mut files := #[]
  for a in args.filter (· != "--late") do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut ks : Array (String × Counts) :=
    if lateOnly then #[("late fuse", {})]
    else #[("early fuse", {}), ("late fuse", {}), ("short circuit", {})]
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
      let name := s!"{path}"
      let r : Except String (Func × Counts) := do
        let tv ← typeView env
        match pass with
        | "early fuse" =>
          loop (fun f b k => do
            let cmp (canOpt : Func → Value → Value → Op → Bool) (f : Func) (k : Counts) :=
              let (f', c) := fuseComparisons tv.isMem canOpt f b
              (f', c, if c then analyzeCmp name f f' b k else k)
            let (f, c1, k) := cmp canOptIntInRange f k
            let (f, c2, k) := cmp canOptSingleBitDifference f k
            let (f, c3, k) := cmp canOptNanCheck f k
            let k := analyze name f b k
            let (f, c4) := fuseBlockPlain f b
            pure (f, c1 || c2 || c3 || c4, k)) none roundFuel f0 k
        | "late fuse" =>
          let pv ← Prove.Prover.ofEnv env
          loop (fun f b k => do
            let (f', c1) ← fuseBlockIf tv f b
            let k := if c1 then analyzeIf tv name f f' b k else k
            let k := if c1 then checkIf tv name f f' b k else k
            let f := f'
            let k := analyze name f b k
            let (f, c2) := fuseBlockPlain f b
            pure (f, c1 || c2, k)) (some (redirectProbe env.tables name pv)) roundFuel f0 k
        | _ =>
          let some boolT := env.typ? "Bool" | throw "no Bool"
          let isBool (t : TypeRef) : Bool := (env.type? t).map (·.kind) == some .BOOL
          let f1 := ShortCircuit.constPhiArgs isBool env.typeOrder.eq boolT f0
          loop (fun f b k => do
            let k := analyze name f b k
            let (f, c1) := fuseBlockPlain f b
            let (f, c2) := ShortCircuit.shortcircuitBlock f b
            pure (f, c2 || c1, k)) none roundFuel f1 k
      match r with
      | .ok (_, k') => ks := ks.set! idx (pass, k')
      | .error _ => errs := errs + 1
  for (p, k) in ks do
    IO.println s!"{p}: plain fusions {k.runs} (run length 2: {k.len2}, 3: {k.len3}, ≥4: {k.len4}); accepted {k.accepted}, rejected {k.rejected}"
    if k.cmps > 0 then
      IO.println s!"  comparison fusions {k.cmps}: rejected {k.cmpRejected}; shared successor has a Phi {k.cmpSPhi}, Phi args differ {k.cmpPhiDiffer}, Phi becomes Copy {k.cmpPhiCopy}, s = p {k.cmpSIsP}, b not speculation-safe {k.cmpUnsafe}, new value beyond table {k.cmpNewBeyond}"
    for (s, n) in k.ifStats do IO.println s!"  if: {s}: {n}"
    for s in k.shown do IO.println s!"  REJECT {s}"
  IO.println s!"errors {errs}"
  return 0

end GoFVTest.FuseProbe

def main (args : List String) : IO UInt32 := GoFVTest.FuseProbe.main args
