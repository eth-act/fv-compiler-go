import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.Deadcode
import GoFV.Proof.Pass.DeadChain
import GoFV.Proof.Pass.CopyFrag

/-! Scratch probe: conditions of the deadcode proof plan (not for merge). -/

open GoFV.SSA GoFV.Opt GoFV.Proof.Dead GoFV.SSA.DomCert

namespace GoFVTest.DeadPlanProbe

def removePhiArgNE (f : Func) (b phi : ID) (i : Nat) : Func :=
  let n := (f.getB b).preds.size
  let args := (f.getV phi).args
  (f.decUses args[i]!).modV phi fun x => { x with args := (x.args.set! i args[n]!).pop }

def removeEdgeNE (f : Func) (b : ID) (i : Nat) : Func :=
  let e := (f.getB b).succs[i]!
  let c := e.b
  let j := e.i
  let f := (f.removeSucc b i).removePred c j
  (f.getB c).values.foldl (init := f) fun f v =>
    if (f.getV v).op == .Phi then removePhiArgNE f c v j else f

def removeDeadEdgesNE (reachable : Array Bool) (f : Func) : Func := Id.run do
  let mut f := f
  for b in f.blocks do
    if reachable.getD b false then continue
    let mut i := 0
    for _ in [0:2 * (f.getB b).succs.size + 1] do
      let ss := (f.getB b).succs
      if h : i < ss.size then
        if reachable.getD ss[i].b false then f := removeEdgeNE f b i
        else i := i + 1
      else break
  return f

def removeFirstEdgesNE (reachable : Array Bool) (f : Func) : Func :=
  f.blocks.foldl (init := f) fun f b =>
    if !reachable.getD b false || (f.getB b).kind != .First then f else
    (removeEdgeNE f b 1).modB b fun x => { x with kind := .Plain, likely := .unknown }

def treeBlocks (f : Func) : Array ID := f.blocks.filter (make f).inTree

def noEmptyTree (tabs : Tables) (f : Func) : Bool :=
  (treeBlocks f).all fun bid =>
    match f.block? bid with
    | none => true
    | some fb => fb.values.all fun x => match f.value? x with
      | some fv => !GoFV.Proof.CopyElim.isOkTrue (zeroSizeAggregate tabs fv.type)
      | none => true

/-- Values that are `Phi` in `f1'` and `Copy` in `f1` have a non-zero-size type. -/
def convOK (tabs : Tables) (f1' f1 : Func) : Bool × Nat := Id.run do
  let mut n := 0
  for bid in f1.blocks do
    let some b := f1.block? bid | continue
    for x in b.values do
      match f1'.value? x, f1.value? x with
      | some u, some v =>
        if u.op == .Phi && v.op == .Copy then
          n := n + 1
          if GoFV.Proof.CopyElim.zeroSizeB tabs u.type then return (false, n)
      | _, _ => pure ()
  return (true, n)

def fragWhy (tabs : Tables) (f : Func) : String := Id.run do
  if f.valueTab.size > f.vidLast + 1 then return "size"
  for bid in f.blocks do
    let some b := f.block? bid | continue
    for x in b.values do
      let some v := f.value? x | continue
      if (v.op == .Copy || v.op == .Phi) && !v.args.all (fun a => (f.value? a).any fun w =>
          GoFV.Proof.CopyElim.tyEq (tabs.ty w.type) (tabs.ty v.type)) then
        let bad := v.args.find? (fun a => !(f.value? a).any fun w =>
          GoFV.Proof.CopyElim.tyEq (tabs.ty w.type) (tabs.ty v.type))
        let wt := (bad.bind f.value?).map (fun w => (repr (tabs.ty w.type)).pretty 60) |>.getD "-"
        let wop := (bad.bind f.value?).map (fun w => w.op.name) |>.getD "-"
        return s!"shape {v.op.name} {(repr (tabs.ty v.type)).pretty 60} <- {wop} {wt}"
      if v.op == .Copy && GoFV.Proof.CopyElim.zeroSizeB tabs v.type then return "zero-size copy"
      if !GoFV.Proof.CopyElim.chainEnds f.value? (f.valueTab.size + 1) x then return "copy cycle"
  return "?"

def noNilB (f : Func) : Bool :=
  f.valueTab.all fun o => match o with
    | some v => v.op != .NilCheck
    | none => true

structure Cnt where
  secs : Nat := 0
  checked : Nat := 0
  conv : Nat := 0
  a : Nat := 0
  b : Nat := 0
  c : Nat := 0
  d : Nat := 0
  e : Nat := 0
  ff : Nat := 0
  g : Nat := 0
  h : Nat := 0
  all : Nat := 0
  allNN : Nat := 0
  deriving Inhabited

def bump (b : Bool) : Nat := if b then 1 else 0

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut c : Cnt := {}
  let mut fails : Std.HashMap String Nat := {}
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
      c := { c with secs := c.secs + 1 }
      match deadcode prev f with
      | .error _ => pure ()
      | .ok g =>
        let ce : CheckEnv := { tabs := prev, typs }
        let okf := (check ce f).toBool
        let okg := (check { tabs := tables, typs } g).toBool
        if !(okf && okg) then continue
        let r := f.reachableBlocks
        let f1 := Deadcode.removeFirstEdges r (Deadcode.removeDeadEdges r f)
        let f1' := removeFirstEdgesNE r (removeDeadEdgesNE r f)
        let .ok f2 := copyelim prev f1 | continue
        let a := (DomCert.check f1').toBool
        let b := (DomCert.check f2).toBool
        let cc := GoFV.Proof.CopyElim.copyFrag prev f1'
        let d := noEmptyTree prev f1' && chainedB f1' (treeBlocks f1')
        let (cv, ncv) := convOK prev f1' f1
        let e := cv && GoFV.Proof.CopyElim.copyFrag prev f1
        let reach := f.blocks.filter (r.getD · false)
        let ff := chainedB f reach
        let gg := chainedB f2 g.blocks
        let hh := noNilB f
        let allNN := a && b && cc && d && e && ff && gg
        let all := allNN && hh
        c := { c with checked := c.checked + 1, conv := c.conv + bump (decide (ncv > 0)) }
        c := { c with a := c.a + bump a, b := c.b + bump b, c := c.c + bump cc }
        c := { c with d := c.d + bump d, e := c.e + bump e, ff := c.ff + bump ff }
        c := { c with g := c.g + bump gg, h := c.h + bump hh, all := c.all + bump all }
        c := { c with allNN := c.allNN + bump allNN }
        let msgA := match check ce f1' with
          | .error m => (m.take 40).toString
          | _ => ""
        let key := if !a then "domcert f1'"
          else if !b then "domcert f2" else if !cc then "copyFrag f1': " ++ fragWhy prev f1' ++ " " ++ name
          else if !d then "simFrag f1'" else if !e then "conv/copyFrag f1" else if !ff then "chained f"
          else if !gg then "chained f2" else "ok"
        fails := fails.insert key (fails.getD key 0 + 1)
  IO.println s!"sections {c.secs}, checked {c.checked}, with phi->copy conversions {c.conv}"
  IO.println s!"domcert f1' {c.a}, domcert f2 {c.b}, copyFrag f1' {c.c}, simFrag(noEmpty,chained) f1' {c.d}, conv+copyFrag f1 {c.e}, chained f reach {c.ff}, chained f2 {c.g}, noNil f {c.h}"
  IO.println s!"all (no NoNil) {c.allNN}, all {c.all}"
  for (k, n) in fails.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  return 0

end GoFVTest.DeadPlanProbe

def main (args : List String) : IO UInt32 := GoFVTest.DeadPlanProbe.main args
