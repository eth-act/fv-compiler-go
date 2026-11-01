import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.Prove.Pass
import GoFV.Opt.ProveCheck.Check

/-!
# `prove-probe`: what stock prove rewrites (issue #24)

Runs `prove` on the input of every `prove` section of the given export files and counts its
rewrites by class (docs/PASSES.md, prove, T3–T16): branch removals (by the removed block's
control op), bounded-shift marks, signed → unsigned `Rsh`/`Div`/`Mod`, `Ctz` → `CtzNonZero`,
`Slicemask` → constant, `Mul` → `And`/`CondSelect`, `Eq` ↔ `Neq`, `And`/`Or` → `Copy`,
constant-folded arguments, and the rest.
-/

open GoFV.SSA GoFV.Opt

namespace GoFVTest.ProveProbe

def isShift (op : Op) : Bool :=
  let n := op.name
  n.startsWith "Lsh" || n.startsWith "Rsh"

/-- The rewrite classes of one value (`fv` in the input, `gv` in prove's output). -/
def valueClasses (f g : Func) (fv gv : Value) : List String := Id.run do
  let mut cs : List String := []
  if fv.op != gv.op then
    let k := if gv.op == .Copy then s!"{(fv.op.name.takeWhile Char.isAlpha)}->Copy"
      else if fv.op == .Slicemask then "Slicemask->Const"
      else if fv.op.name.startsWith "Rsh" then "Rsh->RshU"
      else if fv.op.name.startsWith "Ctz" then "Ctz->NonZero"
      else if fv.op.name.startsWith "Div" || fv.op.name.startsWith "Mod" then "DivMod->u"
      else if fv.op.name.startsWith "Mul" then s!"Mul->{gv.op.name.takeWhile Char.isAlpha}"
      else if fv.op.name.startsWith "Eq" || fv.op.name.startsWith "Neq" then "EqNeq"
      else s!"op {fv.op.name}->{gv.op.name}"
    cs := k :: cs
  if fv.auxInt != gv.auxInt && isShift gv.op && gv.auxInt == 1 then cs := "shift bounded" :: cs
  else if fv.auxInt != gv.auxInt && fv.op == gv.op then cs := s!"auxInt {fv.op.name}" :: cs
  if fv.op == gv.op && fv.args.size == gv.args.size then
    for (a, a') in fv.args.toList.zip gv.args.toList do
      if a != a' then
        let isC := (g.value? a').any fun u => u.op matches .Const8 | .Const16 | .Const32 | .Const64 |
          .ConstBool | .ConstNil
        let k := if isC then
            s!"const arg {if fv.op == .Phi then "phi" else "value"}"
          else s!"arg {fv.op.name}"
        cs := k :: cs
  if fv.op != gv.op && fv.args.size == gv.args.size && fv.op.name.startsWith "Eq" == false &&
      fv.op.name.startsWith "Neq" == false && fv.args != gv.args && gv.op != .Copy &&
      gv.op != .CondSelect then cs := s!"args of {fv.op.name}" :: cs
  let _ := f
  return cs

def bump (m : Std.HashMap String Nat) (k : String) (n : Nat := 1) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + n)

def ptrCacheFn (ts : Array TypeRef) : TypeRef → Bool :=
  let m : Std.HashMap TypeRef Unit := ts.foldl (fun m t => m.insert t ()) {}
  fun t => m.contains t

structure St where
  secs : Nat := 0
  changed : Nat := 0
  errs : Nat := 0
  classes : Std.HashMap String Nat := {}
  funcs : Std.HashMap String Nat := {}
  acc : Std.HashMap String Nat := {}
  rej : Std.HashMap String Nat := {}
  same : Nat := 0
  relFail : Nat := 0
  checkFail : Nat := 0
  cerrs : Nat := 0
  shown : Nat := 0

def checkFile (path : System.FilePath) (st : St) : IO St := do
  let data ← IO.FS.readBinFile path
  let .ok e := parseExport data | return st
  let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
  let base : PassEnv :=
    { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
      pgohot := e.pgohot, config := e.config, typs
      typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
      tables := {}, frontend := e.frontendTables, ptrCache := ptrCacheFn e.ptrCache }
  let mut st := st
  let mut tables : Tables := {}
  for h : k in [0:e.sections.size] do
    let s := e.sections[k]
    let prev := tables
    tables := tables.addAll s.defs
    if k == 0 then continue
    if s.pass.toStringLossy != "prove" then continue
    let env := { base with passName := "prove", tables := prev }
    let f := e.sections[k-1]!.func
    st := { st with secs := st.secs + 1 }
    let .ok out := provePass env f | st := { st with errs := st.errs + 1 }; continue
    let g := out.func
    match ProveCheck.proveCheckedStats env f with
    | .error _ => st := { st with cerrs := st.cerrs + 1 }
    | .ok (h, cs) =>
      for (k, n) in cs.acc.toList do st := { st with acc := bump st.acc k n }
      for (k, n) in cs.rej.toList do st := { st with rej := bump st.rej k n }
      for (k, b, x) in cs.why do
        if !(k.startsWith "args" || k.startsWith "Mul" || k.startsWith "Add" || k.startsWith "And" || k.startsWith "Or") then
          IO.println s!"REJ {k} {path} b{b} v{x}"
      if h == g then st := { st with same := st.same + 1 }
      if h == f && g != f then
        st := { st with relFail := st.relFail + 1 }
        let (h', _) := ProveCheck.revert prev true f g
        let (C, F, inv) := ProveCheck.asmOf f prev
        if h' != f then
          IO.println s!"RELFAIL {path}: atoms {RewriteCheck.atomsOK f h'} closedF {RewriteCheck.closedOK f} closedG {RewriteCheck.closedOK h'} facts {ProveCheck.factsOK f C F} inv {ProveCheck.invOK f prev C F inv inv} values {ProveCheck.valuesOK prev f h' F inv} tree {f.blocks.all C.inTree}"
        else
          IO.println s!"ALLUNDONE {path}: every rewrite rejected, the reverted output is the input"
      if (check { tabs := prev, typs } h).toBool == false then
        st := { st with checkFail := st.checkFail + 1 }
        if st.shown < 5 then
          IO.println s!"CHECK FAIL {path}: {match check { tabs := prev, typs } h with | .error e => e | _ => ""}"
          st := { st with shown := st.shown + 1 }
    if g == f then continue
    st := { st with changed := st.changed + 1 }
    let mut seen : Std.HashMap String Unit := {}
    for b in f.blocks do
      let (some fb, some gb) := (f.block? b, g.block? b) | continue
      if fb.kind == .If && gb.kind == .First then
        let cop := ((fb.controls[0]?.bind f.value?).map (·.op.name)).getD "?"
        let k := s!"branch {cop}"
        st := { st with classes := bump st.classes k }
        seen := seen.insert "branch" ()
      else if fb.kind != gb.kind then
        st := { st with classes := bump st.classes s!"kind {repr fb.kind}->{repr gb.kind}" }
      for x in fb.values do
        let (some fv, some gv) := (f.value? x, g.value? x) | continue
        for c in valueClasses f g fv gv do
          st := { st with classes := bump st.classes c }
          seen := seen.insert ((c.splitOn " ").head!) ()
    for (c, _) in seen.toList do
      st := { st with funcs := bump st.funcs c }
  return st

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut st : St := {}
  for path in files.qsort (·.toString < ·.toString) do
    st ← checkFile path st
  IO.println s!"prove sections {st.secs}: changed {st.changed}, errors {st.errs}"
  IO.println "rewrites by class:"
  for (k, n) in st.classes.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  IO.println s!"checked output = stock output: {st.same}/{st.secs}; checked output fails check: {st.checkFail}; checked = input (relation fails or all undone) {st.relFail}; checked errors {st.cerrs}"
  IO.println "validator by class (accepted / rejected):"
  let keys := (st.acc.toList.map (·.1) ++ st.rej.toList.map (·.1)).eraseDups
  for k in keys.toArray.qsort (· < ·) do
    IO.println s!"  {k}: {st.acc.getD k 0} / {st.rej.getD k 0}"
  IO.println "functions per class (first word):"
  for (k, n) in st.funcs.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  return 0

end GoFVTest.ProveProbe

def main (args : List String) : IO UInt32 := GoFVTest.ProveProbe.main args
