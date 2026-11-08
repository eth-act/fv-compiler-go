import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.Deadcode
import GoFV.Proof.Pass.DeadcodePass

open scoped GoFV.SSA.Sem.Fixed

/-!
# `lake exe deadcode-probe <dir>...`: deadcode's fragment on the corpus

For every section produced by a deadcode instance (input: the previous section), runs the Lean
`deadcode` on the input and counts the sections whose input and output pass `check` and whose
input is in `GoFV.Proof.Dead.DeadFrag` (`deadFragB`), i.e. those `deadcode_refines` covers;
counts each condition of `deadFragB` separately, reports the first failing one by pass instance,
and lists small witness candidates (in the fragment, a block and a value removed).
-/

open GoFV.SSA GoFV.Opt GoFV.Proof.Dead GoFV.Proof.CopyElim

namespace GoFVTest.DeadcodeProbe

/-- The conditions of `deadFragB`, in its order. -/
def conds (tabs : Tables) (f : Func) : Array (String × Bool) :=
  #[("bid", f.blocks.all (· ≤ f.bidLast)), ("firstTwo", firstTwoB f),
    ("copyFrag f1'", copyFrag tabs (edgesG false f)), ("copyFrag f1", copyFrag tabs (edgesG true f)),
    ("emptyFrag f1'", emptyFragB tabs (edgesG false f)),
    ("domCert f1'", (DomCert.check (edgesG false f)).toBool),
    ("domCert f2", match copyelim tabs (edgesG true f) with
      | .ok g => (DomCert.check g).toBool
      | .error _ => true)]

def listedCount (f : Func) : Nat :=
  f.blocks.foldl (fun n bid => n + (((f.block? bid).map (·.values.size)).getD 0)) 0

structure Cnt where
  secs : Nat := 0
  checked : Nat := 0
  frag : Nat := 0
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
  let mut condOK : Std.HashMap String Nat := {}
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
          let cs := conds prev f
          let frag := cs.all (·.2)
          if frag != deadFragB prev f then
            IO.eprintln s!"probe bug: conds disagree with deadFragB on {path} section {k - 1}"
            return 2
          for (n, b) in cs do
            if b then condOK := condOK.insert n (condOK.getD n 0 + 1)
          if let some (n, _) := cs.find? (!·.2) then
            let key := s!"{name}: {n}"
            whys := whys.insert key (whys.getD key 0 + 1)
          let bRem := g.blocks.size < f.blocks.size
          let vRem := listedCount g < listedCount f
          let upd (x : Cnt) : Cnt :=
            { x with checked := x.checked + 1, frag := x.frag + (if frag then 1 else 0),
                     blocksRemoved := x.blocksRemoved + (if bRem then 1 else 0),
                     valuesRemoved := x.valuesRemoved + (if vRem then 1 else 0),
                     fragBlocks := x.fragBlocks + (if frag && bRem then 1 else 0),
                     fragValues := x.fragValues + (if frag && vRem then 1 else 0) }
          c := upd c
          pc := upd pc
          if frag && bRem && vRem then
            cands := cands.push (listedCount f, s!"{path} section {k - 1} -> {k} ({name}): {f.blocks.size} blocks, {listedCount f} values -> {g.blocks.size} blocks, {listedCount g} values")
      byPass := byPass.insert name pc
  let fmt (n : String) (x : Cnt) : String :=
    s!"{n}: sections {x.secs}, both checked {x.checked}, DeadFrag {x.frag}; blocks removed {x.blocksRemoved} (in DeadFrag {x.fragBlocks}), values removed {x.valuesRemoved} (in DeadFrag {x.fragValues})"
  IO.println (fmt "all" c)
  for (n, x) in byPass.toList do
    IO.println (fmt n x)
  IO.println "conditions holding (of both checked):"
  for n in ["bid", "firstTwo", "copyFrag f1'", "copyFrag f1", "emptyFrag f1'", "domCert f1'",
      "domCert f2"] do
    IO.println s!"  {n} {condOK.getD n 0}"
  IO.println "outside DeadFrag (first failing condition):"
  for (k, n) in whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  IO.println "witness candidates (DeadFrag, a block and a value removed), smallest first:"
  for (_, l) in (cands.qsort (fun a b => a.1 < b.1)).extract 0 20 do
    IO.println s!"  {l}"
  return 0

end GoFVTest.DeadcodeProbe

def main (args : List String) : IO UInt32 := GoFVTest.DeadcodeProbe.main args
