import GoFV.SSA.Parse
import GoFV.Opt.Trim
import GoFV.Proof.Pass.TrimLocCheck

/-!
# `lake exe trim-probe <dir>...`: `trimRelB` on the corpus

For every `trim` section (input: the previous section), runs the Lean `trim` on the input and
counts the sections where it succeeds, where it changes the function (removes a block) and where
`trimRelB` (the hypothesis of `trim_refinesLoc`) accepts the input and output; reports the first
failing condition of `trimRelB` with its count and examples, and small witness candidates.
-/

open GoFV.SSA GoFV.Opt GoFV.Proof.TrimLoc

namespace GoFVTest.TrimProbe

/-- The conditions of `trimRelB`, in its order. -/
def conds (f g : Func) : Array (String × Bool) :=
  let hs := locHomes g
  let bs := blocksIdx g
  #[("ctx", ctxLocB f g),
    ("values", (List.range g.valueTab.size).all (valLocB f g)),
    ("entry", entryLocB f g f.entry g.entry),
    ("blockId", bs.all fun (i, K') => K'.id == i),
    ("kept", bs.all fun (_, K') => keptLocB f g K'),
    ("closed", bs.all fun (_, K') => closedLocB g K'),
    ("phis", bs.all fun (_, K') => phisLocB g hs K'),
    ("signs", signsLocB f g)]

structure Cnt where
  secs : Nat := 0
  ran : Nat := 0
  changed : Nat := 0
  accepted : Nat := 0
  acceptedChanged : Nat := 0
  nonEmptyMerge : Nat := 0
  phiDropped : Nat := 0
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
  let mut examples : Std.HashMap String (Array String) := {}
  let mut errs : Nat := 0
  let mut cands : Array (Nat × String) := #[]
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok ex := parseExport data | continue
    for h : k in [0:ex.sections.size] do
      let s := ex.sections[k]
      if k == 0 || s.pass.toStringLossy != "trim" then continue
      let f := ex.sections[k-1]!.func
      c := { c with secs := c.secs + 1 }
      match trim f with
      | .error _ => errs := errs + 1
      | .ok g =>
        let changed := g.blocks.size < f.blocks.size
        -- a removed block with a non-`Phi` value; a value table entry dropped (unused phi)
        let nem := f.blocks.any fun b =>
          (g.block? b).isNone && ((f.block? b).map fun x => !(npLoc f x.values.toList).isEmpty).getD false
        let pd := (List.range f.valueTab.size).any fun i => (f.value? i).isSome && (g.value? i).isNone
        let cs := conds f g
        let acc := cs.all (·.2)
        if acc != trimRelB f g then
          IO.eprintln s!"probe bug: conds disagree with trimRelB on {path} section {k - 1}"
          return 2
        c := { c with ran := c.ran + 1, changed := c.changed + (if changed then 1 else 0),
                      accepted := c.accepted + (if acc then 1 else 0),
                      acceptedChanged := c.acceptedChanged + (if acc && changed then 1 else 0),
                      nonEmptyMerge := c.nonEmptyMerge + (if nem then 1 else 0),
                      phiDropped := c.phiDropped + (if pd then 1 else 0) }
        if let some (n, _) := cs.find? (!·.2) then
          whys := whys.insert n (whys.getD n 0 + 1)
          let ex := examples.getD n #[]
          if ex.size < 5 then examples := examples.insert n (ex.push s!"{path} section {k - 1}")
        if acc && changed && nem then
          let n := f.valueTab.size
          cands := cands.push (n, s!"{path} section {k - 1}: {f.blocks.size} -> {g.blocks.size} blocks, {n} value ids, phi dropped {pd}")
  IO.println s!"trim sections {c.secs}, Lean trim failed {errs}, ran {c.ran}, changed {c.changed}, trimRelB accepted {c.accepted} (changed {c.acceptedChanged}), rejected {c.ran - c.accepted}"
  IO.println s!"  with a merged non-empty block {c.nonEmptyMerge}, with a dropped phi {c.phiDropped}"
  IO.println "rejected (first failing condition):"
  for (n, k) in whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
    for e in examples.getD n #[] do
      IO.println s!"    {e}"
  IO.println "witness candidates (accepted, a non-empty block merged), smallest first:"
  for (_, l) in (cands.qsort (fun a b => a.1 < b.1)).extract 0 10 do
    IO.println s!"  {l}"
  return 0

end GoFVTest.TrimProbe

def main (args : List String) : IO UInt32 := GoFVTest.TrimProbe.main args
