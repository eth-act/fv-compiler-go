import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Proof.Pass.CopyElimPassL
import GoFV.Proof.Pass.DeadcodePassL

/-!
# `lake exe lowfrag-probe [--shard i/n] <dir>...`: coverage of the lowered copyelim and deadcode theorems

For every section produced by `late phielim and copyelim` (`copyelimPass`) or by a lowered
deadcode instance (`lowered deadcode for cse`, `lowered deadcode`, `late deadcode`; all
`deadcodePass`), runs the Lean pass on the input (the previous section, in its tables) and
decides every hypothesis of the `runL` theorem that covers it:

- `copyelim_refinesL`: `check` of input and output, `CopyFrag` (`copyFrag`), `EmptyFrag`
  (`emptyFragB`), `out.lowered = f.lowered`, `CopyLFrag` (`copyLFragB`);
- `deadcode_refinesL`: `check` of input and output, `DeadFrag` (`deadFragB`),
  `out.lowered = f.lowered`, `DeadFragL` (`deadFragLB`).

Counts per pass: sections, sections the pass changes (output function differs from the input),
sections in which every hypothesis holds ("covered"), overall and among the changed ones, and
the first failing hypothesis. `--shard i/n` processes the files whose index is `i` modulo `n`
(sorted paths), so that several processes can share a large corpus; the per-shard counts add up.
-/

open GoFV.SSA GoFV.Opt GoFV.Proof.Dead GoFV.Proof.CopyElim

namespace GoFVTest.LowFragProbe

/-- The hypotheses of the theorem covering pass `name` on input `f` (tables `tabs`, checked in
`ce`) and output `g` (checked in `ce'`), in the theorem's order; `none` if `name` is not one of
the probed passes. -/
def conds (name : String) (ce ce' : CheckEnv) (tabs : Tables) (f g : Func) :
    Option (Array (String × Thunk Bool)) :=
  let common := #[("check f", Thunk.mk fun _ => (check ce f).toBool),
    ("check g", Thunk.mk fun _ => (check ce' g).toBool)]
  let low := ("lowered", Thunk.mk fun _ => g.lowered == f.lowered)
  if name == "late phielim and copyelim" then
    some (common ++ #[("CopyFrag", Thunk.mk fun _ => copyFrag tabs f),
      ("EmptyFrag", Thunk.mk fun _ => emptyFragB tabs f), low,
      ("CopyLFrag", Thunk.mk fun _ => copyLFragB tabs f g)])
  else if name == "lowered deadcode for cse" || name == "lowered deadcode" ||
      name == "late deadcode" then
    some (common ++ #[("DeadFrag", Thunk.mk fun _ => deadFragB tabs f), low,
      ("DeadFragL", Thunk.mk fun _ => deadFragLB tabs f)])
  else none

/-- The probed passes. -/
def probed (name : String) : Bool :=
  name == "late phielim and copyelim" || name == "lowered deadcode for cse" ||
    name == "lowered deadcode" || name == "late deadcode"

/-- The Lean pass of a probed section. -/
def runPass (name : String) (tabs : Tables) (f : Func) : Except String Func :=
  if name == "late phielim and copyelim" then copyelim tabs f else deadcode tabs f

structure Cnt where
  secs : Nat := 0
  errors : Nat := 0
  changed : Nat := 0
  covered : Nat := 0
  coveredChanged : Nat := 0
  deriving Inhabited

def Cnt.add (a b : Cnt) : Cnt :=
  ⟨a.secs + b.secs, a.errors + b.errors, a.changed + b.changed, a.covered + b.covered,
    a.coveredChanged + b.coveredChanged⟩

def parseShard (s : String) : Option (Nat × Nat) :=
  match s.splitOn "/" with
  | [i, n] => do
    let i ← i.toNat?
    let n ← n.toNat?
    if n == 0 || i ≥ n then none else some (i, n)
  | _ => none

def main (args : List String) : IO UInt32 := do
  let (shard, dirs) := match args with
    | "--shard" :: s :: rest => (parseShard s, rest)
    | rest => (some (0, 1), rest)
  let some (si, sn) := shard | IO.eprintln "bad --shard (i/n)"; return 2
  let mut files := #[]
  for a in dirs do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  files := files.qsort (fun a b => a.toString < b.toString)
  let mut byPass : Std.HashMap String Cnt := {}
  let mut whys : Std.HashMap String Nat := {}
  let mut whysChanged : Std.HashMap String Nat := {}
  let mut nfiles := 0
  for h : idx in [0:files.size] do
    if idx % sn != si then continue
    let path := files[idx]
    nfiles := nfiles + 1
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
      let f := ex.sections[k-1]!.func
      if !probed name then continue
      let mut pc := byPass.getD name {}
      pc := { pc with secs := pc.secs + 1 }
      match runPass name prev f with
      | .error _ => pc := { pc with errors := pc.errors + 1 }
      | .ok g =>
        let ch := decide (g ≠ f)
        let some cs := conds name { tabs := prev, typs } { tabs := tables, typs } prev f g
          | continue
        let fail := cs.find? (!·.2.get)
        let cov := fail.isNone
        pc := { pc with changed := pc.changed + (if ch then 1 else 0)
                        covered := pc.covered + (if cov then 1 else 0)
                        coveredChanged := pc.coveredChanged + (if cov && ch then 1 else 0) }
        if let some (n, _) := fail then
          let key := s!"{name}: {n}"
          whys := whys.insert key (whys.getD key 0 + 1)
          if ch then whysChanged := whysChanged.insert key (whysChanged.getD key 0 + 1)
      byPass := byPass.insert name pc
  IO.println s!"files {nfiles} (shard {si}/{sn})"
  let fmt (n : String) (x : Cnt) : String :=
    s!"{n}: sections {x.secs}, pass errors {x.errors}, changed {x.changed}, covered {x.covered}, covered and changed {x.coveredChanged}"
  let mut tot : Cnt := {}
  for n in ["late phielim and copyelim", "lowered deadcode for cse", "lowered deadcode",
      "late deadcode"] do
    let x := byPass.getD n {}
    tot := tot.add x
    IO.println (fmt n x)
  IO.println (fmt "all" tot)
  IO.println "first failing hypothesis (all sections):"
  for (k, n) in whys.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  IO.println "first failing hypothesis (changed sections):"
  for (k, n) in whysChanged.toList.toArray.qsort (fun a b => a.2 > b.2) do
    IO.println s!"  {n} {k}"
  return 0

end GoFVTest.LowFragProbe

def main (args : List String) : IO UInt32 := GoFVTest.LowFragProbe.main args
