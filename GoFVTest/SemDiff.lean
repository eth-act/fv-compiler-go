import GoFV.SSA.Parse
import GoFV.SSA.Sem.Run
import Std.Data.HashMap

/-!
# `sem-difftest`: differential test of `GoFV.SSA.run` (issue #10)

Three modes (driven by `scripts/sem-difftest.sh`):

- `gen <dir> <n> <seed> <func>...`: for each function `<dir>/<func>,1.ssa` of the export,
  print `n` calls `<func> <arg>...` with random and edge-case arguments of its parameter types
  (integers and `bool` only).
- `run <dir> <calls> <native>`: run every call of `<calls>` on **every section** of the
  function's export with `GoFV.SSA.run`, and compare each outcome with the native result
  (`<native>`, the output of `tools/semdiff/prog` under `qemu-aarch64-static`, one line
  `<call> -> <outcome>` per call). Exit status 1 on any disagreement.
- `corpus <n> <seed> <dir>...`: for every export file below the directories whose function has
  integer/`bool` parameters and results only, run `n` random calls on every section and check
  that every section agrees with section 0 whenever section 0 returns or panics (the stock
  pipeline must preserve the semantics). Counts calls whose section 0 is stuck (outside P1)
  separately; a later section that is stuck where section 0 is not is reported as a gap.
-/

open GoFV.SSA GoFV.SSA.Sem

namespace GoFVTest.SemDiff

/-- A parameter or result type the difftest can pass and print. -/
inductive Kind where
  | int (w : Width) (signed : Bool)
  | bool

def Kind.ofType (tabs : Tables) (t : TypeRef) : Option Kind := do
  let d ← tabs.type? t
  let w ← d.size.bind Width.ofSize?
  match d.kind with
  | .INT8 | .INT16 | .INT32 | .INT64 | .INT => some (.int w true)
  | .UINT8 | .UINT16 | .UINT32 | .UINT64 | .UINT | .UINTPTR => some (.int w false)
  | .BOOL => some .bool
  | _ => none

/-- Parameter and result kinds of `f`'s signature, if all are supported. -/
def signature (tabs : Tables) (f : Func) : Option (Array Kind × Array Kind) := do
  let d ← tabs.type? f.type
  match d.tail with
  | .func nrecv nparams nresults fields =>
    let ks ← fields.mapM fun fd => Kind.ofType tabs fd.type
    let nin := nrecv + nparams
    if ks.size != nin + nresults then none
    else some (ks.extract 0 nin, ks.extract nin ks.size)
  | _ => none

def parseVal : Kind → String → Option Val
  | .bool, "true" => some (.bool true)
  | .bool, "false" => some (.bool false)
  | .bool, _ => none
  | .int w _, s => s.toInt?.map fun n => .int w (BitVec.ofInt w.bits n)

def renderVal : Kind → Val → String
  | .int _ true, .int _ x => toString x.toInt
  | .int _ false, .int _ x => toString x.toNat
  | .bool, .bool b => toString b
  | _, v => s!"<{v.render}>"

def renderOutcome (res : Array Kind) : Outcome → String
  | .returned rs _ =>
    "returned" ++ String.join ((rs.zip res.toList).map fun (v, k) => " " ++ renderVal k v) ++
      (if rs.length == res.size then "" else s!" <{rs.length} results>")
  | .panicked e _ => "panicked " ++ e.message
  | .stuck msg => "stuck: " ++ msg
  | .outOfFuel => "outOfFuel"

/-- splitmix64. -/
def nextRand (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

/-- A random argument: an edge value, a small value, or random bits. -/
def randArg (k : Kind) (s : UInt64) : String × UInt64 :=
  let (r, s) := nextRand s
  let (r2, s) := nextRand s
  match k with
  | .bool => (if r % 2 == 0 then "true" else "false", s)
  | .int w signed =>
    let n := w.bits
    let edges : List Int :=
      if signed then [0, 1, -1, 2, -2, 7, -(2 ^ (n - 1)), 2 ^ (n - 1) - 1, -(2 ^ (n - 1)) + 1,
        2 ^ (n - 1) - 2, 2 ^ (n / 2), -(2 ^ (n / 2))]
      else [0, 1, 2, 3, 7, 2 ^ n - 1, 2 ^ n - 2, 2 ^ (n - 1), 2 ^ (n - 1) - 1, 2 ^ (n / 2)]
    let x : BitVec n :=
      match r % 10 with
      | 0 | 1 | 2 => BitVec.ofInt n (edges.getD (r2.toNat % edges.length) 0)
      | 3 | 4 | 5 => BitVec.ofInt n ((r2.toNat % 41 : Nat) - 20 : Int)
      | 6 => BitVec.ofNat n (r2.toNat % 1000)
      | _ => BitVec.ofNat n r2.toNat
    (if signed then toString x.toInt else toString x.toNat, s)

/-- `n` random argument lists for `params`. -/
def randCalls (params : Array Kind) (n : Nat) (s : UInt64) : Array (Array String) × UInt64 :=
  Id.run do
    let mut s := s
    let mut out := #[]
    for _ in [0:n] do
      let mut args := #[]
      for k in params do
        let (a, s') := randArg k s
        s := s'
        args := args.push a
      out := out.push args
    return (out, s)

/-- A parsed export with each section's tables. -/
structure Loaded where
  sections : Array (String × Tables × Func)
  params : Array Kind
  results : Array Kind

def load (path : System.FilePath) : IO (Except String Loaded) := do
  let data ← IO.FS.readBinFile path
  match parseExport data with
  | .error e => return .error s!"{path}: {e}"
  | .ok e =>
    let mut tabs : Tables := {}
    let mut secs := #[]
    for s in e.sections do
      tabs := tabs.addAll s.defs
      secs := secs.push (s.pass.toStringLossy, tabs, s.func)
    match secs[0]? with
    | none => return .error s!"{path}: no sections"
    | some (_, t0, f0) =>
      match signature t0 f0 with
      | none => return .error s!"{path}: signature outside the difftest's types"
      | some (ps, rs) => return .ok { sections := secs, params := ps, results := rs }

def fuel : Nat := 1000000

def runSection (l : Loaded) (k : Nat) (args : List Val) : Outcome :=
  match l.sections[k]? with
  | some (_, tabs, f) => run Env.p1 tabs f args {} fuel
  | none => .stuck "no section"

def funcPath (dir : String) (name : String) : System.FilePath :=
  System.FilePath.mk dir / s!"{name},1.ssa"

def gen (dir : String) (n : Nat) (seed : Nat) (names : List String) : IO UInt32 := do
  let mut s : UInt64 := UInt64.ofNat seed
  for name in names do
    match ← load (funcPath dir name) with
    | .error e => IO.eprintln e; return 1
    | .ok l =>
      let (calls, s') := randCalls l.params n s
      s := s'
      for c in calls do
        IO.println (" ".intercalate (name :: c.toList))
  return 0

def runMode (dir : String) (callsFile nativeFile : String) : IO UInt32 := do
  let calls := (← IO.FS.lines callsFile).filter (· ≠ "")
  let native := (← IO.FS.lines nativeFile).filter (· ≠ "")
  if calls.size != native.size then
    IO.eprintln s!"{calls.size} calls but {native.size} native results"
    return 1
  let mut cache : Std.HashMap String Loaded := {}
  let mut funcs : Std.HashMap String Unit := {}
  let mut nIn := 0
  let mut agree0 := 0
  let mut agreeLast := 0
  let mut agreeAll := 0
  let mut sectionRuns := 0
  let mut bad := 0
  let mut outcomes : Std.HashMap String Nat := {}
  for h : i in [0:calls.size] do
    let call := calls[i]
    let toks := (call.splitOn " ").filter (· ≠ "")
    let name := toks.headD ""
    let l ← match cache[name]? with
      | some l => pure l
      | none =>
        match ← load (funcPath dir name) with
        | .error e => IO.eprintln e; return 1
        | .ok l => pure l
    cache := cache.insert name l
    funcs := funcs.insert name ()
    let some args := (l.params.toList.zip toks.tail).mapM fun (k, s) => parseVal k s
      | IO.eprintln s!"bad call {call}"; return 1
    let want := match native[i]!.splitOn " -> " with
      | [c, o] => if c == call then o else s!"<native line {i} is for {c}>"
      | _ => s!"<bad native line {i}>"
    nIn := nIn + 1
    let kind := (want.splitOn " ").headD ""
    outcomes := outcomes.insert kind (outcomes.getD kind 0 + 1)
    let mut allOk := true
    let last := l.sections.size - 1
    for k in [0:l.sections.size] do
      let got := renderOutcome l.results (runSection l k args)
      sectionRuns := sectionRuns + 1
      if got == want then
        if k == 0 then agree0 := agree0 + 1
        if k == last then agreeLast := agreeLast + 1
      else
        allOk := false
        if bad < 40 then
          IO.println s!"MISMATCH {call} section {k} ({l.sections[k]!.1}): lean {got}, native {want}"
        bad := bad + 1
    if allOk then agreeAll := agreeAll + 1
  let kinds := outcomes.toList.map (fun (k, n) => s!"{k} {n}")
  IO.println s!"sem-difftest: {funcs.size} functions, {nIn} calls ({", ".intercalate kinds}), \
    {sectionRuns} section runs; native agrees with section 0 on {agree0}, with the last section \
    on {agreeLast}, with every section on {agreeAll}; {bad} section mismatches"
  return if bad == 0 && nIn > 0 then 0 else 1

/-- A stuck message without value/block IDs (for a histogram). -/
def stuckKey (msg : String) : String :=
  let isRef (w : String) : Bool :=
    let w := if w.endsWith ":" then (w.dropEnd 1).toString else w
    (w.startsWith "v" || w.startsWith "b") && w.length ≥ 2 && (w.drop 1).all Char.isDigit
  " ".intercalate (((msg.splitOn " ").filter (!isRef ·)).take 8)

structure CStats where
  files : Nat := 0
  eligible : Nat := 0
  calls : Nat := 0
  defined0 : Nat := 0
  stuck0 : Nat := 0
  sectionRuns : Nat := 0
  agree : Nat := 0
  gaps : Nat := 0
  diffs : Nat := 0
  gapFuncs : Nat := 0
  definedFuncs : Nat := 0
  outcomes : Std.HashMap String Nat := {}
  stuckMsgs : Std.HashMap String Nat := {}

def ssaFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "ssa")).qsort (·.toString < ·.toString)
  else return #[p]

def corpus (n seed : Nat) (dirs : List String) : IO UInt32 := do
  let mut st : CStats := {}
  let mut s : UInt64 := UInt64.ofNat seed
  for d in dirs do
    for path in ← ssaFiles d do
      st := { st with files := st.files + 1 }
      let .ok l ← load path | continue
      st := { st with eligible := st.eligible + 1 }
      let (calls, s') := randCalls l.params n s
      s := s'
      let mut gapHere := false
      let mut definedHere := false
      for c in calls do
        let some args := (l.params.toList.zip c.toList).mapM fun (k, a) => parseVal k a
          | continue
        st := { st with calls := st.calls + 1 }
        let o0 := runSection l 0 args
        let r0 := renderOutcome l.results o0
        let key := (r0.splitOn " ").headD ""
        st := { st with outcomes := st.outcomes.insert key (st.outcomes.getD key 0 + 1) }
        match o0 with
        | .stuck msg =>
          let k := stuckKey msg
          st := { st with stuck0 := st.stuck0 + 1,
                          stuckMsgs := st.stuckMsgs.insert k (st.stuckMsgs.getD k 0 + 1) }
        | .outOfFuel => st := { st with stuck0 := st.stuck0 + 1 }
        | _ =>
          st := { st with defined0 := st.defined0 + 1 }
          definedHere := true
          for k in [1:l.sections.size] do
            let o := runSection l k args
            let r := renderOutcome l.results o
            st := { st with sectionRuns := st.sectionRuns + 1 }
            if r == r0 then st := { st with agree := st.agree + 1 }
            else
              match o with
              | .stuck _ =>
                if st.gaps < 30 then
                  IO.println s!"GAP {path} section {k} ({l.sections[k]!.1}) {c.toList}: {r} (section 0: {r0})"
                st := { st with gaps := st.gaps + 1 }
                gapHere := true
              | _ =>
                if st.diffs < 30 then
                  IO.println s!"DIFF {path} section {k} ({l.sections[k]!.1}) {c.toList}: {r} (section 0: {r0})"
                st := { st with diffs := st.diffs + 1 }
      if gapHere then st := { st with gapFuncs := st.gapFuncs + 1 }
      if definedHere then st := { st with definedFuncs := st.definedFuncs + 1 }
  let kinds := st.outcomes.toList.map (fun (k, n) => s!"{k} {n}")
  let top := (st.stuckMsgs.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 15
  IO.println s!"sem-difftest corpus: {st.files} files, {st.eligible} with int/bool signatures, \
    {st.calls} calls (section 0: {", ".intercalate kinds}); {st.defined0} calls defined at \
    section 0 (in {st.definedFuncs} functions), {st.sectionRuns} later-section runs of them: {st.agree} agree, {st.diffs} \
    differ, {st.gaps} stuck (gaps, in {st.gapFuncs} functions)"
  IO.println "section-0 stuck reasons (top 15):"
  for (k, c) in top do IO.println s!"  {c} {k}"
  return if st.diffs == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "gen" :: dir :: n :: seed :: names =>
    gen dir n.toNat! seed.toNat! names
  | ["run", dir, calls, native] => runMode dir calls native
  | "corpus" :: n :: seed :: dirs => corpus n.toNat! seed.toNat! dirs
  | _ =>
    IO.eprintln "usage: sem-difftest gen <dir> <n> <seed> <func>... | run <dir> <calls> <native> | corpus <n> <seed> <dir>..."
    return 2

end GoFVTest.SemDiff

def main (args : List String) : IO UInt32 := GoFVTest.SemDiff.main args
