import GoFV.SSA.Parse
import GoFV.SSA.StoreOrder
import GoFV.SSA.Analysis.CfgCache
import GoFV.SSA.XPosMap
import GoFV.SSA.TypeCmp

/-!
# `analysis-difftest`

Differential test of the CFG analyses and the shared position/type helpers against the
analyses the stock compiler cached (`cache` lines of every section of every export file under
the given directories):

- `postorder`: the cached postorder equals `Analysis.postorder` of the section's function
  (fresh), or else of the function before or after the pass that cached it (the first section
  of the run of sections carrying the same cache): stale, explained;
- `idom`: the cached immediate dominators (over `f.Blocks`) equal `Analysis.dominators`;
- `sdom`: the cached sparse tree equals `newSparseTree` of the cached postorder and idom (the
  ones Go built it from: all three are invalidated together);
- `linestarts`: `XPosMap.ofCache` / `toCache` reproduces the cache;
- `typeorder`: every type number defined in the file is ranked;
- `storeOrder`: each block after `nilcheckelim` lists its values in `storeOrder` of the input
  order (blocks the pass's dominator walk reaches) or keeps them (the others).

usage: `lake exe analysis-difftest <dir|file>...`; exit status 1 on any unexplained mismatch.
-/

open GoFV.SSA GoFV.SSA.Analysis

namespace GoFVTest.AnalysisDiff

structure Stats where
  files : Nat := 0
  sections : Nat := 0
  poCached : Nat := 0
  poFresh : Nat := 0
  poStale : Nat := 0
  poBad : Nat := 0
  idomCached : Nat := 0
  idomOk : Nat := 0
  idomBad : Nat := 0
  sdomCached : Nat := 0
  sdomOk : Nat := 0
  sdomBad : Nat := 0
  loopnest : Nat := 0
  lineStarts : Nat := 0
  lineStartsBad : Nat := 0
  types : Nat := 0
  typesUnranked : Nat := 0
  soBlocks : Nat := 0
  soReordered : Nat := 0
  soUnvisited : Nat := 0
  soBad : Nat := 0
  failed : Nat := 0
  deriving Repr

/-- A by-ID cache projected on `f.Blocks` (what the export prints). -/
def onBlocks {α} [Inhabited α] (f : Func) (a : Array α) : Array (ID × α) :=
  f.blocks.map fun b => (b, a[b]?.getD default)

/-- `nilcheckelim` (section `k`) sets `b.Values = storeOrder(b.Values, …)` for every block of
its dominator walk before changing any op or position, and removes no value: each output block
lists the values of `storeOrder` of its input, or (not reached by the walk) its input order. -/
def checkStoreOrder (path : System.FilePath) (e : ExportFile) (k : Nat) (st : Stats) :
    IO (Stats × Bool) := do
  let some mem := ((e.sections[0]!.typs.getD #[]).find? (·.1 == "Mem")).map (·.2)
    | IO.eprintln s!"FAIL {path}: no Mem type"; return (st, true)
  let tabs := e.tablesAt (k - 1)
  let inp := e.sections[k - 1]!.func
  let out := e.sections[k]!.func
  let mut st := st
  let mut bad := false
  let dom := dominators inp
  -- Go's scratch `storeNumber`, shared by all blocks (their values are disjoint)
  let mut sn : Array Int := Array.replicate (inp.vidLast + 1) 0
  for b in inp.blocks do
    let some bi := inp.block? b | continue
    let some bo := out.block? b | continue
    st := { st with soBlocks := st.soBlocks + 1 }
    let reached := b == inp.entry || (dom[b]?.join).isSome
    match storeOrder inp (tabs.isMemory mem) "nilcheckelim" bi.values sn with
    | .ok (o, sn') =>
      sn := sn'
      if reached && o == bo.values then
        if o != bi.values then st := { st with soReordered := st.soReordered + 1 }
      else if !reached && bi.values == bo.values then
        st := { st with soUnvisited := st.soUnvisited + 1 }
      else
        st := { st with soBad := st.soBad + 1 }
        bad := true
        IO.eprintln s!"FAIL {path}: storeOrder b{b}: {o} want {bo.values}"
    | .error err =>
      st := { st with soBad := st.soBad + 1 }
      bad := true
      IO.eprintln s!"FAIL {path}: storeOrder b{b}: {err}"
  return (st, bad)

def checkFile (path : System.FilePath) (st : Stats) : IO Stats := do
  let data ← IO.FS.readBinFile path
  match parseExportUntil "lower" data with
  | .error e =>
    IO.eprintln s!"FAIL {path}: parse error: {e}"
    return { st with failed := st.failed + 1 }
  | .ok e =>
    let mut st := { st with files := st.files + 1, sections := st.sections + e.sections.size }
    let mut bad := false
    let secs := e.sections
    for h : k in [0:secs.size] do
      let f := secs[k].func
      let c := f.cache
      if c.loopnest.isSome then st := { st with loopnest := st.loopnest + 1 }
      if let some po := c.postorder then
        st := { st with poCached := st.poCached + 1 }
        if Analysis.postorder f == po then st := { st with poFresh := st.poFresh + 1 }
        else
          -- first section of the run carrying the same postorder
          let mut j := k
          for _ in [0:k] do
            if j > 0 && secs[j - 1]!.func.cache.postorder == some po then j := j - 1 else break
          let before := if j > 0 then Analysis.postorder secs[j - 1]!.func == po else false
          if before || Analysis.postorder secs[j]!.func == po then
            st := { st with poStale := st.poStale + 1 }
          else
            st := { st with poBad := st.poBad + 1 }
            bad := true
            IO.eprintln s!"FAIL {path}: section {k} ({secs[k].pass}): postorder {po} unexplained, fresh {Analysis.postorder f}"
      if let some d := c.idom then
        st := { st with idomCached := st.idomCached + 1 }
        let mine := dominators f
        if onBlocks f mine == onBlocks f d then st := { st with idomOk := st.idomOk + 1 }
        else
          st := { st with idomBad := st.idomBad + 1 }
          bad := true
          IO.eprintln s!"FAIL {path}: section {k} ({secs[k].pass}): idom {onBlocks f d} computed {onBlocks f mine}"
      if let some t := c.sdom then
        st := { st with sdomCached := st.sdomCached + 1 }
        match c.postorder, c.idom with
        | some po, some d =>
          let mine := newSparseTree (f.bidLast + 1) f.entry po d
          if onBlocks f mine == onBlocks f t then st := { st with sdomOk := st.sdomOk + 1 }
          else
            st := { st with sdomBad := st.sdomBad + 1 }
            bad := true
            IO.eprintln s!"FAIL {path}: section {k} ({secs[k].pass}): sdom {repr (onBlocks f t)} computed {repr (onBlocks f mine)}"
        | _, _ =>
          st := { st with sdomBad := st.sdomBad + 1 }
          bad := true
          IO.eprintln s!"FAIL {path}: section {k}: sdom cached without postorder and idom"
      if let some ls := c.lineStarts then
        st := { st with lineStarts := st.lineStarts + 1 }
        if (XPosMap.ofLineRanges ls).toCache != ls then
          st := { st with lineStartsBad := st.lineStartsBad + 1 }
          bad := true
          IO.eprintln s!"FAIL {path}: section {k}: linestarts round trip"
    let o := TypeOrder.ofGroups e.typeOrder e.typeCmp
    for s in secs do
      for d in s.defs do
        if let .type n _ := d then
          st := { st with types := st.types + 1 }
          if (o.rank? n).isNone then
            st := { st with typesUnranked := st.typesUnranked + 1 }
            bad := true
            IO.eprintln s!"FAIL {path}: type t{n} not in typeorder"
    if let some k := secs.findIdx? (·.pass == GoStr.ofString "nilcheckelim") then
      let (st', b) ← checkStoreOrder path e k st
      st := st'
      bad := bad || b
    if bad then st := { st with failed := st.failed + 1 }
    return st

def ssaFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "ssa")).qsort (·.toString < ·.toString)
  else return #[p]

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: analysis-difftest <dir|file>..."
    return 2
  let t0 ← IO.monoMsNow
  let mut st : Stats := {}
  for a in args do
    for f in ← ssaFiles a do
      st ← checkFile f st
  let t1 ← IO.monoMsNow
  IO.println s!"{repr st}"
  IO.println s!"time {(t1 - t0) / 1000} s"
  return if st.failed == 0 then 0 else 1

end GoFVTest.AnalysisDiff

def main (args : List String) : IO UInt32 := GoFVTest.AnalysisDiff.main args
