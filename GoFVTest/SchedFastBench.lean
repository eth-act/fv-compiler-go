import GoFV.SSA.Parse
import GoFV.Opt.SchedFast

/-!
# `sched-fast-bench`: `schedFast` against `Sem.schedule`

For every block of every section of every `.ssa` file under the arguments (files or
directories): `schedFast` and `Sem.schedule` agree (same output, hence the same non-pure
sequence), and the total time of each. Exit code 1 if some block differs.
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.SchedFast

namespace GoFVTest.SchedFastBench

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut parseErr := 0
  let mut blocks := 0
  let mut tSlow := 0
  let mut tFast := 0
  let mut same := 0
  let mut npOnly := 0
  let mut differ := 0
  let mut fastNone := 0
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok ex := parseExport data | parseErr := parseErr + 1; continue
    for h : si in [0:ex.sections.size] do
      let f := ex.sections[si].func
      let bs := f.blocks.filterMap f.block?
      let t0 ← IO.monoNanosNow
      let slow ← IO.lazyPure fun _ => bs.map (schedule f)
      let t1 ← IO.monoNanosNow
      let fast ← IO.lazyPure fun _ => bs.map (schedFast f)
      let t2 ← IO.monoNanosNow
      tSlow := tSlow + (t1 - t0)
      tFast := tFast + (t2 - t1)
      for h : i in [0:bs.size] do
        blocks := blocks + 1
        let vs := schedNodes f bs[i]
        let np (o : Array ID) : Array ID :=
          o.filter fun x => vs.any fun n => n.id == x && n.prio != 0
        match slow[i]!, fast[i]! with
        | some a, some b =>
          if a == b then same := same + 1
          else if np a == np b then npOnly := npOnly + 1
          else
            differ := differ + 1
            if differ ≤ 10 then IO.eprintln s!"{path}: section {si} b{bs[i].id}: np sequence differs"
        | none, none => same := same + 1
        | some _, none =>
          fastNone := fastNone + 1
          if fastNone ≤ 10 then IO.eprintln s!"{path}: section {si} b{bs[i].id}: schedFast none"
        | none, some _ =>
          differ := differ + 1
          if differ ≤ 10 then IO.eprintln s!"{path}: section {si} b{bs[i].id}: schedule none"
  IO.println s!"files {files.size} (parse errors {parseErr}), blocks {blocks}: same {same}, \
    same np sequence only {npOnly}, differ {differ}, schedFast none {fastNone}"
  IO.println s!"schedule {tSlow / 1000000} ms, schedFast {tFast / 1000000} ms"
  return if differ == 0 && fastNone == 0 then 0 else 1

end GoFVTest.SchedFastBench

def main (args : List String) : IO UInt32 := GoFVTest.SchedFastBench.main args
