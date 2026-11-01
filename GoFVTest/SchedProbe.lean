import GoFV.SSA.Parse
import GoFV.SSA.Sem.Run

/-!
# `sched-probe`: Kahn's schedules pass `schedValid`

For every block of every section of every `.ssa` file under the arguments (files or
directories): whenever `kahn` schedules the block, its output passes `schedValid` (including
the NilFirst check), so `schedule` returns `kahn`'s output and never falls back to `greedy`.
Exit code 1 if some block fails.
-/

open GoFV.SSA GoFV.SSA.Sem

namespace GoFVTest.SchedProbe

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut parseErr := 0
  let mut secs := 0
  let mut blocks := 0
  let mut cyclic := 0
  let mut valid := 0
  let mut bad := 0
  let mut withNil := 0
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok ex := parseExport data | parseErr := parseErr + 1; continue
    for h : si in [0:ex.sections.size] do
      let f := ex.sections[si].func
      secs := secs + 1
      for bid in f.blocks do
        let some b := f.block? bid | continue
        blocks := blocks + 1
        let vs := schedNodes f b
        if vs.any (·.prio == 1) then withNil := withNil + 1
        match kahn vs with
        | none => cyclic := cyclic + 1
        | some o =>
          if schedValid vs o then valid := valid + 1
          else
            bad := bad + 1
            if bad ≤ 10 then IO.eprintln s!"{path}: section {si} b{bid}: kahn output fails schedValid"
  IO.println s!"files {files.size} (parse errors {parseErr}), sections {secs}, blocks {blocks} \
    (with NilCheck {withNil}): kahn none {cyclic}, kahn valid {valid}, kahn invalid {bad}"
  return if bad == 0 then 0 else 1

end GoFVTest.SchedProbe

def main (args : List String) : IO UInt32 := GoFVTest.SchedProbe.main args
