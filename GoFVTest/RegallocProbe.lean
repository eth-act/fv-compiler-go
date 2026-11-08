import GoFV.SSA.Parse
import GoFV.Opt.RegallocCheck

open scoped GoFV.SSA.Sem.Fixed

/-!
# `lake exe regalloc-probe [--jobs N] [--max-report K] <dir|file>...`: the regalloc checker on
Go's output

For every `.ssa` file: the section before `regalloc` (`flagalloc`'s output, scheduled) and the
`regalloc` section, both in the `regalloc` section's tables, through
`GoFV.Opt.RegallocCheck.checkRA`. Prints the number of functions accepted and rejected, the
rejections by category (the first word of the reason) with up to K examples each, and the
certificate sizes. Exit code 1 if some function is rejected.
-/

open GoFV.SSA GoFV.Opt.RegallocCheck

namespace GoFVTest.RegallocProbe

structure Res where
  files : Nat := 0
  parseErr : Nat := 0
  noRA : Nat := 0
  funcs : Nat := 0
  ok : Nat := 0
  blocks : Nat := 0
  values : Nat := 0
  facts : Nat := 0
  maxFacts : Nat := 0
  reasons : Std.HashMap String (Nat × Array String) := {}
  deriving Inhabited

def Res.add (maxRep : Nat) (a b : Res) : Res :=
  let reasons := b.reasons.fold (init := a.reasons) fun m k (n, ex) =>
    let (n0, ex0) := m.getD k (0, #[])
    m.insert k (n0 + n, (ex0 ++ ex).extract 0 maxRep)
  { files := a.files + b.files, parseErr := a.parseErr + b.parseErr, noRA := a.noRA + b.noRA,
    funcs := a.funcs + b.funcs, ok := a.ok + b.ok, blocks := a.blocks + b.blocks,
    values := a.values + b.values, facts := a.facts + b.facts,
    maxFacts := max a.maxFacts b.maxFacts, reasons }

/-- Every block's certified entry facts and check result. -/
def debugFile (path : System.FilePath) : IO Unit := do
  let data ← IO.FS.readBinFile path
  let .ok ex := parseExportUntil "loop rotate" data | IO.println "parse error"
  let some k := ex.sections.findIdx? (·.pass.toStringLossy == "regalloc") | IO.println "no regalloc"
  let cx := Cx.make (ex.tablesAt k) ex.sections[k - 1]!.func ex.sections[k]!.func
  let passes := ((← IO.getEnv "RA_PASSES").bind String.toNat?).getD 64
  let cert := certify cx passes
  for bid in cx.f.blocks do
    let S := cert.ins.getD bid []
    let fs := S.map fun (l, o) =>
      let ls := match l with
        | .reg r => s!"R{r}" | .slot k => s!"@a{k.name}+{k.off}" | .mem => "mem" | .flags => "flags"
        | .avail => "avail"
      s!"{ls}:v{o.id}{(o.comp.map (s!".{·}")).getD ""}"
    IO.println s!"b{bid}: {fs}"
    match checkBlock cx cert bid with
    | .ok () => pure ()
    | .error e => IO.println s!"  FAIL {e}"
    if let (some b, some b', some order) := (cx.f.block? bid, cx.g.block? bid, (cx.sc.sched[bid]?).join) then
      match walk cx cert S b'.values.toList order.toList with
      | .ok (S, _) =>
        for e in b.succs do
          match phiEdge cx S e.b e.i with
          | .ok E => IO.println s!"  edge b{e.b}: {E.length} facts"
          | .error err => IO.println s!"  edge b{e.b}: {err}"
      | .error err => IO.println s!"  walk: {err}"

def probeFile (maxRep : Nat) (path : System.FilePath) : IO Res := do
  let data ← IO.FS.readBinFile path
  let .ok ex := parseExportUntil "loop rotate" data
    | return { files := 1, parseErr := 1 }
  let some k := ex.sections.findIdx? (·.pass.toStringLossy == "regalloc")
    | return { files := 1, noRA := 1 }
  let some src := ex.sections[k - 1]? | return { files := 1, noRA := 1 }
  let some dst := ex.sections[k]? | return { files := 1, noRA := 1 }
  let tabs := ex.tablesAt k
  let cx := Cx.make tabs src.func dst.func
  let cert := certify cx
  let nfacts := cert.ins.foldl (· + ·.length) 0
  let maxf := cert.ins.foldl (fun m s => max m s.length) 0
  let r : Res := { files := 1, funcs := 1, blocks := src.func.blocks.size,
                   values := (dst.func.valueTab.filter (·.isSome)).size, facts := nfacts,
                   maxFacts := maxf }
  match checkWith cx cert with
  | .ok () => return { r with ok := 1 }
  | .error e =>
    let word := (e.splitOn " ").headD e
    let loc := if (e.splitOn "Loc.flags").length > 1 then "-flags"
      else if (e.splitOn "Loc.slot").length > 1 then "-slot"
      else if (e.splitOn "Loc.reg").length > 1 then "-reg"
      else if (e.splitOn "Loc.mem").length > 1 then "-mem" else ""
    let cat := word ++ loc
    return { r with reasons := ({} : Std.HashMap _ _).insert cat (1, #[s!"{path}: {e}"]) }

def main (args : List String) : IO UInt32 := do
  if let "--debug" :: p :: _ := args then
    debugFile p
    return 0
  let mut jobs := 4
  let mut maxRep := 5
  let mut paths := #[]
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--jobs" :: n :: r => jobs := n.toNat!; rest := r
    | "--max-report" :: n :: r => maxRep := n.toNat!; rest := r
    | p :: r => paths := paths.push p; rest := r
    | [] => rest := []
  let mut files : Array System.FilePath := #[]
  for a in paths do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  files := files.qsort (·.toString < ·.toString)
  -- `jobs` workers over interleaved slices of the file list
  let mut tasks := #[]
  for j in [0:jobs] do
    let mine := (List.range files.size).filter (· % jobs == j) |>.map (files[·]!)
    tasks := tasks.push (← IO.asTask (prio := .dedicated) do
      let mut acc : Res := {}
      for p in mine do
        let r ← try probeFile maxRep p catch e =>
          pure { files := 1, parseErr := 1, reasons := ({} : Std.HashMap _ _).insert "io" (1, #[s!"{p}: {e}"]) }
        acc := acc.add maxRep r
      return acc)
  let mut tot : Res := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok r => tot := tot.add maxRep r
    | .error e => IO.eprintln s!"worker failed: {e}"; return 2
  IO.println s!"files {tot.files} (parse errors {tot.parseErr}, no regalloc section {tot.noRA}), \
    functions {tot.funcs}: accepted {tot.ok}, rejected {tot.funcs - tot.ok}"
  IO.println s!"blocks {tot.blocks}, target values {tot.values}, certificate facts {tot.facts} \
    (max per block {tot.maxFacts})"
  let cats := tot.reasons.toArray.qsort (fun a b => a.2.1 > b.2.1)
  for (c, n, ex) in cats do
    IO.println s!"  {c}: {n}"
    for e in ex do IO.println s!"    {e}"
  return if tot.ok == tot.funcs && tot.parseErr == 0 then 0 else 1

end GoFVTest.RegallocProbe

def main (args : List String) : IO UInt32 := GoFVTest.RegallocProbe.main args
