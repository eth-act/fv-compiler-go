import GoFV.Gen.Genssa
import GoFV.Gen.Check2
import GoFV.Asm.Parse
import GoFV.SSA.Parse

/-!
# `gen-check`: coverage of the genssa validator (`docs/plans/proofs3.md` §3, §4)

For every `*.prog` file under the given directories with its companion `.ssa` file, runs
`GoFV.Gen.genssa` (on the exported frame, as `gen-parity`) and the validators of slice G1
(`GoFV.Gen.Check.checkG1`) and slice G2 (`GoFV.Gen.Check.checkG2`, with the Prog list's symbols
and the exported frame's slot operands) on its P0 output and the function after `trim`, and counts
the accepted functions. Rejections by G2 are grouped by their reason with value and block numbers
removed.

usage: `lake exe gen-check [--jobs N] [--table FILE] <dir|file>...`
-/

open GoFV.SSA (ExportFile)
open GoFV.Asm
open GoFV.Gen

namespace GoFVTest.GenCheck

structure Stats where
  files : Nat := 0
  accepted : Nat := 0
  accepted2 : Nat := 0
  errors : Nat := 0
  values : Nat := 0
  acceptedValues : Nat := 0
  acceptedValues2 : Nat := 0
  /-- Functions by the set of reasons that reject them (sole reason: one-element set). -/
  sole : Std.HashMap String Nat := {}
  /-- Functions each reason occurs in. -/
  occurs : Std.HashMap String Nat := {}
  accept : Array String := #[]

def mergeMap (a b : Std.HashMap String Nat) : Std.HashMap String Nat :=
  b.fold (fun m k n => m.insert k (m.getD k 0 + n)) a

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, accepted := a.accepted + b.accepted,
    accepted2 := a.accepted2 + b.accepted2, errors := a.errors + b.errors,
    values := a.values + b.values, acceptedValues := a.acceptedValues + b.acceptedValues,
    acceptedValues2 := a.acceptedValues2 + b.acceptedValues2,
    sole := mergeMap a.sole b.sole, occurs := mergeMap a.occurs b.occurs,
    accept := a.accept ++ b.accept }

/-- The reason with `v<n>`, `b<n>` and other numbers replaced. -/
def classOf (msg : String) : String := Id.run do
  let mut out := ""
  let mut prevDigit := false
  for c in msg.toList do
    if c.isDigit then
      unless prevDigit do out := out.push '#'
      prevDigit := true
    else
      out := out.push c
      prevDigit := false
  return out

/-- Record a rejected function with its reasons. -/
def Stats.reject (st : Stats) (msgs : List String) : Stats :=
  let ks := (msgs.map classOf).eraseDups
  let occurs := ks.foldl (fun m k => m.insert k (m.getD k 0 + 1)) st.occurs
  let sole := match ks with
    | [k] => st.sole.insert k (st.sole.getD k 0 + 1)
    | _ => st.sole.insert s!"({ks.length} reasons)" (st.sole.getD s!"({ks.length} reasons)" 0 + 1)
  { st with occurs, sole }

/-- Every reason the G2 validator could give for `lc` (homes, values, block kinds, the frame;
then the run itself). -/
def reasons2 (lc : GoFV.SSA.Sem.LocCtx) (ps : Array Prog) (bstart : GoFV.SSA.ID → Option Nat)
    (g : Check.G2In) : List String := Id.run do
  let mut rs : List String := []
  unless lc.ctx.f.lowered do rs := "not lowered" :: rs
  let mut classes : Std.HashMap Nat Nat := {}
  for h : i in [0:lc.homes.size] do
    match lc.homes[i] with
    | some (.reg r) =>
      if r == GoFV.SSA.Sem.zeroReg then continue
      match Check.cls (lc.ty i) with
      | none => rs := s!"v{i}: register value of shape {repr (lc.ty i)}" :: rs
      | some c =>
        match classes[r]? with
        | some c' => if c != c' then rs := s!"v{i}: register {r} holds classes {c'} and {c}" :: rs
        | none => classes := classes.insert r c
    | some _ => unless Check.homeOK2 lc i do rs := Check.homeErr lc i :: rs
    | none => pure ()
  for bid in lc.ctx.f.blocks do
    let some b := lc.ctx.f.block? bid | continue
    for id in b.values do
      let some v := lc.ctx.f.value? id | continue
      match Check.vkind2 lc g v with
      | .error e => rs := e :: rs
      | .ok _ => pure ()
    if Check.condBr b.kind == none && Check.zeroBr b.kind == none && b.kind != .Plain &&
        b.kind != .Ret && b.kind != .Exit then
      rs := s!"b{bid}: block kind {b.kind.name}" :: rs
  if let .error e := Check.checkFrame lc g then rs := e :: rs
  if rs.isEmpty then
    match Check.checkG2 lc ps bstart g with
    | .error e => rs := [e]
    | .ok _ => pure ()
  return rs

/-- Go's frame layout of slot `k`: the name class and operand offset (`AddrAuto`). -/
def slotOpOf (env : Env) (offs : Array (Option Int)) (k : GoFV.SSA.SlotKey) :
    Option (AddrName × Int) := do
  let n ← env.nameOfAux? k.name
  let off ← (offs[n]?).join
  let x ← (env.name n).toOption
  let outregs := (env.inFlags[n]?).any (·.outregs)
  let cls := if x.cls == "PPARAM" || (x.cls == "PPARAMOUT" && !outregs) then AddrName.PARAM
    else .AUTO
  return (cls, off + k.off)

def checkFile (path : System.FilePath) (st : Stats) : IO Stats := do
  let st := { st with files := st.files + 1 }
  let progData ← IO.FS.readBinFile path
  let ssaData ← IO.FS.readBinFile (path.withExtension "ssa")
  let res : Except String (ExportFile × ProgFile) := do
    let (e, _) ← GoFV.SSA.parseExportExt ssaData
    let pf ← parseProgFile progData
    return (e, pf)
  match res with
  | .error e => return { (st.reject [s!"parse: {e}"]) with errors := st.errors + 1 }
  | .ok (e, pf) =>
  match Env.load e pf with
  | .error msg => return { (st.reject [s!"env: {msg}"]) with errors := st.errors + 1 }
  | .ok env =>
  let fr : FrameOut :=
    { dcl := pf.frame.dclOut, optDcl := pf.frame.optDcl, merges := pf.frame.merges,
      stksize := pf.frame.stksize, stkptrsize := pf.frame.stkptrsize,
      stkalign := pf.frame.stkalign }
  match genssa env fr with
  | .error msg => return { (st.reject [s!"genssa: {msg}"]) with errors := st.errors + 1 }
  | .ok out =>
  let ps := out.order.filterMap (out.st.progs[·]?)
  let lc := GoFV.SSA.Sem.LocCtx.make env.tabs env.f
  let nv := env.f.blocks.foldl (fun n b => n + ((env.f.block? b).map (·.values.size)).getD 0) 0
  let st := { st with values := st.values + nv }
  let bstart := fun b => (out.st.bstart[b]?).join
  let st := match Check.checkG1 lc ps bstart with
    | .ok _ => { st with accepted := st.accepted + 1, acceptedValues := st.acceptedValues + nv }
    | .error _ => st
  let g : Check.G2In :=
    { syms := out.st.syms, slotOp := slotOpOf env (Ctx.ofFrame env fr).offsets,
      stksize := fr.stksize }
  match Check.checkG2 lc ps bstart g with
  | .ok _ =>
    return { st with accepted2 := st.accepted2 + 1, acceptedValues2 := st.acceptedValues2 + nv,
                     accept := st.accept.push path.toString }
  | .error msg =>
    let rs := reasons2 lc ps bstart g
    return st.reject (if rs.isEmpty then [msg] else rs)

def progFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "prog")).qsort (·.toString < ·.toString)
  else return #[p]

def pct (a b : Nat) : String :=
  if b == 0 then "-" else
  let x := a * 10000 / b
  s!"{x / 100}.{if x % 100 < 10 then "0" else ""}{x % 100}%"

def main (args : List String) : IO UInt32 := do
  let rec parse : List String → Nat × Option String × Array String → Option (Nat × Option String × Array String)
    | [], o => some o
    | "--jobs" :: n :: rest, (_, t, ps) => n.toNat?.bind fun n => parse rest (max n 1, t, ps)
    | "--table" :: f :: rest, (j, _, ps) => parse rest (j, some f, ps)
    | p :: rest, (j, t, ps) => parse rest (j, t, ps.push p)
  let some (jobs, table, paths) := parse args (1, none, #[])
    | IO.eprintln "usage: gen-check [--jobs N] [--table FILE] <dir|file>..."; return 2
  let mut files := #[]
  for p in paths do files := files ++ (← progFiles p)
  let tasks ← (List.range jobs).toArray.mapM fun j => IO.asTask (prio := .dedicated) do
    let mut st : Stats := {}
    for h : i in [0:files.size] do
      if i % jobs == j then st ← checkFile files[i] st
    return st
  let mut st : Stats := {}
  for t in tasks do
    match ← IO.wait t with
    | .ok s => st := st.merge s
    | .error e => IO.eprintln s!"worker failed: {e}"; return 1
  let mut out := s!"| functions | slice | accepted | share | values | in accepted functions |\n| ---: | --- | ---: | ---: | ---: | ---: |\n"
  out := out ++ s!"| {st.files} | G1 | {st.accepted} | {pct st.accepted st.files} | {st.values} | {st.acceptedValues} |\n"
  out := out ++ s!"| {st.files} | G2 | {st.accepted2} | {pct st.accepted2 st.files} | {st.values} | {st.acceptedValues2} |\n"
  out := out ++ s!"\n{st.errors} parse, env or genssa errors\n"
  let sorted (m : Std.HashMap String Nat) :=
    m.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
  out := out ++ "\n| sole reason | functions |\n| --- | ---: |\n"
  for (k, c) in (sorted st.sole).toList.take 60 do out := out ++ s!"| `{k}` | {c} |\n"
  out := out ++ "\n| reason | functions it occurs in |\n| --- | ---: |\n"
  for (k, c) in (sorted st.occurs).toList.take 80 do out := out ++ s!"| `{k}` | {c} |\n"
  out := out ++ "\naccepted (G2):\n"
  for a in st.accept.qsort (· < ·) do out := out ++ s!"- {a}\n"
  IO.println out
  if let some f := table then IO.FS.writeFile f out
  return 0

end GoFVTest.GenCheck

def main (args : List String) : IO UInt32 := GoFVTest.GenCheck.main args
