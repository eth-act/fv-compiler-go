import GoFV.Gen.Genssa
import GoFV.Gen.Check49
import GoFV.Asm.Parse
import GoFV.SSA.Parse
import GoFVTest.GenIn

open scoped GoFV.SSA.Sem.Fixed

/-!
# `gen-check`: coverage of the genssa validator (`docs/plans/proofs3.md` §3, §4)

For every `*.prog` file under the given directories with its companion `.ssa` file, runs
`GoFV.Gen.genssa` (on the exported frame, as `gen-parity`) and the validators of slices G1
(`GoFV.Gen.Check.checkG1`), G2 (`GoFV.Gen.Check.checkG2`, with the Prog list's symbols and the
exported frame's slot operands), G3 (`GoFV.Gen.Check.checkG3`), G4 (`GoFV.Gen.Check.checkG4`), G5
(`GoFV.Gen.Check.checkG5`), G6 (`GoFV.Gen.Check.checkG6`), G7 (`GoFV.Gen.Check.checkG7`), G8
(`GoFV.Gen.Check.checkG8`), G9 (`GoFV.Gen.Check.checkG9`), G10 (`GoFV.Gen.Check.checkG10`), G11
(`GoFV.Gen.Check.checkG11`), G12 (`GoFV.Gen.Check.checkG12`), G13 (`GoFV.Gen.Check.checkG13`),
G14 (`GoFV.Gen.Check.checkG14`), G15 (`GoFV.Gen.Check.checkG15`), G16 (`GoFV.Gen.Check.checkG16`),
G17 (`GoFV.Gen.Check.checkG17`), G18 (`GoFV.Gen.Check.checkG18`), G19 (`GoFV.Gen.Check.checkG19`),
G20 (`GoFV.Gen.Check.checkG20`), G21 (`GoFV.Gen.Check.checkG21`), G22 (`GoFV.Gen.Check.checkG22`),
G23 (`GoFV.Gen.Check.checkG23`), G24 (`GoFV.Gen.Check.checkG24`), G25 (`GoFV.Gen.Check.checkG25`),
G26 (`GoFV.Gen.Check.checkG26`), G27 (`GoFV.Gen.Check.checkG27`), G28 (`GoFV.Gen.Check.checkG28`),
G29 (`GoFV.Gen.Check.checkG29`), G30 (`GoFV.Gen.Check.checkG30`), G32 (`GoFV.Gen.Check.checkG32`),
G31 (`GoFV.Gen.Check.checkG31`), G33 (`GoFV.Gen.Check.checkG33`), G34 (`GoFV.Gen.Check.checkG34`),
G35 (`GoFV.Gen.Check.checkG35`), G36 (`GoFV.Gen.Check.checkG36`), G37
(`GoFV.Gen.Check.checkG37`), G38 (`GoFV.Gen.Check.checkG38`), G39 (`GoFV.Gen.Check.checkG39`), G40
(`GoFV.Gen.Check.checkG40`), G41 (`GoFV.Gen.Check.checkG41`), G42 (`GoFV.Gen.Check.checkG42`), G43
(`GoFV.Gen.Check.checkG43`), G44 (`GoFV.Gen.Check.checkG44`), G45 (`GoFV.Gen.Check.checkG45`), G46
(`GoFV.Gen.Check.checkG46`), G47 (`GoFV.Gen.Check.checkG47`), G50 (`GoFV.Gen.Check.checkG50`),
G51 (`GoFV.Gen.Check.checkG51`) and G49 (`GoFV.Gen.Check.checkG49`, on G51; G48 is reserved),
all with G2's inputs, on its P0 output and the function after `trim`, and counts the accepted
functions. Rejections by the last
slice are grouped by their reason with value and block numbers removed. `--sets FILE` writes each
rejected function's reason set, one line per function (path, then the reasons, tab-separated), to
measure what a slice covering several reasons would gain.

usage: `lake exe gen-check [--jobs N] [--table FILE] [--sets FILE] <dir|file>...`
-/

open GoFV.SSA (ExportFile)
open GoFV.Asm
open GoFV.Gen

namespace GoFVTest.GenCheck

structure Stats where
  files : Nat := 0
  accepted : Nat := 0
  accepted2 : Nat := 0
  accepted3 : Nat := 0
  accepted4 : Nat := 0
  accepted5 : Nat := 0
  accepted6 : Nat := 0
  accepted7 : Nat := 0
  accepted8 : Nat := 0
  accepted9 : Nat := 0
  accepted10 : Nat := 0
  accepted11 : Nat := 0
  accepted12 : Nat := 0
  accepted13 : Nat := 0
  accepted14 : Nat := 0
  accepted15 : Nat := 0
  accepted16 : Nat := 0
  accepted17 : Nat := 0
  accepted18 : Nat := 0
  accepted19 : Nat := 0
  accepted20 : Nat := 0
  accepted21 : Nat := 0
  accepted22 : Nat := 0
  accepted23 : Nat := 0
  accepted24 : Nat := 0
  accepted25 : Nat := 0
  accepted26 : Nat := 0
  accepted27 : Nat := 0
  accepted28 : Nat := 0
  accepted29 : Nat := 0
  accepted30 : Nat := 0
  accepted32 : Nat := 0
  accepted31 : Nat := 0
  accepted33 : Nat := 0
  accepted34 : Nat := 0
  accepted35 : Nat := 0
  accepted36 : Nat := 0
  accepted37 : Nat := 0
  accepted38 : Nat := 0
  accepted39 : Nat := 0
  accepted40 : Nat := 0
  accepted41 : Nat := 0
  accepted42 : Nat := 0
  accepted43 : Nat := 0
  accepted44 : Nat := 0
  accepted45 : Nat := 0
  accepted46 : Nat := 0
  accepted47 : Nat := 0
  accepted50 : Nat := 0
  accepted51 : Nat := 0
  accepted49 : Nat := 0
  errors : Nat := 0
  values : Nat := 0
  acceptedValues : Nat := 0
  acceptedValues2 : Nat := 0
  acceptedValues3 : Nat := 0
  acceptedValues4 : Nat := 0
  acceptedValues5 : Nat := 0
  acceptedValues6 : Nat := 0
  acceptedValues7 : Nat := 0
  acceptedValues8 : Nat := 0
  acceptedValues9 : Nat := 0
  acceptedValues10 : Nat := 0
  acceptedValues11 : Nat := 0
  acceptedValues12 : Nat := 0
  acceptedValues13 : Nat := 0
  acceptedValues14 : Nat := 0
  acceptedValues15 : Nat := 0
  acceptedValues16 : Nat := 0
  acceptedValues17 : Nat := 0
  acceptedValues18 : Nat := 0
  acceptedValues19 : Nat := 0
  acceptedValues20 : Nat := 0
  acceptedValues21 : Nat := 0
  acceptedValues22 : Nat := 0
  acceptedValues23 : Nat := 0
  acceptedValues24 : Nat := 0
  acceptedValues25 : Nat := 0
  acceptedValues26 : Nat := 0
  acceptedValues27 : Nat := 0
  acceptedValues28 : Nat := 0
  acceptedValues29 : Nat := 0
  acceptedValues30 : Nat := 0
  acceptedValues32 : Nat := 0
  acceptedValues31 : Nat := 0
  acceptedValues33 : Nat := 0
  acceptedValues34 : Nat := 0
  acceptedValues35 : Nat := 0
  acceptedValues36 : Nat := 0
  acceptedValues37 : Nat := 0
  acceptedValues38 : Nat := 0
  acceptedValues39 : Nat := 0
  acceptedValues40 : Nat := 0
  acceptedValues41 : Nat := 0
  acceptedValues42 : Nat := 0
  acceptedValues43 : Nat := 0
  acceptedValues44 : Nat := 0
  acceptedValues45 : Nat := 0
  acceptedValues46 : Nat := 0
  acceptedValues47 : Nat := 0
  acceptedValues50 : Nat := 0
  acceptedValues51 : Nat := 0
  acceptedValues49 : Nat := 0
  /-- Functions by the set of reasons that reject them (sole reason: one-element set). -/
  sole : Std.HashMap String Nat := {}
  /-- Functions each reason occurs in. -/
  occurs : Std.HashMap String Nat := {}
  accept : Array String := #[]
  /-- Rejected functions with their reason sets (`path\treason\t…`). -/
  sets : Array String := #[]

def mergeMap (a b : Std.HashMap String Nat) : Std.HashMap String Nat :=
  b.fold (fun m k n => m.insert k (m.getD k 0 + n)) a

def Stats.merge (a b : Stats) : Stats :=
  { files := a.files + b.files, accepted := a.accepted + b.accepted,
    accepted2 := a.accepted2 + b.accepted2, accepted3 := a.accepted3 + b.accepted3,
    accepted4 := a.accepted4 + b.accepted4, accepted5 := a.accepted5 + b.accepted5,
    accepted6 := a.accepted6 + b.accepted6, accepted7 := a.accepted7 + b.accepted7,
    accepted8 := a.accepted8 + b.accepted8, accepted9 := a.accepted9 + b.accepted9,
    accepted10 := a.accepted10 + b.accepted10, accepted11 := a.accepted11 + b.accepted11,
    accepted12 := a.accepted12 + b.accepted12, accepted13 := a.accepted13 + b.accepted13,
    accepted14 := a.accepted14 + b.accepted14, accepted15 := a.accepted15 + b.accepted15,
    accepted16 := a.accepted16 + b.accepted16, accepted17 := a.accepted17 + b.accepted17,
    accepted18 := a.accepted18 + b.accepted18, accepted19 := a.accepted19 + b.accepted19,
    accepted20 := a.accepted20 + b.accepted20, accepted21 := a.accepted21 + b.accepted21,
    accepted22 := a.accepted22 + b.accepted22, accepted23 := a.accepted23 + b.accepted23,
    accepted24 := a.accepted24 + b.accepted24, accepted25 := a.accepted25 + b.accepted25,
    accepted26 := a.accepted26 + b.accepted26, accepted27 := a.accepted27 + b.accepted27,
    accepted28 := a.accepted28 + b.accepted28, accepted29 := a.accepted29 + b.accepted29,
    accepted30 := a.accepted30 + b.accepted30, accepted32 := a.accepted32 + b.accepted32,
    accepted31 := a.accepted31 + b.accepted31, accepted33 := a.accepted33 + b.accepted33,
    accepted34 := a.accepted34 + b.accepted34, accepted35 := a.accepted35 + b.accepted35,
    accepted36 := a.accepted36 + b.accepted36, accepted37 := a.accepted37 + b.accepted37,
    accepted38 := a.accepted38 + b.accepted38, accepted39 := a.accepted39 + b.accepted39,
    accepted40 := a.accepted40 + b.accepted40, accepted41 := a.accepted41 + b.accepted41,
    accepted42 := a.accepted42 + b.accepted42, accepted43 := a.accepted43 + b.accepted43,
    accepted44 := a.accepted44 + b.accepted44,
    accepted45 := a.accepted45 + b.accepted45,
    accepted46 := a.accepted46 + b.accepted46,
    accepted47 := a.accepted47 + b.accepted47,
    accepted50 := a.accepted50 + b.accepted50,
    accepted51 := a.accepted51 + b.accepted51,
    accepted49 := a.accepted49 + b.accepted49,
    errors := a.errors + b.errors,
    values := a.values + b.values, acceptedValues := a.acceptedValues + b.acceptedValues,
    acceptedValues2 := a.acceptedValues2 + b.acceptedValues2,
    acceptedValues3 := a.acceptedValues3 + b.acceptedValues3,
    acceptedValues4 := a.acceptedValues4 + b.acceptedValues4,
    acceptedValues5 := a.acceptedValues5 + b.acceptedValues5,
    acceptedValues6 := a.acceptedValues6 + b.acceptedValues6,
    acceptedValues7 := a.acceptedValues7 + b.acceptedValues7,
    acceptedValues8 := a.acceptedValues8 + b.acceptedValues8,
    acceptedValues9 := a.acceptedValues9 + b.acceptedValues9,
    acceptedValues10 := a.acceptedValues10 + b.acceptedValues10,
    acceptedValues11 := a.acceptedValues11 + b.acceptedValues11,
    acceptedValues12 := a.acceptedValues12 + b.acceptedValues12,
    acceptedValues13 := a.acceptedValues13 + b.acceptedValues13,
    acceptedValues14 := a.acceptedValues14 + b.acceptedValues14,
    acceptedValues15 := a.acceptedValues15 + b.acceptedValues15,
    acceptedValues16 := a.acceptedValues16 + b.acceptedValues16,
    acceptedValues17 := a.acceptedValues17 + b.acceptedValues17,
    acceptedValues18 := a.acceptedValues18 + b.acceptedValues18,
    acceptedValues19 := a.acceptedValues19 + b.acceptedValues19,
    acceptedValues20 := a.acceptedValues20 + b.acceptedValues20,
    acceptedValues21 := a.acceptedValues21 + b.acceptedValues21,
    acceptedValues22 := a.acceptedValues22 + b.acceptedValues22,
    acceptedValues23 := a.acceptedValues23 + b.acceptedValues23,
    acceptedValues24 := a.acceptedValues24 + b.acceptedValues24,
    acceptedValues25 := a.acceptedValues25 + b.acceptedValues25,
    acceptedValues26 := a.acceptedValues26 + b.acceptedValues26,
    acceptedValues27 := a.acceptedValues27 + b.acceptedValues27,
    acceptedValues28 := a.acceptedValues28 + b.acceptedValues28,
    acceptedValues29 := a.acceptedValues29 + b.acceptedValues29,
    acceptedValues30 := a.acceptedValues30 + b.acceptedValues30,
    acceptedValues32 := a.acceptedValues32 + b.acceptedValues32,
    acceptedValues31 := a.acceptedValues31 + b.acceptedValues31,
    acceptedValues33 := a.acceptedValues33 + b.acceptedValues33,
    acceptedValues34 := a.acceptedValues34 + b.acceptedValues34,
    acceptedValues35 := a.acceptedValues35 + b.acceptedValues35,
    acceptedValues36 := a.acceptedValues36 + b.acceptedValues36,
    acceptedValues37 := a.acceptedValues37 + b.acceptedValues37,
    acceptedValues38 := a.acceptedValues38 + b.acceptedValues38,
    acceptedValues39 := a.acceptedValues39 + b.acceptedValues39,
    acceptedValues40 := a.acceptedValues40 + b.acceptedValues40,
    acceptedValues41 := a.acceptedValues41 + b.acceptedValues41,
    acceptedValues42 := a.acceptedValues42 + b.acceptedValues42,
    acceptedValues43 := a.acceptedValues43 + b.acceptedValues43,
    acceptedValues44 := a.acceptedValues44 + b.acceptedValues44,
    acceptedValues45 := a.acceptedValues45 + b.acceptedValues45,
    acceptedValues46 := a.acceptedValues46 + b.acceptedValues46,
    acceptedValues47 := a.acceptedValues47 + b.acceptedValues47,
    acceptedValues50 := a.acceptedValues50 + b.acceptedValues50,
    acceptedValues51 := a.acceptedValues51 + b.acceptedValues51,
    acceptedValues49 := a.acceptedValues49 + b.acceptedValues49,
    sole := mergeMap a.sole b.sole, occurs := mergeMap a.occurs b.occurs,
    accept := a.accept ++ b.accept, sets := a.sets ++ b.sets }

/-- Record a rejected function with its reasons. -/
def Stats.reject (st : Stats) (path : System.FilePath) (msgs : List String) : Stats :=
  let ks := (msgs.map classOf).eraseDups
  let occurs := ks.foldl (fun m k => m.insert k (m.getD k 0 + 1)) st.occurs
  let sole := match ks with
    | [k] => st.sole.insert k (st.sole.getD k 0 + 1)
    | _ => st.sole.insert s!"({ks.length} reasons)" (st.sole.getD s!"({ks.length} reasons)" 0 + 1)
  { st with occurs, sole, sets := st.sets.push ("\t".intercalate (path.toString :: ks)) }

/-- Every reason the G49 validator could give for `lc`: a value referring to an ID that is no value
of the function; then, on `liveCtx lc`, the homes, values, block kinds, the frame, and the run
itself. On a function with no arm64 op, the values and blocks `checkNL30` rejects. -/
def reasons49 (lc0 : GoFV.SSA.Sem.LocCtx) (ps : Array Prog) (bstart : GoFV.SSA.ID → Option Nat)
    (g : Check.G2In) : List String := Id.run do
  unless Check.refsLive lc0 do return ["a value refers to an ID that is no value of the function"]
  let lc := Check.liveCtx lc0
  let mut rs : List String := []
  let low := lc.ctx.f.lowered
  for h : i in [0:lc.homes.size] do
    unless Check.homeOK10 lc i do rs := Check.homeErr lc i :: rs
  for bid in lc.ctx.f.blocks do
    let some b := lc.ctx.f.block? bid | continue
    for id in b.values do
      let some v := lc.ctx.f.value? id | continue
      match (if low then Check.vkind49 lc g v else Check.vkindNL30 lc g v) with
      | .error e => rs := e :: rs
      | .ok _ => pure ()
    if low then
      if Check.condBr b.kind == none && Check.zeroBr b.kind == none &&
          Check.testBr b.kind == none && b.kind != .Plain && b.kind != .Ret && b.kind != .Exit then
        rs := s!"b{bid}: block kind {b.kind.name}" :: rs
    else if b.kind != .Ret then
      rs := s!"b{bid}: block kind {b.kind.name} in a function with no arm64 op" :: rs
  if let .error e := Check.checkFrame lc g then rs := e :: rs
  if rs.isEmpty then
    match Check.checkG49 lc0 ps bstart g with
    | .error e => rs := [e]
    | .ok _ => pure ()
  return rs

def checkFile (path : System.FilePath) (st : Stats) : IO Stats := do
  let st := { st with files := st.files + 1 }
  let progData ← IO.FS.readBinFile path
  let ssaData ← IO.FS.readBinFile (path.withExtension "ssa")
  let res : Except String (ExportFile × ProgFile) := do
    let (e, _) ← GoFV.SSA.parseExportExt ssaData
    let pf ← parseProgFile progData
    return (e, pf)
  match res with
  | .error e => return { (st.reject path [s!"parse: {e}"]) with errors := st.errors + 1 }
  | .ok (e, pf) =>
  match Env.load e pf with
  | .error msg => return { (st.reject path [s!"env: {msg}"]) with errors := st.errors + 1 }
  | .ok env =>
  let fr : FrameOut :=
    { dcl := pf.frame.dclOut, optDcl := pf.frame.optDcl, merges := pf.frame.merges,
      stksize := pf.frame.stksize, stkptrsize := pf.frame.stkptrsize,
      stkalign := pf.frame.stkalign }
  match genssa env fr with
  | .error msg => return { (st.reject path [s!"genssa: {msg}"]) with errors := st.errors + 1 }
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
  let st := match Check.checkG2 lc ps bstart g with
    | .ok _ => { st with accepted2 := st.accepted2 + 1, acceptedValues2 := st.acceptedValues2 + nv }
    | .error _ => st
  let st := match Check.checkG3 lc ps bstart g with
    | .ok _ => { st with accepted3 := st.accepted3 + 1, acceptedValues3 := st.acceptedValues3 + nv }
    | .error _ => st
  let ok4 := (Check.checkG4 lc ps bstart g).toOption.isSome
  let st := if ok4 then
      { st with accepted4 := st.accepted4 + 1, acceptedValues4 := st.acceptedValues4 + nv }
    else st
  let ok5 := (Check.checkG5 lc ps bstart g).toOption.isSome
  let st := if ok5 then
      { st with accepted5 := st.accepted5 + 1, acceptedValues5 := st.acceptedValues5 + nv }
    else st
  let ok6 := (Check.checkG6 lc ps bstart g).toOption.isSome
  let st := if ok6 then
      { st with accepted6 := st.accepted6 + 1, acceptedValues6 := st.acceptedValues6 + nv }
    else st
  let ok7 := (Check.checkG7 lc ps bstart g).toOption.isSome
  let st := if ok7 then
      { st with accepted7 := st.accepted7 + 1, acceptedValues7 := st.acceptedValues7 + nv }
    else st
  let ok8 := (Check.checkG8 lc ps bstart g).toOption.isSome
  let st := if ok8 then
      { st with accepted8 := st.accepted8 + 1, acceptedValues8 := st.acceptedValues8 + nv }
    else st
  let ok9 := (Check.checkG9 lc ps bstart g).toOption.isSome
  let st := if ok9 then
      { st with accepted9 := st.accepted9 + 1, acceptedValues9 := st.acceptedValues9 + nv }
    else st
  let ok10 := (Check.checkG10 lc ps bstart g).toOption.isSome
  let st := if ok10 then
      { st with accepted10 := st.accepted10 + 1, acceptedValues10 := st.acceptedValues10 + nv }
    else st
  let ok11 := (Check.checkG11 lc ps bstart g).toOption.isSome
  let st := if ok11 then
      { st with accepted11 := st.accepted11 + 1, acceptedValues11 := st.acceptedValues11 + nv }
    else st
  let ok12 := (Check.checkG12 lc ps bstart g).toOption.isSome
  let st := if ok12 then
      { st with accepted12 := st.accepted12 + 1, acceptedValues12 := st.acceptedValues12 + nv }
    else st
  let ok13 := (Check.checkG13 lc ps bstart g).toOption.isSome
  let st := if ok13 then
      { st with accepted13 := st.accepted13 + 1, acceptedValues13 := st.acceptedValues13 + nv }
    else st
  let ok14 := (Check.checkG14 lc ps bstart g).toOption.isSome
  let st := if ok14 then
      { st with accepted14 := st.accepted14 + 1, acceptedValues14 := st.acceptedValues14 + nv }
    else st
  let ok15 := (Check.checkG15 lc ps bstart g).toOption.isSome
  let st := if ok15 then
      { st with accepted15 := st.accepted15 + 1, acceptedValues15 := st.acceptedValues15 + nv }
    else st
  let ok16 := (Check.checkG16 lc ps bstart g).toOption.isSome
  let st := if ok16 then
      { st with accepted16 := st.accepted16 + 1, acceptedValues16 := st.acceptedValues16 + nv }
    else st
  let ok17 := (Check.checkG17 lc ps bstart g).toOption.isSome
  let st := if ok17 then
      { st with accepted17 := st.accepted17 + 1, acceptedValues17 := st.acceptedValues17 + nv }
    else st
  let ok18 := (Check.checkG18 lc ps bstart g).toOption.isSome
  let st := if ok18 then
      { st with accepted18 := st.accepted18 + 1, acceptedValues18 := st.acceptedValues18 + nv }
    else st
  let ok19 := (Check.checkG19 lc ps bstart g).toOption.isSome
  let st := if ok19 then
      { st with accepted19 := st.accepted19 + 1, acceptedValues19 := st.acceptedValues19 + nv }
    else st
  let ok20 := (Check.checkG20 lc ps bstart g).toOption.isSome
  let st := if ok20 then
      { st with accepted20 := st.accepted20 + 1, acceptedValues20 := st.acceptedValues20 + nv }
    else st
  let ok21 := (Check.checkG21 lc ps bstart g).toOption.isSome
  let st := if ok21 then
      { st with accepted21 := st.accepted21 + 1, acceptedValues21 := st.acceptedValues21 + nv }
    else st
  let ok22 := (Check.checkG22 lc ps bstart g).toOption.isSome
  let st := if ok22 then
      { st with accepted22 := st.accepted22 + 1, acceptedValues22 := st.acceptedValues22 + nv }
    else st
  let ok23 := (Check.checkG23 lc ps bstart g).toOption.isSome
  let st := if ok23 then
      { st with accepted23 := st.accepted23 + 1, acceptedValues23 := st.acceptedValues23 + nv }
    else st
  let ok24 := (Check.checkG24 lc ps bstart g).toOption.isSome
  let st := if ok24 then
      { st with accepted24 := st.accepted24 + 1, acceptedValues24 := st.acceptedValues24 + nv }
    else st
  let ok25 := (Check.checkG25 lc ps bstart g).toOption.isSome
  let st := if ok25 then
      { st with accepted25 := st.accepted25 + 1, acceptedValues25 := st.acceptedValues25 + nv }
    else st
  let ok26 := (Check.checkG26 lc ps bstart g).toOption.isSome
  let st := if ok26 then
      { st with accepted26 := st.accepted26 + 1, acceptedValues26 := st.acceptedValues26 + nv }
    else st
  let ok27 := (Check.checkG27 lc ps bstart g).toOption.isSome
  let st := if ok27 then
      { st with accepted27 := st.accepted27 + 1, acceptedValues27 := st.acceptedValues27 + nv }
    else st
  let ok28 := (Check.checkG28 lc ps bstart g).toOption.isSome
  let st := if ok28 then
      { st with accepted28 := st.accepted28 + 1, acceptedValues28 := st.acceptedValues28 + nv }
    else st
  let ok29 := (Check.checkG29 lc ps bstart g).toOption.isSome
  let st := if ok29 then
      { st with accepted29 := st.accepted29 + 1, acceptedValues29 := st.acceptedValues29 + nv }
    else st
  let ok30 := (Check.checkG30 lc ps bstart g).toOption.isSome
  let st := if ok30 then
      { st with accepted30 := st.accepted30 + 1, acceptedValues30 := st.acceptedValues30 + nv }
    else st
  let ok32 := (Check.checkG32 lc ps bstart g).toOption.isSome
  let st := if ok32 then
      { st with accepted32 := st.accepted32 + 1, acceptedValues32 := st.acceptedValues32 + nv }
    else st
  let ok31 := (Check.checkG31 lc ps bstart g).toOption.isSome
  let st := if ok31 then
      { st with accepted31 := st.accepted31 + 1, acceptedValues31 := st.acceptedValues31 + nv }
    else st
  let ok33 := (Check.checkG33 lc ps bstart g).toOption.isSome
  let st := if ok33 then
      { st with accepted33 := st.accepted33 + 1, acceptedValues33 := st.acceptedValues33 + nv }
    else st
  let ok34 := (Check.checkG34 lc ps bstart g).toOption.isSome
  let st := if ok34 then
      { st with accepted34 := st.accepted34 + 1, acceptedValues34 := st.acceptedValues34 + nv }
    else st
  let ok35 := (Check.checkG35 lc ps bstart g).toOption.isSome
  let st := if ok35 then
      { st with accepted35 := st.accepted35 + 1, acceptedValues35 := st.acceptedValues35 + nv }
    else st
  let ok36 := (Check.checkG36 lc ps bstart g).toOption.isSome
  let st := if ok36 then
      { st with accepted36 := st.accepted36 + 1, acceptedValues36 := st.acceptedValues36 + nv }
    else st
  let ok37 := (Check.checkG37 lc ps bstart g).toOption.isSome
  let st := if ok37 then
      { st with accepted37 := st.accepted37 + 1, acceptedValues37 := st.acceptedValues37 + nv }
    else st
  let ok38 := (Check.checkG38 lc ps bstart g).toOption.isSome
  let st := if ok38 then
      { st with accepted38 := st.accepted38 + 1, acceptedValues38 := st.acceptedValues38 + nv }
    else st
  let ok39 := (Check.checkG39 lc ps bstart g).toOption.isSome
  let st := if ok39 then
      { st with accepted39 := st.accepted39 + 1, acceptedValues39 := st.acceptedValues39 + nv }
    else st
  let ok40 := (Check.checkG40 lc ps bstart g).toOption.isSome
  let st := if ok40 then
      { st with accepted40 := st.accepted40 + 1, acceptedValues40 := st.acceptedValues40 + nv }
    else st
  let ok41 := (Check.checkG41 lc ps bstart g).toOption.isSome
  let st := if ok41 then
      { st with accepted41 := st.accepted41 + 1, acceptedValues41 := st.acceptedValues41 + nv }
    else st
  let ok42 := (Check.checkG42 lc ps bstart g).toOption.isSome
  let st := if ok42 then
      { st with accepted42 := st.accepted42 + 1, acceptedValues42 := st.acceptedValues42 + nv }
    else st
  let ok43 := (Check.checkG43 lc ps bstart g).toOption.isSome
  let st := if ok43 then
      { st with accepted43 := st.accepted43 + 1, acceptedValues43 := st.acceptedValues43 + nv }
    else st
  let ok44 := (Check.checkG44 lc ps bstart g).toOption.isSome
  let st := if ok44 then
      { st with accepted44 := st.accepted44 + 1, acceptedValues44 := st.acceptedValues44 + nv }
    else st
  let ok45 := (Check.checkG45 lc ps bstart g).toOption.isSome
  let st := if ok45 then
      { st with accepted45 := st.accepted45 + 1, acceptedValues45 := st.acceptedValues45 + nv }
    else st
  let ok46 := (Check.checkG46 lc ps bstart g).toOption.isSome
  let st := if ok46 then
      { st with accepted46 := st.accepted46 + 1, acceptedValues46 := st.acceptedValues46 + nv }
    else st
  let ok47 := (Check.checkG47 lc ps bstart g).toOption.isSome
  let st := if ok47 then
      { st with accepted47 := st.accepted47 + 1, acceptedValues47 := st.acceptedValues47 + nv }
    else st
  let ok50 := (Check.checkG50 lc ps bstart g).toOption.isSome
  let st := if ok50 then
      { st with accepted50 := st.accepted50 + 1, acceptedValues50 := st.acceptedValues50 + nv }
    else st
  let ok51 := (Check.checkG51 lc ps bstart g).toOption.isSome
  let st := if ok51 then
      { st with accepted51 := st.accepted51 + 1, acceptedValues51 := st.acceptedValues51 + nv }
    else st
  match Check.checkG49 lc ps bstart g with
  | .ok _ =>
    let tag := if ok4 then "" else if ok5 then " (G5)" else if ok6 then " (G6)"
      else if ok7 then " (G7)" else if ok8 then " (G8)" else if ok9 then " (G9)"
      else if ok10 then " (G10)" else if ok11 then " (G11)" else if ok12 then " (G12)"
      else if ok13 then " (G13)" else if ok14 then " (G14)" else if ok15 then " (G15)"
      else if ok16 then " (G16)" else if ok17 then " (G17)" else if ok18 then " (G18)"
      else if ok19 then " (G19)" else if ok20 then " (G20)" else if ok21 then " (G21)"
      else if ok22 then " (G22)" else if ok23 then " (G23)" else if ok24 then " (G24)"
      else if ok25 then " (G25)" else if ok26 then " (G26)" else if ok27 then " (G27)"
      else if ok28 then " (G28)" else if ok29 then " (G29)" else if ok30 then " (G30)"
      else if ok32 then " (G32)" else if ok31 then " (G31)" else if ok33 then " (G33)"
      else if ok34 then " (G34)" else if ok35 then " (G35)" else if ok36 then " (G36)"
      else if ok37 then " (G37)" else if ok38 then " (G38)" else if ok39 then " (G39)"
      else if ok40 then " (G40)" else if ok41 then " (G41)" else if ok42 then " (G42)"
      else if ok43 then " (G43)" else if ok44 then " (G44)" else if ok45 then " (G45)"
      else if ok46 then " (G46)" else if ok47 then " (G47)" else if ok50 then " (G50)"
      else if ok51 then " (G51)" else " (G49)"
    return { st with accepted49 := st.accepted49 + 1, acceptedValues49 := st.acceptedValues49 + nv,
                     accept := st.accept.push s!"{path}{tag}" }
  | .error msg =>
    let rs := reasons49 lc ps bstart g
    return st.reject path (if rs.isEmpty then [msg] else rs)

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
  let rec parse : List String → Nat × Option String × Option String × Array String →
      Option (Nat × Option String × Option String × Array String)
    | [], o => some o
    | "--jobs" :: n :: rest, (_, t, s, ps) => n.toNat?.bind fun n => parse rest (max n 1, t, s, ps)
    | "--table" :: f :: rest, (j, _, s, ps) => parse rest (j, some f, s, ps)
    | "--sets" :: f :: rest, (j, t, _, ps) => parse rest (j, t, some f, ps)
    | p :: rest, (j, t, s, ps) => parse rest (j, t, s, ps.push p)
  let some (jobs, table, sets, paths) := parse args (1, none, none, #[])
    | IO.eprintln "usage: gen-check [--jobs N] [--table FILE] [--sets FILE] <dir|file>..."; return 2
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
  out := out ++ s!"| {st.files} | G3 | {st.accepted3} | {pct st.accepted3 st.files} | {st.values} | {st.acceptedValues3} |\n"
  out := out ++ s!"| {st.files} | G4 | {st.accepted4} | {pct st.accepted4 st.files} | {st.values} | {st.acceptedValues4} |\n"
  out := out ++ s!"| {st.files} | G5 | {st.accepted5} | {pct st.accepted5 st.files} | {st.values} | {st.acceptedValues5} |\n"
  out := out ++ s!"| {st.files} | G6 | {st.accepted6} | {pct st.accepted6 st.files} | {st.values} | {st.acceptedValues6} |\n"
  out := out ++ s!"| {st.files} | G7 | {st.accepted7} | {pct st.accepted7 st.files} | {st.values} | {st.acceptedValues7} |\n"
  out := out ++ s!"| {st.files} | G8 | {st.accepted8} | {pct st.accepted8 st.files} | {st.values} | {st.acceptedValues8} |\n"
  out := out ++ s!"| {st.files} | G9 | {st.accepted9} | {pct st.accepted9 st.files} | {st.values} | {st.acceptedValues9} |\n"
  out := out ++ s!"| {st.files} | G10 | {st.accepted10} | {pct st.accepted10 st.files} | {st.values} | {st.acceptedValues10} |\n"
  out := out ++ s!"| {st.files} | G11 | {st.accepted11} | {pct st.accepted11 st.files} | {st.values} | {st.acceptedValues11} |\n"
  out := out ++ s!"| {st.files} | G12 | {st.accepted12} | {pct st.accepted12 st.files} | {st.values} | {st.acceptedValues12} |\n"
  out := out ++ s!"| {st.files} | G13 | {st.accepted13} | {pct st.accepted13 st.files} | {st.values} | {st.acceptedValues13} |\n"
  out := out ++ s!"| {st.files} | G14 | {st.accepted14} | {pct st.accepted14 st.files} | {st.values} | {st.acceptedValues14} |\n"
  out := out ++ s!"| {st.files} | G15 | {st.accepted15} | {pct st.accepted15 st.files} | {st.values} | {st.acceptedValues15} |\n"
  out := out ++ s!"| {st.files} | G16 | {st.accepted16} | {pct st.accepted16 st.files} | {st.values} | {st.acceptedValues16} |\n"
  out := out ++ s!"| {st.files} | G17 | {st.accepted17} | {pct st.accepted17 st.files} | {st.values} | {st.acceptedValues17} |\n"
  out := out ++ s!"| {st.files} | G18 | {st.accepted18} | {pct st.accepted18 st.files} | {st.values} | {st.acceptedValues18} |\n"
  out := out ++ s!"| {st.files} | G19 | {st.accepted19} | {pct st.accepted19 st.files} | {st.values} | {st.acceptedValues19} |\n"
  out := out ++ s!"| {st.files} | G20 | {st.accepted20} | {pct st.accepted20 st.files} | {st.values} | {st.acceptedValues20} |\n"
  out := out ++ s!"| {st.files} | G21 | {st.accepted21} | {pct st.accepted21 st.files} | {st.values} | {st.acceptedValues21} |\n"
  out := out ++ s!"| {st.files} | G22 | {st.accepted22} | {pct st.accepted22 st.files} | {st.values} | {st.acceptedValues22} |\n"
  out := out ++ s!"| {st.files} | G23 | {st.accepted23} | {pct st.accepted23 st.files} | {st.values} | {st.acceptedValues23} |\n"
  out := out ++ s!"| {st.files} | G24 | {st.accepted24} | {pct st.accepted24 st.files} | {st.values} | {st.acceptedValues24} |\n"
  out := out ++ s!"| {st.files} | G25 | {st.accepted25} | {pct st.accepted25 st.files} | {st.values} | {st.acceptedValues25} |\n"
  out := out ++ s!"| {st.files} | G26 | {st.accepted26} | {pct st.accepted26 st.files} | {st.values} | {st.acceptedValues26} |\n"
  out := out ++ s!"| {st.files} | G27 | {st.accepted27} | {pct st.accepted27 st.files} | {st.values} | {st.acceptedValues27} |\n"
  out := out ++ s!"| {st.files} | G28 | {st.accepted28} | {pct st.accepted28 st.files} | {st.values} | {st.acceptedValues28} |\n"
  out := out ++ s!"| {st.files} | G29 | {st.accepted29} | {pct st.accepted29 st.files} | {st.values} | {st.acceptedValues29} |\n"
  out := out ++ s!"| {st.files} | G30 | {st.accepted30} | {pct st.accepted30 st.files} | {st.values} | {st.acceptedValues30} |\n"
  out := out ++ s!"| {st.files} | G32 | {st.accepted32} | {pct st.accepted32 st.files} | {st.values} | {st.acceptedValues32} |\n"
  out := out ++ s!"| {st.files} | G31 | {st.accepted31} | {pct st.accepted31 st.files} | {st.values} | {st.acceptedValues31} |\n"
  out := out ++ s!"| {st.files} | G33 | {st.accepted33} | {pct st.accepted33 st.files} | {st.values} | {st.acceptedValues33} |\n"
  out := out ++ s!"| {st.files} | G34 | {st.accepted34} | {pct st.accepted34 st.files} | {st.values} | {st.acceptedValues34} |\n"
  out := out ++ s!"| {st.files} | G35 | {st.accepted35} | {pct st.accepted35 st.files} | {st.values} | {st.acceptedValues35} |\n"
  out := out ++ s!"| {st.files} | G36 | {st.accepted36} | {pct st.accepted36 st.files} | {st.values} | {st.acceptedValues36} |\n"
  out := out ++ s!"| {st.files} | G37 | {st.accepted37} | {pct st.accepted37 st.files} | {st.values} | {st.acceptedValues37} |\n"
  out := out ++ s!"| {st.files} | G38 | {st.accepted38} | {pct st.accepted38 st.files} | {st.values} | {st.acceptedValues38} |\n"
  out := out ++ s!"| {st.files} | G39 | {st.accepted39} | {pct st.accepted39 st.files} | {st.values} | {st.acceptedValues39} |\n"
  out := out ++ s!"| {st.files} | G40 | {st.accepted40} | {pct st.accepted40 st.files} | {st.values} | {st.acceptedValues40} |\n"
  out := out ++ s!"| {st.files} | G41 | {st.accepted41} | {pct st.accepted41 st.files} | {st.values} | {st.acceptedValues41} |\n"
  out := out ++ s!"| {st.files} | G42 | {st.accepted42} | {pct st.accepted42 st.files} | {st.values} | {st.acceptedValues42} |\n"
  out := out ++ s!"| {st.files} | G43 | {st.accepted43} | {pct st.accepted43 st.files} | {st.values} | {st.acceptedValues43} |\n"
  out := out ++ s!"| {st.files} | G44 | {st.accepted44} | {pct st.accepted44 st.files} | {st.values} | {st.acceptedValues44} |\n"
  out := out ++ s!"| {st.files} | G45 | {st.accepted45} | {pct st.accepted45 st.files} | {st.values} | {st.acceptedValues45} |\n"
  out := out ++ s!"| {st.files} | G46 | {st.accepted46} | {pct st.accepted46 st.files} | {st.values} | {st.acceptedValues46} |\n"
  out := out ++ s!"| {st.files} | G47 | {st.accepted47} | {pct st.accepted47 st.files} | {st.values} | {st.acceptedValues47} |\n"
  out := out ++ s!"| {st.files} | G50 | {st.accepted50} | {pct st.accepted50 st.files} | {st.values} | {st.acceptedValues50} |\n"
  out := out ++ s!"| {st.files} | G51 | {st.accepted51} | {pct st.accepted51 st.files} | {st.values} | {st.acceptedValues51} |\n"
  out := out ++ s!"| {st.files} | G49 | {st.accepted49} | {pct st.accepted49 st.files} | {st.values} | {st.acceptedValues49} |\n"
  out := out ++ s!"\n{st.errors} parse, env or genssa errors\n"
  let sorted (m : Std.HashMap String Nat) :=
    m.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
  out := out ++ "\n| sole reason | functions |\n| --- | ---: |\n"
  for (k, c) in (sorted st.sole).toList.take 60 do out := out ++ s!"| `{k}` | {c} |\n"
  out := out ++ "\n| reason | functions it occurs in |\n| --- | ---: |\n"
  for (k, c) in (sorted st.occurs).toList.take 80 do out := out ++ s!"| `{k}` | {c} |\n"
  out := out ++ "\naccepted (G49; the first slice that accepts a function past G4 in parentheses):\n"
  for a in st.accept.qsort (· < ·) do out := out ++ s!"- {a}\n"
  IO.println out
  if let some f := table then IO.FS.writeFile f out
  if let some f := sets then
    IO.FS.writeFile f (String.join ((st.sets.qsort (· < ·)).toList.map (· ++ "\n")))
  return 0

end GoFVTest.GenCheck

def main (args : List String) : IO UInt32 := GoFVTest.GenCheck.main args
