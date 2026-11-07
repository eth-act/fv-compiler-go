import GoFV.SSA.Parse
import GoFV.SSA.Sem.RunSched
import GoFV.SSA.Sem.RunLoc
import GoFV.SSA.Sem.RunFrame
import GoFV.Asm.Parse
import GoFV.SSA.Sem.Image
import GoFV.SSA.Sem.Runtime
import Std.Data.HashMap

/-!
# `sem-difftest`: differential test of `GoFV.SSA.run` (issue #10)

Three modes (driven by `scripts/sem-difftest.sh`):

- `gen <dir> <n> <seed> <func>...`: for each function `<dir>/<func>,1.ssa` of the export,
  print `n` calls `<func>\t<arg>...` with random and edge-case arguments of its parameter
  types.
- `run <dir> <calls> <native>`: run every call of `<calls>` on **every section** of the
  function's export (the generic sections with `GoFV.SSA.run`, the lowered ones, `lower` …
  `layout`, with `GoFV.SSA.runL`, `schedule` … `flagalloc` with `GoFV.SSA.runSched`, and
  `regalloc` … `trim` with `GoFV.SSA.runLoc`, `docs/plans/semantics2.md` L0/L1/L2), and compare
  each outcome with the native result
  (`<native>`, the output of `tools/semdiff/prog` under `qemu-aarch64-static`, one line
  `<call> -> <outcome>` per call). Exit status 1 on any disagreement. When the function's
  `.prog` companion (same stem) exists, each call also runs on the last section with
  `GoFV.SSA.runFrame` (L2f, `docs/plans/semantics3.md` §4.2) under the frame layout of the
  `.prog` file (`progLayout`), compared with native the same way (`frame` in the summary and
  in `MISMATCH` lines); a layout `FrameLayout.problems` rejects is printed as `FRAMELAYOUT`.
- `corpus <n> <seed> <dir>...`: for every export file below the directories whose function's
  parameter and result types the difftest can build and print, run `n` random calls on every
  section and check that every section agrees with section 0 whenever section 0 returns or
  panics (the stock pipeline must preserve the semantics). Counts calls whose section 0 is
  stuck (outside the implemented phases) separately; a later section that is stuck where
  section 0 is not is reported as a gap.

Values are written in the syntax of `tools/semdiff/prog/main.go`: integers in decimal,
floats as their bit patterns in hex (`0x3ff0000000000000`), complex numbers `{re,im}`,
`true`/`false`, Go-quoted strings, slices `nil` or `[e,…]`, arrays `[e,…]`, structs `{f,…}`,
pointers `nil` or `&e`. A value is built as its in-memory bytes, with fresh heap allocations
for what slices, strings and pointers point to; the outcome prints the results and then the
arguments again (`||`), read from the final memory, so writes through pointers are compared.
-/

open GoFV.SSA GoFV.SSA.Sem

namespace GoFVTest.SemDiff

/-! ## Types the difftest supports -/

/-- `t` can be built, generated and printed (integers, floats, complex, `bool`, strings, slices, arrays,
structs, pointers, each at most 1 KB; `depth` bounds the recursion through pointers and
elements). -/
def supported (tabs : Tables) : Nat → TypeRef → Bool
  | 0, _ => true
  | d + 1, t =>
    match tabs.type? t with
    | none => false
    | some td =>
      -- values are built as text and bytes: keep them small (runtime's `traceBuf` is 64 KB)
      if (td.size.getD 4096) > 1024 then false else
      match td.kind, td.tail with
      | .INT8, _ | .INT16, _ | .INT32, _ | .INT64, _ | .INT, _ | .UINT8, _ | .UINT16, _
      | .UINT32, _ | .UINT64, _ | .UINT, _ | .UINTPTR, _ | .BOOL, _ | .STRING, _ => true
      | .FLOAT32, _ | .FLOAT64, _ | .COMPLEX64, _ | .COMPLEX128, _ => true
      | .SLICE, .elem e | .PTR, .elem e => supported tabs d e && (typeSize? tabs e).isSome
      | .ARRAY, .array e _ => supported tabs d e
      | .STRUCT, .struct fs => fs.all fun f => f.offset.isSome && supported tabs d f.type
      | _, _ => false

/-- Parameter and result types of `f`'s signature, if all are supported. -/
def signature (tabs : Tables) (f : Func) : Option (Array TypeRef × Array TypeRef) := do
  let d ← tabs.type? f.type
  match d.tail with
  | .func nrecv nparams nresults fields =>
    let ts := fields.map (·.type)
    if !ts.all (supported tabs 6) then none
    -- a generic shape instantiation's dictionary must be the right one, not a random pointer
    if fields.any (·.name == GoStr.ofString ".dict") then none
    let nin := nrecv + nparams
    if ts.size != nin + nresults then none
    else some (ts.extract 0 nin, ts.extract nin ts.size)
  | _ => none

def isFloat : TypeKind → Bool
  | .FLOAT32 | .FLOAT64 => true
  | _ => false

/-- A natural number written in hex (`0x…`) or decimal. -/
def parseNat (w : String) : Option Nat :=
  if w.startsWith "0x" then
    (w.drop 2).toString.foldl (fun acc c => acc.bind fun n =>
      if c.isDigit then some (16 * n + (c.toNat - '0'.toNat))
      else if 'a' ≤ c ∧ c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
      else none) (some 0)
  else w.toNat?

/-- `x` as `0x` and `2 * bytes` hex digits. -/
def hexBits (bytes : Nat) (x : Nat) : String :=
  let hex := "0123456789abcdef".toList
  "0x" ++ String.ofList ((List.range (2 * bytes)).reverse.map fun k => hex[x / 16 ^ k % 16]!)

def isSigned : TypeKind → Bool
  | .INT8 | .INT16 | .INT32 | .INT64 | .INT => true
  | _ => false

/-! ## Parsing values into memory -/

structure PState where
  s : Array Char
  i : Nat
  mem : Mem

abbrev PM := StateT PState (Except String)

def peek : PM (Option Char) := do let st ← get; return st.s[st.i]?
def advance (n : Nat := 1) : PM Unit := modify fun st => { st with i := st.i + n }
def eat (c : Char) : PM Bool := do
  if (← peek) == some c then advance; return true else return false
def expect (c : Char) : PM Unit := do
  if !(← eat c) then throw s!"expected {c} at {(← get).i}"
def lit (w : String) : PM Bool := do
  let st ← get
  let cs := w.toList
  if (List.range cs.length).all fun k => st.s[st.i + k]? == cs[k]? then
    advance cs.length; return true
  else return false
def word : PM String := do
  let mut out := ""
  for _ in [0:(← get).s.size] do
    match ← peek with
    | some c => if c == ',' || c == ']' || c == '}' then break else out := out.push c; advance
    | none => break
  return out

/-- A Go-quoted string literal at the cursor, as bytes. -/
def quoted : PM (Array UInt8) := do
  let st ← get
  if st.s[st.i]? != some '"' then throw "expected string"
  let mut j := st.i + 1
  for _ in [0:st.s.size] do
    match st.s[j]? with
    | some '\\' => j := j + 2
    | some '"' => break
    | some _ => j := j + 1
    | none => throw "unterminated string"
  let lit := String.ofList (st.s.extract st.i (j + 1)).toList
  set { st with i := j + 1 }
  match goUnquote lit with
  | some bs => return bs
  | none => throw s!"bad string {lit}"

def allocBytes (bs : Array Byte) : PM Ptr := do
  let st ← get
  let (p, m) := st.mem.allocHeap bs
  set { st with mem := m }
  return p

/-- Parse a list `e,e,…close` (the opening bracket consumed) with `elem`. -/
def listOf {α} (close : Char) (elem : PM α) : PM (Array α) := do
  if ← eat close then return #[]
  let mut out := #[]
  for _ in [0:(← get).s.size + 1] do
    out := out.push (← elem)
    if ← eat close then return out
    expect ','
  throw "list too long"

/-- The bytes of a value of type `t` written at the cursor. -/
def parseBytes (tabs : Tables) : Nat → TypeRef → PM (Array Byte)
  | 0, _ => throw "too deep"
  | d + 1, t => do
    let some td := tabs.type? t | throw s!"unknown type t{t}"
    let size := (typeSize? tabs t).getD 0
    match td.kind, td.tail with
    | .BOOL, _ =>
      match ← word with
      | "true" => return #[.b 1]
      | "false" => return #[.b 0]
      | w => throw s!"bad bool {w}"
    | .STRING, _ =>
      let bs ← quoted
      let p ← if bs.isEmpty then pure Ptr.null
        else allocBytes (bs.map fun x => .b (BitVec.ofNat 8 x.toNat))
      return ptrBytes p ++ intBytes 8 bs.size
    | .SLICE, .elem e =>
      if ← lit "nil" then return ptrBytes Ptr.null ++ intBytes 16 0
      expect '['
      let es ← listOf ']' (parseBytes tabs d e)
      let p ← allocBytes (es.foldl (· ++ ·) #[])
      return ptrBytes p ++ intBytes 8 es.size ++ intBytes 8 es.size
    | .ARRAY, .array e _ =>
      expect '['
      let es ← listOf ']' (parseBytes tabs d e)
      return es.foldl (· ++ ·) #[]
    | .STRUCT, .struct fs =>
      expect '{'
      let mut buf : Array Byte := Array.replicate size (.b 0)
      for h : k in [0:fs.size] do
        if k > 0 then expect ','
        let f := fs[k]
        buf := putBytes buf (f.offset.getD 0).toNat (← parseBytes tabs d f.type)
      expect '}'
      return buf
    | .PTR, .elem e =>
      if ← lit "nil" then return ptrBytes Ptr.null
      expect '&'
      return ptrBytes (← allocBytes (← parseBytes tabs d e))
    | .COMPLEX64, _ | .COMPLEX128, _ =>
      expect '{'
      let some re := parseNat (← word) | throw "bad complex"
      expect ','
      let some im := parseNat (← word) | throw "bad complex"
      expect '}'
      return intBytes (size / 2) re ++ intBytes (size / 2) im
    | .FLOAT32, _ | .FLOAT64, _ =>
      let w ← word
      let some n := parseNat w | throw s!"bad float {w}"
      return intBytes size n
    | k, _ =>
      let w ← word
      let some n := w.toInt? | throw s!"bad integer {w}"
      if isSigned k || k == .UINT8 || k == .UINT16 || k == .UINT32 || k == .UINT64 || k == .UINT
          || k == .UINTPTR then
        return intBytes size (BitVec.ofInt (8 * size) n).toNat
      else throw s!"unsupported type t{t}"

/-! ## Printing values from memory -/

/-- Go's `strconv.Quote` byte by byte: non-ASCII bytes as `\xHH` even inside valid UTF-8
(`quoteBytes` in `tools/semdiff/prog/main.go`). -/
def goQuote (bs : Array UInt8) : String := Id.run do
  let hex := "0123456789abcdef".toList
  let mut out := "\""
  for b in bs do
    let n := b.toNat
    out := match n with
      | 7 => out ++ "\\a" | 8 => out ++ "\\b" | 12 => out ++ "\\f" | 10 => out ++ "\\n"
      | 13 => out ++ "\\r" | 9 => out ++ "\\t" | 11 => out ++ "\\v" | 92 => out ++ "\\\\"
      | 34 => out ++ "\\\""
      | _ => if 32 ≤ n && n < 127 then out.push (Char.ofNat n)
        else out ++ "\\x" ++ String.ofList [hex[n / 16]!, hex[n % 16]!]
  return out ++ "\""

/-- The value of type `t` in `bs` at `off`, printed, reading what pointers point to in `m`. -/
def renderBytes (tabs : Tables) (m : Mem) : Nat → TypeRef → Array Byte → Nat → String
  | 0, _, _, _ => "<deep>"
  | d + 1, t, bs, off =>
    let ty := tabs.ty t
    match tabs.type? t with
    | none => "<?>"
    | some td =>
      let size := (typeSize? tabs t).getD 0
      match td.kind, td.tail, decode bs off ty with
      | .BOOL, _, .bool b => toString b
      | .STRING, _, .agg [w, .int _ n] =>
        if n.toNat == 0 then "\"\"" else
        match w.asPtrWord.bind (m.read · n.toNat) with
        | some cs => match cs.mapM (fun | .b x => some (UInt8.ofNat x.toNat) | _ => none) with
          | some u => goQuote u
          | none => "<poison string>"
        | none => "<bad string>"
      | .SLICE, .elem e, .agg [w, .int _ n, _] =>
        match w.asPtrWord with
        | none => "<bad slice>"
        | some p =>
        if p.isNil then "nil" else
        let es := (typeSize? tabs e).getD 0
        match m.read p (n.toNat * es) with
        | some ebs => "[" ++ ",".intercalate ((List.range n.toNat).map fun k =>
            renderBytes tabs m d e ebs (k * es)) ++ "]"
        | none => "<bad slice>"
      | .ARRAY, .array e n, _ =>
        let es := (typeSize? tabs e).getD 0
        "[" ++ ",".intercalate ((List.range n.toNat).map fun k =>
          renderBytes tabs m d e bs (off + k * es)) ++ "]"
      | .STRUCT, .struct fs, _ =>
        "{" ++ ",".intercalate (fs.toList.map fun f =>
          renderBytes tabs m d f.type bs (off + (f.offset.getD 0).toNat)) ++ "}"
      | .PTR, .elem e, w =>
        match w.asPtrWord with
        | none => s!"<{w.render}>"
        | some p =>
        if p.isNil then "nil" else
        let es := (typeSize? tabs e).getD 0
        match m.read p es with
        | some ebs => "&" ++ renderBytes tabs m d e ebs 0
        | none => "<bad pointer>"
      | .COMPLEX64, _, .agg [.int _ a, .int _ b] | .COMPLEX128, _, .agg [.int _ a, .int _ b] =>
        "{" ++ hexBits (size / 2) a.toNat ++ "," ++ hexBits (size / 2) b.toNat ++ "}"
      | k, _, .int _ x =>
        if isFloat k then hexBits size x.toNat
        else if isSigned k then toString x.toInt else toString x.toNat
      | _, _, v => if size == 0 then "<empty>" else s!"<{v.render}>"

/-! ## Loading exports and running calls -/

def ssaFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "ssa")).qsort (·.toString < ·.toString)
  else return #[p]

/-- A parsed export: each section's tables and function, the signature, the global image. -/
structure Loaded where
  sections : Array (String × Tables × Func × Ctx)
  /-- Each section's mode (`runCtxL`): lowered functions read registers, L1 sections fault. -/
  modes : Array LMode
  /-- The `runLoc` context of each allocated section (L2, from `regalloc` on). -/
  locs : Array (Option LocCtx)
  params : Array TypeRef
  results : Array TypeRef
  env : Env
  /-- The `runFrame` context of the last section, when the export has a `.prog` companion. -/
  frame : Option FrameCtx := none

/-- The frame layout of a `.prog` file (`semantics3.md` §5, `obj7.go` `preprocess`): `autosize`
from the asm section's TEXT, `framesize` and the argument size from prog0's TEXT,
`extrasize = autosize - framesize - 8` (0 when frameless), and the `FrameOffset` of each variable
of the frame section's `out` lines whose `name` definition links an SSA aux ref. -/
def progLayout (pf : GoFV.Asm.ProgFile) : FrameLayout :=
  let autosize := match pf.asm.progs[0]? with
    | some p => if p.as == .TEXT then p.to.offset else 0
    | none => 0
  let text0 := pf.prog0.progs.find? (·.as == .TEXT)
  let framesize := (text0.map (·.to.offset)).getD 0
  let argsize := match text0.map (·.to.val) with
    | some (.textSize n) => n
    | _ => 0
  let extrasize := if autosize == 0 then 0 else autosize - framesize - 8
  let defs := pf.frame.defs ++ pf.genin.defs ++ pf.prog0.defs ++ pf.asm.defs
  let auxOf : Std.HashMap Nat AuxRef := defs.foldl (fun m d => match d with
    | .name n nd => match nd.aux with
      | some a => m.insert n a
      | none => m
    | _ => m) {}
  let offsets := pf.frame.dclOut.toList.filterMap fun e => (auxOf[e.name]?).map (·, e.off)
  { autosize, extrasize, offsets, size := (autosize + 8 + argsize).toNat }

/-- The first section run as allocated code (`runLoc`, L2): `regalloc` assigns homes. -/
def locPass : String := "regalloc"

/-- The first section run as scheduled SSA (`runSched`'s context, L1). -/
def schedPass : String := "schedule"

def load (path : System.FilePath) : IO (Except String Loaded) := do
  let data ← IO.FS.readBinFile path
  match parseExport data with
  | .error e => return .error s!"{path}: {e}"
  | .ok e =>
    let mut tabs : Tables := {}
    let mut secs := #[]
    let mut modes := #[]
    let mut locs := #[]
    let mut sched := false
    let mut alloc := false
    for s in e.sections do
      tabs := tabs.addAll s.defs
      let pass := s.pass.toStringLossy
      if pass == schedPass then sched := true
      if pass == locPass then alloc := true
      let ctx := if sched then Ctx.makeSched tabs s.func else Ctx.makeL tabs s.func
      secs := secs.push (pass, tabs, s.func, ctx)
      modes := modes.push ⟨s.func.lowered, sched⟩
      locs := locs.push (if alloc then some (LocCtx.make tabs s.func) else none)
    match secs[0]? with
    | none => return .error s!"{path}: no sections"
    | some (_, t0, f0, _) =>
      match signature t0 f0 with
      | none => return .error s!"{path}: signature outside the difftest's types"
      | some (ps, rs) =>
        let pp := path.withExtension "prog"
        let pf? ← if ← pp.pathExists then
            pure (some (GoFV.Asm.parseProgFile (← IO.FS.readBinFile pp)))
          else pure none
        match pf? with
        | some (.error err) => return .error s!"{pp}: {err}"
        | _ =>
          let frame := match pf? with
            | some (.ok pf) =>
              (locs.back?.join).map (FrameCtx.ofLoc · (progLayout pf))
            | _ => none
          return .ok { sections := secs, modes, locs, params := ps, results := rs,
                       env := { Env.runtime with globals := globalImage e }, frame }

/-- Program functions of an export directory, for calls (`Env.withFuncs`): each file's
function by link symbol name (`<pkg>.<name>`), section 0, and the union of the files' global
images. -/
def loadProgram (dir : String) : IO (Std.HashMap String Ctx × List (String × Alloc)) := do
  let mut funcs : Std.HashMap String Ctx := {}
  let mut globals : Std.HashMap String Alloc := {}
  for path in ← ssaFiles dir do
    let .ok e := parseExportUntil "lower" (← IO.FS.readBinFile path) | continue
    let some s0 := e.sections[0]? | continue
    let tabs := e.tablesAt 0
    funcs := funcs.insert (e.pkg.toStringLossy ++ "." ++ e.name.toStringLossy) (Ctx.make tabs s0.func)
    for (k, a) in globalImage e do
      if !globals.contains k then globals := globals.insert k a
  return (funcs, globals.toList)

/-- Block entries per activation of a called program function. -/
def calleeFuel : Nat := 100000

/-- The environment of a program: the runtime contracts, the program's globals, and its
functions as callees nested at most 1000 deep. -/
def programEnv (dir : String) : IO Env := do
  let (funcs, globals) ← loadProgram dir
  return ({ Env.runtime with globals }).withFuncs (fun n => funcs[n]?) calleeFuel 1000

/-- Block entries per run against native results (the test programs loop at most a few
thousand times). -/
def fuel : Nat := 1000000

/-- Block entries per run in `corpus` mode: corpus functions may loop 10^5 times and more
(`test/gc1.go`); such runs end `outOfFuel` and count as not defined. -/
def corpusFuel : Nat := 20000

/-- The arguments of a call: their bytes and the memory holding what they point to. -/
def buildArgs (tabs : Tables) (params : Array TypeRef) (texts : List String) :
    Except String (Array (Array Byte) × Mem) := do
  if texts.length != params.size then throw s!"{texts.length} arguments for {params.size}"
  let mut mem : Mem := {}
  let mut out := #[]
  for (t, s) in params.toList.zip texts do
    match (parseBytes tabs 8 t).run { s := s.toList.toArray, i := 0, mem } with
    | .ok (bs, st) =>
      if st.i != st.s.size then throw s!"trailing input in {s}"
      mem := st.mem
      out := out.push bs
    | .error e => throw e
  return (out, mem)

/-- Run a call on section `k` with `run` (given the section's context, the arguments and the
memory) and print the outcome as the native harness does. -/
def runSectionWith (l : Loaded) (k : Nat) (texts : List String)
    (run : Ctx → List Val → Mem → Outcome) : String :=
  match l.sections[k]? with
  | none => "stuck: no section"
  | some (_, tabs, _, ctx) =>
    match buildArgs tabs l.params texts with
    | .error e => s!"stuck: bad arguments: {e}"
    | .ok (imgs, mem) =>
      let args := (imgs.zip l.params).toList.map fun (bs, t) => decode bs 0 (tabs.ty t)
      let out := run ctx args mem
      match out with
      | .returned rs m =>
        let rsT := (rs.zip l.results.toList).map fun (v, t) =>
          renderBytes tabs m 8 t (encode (tabs.ty t) v) 0
        let asT := (imgs.zip l.params).toList.map fun (bs, t) => renderBytes tabs m 8 t bs 0
        "\t".intercalate ("returned" :: rsT ++ "||" :: asT) ++
          (if rs.length == l.results.size then "" else s!"\t<{rs.length} results>")
      | .panicked e _ => "panicked " ++ e.message
      | .stuck msg => "stuck: " ++ msg
      | .outOfFuel => "outOfFuel"

/-- Run a call on section `k` and print the outcome as the native harness does. -/
def runSection (l : Loaded) (k : Nat) (texts : List String) (fuel : Nat := fuel) : String :=
  runSectionWith l k texts fun ctx args mem =>
    match l.locs[k]? with
    | some (some lc) => runCtxLoc l.env lc args mem fuel
    | _ => runCtxL (l.modes[k]?.getD ⟨false, false⟩) l.env ctx args mem fuel

/-- Run a call on the last section with `runFrame` (none without a `.prog` companion). -/
def runFrameSection (l : Loaded) (texts : List String) (fuel : Nat := fuel) : Option String :=
  l.frame.map fun fc =>
    runSectionWith l (l.sections.size - 1) texts fun _ args mem =>
      runCtxFrame l.env fc args mem fuel

/-! ## Random arguments -/

/-- splitmix64. -/
def nextRand (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

abbrev RM := StateM UInt64

def rand : RM Nat := do
  let (r, s) := nextRand (← get)
  set s
  return r.toNat

/-- A random integer of `n` bits: an edge value, a small value, or random bits. -/
def randInt (n : Nat) (signed : Bool) : RM String := do
  let r ← rand
  let r2 ← rand
  let edges : List Int :=
    if signed then [0, 1, -1, 2, -2, 7, -(2 ^ (n - 1)), 2 ^ (n - 1) - 1, -(2 ^ (n - 1)) + 1,
      2 ^ (n - 1) - 2, 2 ^ (n / 2), -(2 ^ (n / 2))]
    else [0, 1, 2, 3, 7, 2 ^ n - 1, 2 ^ n - 2, 2 ^ (n - 1), 2 ^ (n - 1) - 1, 2 ^ (n / 2)]
  let x : BitVec n :=
    match r % 10 with
    | 0 | 1 | 2 => BitVec.ofInt n (edges.getD (r2 % edges.length) 0)
    | 3 | 4 | 5 => BitVec.ofInt n ((r2 % 41 : Nat) - 20 : Int)
    | 6 => BitVec.ofNat n (r2 % 1000)
    | _ => BitVec.ofNat n r2
  return if signed then toString x.toInt else toString x.toNat

/-- A random float of `n` bits (32 or 64): an edge value (zeros, infinities, quiet and
signalling NaNs with payloads, subnormals, extremes, values at integer-conversion boundaries
and rounding ties), a small integer or half-integer, or random bits. -/
def randFloat (n : Nat) : RM String := do
  let r ← rand
  let r2 ← rand
  let (E, F) := if n == 32 then (8, 23) else (11, 52)
  let bias := 2 ^ (E - 1) - 1
  -- the bits of `±m · 2^e` for an exactly representable value (`m < 2^(F+1)`)
  let enc (neg : Bool) (m : Nat) (e : Int) : Nat := Id.run do
    if m == 0 then return if neg then 2 ^ (n - 1) else 0
    let lg := m.log2
    let be : Int := lg + e + bias
    let frac := (m * 2 ^ (F - lg)) % 2 ^ F
    return (if neg then 2 ^ (n - 1) else 0) + be.toNat * 2 ^ F + frac
  let ones := 2 ^ E - 1
  let edges : List Nat := [0, 2 ^ (n - 1), ones * 2 ^ F, 2 ^ (n - 1) + ones * 2 ^ F,
    ones * 2 ^ F + 2 ^ (F - 1), 2 ^ (n - 1) + ones * 2 ^ F + 2 ^ (F - 1) + 5,
    ones * 2 ^ F + 1, ones * 2 ^ F + 2 ^ (F - 2) + 3, 1, 2 ^ F - 1, 2 ^ F,
    (ones - 1) * 2 ^ F + 2 ^ F - 1, 2 ^ (n - 1) + 2 ^ F - 1,
    enc false 1 0, enc true 1 0, enc false 1 (-1), enc false 3 (-1), enc false 5 (-1),
    enc true 5 (-1), enc false 7 (-1), enc false 1 31, enc true 1 31, enc false (2 ^ 32 - 1) (-1),
    enc true (2 ^ 32 + 1) (-1), enc false 1 32, enc false 1 63, enc true 1 63, enc false 1 64,
    enc false (2 ^ (F + 1) - 1) (63 - (F : Int)), enc false 1 (F + 1), enc false 3 F,
    enc false 1 15, enc true 1 15, enc false 255 0, enc false 1 8, enc true 129 0]
  let x : Nat :=
    match r % 10 with
    | 0 | 1 | 2 | 3 => edges.getD (r2 % edges.length) 0
    | 4 | 5 => enc (r2 % 2 == 1) (r2 / 2 % 41) (if r2 / 128 % 2 == 0 then 0 else -1)
    | 6 => enc (r2 % 2 == 1) (r2 / 2 % 2 ^ (F + 1) + 1) ((r2 / 2 ^ 40 % 64 : Nat) - 32 - (F : Int))
    | _ => r2 % 2 ^ n
  return hexBits (n / 8) x

/-- A random value of type `t` (`d` bounds the depth; beyond it pointers and slices are nil). -/
def randVal (tabs : Tables) : Nat → TypeRef → RM String
  | 0, _ => pure "nil"
  | d + 1, t => do
    let some td := tabs.type? t | return "?"
    let size := (typeSize? tabs t).getD 0
    match td.kind, td.tail with
    | .BOOL, _ => return if (← rand) % 2 == 0 then "true" else "false"
    | .STRING, _ =>
      let r ← rand
      if r % 7 == 0 then return "\"abc\""
      let alphabet := "abcxyz 019,]{}\"\\".toList
      let n := (← rand) % 9
      let mut bs : Array UInt8 := #[]
      for _ in [0:n] do
        bs := bs.push (alphabet[(← rand) % alphabet.length]!).toNat.toUInt8
      return goQuote bs
    | .SLICE, .elem e =>
      if (← rand) % 10 == 0 || d ≤ 1 then return "nil"
      let n := (← rand) % 7
      let mut es := #[]
      for _ in [0:n] do es := es.push (← randVal tabs d e)
      return "[" ++ ",".intercalate es.toList ++ "]"
    | .ARRAY, .array e n =>
      let mut es := #[]
      for _ in [0:n.toNat] do es := es.push (← randVal tabs d e)
      return "[" ++ ",".intercalate es.toList ++ "]"
    | .STRUCT, .struct fs =>
      let mut es := #[]
      for f in fs do es := es.push (← randVal tabs d f.type)
      return "{" ++ ",".intercalate es.toList ++ "}"
    | .PTR, .elem e =>
      if (← rand) % 7 == 0 || d ≤ 2 then return "nil"
      return "&" ++ (← randVal tabs d e)
    | .FLOAT32, _ | .FLOAT64, _ => randFloat (8 * size)
    | .COMPLEX64, _ | .COMPLEX128, _ =>
      return "{" ++ (← randFloat (4 * size)) ++ "," ++ (← randFloat (4 * size)) ++ "}"
    | k, _ => randInt (8 * size) (isSigned k)

def randCalls (tabs : Tables) (params : Array TypeRef) (n : Nat) : RM (Array (List String)) := do
  let mut out := #[]
  for _ in [0:n] do
    let mut args := []
    for t in params do args := args ++ [← randVal tabs 6 t]
    out := out.push args
  return out

/-! ## Modes -/

def funcPath (dir : String) (name : String) : System.FilePath :=
  System.FilePath.mk dir / s!"{name},1.ssa"

def gen (dir : String) (n : Nat) (seed : Nat) (names : List String) : IO UInt32 := do
  let mut s : UInt64 := UInt64.ofNat seed
  for name in names do
    match ← load (funcPath dir name) with
    | .error e => IO.eprintln e; return 1
    | .ok l =>
      let tabs := l.sections[0]!.2.1
      let (calls, s') := (randCalls tabs l.params n).run s
      s := s'
      for c in calls do
        IO.println ("\t".intercalate (name :: c))
  return 0

def runMode (dir : String) (callsFile nativeFile : String) : IO UInt32 := do
  let calls := (← IO.FS.lines callsFile).filter (· ≠ "")
  let native := (← IO.FS.lines nativeFile).filter (· ≠ "")
  if calls.size != native.size then
    IO.eprintln s!"{calls.size} calls but {native.size} native results"
    return 1
  let env ← programEnv dir
  let mut cache : Std.HashMap String Loaded := {}
  let mut nIn := 0
  let mut agree0 := 0
  let mut agreeLast := 0
  let mut agreeAll := 0
  let mut sectionRuns := 0
  let mut bad := 0
  let mut outcomes : Std.HashMap String Nat := {}
  -- `runFrame` on the last section: runs, of them in functions with a slot home, agreements,
  -- mismatches, of them where the last section itself mismatches, functions with a layout problem
  let mut frameRuns := 0
  let mut frameSlotRuns := 0
  let mut frameAgree := 0
  let mut frameBad := 0
  let mut frameBadBase := 0
  let mut frameFuncs : Std.HashMap String Bool := {}
  let mut layoutBad := 0
  for h : i in [0:calls.size] do
    let call := calls[i]
    let toks := call.splitOn "\t"
    let name := toks.headD ""
    let l ← match cache[name]? with
      | some l => pure l
      | none =>
        match ← load (funcPath dir name) with
        | .error e => IO.eprintln e; return 1
        | .ok l => pure { l with env }
    if !cache.contains name then
      if let some fc := l.frame then
        let ps := FrameLayout.problems fc
        for p in ps do IO.println s!"FRAMELAYOUT {name}: {p}"
        if !ps.isEmpty then layoutBad := layoutBad + 1
        frameFuncs := frameFuncs.insert name
          (fc.lc.homes.any fun o => o matches some (.slot _))
    cache := cache.insert name l
    let want := match native[i]!.splitOn " -> " with
      | [c, o] => if c == call then o else s!"<native line {i} is for {c}>"
      | _ => s!"<bad native line {i}>"
    nIn := nIn + 1
    let kind := ((want.splitOn "\t").headD "").splitOn " " |>.headD ""
    outcomes := outcomes.insert kind (outcomes.getD kind 0 + 1)
    let mut allOk := true
    -- one mismatch line per call: the first differing section
    let mut allOk' := true
    let last := l.sections.size - 1
    for k in [0:l.sections.size] do
      let got := runSection l k toks.tail
      sectionRuns := sectionRuns + 1
      if got == want then
        if k == 0 then agree0 := agree0 + 1
        if k == last then agreeLast := agreeLast + 1
      else
        allOk := false
        if allOk' then
          IO.println s!"MISMATCH {call} section {k} ({l.sections[k]!.1}): lean {got}, native {want}"
          allOk' := false
        bad := bad + 1
    if allOk then agreeAll := agreeAll + 1
    if let some got := runFrameSection l toks.tail then
      frameRuns := frameRuns + 1
      if frameFuncs.getD name false then frameSlotRuns := frameSlotRuns + 1
      if got == want then frameAgree := frameAgree + 1
      else
        IO.println s!"MISMATCH {call} frame ({l.sections[last]!.1}): lean {got}, native {want}"
        frameBad := frameBad + 1
        if runSection l last toks.tail != want then frameBadBase := frameBadBase + 1
  let kinds := outcomes.toList.map (fun (k, n) => s!"{k} {n}")
  IO.println s!"sem-difftest: {cache.size} functions, {nIn} calls ({", ".intercalate kinds}), \
    {sectionRuns} section runs; native agrees with section 0 on {agree0}, with the last section \
    on {agreeLast}, with every section on {agreeAll}; {bad} section mismatches; frame runs \
    (runFrame on the last section): {frameRuns} in {frameFuncs.size} functions ({frameSlotRuns} \
    in functions with spill slots), native agrees with {frameAgree}, {frameBad} mismatches \
    ({frameBadBase} where the last section mismatches too), {layoutBad} functions with layout \
    problems"
  return if bad == 0 && frameBad == 0 && nIn > 0 then 0 else 1

structure CStats where
  files : Nat := 0
  eligible : Nat := 0
  calls : Nat := 0
  defined0 : Nat := 0
  definedFuncs : Nat := 0
  stuck0 : Nat := 0
  sectionRuns : Nat := 0
  agree : Nat := 0
  gaps : Nat := 0
  diffs : Nat := 0
  gapFuncs : Nat := 0
  outcomes : Std.HashMap String Nat := {}
  stuckMsgs : Std.HashMap String Nat := {}
  /-- First file and call per stuck reason. -/
  stuckEx : Std.HashMap String String := {}
  /-- Slowest files (ms). -/
  slow : Array (Nat × String) := #[]
  /-- Runs of the unscheduled lowered sections (`lower` … `layout`, L0), of the scheduled ones
  (`schedule` … `flagalloc`, L1) and of the allocated ones (`regalloc` …, L2), and how many agree
  with section 0. -/
  l0Runs : Nat := 0
  l0Agree : Nat := 0
  l1Runs : Nat := 0
  l1Agree : Nat := 0
  l2Runs : Nat := 0
  l2Agree : Nat := 0
  /-- Per pass name: gaps and differences of its sections. -/
  byPass : Std.HashMap String (Nat × Nat) := {}
  /-- Gap reasons (stuck messages of later sections), with a first example. -/
  gapMsgs : Std.HashMap String Nat := {}
  gapEx : Std.HashMap String String := {}
  /-- Differences of lowered sections whose function holds a fused multiply-add (`Contract`). -/
  contracted : Nat := 0

/-- The fused multiply-adds `lower` contracts `a ± x*y` into (the 12 `useFMA` rules,
`docs/plans/semantics2.md` §2.1). -/
def fusedOp (op : Op) : Bool :=
  [Op.ARM64FMADDS, .ARM64FMADDD, .ARM64FMSUBS, .ARM64FMSUBD, .ARM64FNMADDS, .ARM64FNMADDD,
    .ARM64FNMSUBS, .ARM64FNMSUBD].contains op

/-- `f` holds a fused multiply-add: its float results may differ from the unfused section 0's by
the rounding the Go spec lets an implementation omit. -/
def hasFused (f : Func) : Bool := f.valueTab.any fun o => (o.map (fusedOp ·.op)).getD false

/-- A stuck message without value/block IDs (for a histogram). -/
def stuckKey (msg : String) : String :=
  let isRef (w : String) : Bool :=
    let w := if w.endsWith ":" then (w.dropEnd 1).toString else w
    (w.startsWith "v" || w.startsWith "b") && w.length ≥ 2 && (w.drop 1).all Char.isDigit
  " ".intercalate (((msg.splitOn " ").filter (!isRef ·)).take 8)

def corpus (n seed : Nat) (dirs : List String) : IO UInt32 := do
  let mut st : CStats := {}
  let mut s : UInt64 := UInt64.ofNat seed
  for d in dirs do
    for path in ← ssaFiles d do
      st := { st with files := st.files + 1 }
      let t0 ← IO.monoMsNow
      let .ok l ← load path | continue
      st := { st with eligible := st.eligible + 1 }
      let (calls, s') := (randCalls l.sections[0]!.2.1 l.params n).run s
      s := s'
      let mut gapHere := false
      let mut definedHere := false
      for c in calls do
        st := { st with calls := st.calls + 1 }
        let r0 := runSection l 0 c corpusFuel
        let key := ((r0.splitOn "\t").headD "").splitOn " " |>.headD ""
        st := { st with outcomes := st.outcomes.insert key (st.outcomes.getD key 0 + 1) }
        if r0.startsWith "stuck" || r0 == "outOfFuel" then
          let k := stuckKey (r0.drop 7).toString
          st := { st with stuck0 := st.stuck0 + 1,
                          stuckMsgs := st.stuckMsgs.insert k (st.stuckMsgs.getD k 0 + 1),
                          stuckEx := if st.stuckEx.contains k then st.stuckEx
                            else st.stuckEx.insert k s!"{path} {c}" }
          continue
        st := { st with defined0 := st.defined0 + 1 }
        definedHere := true
        let mut form := 0
        for k in [1:l.sections.size] do
          let r := runSection l k c corpusFuel
          let pass := l.sections[k]!.1
          if pass == "lower" then form := 1
          if pass == schedPass then form := 2
          if pass == locPass then form := 3
          st := { st with sectionRuns := st.sectionRuns + 1 }
          if form == 1 then st := { st with l0Runs := st.l0Runs + 1 }
          if form == 2 then st := { st with l1Runs := st.l1Runs + 1 }
          if form == 3 then st := { st with l2Runs := st.l2Runs + 1 }
          if r == r0 then
            st := { st with agree := st.agree + 1 }
            if form == 1 then st := { st with l0Agree := st.l0Agree + 1 }
            if form == 2 then st := { st with l1Agree := st.l1Agree + 1 }
            if form == 3 then st := { st with l2Agree := st.l2Agree + 1 }
          else
            let (g, df) := st.byPass.getD pass (0, 0)
            if r.startsWith "stuck" then
              if !gapHere then
                IO.println s!"GAP {path} section {k} ({pass}) {c}: {r} (section 0: {r0})"
              let gk := pass ++ ": " ++ stuckKey (r.drop 7).toString
              st := { st with gaps := st.gaps + 1, byPass := st.byPass.insert pass (g + 1, df),
                              gapMsgs := st.gapMsgs.insert gk (st.gapMsgs.getD gk 0 + 1),
                              gapEx := if st.gapEx.contains gk then st.gapEx
                                else st.gapEx.insert gk s!"{path} {c}" }
              gapHere := true
            else if form ≥ 1 && hasFused l.sections[k]!.2.2.1 then
              if st.contracted < 10 then
                IO.println s!"CONTRACT {path} section {k} ({pass}) {c}: {r} (section 0: {r0})"
              st := { st with contracted := st.contracted + 1 }
            else
              if st.diffs < 30 then
                IO.println s!"DIFF {path} section {k} ({pass}) {c}: {r} (section 0: {r0})"
              st := { st with diffs := st.diffs + 1, byPass := st.byPass.insert pass (g, df + 1) }
      if gapHere then st := { st with gapFuncs := st.gapFuncs + 1 }
      if definedHere then st := { st with definedFuncs := st.definedFuncs + 1 }
      let dt := (← IO.monoMsNow) - t0
      if dt > 2000 then
        st := { st with slow := st.slow.push (dt, path.toString) }
        IO.eprintln s!"slow: {dt} ms {path}"
  let kinds := st.outcomes.toList.map (fun (k, n) => s!"{k} {n}")
  let top := (st.stuckMsgs.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 20
  IO.println s!"sem-difftest corpus: {st.files} files, {st.eligible} with supported signatures, \
    {st.calls} calls (section 0: {", ".intercalate kinds}); {st.defined0} calls defined at \
    section 0 (in {st.definedFuncs} functions), {st.sectionRuns} later-section runs of them: \
    {st.agree} agree, {st.diffs} differ, {st.contracted} differ by FMA contraction, {st.gaps} \
    stuck (gaps, in {st.gapFuncs} functions); \
    L0 sections (lower … layout): {st.l0Runs} runs, {st.l0Agree} agree; L1 sections \
    (schedule … flagalloc, runSched): {st.l1Runs} runs, {st.l1Agree} agree; L2 sections \
    (regalloc …, runLoc): {st.l2Runs} runs, {st.l2Agree} agree"
  IO.println "gaps and differences by pass:"
  for (p, (g, df)) in st.byPass.toList do IO.println s!"  {p}: {g} gaps, {df} differences"
  IO.println "gap reasons (top 30):"
  for (k, c) in ((st.gapMsgs.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 30) do
    IO.println s!"  {c} {k}    e.g. {st.gapEx.getD k ""}"
  IO.println "slowest files (ms):"
  for (ms, p) in ((st.slow.qsort (fun a b => a.1 > b.1)).toList.take 10) do
    IO.println s!"  {ms} {p}"
  IO.println "section-0 stuck reasons (top 20):"
  for (k, c) in top do IO.println s!"  {c} {k}    e.g. {st.stuckEx.getD k ""}"
  return if st.diffs == 0 then 0 else 1

/-- `trace <file> <section> <arg>...`: run one call on one section, printing every block entry
and the values the block computed (for debugging a stuck or differing run). -/
def trace (path : String) (k : Nat) (texts : List String) : IO UInt32 := do
  let .ok l ← load path | IO.eprintln "load failed"; return 1
  let dir := ((System.FilePath.mk path).parent.map (·.toString)).getD "."
  let l := { l with env := ← programEnv dir }
  let some (_, tabs, f, ctx) := l.sections[k]? | IO.eprintln "no section"; return 1
  let .ok (imgs, mem) := buildArgs tabs l.params texts | IO.eprintln "bad args"; return 1
  let args := (imgs.zip l.params).toList.map fun (bs, t) => decode bs 0 (tabs.ty t)
  let images := (args.toArray.zip ctx.paramTys).map fun (a, t) => encode t a
  let mut fr : Frame := { regs := Array.replicate f.valueTab.size none, args,
                          mem0 := frameMem l.env ctx images mem, images }
  let mut bid := f.entry
  let mut i := 0
  for _ in [0:200] do
    let some b := f.block? bid | IO.println s!"b{bid} missing"; return 1
    IO.println s!"enter b{bid} from edge {i}"
    match enterBlockL (l.modes[k]?.getD ⟨false, false⟩) l.env ctx fr b i with
    | .stuck msg => IO.println s!"  stuck: {msg}"; return 0
    | .panic e _ => IO.println s!"  panicked {e.message}"; return 0
    | .ok fr' =>
      fr := fr'
      for vid in b.values do
        let op := ((f.value? vid).map (·.op.name)).getD "?"
        IO.println s!"  v{vid} {op} = {((fr.regs[vid]?).join.map Val.render).getD "-"}"
      match stepTermL fr b with
      | .ok (.goto e) => bid := e.b; i := e.i
      | .ok (.ret rs _) => IO.println s!"return {rs.map Val.render}"; return 0
      | .stuck msg => IO.println s!"  terminator stuck: {msg}"; return 0
      | .panic e _ => IO.println s!"  panicked {e.message}"; return 0
  return 0

/-- The `sem-difftest` command line (`GoFVTest/SemDiffMain.lean` is the executable root: a module
defining `main` cannot be imported with the others, `scripts/axioms-audit.sh`). -/
def run (args : List String) : IO UInt32 := do
  match args with
  | "gen" :: dir :: n :: seed :: names =>
    gen dir n.toNat! seed.toNat! names
  | ["run", dir, calls, native] => runMode dir calls native
  | "corpus" :: n :: seed :: dirs => corpus n.toNat! seed.toNat! dirs
  | "trace" :: file :: k :: texts => trace file k.toNat! texts
  | _ =>
    IO.eprintln "usage: sem-difftest gen <dir> <n> <seed> <func>... | run <dir> <calls> <native> | corpus <n> <seed> <dir>..."
    return 2

end GoFVTest.SemDiff
