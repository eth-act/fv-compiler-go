import GoFV.Asm.Parse
import GoFV.SSA.Sem.RunProg
import Std.Data.HashMap

open scoped GoFV.SSA.Sem.Fixed

/-!
# `arm64-decode`: the Prog semantics against the machine on the asm sections (issue #552)

`docs/plans/semantics3.md` §3 (a), (c), §7. For every `gofv-prog` file under the given
directories, the asm section's text bytes are cut at the Progs' PCs and every Prog's words are
decoded with `GoFV.Arm64.decode`.

**Per Prog.** A Prog **matches** when its words decode and executing them with `GoFV.Arm64.step`
from a random state ends in the state `GoFV.Arm64.progStep` gives (the effect `progEffect` of
`GoFV/SSA/Sem/RunProg.lean`, in Go's assembly-language operand conventions): every register,
`SP`, the vector registers, the flags, the bytes of the Prog's stores and the next PC agree,
except `R27` (REGTMP, the assembler's scratch) unless the Prog names it, as in `progSpec`. This
checks the decoder and the instruction semantics
against the Progs the assembler encoded, including multi-word expansions (constants, large
offsets, literal pools, `REM`), without modelling the assembler's choices.

**Per block.** The asm Prog list is cut into basic blocks (leaders: the first Prog, branch and
jump-table targets, the Prog after a branch, `CALL`, `RET` or `JMP`; a block ends at those or
before a leader). From 3 random states at the block's first address, `runProg` over the block's
Progs and `runMach` over the block's words run to the block's exit (a PC outside the block,
caught by a hook that ends the run; for a block that branches back to its own leader, the
leader after one pass); the final states must agree as above (`R27` never compared: a Prog that
does not name it may leave anything there), the stored bytes on every store the Prog run made.
Blocks with `WORD`/`DWORD` (literal pools, jump tables) or without code are not run.

The text is placed at `BASE`; relocations are applied as the linker would (`R_CALLARM64`,
`R_ADDRARM64`, `R_ARM64_PCREL_LDST{8,16,32,64}`) with symbol `y<n>` at `symAddr n`, the same
layout as the `GoFV.Arm64.Link` the Prog semantics gets, and the memory outside the text is a
fixed pseudo-random byte pattern. Pseudo-ops (`TEXT`, `FUNCDATA`, `PCDATA`, `NOP`) must cover no
bytes; `WORD`/`DWORD` must be their constant; the words after the last Prog must be zero
(alignment padding, `UDF #0`).

usage: `arm64-decode [--words FILE] [--no-blocks] <dir|file>...`: prints per mismatch class
(blocks: the last opcode and reason; Progs: opcode, optab entry, reason) the number of blocks or
Progs and an example, then totals (the per-Prog totals last). `--words` writes the distinct words
of the text bytes with their counts (input of `arm64-cosim`); `--no-blocks` skips the per-block
check. Exit status 1 if a Prog or a block does not match.
-/

open GoFV.Asm GoFV.Arm64 GoFV.Arm64.ProgOp

namespace GoFVTest.Arm64Decode

def BASE : BitVec 64 := 0x10000000

/-- Where symbol `y<n>` is linked: within `BL`'s ±128 MiB of the text, 256-byte aligned. -/
def symAddr (n : Nat) : BitVec 64 := 0x14000000 + BitVec.ofNat 64 (n * 0x100)

/-- The background memory: a fixed byte pattern. -/
def pattern (a : BitVec 64) : BitVec 8 :=
  let x := a.toNat
  BitVec.ofNat 8 ((x * 2654435761 + x / 256 * 40503 + 17) / 4096)

/-! ## Relocations (as the linker applies them) -/

def getW (t : ByteArray) (o : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((t[o]!).toNat + (t[o+1]!).toNat * 256 + (t[o+2]!).toNat * 65536 +
    (t[o+3]!).toNat * 16777216)

def putW (t : ByteArray) (o : Nat) (w : BitVec 32) : ByteArray := Id.run do
  let mut t := t
  for j in [0:4] do t := t.set! (o + j) (w.toNat / 256 ^ j % 256).toUInt8
  t

def setBits (w : BitVec 32) (lo len : Nat) (v : Nat) : BitVec 32 :=
  let m : BitVec 32 := BitVec.ofNat 32 ((2 ^ len - 1) * 2 ^ lo)
  (w &&& ~~~m) ||| BitVec.ofNat 32 ((v % 2 ^ len) * 2 ^ lo)

/-- Patch the text with the relocations the decoder check understands. -/
def applyRelocs (text : ByteArray) (rs : Array Reloc) : ByteArray := Id.run do
  let mut t := text
  for r in rs do
    let o := r.off.toNat
    match r.sym with
    | none => pure ()
    | some n =>
      let target := symAddr n + BitVec.ofInt 64 r.add
      let pc := BASE + BitVec.ofNat 64 o
      let adrp (w : BitVec 32) : BitVec 32 :=
        let pages := ((target >>> 12) - (pc >>> 12)).toNat
        setBits (setBits w 29 2 pages) 5 19 (pages / 4)
      -- `RelocType(-32759)` is `R_WEAK | R_CALLARM64` (`weakenGlobalMapInitRelocs`): the linker
      -- patches it like `R_CALLARM64` when the target is live
      if (r.type == "R_CALLARM64" || r.type == "RelocType(-32759)") && o + 4 ≤ t.size then
        t := putW t o (setBits (getW t o) 0 26 ((target - pc) >>> 2).toNat)
      else if r.type == "R_ADDRARM64" && o + 8 ≤ t.size then
        t := putW t o (adrp (getW t o))
        t := putW t (o + 4) (setBits (getW t (o + 4)) 10 12 (target.toNat % 4096))
      else if r.type.startsWith "R_ARM64_PCREL_LDST" && o + 8 ≤ t.size then
        let sc := match dropS r.type 18 with
          | "8" => 0 | "16" => 1 | "32" => 2 | "64" => 3 | _ => 0
        t := putW t o (adrp (getW t o))
        t := putW t (o + 4) (setBits (getW t (o + 4)) 10 12 (target.toNat % 4096 / 2 ^ sc))
  t

/-! ## Random states -/

def mix (x : UInt64) : UInt64 :=
  let x := x ^^^ (x >>> 33)
  let x := x * 0xff51afd7ed558ccd
  let x := x ^^^ (x >>> 33)
  let x := x * 0xc4ceb9fe1a85ec53
  x ^^^ (x >>> 33)

def randState (seed : UInt64) (text : ByteArray) (pc : BitVec 64) : MState :=
  let r (k : Nat) : BitVec 64 := BitVec.ofNat 64 (mix (seed + k.toUInt64 * 0x9E3779B97F4A7C15)).toNat
  -- registers with small low bits half of the time, so shift amounts and bit numbers vary; never
  -- below 4096, so that accesses through them do not fault in the nil page
  let rx (k : Nat) : BitVec 64 := if (r (k + 1000)).getLsbD 0 then r k else 0x10000 + (r k &&& 0xFF)
  { x := fun i => rx i.toNat
    sp := 0x7FFF00000000 + (r 40 &&& 0xFFFF0)
    v := fun i => ((r (64 + 2 * i.toNat)).setWidth 128 <<< 64) ||| (r (65 + 2 * i.toNat)).setWidth 128
    nzcv := GoFV.SSA.Sem.Flags.ofNZCV ((r 41).toNat % 16)
    pc
    mem := fun a =>
      let d := a - BASE
      if d.toNat < text.size then BitVec.ofNat 8 (text[d.toNat]!).toNat else pattern a }

/-! ## Comparing states -/

/-- Compare the machine state `s` (after the words) with the Prog-level state `t`: every `X`
(but `R27` when `tmpFree`), `SP`, the vector registers, the flags, the bytes of `stores`, the
PC. -/
def diffState (s t : MState) (stores : List (BitVec 64 × Nat)) (tmpFree : Bool) :
    Option String := Id.run do
  for k in [0:31] do
    if k == 27 && tmpFree then continue
    if s.x (BitVec.ofNat 5 k) != t.x (BitVec.ofNat 5 k) then return some s!"R{k}"
  if s.sp != t.sp then return some "RSP"
  for k in [0:32] do
    if s.v (BitVec.ofNat 5 k) != t.v (BitVec.ofNat 5 k) then return some s!"V{k}"
  if s.nzcv != t.nzcv then return some "flags"
  for (a, n) in stores do
    if readMem s.mem a n != readMem t.mem a n then return some "store"
  if s.pc != t.pc then return some "pc"
  none

/-- The stores of an effect: address and size. -/
def storeSpans (e : Eff) : List (BitVec 64 × Nat) := e.stores.map fun (a, n, _) => (a, n)

structure Stats where
  progs : Nat := 0
  code : Nat := 0
  matched : Nat := 0
  classes : Std.HashMap String (Nat × String) := {}
  words : Std.HashMap UInt32 Nat := {}
  files : Nat := 0
  bad : Nat := 0
  /-- Blocks cut, run, with data words, without code. -/
  blocks : Nat := 0
  bRun : Nat := 0
  bData : Nat := 0
  bNoCode : Nat := 0
  /-- Blocks run that branch back to their leader. -/
  bLoops : Nat := 0
  bMatched : Nat := 0
  bClasses : Std.HashMap String (Nat × String) := {}
  bBad : Nat := 0

def bump (m : Std.HashMap String (Nat × String)) (cls ex : String) :
    Std.HashMap String (Nat × String) :=
  m.alter cls fun e => some ((e.map (·.1)).getD 0 + 1, (e.map (·.2)).getD ex)

def Stats.fail (st : Stats) (cls ex : String) : Stats :=
  { st with classes := bump st.classes cls ex, bad := st.bad + 1 }

def Stats.bfail (st : Stats) (cls ex : String) : Stats :=
  { st with bClasses := bump st.bClasses cls ex, bBad := st.bBad + 1 }

def pseudo : List String := ["TEXT", "FUNCDATA", "PCDATA", "NOP"]

/-! ## Checking the blocks -/

/-- The hook of the block runs: every PC outside the block ends the run with its state. -/
def exitHook : Hooks := ⟨fun s => some (.panicked (.runtime "block exit") s)⟩

/-- A Prog after which a new block starts. -/
def isTerm (p : Prog) : Bool :=
  p.to.type == .BRANCH || p.as == .RET || p.as == .JMP || p.as == .CALL

/-- The basic blocks of a Prog list as index ranges `[start, stop)`. -/
def cutBlocks (ps : Array Prog) (jumpTargets : Array Nat) : Array (Nat × Nat) := Id.run do
  let idx : Std.HashMap Nat Nat :=
    (ps.foldl (init := (({} : Std.HashMap Nat Nat), 0)) fun (m, i) p => (m.insert p.id i, i + 1)).1
  let mut lead : Array Bool := Array.replicate (ps.size + 1) false
  lead := lead.set! 0 true
  for i in [0:ps.size] do
    let p := ps[i]!
    if p.to.type == .BRANCH then
      if let .target id := p.to.val then
        if let some j := idx.get? id then lead := lead.set! j true
    if isTerm p then lead := lead.set! (i + 1) true
  for id in jumpTargets do
    if let some j := idx.get? id then lead := lead.set! j true
  let mut out := #[]
  let mut start := 0
  for i in [1:ps.size + 1] do
    if i == ps.size || lead[i]! then
      out := out.push (start, i)
      start := i
  out

/-- The Prog side of a block run: `runProg` from `s0`; for a block branching back to its
leader, one `progStep` and then `runProg` returning at the leader. -/
def progSide (L : Link) (bl : List Prog) (lead : BitVec 64) (selfLoop : Bool) (fuel : Nat)
    (s0 : MState) : MOutcome :=
  if !selfLoop then runProg exitHook L bl 0 fuel s0 else
  match progAt? L bl s0.pc with
  | none => .stuck "no Prog at the leader"
  | some p =>
    match progStep L p s0 with
    | .ok s1 => runProg exitHook L bl lead fuel s1
    | .error (.nilPage _) => .panicked .nilDeref s0
    | .error (.stuck m) => .stuck m

/-- The machine side: `runMach` over the block's words from `s0`; for a block branching back to
its leader, the words of its first Prog (`firstSize` bytes) and then `runMach` returning at the
leader. -/
def machSide (code : Code) (lead : BitVec 64) (firstSize : Nat) (selfLoop : Bool) (fuel : Nat)
    (s0 : MState) : MOutcome :=
  let rec go : Nat → MState → MOutcome
    | 0, s => runMach exitHook code lead fuel s
    | k + 1, s =>
      if (s.pc - lead).toNat < firstSize then
        match step code s with
        | .ok s' => go k s'
        | .error f => .ofFault s f
      else runMach exitHook code lead fuel s
  if !selfLoop then runMach exitHook code 0 fuel s0 else go (firstSize / 4) s0

/-- The stores of the Prog run of `progSide`, replayed (`stop`: the PC it returns at). -/
def traceStores (L : Link) (bl : List Prog) (stop : BitVec 64) :
    Bool → Nat → MState → List (BitVec 64 × Nat) → List (BitVec 64 × Nat)
  | _, 0, _, acc => acc
  | first, n + 1, s, acc =>
    if !first && s.pc == stop then acc else
    match progAt? L bl s.pc with
    | none => acc
    | some p =>
      let acc := if p.isSkip then acc else match progEffect ⟨L, s, p⟩ with
        | .ok e => acc ++ storeSpans e
        | .error _ => acc
      match progStep L p s with
      | .ok s' => traceStores L bl stop false n s' acc
      | .error _ => acc

def outKind : MOutcome → String
  | .returned _ => "returned"
  | .panicked (.runtime "block exit") _ => "exit"
  | .panicked .nilDeref _ => "nil dereference"
  | .panicked _ _ => "panic"
  | .stuck _ => "stuck"
  | .outOfFuel => "out of fuel"

def outState : MOutcome → Option MState
  | .returned s => some s
  | .panicked _ s => some s
  | _ => none

def outMsg : MOutcome → String
  | .stuck m => s!" ({m})"
  | _ => ""

/-- Run every block of the asm Prog list (`nexts[i]`: the offset Prog `i` falls through to). -/
def checkBlocks (path : System.FilePath) (st : Stats) (L : Link) (ps : Array Prog)
    (nexts : Array Int) (linked : ByteArray) (jumpTargets : Array Nat) : Stats := Id.run do
  let mut st := st
  let sizeOf (k : Nat) : Nat := (nexts[k]! - ps[k]!.pc).toNat
  for (i, j) in cutBlocks ps jumpTargets do
    st := { st with blocks := st.blocks + 1 }
    let ks := (List.range (j - i)).map (· + i)
    if ks.any fun k => ps[k]!.as.name == "WORD" || ps[k]!.as.name == "DWORD" then
      st := { st with bData := st.bData + 1 }
      continue
    let some k1 := ks.find? (sizeOf · != 0)
      | do st := { st with bNoCode := st.bNoCode + 1 }; continue
    st := { st with bRun := st.bRun + 1 }
    let bl := ks.map (ps[·]!)
    let lo := ps[i]!.pc.toNat
    let hi := nexts[j - 1]!.toNat
    let lead := BASE + BitVec.ofNat 64 lo
    let code : Code := fun pc =>
      let d := (pc - BASE).toNat
      if lo ≤ d && d < hi && d % 4 == 0 && d + 4 ≤ linked.size then some (getW linked d) else none
    let q := ps[j - 1]!
    let selfLoop := q.to.type == .BRANCH && match q.to.val with
      | .target id => L.addr id == some lead
      | _ => false
    if selfLoop then st := { st with bLoops := st.bLoops + 1 }
    let lastCode := ((ks.filter (sizeOf · != 0)).getLast?.map (ps[·]!.as.name)).getD "?"
    let mut err : Option String := none
    for t in [0:3] do
      let s0 := randState (UInt64.ofNat (ps[i]!.id * 7919 + t * 104729 + st.files + 1000003))
        linked lead
      let rp := progSide L bl lead selfLoop (bl.length + 2) s0
      let rm := machSide code lead (sizeOf k1) selfLoop ((hi - lo) / 4 + 2) s0
      match outState rp, outState rm with
      | some sp, some sm =>
        if outKind rp != outKind rm then
          err := some s!"outcome: Progs {outKind rp}, words {outKind rm}"; break
        let stores := traceStores L bl (if selfLoop then lead else 0) true (bl.length + 2) s0 []
        if let some d := diffState sm sp stores true then
          err := some s!"differs in {d}"; break
      | _, _ =>
        err := some s!"outcome: Progs {outKind rp}{outMsg rp}, words {outKind rm}{outMsg rm}"
        break
    match err with
    | none => st := { st with bMatched := st.bMatched + 1 }
    | some why => st := st.bfail s!"block ending {lastCode}: {why}" s!"{path} @{ps[i]!.id}"
  return st

/-! ## Checking a file -/

def checkFile (path : System.FilePath) (st : Stats) (collect blocks : Bool) : IO Stats := do
  let data ← IO.FS.readBinFile path
  match parseProgFile data with
  | .error e => return st.fail "parse error" s!"{path}: {e}"
  | .ok f =>
    let a := f.asm
    let text := a.text
    let mut st := { st with files := st.files + 1 }
    if collect then
      let mut ws := st.words
      for k in [0:text.size / 4] do
        ws := ws.alter (getW text (4 * k)).toNat.toUInt32 (some <| ·.getD 0 + 1)
      st := { st with words := ws }
    let linked := applyRelocs text a.relocs
    let ps := a.progs
    -- the offset each Prog falls through to: its successor's PC; the last Prog up to the padding
    let nexts : Array Int := (List.range ps.size).toArray.map fun i =>
      let p := ps[i]!
      if h : i + 1 < ps.size then ps[i+1].pc else
        if p.as.name == "DWORD" then p.pc + 8 else if pseudo.contains p.as.name then p.pc else p.pc + 4
    let pcs : Std.HashMap Nat Int := ps.foldl (fun m p => m.insert p.id p.pc) {}
    let nextOf : Std.HashMap Nat Int :=
      (List.range ps.size).foldl (fun m i => m.insert ps[i]!.id nexts[i]!) {}
    let autosize := match ps[0]? with
      | some p => if p.as == .TEXT then p.to.offset else 0
      | none => 0
    let pre := match f.prog0.progs.find? (·.as == .TEXT) with
      | some p => p.to.offset
      | none => 0
    -- `preprocess`: autosize = frame size + 8 (saved LR) + extrasize (`obj7.go`), and `span7`
    -- drops the packed extrasize from the asm section's TEXT
    let extrasize := if autosize == 0 then 0 else autosize - pre - 8
    -- the layout `Link.ofProgs … ps.toList (·.pc) …` describes, with hash maps for the lookups
    let L : Link :=
      { sym := symAddr, text := BASE, off := pcs.get?, next := nextOf.get?, autosize, extrasize }
    let code : Code := fun pc =>
      let d := pc - BASE
      if d.toNat % 4 == 0 && d.toNat + 4 ≤ linked.size then some (getW linked d.toNat) else none
    let mut lastEnd : Nat := 0
    for i in [0:ps.size] do
      let p := ps[i]!
      let size := (nexts[i]! - p.pc).toNat
      st := { st with progs := st.progs + 1 }
      let key := s!"{p.as.name} optab {p.optab}"
      if pseudo.contains p.as.name then
        if size != 0 then st := st.fail s!"{key}: pseudo-op with code" s!"{path} @{p.id}"
        continue
      if size == 0 then
        st := st.fail s!"{key}: no code" s!"{path} @{p.id}"
        continue
      st := { st with code := st.code + 1 }
      lastEnd := p.pc.toNat + size
      if p.as.name == "WORD" || p.as.name == "DWORD" then
        let n := if p.as.name == "WORD" then 4 else 8
        let v := (List.range n).foldl (fun acc j => acc + (text[p.pc.toNat + j]!).toNat * 256 ^ j) 0
        if size == n && v == p.to.offset.toNat % 2 ^ (8 * n) then st := { st with matched := st.matched + 1 }
        else st := st.fail s!"{key}: data word" s!"{path} @{p.id}"
        continue
      -- decode every word
      let mut undec := none
      for k in [0:size / 4] do
        if (decode (getW linked (p.pc.toNat + 4 * k))).isNone then
          undec := some (getW linked (p.pc.toNat + 4 * k))
      if let some w := undec then
        st := st.fail s!"{key}: undecoded word" s!"{path} @{p.id} {w.toHex}"
        continue
      -- execute from three random states and compare with `progStep`
      let pc0 := BASE + BitVec.ofInt 64 p.pc
      let mut err : Option String := none
      for t in [0:3] do
        let s0 := randState (UInt64.ofNat (p.id * 7919 + t * 104729 + st.files)) linked pc0
        match progEffect ⟨L, s0, p⟩, progStep L p s0 with
        | .error why, _ => err := some why; break
        | _, .error (.stuck why) => err := some why; break
        | _, .error (.nilPage _) => err := some "Prog: nil page"; break
        | .ok e, .ok t =>
          let steps := if e.pc.isSome then 1 else size / 4
          match run code steps s0 with
          | .error flt =>
            err := some (match flt with
              | .nilPage _ => "fault: nil page" | .undefined _ => "fault: undefined"
              | .noCode _ => "fault: no code"); break
          | .ok s =>
            if let some d := diffState s t (storeSpans e) (!p.namesX 27) then
              err := some s!"differs in {d}"; break
      match err with
      | none => st := { st with matched := st.matched + 1 }
      | some why => st := st.fail s!"{key}: {why}" s!"{path} @{p.id}"
    -- padding after the last Prog
    let mut pad := true
    for k in [lastEnd:text.size] do
      if text[k]! != 0 then pad := false
    if !pad then st := st.fail "padding: nonzero bytes after the last Prog" s!"{path}"
    if blocks then
      st := checkBlocks path st L ps nexts linked (a.fn.jumpTables.flatMap (·.2))
    return st

def progFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "prog")).qsort (·.toString < ·.toString)
  else return #[p]

def printClasses (m : Std.HashMap String (Nat × String)) : IO Nat := do
  let rows := m.toArray.qsort fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.1 < b.1)
  for (k, (n, ex)) in rows do IO.println s!"{n} {k} (e.g. {ex})"
  return rows.size

def main (args : List String) : IO UInt32 := do
  let rec opts : List String → Option String × Bool × List String
    | "--words" :: f :: rest => let (_, b, r) := opts rest; (some f, b, r)
    | "--no-blocks" :: rest => let (w, _, r) := opts rest; (w, false, r)
    | rest => (none, true, rest)
  let (wordsOut, blocks, paths) := opts args
  if paths.isEmpty then
    IO.eprintln "usage: arm64-decode [--words FILE] [--no-blocks] <dir|file>..."
    return 2
  let mut st : Stats := {}
  for a in paths do
    for f in ← progFiles a do
      st ← checkFile f st wordsOut.isSome blocks
  if blocks then
    let n ← printClasses st.bClasses
    IO.println s!"arm64-decode blocks: {st.blocks} blocks, {st.bRun} run ({st.bLoops} branching \
      back to their leader; {st.bData} with data words and {st.bNoCode} without code not run), \
      {st.bMatched} match, {st.bBad} do not ({n} classes)"
  let n ← printClasses st.classes
  IO.println s!"arm64-decode: {st.files} files, {st.progs} asm Progs, {st.code} with code, \
    {st.matched} match, {st.bad} do not ({n} classes)"
  if let some out := wordsOut then
    let ws := st.words.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
    let mut s := ""
    for (w, n) in ws do
      s := s ++ s!"{(BitVec.ofNat 32 w.toNat).toHex} {n}\n"
    IO.FS.writeFile out s
  return if st.bad == 0 && st.bBad == 0 then 0 else 1

end GoFVTest.Arm64Decode

def main (args : List String) : IO UInt32 := GoFVTest.Arm64Decode.main args
