import GoFV.Arm64.Exec
import Std.Data.HashMap

/-!
# `arm64-cosim`: co-simulation of `GoFV.Arm64` against qemu (issue #552)

`docs/plans/semantics3.md` §3 (a). Two modes, driven by `scripts/arm64-cosim.sh`:

- `gen <words> <n> <min> <fuzz> <seed> <cases>`: for every word of `<words>` (lines `<hex word>
  <count>`, the distinct words of the corpus' asm sections, written by `arm64-decode --words`)
  and `fuzz` random words, that `decode` accepts, write `n` cases (and at least `min` per
  `Insn.form`) to `<cases>` in the binary protocol of `tools/arm64cosim/main.go`:
  the word (patched where the harness needs it, below), a random machine state with edge-value
  bias and a random 256-byte memory window.
- `check <words> <n> <min> <fuzz> <seed> <results>`: regenerate the same cases, run each through
  `GoFV.Arm64.step` and compare with the native results (`tools/arm64cosim` under
  `qemu-aarch64-static`): X0–X30, SP, NZCV, V0–V31, the exit (fall through or the taken
  landing) and the window bytes. Prints coverage per `Insn.form` (words, cases, mismatches),
  the forms of the corpus not co-simulated and why, and the first mismatches. Exit status 1 on a
  mismatch.

What the generator adapts so that a corpus word can run in the harness (the harness only
provides the window `[WIN, WIN + 256)` as data memory and two landing addresses):

- loads/stores: the base register is set so that the access lands in the window (16-byte
  aligned target; for an `SP` base, `SP` itself 16-byte aligned), an index register to a small
  offset; forms whose index register is the base, and write-back forms whose base is the
  transfer register (CONSTRAINED UNPREDICTABLE; Go never emits them), are skipped;
- `CAS`: in half the cases the compared register is set to the memory value;
- `STXR`/`STLXR`: preceded by an `LDAXR` of the same address into a register the store does not
  use, since qemu, unlike the single-core model, fails an exclusive store without a monitor;
- branches: the offset is patched to reach the taken landing; `BR`/`BLR`/`RET` get the landing
  in their register (index 31, XZR, is skipped);
- `LDR` (literal): the offset is patched to 0, so it loads its own word (and the following
  `B exit0` for 8 bytes), which the Lean memory holds too;
- `BRK`/`UDF` trap and are not run (`exec` gives `Fault.undefined` by definition);
- CONSTRAINED UNPREDICTABLE shapes the random words can have and Go never emits are skipped:
  a pair load into one register, an exclusive store whose status register is its transfer or
  base register; a 16-byte literal load reads beyond the code bytes the Lean side knows.

The random words (`fuzz`) cover the encodings `decode` accepts beyond the corpus' words (other
registers, immediates, sizes and the classes' remaining opcodes), so the whole domain of
`decode` is co-simulated, not only what the corpus happens to contain.
-/

open GoFV.Arm64
open GoFV.SSA.Sem (Flags)

namespace GoFVTest.Arm64Cosim

/-! ## Harness layout (`tools/arm64cosim/main.go`) -/

def CODE : BitVec 64 := 0x40000000
def TEST : BitVec 64 := 0x40001000
def TAKEN : BitVec 64 := 0x40002000
def EXIT0 : BitVec 64 := 0x40003000
def WIN : BitVec 64 := 0x50000800
def WINSIZE : Nat := 256

/-! ## Random numbers -/

structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let x := g.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x, ⟨x⟩)

def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (x.toNat % n, g)

def edgeInts : Array UInt64 := #[0, 1, 2, 0xFFFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF,
  0x8000000000000000, 0xFFFFFFFF, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF80000000, 0x100000000,
  0xFF, 0xFFFF, 0x8000, 0x80, 63, 64, 31, 32]

/-- A random register value: edge values, small values, 32-bit values, full random. -/
def Rng.reg (g : Rng) : UInt64 × Rng :=
  let (k, g) := g.below 8
  match k with
  | 0 => let (i, g) := g.below edgeInts.size; (edgeInts[i]!, g)
  | 1 => let (x, g) := g.below 70; (x.toUInt64, g)
  | 2 => let (x, g) := g.next; (x &&& 0xFFFFFFFF, g)
  | 3 => let (x, g) := g.next; (0 - (x &&& 0xFF), g)
  | _ => g.next

def edgeF64 : Array UInt64 := #[0, 0x8000000000000000, 0x3FF0000000000000, 0xBFF0000000000000,
  0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000, 0x7FF4000000000000,
  0xFFF8000000000001, 0x0000000000000001, 0x000FFFFFFFFFFFFF, 0x0010000000000000,
  0x7FEFFFFFFFFFFFFF, 0x43E0000000000000, 0xC3E0000000000000, 0x41E0000000000000,
  0x3FE0000000000000, 0x4330000000000000, 0x3FF8000000000000, 0x400C000000000000]

def edgeF32 : Array UInt64 := #[0, 0x80000000, 0x3F800000, 0xBF800000, 0x7F800000, 0xFF800000,
  0x7FC00000, 0x7FA00000, 0xFFC00001, 0x00000001, 0x007FFFFF, 0x00800000, 0x7F7FFFFF,
  0x5F000000, 0xDF000000, 0x4F000000, 0x3F000000, 0x4B000000, 0x3FC00000, 0x40600000]

/-- A random 64-bit half of a vector register: float64/float32 edge values or random bits. -/
def Rng.fp (g : Rng) : UInt64 × Rng :=
  let (k, g) := g.below 6
  match k with
  | 0 => let (i, g) := g.below edgeF64.size; (edgeF64[i]!, g)
  | 1 =>
    let (i, g) := g.below edgeF32.size
    let (x, g) := g.next
    ((x &&& 0xFFFFFFFF00000000) ||| edgeF32[i]!, g)
  | 2 =>
    -- a "nice" double: small integer or half
    let (m, g) := g.below 2000
    let (s, g) := g.below 2
    let v : Float := (m.toFloat - 1000.0) / (if s == 0 then 1.0 else 8.0)
    (v.toBits, g)
  | 3 =>
    let (m, g) := g.below 2000
    let v : Float32 := (m.toFloat32 - 1000.0) / 4.0
    let (x, g) := g.next
    ((x &&& 0xFFFFFFFF00000000) ||| v.toBits.toUInt64, g)
  | _ => g.next

/-! ## Cases -/

/-- A case: words (the first possibly patched), initial registers, flags, window. -/
structure Case where
  words : Array (BitVec 32)
  x : Array (BitVec 64)       -- 31
  sp : BitVec 64
  nzcv : Flags
  v : Array (BitVec 128)      -- 32
  win : ByteArray

/-- The `B` from `TEST + 4 n` to the exit0 stub. -/
def bExit0 (n : Nat) : BitVec 32 :=
  let off := (EXIT0 - (TEST + BitVec.ofNat 64 (4 * n))) >>> 2
  0x14000000 ||| (off.setWidth 26).setWidth 32

/-- Replace bits `lo .. lo + len` of `w`. -/
def setFld (w : BitVec 32) (lo len : Nat) (v : Nat) : BitVec 32 :=
  let m : BitVec 32 := BitVec.ofNat 32 ((2 ^ len - 1) * 2 ^ lo)
  (w &&& ~~~m) ||| (BitVec.ofNat 32 ((v % 2 ^ len) * 2 ^ lo))

/-- The word offset from `TEST + 4 i` to `TAKEN`. -/
def toTaken (i : Nat) : Nat := (TAKEN - (TEST + BitVec.ofNat 64 (4 * i))).toNat / 4

/-- How a word is set up, or why it is not run. -/
inductive Plan where
  | run
  | skip (why : String)

/-- The memory access of an instruction, for steering its base into the window:
`(base register, displacement as a function of the state, index register, access bytes)`. -/
structure Access where
  rn : Reg
  /-- Displacement from the base register to the first accessed byte, given the index
  register's value. -/
  disp : BitVec 64 → BitVec 64
  rm : Option Reg := none
  /-- Write-back form (base must differ from the transfer registers). -/
  wb : Bool := false
  transfer : List Reg := []

def access? : Insn → Option Access
  | .ldst size vec opc mode rn rt =>
    let n := accessBytes size vec opc
    match mode with
    | .uimm imm12 => some { rn, disp := fun _ => BitVec.ofNat 64 (imm12.toNat * n) }
    | .simm imm9 idx =>
      let off := imm9.signExtend 64
      match idx with
      | .unscaled => some { rn, disp := fun _ => off }
      | .post => some { rn, disp := fun _ => 0, wb := true, transfer := if vec then [] else [rt] }
      | .pre => some { rn, disp := fun _ => off, wb := true, transfer := if vec then [] else [rt] }
    | .reg rm option s =>
      some { rn, rm := some rm,
             disp := fun i => extendReg i option (if s then Nat.log2 n else 0) }
  | .ldstPair opc vec mode _ imm7 rt2 rn rt =>
    let n := if vec then 4 * 2 ^ opc.toNat else (if opc.getLsbD 1 then 8 else 4)
    let off := imm7.signExtend 64 * BitVec.ofNat 64 n
    some { rn, disp := fun _ => if mode = 1 then 0 else off, wb := mode != 2,
           transfer := if vec then [] else [rt, rt2] }
  | .ldstExcl _ _ _ _ _ rn _ | .cas _ _ _ _ rn _ | .atomic _ _ _ _ _ _ rn _ =>
    some { rn, disp := fun _ => 0 }
  | _ => none

/-- Generate case `k` for word `w` (decoded as `i`). -/
def genCase (w : BitVec 32) (i : Insn) (g : Rng) : Except String Case × Rng := Id.run do
  let mut g := g
  let mut x : Array (BitVec 64) := #[]
  for _ in [0:31] do
    let (r, g') := g.reg; g := g'
    x := x.push (BitVec.ofNat 64 r.toNat)
  let mut v : Array (BitVec 128) := #[]
  for _ in [0:32] do
    let (lo, g') := g.fp; g := g'
    let (hi, g') := g.next; g := g'
    v := v.push (BitVec.ofNat 128 (hi.toNat * 2 ^ 64 + lo.toNat))
  let (spr, g') := g.next; g := g'
  let sp : BitVec 64 := BitVec.ofNat 64 (spr.toNat &&& 0xFFFFFFFFFFF0)
  let (fl, g') := g.below 16; g := g'
  let nzcv := Flags.ofNZCV fl
  let mut win := ByteArray.empty
  for _ in [0:WINSIZE / 8] do
    let (r, g') := g.next; g := g'
    for j in [0:8] do win := win.push ((r >>> (8 * j).toUInt64).toUInt8)
  let mut words := #[w]
  let mut sp := sp
  let setX (x : Array (BitVec 64)) (r : Reg) (val : BitVec 64) := x.set! r.toNat val
  -- branches: patch the offset to reach TAKEN
  match i with
  | .b .. => words := #[setFld w 0 26 (toTaken 0)]
  | .bcond .. | .cbz .. => words := #[setFld w 5 19 (toTaken 0)]
  | .tbz .. => words := #[setFld w 5 14 (toTaken 0)]
  | .ldrLit opc vec .. =>
    if vec && opc = 2 then return (.error "16-byte literal (beyond the known code bytes)", g)
    words := #[setFld w 5 19 0]
  | .br _ rn =>
    if rn = 31 then return (.error "BR/BLR/RET XZR", g)
    x := setX x rn TAKEN
  | .brk .. | .udf .. => return (.error "BRK/UDF trap", g)
  | _ => pure ()
  match access? i with
  | none => pure ()
  | some a =>
    if a.wb && a.rn != 31 && a.transfer.contains a.rn then
      return (.error "write-back with base = transfer register", g)
    if a.rm == some a.rn && a.rn != 31 then return (.error "index register = base", g)
    match i with
    | .ldstPair _ _ _ true _ rt2 _ rt =>
      if rt == rt2 then return (.error "load pair into one register", g)
    | .ldstExcl _ false false _ rs rn rt =>
      if rs == rt || (rs == rn && rn != 31) then
        return (.error "exclusive store status register = transfer or base register", g)
    | _ => pure ()
    let (slot, g') := g.below 8; g := g'
    let t : BitVec 64 := WIN + BitVec.ofNat 64 (64 + 16 * slot)
    let mut idx : BitVec 64 := 0
    if let some rm := a.rm then
      let (k, g') := g.below 8; g := g'
      idx := BitVec.ofNat 64 k
      if rm != 31 then x := setX x rm idx else idx := 0
    let base := t - a.disp idx
    if a.rn = 31 then sp := base &&& ~~~(15 : BitVec 64)
    else x := setX x a.rn base
    -- CAS: compare equal half of the time; exclusive store: monitor first
    match i with
    | .cas size _ _ rs rn _ =>
      let (eq, g') := g.below 2; g := g'
      if eq == 0 && rs != 31 && rs != rn then
        let a0 := (if rn = 31 then sp else x[rn.toNat]!) - WIN
        let n := 2 ^ size.toNat
        let mut val : Nat := 0
        for j in [0:n] do val := val + (win[a0.toNat + j]!).toNat * 256 ^ j
        let (hi, g') := g.next; g := g'
        -- the upper bits of Rs do not take part for B/H/W
        let hiBits := if n == 8 then 0 else (hi.toNat % 2 ^ (64 - 8 * n)) * 2 ^ (8 * n)
        x := setX x rs (BitVec.ofNat 64 (val + hiBits))
    | .ldstExcl size false false _ rs rn rt =>
      let tmp : Reg := ([0, 1, 2, 3].map (BitVec.ofNat 5)).find? (fun r => r != rs && r != rn && r != rt)
        |>.getD 4
      let ldaxr : BitVec 32 := 0x085FFC00 ||| (size.setWidth 32 <<< 30) ||| (rn.setWidth 32 <<< 5) |||
        tmp.setWidth 32
      words := #[ldaxr, w]
    | _ => pure ()
  return (.ok { words, x, sp, nzcv, v, win }, g)

/-! ## Binary protocol -/

def pushU32 (b : ByteArray) (x : Nat) : ByteArray := Id.run do
  let mut b := b
  for j in [0:4] do b := b.push (x / 256 ^ j % 256).toUInt8
  b

def pushU64 (b : ByteArray) (x : Nat) : ByteArray := Id.run do
  let mut b := b
  for j in [0:8] do b := b.push (x / 256 ^ j % 256).toUInt8
  b

def nzcvBits (f : Flags) : Nat :=
  (if f.n then 2 ^ 31 else 0) + (if f.z then 2 ^ 30 else 0) + (if f.c then 2 ^ 29 else 0) +
  (if f.v then 2 ^ 28 else 0)

def encodeState (b : ByteArray) (x : Array (BitVec 64)) (sp : BitVec 64) (f : Flags)
    (v : Array (BitVec 128)) : ByteArray := Id.run do
  let mut b := b
  for r in x do b := pushU64 b r.toNat
  b := pushU64 b sp.toNat
  b := pushU64 b (nzcvBits f)
  for r in v do
    b := pushU64 b (r.toNat % 2 ^ 64)
    b := pushU64 b (r.toNat / 2 ^ 64)
  b

def encodeCase (b : ByteArray) (c : Case) : ByteArray := Id.run do
  let mut b := pushU32 b c.words.size
  for w in c.words do b := pushU32 b w.toNat
  b := encodeState b c.x c.sp c.nzcv c.v
  b ++ c.win

def readLE (b : ByteArray) (off n : Nat) : Nat := Id.run do
  let mut r := 0
  for j in [0:n] do r := r + (b[off + j]!).toNat * 256 ^ j
  r

/-- A native result. -/
structure Result where
  x : Array (BitVec 64)
  sp : BitVec 64
  nzcv : Nat
  v : Array (BitVec 128)
  tag : Nat
  win : ByteArray

def resultSize : Nat := 31 * 8 + 8 + 8 + 32 * 16 + 4 + WINSIZE

def decodeResult (b : ByteArray) (off : Nat) : Result := Id.run do
  let mut o := off
  let mut x := #[]
  for _ in [0:31] do
    x := x.push (BitVec.ofNat 64 (readLE b o 8)); o := o + 8
  let sp := BitVec.ofNat 64 (readLE b o 8); o := o + 8
  let nzcv := readLE b o 8; o := o + 8
  let mut v := #[]
  for _ in [0:32] do
    v := v.push (BitVec.ofNat 128 (readLE b o 16)); o := o + 16
  let tag := readLE b o 4; o := o + 4
  { x, sp, nzcv, v, tag, win := b.extract o (o + WINSIZE) }

/-! ## Running a case in Lean -/

def initState (c : Case) : MState :=
  let win := c.win
  let words := c.words.push (bExit0 c.words.size)
  let codeBytes : ByteArray := words.foldl (fun b w => pushU32 b w.toNat) ByteArray.empty
  { x := fun r => c.x.getD r.toNat 0
    sp := c.sp
    v := fun r => c.v.getD r.toNat 0
    nzcv := c.nzcv
    pc := TEST
    mem := fun a =>
      let d := a - WIN
      if d.toNat < WINSIZE then BitVec.ofNat 8 (win[d.toNat]!).toNat
      else
        let e := a - TEST
        if e.toNat < codeBytes.size then BitVec.ofNat 8 (codeBytes[e.toNat]!).toNat else 0 }

def codeOf (c : Case) : Code := fun a =>
  let e := a - TEST
  if e.toNat % 4 == 0 && e.toNat / 4 < c.words.size then some c.words[e.toNat / 4]! else none

/-- Run until the PC leaves the test words: the final state and the exit tag. -/
def runCase (c : Case) : Except String (MState × Nat) := Id.run do
  let code := codeOf c
  let fall := TEST + BitVec.ofNat 64 (4 * c.words.size)
  let mut s := initState c
  for _ in [0:c.words.size + 1] do
    if s.pc == fall then return .ok (s, 0)
    if s.pc == TAKEN then return .ok (s, 1)
    match step code s with
    | .ok s' => s := s'
    | .error f => return .error s!"fault {repr f}"
  return .error s!"pc {s.pc.toHex} outside the test words"

def hex64 (x : BitVec 64) : String := "0x" ++ x.toHex

/-- Differences between the Lean final state and the native result. -/
def compare (s : MState) (tag : Nat) (r : Result) : List String := Id.run do
  let mut d := []
  for k in [0:31] do
    let l := s.x (BitVec.ofNat 5 k)
    if l != r.x[k]! then d := d ++ [s!"X{k}: lean {hex64 l} native {hex64 r.x[k]!}"]
  if s.sp != r.sp then d := d ++ [s!"SP: lean {hex64 s.sp} native {hex64 r.sp}"]
  if nzcvBits s.nzcv != r.nzcv then
    d := d ++ [s!"NZCV: lean {(nzcvBits s.nzcv) / 2 ^ 28} native {r.nzcv / 2 ^ 28}"]
  for k in [0:32] do
    let l := s.v (BitVec.ofNat 5 k)
    if l != r.v[k]! then d := d ++ [s!"V{k}: lean 0x{l.toHex} native 0x{r.v[k]!.toHex}"]
  if tag != r.tag then d := d ++ [s!"exit: lean {tag} native {r.tag}"]
  for k in [0:WINSIZE] do
    let l := s.mem (WIN + BitVec.ofNat 64 k)
    if l.toNat != (r.win[k]!).toNat then
      d := d ++ [s!"mem WIN+{k}: lean {l.toNat} native {(r.win[k]!).toNat}"]
  d

/-! ## Driver -/

def readWords (path : System.FilePath) : IO (Array (BitVec 32 × Nat)) := do
  let txt ← IO.FS.readFile path
  let mut out := #[]
  for line in txt.splitOn "\n" do
    match line.splitOn " " with
    | [h, c] =>
      let w := h.foldl (fun acc ch =>
        acc * 16 + (if ch.isDigit then ch.toNat - '0'.toNat else ch.toLower.toNat - 'a'.toNat + 10)) 0
      out := out.push (BitVec.ofNat 32 w, c.toNat!)
    | _ => pure ()
  return out

/-- `k` random words that `decode` accepts (except `BRK`/`UDF`, which trap), with count 0:
the encodings the decoder accepts beyond the corpus' words. Half are uniformly random words,
half are corpus words (of a form chosen uniformly) with one to three bits flipped (neighbouring encodings of the same class:
other opcodes, sizes, registers, immediates; the narrow classes uniform words rarely hit). -/
def fuzzWords (corpus : Array (BitVec 32 × Nat)) (k seed : Nat) : Array (BitVec 32 × Nat) := Id.run do
  let mut g : Rng := ⟨UInt64.ofNat (seed * 0xD1B54A32D192ED03 + 7)⟩
  -- corpus words by form, so that every form's neighbourhood is explored equally
  let mut byForm : Std.HashMap String (Array (BitVec 32)) := {}
  for (w, _) in corpus do
    if let some i := decode w then byForm := byForm.alter i.form fun e => some ((e.getD #[]).push w)
  let groups := (byForm.toArray.qsort (fun a b => a.1 < b.1)).map (·.2)
  let mut out := #[]
  let mut tries := 0
  while out.size < k && tries < 1000 * k do
    tries := tries + 1
    let (x, g') := g.next; g := g'
    let mut w : BitVec 32 := BitVec.ofNat 32 (x.toNat % 2 ^ 32)
    if x.toNat / 2 ^ 32 % 2 == 0 && !groups.isEmpty then
      let (f, g') := g.below groups.size; g := g'
      let ws := groups[f]!
      let (i, g') := g.below ws.size; g := g'
      let (nf, g') := g.below 3; g := g'
      w := ws[i]!
      for _ in [0:nf + 1] do
        let (b, g') := g.below 32; g := g'
        w := w ^^^ BitVec.ofNat 32 (2 ^ b)
    match decode w with
    | some (.brk _) | some (.udf _) | none => pure ()
    | some _ => out := out.push (w, 0)
  out

/-- All cases, in order, with their word's form; and the cases not run, by reason. Each form
gets `n` cases per distinct word and at least `minPerForm` cases (its words in turn). -/
def genAll (words : Array (BitVec 32 × Nat)) (n minPerForm seed : Nat) :
    Array (String × BitVec 32 × Case) × Std.HashMap String (Nat × String) := Id.run do
  let mut g : Rng := ⟨UInt64.ofNat (seed * 0x9E3779B97F4A7C15 + 1)⟩
  let mut byForm : Std.HashMap String (Array (BitVec 32 × Insn)) := {}
  let mut order : Array String := #[]
  let mut skipped : Std.HashMap String (Nat × String) := {}
  for (w, _) in words do
    match decode w with
    | none => skipped := skipped.alter "undecoded" fun e => some ((e.map (·.1)).getD 0 + 1, w.toHex)
    | some i =>
      if !byForm.contains i.form then order := order.push i.form
      byForm := byForm.alter i.form fun e => some ((e.getD #[]).push (w, i))
  let mut cases := #[]
  for f in order do
    let ws := byForm.getD f #[]
    let total := max (n * ws.size) minPerForm
    for k in [0:total] do
      let (w, i) := ws[k % ws.size]!
      let (c, g') := genCase w i g
      g := g'
      match c with
      | .ok c => cases := cases.push (f, w, c)
      | .error why =>
        skipped := skipped.alter s!"{f}: {why}" fun e => some ((e.map (·.1)).getD 0 + 1, w.toHex)
  (cases, skipped)

def gen (words : Array (BitVec 32 × Nat)) (n m seed : Nat) (out : System.FilePath) : IO UInt32 := do
  let (cases, _) := genAll words n m seed
  let h ← IO.FS.Handle.mk out .write
  let mut b := ByteArray.empty
  for (_, _, c) in cases do
    b := encodeCase b c
    if b.size > (1 <<< 22) then
      h.write b; b := ByteArray.empty
  h.write b
  IO.eprintln s!"arm64-cosim gen: {cases.size} cases"
  return 0

structure Cov where
  words : Std.HashMap (BitVec 32) Unit := {}
  cases : Nat := 0
  bad : Nat := 0

def check (words : Array (BitVec 32 × Nat)) (n m seed : Nat) (resPath : System.FilePath) :
    IO UInt32 := do
  let (cases, skipped) := genAll words n m seed
  let res ← IO.FS.readBinFile resPath
  if res.size != cases.size * resultSize then
    IO.eprintln s!"arm64-cosim check: {res.size} result bytes for {cases.size} cases \
      ({cases.size * resultSize} expected)"
    return 1
  let mut cov : Std.HashMap String Cov := {}
  let mut shown := 0
  let mut bad := 0
  let mut k := 0
  for (form, w, c) in cases do
    let r := decodeResult res (k * resultSize)
    k := k + 1
    let diffs := match runCase c with
      | .ok (s, tag) => compare s tag r
      | .error e => [e]
    let e := (cov.getD form {})
    let e := { e with words := e.words.insert w (), cases := e.cases + 1,
                      bad := e.bad + (if diffs.isEmpty then 0 else 1) }
    cov := cov.insert form e
    if !diffs.isEmpty then
      bad := bad + 1
      if shown < 40 then
        shown := shown + 1
        IO.println s!"MISMATCH {form} word {w.toHex} (run {c.words.map (·.toHex)}): \
          {", ".intercalate (diffs.take 6)}"
  -- forms of the corpus words (by occurrence) and their coverage
  let mut occ : Std.HashMap String Nat := {}
  for (w, cnt) in words do
    let f := (decode w).map (·.form) |>.getD "undecoded"
    occ := occ.alter f (some <| ·.getD 0 + cnt)
  let forms := occ.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
  IO.println "form | corpus occurrences | distinct words run | cases | mismatches"
  let mut covered := 0
  let mut inCorpus := 0
  let mut extra := 0
  for (f, o) in forms do
    let e := cov.getD f {}
    if o > 0 then inCorpus := inCorpus + 1
    if e.cases > 0 then
      if o > 0 then covered := covered + 1 else extra := extra + 1
    IO.println s!"{f} | {o} | {e.words.size} | {e.cases} | {e.bad}"
  for (why, (cnt, ex)) in skipped.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"not run: {why}: {cnt} cases (e.g. {ex})"
  let fuzz := words.filter (·.2 == 0) |>.size
  IO.println s!"arm64-cosim: {inCorpus} forms in the corpus, {covered} co-simulated; \
    {fuzz} random decodable words add {extra} forms; {cases.size} cases, {bad} mismatches"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["gen", ws, n, m, k, seed, out] =>
    let ws ← readWords ws
    gen (ws ++ fuzzWords ws k.toNat! seed.toNat!) n.toNat! m.toNat! seed.toNat! out
  | ["check", ws, n, m, k, seed, res] =>
    let ws ← readWords ws
    check (ws ++ fuzzWords ws k.toNat! seed.toNat!) n.toNat! m.toNat! seed.toNat! res
  | _ =>
    IO.eprintln "usage: arm64-cosim gen <words> <n> <min> <fuzz> <seed> <cases> | \
      check <words> <n> <min> <fuzz> <seed> <results>"
    return 2

end GoFVTest.Arm64Cosim

def main (args : List String) : IO UInt32 := GoFVTest.Arm64Cosim.main args
