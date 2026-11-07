import GoFV.SSA.Sem.Flags

/-!
# ARM64 machine state (`docs/plans/semantics3.md` §3)

The state of the Phase 3 machine: X0–X30, SP, V0–V31 (128 bits), `PSTATE.NZCV` (Phase 2's
`GoFV.SSA.Sem.Flags`), the PC, and a flat little-endian byte memory `BitVec 64 → BitVec 8`.
Code is not part of the state: it is a separate read-only fetch function (`Code`), since Go code
is never written. `FPCR` is fixed to 0 (round to nearest even, no flush-to-zero, no default NaN:
what Linux gives a process; Go never writes it) and is therefore not a field; `FPSR` is not
modelled (no Go code reads it). One core: exclusive stores succeed (`Exec.lean`).

**Memory and Phase 2's `Mem`.** Phase 1/2 memory is block-structured with provenance
(`GoFV/SSA/Sem/Mem.lean`); this memory is flat. The bridge is the injection `ι : Blk → Option
(BitVec 64)` of `docs/plans/semantics3.md` §4.3: bytes of live blocks equal the machine bytes at
`ι`, pointer fragments equal the encoding of the injected address. The only memory fault the
machine has is the nil page: an access whose address is below 4096 faults (`Fault.nilPage`), the
kernel's SIGSEGV that `sigpanic` turns into a nil-dereference panic (§6).

Registers are indexed by their 5-bit encoding field. `rX` reads index 31 as XZR, `rXsp` as SP,
matching the two readings the Arm ARM gives the field per instruction form (`X[n]` and
`SP`-or-`X[n]`); index 31 of `x` is never read.
-/

namespace GoFV.Arm64

open GoFV.SSA.Sem (Flags)

/-- A register field of an encoding. -/
abbrev Reg := BitVec 5

/-- A flat byte memory. -/
abbrev Memory := BitVec 64 → BitVec 8

/-- The machine state. -/
structure MState where
  /-- X0–X30 by index (index 31 unused: XZR or SP depending on the form). -/
  x : Reg → BitVec 64
  sp : BitVec 64
  /-- V0–V31. -/
  v : Reg → BitVec 128
  nzcv : Flags
  pc : BitVec 64
  mem : Memory

/-- The read-only code: the instruction word at an address, if code is mapped there. -/
abbrev Code := BitVec 64 → Option (BitVec 32)

/-- Why a step stops without a successor state. -/
inductive Fault where
  /-- A load or store touching the nil page `[0, 4096)`. -/
  | nilPage (addr : BitVec 64)
  /-- `BRK`/`UDF`, or a word `decode` rejects (unallocated or outside the modelled subset). -/
  | undefined (w : BitVec 32)
  /-- No code at the PC. -/
  | noCode (pc : BitVec 64)
  deriving DecidableEq, Repr

namespace MState

/-- `X[r]` with index 31 read as XZR. -/
def rX (s : MState) (r : Reg) : BitVec 64 := if r = 31 then 0 else s.x r

/-- `X[r]` with index 31 read as SP. -/
def rXsp (s : MState) (r : Reg) : BitVec 64 := if r = 31 then s.sp else s.x r

/-- Write `X[r]`; index 31 is XZR, the write is discarded. -/
def wX (s : MState) (r : Reg) (val : BitVec 64) : MState :=
  if r = 31 then s else { s with x := fun i => if i = r then val else s.x i }

/-- Write `X[r]` with index 31 meaning SP. -/
def wXsp (s : MState) (r : Reg) (val : BitVec 64) : MState :=
  if r = 31 then { s with sp := val } else { s with x := fun i => if i = r then val else s.x i }

/-- Write `V[r]`. -/
def wV (s : MState) (r : Reg) (val : BitVec 128) : MState :=
  { s with v := fun i => if i = r then val else s.v i }

end MState

/-- `n` bytes at `a`, little-endian. -/
def readMem (m : Memory) (a : BitVec 64) : (n : Nat) → BitVec (8 * n)
  | 0 => 0
  | n + 1 => ((readMem m (a + 1) n) ++ m a).cast (by omega)

/-- Write the `n` bytes of `val` at `a`, little-endian. -/
def writeMem (m : Memory) (a : BitVec 64) : (n : Nat) → BitVec (8 * n) → Memory
  | 0, _ => m
  | n + 1, val =>
    let m' : Memory := fun i => if i = a then val.extractLsb' 0 8 else m i
    writeMem m' (a + 1) n (val.extractLsb' 8 (8 * n))

/-- Whether an access at `a` faults: the nil page. -/
def nilPage (a : BitVec 64) : Bool := a.toNat < 4096

end GoFV.Arm64
