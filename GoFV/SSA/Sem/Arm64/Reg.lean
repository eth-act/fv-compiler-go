import GoFV.SSA.Sem.Ptr
import GoFV.SSA.Sem.Flags

/-!
# Registers of lowered arm64 SSA (`docs/plans/semantics2.md` §3)

An arm64 op reads and writes 64-bit registers; lowered SSA values keep Phase 1's domain. The
bridge, used by every op family of `Sem/Arm64`:

* **Reading** (`reg`): an integer of width `w` is the register holding it zero-extended (a value
  of a narrow type has unspecified upper bits on the machine; Go's rules only rely on them where
  the producing instruction defines them, and those producers keep their full register, see
  `Sem/RunL.lean` `arm64Op` for `MOVDreg`), a boolean is 0 or 1, a pointer its concrete address
  (`Ptr.addr?`; a global has none, so an op that needs its bits is `poison`).
* **Writing** (`res`): a 64-bit integer, or at the `bool` shape the boolean of bit 0 (the bit Go
  branches on, `(If c) => (TBNZ [0] c)`); `runL` then shapes it at the value's type
  (`Val.retypeL`).
* **Provenance** (`addP`): the pointer cases of §3 (`ADD p i`, `SUB p i`, `ADDconst`, …) add to a
  pointer that has no integer form as Phase 1's `AddPtr` does (`PtrOps.ptrRes`).
-/

namespace GoFV.SSA.Sem.Arm64

/-- The 64-bit register holding `v`. -/
def reg : Val → Option (BitVec 64)
  | .int _ x => some (x.setWidth 64)
  | .bool b => some (if b then 1 else 0)
  | .ptr p => p.addr?
  | _ => none

/-- The low 32 bits of the register holding `v` (the `W` register). -/
def reg32 (v : Val) : Option (BitVec 32) := (reg v).map (·.setWidth 32)

/-- The low `w` bits set. -/
def mask (w : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ w - 1)

/-- The low `w` bits of `x` sign-extended (`w ≥ 1`; `w = 0` gives 0). -/
def sext (w : Nat) (x : BitVec 64) : BitVec 64 :=
  if w = 0 then 0 else ((x &&& mask w) <<< (64 - w)).sshiftRight (64 - w)

/-- The value of a 64-bit register result at shape `ty`. -/
def res (ty : Ty) (r : BitVec 64) : Val :=
  match ty with
  | .bool => .bool (r.getLsbD 0)
  | _ => .int .w64 r

/-- The value of a 32-bit (`W`) register result at shape `ty`: zero-extended, as a write of
`Wd` clears the upper half. -/
def res32 (ty : Ty) (r : BitVec 32) : Val := res ty (r.setWidth 64)

/-- A register value moved unchanged (`CSEL`'s selected input, `MOVDreg`): a pointer without an
integer form stays the pointer, any other value is its register. -/
def regVal (ty : Ty) (v : Val) : Val :=
  match v with
  | .ptr p => .ptr p
  | v => match reg v with
    | some r => res ty r
    | none => .poison

/-- A unary op on 64-bit registers. -/
@[inline] def op1 (ty : Ty) (f : BitVec 64 → BitVec 64) : List Val → Val
  | [a] => match reg a with
    | some x => res ty (f x)
    | none => .poison
  | _ => .poison

/-- A binary op on 64-bit registers. -/
@[inline] def op2 (ty : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64) : List Val → Val
  | [a, b] => match reg a, reg b with
    | some x, some y => res ty (f x y)
    | _, _ => .poison
  | _ => .poison

/-- A ternary op on 64-bit registers. -/
@[inline] def op3 (ty : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) :
    List Val → Val
  | [a, b, c] => match reg a, reg b, reg c with
    | some x, some y, some z => res ty (f x y z)
    | _, _, _ => .poison
  | _ => .poison

/-- A unary op on 32-bit registers. -/
@[inline] def op1w (ty : Ty) (f : BitVec 32 → BitVec 32) : List Val → Val
  | [a] => match reg32 a with
    | some x => res32 ty (f x)
    | none => .poison
  | _ => .poison

/-- A binary op on 32-bit registers. -/
@[inline] def op2w (ty : Ty) (f : BitVec 32 → BitVec 32 → BitVec 32) : List Val → Val
  | [a, b] => match reg32 a, reg32 b with
    | some x, some y => res32 ty (f x y)
    | _, _ => .poison
  | _ => .poison

/-- A ternary op on 32-bit registers. -/
@[inline] def op3w (ty : Ty) (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) :
    List Val → Val
  | [a, b, c] => match reg32 a, reg32 b, reg32 c with
    | some x, some y, some z => res32 ty (f x y z)
    | _, _, _ => .poison
  | _ => .poison

/-- `a + k` where `a` may be a pointer without an integer form (§3 provenance case): that
pointer moved by `k` under Phase 1's window rule (`PtrOps.ptrRes`), else the register sum. -/
def addP (ty : Ty) (a : Val) (k : BitVec 64) : Val :=
  match a with
  | .ptr p => PtrOps.ptrRes (p.add k)
  | a => match reg a with
    | some x => res ty (x + k)
    | none => .poison

/-- `ADD a b` with the provenance cases `ADD p i`, `ADD i p`; two pointers add as words (the sum
of their addresses, `semantics2.md` §3), so `ADD` is symmetric, as its `commutative` flag says
(cse swaps its arguments). -/
def add (ty : Ty) : List Val → Val
  | [.ptr p, .ptr q] => op2 ty (· + ·) [.ptr p, .ptr q]
  | [.ptr p, b] => match reg b with
    | some k => PtrOps.ptrRes (p.add k)
    | none => .poison
  | [a, .ptr p] => match reg a with
    | some k => PtrOps.ptrRes (p.add k)
    | none => .poison
  | args => op2 ty (· + ·) args

/-- `SUB a b` with the provenance cases `SUB p i` (a pointer) and `SUB p q` (Phase 1's `SubPtr`:
the difference of offsets within one allocation). -/
def sub (ty : Ty) : List Val → Val
  | [.ptr p, .ptr q] =>
    match p.addr?, q.addr? with
    | some x, some y => res ty (x - y)
    | _, _ => if p.blk == q.blk then res ty (p.off - q.off) else .poison
  | [.ptr p, b] => match reg b with
    | some k => PtrOps.ptrRes (p.add (-k))
    | none => .poison
  | args => op2 ty (· - ·) args

/-- The address `base + k` an access reads or writes (`base` a pointer or a pointer word). -/
def addr (base : Val) (k : BitVec 64) : Option Ptr :=
  match base with
  | .ptr p => some (p.add k)
  | v => (reg v).map fun x => Ptr.ofAddr (x + k)

/-! ## Flags producers -/

/-- `SUBS x y` (`CMP`): `AddWithCarry(x, NOT y, 1)`. -/
def subFlags {n : Nat} (x y : BitVec n) : BitVec n × Flags := addWithCarry x (~~~y) true

/-- The flags of the compare `SUBS`/`ADDS` result `p` (`Flags.toValSub`: with the sign of the
negated difference). -/
@[inline] def cmpRes {n : Nat} (p : BitVec n × Flags) : Val := p.2.toValSub p.1

/-- `CMP a b` of 64-bit registers (`f` the second operand's transformation: a shift or a
constant). Pointers of one allocation compare by offset; pointers of different allocations
without concrete addresses only by `Z` (they are never equal, Phase 1's `EqPtr`), the order bits
being unknown. -/
def cmp (a b : Val) : Val :=
  match reg a, reg b with
  | some x, some y => cmpRes (subFlags x y)
  | _, _ =>
    match a, b with
    | .ptr p, .ptr q =>
      if p.blk == q.blk then cmpRes (subFlags p.off q.off)
      else .agg [.poison, .bool false, .poison, .poison, .poison]
    | .ptr _, b | b, .ptr _ =>
      if (reg b).isSome then .agg [.poison, .bool false, .poison, .poison, .poison] else .poison
    | _, _ => .poison

/-- Flags of a binary 64-bit compare (`CMP`/`CMN` forms; `f` gives the difference and the flags)
whose operands are registers. -/
@[inline] def cmp2 (f : BitVec 64 → BitVec 64 → BitVec 64 × Flags) : List Val → Val
  | [a, b] => match reg a, reg b with
    | some x, some y => cmpRes (f x y)
    | _, _ => .poison
  | _ => .poison

/-- Flags of a binary 32-bit compare. -/
@[inline] def cmp2w (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) : List Val → Val
  | [a, b] => match reg32 a, reg32 b with
    | some x, some y => cmpRes (f x y)
    | _, _ => .poison
  | _ => .poison

/-- Flags of a 64-bit compare with an immediate. -/
@[inline] def cmp1 (f : BitVec 64 → BitVec 64 × Flags) : List Val → Val
  | [a] => match reg a with
    | some x => cmpRes (f x)
    | none => .poison
  | _ => .poison

/-- Flags of a 32-bit compare with an immediate. -/
@[inline] def cmp1w (f : BitVec 32 → BitVec 32 × Flags) : List Val → Val
  | [a] => match reg32 a with
    | some x => cmpRes (f x)
    | none => .poison
  | _ => .poison

/-- Flags of a binary 64-bit op whose operands are registers. -/
@[inline] def flags2 (f : BitVec 64 → BitVec 64 → Flags) : List Val → Val
  | [a, b] => match reg a, reg b with
    | some x, some y => (f x y).toVal
    | _, _ => .poison
  | _ => .poison

/-- Flags of a binary 32-bit op. -/
@[inline] def flags2w (f : BitVec 32 → BitVec 32 → Flags) : List Val → Val
  | [a, b] => match reg32 a, reg32 b with
    | some x, some y => (f x y).toVal
    | _, _ => .poison
  | _ => .poison

/-- Flags of a unary 64-bit op. -/
@[inline] def flags1 (f : BitVec 64 → Flags) : List Val → Val
  | [a] => match reg a with
    | some x => (f x).toVal
    | none => .poison
  | _ => .poison

/-- Flags of a unary 32-bit op. -/
@[inline] def flags1w (f : BitVec 32 → Flags) : List Val → Val
  | [a] => match reg32 a with
    | some x => (f x).toVal
    | none => .poison
  | _ => .poison

/-- The `PSTATE.C` bit of a flags value. -/
def carry : Val → Option Bool
  | .agg [_, _, c, _, _] => c.flagBit
  | _ => none

end GoFV.SSA.Sem.Arm64
