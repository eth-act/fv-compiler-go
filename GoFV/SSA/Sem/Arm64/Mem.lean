import GoFV.SSA.Sem.Arm64.Reg

/-!
# arm64 memory ops on the Phase 1 memory (`docs/plans/semantics2.md` §4 (c.4))

Loads, stores and their pair, indexed and 128-bit forms, `LoweredZero`/`LoweredMove` (and their
loop forms), on Phase 1's `Mem` with its access rule (`Sem/Mem.lean`): an invalid load gives
`poison` (loads are pure, §3.4), an invalid store is `stuck` (`none` here; the caller decides).
The address is computed by the caller (`Arm64.addr`, or the symbol of the aux, `Sem.symAddr` in
`Sem/RunL.lean`).

A narrow load is the `LDR{B,H,W}`/`LDRS{B,H,W}` of its op: the loaded bits zero- or
sign-extended to the register. An 8-byte load reads a stored pointer back as its word
(`decodeInt`). A 16-byte (`Vec128`, `FMOVQ`, `FLDPQ`) value is a `blob` of its bytes.
-/

namespace GoFV.SSA.Sem.Arm64

/-- The load of `n` bytes (`1, 2, 4, 8`) at `p` into a register, sign-extended if `signed`. -/
def loadN (ty : Ty) (n : Nat) (signed : Bool) (m : Mem) (p : Ptr) : Val :=
  match n with
  | 8 => match m.load (.int .w64) p with
    | .int .w64 x => res ty x
    | v => v
  | _ => match Width.ofSize? n with
    | some w => match m.load (.int w) p with
      | .int _ x =>
        let x : BitVec 64 := x.setWidth 64
        res ty (if signed then sext (8 * n) x else x)
      | _ => .poison
    | none => .poison

/-- The 16 bytes at `p` as a `Vec128` value. -/
def load16 (m : Mem) (p : Ptr) : Val :=
  match m.read p 16 with
  | some bs => .blob bs.toList
  | none => .poison

/-- The shape of component `i` of a tuple-typed value. -/
def tupleTy (ty : Ty) (i : Nat) : Ty :=
  match ty with
  | .tuple ts => ts.getD i .other
  | _ => .other

/-- A pair load (`LDP`, `LDPW`, `LDPSW`, `FLDP{S,D,Q}`) of two `n`-byte elements at `p`. -/
def loadPair (ty : Ty) (n : Nat) (signed : Bool) (m : Mem) (p : Ptr) : Val :=
  if n = 16 then .tuple [load16 m p, load16 m (p.add 16)]
  else .tuple [loadN (tupleTy ty 0) n signed m p,
    loadN (tupleTy ty 1) n signed m (p.add (BitVec.ofNat 64 n))]

/-- The `n` bytes (`1, 2, 4, 8, 16`) a store of `v` writes: the low bytes of its register, a
pointer as its fragments (8 bytes), a `Vec128` blob as its bytes; `poison` bytes otherwise. -/
def storeBytes (n : Nat) (v : Val) : Array Byte :=
  match n, v with
  | 8, .ptr p => ptrBytes p
  | _, .blob bs => if bs.length == n then bs.toArray else Array.replicate n .poison
  | _, v => match reg v with
    | some x => if n ≤ 8 then intBytes n x.toNat else Array.replicate n .poison
    | none => Array.replicate n .poison

/-- A store of `v` (`n` bytes) at `p`. -/
def storeN (n : Nat) (p : Ptr) (v : Val) (m : Mem) : Option Mem := m.write p (storeBytes n v)

/-- A pair store (`STP`, `STPW`, `FSTP{S,D,Q}`) of `a` at `p` and `b` after it. -/
def storePair (n : Nat) (p : Ptr) (a b : Val) (m : Mem) : Option Mem :=
  m.write p (storeBytes n a ++ storeBytes n b)

/-- `LoweredZero [n] p mem` (and `LoweredZeroLoop`): `n` zero bytes at `p`; `poison` (a memory
no later access can use) if the write is invalid. -/
def zero (n : Int64) : List Val → Val
  | [a, .mem m] => match addr a 0 with
    | some p => match m.write p (Array.replicate n.toInt.toNat (.b 0)) with
      | some m' => .mem m'
      | none => .poison
    | none => .poison
  | _ => .poison

/-- `LoweredMove [n] dst src mem` (and `LoweredMoveLoop`): copy `n` bytes. -/
def move (n : Int64) : List Val → Val
  | [d, s, .mem m] => match addr d 0, addr s 0 with
    | some pd, some ps => match m.read ps n.toInt.toNat with
      | some bs => match m.write pd bs with
        | some m' => .mem m'
        | none => .poison
      | none => .poison
    | _, _ => .poison
  | _ => .poison

end GoFV.SSA.Sem.Arm64
