import GoFV.SSA.Sem.Arm64.Reg

/-!
# arm64 integer ops (`docs/plans/semantics2.md` §4 (c.1))

One definition per family on `BitVec`, total as the instructions are, transcribed from the Arm
ARM pseudocode of the instruction `ssaGenValue` emits (`cmd/compile/internal/arm64/ssa.go`):

* `ADD`/`SUB`/`AND`/`ORR`/`EOR`/`BIC`/`EON`/`ORN`/`MVN`/`NEG` and their shifted-register forms
  (`DecodeShift`, `ShiftReg`: `LSL`, `LSR`, `ASR`, `ROR` by the auxint);
* `LSLV`/`LSRV`/`ASRV`/`RORV` (`SLL`, `SRL`, `SRA`, `ROR`, `RORW`): the amount modulo the width;
* `MUL`/`MNEG`/`MADD`/`MSUB`, `SMULH`/`UMULH`, `SMULL`/`UMULL`, `SDIV`/`UDIV` (a zero divisor
  gives 0, `MIN / −1 = MIN`), `REM`/`UREM` (Go's `SDIV` + `MSUB` pair: `x − (x / y)·y`);
* the bitfield moves (`UBFX`, `SBFX`, `UBFIZ`, `SBFIZ`, `BFI`, `BFXIL`; auxint `lsb << 8 | width`,
  `_gen/ARM64Ops.go` "bitfield ops"), `EXTR`, `CLZ`, `RBIT`, `REV*`, the extensions
  `SXTB`…`UXTW` (`MOV{B,BU,H,HU,W,WU}reg`);
* compares to flags (`AddWithCarry`, `ANDS`), the flag-setting adds of `math/bits` lowering, and
  the conditional ops `CSEL`/`CSINC`/`CSINV`/`CSNEG`/`CSETM`/`CCMP`/`CCMN` (`ConditionHolds`).

`W` forms read the low 32 bits and zero-extend their result.
-/

namespace GoFV.SSA.Sem.Arm64

/-- A shift kind of a shifted-register operand. -/
inductive Shift where
  | ll | rl | ra | ro
  deriving DecidableEq, Repr

/-- `ShiftReg(x, kind, amount)` (the amount taken modulo the width). -/
def Shift.apply {n : Nat} (k : Shift) (x : BitVec n) (s : Nat) : BitVec n :=
  let s := s % n
  match k with
  | .ll => x <<< s
  | .rl => x >>> s
  | .ra => x.sshiftRight s
  | .ro => x.rotateRight s

/-- The auxint as an amount (negative auxints never occur; read as 0). -/
def amt (k : Int64) : Nat := k.toInt.toNat

/-- The auxint as a 64-bit immediate. -/
def imm (k : Int64) : BitVec 64 := BitVec.ofInt 64 k.toInt

/-- The auxint as a 32-bit immediate (`Int32` auxints of the `W` compares). -/
def imm32 (k : Int64) : BitVec 32 := BitVec.ofInt 32 k.toInt

/-! ## Bitfield moves -/

/-- `lsb` and `width` of an `ARM64BitField` auxint. -/
def bf (k : Int64) : Nat × Nat := (k.toInt.toNat / 256, k.toInt.toNat % 256)

def ubfx (k : Int64) (x : BitVec 64) : BitVec 64 := (x >>> (bf k).1) &&& mask (bf k).2
def sbfx (k : Int64) (x : BitVec 64) : BitVec 64 := sext (bf k).2 (x >>> (bf k).1)
def ubfiz (k : Int64) (x : BitVec 64) : BitVec 64 := (x &&& mask (bf k).2) <<< (bf k).1
def sbfiz (k : Int64) (x : BitVec 64) : BitVec 64 := sext (bf k).2 x <<< (bf k).1
/-- `BFI`: the low `width` bits of `b` inserted into `a` at `lsb`. -/
def bfi (k : Int64) (a b : BitVec 64) : BitVec 64 :=
  (a &&& ~~~(mask (bf k).2 <<< (bf k).1)) ||| ((b &&& mask (bf k).2) <<< (bf k).1)
/-- `BFXIL`: `width` bits of `b` at `lsb` inserted into the low end of `a`. -/
def bfxil (k : Int64) (a b : BitVec 64) : BitVec 64 :=
  (a &&& ~~~(mask (bf k).2)) ||| ((b >>> (bf k).1) &&& mask (bf k).2)

/-- `EXTR`: bits `lsb + n − 1 … lsb` of `hi:lo`. -/
def extr {n : Nat} (lsb : Nat) (hi lo : BitVec n) : BitVec n :=
  let s := lsb % n
  if s = 0 then lo else (hi <<< (n - s)) ||| (lo >>> s)

/-! ## Multiplication and division -/

/-- `SMULH`. -/
def smulh (x y : BitVec 64) : BitVec 64 := (x.signExtend 128 * y.signExtend 128).extractLsb' 64 64
/-- `UMULH`. -/
def umulh (x y : BitVec 64) : BitVec 64 := (x.setWidth 128 * y.setWidth 128).extractLsb' 64 64
/-- `SMULL`: the product of the sign-extended low words. -/
def smull (x y : BitVec 64) : BitVec 64 :=
  (x.setWidth 32).signExtend 64 * (y.setWidth 32).signExtend 64
/-- `UMULL`. -/
def umull (x y : BitVec 64) : BitVec 64 := (x.setWidth 32).setWidth 64 * (y.setWidth 32).setWidth 64
/-- `SDIV`: truncated, by zero 0 (`BitVec.sdiv`). -/
def sdiv {n : Nat} (x y : BitVec n) : BitVec n := x.sdiv y
/-- `UDIV`: by zero 0. -/
def udiv {n : Nat} (x y : BitVec n) : BitVec n := x / y
/-- `REM` (Go's `SDIV tmp; MSUB`). -/
def srem {n : Nat} (x y : BitVec n) : BitVec n := x - x.sdiv y * y
/-- `UREM`. -/
def urem {n : Nat} (x y : BitVec n) : BitVec n := x - x / y * y

/-! ## Bit operations -/

def clz {n : Nat} (x : BitVec n) : BitVec n := BitVec.ofNat n x.clz.toNat
def rbit {n : Nat} (x : BitVec n) : BitVec n := x.reverse
/-- `REV`/`REVW`: the bytes reversed. -/
def rev {n : Nat} (x : BitVec n) : BitVec n := BitVec.ofNat n (Int.bswapNat (n / 8) x.toNat)
/-- `REV16`/`REV16W`: the bytes of each halfword swapped. -/
def rev16 {n : Nat} (x : BitVec n) : BitVec n :=
  let hi := x &&& BitVec.ofNat n (0xff00ff00ff00ff00 % 2 ^ n)
  let lo := x &&& BitVec.ofNat n (0x00ff00ff00ff00ff % 2 ^ n)
  (hi >>> 8) ||| (lo <<< 8)

/-- `VCNT` (8B arrangement): the population count of each byte. -/
def vcnt (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 8).foldl (fun acc i =>
    acc + ((x >>> (8 * i)) &&& 0xff).cpop.toNat * 256 ^ i) 0)

/-- `UADDLV` (8B): the sum of the bytes. -/
def vuaddlv (x : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((List.range 8).foldl (fun acc i => acc + ((x >>> (8 * i)) &&& 0xff).toNat) 0)

/-! ## Extensions -/

/-- `MOV{B,H,W}reg` (`signed`) and `MOV{BU,HU,WU}reg`: the low `w` bits extended. -/
def ext (signed : Bool) (w : Nat) (x : BitVec 64) : BitVec 64 :=
  if signed then sext w x else x &&& mask w

/-! ## Flags -/

/-- `CMN x y`: `AddWithCarry(x, y, 0)`. -/
def cmnFlags {n : Nat} (x y : BitVec n) : Flags := (addWithCarry x y false).2

/-- A flag-setting add as a tuple `(result, flags)` (`ADDS`, `ADCS`, `SUBS`, `SBCS`, `NEGS`). -/
def flagsTuple (ty : Ty) (r : BitVec 64 × Flags) : Val :=
  let t0 := match ty with
    | .tuple (t :: _) => t
    | _ => .int .w64
  .tuple [res t0 r.1, r.2.toVal]

/-- `ADDS x y` (`ADDSflags`). -/
def adds (ty : Ty) : List Val → Val
  | [a, b] => match reg a, reg b with
    | some x, some y => flagsTuple ty (addWithCarry x y false)
    | _, _ => .poison
  | _ => .poison

/-- `SUBS x y` (`SUBSflags`). -/
def subs (ty : Ty) : List Val → Val
  | [a, b] => match reg a, reg b with
    | some x, some y => flagsTuple ty (subFlags x y)
    | _, _ => .poison
  | _ => .poison

/-- `ADDS x #c` (`ADDSconstflags`). -/
def addsConst (ty : Ty) (k : Int64) : List Val → Val
  | [a] => match reg a with
    | some x => flagsTuple ty (addWithCarry x (imm k) false)
    | none => .poison
  | _ => .poison

/-- `NEGS x` = `SUBS ZR, x`. -/
def negs (ty : Ty) : List Val → Val
  | [a] => match reg a with
    | some x => flagsTuple ty (subFlags 0 x)
    | none => .poison
  | _ => .poison

/-- `ADCS x y` with carry-in `PSTATE.C` of `f`. -/
def adcs (ty : Ty) : List Val → Val
  | [a, b, f] => match reg a, reg b, carry f with
    | some x, some y, some c => flagsTuple ty (addWithCarry x y c)
    | _, _, _ => .poison
  | _ => .poison

/-- `SBCS x y` = `AddWithCarry(x, NOT y, C)`. -/
def sbcs (ty : Ty) : List Val → Val
  | [a, b, f] => match reg a, reg b, carry f with
    | some x, some y, some c => flagsTuple ty (addWithCarry x (~~~y) c)
    | _, _, _ => .poison
  | _ => .poison

/-- `ADC ZR, ZR` (`ADCzerocarry`): the carry. -/
def adcZero (ty : Ty) : List Val → Val
  | [f] => match carry f with
    | some c => res ty (if c then 1 else 0)
    | none => .poison
  | _ => .poison

/-- `NGC ZR` (`NGCzerocarry`) = `SBC ZR, ZR, ZR`: −1 if borrowing (`C` clear), else 0. -/
def ngcZero (ty : Ty) : List Val → Val
  | [f] => match carry f with
    | some c => res ty (if c then 0 else -1)
    | none => .poison
  | _ => .poison

/-! ## Conditional ops -/

/-- The condition of a `CCop` auxint on a flags value. -/
def condOn (k : Int64) (f : Val) : Option Bool := (Cond.ofAux k).bind (·.onVal f)

/-- `CSEL [cc] x y f` and its variants: `x` if the condition holds, else `g y` (`CSEL`:
`y` itself, `CSINC` `y + 1`, `CSINV` `NOT y`, `CSNEG` `−y`). -/
def csel (ty : Ty) (k : Int64) (g : Option (BitVec 64 → BitVec 64)) : List Val → Val
  | [x, y, f] => match condOn k f with
    | some true => regVal ty x
    | some false => match g with
      | none => regVal ty y
      | some g => match reg y with
        | some r => res ty (g r)
        | none => .poison
    | none => .poison
  | _ => .poison

/-- `CSINC [cc] x y f`: `x` if the condition holds, else `y + 1` with `ADDconst`'s provenance
case of a pointer `y` (`addP`: `(CSEL [cc] x (ADDconst [1] y) f)` moves it by 1). -/
def csinc (ty : Ty) (k : Int64) : List Val → Val
  | [x, y, f] => match condOn k f with
    | some true => regVal ty x
    | some false => addP ty y 1
    | none => .poison
  | _ => .poison

/-- `CSEL [cc] x ZR f` (`CSEL0`). -/
def csel0 (ty : Ty) (k : Int64) : List Val → Val
  | [x, f] => match condOn k f with
    | some true => regVal ty x
    | some false => res ty 0
    | none => .poison
  | _ => .poison

/-- `CSETM [cc] f`: −1 or 0. -/
def csetm (ty : Ty) (k : Int64) : List Val → Val
  | [f] => match condOn k f with
    | some b => res ty (if b then -1 else 0)
    | none => .poison
  | _ => .poison

/-- `Equal`, `LessThanU`, … (`CSET` of the op's condition): the boolean, or 0/1 at an integer
shape. -/
def cset (ty : Ty) (op : Op) : List Val → Val
  | [f] => match (Cond.ofOp op).bind (·.onVal f) with
    | some b => res ty (if b then 1 else 0)
    | none => .poison
  | _ => .poison

/-- An `ARM64ConditionalParams` auxint: condition, fallback `#nzcv`, immediate and whether the
immediate is used (`rewrite.go` `auxIntToArm64ConditionalParams`). -/
def condParams (k : Int64) : Option Cond × Flags × Nat :=
  let n := k.toInt.toNat
  ((Op.ofGoNum? (n % 65536)).bind Cond.ofOp, Flags.ofNZCV (n / 65536 % 16), n / 1048576 % 32)

/-- `CCMP`/`CCMN` (`neg`: compare with the negated operand, `AddWithCarry(x, y, 0)`) on 64 or 32
bits (`w32`), the second operand `y` or the auxint's immediate (`konst`): the comparison's flags if
the condition holds on `f`, else the fallback. -/
def ccmp (neg w32 konst : Bool) (k : Int64) : List Val → Val
  | args =>
    let (c?, fb, i) := condParams k
    let ops : Option (Val × Val × Val) := match konst, args with
      | true, [a, f] => some (a, .int .w64 (BitVec.ofNat 64 i), f)
      | false, [a, b, f] => some (a, b, f)
      | _, _ => none
    match ops, c? with
    | some (a, b, f), some c =>
      match c.onVal f with
      | some true =>
        if w32 then
          match reg32 a, reg32 b with
          | some x, some y => (if neg then cmnFlags x y else (subFlags x y).2).toVal
          | _, _ => .poison
        else
          match reg a, reg b with
          | some x, some y => (if neg then cmnFlags x y else (subFlags x y).2).toVal
          | _, _ => .poison
      | some false => fb.toVal
      | none => .poison
    | _, _ => .poison

end GoFV.SSA.Sem.Arm64
