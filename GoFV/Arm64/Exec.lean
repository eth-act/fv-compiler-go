import GoFV.Arm64.Decode
import GoFV.SSA.Sem.Arm64.Int
import GoFV.SSA.Sem.Arm64.Float

/-!
# Executing ARM64 instructions (`docs/plans/semantics3.md` §3 (a))

`exec : Insn → MState → Except Fault MState`, the pseudocode of each class of `Insn` (Arm ARM,
DDI 0487, C6 "A64 base instruction descriptions", C7 "SIMD and floating-point") on `MState`,
and `step`, which fetches from the read-only `Code`, decodes and executes. The data operations
are Phase 2's (`GoFV/SSA/Sem/Arm64/*`, `GoFV/SSA/Sem/Flags.lean`, `GoFV.IEEE`), so the
agreement of `evalArm64` with the instruction an op is emitted as is unfolding:
`addWithCarry` (`AddWithCarry`), `Cond.holds` (`ConditionHolds`), `Shift.apply`
(`ShiftReg`), `extr`, `smulh`/`umulh`, `sdiv`/`udiv`, `clz`/`rbit`/`rev`/`rev16`, `vcnt`/
`vuaddlv`, `sext`/`mask`, `fcmpFlags` (the `FPCompare` outcome), and `GoFV.IEEE`'s `add`, `sub`,
`mul`, `div`, `sqrt`, `mulAdd`, `max`, `min`, `roundInt`, `convert`, `toFixed`, `fromFixed`
with `FPCR = 0` (round to nearest even except where the instruction fixes the mode).

Machine choices (§3, §6 of the plan):

* Memory accesses fault only in the nil page (`nilPage`); a fault leaves no state.
* One core: `LDAXR`/`LDXR` set no monitor and `STLXR`/`STXR` always succeed (status 0);
  acquire/release orderings and barriers have no effect; `NOP` and `PRFM` do nothing (a `PRFM`
  never faults).
* `BRK`, `UDF` and words outside the subset are `Fault.undefined`.
* Scalar FP and SIMD writes zero the upper bits of the destination `V` register.
-/

namespace GoFV.Arm64

open GoFV.SSA.Sem (Flags addWithCarry logicFlags Cond)
open GoFV.SSA.Sem.Arm64 (Shift sext mask extr smulh umulh clz rbit rev rev16 vcnt vuaddlv
  fcmpFlags)
open GoFV.IEEE (Fmt RMode)

/-! ## Helpers -/

/-- The condition of an encoding's `cond` field. -/
def condOf (c : BitVec 4) : Cond :=
  match c.toNat with
  | 0 => .eq | 1 => .ne | 2 => .hs | 3 => .lo | 4 => .mi | 5 => .pl | 6 => .vs | 7 => .vc
  | 8 => .hi | 9 => .ls | 10 => .ge | 11 => .lt | 12 => .gt | 13 => .le | 14 => .al | _ => .nv

/-- `ConditionHolds(cond)` on the state's flags. -/
def MState.holds (s : MState) (c : BitVec 4) : Bool := (condOf c).holds s.nzcv

/-- The shift kind of a `shift` field (`DecodeShift`). -/
def shiftOf (k : BitVec 2) : Shift :=
  match k.toNat with
  | 0 => .ll | 1 => .rl | 2 => .ra | _ => .ro

/-- A width-generic integer computation at the datasize `sf` selects, zero-extended to 64 bits
(`ext` reads an operand at that width). -/
@[inline] def sized (sf : Bool) (f : (n : Nat) → (BitVec 64 → BitVec n) → BitVec n) : BitVec 64 :=
  if sf then f 64 (·.setWidth 64) else (f 32 (·.setWidth 32)).setWidth 64

/-- `sized` for computations that also produce flags. -/
@[inline] def sizedF (sf : Bool) (f : (n : Nat) → (BitVec 64 → BitVec n) → BitVec n × Flags) :
    BitVec 64 × Flags :=
  if sf then f 64 (·.setWidth 64) else
    let r := f 32 (·.setWidth 32)
    (r.1.setWidth 64, r.2)

/-- `ExtendReg(m, option, shift)` at 64 bits (the caller truncates to the datasize). -/
def extendReg (x : BitVec 64) (option : BitVec 3) (shift : Nat) : BitVec 64 :=
  let len := 8 * 2 ^ (option.toNat % 4)
  (if option.getLsbD 2 then sext len x else x &&& mask len) <<< shift

/-- The flags of `NZCV` as a 4-bit field (`N` bit 3). -/
def flagsOfNZCV (k : BitVec 4) : Flags := Flags.ofNZCV k.toNat

/-- `n` bytes at `a`, or the nil-page fault. -/
def load (s : MState) (a : BitVec 64) (n : Nat) : Except Fault (BitVec (8 * n)) :=
  if nilPage a then .error (.nilPage a) else .ok (readMem s.mem a n)

/-- Store `n` bytes at `a`, or the nil-page fault. -/
def store (s : MState) (a : BitVec 64) (n : Nat) (val : BitVec (8 * n)) : Except Fault MState :=
  if nilPage a then .error (.nilPage a) else .ok { s with mem := writeMem s.mem a n val }

/-- The state with the PC advanced past the instruction. -/
def MState.next (s : MState) : MState := { s with pc := s.pc + 4 }

/-! ## Integer data processing -/

/-- `ADD`/`SUB` (`sub`: `AddWithCarry(x, NOT y, 1)`) at the datasize. -/
def addSub (sf sub : Bool) (x y : BitVec 64) : BitVec 64 × Flags :=
  sizedF sf fun _ e => if sub then addWithCarry (e x) (~~~(e y)) true else addWithCarry (e x) (e y) false

/-- Write an add/sub result: to `Rd` (SP for index 31 unless flags are set, `spDest`), and the
flags if `setf`. -/
def MState.addSubResult (s : MState) (setf spDest : Bool) (rd : Reg) (r : BitVec 64 × Flags) :
    MState :=
  if setf then { s.wX rd r.1 with nzcv := r.2 }
  else if spDest then s.wXsp rd r.1 else s.wX rd r.1

/-- `AND`/`ORR`/`EOR`/`ANDS` (`opc`) of two operands at the datasize, with `ANDS`' flags. -/
def logical (sf : Bool) (opc : BitVec 2) (x y : BitVec 64) : BitVec 64 × Flags :=
  sizedF sf fun _ e =>
    let r := match opc.toNat with
      | 0 => e x &&& e y | 1 => e x ||| e y | 2 => e x ^^^ e y | _ => e x &&& e y
    (r, logicFlags r)

/-- `SBFM`/`BFM`/`UBFM` (Arm ARM C6 "SBFM": `bot`, `top`, the two masks). -/
def bitfieldMove (sf : Bool) (opc : BitVec 2) (immr imms : BitVec 6) (dst src : BitVec 64) :
    BitVec 64 :=
  sized sf fun n e =>
    match decodeBitMasks n sf imms immr false with
    | none => 0
    | some (wmask, tmask) =>
      let inzero := opc != 1
      let extend := opc = 0
      let d : BitVec n := if inzero then 0 else e dst
      let x := e src
      let bot := (d &&& ~~~wmask) ||| (x.rotateRight immr.toNat &&& wmask)
      let top : BitVec n := if extend then (if x.getLsbD imms.toNat then -1 else 0) else d
      (top &&& ~~~tmask) ||| (bot &&& tmask)

/-- `REV32` of a 64-bit register: the bytes of each word reversed. -/
def rev32 (x : BitVec 64) : BitVec 64 :=
  (rev (x.extractLsb' 32 32) ++ rev (x.extractLsb' 0 32))

/-- `CLS`: `CountLeadingZeroBits(x<n-1:1> EOR x<n-2:0>)`, the leading bits equal to the sign
bit, not counting the sign bit itself (`x ^^^ x.sshiftRight 1` has bit `n - 1` clear and bit
`i` = `x<i+1> EOR x<i>`). -/
def cls {n : Nat} (x : BitVec n) : BitVec n :=
  BitVec.ofNat n ((x ^^^ x.sshiftRight 1).clz.toNat - 1)

/-- Data-processing (1 source). -/
def dp1Op (sf : Bool) (opc : BitVec 3) (x : BitVec 64) : BitVec 64 :=
  match opc.toNat with
  | 0 => sized sf fun _ e => rbit (e x)
  | 1 => sized sf fun _ e => rev16 (e x)
  | 2 => if sf then rev32 x else (rev (x.setWidth 32)).setWidth 64
  | 3 => rev x
  | 4 => sized sf fun _ e => clz (e x)
  | _ => sized sf fun _ e => cls (e x)

/-- Data-processing (2 source): division (by zero 0) and variable shifts (the amount modulo the
datasize). -/
def dp2Op (sf : Bool) (opc : BitVec 6) (x y : BitVec 64) : BitVec 64 :=
  sized sf fun n e =>
    match opc.toNat with
    | 2 => e x / e y
    | 3 => (e x).sdiv (e y)
    | 8 => Shift.apply .ll (e x) (e y).toNat
    | 9 => Shift.apply .rl (e x) (e y).toNat
    | 10 => Shift.apply .ra (e x) (e y).toNat
    | _ => Shift.apply .ro (e x) (e y).toNat

/-- Data-processing (3 source). -/
def dp3Op (sf : Bool) (op31 : BitVec 3) (o0 : Bool) (a x y : BitVec 64) : BitVec 64 :=
  match op31.toNat with
  | 0 => sized sf fun _ e => if o0 then e a - e x * e y else e a + e x * e y
  | 1 =>
    let p := (x.setWidth 32).signExtend 64 * (y.setWidth 32).signExtend 64
    if o0 then a - p else a + p
  | 5 =>
    let p := (x.setWidth 32).setWidth 64 * (y.setWidth 32).setWidth 64
    if o0 then a - p else a + p
  | 2 => smulh x y
  | _ => umulh x y

/-! ## Floating point -/

/-- A binary operation on the scalar operands of `ftype` (00 single, 01 double) of two `V`
registers, the result zero-extended to the register. -/
@[inline] def fpBin (ftype : BitVec 2)
    (g : (f : Fmt) → GoFV.IEEE.Bits f → GoFV.IEEE.Bits f → GoFV.IEEE.Bits f)
    (x y : BitVec 128) : BitVec 128 :=
  if ftype = 0 then (g Fmt.b32 (x.setWidth 32) (y.setWidth 32)).setWidth 128
  else (g Fmt.b64 (x.setWidth 64) (y.setWidth 64)).setWidth 128

/-- `fpBin` for unary operations. -/
@[inline] def fpUn (ftype : BitVec 2) (g : (f : Fmt) → GoFV.IEEE.Bits f → GoFV.IEEE.Bits f)
    (x : BitVec 128) : BitVec 128 :=
  if ftype = 0 then (g Fmt.b32 (x.setWidth 32)).setWidth 128
  else (g Fmt.b64 (x.setWidth 64)).setWidth 128

/-- Floating-point data-processing (1 source). -/
def fp1Op (ftype : BitVec 2) (opc : BitVec 6) (x : BitVec 128) : BitVec 128 :=
  let ri (rm : RMode) := fpUn ftype fun f => GoFV.IEEE.roundInt f rm
  match opc.toNat with
  | 0 => fpUn ftype (fun _ a => a) x
  | 1 => fpUn ftype GoFV.IEEE.abs x
  | 2 => fpUn ftype GoFV.IEEE.neg x
  | 3 => fpUn ftype (fun f => GoFV.IEEE.sqrt f .rne) x
  | 4 => (GoFV.IEEE.convert Fmt.b64 Fmt.b32 .rne (x.setWidth 64)).setWidth 128
  | 5 => (GoFV.IEEE.convert Fmt.b32 Fmt.b64 .rne (x.setWidth 32)).setWidth 128
  | 8 => ri .rne x
  | 9 => ri .rpi x
  | 10 => ri .rmi x
  | 11 => ri .rz x
  | 12 => ri .rna x
  | _ => ri .rne x

/-- Floating-point data-processing (2 source); operands in encoding order (`Rn`, `Rm`). -/
def fp2Op (ftype : BitVec 2) (opc : BitVec 4) (x y : BitVec 128) : BitVec 128 :=
  match opc.toNat with
  | 0 => fpBin ftype (fun f => GoFV.IEEE.mul f .rne) x y
  | 1 => fpBin ftype (fun f => GoFV.IEEE.div f .rne) x y
  | 2 => fpBin ftype (fun f => GoFV.IEEE.add f .rne) x y
  | 3 => fpBin ftype (fun f => GoFV.IEEE.sub f .rne) x y
  | 4 => fpBin ftype (fun f => GoFV.IEEE.max f .rne) x y
  | 5 => fpBin ftype (fun f => GoFV.IEEE.min f .rne) x y
  | _ => fpBin ftype (fun f a b => GoFV.IEEE.neg f (GoFV.IEEE.mul f .rne a b)) x y

/-- `FMADD`/`FMSUB`/`FNMADD`/`FNMSUB`: `FPMulAdd(a', n', m)` with `a` negated if `o1` and `n`
negated if `o1 ≠ o0` (Arm ARM C7 "FMADD": `op1_neg`, `opa_neg`). -/
def fp3Op (ftype : BitVec 2) (o1 o0 : Bool) (a n m : BitVec 128) : BitVec 128 :=
  let go (f : Fmt) (a n m : GoFV.IEEE.Bits f) : GoFV.IEEE.Bits f :=
    let a := if o1 then GoFV.IEEE.neg f a else a
    let n := if o1 != o0 then GoFV.IEEE.neg f n else n
    GoFV.IEEE.mulAdd f .rne a n m
  if ftype = 0 then (go Fmt.b32 (a.setWidth 32) (n.setWidth 32) (m.setWidth 32)).setWidth 128
  else (go Fmt.b64 (a.setWidth 64) (n.setWidth 64) (m.setWidth 64)).setWidth 128

/-- `VFPExpandImm(imm8)` for single (`ftype` 00) or double precision. -/
def vfpExpandImm (ftype : BitVec 2) (imm8 : BitVec 8) : BitVec 128 :=
  let sign := if imm8.getLsbD 7 then 1 else 0
  let b6 := imm8.getLsbD 6
  let e54 := (imm8.toNat / 16) % 4
  let frac := imm8.toNat % 16
  if ftype = 0 then
    let exp := (if b6 then 0 else 128) + (if b6 then 31 * 4 else 0) + e54
    BitVec.ofNat 128 (sign * 2 ^ 31 + exp * 2 ^ 23 + frac * 2 ^ 19)
  else
    let exp := (if b6 then 0 else 1024) + (if b6 then 255 * 4 else 0) + e54
    BitVec.ofNat 128 (sign * 2 ^ 63 + exp * 2 ^ 52 + frac * 2 ^ 48)

/-- `FCMP` flags. -/
def fcmpOp (ftype : BitVec 2) (x y : BitVec 128) : Flags :=
  if ftype = 0 then fcmpFlags (GoFV.IEEE.compare Fmt.b32 (x.setWidth 32) (y.setWidth 32))
  else fcmpFlags (GoFV.IEEE.compare Fmt.b64 (x.setWidth 64) (y.setWidth 64))

/-! ## Loads and stores -/

/-- Bytes accessed by a single-register load/store (`8 << size`, 16 for the SIMD&FP `Q` form). -/
def accessBytes (size : BitVec 2) (vec : Bool) (opc : BitVec 2) : Nat :=
  if vec && size = 0 && opc.getLsbD 1 then 16 else 2 ^ size.toNat

/-- Load `n` bytes into `Rt` (`opc` 01 zero-extend, 10 sign-extend to 64, 11 sign-extend to 32)
or into `Vt` (zero-extended). -/
def MState.loadInto (s : MState) (vec : Bool) (opc : BitVec 2) (n : Nat) (rt : Reg)
    (data : BitVec (8 * n)) : MState :=
  if vec then s.wV rt (data.setWidth 128)
  else
    let x : BitVec 64 := data.setWidth 64
    match opc.toNat with
    | 2 => s.wX rt (sext (8 * n) x)
    | 3 => s.wX rt ((sext (8 * n) x).setWidth 32 |>.setWidth 64)
    | _ => s.wX rt x

/-- The value a store of `Rt`/`Vt` writes (`n` bytes). -/
def MState.storeVal (s : MState) (vec : Bool) (n : Nat) (rt : Reg) : BitVec (8 * n) :=
  if vec then (s.v rt).setWidth (8 * n) else (s.rX rt).setWidth (8 * n)

/-- Effective address and base write-back of a single-register addressing mode
(`n` the access size in bytes). -/
def MState.amode (s : MState) (mode : AMode) (rn : Reg) (n : Nat) :
    BitVec 64 × Option (BitVec 64) :=
  let base := s.rXsp rn
  match mode with
  | .uimm imm12 => (base + BitVec.ofNat 64 (imm12.toNat * n), none)
  | .simm imm9 idx =>
    let off := imm9.signExtend 64
    match idx with
    | .unscaled => (base + off, none)
    | .post => (base, some (base + off))
    | .pre => (base + off, some (base + off))
  | .reg rm option sc =>
    (base + extendReg (s.rX rm) option (if sc then Nat.log2 n else 0), none)

/-- Single-register load/store. -/
def execLdSt (s : MState) (size : BitVec 2) (vec : Bool) (opc : BitVec 2) (mode : AMode)
    (rn rt : Reg) : Except Fault MState := do
  let n := accessBytes size vec opc
  let (a, wb) := s.amode mode rn n
  let s' ← if !vec && size = 3 && opc = 2 then pure s  -- PRFM
    else if (if vec then opc.getLsbD 0 else opc != 0) then
      let d ← load s a n
      pure (s.loadInto vec opc n rt d)
    else store s a n (s.storeVal vec n rt)
  let s' := match wb with
    | some b => s'.wXsp rn b
    | none => s'
  pure s'.next

/-- Load/store pair. -/
def execPair (s : MState) (opc : BitVec 2) (vec : Bool) (mode : BitVec 2) (ld : Bool)
    (imm7 : BitVec 7) (rt2 rn rt : Reg) : Except Fault MState := do
  let n := if vec then 4 * 2 ^ opc.toNat else (if opc.getLsbD 1 then 8 else 4)
  let base := s.rXsp rn
  let off := imm7.signExtend 64 * BitVec.ofNat 64 n
  let a := if mode = 1 then base else base + off
  let s' ← if ld then do
      let d1 ← load s a n
      let d2 ← load s (a + BitVec.ofNat 64 n) n
      let lopc : BitVec 2 := if !vec && opc = 1 then 2 else 1
      pure ((s.loadInto vec lopc n rt d1).loadInto vec lopc n rt2 d2)
    else do
      let s1 ← store s a n (s.storeVal vec n rt)
      store s1 (a + BitVec.ofNat 64 n) n (s.storeVal vec n rt2)
  let s' := if mode = 2 then s' else s'.wXsp rn (base + off)
  pure s'.next

/-- LSE atomic memory operations (`LDADD`, `LDCLR`, `LDEOR`, `LDSET`, `SWP`): the old value to
`Rt`, the combination with `Rs` stored. -/
def execAtomic (s : MState) (size : BitVec 2) (rs : Reg) (o3 : Bool) (opc : BitVec 3)
    (rn rt : Reg) : Except Fault MState := do
  let n := 2 ^ size.toNat
  let a := s.rXsp rn
  let old ← load s a n
  let v : BitVec (8 * n) := (s.rX rs).setWidth (8 * n)
  let nw := if o3 then v else match opc.toNat with
    | 0 => old + v | 1 => old &&& ~~~v | 2 => old ^^^ v | _ => old ||| v
  let s' ← store s a n nw
  pure (s'.wX rt (old.setWidth 64)).next

/-- `CAS`: compare `Rs` with memory, store `Rt` if equal; `Rs` receives the old value. -/
def execCas (s : MState) (size : BitVec 2) (rs rn rt : Reg) : Except Fault MState := do
  let n := 2 ^ size.toNat
  let a := s.rXsp rn
  let old ← load s a n
  let cmp : BitVec (8 * n) := (s.rX rs).setWidth (8 * n)
  let s' ← if old == cmp then store s a n ((s.rX rt).setWidth (8 * n)) else pure s
  pure (s'.wX rs (old.setWidth 64)).next

/-- Load/store exclusive and ordered. One core: an exclusive store succeeds (`Rs` = 0). -/
def execExcl (s : MState) (size : BitVec 2) (o2 ld : Bool) (rs rn rt : Reg) :
    Except Fault MState := do
  let n := 2 ^ size.toNat
  let a := s.rXsp rn
  if ld then
    let d ← load s a n
    pure (s.wX rt (d.setWidth 64)).next
  else
    let s' ← store s a n ((s.rX rt).setWidth (8 * n))
    pure (if o2 then s' else s'.wX rs 0).next

/-! ## Execution -/

/-- The PC plus a sign-extended word offset. -/
@[inline] def MState.pcRel {k : Nat} (s : MState) (imm : BitVec k) : BitVec 64 :=
  s.pc + (imm ++ (0 : BitVec 2)).signExtend 64

/-- Branch to `t` if `c`, else fall through. -/
@[inline] def MState.branchIf (s : MState) (c : Bool) (t : BitVec 64) : MState :=
  if c then { s with pc := t } else s.next

/-- Execute one instruction. -/
def exec (i : Insn) (s : MState) : Except Fault MState :=
  match i with
  | .adr page imm rd =>
    let r := if page then (s.pc &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12)
      else s.pc + imm.signExtend 64
    pure (s.wX rd r).next
  | .addSubImm sf sub setf sh imm12 rn rd =>
    let imm : BitVec 64 := imm12.setWidth 64 <<< (if sh then 12 else 0)
    pure (s.addSubResult setf true rd (addSub sf sub (s.rXsp rn) imm)).next
  | .logImm sf opc n immr imms rn rd =>
    let imm : BitVec 64 := match decodeBitMasks (if sf then 64 else 32) n imms immr true with
      | some (w, _) => w.setWidth 64
      | none => 0
    let r := logical sf opc (s.rX rn) imm
    pure (if opc = 3 then { s.wX rd r.1 with nzcv := r.2 } else s.wXsp rd r.1).next
  | .movWide sf opc hw imm16 rd =>
    let sh := 16 * hw.toNat
    let r : BitVec 64 := match opc.toNat with
      | 0 => sized sf fun _ e => ~~~(e (imm16.setWidth 64 <<< sh))
      | 2 => imm16.setWidth 64 <<< sh
      | _ => sized sf fun _ e =>
        e ((s.rX rd &&& ~~~((0xFFFF : BitVec 64) <<< sh)) ||| (imm16.setWidth 64 <<< sh))
    pure (s.wX rd r).next
  | .bitfield sf opc immr imms rn rd =>
    pure (s.wX rd (bitfieldMove sf opc immr imms (s.rX rd) (s.rX rn))).next
  | .extr sf rm imms rn rd =>
    pure (s.wX rd (sized sf fun _ e => extr imms.toNat (e (s.rX rn)) (e (s.rX rm)))).next
  | .b link imm26 =>
    let s' := if link then s.wX 30 (s.pc + 4) else s
    pure { s' with pc := s.pcRel imm26 }
  | .bcond cond imm19 => pure (s.branchIf (s.holds cond) (s.pcRel imm19))
  | .cbz sf nz imm19 rt =>
    let z := (sized sf fun _ e => e (s.rX rt)) == 0
    pure (s.branchIf (z != nz) (s.pcRel imm19))
  | .tbz nz b imm14 rt => pure (s.branchIf ((s.rX rt).getLsbD b.toNat == nz) (s.pcRel imm14))
  | .br kind rn =>
    let t := s.rX rn
    let s' := if kind = .blr then s.wX 30 (s.pc + 4) else s
    pure { s' with pc := t }
  | .nop | .barrier .. => pure s.next
  | .brk imm16 => .error (.undefined (0xD4200000 ||| (imm16.setWidth 32 <<< 5)))
  | .udf imm16 => .error (.undefined (imm16.setWidth 32))
  | .logShift sf opc shift n rm imm6 rn rd =>
    let y := sized sf fun _ e => Shift.apply (shiftOf shift) (e (s.rX rm)) imm6.toNat
    let y := if n then sized sf fun _ e => ~~~(e y) else y
    let r := logical sf opc (s.rX rn) y
    pure (if opc = 3 then { s.wX rd r.1 with nzcv := r.2 } else s.wX rd r.1).next
  | .addSubShift sf sub setf shift rm imm6 rn rd =>
    let y := sized sf fun _ e => Shift.apply (shiftOf shift) (e (s.rX rm)) imm6.toNat
    pure (s.addSubResult setf false rd (addSub sf sub (s.rX rn) y)).next
  | .addSubExt sf sub setf rm option imm3 rn rd =>
    let y := extendReg (s.rX rm) option imm3.toNat
    pure (s.addSubResult setf true rd (addSub sf sub (s.rXsp rn) y)).next
  | .addSubCarry sf sub setf rm rn rd =>
    let r := sizedF sf fun _ e =>
      addWithCarry (e (s.rX rn)) (if sub then ~~~(e (s.rX rm)) else e (s.rX rm)) s.nzcv.c
    pure (s.addSubResult setf false rd r).next
  | .condCmp sf sub imm rm cond rn nzcv =>
    let y : BitVec 64 := if imm then rm.setWidth 64 else s.rX rm
    let f := if s.holds cond then (addSub sf sub (s.rX rn) y).2 else flagsOfNZCV nzcv
    pure { s with nzcv := f }.next
  | .condSel sf op op2 rm cond rn rd =>
    let r := if s.holds cond then sized sf fun _ e => e (s.rX rn)
      else sized sf fun _ e =>
        let y := e (s.rX rm)
        let y := if op then ~~~y else y
        if op2 then y + 1 else y
    pure (s.wX rd r).next
  | .dp1 sf opc rn rd => pure (s.wX rd (dp1Op sf opc (s.rX rn))).next
  | .dp2 sf opc rm rn rd => pure (s.wX rd (dp2Op sf opc (s.rX rn) (s.rX rm))).next
  | .dp3 sf op31 o0 rm ra rn rd =>
    pure (s.wX rd (dp3Op sf op31 o0 (s.rX ra) (s.rX rn) (s.rX rm))).next
  | .ldst size vec opc mode rn rt => execLdSt s size vec opc mode rn rt
  | .ldstPair opc vec mode ld imm7 rt2 rn rt => execPair s opc vec mode ld imm7 rt2 rn rt
  | .ldrLit opc vec imm19 rt => do
    let a := s.pcRel imm19
    if !vec && opc = 3 then pure s.next  -- PRFM (literal)
    else
      let n := if vec then 4 * 2 ^ opc.toNat else (if opc = 1 then 8 else 4)
      let d ← load s a n
      pure (s.loadInto vec (if !vec && opc = 2 then 2 else 1) n rt d).next
  | .ldstExcl size o2 ld _ rs rn rt => execExcl s size o2 ld rs rn rt
  | .cas size _ _ rs rn rt => execCas s size rs rn rt
  | .atomic size _ _ rs o3 opc rn rt => execAtomic s size rs o3 opc rn rt
  | .fp1 ftype opc rn rd => pure (s.wV rd (fp1Op ftype opc (s.v rn))).next
  | .fp2 ftype opc rm rn rd => pure (s.wV rd (fp2Op ftype opc (s.v rn) (s.v rm))).next
  | .fp3 ftype o1 o0 rm ra rn rd =>
    pure (s.wV rd (fp3Op ftype o1 o0 (s.v ra) (s.v rn) (s.v rm))).next
  | .fcmp ftype rm rn zero _ =>
    pure { s with nzcv := fcmpOp ftype (s.v rn) (if zero then 0 else s.v rm) }.next
  | .fmovImm ftype imm8 rd => pure (s.wV rd (vfpExpandImm ftype imm8)).next
  | .fcsel ftype rm cond rn rd =>
    let r := if s.holds cond then s.v rn else s.v rm
    pure (s.wV rd (fpUn ftype (fun _ a => a) r)).next
  | .fcvtInt sf ftype rmode opc rn rd =>
    let m := if sf then 64 else 32
    match rmode.toNat, opc.toNat with
    | 0, 6 => pure (s.wX rd (if ftype = 0 then (s.v rn).setWidth 32 |>.setWidth 64
        else (s.v rn).setWidth 64)).next
    | 0, 7 => pure (s.wV rd (if ftype = 0 then (s.rX rn).setWidth 32 |>.setWidth 128
        else (s.rX rn).setWidth 128)).next
    | 0, _ =>
      let x := (s.rX rn).setWidth m
      let u := opc = 3
      let r : BitVec 128 := if ftype = 0 then (GoFV.IEEE.fromFixed Fmt.b32 m x u .rne).setWidth 128
        else (GoFV.IEEE.fromFixed Fmt.b64 m x u .rne).setWidth 128
      pure (s.wV rd r).next
    | _, _ =>
      let u := opc = 1
      let r : BitVec 64 := if ftype = 0
        then (GoFV.IEEE.toFixed Fmt.b32 ((s.v rn).setWidth 32) u m .rz).setWidth 64
        else (GoFV.IEEE.toFixed Fmt.b64 ((s.v rn).setWidth 64) u m .rz).setWidth 64
      pure (s.wX rd r).next
  | .cnt8b rn rd => pure (s.wV rd ((vcnt ((s.v rn).setWidth 64)).setWidth 128)).next
  | .uaddlv8b rn rd => pure (s.wV rd ((vuaddlv ((s.v rn).setWidth 64)).setWidth 128)).next

/-- Fetch, decode and execute the instruction at the PC. -/
def step (code : Code) (s : MState) : Except Fault MState :=
  match code s.pc with
  | none => .error (.noCode s.pc)
  | some w => match decode w with
    | some i => exec i s
    | none => .error (.undefined w)

/-- `n` steps, stopping at the first fault. -/
def run (code : Code) : Nat → MState → Except Fault MState
  | 0, s => .ok s
  | n + 1, s => (step code s).bind (run code n)

end GoFV.Arm64
