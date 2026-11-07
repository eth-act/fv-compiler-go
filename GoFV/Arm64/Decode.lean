import GoFV.Arm64.Insn

/-!
# Decoding ARM64 words (`docs/plans/semantics3.md` §3 (a))

`decode : BitVec 32 → Option Insn`, written from the encoding diagrams of the Arm ARM (DDI 0487,
C4.1) for the classes of `Insn`. A word decodes to `some i` only if it is an allocated encoding
of that class whose behaviour `exec` defines (`decode` rejects the unallocated and reserved
combinations inside a class, e.g. `sf = 0` with `N = 1` or a shift amount ≥ 32, encodings whose
should-be-one/zero fields do not hold (`SMULH`'s `Ra`, `FCMP #0.0`'s `Rm`, the exclusives'
`Rt2`), and the encodings outside the emitted subset, e.g. half-precision `ftype = 11`); every
other word is `none`, which the machine treats as `UNDEFINED` (`Fault.undefined`).

`decodeBitMasks` (the Arm ARM's `DecodeBitMasks`, shared/functions/integer) is here because the
logical-immediate class is only allocated where it is defined.
-/

namespace GoFV.Arm64

/-- `len` bits of `w` from bit `lo`. -/
@[inline] def fld (w : BitVec 32) (lo len : Nat) : BitVec len := w.extractLsb' lo len

/-- Bit `i` of `w`. -/
@[inline] def bit (w : BitVec 32) (i : Nat) : Bool := w.getLsbD i

/-- `HighestSetBit` of a 7-bit value. -/
def highestSetBit (x : BitVec 7) : Option Nat := [6, 5, 4, 3, 2, 1, 0].find? (x.getLsbD ·)

/-- The `M`-bit value repeating the `e`-bit element `x` (`Replicate`; `e` divides `M`). -/
def replicateTo (M e : Nat) (x : Nat) : BitVec M :=
  BitVec.ofNat M ((List.range (M / e)).foldl (fun acc i => acc + x * 2 ^ (i * e)) 0)

/-- `DecodeBitMasks(immN, imms, immr, immediate, M)`: `(wmask, tmask)`, or `none` where the Arm
ARM says `UNDEFINED` (no element size, an element wider than `M`, or an all-ones immediate). -/
def decodeBitMasks (M : Nat) (immN : Bool) (imms immr : BitVec 6) (immediate : Bool) :
    Option (BitVec M × BitVec M) := do
  let len ← highestSetBit ((BitVec.ofBool immN) ++ ~~~imms)
  if len < 1 then none
  let esize := 2 ^ len
  if M < esize then none
  let levels := esize - 1
  let s := imms.toNat &&& levels
  let r := immr.toNat &&& levels
  if immediate && s == levels then none
  let d := (s + esize - r) % esize
  let welem : BitVec esize := BitVec.ofNat esize (2 ^ (s + 1) - 1)
  let telem : Nat := 2 ^ (d + 1) - 1
  pure (replicateTo M esize (welem.rotateRight r).toNat, replicateTo M esize telem)

/-- Data processing, immediate (op0 = 100x). -/
def decodeDPImm (w : BitVec 32) : Option Insn :=
  let sf := bit w 31
  let rd := fld w 0 5
  let rn := fld w 5 5
  if w &&& 0x1F000000 == 0x10000000 then
    some (.adr (bit w 31) (fld w 5 19 ++ fld w 29 2) rd)
  else if w &&& 0x1F800000 == 0x11000000 then
    some (.addSubImm sf (bit w 30) (bit w 29) (bit w 22) (fld w 10 12) rn rd)
  else if w &&& 0x1F800000 == 0x12000000 then
    let n := bit w 22
    let immr := fld w 16 6
    let imms := fld w 10 6
    if !sf && n then none
    else if (decodeBitMasks (if sf then 64 else 32) n imms immr true).isNone then none
    else some (.logImm sf (fld w 29 2) n immr imms rn rd)
  else if w &&& 0x1F800000 == 0x12800000 then
    let opc := fld w 29 2
    let hw := fld w 21 2
    if opc = 1 || (!sf && hw.getLsbD 1) then none
    else some (.movWide sf opc hw (fld w 5 16) rd)
  else if w &&& 0x1F800000 == 0x13000000 then
    let opc := fld w 29 2
    let n := bit w 22
    let immr := fld w 16 6
    let imms := fld w 10 6
    if opc = 3 || n != sf || (!sf && (immr.getLsbD 5 || imms.getLsbD 5)) then none
    else some (.bitfield sf opc immr imms rn rd)
  else if w &&& 0x7FA00000 == 0x13800000 then
    let n := bit w 22
    let imms := fld w 10 6
    if n != sf || (!sf && imms.getLsbD 5) then none
    else some (.extr sf (fld w 16 5) imms rn rd)
  else none

/-- Branches, exception generation and system instructions (op0 = 101x). -/
def decodeBranch (w : BitVec 32) : Option Insn :=
  if w &&& 0x7C000000 == 0x14000000 then some (.b (bit w 31) (fld w 0 26))
  else if w &&& 0x7E000000 == 0x34000000 then
    some (.cbz (bit w 31) (bit w 24) (fld w 5 19) (fld w 0 5))
  else if w &&& 0x7E000000 == 0x36000000 then
    some (.tbz (bit w 24) (fld w 31 1 ++ fld w 19 5) (fld w 5 14) (fld w 0 5))
  else if w &&& 0xFF000010 == 0x54000000 then some (.bcond (fld w 0 4) (fld w 5 19))
  else if w &&& 0xFFFFFC1F == 0xD61F0000 then some (.br .br (fld w 5 5))
  else if w &&& 0xFFFFFC1F == 0xD63F0000 then some (.br .blr (fld w 5 5))
  else if w &&& 0xFFFFFC1F == 0xD65F0000 then some (.br .ret (fld w 5 5))
  else if w == 0xD503201F then some .nop
  else if w &&& 0xFFFFF01F == 0xD503301F then
    let op2 := fld w 5 3
    -- CLREX (010), DSB (100), DMB (101), ISB (110)
    if op2 = 2 || op2 = 4 || op2 = 5 || op2 = 6 then some (.barrier op2 (fld w 8 4)) else none
  else if w &&& 0xFFE0001F == 0xD4200000 then some (.brk (fld w 5 16))
  else none

/-- Loads and stores (op0 = x1x0). -/
def decodeLdSt (w : BitVec 32) : Option Insn :=
  let size := fld w 30 2
  let vec := bit w 26
  let opc := fld w 22 2
  let rt := fld w 0 5
  let rn := fld w 5 5
  -- the (size, V, opc) combinations of the single-register classes that are allocated
  let okSingle : Bool :=
    if vec then size = 0 || !opc.getLsbD 1
    else !(size = 3 && opc = 3) && !(size = 2 && opc = 3)
  if w &&& 0x3F000000 == 0x08000000 then
    let o2 := bit w 23
    let load := bit w 22
    let o1 := bit w 21
    let o0 := bit w 15
    let rs := fld w 16 5
    if fld w 10 5 != 31 then none
    else if o2 && o1 then
      -- CAS (size 00..11, o2 = 1, o1 = 1): L = bit 22, o0 = bit 15
      some (.cas size load o0 rs rn rt)
    else if o1 then none
    else if o2 && !o0 then none  -- LDLAR/STLLR (LORegions) not modelled
    else if !o2 && load && rs != 31 then none
    else if o2 && rs != 31 then none
    else some (.ldstExcl size o2 load o0 rs rn rt)
  else if w &&& 0x3B000000 == 0x18000000 then
    -- the literal class's `opc` is bits 31:30
    if vec && size = 3 then none else some (.ldrLit size vec (fld w 5 19) rt)
  else if w &&& 0x3A000000 == 0x28000000 then
    let mode := fld w 23 2
    let load := bit w 22
    -- the pair's `opc` is bits 31:30 (the single-register classes' `size` field)
    if mode = 0 || size = 3 then none
    else if !vec && size = 1 && !load then none
    else some (.ldstPair size vec mode load (fld w 15 7) (fld w 10 5) rn rt)
  else if w &&& 0x3B000000 == 0x39000000 then
    if okSingle then some (.ldst size vec opc (.uimm (fld w 10 12)) rn rt) else none
  else if w &&& 0x3B200000 == 0x38000000 then
    let idx? : Option Idx := match (fld w 10 2).toNat with
      | 0 => some .unscaled | 1 => some .post | 3 => some .pre | _ => none
    match idx? with
    | some idx =>
      if !okSingle then none
      else if idx != .unscaled && !vec && size = 3 && opc = 2 then none
      else some (.ldst size vec opc (.simm (fld w 12 9) idx) rn rt)
    | none => none
  else if w &&& 0x3B200C00 == 0x38200800 then
    let option := fld w 13 3
    if !okSingle || !option.getLsbD 1 then none
    else some (.ldst size vec opc (.reg (fld w 16 5) option (bit w 12)) rn rt)
  else if w &&& 0x3F200C00 == 0x38200000 then
    let o3 := bit w 15
    let aopc := fld w 12 3
    if (o3 && aopc != 0) || (!o3 && aopc.getLsbD 2) then none
    else some (.atomic size (bit w 23) (bit w 22) (fld w 16 5) o3 aopc rn rt)
  else none

/-- Data processing, register (op0 = x101). -/
def decodeDPReg (w : BitVec 32) : Option Insn :=
  let sf := bit w 31
  let rd := fld w 0 5
  let rn := fld w 5 5
  let rm := fld w 16 5
  if w &&& 0x1F000000 == 0x0A000000 then
    let imm6 := fld w 10 6
    if !sf && imm6.getLsbD 5 then none
    else some (.logShift sf (fld w 29 2) (fld w 22 2) (bit w 21) rm imm6 rn rd)
  else if w &&& 0x1F200000 == 0x0B000000 then
    let shift := fld w 22 2
    let imm6 := fld w 10 6
    if shift = 3 || (!sf && imm6.getLsbD 5) then none
    else some (.addSubShift sf (bit w 30) (bit w 29) shift rm imm6 rn rd)
  else if w &&& 0x1FE00000 == 0x0B200000 then
    let imm3 := fld w 10 3
    if imm3.toNat > 4 then none
    else some (.addSubExt sf (bit w 30) (bit w 29) rm (fld w 13 3) imm3 rn rd)
  else if w &&& 0x1FE0FC00 == 0x1A000000 then
    some (.addSubCarry sf (bit w 30) (bit w 29) rm rn rd)
  else if w &&& 0x3FE00410 == 0x3A400000 then
    some (.condCmp sf (bit w 30) (bit w 11) rm (fld w 12 4) rn (fld w 0 4))
  else if w &&& 0x3FE00800 == 0x1A800000 then
    some (.condSel sf (bit w 30) (bit w 10) rm (fld w 12 4) rn rd)
  else if w &&& 0x7FFFE000 == 0x5AC00000 then
    let opc := fld w 10 3
    if opc.toNat > 5 || (!sf && opc = 3) then none else some (.dp1 sf opc rn rd)
  else if w &&& 0x7FE00000 == 0x1AC00000 then
    let opc := fld w 10 6
    if [2, 3, 8, 9, 10, 11].contains opc.toNat then some (.dp2 sf opc rm rn rd) else none
  else if w &&& 0x7F000000 == 0x1B000000 then
    let op31 := fld w 21 3
    let o0 := bit w 15
    let ra := fld w 10 5
    match op31.toNat with
    | 0 => some (.dp3 sf op31 o0 rm ra rn rd)
    | 1 | 5 => if sf then some (.dp3 sf op31 o0 rm ra rn rd) else none
    | 2 | 6 => if sf && !o0 && ra = 31 then some (.dp3 sf op31 o0 rm ra rn rd) else none
    | _ => none
  else none

/-- Scalar floating point and the two SIMD forms the compiler emits (op0 = x111). -/
def decodeFP (w : BitVec 32) : Option Insn :=
  let ftype := fld w 22 2
  let rd := fld w 0 5
  let rn := fld w 5 5
  let rm := fld w 16 5
  let okT := ftype = 0 || ftype = 1
  if w == (0x0E205800 ||| (rn.setWidth 32 <<< 5) ||| rd.setWidth 32) then some (.cnt8b rn rd)
  else if w == (0x2E303800 ||| (rn.setWidth 32 <<< 5) ||| rd.setWidth 32) then
    some (.uaddlv8b rn rd)
  else if !okT then none
  else if w &&& 0xFF000000 == 0x1F000000 then
    some (.fp3 ftype (bit w 21) (bit w 15) rm (fld w 10 5) rn rd)
  else if w &&& 0x7F20FC00 == 0x1E200000 then
    let sf := bit w 31
    let rmode := fld w 19 2
    let opc := fld w 16 3
    let ok := match rmode.toNat, opc.toNat with
      | 0, 2 | 0, 3 | 3, 0 | 3, 1 => true
      | 0, 6 | 0, 7 => sf == (ftype = 1)
      | _, _ => false
    if ok then some (.fcvtInt sf ftype rmode opc rn rd) else none
  else if w &&& 0xFF207C00 == 0x1E204000 then
    let opc := fld w 15 6
    let ok := match opc.toNat with
      | 0 | 1 | 2 | 3 | 8 | 9 | 10 | 11 | 12 | 14 | 15 => true
      | 4 | 5 => opc.setWidth 2 != ftype  -- FCVT to the other precision
      | _ => false
    if ok then some (.fp1 ftype opc rn rd) else none
  else if w &&& 0xFF20FC07 == 0x1E202000 then
    let opc2 := fld w 3 2
    if opc2.getLsbD 0 && rm != 0 then none  -- `#0.0`: Rm is (0)(0)(0)(0)(0)
    else some (.fcmp ftype rm rn (opc2.getLsbD 0) (opc2.getLsbD 1))
  else if w &&& 0xFF201FE0 == 0x1E201000 then some (.fmovImm ftype (fld w 13 8) rd)
  else if w &&& 0xFF200C00 == 0x1E200800 then
    let opc := fld w 12 4
    if opc.toNat ≤ 5 || opc.toNat = 8 then some (.fp2 ftype opc rm rn rd) else none
  else if w &&& 0xFF200C00 == 0x1E200C00 then some (.fcsel ftype rm (fld w 12 4) rn rd)
  else none

/-- Decode a word. -/
def decode (w : BitVec 32) : Option Insn :=
  if w &&& 0xFFFF0000 == 0 then some (.udf (fld w 0 16))
  else
    let op0 := fld w 25 4
    if op0 &&& 0b1110 == 0b1000 then decodeDPImm w
    else if op0 &&& 0b1110 == 0b1010 then decodeBranch w
    else if op0 &&& 0b0101 == 0b0100 then decodeLdSt w
    else if op0 &&& 0b0111 == 0b0101 then decodeDPReg w
    else if op0 &&& 0b0111 == 0b0111 then decodeFP w
    else none

end GoFV.Arm64
