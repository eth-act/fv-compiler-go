import GoFV.Proof.Gen.Value
import GoFV.Proof.Gen.Progs3

variable [GoFV.SSA.Sem.Addrs]

/-!
# The values of slice G3's ops against the machine's words (`docs/plans/proofs3.md` §4)

Under `AddrAgree` (`Rel.lean`), each op slice G3 adds (`vkind3`: the extensions
`MOV{B,BU,H,HU,W,WU}reg`, `ANDconst`, `SLLconst`, `SRLconst`, `UBFX`, `CMPW`, `CMPWconst`) computes,
from an argument related to the machine word `X` (`ValRel`) whose register holds class `ca`
(`Fits`), a value related to the word the Prog computes, in the form of the step lemmas of
`Progs3.lean` (`progStep_ext`, `progStep_andK`, …): `Lo` at the class the validator checks
(`lo_ext`, `lo_andK`, `lo_lslK`, `lo_lsrK`, `lo_ubfx`), with `valRel_*` the value read back at
its shape (`valRel_retypeL_lo`), and the flags of the 32-bit compares (`flagsRel_cmpw`,
`flagsRel_cmpwK`). The 32-bit register tests and the bit tests (`Arm64.taken` of `ZW`, `NZW`,
`TBZ`, `TBNZ`) decide as `CBZW`/`CBNZW`/`TBZ`/`TBNZ` on the machine word (`taken_zw`, …).

Only the low `ca` bits of a narrow argument's register are known, so an op reading bits of its
argument is related when the bits it reads lie below `ca` (or the argument is a boolean, 0 or 1 in
the whole register).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

variable {ι : Blk → Option (BitVec 64)}

/-! ## Helpers -/

private theorem low_of_le {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem res_int {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

private theorem cls_le {t : Ty} {c : Nat} (hc : cls t = some c) : c ≤ 64 := by
  cases t with
  | int w =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases w <;> decide
  | ptr e => simp only [cls, Option.some.injEq] at hc; omega
  | bool => simp only [cls, Option.some.injEq] at hc; omega
  | _ => simp [cls] at hc

/-- Bits below `c` of words agreeing on the low `c` bits. -/
private theorem bit_of_low {c i : Nat} {a b : BitVec 64} (h : a.setWidth c = b.setWidth c)
    (hi : i < c) : a.getLsbD i = b.getLsbD i := by
  have := congrArg (fun v => v.getLsbD i) h
  simpa only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and] using this

/-- Words agreeing on every bit below `c` agree on the low `c` bits. -/
private theorem low_of_bits {c : Nat} {a b : BitVec 64}
    (h : ∀ i, i < c → i < 64 → a.getLsbD i = b.getLsbD i) : a.setWidth c = b.setWidth c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth]
  by_cases h64 : i < 64
  · rw [h i hi h64]
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ i)]

/-- The register of an argument of class `ca` on the low `w ≤ ca` bits, or all of it for a
boolean. -/
private theorem reg_lowW (hA : AddrAgree ι) {x : Val} {X a : BitVec 64} {ca w : Nat}
    (hx : ValRel ι x X) (hf : Fits ca x) (hr : Arm64.reg x = some a) (hw : w ≤ ca ∨ ca = 1) :
    a.setWidth w = X.setWidth w := by
  rcases hw with hw | rfl
  · exact low_of_le (reg_low hA hx hf hr) hw
  · cases x with
    | bool b =>
      have hr' : (if b then (1 : BitVec 64) else 0) = a := Option.some.inj hr
      have hx' : X = if b then 1 else 0 := hx
      rw [hx', hr']
    | int v _ =>
      have hf' : v.bits = 1 := hf
      cases v <;> exact absurd hf' (by decide)
    | ptr p =>
      have h1 : (1 : Nat) = 64 := hf
      omega
    | poison => cases hr
    | _ => exact False.elim hf

/-- A unary op on the register of `x`, each register giving `Z` on the low `c` bits. -/
private theorem lo_op1 {t : Ty} {f : BitVec 64 → BitVec 64} {x : Val} {Z : BitVec 64} {c : Nat}
    (ht : t ≠ .bool) (hf : ∀ a, Arm64.reg x = some a → (f a).setWidth c = Z.setWidth c) :
    Lo ι c (Arm64.op1 t f [x]) Z := by
  simp only [Arm64.op1]
  cases hr : Arm64.reg x with
  | none => trivial
  | some a =>
    show Lo ι c (Arm64.res t (f a)) Z
    rw [res_int ht]
    exact hf a hr

private theorem and_mask_eq {w : Nat} {a b : BitVec 64} (h : a.setWidth w = b.setWidth w) :
    a &&& Arm64.mask w = b &&& Arm64.mask w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, Arm64.mask, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases hiw : i < w
  · rw [bit_of_low h hiw]
  · simp [hiw]

/-! ## Extensions -/

/-- The machine's extension (`progStep_ext` with `n = w / 8`) is Phase 2's `Arm64.ext`. -/
theorem ext_eq_mov {w : Nat} {sg : Bool} (hw : w = 8 ∨ w = 16 ∨ w = 32) (X : BitVec 64) :
    (if sg then GoFV.Arm64.ProgOp.sextTo64 (w / 8) X else GoFV.Arm64.ProgOp.maskN (w / 8) X) =
      Arm64.ext sg w X := by
  rcases hw with rfl | rfl | rfl <;> cases sg <;> rfl

/-- `MOV{B,BU,H,HU,W,WU}reg` (`extOp?`) of an argument of class at least the extended bits, or a
boolean: the machine's extension `MOV{B,…} Rn, Rd` (`progStep_ext`) of its word. -/
theorem lo_ext (hA : AddrAgree ι) {op : Op} {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {ca w : Nat} {as : GoFV.Asm.As} {sg : Bool} (hx : ValRel ι x X) (hfx : Fits ca x)
    (ht : t ≠ .bool) (he : extOp? op = some (as, w, sg)) (hw : w ≤ ca ∨ ca = 1) :
    Lo ι 64 (Arm64.evalPure op t k aux [x])
      (if sg then GoFV.Arm64.ProgOp.sextTo64 (w / 8) X else GoFV.Arm64.ProgOp.maskN (w / 8) X) := by
  have hev : Arm64.evalPure op t k aux [x] = Arm64.op1 t (Arm64.ext sg w) [x] := by
    unfold extOp? at he
    split at he <;> first | (cases he; rfl) | cases he
  rw [hev, ext_eq_mov (extOp?_movMem he).2]
  refine lo_op1 ht fun a hr => ?_
  have hlow := reg_lowW hA hx hfx hr hw
  simp only [Arm64.ext, Arm64.sext, and_mask_eq hlow]

/-- `lo_ext` read back at a register shape of class `c`. -/
theorem valRel_ext (hA : AddrAgree ι) {op : Op} {t : Ty} {k : Int64} {aux : Option AuxRef}
    {x : Val} {X : BitVec 64} {c ca w : Nat} {as : GoFV.Asm.As} {sg : Bool} (hx : ValRel ι x X)
    (hfx : Fits ca x) (hc : cls t = some c) (ht : t ≠ .bool) (he : extOp? op = some (as, w, sg))
    (hw : w ≤ ca ∨ ca = 1) :
    ValRel ι ((Arm64.evalPure op t k aux [x]).retypeL t)
      (if sg then GoFV.Arm64.ProgOp.sextTo64 (w / 8) X else GoFV.Arm64.ProgOp.maskN (w / 8) X) :=
  valRel_retypeL_lo hA hc ht ((lo_ext hA hx hfx ht he hw).mono (cls_le hc))

/-! ## Narrow ALU ops -/

/-- `ANDconst [k]` of an argument of class `ca ≥ c`: `AND $k, Rn, Rd` (`progStep_andK`) on the
low `c` bits. -/
theorem lo_andK (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {c ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hca : c ≤ ca)
    (ht : t ≠ .bool) :
    Lo ι c (Arm64.evalPure .ARM64ANDconst t k aux [x]) (X &&& BitVec.ofInt 64 k.toInt) := by
  refine lo_op1 ht fun a hr => low_of_bits fun i hi _ => ?_
  have hlow := low_of_le (reg_low hA hx hfx hr) hca
  simp only [Arm64.imm, BitVec.getLsbD_and, bit_of_low hlow hi]

/-- `lo_andK` read back at a register shape of class `c`. -/
theorem valRel_andK (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {c ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hc : cls t = some c)
    (hca : c ≤ ca) (ht : t ≠ .bool) :
    ValRel ι ((Arm64.evalPure .ARM64ANDconst t k aux [x]).retypeL t) (X &&& BitVec.ofInt 64 k.toInt) :=
  valRel_retypeL_lo hA hc ht (lo_andK hA hx hfx hca ht)

/-- `SLLconst [k]` of an argument of class `ca ≥ c`: `LSL $k, Rn, Rd` (`progStep_lslK`, `k` the
auxint) on the low `c` bits. -/
theorem lo_lslK (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {c ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hca : c ≤ ca)
    (ht : t ≠ .bool) :
    Lo ι c (Arm64.evalPure .ARM64SLLconst t k aux [x]) (X <<< (k.toInt.toNat % 64)) := by
  refine lo_op1 ht fun a hr => low_of_bits fun i hi h64 => ?_
  have hlow := low_of_le (reg_low hA hx hfx hr) hca
  show (a <<< (k.toInt.toNat % 64)).getLsbD i = (X <<< (k.toInt.toNat % 64)).getLsbD i
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  by_cases hs : i < k.toInt.toNat % 64
  · simp only [hs, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
  · simp only [hs, decide_false, Bool.not_false, Bool.and_true]
    rw [bit_of_low hlow (by omega)]

/-- `lo_lslK` read back at a register shape of class `c`. -/
theorem valRel_lslK (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {c ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hc : cls t = some c)
    (hca : c ≤ ca) (ht : t ≠ .bool) :
    ValRel ι ((Arm64.evalPure .ARM64SLLconst t k aux [x]).retypeL t) (X <<< (k.toInt.toNat % 64)) :=
  valRel_retypeL_lo hA hc ht (lo_lslK hA hx hfx hca ht)

/-- `SRLconst [k]` of a 64-bit argument: `LSR $k, Rn, Rd` (`progStep_lsrK`, `k` the auxint). -/
theorem lo_lsrK (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} (hx : ValRel ι x X) (hfx : Fits 64 x) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure .ARM64SRLconst t k aux [x]) (X >>> (k.toInt.toNat % 64)) := by
  refine lo_op1 ht fun a hr => ?_
  have hlow := reg_low hA hx hfx hr
  simp only [BitVec.setWidth_eq] at hlow
  subst hlow
  rfl

/-- `lo_lsrK` read back at a register shape. -/
theorem valRel_lsrK (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {c : Nat} (hx : ValRel ι x X) (hfx : Fits 64 x) (hc : cls t = some c)
    (ht : t ≠ .bool) :
    ValRel ι ((Arm64.evalPure .ARM64SRLconst t k aux [x]).retypeL t) (X >>> (k.toInt.toNat % 64)) :=
  valRel_retypeL_lo hA hc ht ((lo_lsrK hA hx hfx ht).mono (cls_le hc))

/-- `UBFX [k]` (`k = lsb · 256 + width ≥ 0`, `vkind3`'s `lsb := k / 256`, `width := k % 256`)
of an argument holding the extracted bits (`lsb + width ≤ ca`): `UBFX $lsb, Rn, $width, Rd`
(`progStep_ubfx`). -/
theorem lo_ubfx (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hk : 0 ≤ k.toInt)
    (hlw : k.toInt / 256 + k.toInt % 256 ≤ ca) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure .ARM64UBFX t k aux [x])
      ((X >>> (k.toInt / 256).toNat) &&& Arm64.mask (k.toInt % 256).toNat) := by
  refine lo_op1 ht fun a hr => low_of_bits fun i _ h64 => ?_
  have hlow := reg_low hA hx hfx hr
  have h1 : k.toInt.toNat / 256 = (k.toInt / 256).toNat := by omega
  have h2 : k.toInt.toNat % 256 = (k.toInt % 256).toNat := by omega
  show ((a >>> (k.toInt.toNat / 256)) &&& Arm64.mask (k.toInt.toNat % 256)).getLsbD i = _
  rw [h1, h2]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, Arm64.mask, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases hiw : i < (k.toInt % 256).toNat
  · rw [bit_of_low hlow (by omega)]
  · simp [hiw]

/-- `lo_ubfx` read back at a register shape. -/
theorem valRel_ubfx (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {c ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hk : 0 ≤ k.toInt)
    (hlw : k.toInt / 256 + k.toInt % 256 ≤ ca) (hc : cls t = some c) (ht : t ≠ .bool) :
    ValRel ι ((Arm64.evalPure .ARM64UBFX t k aux [x]).retypeL t)
      ((X >>> (k.toInt / 256).toNat) &&& Arm64.mask (k.toInt % 256).toNat) :=
  valRel_retypeL_lo hA hc ht ((lo_ubfx hA hx hfx hk hlw ht).mono (cls_le hc))

/-! ## 32-bit compares -/

/-- The `W` register of an argument of class at least 32: none, or the machine word's low word. -/
private theorem reg32_eq (hA : AddrAgree ι) {x : Val} {X : BitVec 64} {ca : Nat}
    (hx : ValRel ι x X) (hf : Fits ca x) (hca : 32 ≤ ca ∨ ca = 1) :
    Arm64.reg32 x = none ∨ Arm64.reg32 x = some (X.setWidth 32) := by
  unfold Arm64.reg32
  cases hr : Arm64.reg x with
  | none => exact .inl rfl
  | some a => exact .inr (congrArg some (reg_lowW hA hx hf hr hca))

private theorem flagsRel_cmpRes {n : Nat} (p : BitVec n × Flags) : FlagsRel (Arm64.cmpRes p) p.2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `CMPW` of arguments of classes at least 32: the flags of the machine's `CMPW Rm, Rn`
(`progStep_cmpwReg`); `poison` if an argument has no register. -/
theorem flagsRel_cmpw (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x y : Val}
    {X Y : BitVec 64} {ca cb : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x)
    (hfy : Fits cb y) (hca : 32 ≤ ca) (hcb : 32 ≤ cb) :
    FlagsRel (Arm64.evalPure .ARM64CMPW t k aux [x, y])
      (Arm64.subFlags (X.setWidth 32) (Y.setWidth 32)).2 := by
  show FlagsRel (Arm64.cmp2w (fun a b => Arm64.subFlags a b) [x, y]) _
  rcases reg32_eq hA hx hfx (.inl hca) with h | h <;>
    rcases reg32_eq hA hy hfy (.inl hcb) with h' | h' <;>
    simp only [Arm64.cmp2w, h, h'] <;> first | trivial | exact flagsRel_cmpRes _

/-- `flagsRel_cmpw` read back at the flags shape. -/
theorem flagsRel_cmpw_retypeL (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef}
    {x y : Val} {X Y : BitVec 64} {ca cb : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y)
    (hfx : Fits ca x) (hfy : Fits cb y) (hca : 32 ≤ ca) (hcb : 32 ≤ cb) :
    FlagsRel ((Arm64.evalPure .ARM64CMPW t k aux [x, y]).retypeL Ty.flags)
      (Arm64.subFlags (X.setWidth 32) (Y.setWidth 32)).2 :=
  (flags_retypeL (flagsRel_cmpw hA hx hy hfx hfy hca hcb)).1

/-- The low word of a 64-bit constant. -/
theorem ofInt_setWidth32 (i : Int) : (BitVec.ofInt 64 i).setWidth 32 = BitVec.ofInt 32 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have h64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
  have h32 : ((2 ^ 32 : Nat) : Int) = 4294967296 := rfl
  rw [h64, h32]
  omega

/-- `CMPWconst [k]` of an argument of class at least 32: the flags of the machine's
`CMPW $k, Rn` (`progStep_cmpwConst`, `k` the auxint). -/
theorem flagsRel_cmpwK (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hca : 32 ≤ ca) :
    FlagsRel (Arm64.evalPure .ARM64CMPWconst t k aux [x])
      (Arm64.subFlags (X.setWidth 32) ((BitVec.ofInt 64 k.toInt).setWidth 32)).2 := by
  show FlagsRel (Arm64.cmp1w (fun a => Arm64.subFlags a (Arm64.imm32 k)) [x]) _
  rw [ofInt_setWidth32]
  rcases reg32_eq hA hx hfx (.inl hca) with h | h <;>
    simp only [Arm64.cmp1w, h] <;> first | trivial | exact flagsRel_cmpRes _

/-- `flagsRel_cmpwK` read back at the flags shape. -/
theorem flagsRel_cmpwK_retypeL (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef}
    {x : Val} {X : BitVec 64} {ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hca : 32 ≤ ca) :
    FlagsRel ((Arm64.evalPure .ARM64CMPWconst t k aux [x]).retypeL Ty.flags)
      (Arm64.subFlags (X.setWidth 32) ((BitVec.ofInt 64 k.toInt).setWidth 32)).2 :=
  (flags_retypeL (flagsRel_cmpwK hA hx hfx hca)).1

/-! ## Register and bit tests -/

/-- `ZW` on a register of at least 32 bits or a boolean: taken exactly when the machine word's
low word is zero (`CBZW`, `progStep_cbzw`). -/
theorem taken_zw (hA : AddrAgree ι) {k : Int64} {x : Val} {X : BitVec 64} {ca : Nat} {b : Bool}
    (hx : ValRel ι x X) (hf : Fits ca x) (hca : 32 ≤ ca ∨ ca = 1)
    (h : Arm64.taken .ARM64ZW k x = some b) : b = (X.setWidth 32 == 0) := by
  have h' : (Arm64.reg32 x).map (· == 0) = some b := h
  rcases reg32_eq hA hx hf hca with hr | hr <;> rw [hr] at h'
  · cases h'
  · exact (Option.some.inj h').symm

/-- `NZW` on a register of at least 32 bits or a boolean: taken exactly when the machine word's
low word is not zero (`CBNZW`, `progStep_cbzw`). -/
theorem taken_nzw (hA : AddrAgree ι) {k : Int64} {x : Val} {X : BitVec 64} {ca : Nat} {b : Bool}
    (hx : ValRel ι x X) (hf : Fits ca x) (hca : 32 ≤ ca ∨ ca = 1)
    (h : Arm64.taken .ARM64NZW k x = some b) : b = !(X.setWidth 32 == 0) := by
  have h' : (Arm64.reg32 x).map (· != 0) = some b := h
  rcases reg32_eq hA hx hf hca with hr | hr <;> rw [hr] at h'
  · cases h'
  · exact (Option.some.inj h').symm

/-- The bit `i` of the register of an argument holding it (`i < ca`) or of a boolean. -/
private theorem reg_bit (hA : AddrAgree ι) {x : Val} {X a : BitVec 64} {ca i : Nat}
    (hx : ValRel ι x X) (hf : Fits ca x) (hr : Arm64.reg x = some a) (hi : i < ca ∨ ca = 1) :
    a.getLsbD i = X.getLsbD i := by
  rcases hi with hi | h1
  · exact bit_of_low (reg_low hA hx hf hr) hi
  · have := reg_lowW hA hx hf hr (w := 64) (.inr h1)
    simp only [BitVec.setWidth_eq] at this
    rw [this]

/-- `TBZ [k]` on a register holding bit `k` or a boolean: taken exactly when that bit of the
machine word is clear (`progStep_tbz`, `bit` the auxint). -/
theorem taken_tbz (hA : AddrAgree ι) {k : Int64} {x : Val} {X : BitVec 64} {ca : Nat} {b : Bool}
    (hx : ValRel ι x X) (hf : Fits ca x) (hi : k.toInt.toNat < ca ∨ ca = 1)
    (h : Arm64.taken .ARM64TBZ k x = some b) : b = !X.getLsbD k.toInt.toNat := by
  have h' : (Arm64.reg x).map (fun a => !a.getLsbD k.toInt.toNat) = some b := h
  cases hr : Arm64.reg x with
  | none => rw [hr] at h'; cases h'
  | some a =>
    rw [hr] at h'
    rw [← Option.some.inj h']
    show (!a.getLsbD k.toInt.toNat) = _
    rw [reg_bit hA hx hf hr hi]

/-- `TBNZ [k]` on a register holding bit `k` or a boolean: taken exactly when that bit of the
machine word is set (`progStep_tbz`). -/
theorem taken_tbnz (hA : AddrAgree ι) {k : Int64} {x : Val} {X : BitVec 64} {ca : Nat} {b : Bool}
    (hx : ValRel ι x X) (hf : Fits ca x) (hi : k.toInt.toNat < ca ∨ ca = 1)
    (h : Arm64.taken .ARM64TBNZ k x = some b) : b = X.getLsbD k.toInt.toNat := by
  have h' : (Arm64.reg x).map (fun a => a.getLsbD k.toInt.toNat) = some b := h
  cases hr : Arm64.reg x with
  | none => rw [hr] at h'; cases h'
  | some a =>
    rw [hr] at h'
    rw [← Option.some.inj h']
    exact reg_bit hA hx hf hr hi

end GoFV.Proof.Gen
