import GoFV.Proof.Pass.UnreadLAvoid

/-!
# elim unread autos on `runL`: every pure arm64 op keeps values avoiding frame temporaries

`evalPure_av`: one case per op of `Arm64.evalPure`, by its family lemma (`UnreadLAvoid`); every
other op is `poison`. Kept in its own module: the case split over `Op` is the costly part.
-/

namespace GoFV.Proof.UnreadL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.DAE

variable {U : Blk → Prop}

theorem fop_av (w : Width) (g : Width → List Val → Val) (hg : ∀ w args, Val.Avoids U (g w args))
    (args : List Val) : Val.Avoids U (Arm64.fop w g args) := hg _ _

set_option maxHeartbeats 4000000 in
/-- **Every pure arm64 op keeps values avoiding frame temporaries.** -/
theorem evalPure_av (hU : TempU U) (op : Op) (ty : Ty) (k : Int64) (aux : Option AuxRef)
    {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Arm64.evalPure op ty k aux args) := by
  cases op
  case ARM64ADD =>
    show Val.Avoids U (Arm64.add ty args)
    exact add_av _ h
  case ARM64ADDconst =>
    show Val.Avoids U (Arm64.addK ty (Arm64.imm k) args)
    exact addK_av _ _ h
  case ARM64SUB =>
    show Val.Avoids U (Arm64.sub ty args)
    exact sub_av _ h
  case ARM64SUBconst =>
    show Val.Avoids U (Arm64.addK ty (-Arm64.imm k) args)
    exact addK_av _ _ h
  case ARM64MUL =>
    show Val.Avoids U (Arm64.op2 ty (· * ·) args)
    exact op2_av _ _ _
  case ARM64MULW =>
    show Val.Avoids U (Arm64.op2w ty (· * ·) args)
    exact op2w_av _ _ _
  case ARM64MNEG =>
    show Val.Avoids U (Arm64.op2 ty (fun x y => -(x * y)) args)
    exact op2_av _ _ _
  case ARM64MNEGW =>
    show Val.Avoids U (Arm64.op2w ty (fun x y => -(x * y)) args)
    exact op2w_av _ _ _
  case ARM64MULH =>
    show Val.Avoids U (Arm64.op2 ty Arm64.smulh args)
    exact op2_av _ _ _
  case ARM64UMULH =>
    show Val.Avoids U (Arm64.op2 ty Arm64.umulh args)
    exact op2_av _ _ _
  case ARM64MULL =>
    show Val.Avoids U (Arm64.op2 ty Arm64.smull args)
    exact op2_av _ _ _
  case ARM64UMULL =>
    show Val.Avoids U (Arm64.op2 ty Arm64.umull args)
    exact op2_av _ _ _
  case ARM64DIV =>
    show Val.Avoids U (Arm64.op2 ty Arm64.sdiv args)
    exact op2_av _ _ _
  case ARM64UDIV =>
    show Val.Avoids U (Arm64.op2 ty Arm64.udiv args)
    exact op2_av _ _ _
  case ARM64DIVW =>
    show Val.Avoids U (Arm64.op2w ty Arm64.sdiv args)
    exact op2w_av _ _ _
  case ARM64UDIVW =>
    show Val.Avoids U (Arm64.op2w ty Arm64.udiv args)
    exact op2w_av _ _ _
  case ARM64MOD =>
    show Val.Avoids U (Arm64.op2 ty Arm64.srem args)
    exact op2_av _ _ _
  case ARM64UMOD =>
    show Val.Avoids U (Arm64.op2 ty Arm64.urem args)
    exact op2_av _ _ _
  case ARM64MODW =>
    show Val.Avoids U (Arm64.op2w ty Arm64.srem args)
    exact op2w_av _ _ _
  case ARM64UMODW =>
    show Val.Avoids U (Arm64.op2w ty Arm64.urem args)
    exact op2w_av _ _ _
  case ARM64MADD =>
    show Val.Avoids U (Arm64.op3 ty (fun a x y => a + x * y) args)
    exact op3_av _ _ _
  case ARM64MADDW =>
    show Val.Avoids U (Arm64.op3w ty (fun a x y => a + x * y) args)
    exact op3w_av _ _ _
  case ARM64MSUB =>
    show Val.Avoids U (Arm64.op3 ty (fun a x y => a - x * y) args)
    exact op3_av _ _ _
  case ARM64MSUBW =>
    show Val.Avoids U (Arm64.op3w ty (fun a x y => a - x * y) args)
    exact op3w_av _ _ _
  case ARM64NEG =>
    show Val.Avoids U (Arm64.op1 ty (- ·) args)
    exact op1_av _ _ _
  case ARM64MVN =>
    show Val.Avoids U (Arm64.op1 ty (~~~ ·) args)
    exact op1_av _ _ _
  case ARM64AND =>
    show Val.Avoids U (Arm64.op2 ty (· &&& ·) args)
    exact op2_av _ _ _
  case ARM64ANDconst =>
    show Val.Avoids U (Arm64.op1 ty (· &&& Arm64.imm k) args)
    exact op1_av _ _ _
  case ARM64OR =>
    show Val.Avoids U (Arm64.op2 ty (· ||| ·) args)
    exact op2_av _ _ _
  case ARM64ORconst =>
    show Val.Avoids U (Arm64.op1 ty (· ||| Arm64.imm k) args)
    exact op1_av _ _ _
  case ARM64XOR =>
    show Val.Avoids U (Arm64.op2 ty (· ^^^ ·) args)
    exact op2_av _ _ _
  case ARM64XORconst =>
    show Val.Avoids U (Arm64.op1 ty (· ^^^ Arm64.imm k) args)
    exact op1_av _ _ _
  case ARM64BIC =>
    show Val.Avoids U (Arm64.op2 ty (fun x y => x &&& ~~~y) args)
    exact op2_av _ _ _
  case ARM64EON =>
    show Val.Avoids U (Arm64.op2 ty (fun x y => x ^^^ ~~~y) args)
    exact op2_av _ _ _
  case ARM64ORN =>
    show Val.Avoids U (Arm64.op2 ty (fun x y => x ||| ~~~y) args)
    exact op2_av _ _ _
  case ARM64SLL =>
    show Val.Avoids U (Arm64.op2 ty (fun x y => x <<< (y.toNat % 64)) args)
    exact op2_av _ _ _
  case ARM64SRL =>
    show Val.Avoids U (Arm64.op2 ty (fun x y => x >>> (y.toNat % 64)) args)
    exact op2_av _ _ _
  case ARM64SRA =>
    show Val.Avoids U (Arm64.op2 ty (fun x y => x.sshiftRight (y.toNat % 64)) args)
    exact op2_av _ _ _
  case ARM64ROR =>
    show Val.Avoids U (Arm64.op2 ty (fun x y => x.rotateRight (y.toNat % 64)) args)
    exact op2_av _ _ _
  case ARM64RORW =>
    show Val.Avoids U (Arm64.op2w ty (fun x y => x.rotateRight (y.toNat % 32)) args)
    exact op2w_av _ _ _
  case ARM64SLLconst =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.Shift.ll.apply · (Arm64.amt k)) args)
    exact op1_av _ _ _
  case ARM64SRLconst =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.Shift.rl.apply · (Arm64.amt k)) args)
    exact op1_av _ _ _
  case ARM64SRAconst =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.Shift.ra.apply · (Arm64.amt k)) args)
    exact op1_av _ _ _
  case ARM64RORconst =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.Shift.ro.apply · (Arm64.amt k)) args)
    exact op1_av _ _ _
  case ARM64RORWconst =>
    show Val.Avoids U (Arm64.op1w ty (Arm64.Shift.ro.apply · (Arm64.amt k)) args)
    exact op1w_av _ _ _
  case ARM64EXTRconst =>
    show Val.Avoids U (Arm64.op2 ty (Arm64.extr (Arm64.amt k)) args)
    exact op2_av _ _ _
  case ARM64EXTRWconst =>
    show Val.Avoids U (Arm64.op2w ty (Arm64.extr (Arm64.amt k)) args)
    exact op2w_av _ _ _
  case ARM64MVNshiftLL =>
    show Val.Avoids U (Arm64.op1 ty (fun x => ~~~(Arm64.shifted .ll k x)) args)
    exact op1_av _ _ _
  case ARM64MVNshiftRL =>
    show Val.Avoids U (Arm64.op1 ty (fun x => ~~~(Arm64.shifted .rl k x)) args)
    exact op1_av _ _ _
  case ARM64MVNshiftRA =>
    show Val.Avoids U (Arm64.op1 ty (fun x => ~~~(Arm64.shifted .ra k x)) args)
    exact op1_av _ _ _
  case ARM64MVNshiftRO =>
    show Val.Avoids U (Arm64.op1 ty (fun x => ~~~(Arm64.shifted .ro k x)) args)
    exact op1_av _ _ _
  case ARM64NEGshiftLL =>
    show Val.Avoids U (Arm64.op1 ty (fun x => -(Arm64.shifted .ll k x)) args)
    exact op1_av _ _ _
  case ARM64NEGshiftRL =>
    show Val.Avoids U (Arm64.op1 ty (fun x => -(Arm64.shifted .rl k x)) args)
    exact op1_av _ _ _
  case ARM64NEGshiftRA =>
    show Val.Avoids U (Arm64.op1 ty (fun x => -(Arm64.shifted .ra k x)) args)
    exact op1_av _ _ _
  case ARM64ADDshiftLL =>
    show Val.Avoids U (Arm64.addSh ty .ll k args)
    exact addSh_av _ _ _ h
  case ARM64ADDshiftRL =>
    show Val.Avoids U (Arm64.addSh ty .rl k args)
    exact addSh_av _ _ _ h
  case ARM64ADDshiftRA =>
    show Val.Avoids U (Arm64.addSh ty .ra k args)
    exact addSh_av _ _ _ h
  case ARM64SUBshiftLL =>
    show Val.Avoids U (Arm64.subSh ty .ll k args)
    exact subSh_av _ _ _ h
  case ARM64SUBshiftRL =>
    show Val.Avoids U (Arm64.subSh ty .rl k args)
    exact subSh_av _ _ _ h
  case ARM64SUBshiftRA =>
    show Val.Avoids U (Arm64.subSh ty .ra k args)
    exact subSh_av _ _ _ h
  case ARM64ANDshiftLL =>
    show Val.Avoids U (Arm64.opSh ty .ll k (· &&& ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64ANDshiftRL =>
    show Val.Avoids U (Arm64.opSh ty .rl k (· &&& ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64ANDshiftRA =>
    show Val.Avoids U (Arm64.opSh ty .ra k (· &&& ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64ANDshiftRO =>
    show Val.Avoids U (Arm64.opSh ty .ro k (· &&& ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64ORshiftLL =>
    show Val.Avoids U (Arm64.opSh ty .ll k (· ||| ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64ORshiftRL =>
    show Val.Avoids U (Arm64.opSh ty .rl k (· ||| ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64ORshiftRA =>
    show Val.Avoids U (Arm64.opSh ty .ra k (· ||| ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64ORshiftRO =>
    show Val.Avoids U (Arm64.opSh ty .ro k (· ||| ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64XORshiftLL =>
    show Val.Avoids U (Arm64.opSh ty .ll k (· ^^^ ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64XORshiftRL =>
    show Val.Avoids U (Arm64.opSh ty .rl k (· ^^^ ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64XORshiftRA =>
    show Val.Avoids U (Arm64.opSh ty .ra k (· ^^^ ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64XORshiftRO =>
    show Val.Avoids U (Arm64.opSh ty .ro k (· ^^^ ·) args)
    exact opSh_av _ _ _ _ _
  case ARM64BICshiftLL =>
    show Val.Avoids U (Arm64.opSh ty .ll k (fun x y => x &&& ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64BICshiftRL =>
    show Val.Avoids U (Arm64.opSh ty .rl k (fun x y => x &&& ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64BICshiftRA =>
    show Val.Avoids U (Arm64.opSh ty .ra k (fun x y => x &&& ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64BICshiftRO =>
    show Val.Avoids U (Arm64.opSh ty .ro k (fun x y => x &&& ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64EONshiftLL =>
    show Val.Avoids U (Arm64.opSh ty .ll k (fun x y => x ^^^ ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64EONshiftRL =>
    show Val.Avoids U (Arm64.opSh ty .rl k (fun x y => x ^^^ ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64EONshiftRA =>
    show Val.Avoids U (Arm64.opSh ty .ra k (fun x y => x ^^^ ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64EONshiftRO =>
    show Val.Avoids U (Arm64.opSh ty .ro k (fun x y => x ^^^ ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64ORNshiftLL =>
    show Val.Avoids U (Arm64.opSh ty .ll k (fun x y => x ||| ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64ORNshiftRL =>
    show Val.Avoids U (Arm64.opSh ty .rl k (fun x y => x ||| ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64ORNshiftRA =>
    show Val.Avoids U (Arm64.opSh ty .ra k (fun x y => x ||| ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64ORNshiftRO =>
    show Val.Avoids U (Arm64.opSh ty .ro k (fun x y => x ||| ~~~y) args)
    exact opSh_av _ _ _ _ _
  case ARM64UBFX =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.ubfx k) args)
    exact op1_av _ _ _
  case ARM64SBFX =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.sbfx k) args)
    exact op1_av _ _ _
  case ARM64UBFIZ =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.ubfiz k) args)
    exact op1_av _ _ _
  case ARM64SBFIZ =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.sbfiz k) args)
    exact op1_av _ _ _
  case ARM64BFI =>
    show Val.Avoids U (Arm64.op2 ty (Arm64.bfi k) args)
    exact op2_av _ _ _
  case ARM64BFXIL =>
    show Val.Avoids U (Arm64.op2 ty (Arm64.bfxil k) args)
    exact op2_av _ _ _
  case ARM64CLZ =>
    show Val.Avoids U (Arm64.op1 ty Arm64.clz args)
    exact op1_av _ _ _
  case ARM64CLZW =>
    show Val.Avoids U (Arm64.op1w ty Arm64.clz args)
    exact op1w_av _ _ _
  case ARM64RBIT =>
    show Val.Avoids U (Arm64.op1 ty Arm64.rbit args)
    exact op1_av _ _ _
  case ARM64RBITW =>
    show Val.Avoids U (Arm64.op1w ty Arm64.rbit args)
    exact op1w_av _ _ _
  case ARM64REV =>
    show Val.Avoids U (Arm64.op1 ty Arm64.rev args)
    exact op1_av _ _ _
  case ARM64REVW =>
    show Val.Avoids U (Arm64.op1w ty Arm64.rev args)
    exact op1w_av _ _ _
  case ARM64REV16 =>
    show Val.Avoids U (Arm64.op1 ty Arm64.rev16 args)
    exact op1_av _ _ _
  case ARM64REV16W =>
    show Val.Avoids U (Arm64.op1w ty Arm64.rev16 args)
    exact op1w_av _ _ _
  case ARM64VCNT =>
    show Val.Avoids U (Arm64.op1 ty Arm64.vcnt args)
    exact op1_av _ _ _
  case ARM64VUADDLV =>
    show Val.Avoids U (Arm64.op1 ty Arm64.vuaddlv args)
    exact op1_av _ _ _
  case ARM64MOVBreg =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.ext true 8) args)
    exact op1_av _ _ _
  case ARM64MOVBUreg =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.ext false 8) args)
    exact op1_av _ _ _
  case ARM64MOVHreg =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.ext true 16) args)
    exact op1_av _ _ _
  case ARM64MOVHUreg =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.ext false 16) args)
    exact op1_av _ _ _
  case ARM64MOVWreg =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.ext true 32) args)
    exact op1_av _ _ _
  case ARM64MOVWUreg =>
    show Val.Avoids U (Arm64.op1 ty (Arm64.ext false 32) args)
    exact op1_av _ _ _
  case ARM64MOVDconst =>
    show Val.Avoids U (Arm64.res ty (Arm64.imm k))
    exact res_av _ _
  case ARM64ZERO =>
    show Val.Avoids U (Arm64.res ty 0)
    exact res_av _ _
  case ARM64CMP => exact cmpArgs_av _
  case ARM64CMPconst => exact cmpK_av _ _
  case ARM64CMPW =>
    show Val.Avoids U (Arm64.cmp2w (fun x y => Arm64.subFlags x y) args)
    exact cmp2w_av _ _
  case ARM64CMPWconst =>
    show Val.Avoids U (Arm64.cmp1w (fun x => Arm64.subFlags x (Arm64.imm32 k)) args)
    exact cmp1w_av _ _
  case ARM64CMN =>
    show Val.Avoids U (Arm64.cmp2 (fun x y => addWithCarry x y false) args)
    exact cmp2_av _ _
  case ARM64CMNconst =>
    show Val.Avoids U (Arm64.cmp1 (fun x => addWithCarry x (Arm64.imm k) false) args)
    exact cmp1_av _ _
  case ARM64CMNW =>
    show Val.Avoids U (Arm64.cmp2w (fun x y => addWithCarry x y false) args)
    exact cmp2w_av _ _
  case ARM64CMNWconst =>
    show Val.Avoids U (Arm64.cmp1w (fun x => addWithCarry x (Arm64.imm32 k) false) args)
    exact cmp1w_av _ _
  case ARM64TST =>
    show Val.Avoids U (Arm64.flags2 (fun x y => logicFlags (x &&& y)) args)
    exact flags2_av _ _
  case ARM64TSTconst =>
    show Val.Avoids U (Arm64.flags1 (fun x => logicFlags (x &&& Arm64.imm k)) args)
    exact flags1_av _ _
  case ARM64TSTW =>
    show Val.Avoids U (Arm64.flags2w (fun x y => logicFlags (x &&& y)) args)
    exact flags2w_av _ _
  case ARM64TSTWconst =>
    show Val.Avoids U (Arm64.flags1w (fun x => logicFlags (x &&& Arm64.imm32 k)) args)
    exact flags1w_av _ _
  case ARM64CMPshiftLL =>
    show Val.Avoids U (Arm64.cmp2 (fun x y => Arm64.subFlags x (Arm64.shifted .ll k y)) args)
    exact cmp2_av _ _
  case ARM64CMPshiftRL =>
    show Val.Avoids U (Arm64.cmp2 (fun x y => Arm64.subFlags x (Arm64.shifted .rl k y)) args)
    exact cmp2_av _ _
  case ARM64CMPshiftRA =>
    show Val.Avoids U (Arm64.cmp2 (fun x y => Arm64.subFlags x (Arm64.shifted .ra k y)) args)
    exact cmp2_av _ _
  case ARM64CMNshiftLL =>
    show Val.Avoids U (Arm64.cmp2 (fun x y => addWithCarry x (Arm64.shifted .ll k y) false) args)
    exact cmp2_av _ _
  case ARM64CMNshiftRL =>
    show Val.Avoids U (Arm64.cmp2 (fun x y => addWithCarry x (Arm64.shifted .rl k y) false) args)
    exact cmp2_av _ _
  case ARM64CMNshiftRA =>
    show Val.Avoids U (Arm64.cmp2 (fun x y => addWithCarry x (Arm64.shifted .ra k y) false) args)
    exact cmp2_av _ _
  case ARM64TSTshiftLL =>
    show Val.Avoids U (Arm64.flags2 (fun x y => logicFlags (x &&& Arm64.shifted .ll k y)) args)
    exact flags2_av _ _
  case ARM64TSTshiftRL =>
    show Val.Avoids U (Arm64.flags2 (fun x y => logicFlags (x &&& Arm64.shifted .rl k y)) args)
    exact flags2_av _ _
  case ARM64TSTshiftRA =>
    show Val.Avoids U (Arm64.flags2 (fun x y => logicFlags (x &&& Arm64.shifted .ra k y)) args)
    exact flags2_av _ _
  case ARM64TSTshiftRO =>
    show Val.Avoids U (Arm64.flags2 (fun x y => logicFlags (x &&& Arm64.shifted .ro k y)) args)
    exact flags2_av _ _
  case ARM64FlagConstant =>
    show Val.Avoids U ((Flags.ofFlagConstant k.toInt.toNat).toVal)
    exact flags_av _
  case ARM64InvertFlags =>
    rcases args with _ | ⟨f, _ | ⟨_, _⟩⟩
    · exact True.intro
    · exact invertFlags_av f
    · exact True.intro
  case ARM64ADDSflags =>
    show Val.Avoids U (Arm64.adds ty args)
    exact adds_av _ _
  case ARM64ADDSconstflags =>
    show Val.Avoids U (Arm64.addsConst ty k args)
    exact addsConst_av _ _ _
  case ARM64SUBSflags =>
    show Val.Avoids U (Arm64.subs ty args)
    exact subs_av _ _
  case ARM64ADCSflags =>
    show Val.Avoids U (Arm64.adcs ty args)
    exact adcs_av _ _
  case ARM64SBCSflags =>
    show Val.Avoids U (Arm64.sbcs ty args)
    exact sbcs_av _ _
  case ARM64NEGSflags =>
    show Val.Avoids U (Arm64.negs ty args)
    exact negs_av _ _
  case ARM64ADCzerocarry =>
    show Val.Avoids U (Arm64.adcZero ty args)
    exact adcZero_av _ _
  case ARM64NGCzerocarry =>
    show Val.Avoids U (Arm64.ngcZero ty args)
    exact ngcZero_av _ _
  case ARM64CSEL =>
    show Val.Avoids U (Arm64.csel ty k none args)
    exact csel_av _ _ _ h
  case ARM64CSEL0 =>
    show Val.Avoids U (Arm64.csel0 ty k args)
    exact csel0_av _ _ h
  case ARM64CSINC =>
    show Val.Avoids U (Arm64.csel ty k (some (· + 1)) args)
    exact csel_av _ _ _ h
  case ARM64CSINV =>
    show Val.Avoids U (Arm64.csel ty k (some (~~~ ·)) args)
    exact csel_av _ _ _ h
  case ARM64CSNEG =>
    show Val.Avoids U (Arm64.csel ty k (some (- ·)) args)
    exact csel_av _ _ _ h
  case ARM64CSETM =>
    show Val.Avoids U (Arm64.csetm ty k args)
    exact csetm_av _ _ _
  case ARM64CCMP =>
    show Val.Avoids U (Arm64.ccmp false false false k args)
    exact ccmp_av _ _ _ _ _
  case ARM64CCMN =>
    show Val.Avoids U (Arm64.ccmp true false false k args)
    exact ccmp_av _ _ _ _ _
  case ARM64CCMPconst =>
    show Val.Avoids U (Arm64.ccmp false false true k args)
    exact ccmp_av _ _ _ _ _
  case ARM64CCMNconst =>
    show Val.Avoids U (Arm64.ccmp true false true k args)
    exact ccmp_av _ _ _ _ _
  case ARM64CCMPW =>
    show Val.Avoids U (Arm64.ccmp false true false k args)
    exact ccmp_av _ _ _ _ _
  case ARM64CCMNW =>
    show Val.Avoids U (Arm64.ccmp true true false k args)
    exact ccmp_av _ _ _ _ _
  case ARM64CCMPWconst =>
    show Val.Avoids U (Arm64.ccmp false true true k args)
    exact ccmp_av _ _ _ _ _
  case ARM64CCMNWconst =>
    show Val.Avoids U (Arm64.ccmp true true true k args)
    exact ccmp_av _ _ _ _ _
  case ARM64GreaterEqualF =>
    show Val.Avoids U (Arm64.cset ty .ARM64GreaterEqualF args)
    exact cset_av _ _ _
  case ARM64NotLessThanF =>
    show Val.Avoids U (Arm64.cset ty .ARM64NotLessThanF args)
    exact cset_av _ _ _
  case ARM64NotLessEqualF =>
    show Val.Avoids U (Arm64.cset ty .ARM64NotLessEqualF args)
    exact cset_av _ _ _
  case ARM64NotGreaterThanF =>
    show Val.Avoids U (Arm64.cset ty .ARM64NotGreaterThanF args)
    exact cset_av _ _ _
  case ARM64GreaterEqualU =>
    show Val.Avoids U (Arm64.cset ty .ARM64GreaterEqualU args)
    exact cset_av _ _ _
  case ARM64LessThanF =>
    show Val.Avoids U (Arm64.cset ty .ARM64LessThanF args)
    exact cset_av _ _ _
  case ARM64LessEqualF =>
    show Val.Avoids U (Arm64.cset ty .ARM64LessEqualF args)
    exact cset_av _ _ _
  case ARM64GreaterThanF =>
    show Val.Avoids U (Arm64.cset ty .ARM64GreaterThanF args)
    exact cset_av _ _ _
  case ARM64GreaterEqual =>
    show Val.Avoids U (Arm64.cset ty .ARM64GreaterEqual args)
    exact cset_av _ _ _
  case ARM64LessThanU =>
    show Val.Avoids U (Arm64.cset ty .ARM64LessThanU args)
    exact cset_av _ _ _
  case ARM64LessEqualU =>
    show Val.Avoids U (Arm64.cset ty .ARM64LessEqualU args)
    exact cset_av _ _ _
  case ARM64GreaterThanU =>
    show Val.Avoids U (Arm64.cset ty .ARM64GreaterThanU args)
    exact cset_av _ _ _
  case ARM64Equal =>
    show Val.Avoids U (Arm64.cset ty .ARM64Equal args)
    exact cset_av _ _ _
  case ARM64NotEqual =>
    show Val.Avoids U (Arm64.cset ty .ARM64NotEqual args)
    exact cset_av _ _ _
  case ARM64LessThan =>
    show Val.Avoids U (Arm64.cset ty .ARM64LessThan args)
    exact cset_av _ _ _
  case ARM64LessEqual =>
    show Val.Avoids U (Arm64.cset ty .ARM64LessEqual args)
    exact cset_av _ _ _
  case ARM64GreaterThan =>
    show Val.Avoids U (Arm64.cset ty .ARM64GreaterThan args)
    exact cset_av _ _ _
  case ARM64NotGreaterEqualF =>
    show Val.Avoids U (Arm64.cset ty .ARM64NotGreaterEqualF args)
    exact cset_av _ _ _
  case ARM64LessThanNoov =>
    show Val.Avoids U (Arm64.cset ty .ARM64LessThanNoov args)
    exact cset_av _ _ _
  case ARM64GreaterEqualNoov =>
    show Val.Avoids U (Arm64.cset ty .ARM64GreaterEqualNoov args)
    exact cset_av _ _ _
  case ARM64FADDS =>
    show Val.Avoids U (Arm64.fop .w32 FOps.add args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FADDD =>
    show Val.Avoids U (Arm64.fop .w64 FOps.add args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FSUBS =>
    show Val.Avoids U (Arm64.fop .w32 FOps.sub args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FSUBD =>
    show Val.Avoids U (Arm64.fop .w64 FOps.sub args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FMULS =>
    show Val.Avoids U (Arm64.fop .w32 FOps.mul args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FMULD =>
    show Val.Avoids U (Arm64.fop .w64 FOps.mul args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FNMULS =>
    show Val.Avoids U (Arm64.fnmul .w32 args)
    exact fnmul_av _ _
  case ARM64FNMULD =>
    show Val.Avoids U (Arm64.fnmul .w64 args)
    exact fnmul_av _ _
  case ARM64FDIVS =>
    show Val.Avoids U (Arm64.fop .w32 FOps.div args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FDIVD =>
    show Val.Avoids U (Arm64.fop .w64 FOps.div args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FABSS =>
    show Val.Avoids U (Arm64.fop .w32 FOps.abs args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FABSD =>
    show Val.Avoids U (Arm64.fop .w64 FOps.abs args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FNEGS =>
    show Val.Avoids U (Arm64.fop .w32 FOps.neg args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FNEGD =>
    show Val.Avoids U (Arm64.fop .w64 FOps.neg args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FSQRTS =>
    show Val.Avoids U (Arm64.fop .w32 FOps.sqrt args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FSQRTD =>
    show Val.Avoids U (Arm64.fop .w64 FOps.sqrt args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FMINS =>
    show Val.Avoids U (Arm64.fop .w32 FOps.min args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FMIND =>
    show Val.Avoids U (Arm64.fop .w64 FOps.min args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FMAXS =>
    show Val.Avoids U (Arm64.fop .w32 FOps.max args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FMAXD =>
    show Val.Avoids U (Arm64.fop .w64 FOps.max args)
    exact fop_av _ _ (fun _ _ => fbin_av _ _ _) _
  case ARM64FMADDS =>
    show Val.Avoids U (Arm64.fmadd .w32 false false args)
    exact fmadd_av _ _ _ _
  case ARM64FMADDD =>
    show Val.Avoids U (Arm64.fmadd .w64 false false args)
    exact fmadd_av _ _ _ _
  case ARM64FMSUBS =>
    show Val.Avoids U (Arm64.fmadd .w32 false true args)
    exact fmadd_av _ _ _ _
  case ARM64FMSUBD =>
    show Val.Avoids U (Arm64.fmadd .w64 false true args)
    exact fmadd_av _ _ _ _
  case ARM64FNMADDS =>
    show Val.Avoids U (Arm64.fmadd .w32 true true args)
    exact fmadd_av _ _ _ _
  case ARM64FNMADDD =>
    show Val.Avoids U (Arm64.fmadd .w64 true true args)
    exact fmadd_av _ _ _ _
  case ARM64FNMSUBS =>
    show Val.Avoids U (Arm64.fmadd .w32 true false args)
    exact fmadd_av _ _ _ _
  case ARM64FNMSUBD =>
    show Val.Avoids U (Arm64.fmadd .w64 true false args)
    exact fmadd_av _ _ _ _
  case ARM64FRINTAS =>
    show Val.Avoids U (Arm64.fop .w32 (FOps.roundInt .rna) args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FRINTAD =>
    show Val.Avoids U (Arm64.fop .w64 (FOps.roundInt .rna) args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FRINTMS =>
    show Val.Avoids U (Arm64.fop .w32 (FOps.roundInt .rmi) args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FRINTMD =>
    show Val.Avoids U (Arm64.fop .w64 (FOps.roundInt .rmi) args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FRINTNS =>
    show Val.Avoids U (Arm64.fop .w32 (FOps.roundInt .rne) args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FRINTND =>
    show Val.Avoids U (Arm64.fop .w64 (FOps.roundInt .rne) args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FRINTPS =>
    show Val.Avoids U (Arm64.fop .w32 (FOps.roundInt .rpi) args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FRINTPD =>
    show Val.Avoids U (Arm64.fop .w64 (FOps.roundInt .rpi) args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FRINTZS =>
    show Val.Avoids U (Arm64.fop .w32 (FOps.roundInt .rz) args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64FRINTZD =>
    show Val.Avoids U (Arm64.fop .w64 (FOps.roundInt .rz) args)
    exact fop_av _ _ (fun _ _ => fun_av _ _ _) _
  case ARM64LoweredRound32F =>
    show Val.Avoids U (Arm64.fop .w32 FOps.round args)
    exact fop_av _ _ (fun _ _ => fround_av _ _) _
  case ARM64LoweredRound64F =>
    show Val.Avoids U (Arm64.fop .w64 FOps.round args)
    exact fop_av _ _ (fun _ _ => fround_av _ _) _
  case ARM64FCMPS =>
    show Val.Avoids U (Arm64.fcmp .w32 false args)
    exact fcmp_av _ _ _
  case ARM64FCMPD =>
    show Val.Avoids U (Arm64.fcmp .w64 false args)
    exact fcmp_av _ _ _
  case ARM64FCMPS0 =>
    show Val.Avoids U (Arm64.fcmp .w32 true args)
    exact fcmp_av _ _ _
  case ARM64FCMPD0 =>
    show Val.Avoids U (Arm64.fcmp .w64 true args)
    exact fcmp_av _ _ _
  case ARM64FCVTSD =>
    show Val.Avoids U (FOps.f32to64 (args.map (Arm64.fval .w32)))
    exact f32to64_av _
  case ARM64FCVTDS =>
    show Val.Avoids U (FOps.f64to32 (args.map (Arm64.fval .w64)))
    exact f64to32_av _
  case ARM64SCVTFWS =>
    show Val.Avoids U (Arm64.cvtf false .w32 .w32 args)
    exact cvtf_av _ _ _ _
  case ARM64SCVTFWD =>
    show Val.Avoids U (Arm64.cvtf false .w32 .w64 args)
    exact cvtf_av _ _ _ _
  case ARM64UCVTFWS =>
    show Val.Avoids U (Arm64.cvtf true .w32 .w32 args)
    exact cvtf_av _ _ _ _
  case ARM64UCVTFWD =>
    show Val.Avoids U (Arm64.cvtf true .w32 .w64 args)
    exact cvtf_av _ _ _ _
  case ARM64SCVTFS =>
    show Val.Avoids U (Arm64.cvtf false .w64 .w32 args)
    exact cvtf_av _ _ _ _
  case ARM64SCVTFD =>
    show Val.Avoids U (Arm64.cvtf false .w64 .w64 args)
    exact cvtf_av _ _ _ _
  case ARM64UCVTFS =>
    show Val.Avoids U (Arm64.cvtf true .w64 .w32 args)
    exact cvtf_av _ _ _ _
  case ARM64UCVTFD =>
    show Val.Avoids U (Arm64.cvtf true .w64 .w64 args)
    exact cvtf_av _ _ _ _
  case ARM64FCVTZSSW =>
    show Val.Avoids U (Arm64.fcvtz ty false .w32 .w32 args)
    exact fcvtz_av _ _ _ _ _
  case ARM64FCVTZSDW =>
    show Val.Avoids U (Arm64.fcvtz ty false .w64 .w32 args)
    exact fcvtz_av _ _ _ _ _
  case ARM64FCVTZUSW =>
    show Val.Avoids U (Arm64.fcvtz ty true .w32 .w32 args)
    exact fcvtz_av _ _ _ _ _
  case ARM64FCVTZUDW =>
    show Val.Avoids U (Arm64.fcvtz ty true .w64 .w32 args)
    exact fcvtz_av _ _ _ _ _
  case ARM64FCVTZSS =>
    show Val.Avoids U (Arm64.fcvtz ty false .w32 .w64 args)
    exact fcvtz_av _ _ _ _ _
  case ARM64FCVTZSD =>
    show Val.Avoids U (Arm64.fcvtz ty false .w64 .w64 args)
    exact fcvtz_av _ _ _ _ _
  case ARM64FCVTZUS =>
    show Val.Avoids U (Arm64.fcvtz ty true .w32 .w64 args)
    exact fcvtz_av _ _ _ _ _
  case ARM64FCVTZUD =>
    show Val.Avoids U (Arm64.fcvtz ty true .w64 .w64 args)
    exact fcvtz_av _ _ _ _ _
  case ARM64FMOVSconst =>
    show Val.Avoids U (FOps.const32 k)
    exact True.intro
  case ARM64FMOVDconst =>
    show Val.Avoids U (FOps.const64 k)
    exact True.intro
  case ARM64FMOVDgpfp =>
    show Val.Avoids U (Arm64.fmov .w64 ty args)
    exact fmov_av _ _ _
  case ARM64FMOVDfpgp =>
    show Val.Avoids U (Arm64.fmov .w64 ty args)
    exact fmov_av _ _ _
  case ARM64FMOVSgpfp =>
    show Val.Avoids U (Arm64.fmov .w32 ty args)
    exact fmov_av _ _ _
  case ARM64FMOVSfpgp =>
    show Val.Avoids U (Arm64.fmov .w32 ty args)
    exact fmov_av _ _ _
  case ARM64MOVDloadidx =>
    show Val.Avoids U (Arm64.loadIdx ty 8 1 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVWloadidx =>
    show Val.Avoids U (Arm64.loadIdx ty 4 1 true args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVWUloadidx =>
    show Val.Avoids U (Arm64.loadIdx ty 4 1 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVHloadidx =>
    show Val.Avoids U (Arm64.loadIdx ty 2 1 true args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVHUloadidx =>
    show Val.Avoids U (Arm64.loadIdx ty 2 1 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVBloadidx =>
    show Val.Avoids U (Arm64.loadIdx ty 1 1 true args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVBUloadidx =>
    show Val.Avoids U (Arm64.loadIdx ty 1 1 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64FMOVSloadidx =>
    show Val.Avoids U (Arm64.loadIdx ty 4 1 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64FMOVDloadidx =>
    show Val.Avoids U (Arm64.loadIdx ty 8 1 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVHloadidx2 =>
    show Val.Avoids U (Arm64.loadIdx ty 2 2 true args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVHUloadidx2 =>
    show Val.Avoids U (Arm64.loadIdx ty 2 2 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVWloadidx4 =>
    show Val.Avoids U (Arm64.loadIdx ty 4 4 true args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVWUloadidx4 =>
    show Val.Avoids U (Arm64.loadIdx ty 4 4 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64MOVDloadidx8 =>
    show Val.Avoids U (Arm64.loadIdx ty 8 8 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64FMOVSloadidx4 =>
    show Val.Avoids U (Arm64.loadIdx ty 4 4 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64FMOVDloadidx8 =>
    show Val.Avoids U (Arm64.loadIdx ty 8 8 false args)
    exact loadIdx_av hU _ _ _ _ h
  case ARM64LDAR =>
    show Val.Avoids U (atomicLoad ty args)
    exact atomicLoad_avoids hU _ h
  case ARM64LDARB =>
    show Val.Avoids U (atomicLoad ty args)
    exact atomicLoad_avoids hU _ h
  case ARM64LDARW =>
    show Val.Avoids U (atomicLoad ty args)
    exact atomicLoad_avoids hU _ h
  case ARM64LoweredZero =>
    show Val.Avoids U (Arm64.zero k args)
    exact zero_av hU _ h
  case ARM64LoweredZeroLoop =>
    show Val.Avoids U (Arm64.zero k args)
    exact zero_av hU _ h
  case ARM64LoweredMove =>
    show Val.Avoids U (Arm64.move k args)
    exact move_av hU _ h
  case ARM64LoweredMoveLoop =>
    show Val.Avoids U (Arm64.move k args)
    exact move_av hU _ h
  case ARM64LoweredWB =>
    show Val.Avoids U (wbOp k args)
    exact wbOp_avoids hU _ h
  case ARM64LoweredMemEq =>
    show Val.Avoids U (memEq args)
    exact memEq_avoids _
  all_goals exact True.intro

end GoFV.Proof.UnreadL
