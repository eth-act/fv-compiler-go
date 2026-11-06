import GoFV.Proof.Low.ArmMonoFam
import GoFV.Opt.LowerTerm

/-!
# The pure arm64 term ops are monotone, op by op (issue #385)

`evalPure_<op>`: for each op of `GoFV.Opt.LowerTerm.armTerm`, `Arm64.evalPure` at that op is its
family (`GoFV.Proof.Low.ArmMonoFam`), monotone; one declaration per op keeps each unfolding of
`Arm64.evalPure` at a concrete op small. `armPure_cases` assembles them
(`GoFV.Proof.Low.armPure_mono`).
-/

namespace GoFV.Proof.Low.Mono

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.Sem.Arm64 GoFV.Opt.LowerTerm

variable {as bs : List Val}

theorem evalPure_ARM64ADD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ADD ty k ax as) (Arm64.evalPure .ARM64ADD ty k ax bs) :=
  add_mono ty hr

theorem evalPure_ARM64ADDconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ADDconst ty k ax as) (Arm64.evalPure .ARM64ADDconst ty k ax bs) :=
  addK_mono ty (imm k) hr

theorem evalPure_ARM64SUB (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SUB ty k ax as) (Arm64.evalPure .ARM64SUB ty k ax bs) :=
  sub_mono ty hr

theorem evalPure_ARM64SUBconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SUBconst ty k ax as) (Arm64.evalPure .ARM64SUBconst ty k ax bs) :=
  addK_mono ty (-imm k) hr

theorem evalPure_ARM64MUL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MUL ty k ax as) (Arm64.evalPure .ARM64MUL ty k ax bs) :=
  op2_mono ty (· * ·) hr

theorem evalPure_ARM64MULW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MULW ty k ax as) (Arm64.evalPure .ARM64MULW ty k ax bs) :=
  op2w_mono ty (· * ·) hr

theorem evalPure_ARM64MNEG (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MNEG ty k ax as) (Arm64.evalPure .ARM64MNEG ty k ax bs) :=
  op2_mono ty (fun x y => -(x * y)) hr

theorem evalPure_ARM64MNEGW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MNEGW ty k ax as) (Arm64.evalPure .ARM64MNEGW ty k ax bs) :=
  op2w_mono ty (fun x y => -(x * y)) hr

theorem evalPure_ARM64MULH (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MULH ty k ax as) (Arm64.evalPure .ARM64MULH ty k ax bs) :=
  op2_mono ty smulh hr

theorem evalPure_ARM64UMULH (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UMULH ty k ax as) (Arm64.evalPure .ARM64UMULH ty k ax bs) :=
  op2_mono ty umulh hr

theorem evalPure_ARM64MULL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MULL ty k ax as) (Arm64.evalPure .ARM64MULL ty k ax bs) :=
  op2_mono ty smull hr

theorem evalPure_ARM64UMULL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UMULL ty k ax as) (Arm64.evalPure .ARM64UMULL ty k ax bs) :=
  op2_mono ty umull hr

theorem evalPure_ARM64DIV (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64DIV ty k ax as) (Arm64.evalPure .ARM64DIV ty k ax bs) :=
  op2_mono ty sdiv hr

theorem evalPure_ARM64UDIV (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UDIV ty k ax as) (Arm64.evalPure .ARM64UDIV ty k ax bs) :=
  op2_mono ty udiv hr

theorem evalPure_ARM64DIVW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64DIVW ty k ax as) (Arm64.evalPure .ARM64DIVW ty k ax bs) :=
  op2w_mono ty sdiv hr

theorem evalPure_ARM64UDIVW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UDIVW ty k ax as) (Arm64.evalPure .ARM64UDIVW ty k ax bs) :=
  op2w_mono ty udiv hr

theorem evalPure_ARM64MOD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOD ty k ax as) (Arm64.evalPure .ARM64MOD ty k ax bs) :=
  op2_mono ty srem hr

theorem evalPure_ARM64UMOD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UMOD ty k ax as) (Arm64.evalPure .ARM64UMOD ty k ax bs) :=
  op2_mono ty urem hr

theorem evalPure_ARM64MODW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MODW ty k ax as) (Arm64.evalPure .ARM64MODW ty k ax bs) :=
  op2w_mono ty srem hr

theorem evalPure_ARM64UMODW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UMODW ty k ax as) (Arm64.evalPure .ARM64UMODW ty k ax bs) :=
  op2w_mono ty urem hr

theorem evalPure_ARM64MADD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MADD ty k ax as) (Arm64.evalPure .ARM64MADD ty k ax bs) :=
  op3_mono ty (fun a x y => a + x * y) hr

theorem evalPure_ARM64MADDW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MADDW ty k ax as) (Arm64.evalPure .ARM64MADDW ty k ax bs) :=
  op3w_mono ty (fun a x y => a + x * y) hr

theorem evalPure_ARM64MSUB (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MSUB ty k ax as) (Arm64.evalPure .ARM64MSUB ty k ax bs) :=
  op3_mono ty (fun a x y => a - x * y) hr

theorem evalPure_ARM64MSUBW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MSUBW ty k ax as) (Arm64.evalPure .ARM64MSUBW ty k ax bs) :=
  op3w_mono ty (fun a x y => a - x * y) hr

theorem evalPure_ARM64NEG (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64NEG ty k ax as) (Arm64.evalPure .ARM64NEG ty k ax bs) :=
  op1_mono ty (- ·) hr

theorem evalPure_ARM64MVN (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MVN ty k ax as) (Arm64.evalPure .ARM64MVN ty k ax bs) :=
  op1_mono ty (~~~ ·) hr

theorem evalPure_ARM64AND (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64AND ty k ax as) (Arm64.evalPure .ARM64AND ty k ax bs) :=
  op2_mono ty (· &&& ·) hr

theorem evalPure_ARM64ANDconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ANDconst ty k ax as) (Arm64.evalPure .ARM64ANDconst ty k ax bs) :=
  op1_mono ty (· &&& imm k) hr

theorem evalPure_ARM64OR (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64OR ty k ax as) (Arm64.evalPure .ARM64OR ty k ax bs) :=
  op2_mono ty (· ||| ·) hr

theorem evalPure_ARM64ORconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ORconst ty k ax as) (Arm64.evalPure .ARM64ORconst ty k ax bs) :=
  op1_mono ty (· ||| imm k) hr

theorem evalPure_ARM64XOR (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64XOR ty k ax as) (Arm64.evalPure .ARM64XOR ty k ax bs) :=
  op2_mono ty (· ^^^ ·) hr

theorem evalPure_ARM64XORconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64XORconst ty k ax as) (Arm64.evalPure .ARM64XORconst ty k ax bs) :=
  op1_mono ty (· ^^^ imm k) hr

theorem evalPure_ARM64BIC (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64BIC ty k ax as) (Arm64.evalPure .ARM64BIC ty k ax bs) :=
  op2_mono ty (fun x y => x &&& ~~~y) hr

theorem evalPure_ARM64EON (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64EON ty k ax as) (Arm64.evalPure .ARM64EON ty k ax bs) :=
  op2_mono ty (fun x y => x ^^^ ~~~y) hr

theorem evalPure_ARM64ORN (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ORN ty k ax as) (Arm64.evalPure .ARM64ORN ty k ax bs) :=
  op2_mono ty (fun x y => x ||| ~~~y) hr

theorem evalPure_ARM64SLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SLL ty k ax as) (Arm64.evalPure .ARM64SLL ty k ax bs) :=
  op2_mono ty (fun x y => x <<< (y.toNat % 64)) hr

theorem evalPure_ARM64SRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SRL ty k ax as) (Arm64.evalPure .ARM64SRL ty k ax bs) :=
  op2_mono ty (fun x y => x >>> (y.toNat % 64)) hr

theorem evalPure_ARM64SRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SRA ty k ax as) (Arm64.evalPure .ARM64SRA ty k ax bs) :=
  op2_mono ty (fun x y => x.sshiftRight (y.toNat % 64)) hr

theorem evalPure_ARM64ROR (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ROR ty k ax as) (Arm64.evalPure .ARM64ROR ty k ax bs) :=
  op2_mono ty (fun x y => x.rotateRight (y.toNat % 64)) hr

theorem evalPure_ARM64RORW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64RORW ty k ax as) (Arm64.evalPure .ARM64RORW ty k ax bs) :=
  op2w_mono ty (fun x y => x.rotateRight (y.toNat % 32)) hr

theorem evalPure_ARM64SLLconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SLLconst ty k ax as) (Arm64.evalPure .ARM64SLLconst ty k ax bs) :=
  op1_mono ty (Shift.ll.apply · (amt k)) hr

theorem evalPure_ARM64SRLconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SRLconst ty k ax as) (Arm64.evalPure .ARM64SRLconst ty k ax bs) :=
  op1_mono ty (Shift.rl.apply · (amt k)) hr

theorem evalPure_ARM64SRAconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SRAconst ty k ax as) (Arm64.evalPure .ARM64SRAconst ty k ax bs) :=
  op1_mono ty (Shift.ra.apply · (amt k)) hr

theorem evalPure_ARM64RORconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64RORconst ty k ax as) (Arm64.evalPure .ARM64RORconst ty k ax bs) :=
  op1_mono ty (Shift.ro.apply · (amt k)) hr

theorem evalPure_ARM64RORWconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64RORWconst ty k ax as) (Arm64.evalPure .ARM64RORWconst ty k ax bs) :=
  op1w_mono ty (Shift.ro.apply · (amt k)) hr

theorem evalPure_ARM64EXTRconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64EXTRconst ty k ax as) (Arm64.evalPure .ARM64EXTRconst ty k ax bs) :=
  op2_mono ty (extr (amt k)) hr

theorem evalPure_ARM64EXTRWconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64EXTRWconst ty k ax as) (Arm64.evalPure .ARM64EXTRWconst ty k ax bs) :=
  op2w_mono ty (extr (amt k)) hr

theorem evalPure_ARM64MVNshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MVNshiftLL ty k ax as) (Arm64.evalPure .ARM64MVNshiftLL ty k ax bs) :=
  op1_mono ty (fun x => ~~~(shifted .ll k x)) hr

theorem evalPure_ARM64MVNshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MVNshiftRL ty k ax as) (Arm64.evalPure .ARM64MVNshiftRL ty k ax bs) :=
  op1_mono ty (fun x => ~~~(shifted .rl k x)) hr

theorem evalPure_ARM64MVNshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MVNshiftRA ty k ax as) (Arm64.evalPure .ARM64MVNshiftRA ty k ax bs) :=
  op1_mono ty (fun x => ~~~(shifted .ra k x)) hr

theorem evalPure_ARM64MVNshiftRO (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MVNshiftRO ty k ax as) (Arm64.evalPure .ARM64MVNshiftRO ty k ax bs) :=
  op1_mono ty (fun x => ~~~(shifted .ro k x)) hr

theorem evalPure_ARM64NEGshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64NEGshiftLL ty k ax as) (Arm64.evalPure .ARM64NEGshiftLL ty k ax bs) :=
  op1_mono ty (fun x => -(shifted .ll k x)) hr

theorem evalPure_ARM64NEGshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64NEGshiftRL ty k ax as) (Arm64.evalPure .ARM64NEGshiftRL ty k ax bs) :=
  op1_mono ty (fun x => -(shifted .rl k x)) hr

theorem evalPure_ARM64NEGshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64NEGshiftRA ty k ax as) (Arm64.evalPure .ARM64NEGshiftRA ty k ax bs) :=
  op1_mono ty (fun x => -(shifted .ra k x)) hr

theorem evalPure_ARM64ADDshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ADDshiftLL ty k ax as) (Arm64.evalPure .ARM64ADDshiftLL ty k ax bs) :=
  addSh_mono ty .ll k hr

theorem evalPure_ARM64ADDshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ADDshiftRL ty k ax as) (Arm64.evalPure .ARM64ADDshiftRL ty k ax bs) :=
  addSh_mono ty .rl k hr

theorem evalPure_ARM64ADDshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ADDshiftRA ty k ax as) (Arm64.evalPure .ARM64ADDshiftRA ty k ax bs) :=
  addSh_mono ty .ra k hr

theorem evalPure_ARM64SUBshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SUBshiftLL ty k ax as) (Arm64.evalPure .ARM64SUBshiftLL ty k ax bs) :=
  subSh_mono ty .ll k hr

theorem evalPure_ARM64SUBshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SUBshiftRL ty k ax as) (Arm64.evalPure .ARM64SUBshiftRL ty k ax bs) :=
  subSh_mono ty .rl k hr

theorem evalPure_ARM64SUBshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SUBshiftRA ty k ax as) (Arm64.evalPure .ARM64SUBshiftRA ty k ax bs) :=
  subSh_mono ty .ra k hr

theorem evalPure_ARM64ANDshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ANDshiftLL ty k ax as) (Arm64.evalPure .ARM64ANDshiftLL ty k ax bs) :=
  opSh_mono ty .ll k (· &&& ·) hr

theorem evalPure_ARM64ANDshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ANDshiftRL ty k ax as) (Arm64.evalPure .ARM64ANDshiftRL ty k ax bs) :=
  opSh_mono ty .rl k (· &&& ·) hr

theorem evalPure_ARM64ANDshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ANDshiftRA ty k ax as) (Arm64.evalPure .ARM64ANDshiftRA ty k ax bs) :=
  opSh_mono ty .ra k (· &&& ·) hr

theorem evalPure_ARM64ANDshiftRO (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ANDshiftRO ty k ax as) (Arm64.evalPure .ARM64ANDshiftRO ty k ax bs) :=
  opSh_mono ty .ro k (· &&& ·) hr

theorem evalPure_ARM64ORshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ORshiftLL ty k ax as) (Arm64.evalPure .ARM64ORshiftLL ty k ax bs) :=
  opSh_mono ty .ll k (· ||| ·) hr

theorem evalPure_ARM64ORshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ORshiftRL ty k ax as) (Arm64.evalPure .ARM64ORshiftRL ty k ax bs) :=
  opSh_mono ty .rl k (· ||| ·) hr

theorem evalPure_ARM64ORshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ORshiftRA ty k ax as) (Arm64.evalPure .ARM64ORshiftRA ty k ax bs) :=
  opSh_mono ty .ra k (· ||| ·) hr

theorem evalPure_ARM64ORshiftRO (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ORshiftRO ty k ax as) (Arm64.evalPure .ARM64ORshiftRO ty k ax bs) :=
  opSh_mono ty .ro k (· ||| ·) hr

theorem evalPure_ARM64XORshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64XORshiftLL ty k ax as) (Arm64.evalPure .ARM64XORshiftLL ty k ax bs) :=
  opSh_mono ty .ll k (· ^^^ ·) hr

theorem evalPure_ARM64XORshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64XORshiftRL ty k ax as) (Arm64.evalPure .ARM64XORshiftRL ty k ax bs) :=
  opSh_mono ty .rl k (· ^^^ ·) hr

theorem evalPure_ARM64XORshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64XORshiftRA ty k ax as) (Arm64.evalPure .ARM64XORshiftRA ty k ax bs) :=
  opSh_mono ty .ra k (· ^^^ ·) hr

theorem evalPure_ARM64XORshiftRO (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64XORshiftRO ty k ax as) (Arm64.evalPure .ARM64XORshiftRO ty k ax bs) :=
  opSh_mono ty .ro k (· ^^^ ·) hr

theorem evalPure_ARM64BICshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64BICshiftLL ty k ax as) (Arm64.evalPure .ARM64BICshiftLL ty k ax bs) :=
  opSh_mono ty .ll k (fun x y => x &&& ~~~y) hr

theorem evalPure_ARM64BICshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64BICshiftRL ty k ax as) (Arm64.evalPure .ARM64BICshiftRL ty k ax bs) :=
  opSh_mono ty .rl k (fun x y => x &&& ~~~y) hr

theorem evalPure_ARM64BICshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64BICshiftRA ty k ax as) (Arm64.evalPure .ARM64BICshiftRA ty k ax bs) :=
  opSh_mono ty .ra k (fun x y => x &&& ~~~y) hr

theorem evalPure_ARM64BICshiftRO (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64BICshiftRO ty k ax as) (Arm64.evalPure .ARM64BICshiftRO ty k ax bs) :=
  opSh_mono ty .ro k (fun x y => x &&& ~~~y) hr

theorem evalPure_ARM64EONshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64EONshiftLL ty k ax as) (Arm64.evalPure .ARM64EONshiftLL ty k ax bs) :=
  opSh_mono ty .ll k (fun x y => x ^^^ ~~~y) hr

theorem evalPure_ARM64EONshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64EONshiftRL ty k ax as) (Arm64.evalPure .ARM64EONshiftRL ty k ax bs) :=
  opSh_mono ty .rl k (fun x y => x ^^^ ~~~y) hr

theorem evalPure_ARM64EONshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64EONshiftRA ty k ax as) (Arm64.evalPure .ARM64EONshiftRA ty k ax bs) :=
  opSh_mono ty .ra k (fun x y => x ^^^ ~~~y) hr

theorem evalPure_ARM64EONshiftRO (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64EONshiftRO ty k ax as) (Arm64.evalPure .ARM64EONshiftRO ty k ax bs) :=
  opSh_mono ty .ro k (fun x y => x ^^^ ~~~y) hr

theorem evalPure_ARM64ORNshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ORNshiftLL ty k ax as) (Arm64.evalPure .ARM64ORNshiftLL ty k ax bs) :=
  opSh_mono ty .ll k (fun x y => x ||| ~~~y) hr

theorem evalPure_ARM64ORNshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ORNshiftRL ty k ax as) (Arm64.evalPure .ARM64ORNshiftRL ty k ax bs) :=
  opSh_mono ty .rl k (fun x y => x ||| ~~~y) hr

theorem evalPure_ARM64ORNshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ORNshiftRA ty k ax as) (Arm64.evalPure .ARM64ORNshiftRA ty k ax bs) :=
  opSh_mono ty .ra k (fun x y => x ||| ~~~y) hr

theorem evalPure_ARM64ORNshiftRO (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ORNshiftRO ty k ax as) (Arm64.evalPure .ARM64ORNshiftRO ty k ax bs) :=
  opSh_mono ty .ro k (fun x y => x ||| ~~~y) hr

theorem evalPure_ARM64UBFX (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UBFX ty k ax as) (Arm64.evalPure .ARM64UBFX ty k ax bs) :=
  op1_mono ty (ubfx k) hr

theorem evalPure_ARM64SBFX (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SBFX ty k ax as) (Arm64.evalPure .ARM64SBFX ty k ax bs) :=
  op1_mono ty (sbfx k) hr

theorem evalPure_ARM64UBFIZ (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UBFIZ ty k ax as) (Arm64.evalPure .ARM64UBFIZ ty k ax bs) :=
  op1_mono ty (ubfiz k) hr

theorem evalPure_ARM64SBFIZ (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SBFIZ ty k ax as) (Arm64.evalPure .ARM64SBFIZ ty k ax bs) :=
  op1_mono ty (sbfiz k) hr

theorem evalPure_ARM64BFI (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64BFI ty k ax as) (Arm64.evalPure .ARM64BFI ty k ax bs) :=
  op2_mono ty (bfi k) hr

theorem evalPure_ARM64BFXIL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64BFXIL ty k ax as) (Arm64.evalPure .ARM64BFXIL ty k ax bs) :=
  op2_mono ty (bfxil k) hr

theorem evalPure_ARM64CLZ (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CLZ ty k ax as) (Arm64.evalPure .ARM64CLZ ty k ax bs) :=
  op1_mono ty clz hr

theorem evalPure_ARM64CLZW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CLZW ty k ax as) (Arm64.evalPure .ARM64CLZW ty k ax bs) :=
  op1w_mono ty clz hr

theorem evalPure_ARM64RBIT (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64RBIT ty k ax as) (Arm64.evalPure .ARM64RBIT ty k ax bs) :=
  op1_mono ty rbit hr

theorem evalPure_ARM64RBITW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64RBITW ty k ax as) (Arm64.evalPure .ARM64RBITW ty k ax bs) :=
  op1w_mono ty rbit hr

theorem evalPure_ARM64REV (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64REV ty k ax as) (Arm64.evalPure .ARM64REV ty k ax bs) :=
  op1_mono ty rev hr

theorem evalPure_ARM64REVW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64REVW ty k ax as) (Arm64.evalPure .ARM64REVW ty k ax bs) :=
  op1w_mono ty rev hr

theorem evalPure_ARM64REV16 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64REV16 ty k ax as) (Arm64.evalPure .ARM64REV16 ty k ax bs) :=
  op1_mono ty rev16 hr

theorem evalPure_ARM64REV16W (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64REV16W ty k ax as) (Arm64.evalPure .ARM64REV16W ty k ax bs) :=
  op1w_mono ty rev16 hr

theorem evalPure_ARM64MOVBreg (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVBreg ty k ax as) (Arm64.evalPure .ARM64MOVBreg ty k ax bs) :=
  op1_mono ty (ext true 8) hr

theorem evalPure_ARM64MOVBUreg (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVBUreg ty k ax as) (Arm64.evalPure .ARM64MOVBUreg ty k ax bs) :=
  op1_mono ty (ext false 8) hr

theorem evalPure_ARM64MOVHreg (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVHreg ty k ax as) (Arm64.evalPure .ARM64MOVHreg ty k ax bs) :=
  op1_mono ty (ext true 16) hr

theorem evalPure_ARM64MOVHUreg (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVHUreg ty k ax as) (Arm64.evalPure .ARM64MOVHUreg ty k ax bs) :=
  op1_mono ty (ext false 16) hr

theorem evalPure_ARM64MOVWreg (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVWreg ty k ax as) (Arm64.evalPure .ARM64MOVWreg ty k ax bs) :=
  op1_mono ty (ext true 32) hr

theorem evalPure_ARM64MOVWUreg (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVWUreg ty k ax as) (Arm64.evalPure .ARM64MOVWUreg ty k ax bs) :=
  op1_mono ty (ext false 32) hr

theorem evalPure_ARM64MOVDconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVDconst ty k ax as) (Arm64.evalPure .ARM64MOVDconst ty k ax bs) :=
  Refines.refl _

theorem evalPure_ARM64ZERO (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64ZERO ty k ax as) (Arm64.evalPure .ARM64ZERO ty k ax bs) :=
  Refines.refl _

theorem evalPure_ARM64CMP (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMP ty k ax as) (Arm64.evalPure .ARM64CMP ty k ax bs) :=
  by
  rcases hr with _ | ⟨h1, _ | ⟨h2, _ | ⟨_, _⟩⟩⟩
  · exact .poison _
  · exact .poison _
  · exact cmp_mono h1 h2
  · exact .poison _

theorem evalPure_ARM64CMPconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMPconst ty k ax as) (Arm64.evalPure .ARM64CMPconst ty k ax bs) :=
  by
  rcases hr with _ | ⟨h1, _ | ⟨_, _⟩⟩
  · exact .poison _
  · exact cmp_mono h1 (Refines.refl _)
  · exact .poison _

theorem evalPure_ARM64CMPW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMPW ty k ax as) (Arm64.evalPure .ARM64CMPW ty k ax bs) :=
  cmp2w_mono (fun x y => subFlags x y) hr

theorem evalPure_ARM64CMPWconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMPWconst ty k ax as) (Arm64.evalPure .ARM64CMPWconst ty k ax bs) :=
  cmp1w_mono (fun x => subFlags x (imm32 k)) hr

theorem evalPure_ARM64CMN (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMN ty k ax as) (Arm64.evalPure .ARM64CMN ty k ax bs) :=
  cmp2_mono (fun x y => addWithCarry x y false) hr

theorem evalPure_ARM64CMNconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMNconst ty k ax as) (Arm64.evalPure .ARM64CMNconst ty k ax bs) :=
  cmp1_mono (fun x => addWithCarry x (imm k) false) hr

theorem evalPure_ARM64CMNW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMNW ty k ax as) (Arm64.evalPure .ARM64CMNW ty k ax bs) :=
  cmp2w_mono (fun x y => addWithCarry x y false) hr

theorem evalPure_ARM64CMNWconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMNWconst ty k ax as) (Arm64.evalPure .ARM64CMNWconst ty k ax bs) :=
  cmp1w_mono (fun x => addWithCarry x (imm32 k) false) hr

theorem evalPure_ARM64TST (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64TST ty k ax as) (Arm64.evalPure .ARM64TST ty k ax bs) :=
  flags2_mono (fun x y => logicFlags (x &&& y)) hr

theorem evalPure_ARM64TSTconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64TSTconst ty k ax as) (Arm64.evalPure .ARM64TSTconst ty k ax bs) :=
  flags1_mono (fun x => logicFlags (x &&& imm k)) hr

theorem evalPure_ARM64TSTW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64TSTW ty k ax as) (Arm64.evalPure .ARM64TSTW ty k ax bs) :=
  flags2w_mono (fun x y => logicFlags (x &&& y)) hr

theorem evalPure_ARM64TSTWconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64TSTWconst ty k ax as) (Arm64.evalPure .ARM64TSTWconst ty k ax bs) :=
  flags1w_mono (fun x => logicFlags (x &&& imm32 k)) hr

theorem evalPure_ARM64CMPshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMPshiftLL ty k ax as) (Arm64.evalPure .ARM64CMPshiftLL ty k ax bs) :=
  cmp2_mono (fun x y => subFlags x (shifted .ll k y)) hr

theorem evalPure_ARM64CMPshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMPshiftRL ty k ax as) (Arm64.evalPure .ARM64CMPshiftRL ty k ax bs) :=
  cmp2_mono (fun x y => subFlags x (shifted .rl k y)) hr

theorem evalPure_ARM64CMPshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMPshiftRA ty k ax as) (Arm64.evalPure .ARM64CMPshiftRA ty k ax bs) :=
  cmp2_mono (fun x y => subFlags x (shifted .ra k y)) hr

theorem evalPure_ARM64CMNshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMNshiftLL ty k ax as) (Arm64.evalPure .ARM64CMNshiftLL ty k ax bs) :=
  cmp2_mono (fun x y => addWithCarry x (shifted .ll k y) false) hr

theorem evalPure_ARM64CMNshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMNshiftRL ty k ax as) (Arm64.evalPure .ARM64CMNshiftRL ty k ax bs) :=
  cmp2_mono (fun x y => addWithCarry x (shifted .rl k y) false) hr

theorem evalPure_ARM64CMNshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CMNshiftRA ty k ax as) (Arm64.evalPure .ARM64CMNshiftRA ty k ax bs) :=
  cmp2_mono (fun x y => addWithCarry x (shifted .ra k y) false) hr

theorem evalPure_ARM64TSTshiftLL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64TSTshiftLL ty k ax as) (Arm64.evalPure .ARM64TSTshiftLL ty k ax bs) :=
  flags2_mono (fun x y => logicFlags (x &&& shifted .ll k y)) hr

theorem evalPure_ARM64TSTshiftRL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64TSTshiftRL ty k ax as) (Arm64.evalPure .ARM64TSTshiftRL ty k ax bs) :=
  flags2_mono (fun x y => logicFlags (x &&& shifted .rl k y)) hr

theorem evalPure_ARM64TSTshiftRA (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64TSTshiftRA ty k ax as) (Arm64.evalPure .ARM64TSTshiftRA ty k ax bs) :=
  flags2_mono (fun x y => logicFlags (x &&& shifted .ra k y)) hr

theorem evalPure_ARM64TSTshiftRO (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64TSTshiftRO ty k ax as) (Arm64.evalPure .ARM64TSTshiftRO ty k ax bs) :=
  flags2_mono (fun x y => logicFlags (x &&& shifted .ro k y)) hr

theorem evalPure_ARM64FlagConstant (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FlagConstant ty k ax as) (Arm64.evalPure .ARM64FlagConstant ty k ax bs) :=
  Refines.refl _

theorem evalPure_ARM64InvertFlags (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64InvertFlags ty k ax as) (Arm64.evalPure .ARM64InvertFlags ty k ax bs) :=
  by
  rcases hr with _ | ⟨h1, _ | ⟨_, _⟩⟩
  · exact .poison _
  · exact invertFlags_mono h1
  · exact .poison _

theorem evalPure_ARM64CSEL (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CSEL ty k ax as) (Arm64.evalPure .ARM64CSEL ty k ax bs) :=
  csel_mono ty k none hr

theorem evalPure_ARM64CSEL0 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CSEL0 ty k ax as) (Arm64.evalPure .ARM64CSEL0 ty k ax bs) :=
  csel0_mono ty k hr

theorem evalPure_ARM64CSINC (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CSINC ty k ax as) (Arm64.evalPure .ARM64CSINC ty k ax bs) :=
  csel_mono ty k (some (· + 1)) hr

theorem evalPure_ARM64CSINV (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CSINV ty k ax as) (Arm64.evalPure .ARM64CSINV ty k ax bs) :=
  csel_mono ty k (some (~~~ ·)) hr

theorem evalPure_ARM64CSNEG (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CSNEG ty k ax as) (Arm64.evalPure .ARM64CSNEG ty k ax bs) :=
  csel_mono ty k (some (- ·)) hr

theorem evalPure_ARM64CSETM (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64CSETM ty k ax as) (Arm64.evalPure .ARM64CSETM ty k ax bs) :=
  csetm_mono ty k hr

theorem evalPure_ARM64Equal (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64Equal ty k ax as) (Arm64.evalPure .ARM64Equal ty k ax bs) :=
  cset_mono ty .ARM64Equal hr

theorem evalPure_ARM64NotEqual (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64NotEqual ty k ax as) (Arm64.evalPure .ARM64NotEqual ty k ax bs) :=
  cset_mono ty .ARM64NotEqual hr

theorem evalPure_ARM64LessThan (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64LessThan ty k ax as) (Arm64.evalPure .ARM64LessThan ty k ax bs) :=
  cset_mono ty .ARM64LessThan hr

theorem evalPure_ARM64LessEqual (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64LessEqual ty k ax as) (Arm64.evalPure .ARM64LessEqual ty k ax bs) :=
  cset_mono ty .ARM64LessEqual hr

theorem evalPure_ARM64GreaterThan (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64GreaterThan ty k ax as) (Arm64.evalPure .ARM64GreaterThan ty k ax bs) :=
  cset_mono ty .ARM64GreaterThan hr

theorem evalPure_ARM64GreaterEqual (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64GreaterEqual ty k ax as) (Arm64.evalPure .ARM64GreaterEqual ty k ax bs) :=
  cset_mono ty .ARM64GreaterEqual hr

theorem evalPure_ARM64LessThanU (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64LessThanU ty k ax as) (Arm64.evalPure .ARM64LessThanU ty k ax bs) :=
  cset_mono ty .ARM64LessThanU hr

theorem evalPure_ARM64LessEqualU (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64LessEqualU ty k ax as) (Arm64.evalPure .ARM64LessEqualU ty k ax bs) :=
  cset_mono ty .ARM64LessEqualU hr

theorem evalPure_ARM64GreaterThanU (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64GreaterThanU ty k ax as) (Arm64.evalPure .ARM64GreaterThanU ty k ax bs) :=
  cset_mono ty .ARM64GreaterThanU hr

theorem evalPure_ARM64GreaterEqualU (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64GreaterEqualU ty k ax as) (Arm64.evalPure .ARM64GreaterEqualU ty k ax bs) :=
  cset_mono ty .ARM64GreaterEqualU hr

theorem evalPure_ARM64LessThanF (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64LessThanF ty k ax as) (Arm64.evalPure .ARM64LessThanF ty k ax bs) :=
  cset_mono ty .ARM64LessThanF hr

theorem evalPure_ARM64LessEqualF (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64LessEqualF ty k ax as) (Arm64.evalPure .ARM64LessEqualF ty k ax bs) :=
  cset_mono ty .ARM64LessEqualF hr

theorem evalPure_ARM64GreaterThanF (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64GreaterThanF ty k ax as) (Arm64.evalPure .ARM64GreaterThanF ty k ax bs) :=
  cset_mono ty .ARM64GreaterThanF hr

theorem evalPure_ARM64GreaterEqualF (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64GreaterEqualF ty k ax as) (Arm64.evalPure .ARM64GreaterEqualF ty k ax bs) :=
  cset_mono ty .ARM64GreaterEqualF hr

theorem evalPure_ARM64NotLessThanF (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64NotLessThanF ty k ax as) (Arm64.evalPure .ARM64NotLessThanF ty k ax bs) :=
  cset_mono ty .ARM64NotLessThanF hr

theorem evalPure_ARM64NotLessEqualF (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64NotLessEqualF ty k ax as) (Arm64.evalPure .ARM64NotLessEqualF ty k ax bs) :=
  cset_mono ty .ARM64NotLessEqualF hr

theorem evalPure_ARM64NotGreaterThanF (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64NotGreaterThanF ty k ax as) (Arm64.evalPure .ARM64NotGreaterThanF ty k ax bs) :=
  cset_mono ty .ARM64NotGreaterThanF hr

theorem evalPure_ARM64NotGreaterEqualF (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64NotGreaterEqualF ty k ax as) (Arm64.evalPure .ARM64NotGreaterEqualF ty k ax bs) :=
  cset_mono ty .ARM64NotGreaterEqualF hr

theorem evalPure_ARM64LessThanNoov (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64LessThanNoov ty k ax as) (Arm64.evalPure .ARM64LessThanNoov ty k ax bs) :=
  cset_mono ty .ARM64LessThanNoov hr

theorem evalPure_ARM64GreaterEqualNoov (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64GreaterEqualNoov ty k ax as) (Arm64.evalPure .ARM64GreaterEqualNoov ty k ax bs) :=
  cset_mono ty .ARM64GreaterEqualNoov hr

theorem evalPure_ARM64FADDS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FADDS ty k ax as) (Arm64.evalPure .ARM64FADDS ty k ax bs) :=
  fop_mono_add .w32 hr

theorem evalPure_ARM64FADDD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FADDD ty k ax as) (Arm64.evalPure .ARM64FADDD ty k ax bs) :=
  fop_mono_add .w64 hr

theorem evalPure_ARM64FSUBS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FSUBS ty k ax as) (Arm64.evalPure .ARM64FSUBS ty k ax bs) :=
  fop_mono_sub .w32 hr

theorem evalPure_ARM64FSUBD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FSUBD ty k ax as) (Arm64.evalPure .ARM64FSUBD ty k ax bs) :=
  fop_mono_sub .w64 hr

theorem evalPure_ARM64FMULS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMULS ty k ax as) (Arm64.evalPure .ARM64FMULS ty k ax bs) :=
  fop_mono_mul .w32 hr

theorem evalPure_ARM64FMULD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMULD ty k ax as) (Arm64.evalPure .ARM64FMULD ty k ax bs) :=
  fop_mono_mul .w64 hr

theorem evalPure_ARM64FNMULS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FNMULS ty k ax as) (Arm64.evalPure .ARM64FNMULS ty k ax bs) :=
  fnmul_mono .w32 hr

theorem evalPure_ARM64FNMULD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FNMULD ty k ax as) (Arm64.evalPure .ARM64FNMULD ty k ax bs) :=
  fnmul_mono .w64 hr

theorem evalPure_ARM64FDIVS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FDIVS ty k ax as) (Arm64.evalPure .ARM64FDIVS ty k ax bs) :=
  fop_mono_div .w32 hr

theorem evalPure_ARM64FDIVD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FDIVD ty k ax as) (Arm64.evalPure .ARM64FDIVD ty k ax bs) :=
  fop_mono_div .w64 hr

theorem evalPure_ARM64FABSS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FABSS ty k ax as) (Arm64.evalPure .ARM64FABSS ty k ax bs) :=
  fop_mono_abs .w32 hr

theorem evalPure_ARM64FABSD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FABSD ty k ax as) (Arm64.evalPure .ARM64FABSD ty k ax bs) :=
  fop_mono_abs .w64 hr

theorem evalPure_ARM64FNEGS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FNEGS ty k ax as) (Arm64.evalPure .ARM64FNEGS ty k ax bs) :=
  fop_mono_neg .w32 hr

theorem evalPure_ARM64FNEGD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FNEGD ty k ax as) (Arm64.evalPure .ARM64FNEGD ty k ax bs) :=
  fop_mono_neg .w64 hr

theorem evalPure_ARM64FSQRTS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FSQRTS ty k ax as) (Arm64.evalPure .ARM64FSQRTS ty k ax bs) :=
  fop_mono_sqrt .w32 hr

theorem evalPure_ARM64FSQRTD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FSQRTD ty k ax as) (Arm64.evalPure .ARM64FSQRTD ty k ax bs) :=
  fop_mono_sqrt .w64 hr

theorem evalPure_ARM64FMINS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMINS ty k ax as) (Arm64.evalPure .ARM64FMINS ty k ax bs) :=
  fop_mono_min .w32 hr

theorem evalPure_ARM64FMIND (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMIND ty k ax as) (Arm64.evalPure .ARM64FMIND ty k ax bs) :=
  fop_mono_min .w64 hr

theorem evalPure_ARM64FMAXS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMAXS ty k ax as) (Arm64.evalPure .ARM64FMAXS ty k ax bs) :=
  fop_mono_max .w32 hr

theorem evalPure_ARM64FMAXD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMAXD ty k ax as) (Arm64.evalPure .ARM64FMAXD ty k ax bs) :=
  fop_mono_max .w64 hr

theorem evalPure_ARM64FMADDS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMADDS ty k ax as) (Arm64.evalPure .ARM64FMADDS ty k ax bs) :=
  fmadd_mono .w32 false false hr

theorem evalPure_ARM64FMADDD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMADDD ty k ax as) (Arm64.evalPure .ARM64FMADDD ty k ax bs) :=
  fmadd_mono .w64 false false hr

theorem evalPure_ARM64FMSUBS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMSUBS ty k ax as) (Arm64.evalPure .ARM64FMSUBS ty k ax bs) :=
  fmadd_mono .w32 false true hr

theorem evalPure_ARM64FMSUBD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMSUBD ty k ax as) (Arm64.evalPure .ARM64FMSUBD ty k ax bs) :=
  fmadd_mono .w64 false true hr

theorem evalPure_ARM64FNMADDS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FNMADDS ty k ax as) (Arm64.evalPure .ARM64FNMADDS ty k ax bs) :=
  fmadd_mono .w32 true true hr

theorem evalPure_ARM64FNMADDD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FNMADDD ty k ax as) (Arm64.evalPure .ARM64FNMADDD ty k ax bs) :=
  fmadd_mono .w64 true true hr

theorem evalPure_ARM64FNMSUBS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FNMSUBS ty k ax as) (Arm64.evalPure .ARM64FNMSUBS ty k ax bs) :=
  fmadd_mono .w32 true false hr

theorem evalPure_ARM64FNMSUBD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FNMSUBD ty k ax as) (Arm64.evalPure .ARM64FNMSUBD ty k ax bs) :=
  fmadd_mono .w64 true false hr

theorem evalPure_ARM64FRINTAD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FRINTAD ty k ax as) (Arm64.evalPure .ARM64FRINTAD ty k ax bs) :=
  fop_mono_roundInt .w64 .rna hr

theorem evalPure_ARM64FRINTMD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FRINTMD ty k ax as) (Arm64.evalPure .ARM64FRINTMD ty k ax bs) :=
  fop_mono_roundInt .w64 .rmi hr

theorem evalPure_ARM64FRINTND (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FRINTND ty k ax as) (Arm64.evalPure .ARM64FRINTND ty k ax bs) :=
  fop_mono_roundInt .w64 .rne hr

theorem evalPure_ARM64FRINTPD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FRINTPD ty k ax as) (Arm64.evalPure .ARM64FRINTPD ty k ax bs) :=
  fop_mono_roundInt .w64 .rpi hr

theorem evalPure_ARM64FRINTZD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FRINTZD ty k ax as) (Arm64.evalPure .ARM64FRINTZD ty k ax bs) :=
  fop_mono_roundInt .w64 .rz hr

theorem evalPure_ARM64LoweredRound32F (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64LoweredRound32F ty k ax as) (Arm64.evalPure .ARM64LoweredRound32F ty k ax bs) :=
  fop_mono_round .w32 hr

theorem evalPure_ARM64LoweredRound64F (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64LoweredRound64F ty k ax as) (Arm64.evalPure .ARM64LoweredRound64F ty k ax bs) :=
  fop_mono_round .w64 hr

theorem evalPure_ARM64FCMPS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCMPS ty k ax as) (Arm64.evalPure .ARM64FCMPS ty k ax bs) :=
  fcmp_mono .w32 false hr

theorem evalPure_ARM64FCMPD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCMPD ty k ax as) (Arm64.evalPure .ARM64FCMPD ty k ax bs) :=
  fcmp_mono .w64 false hr

theorem evalPure_ARM64FCMPS0 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCMPS0 ty k ax as) (Arm64.evalPure .ARM64FCMPS0 ty k ax bs) :=
  fcmp_mono .w32 true hr

theorem evalPure_ARM64FCMPD0 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCMPD0 ty k ax as) (Arm64.evalPure .ARM64FCMPD0 ty k ax bs) :=
  fcmp_mono .w64 true hr

theorem evalPure_ARM64FCVTSD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCVTSD ty k ax as) (Arm64.evalPure .ARM64FCVTSD ty k ax bs) :=
  cvtsd_mono hr

theorem evalPure_ARM64FCVTDS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCVTDS ty k ax as) (Arm64.evalPure .ARM64FCVTDS ty k ax bs) :=
  cvtds_mono hr

theorem evalPure_ARM64SCVTFWS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SCVTFWS ty k ax as) (Arm64.evalPure .ARM64SCVTFWS ty k ax bs) :=
  cvtf_mono false .w32 .w32 hr

theorem evalPure_ARM64SCVTFWD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SCVTFWD ty k ax as) (Arm64.evalPure .ARM64SCVTFWD ty k ax bs) :=
  cvtf_mono false .w32 .w64 hr

theorem evalPure_ARM64UCVTFWS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UCVTFWS ty k ax as) (Arm64.evalPure .ARM64UCVTFWS ty k ax bs) :=
  cvtf_mono true .w32 .w32 hr

theorem evalPure_ARM64UCVTFWD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UCVTFWD ty k ax as) (Arm64.evalPure .ARM64UCVTFWD ty k ax bs) :=
  cvtf_mono true .w32 .w64 hr

theorem evalPure_ARM64SCVTFS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SCVTFS ty k ax as) (Arm64.evalPure .ARM64SCVTFS ty k ax bs) :=
  cvtf_mono false .w64 .w32 hr

theorem evalPure_ARM64SCVTFD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64SCVTFD ty k ax as) (Arm64.evalPure .ARM64SCVTFD ty k ax bs) :=
  cvtf_mono false .w64 .w64 hr

theorem evalPure_ARM64UCVTFS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UCVTFS ty k ax as) (Arm64.evalPure .ARM64UCVTFS ty k ax bs) :=
  cvtf_mono true .w64 .w32 hr

theorem evalPure_ARM64UCVTFD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64UCVTFD ty k ax as) (Arm64.evalPure .ARM64UCVTFD ty k ax bs) :=
  cvtf_mono true .w64 .w64 hr

theorem evalPure_ARM64FCVTZSSW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCVTZSSW ty k ax as) (Arm64.evalPure .ARM64FCVTZSSW ty k ax bs) :=
  fcvtz_mono ty false .w32 .w32 hr

theorem evalPure_ARM64FCVTZSDW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCVTZSDW ty k ax as) (Arm64.evalPure .ARM64FCVTZSDW ty k ax bs) :=
  fcvtz_mono ty false .w64 .w32 hr

theorem evalPure_ARM64FCVTZUSW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCVTZUSW ty k ax as) (Arm64.evalPure .ARM64FCVTZUSW ty k ax bs) :=
  fcvtz_mono ty true .w32 .w32 hr

theorem evalPure_ARM64FCVTZUDW (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCVTZUDW ty k ax as) (Arm64.evalPure .ARM64FCVTZUDW ty k ax bs) :=
  fcvtz_mono ty true .w64 .w32 hr

theorem evalPure_ARM64FCVTZSS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCVTZSS ty k ax as) (Arm64.evalPure .ARM64FCVTZSS ty k ax bs) :=
  fcvtz_mono ty false .w32 .w64 hr

theorem evalPure_ARM64FCVTZSD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCVTZSD ty k ax as) (Arm64.evalPure .ARM64FCVTZSD ty k ax bs) :=
  fcvtz_mono ty false .w64 .w64 hr

theorem evalPure_ARM64FCVTZUS (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCVTZUS ty k ax as) (Arm64.evalPure .ARM64FCVTZUS ty k ax bs) :=
  fcvtz_mono ty true .w32 .w64 hr

theorem evalPure_ARM64FCVTZUD (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FCVTZUD ty k ax as) (Arm64.evalPure .ARM64FCVTZUD ty k ax bs) :=
  fcvtz_mono ty true .w64 .w64 hr

theorem evalPure_ARM64FMOVSconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMOVSconst ty k ax as) (Arm64.evalPure .ARM64FMOVSconst ty k ax bs) :=
  Refines.refl _

theorem evalPure_ARM64FMOVDconst (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMOVDconst ty k ax as) (Arm64.evalPure .ARM64FMOVDconst ty k ax bs) :=
  Refines.refl _

theorem evalPure_ARM64FMOVDgpfp (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMOVDgpfp ty k ax as) (Arm64.evalPure .ARM64FMOVDgpfp ty k ax bs) :=
  fmov_mono .w64 ty hr

theorem evalPure_ARM64FMOVDfpgp (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMOVDfpgp ty k ax as) (Arm64.evalPure .ARM64FMOVDfpgp ty k ax bs) :=
  fmov_mono .w64 ty hr

theorem evalPure_ARM64FMOVSgpfp (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMOVSgpfp ty k ax as) (Arm64.evalPure .ARM64FMOVSgpfp ty k ax bs) :=
  fmov_mono .w32 ty hr

theorem evalPure_ARM64FMOVSfpgp (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMOVSfpgp ty k ax as) (Arm64.evalPure .ARM64FMOVSfpgp ty k ax bs) :=
  fmov_mono .w32 ty hr

theorem evalPure_ARM64LoweredWB (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64LoweredWB ty k ax as) (Arm64.evalPure .ARM64LoweredWB ty k ax bs) :=
  GoFV.SSA.Sem.wbOp_mono k hr

theorem evalPure_ARM64MOVDloadidx (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVDloadidx ty k ax as) (Arm64.evalPure .ARM64MOVDloadidx ty k ax bs) :=
  loadIdx_mono ty 8 1 false hr

theorem evalPure_ARM64MOVWloadidx (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVWloadidx ty k ax as) (Arm64.evalPure .ARM64MOVWloadidx ty k ax bs) :=
  loadIdx_mono ty 4 1 true hr

theorem evalPure_ARM64MOVWUloadidx (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVWUloadidx ty k ax as) (Arm64.evalPure .ARM64MOVWUloadidx ty k ax bs) :=
  loadIdx_mono ty 4 1 false hr

theorem evalPure_ARM64MOVHloadidx (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVHloadidx ty k ax as) (Arm64.evalPure .ARM64MOVHloadidx ty k ax bs) :=
  loadIdx_mono ty 2 1 true hr

theorem evalPure_ARM64MOVHUloadidx (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVHUloadidx ty k ax as) (Arm64.evalPure .ARM64MOVHUloadidx ty k ax bs) :=
  loadIdx_mono ty 2 1 false hr

theorem evalPure_ARM64MOVBloadidx (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVBloadidx ty k ax as) (Arm64.evalPure .ARM64MOVBloadidx ty k ax bs) :=
  loadIdx_mono ty 1 1 true hr

theorem evalPure_ARM64MOVBUloadidx (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVBUloadidx ty k ax as) (Arm64.evalPure .ARM64MOVBUloadidx ty k ax bs) :=
  loadIdx_mono ty 1 1 false hr

theorem evalPure_ARM64FMOVSloadidx (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMOVSloadidx ty k ax as) (Arm64.evalPure .ARM64FMOVSloadidx ty k ax bs) :=
  loadIdx_mono ty 4 1 false hr

theorem evalPure_ARM64FMOVDloadidx (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMOVDloadidx ty k ax as) (Arm64.evalPure .ARM64FMOVDloadidx ty k ax bs) :=
  loadIdx_mono ty 8 1 false hr

theorem evalPure_ARM64MOVHloadidx2 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVHloadidx2 ty k ax as) (Arm64.evalPure .ARM64MOVHloadidx2 ty k ax bs) :=
  loadIdx_mono ty 2 2 true hr

theorem evalPure_ARM64MOVHUloadidx2 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVHUloadidx2 ty k ax as) (Arm64.evalPure .ARM64MOVHUloadidx2 ty k ax bs) :=
  loadIdx_mono ty 2 2 false hr

theorem evalPure_ARM64MOVWloadidx4 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVWloadidx4 ty k ax as) (Arm64.evalPure .ARM64MOVWloadidx4 ty k ax bs) :=
  loadIdx_mono ty 4 4 true hr

theorem evalPure_ARM64MOVWUloadidx4 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVWUloadidx4 ty k ax as) (Arm64.evalPure .ARM64MOVWUloadidx4 ty k ax bs) :=
  loadIdx_mono ty 4 4 false hr

theorem evalPure_ARM64MOVDloadidx8 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64MOVDloadidx8 ty k ax as) (Arm64.evalPure .ARM64MOVDloadidx8 ty k ax bs) :=
  loadIdx_mono ty 8 8 false hr

theorem evalPure_ARM64FMOVSloadidx4 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMOVSloadidx4 ty k ax as) (Arm64.evalPure .ARM64FMOVSloadidx4 ty k ax bs) :=
  loadIdx_mono ty 4 4 false hr

theorem evalPure_ARM64FMOVDloadidx8 (ty : Ty) (k : Int64) (ax : Option AuxRef) (hr : RefinesList as bs) :
    Refines (Arm64.evalPure .ARM64FMOVDloadidx8 ty k ax as) (Arm64.evalPure .ARM64FMOVDloadidx8 ty k ax bs) :=
  loadIdx_mono ty 8 8 false hr

theorem armPure_cases {op : Op} (h : armTerm op = true) (ty : Ty) (k : Int64) (ax : Option AuxRef)
    (hr : RefinesList as bs) :
    Refines (Arm64.evalPure op ty k ax as) (Arm64.evalPure op ty k ax bs) := by
  cases op <;> try exact absurd h Bool.false_ne_true
  case ARM64ADD => exact evalPure_ARM64ADD ty k ax hr
  case ARM64MOVDloadidx => exact evalPure_ARM64MOVDloadidx ty k ax hr
  case ARM64MOVWloadidx => exact evalPure_ARM64MOVWloadidx ty k ax hr
  case ARM64MOVWUloadidx => exact evalPure_ARM64MOVWUloadidx ty k ax hr
  case ARM64MOVHloadidx => exact evalPure_ARM64MOVHloadidx ty k ax hr
  case ARM64MOVHUloadidx => exact evalPure_ARM64MOVHUloadidx ty k ax hr
  case ARM64MOVBloadidx => exact evalPure_ARM64MOVBloadidx ty k ax hr
  case ARM64MOVBUloadidx => exact evalPure_ARM64MOVBUloadidx ty k ax hr
  case ARM64FMOVSloadidx => exact evalPure_ARM64FMOVSloadidx ty k ax hr
  case ARM64FMOVDloadidx => exact evalPure_ARM64FMOVDloadidx ty k ax hr
  case ARM64MOVHloadidx2 => exact evalPure_ARM64MOVHloadidx2 ty k ax hr
  case ARM64MOVHUloadidx2 => exact evalPure_ARM64MOVHUloadidx2 ty k ax hr
  case ARM64MOVWloadidx4 => exact evalPure_ARM64MOVWloadidx4 ty k ax hr
  case ARM64MOVWUloadidx4 => exact evalPure_ARM64MOVWUloadidx4 ty k ax hr
  case ARM64MOVDloadidx8 => exact evalPure_ARM64MOVDloadidx8 ty k ax hr
  case ARM64FMOVSloadidx4 => exact evalPure_ARM64FMOVSloadidx4 ty k ax hr
  case ARM64FMOVDloadidx8 => exact evalPure_ARM64FMOVDloadidx8 ty k ax hr
  case ARM64ADDconst => exact evalPure_ARM64ADDconst ty k ax hr
  case ARM64SUB => exact evalPure_ARM64SUB ty k ax hr
  case ARM64SUBconst => exact evalPure_ARM64SUBconst ty k ax hr
  case ARM64MUL => exact evalPure_ARM64MUL ty k ax hr
  case ARM64MULW => exact evalPure_ARM64MULW ty k ax hr
  case ARM64MNEG => exact evalPure_ARM64MNEG ty k ax hr
  case ARM64MNEGW => exact evalPure_ARM64MNEGW ty k ax hr
  case ARM64MULH => exact evalPure_ARM64MULH ty k ax hr
  case ARM64UMULH => exact evalPure_ARM64UMULH ty k ax hr
  case ARM64MULL => exact evalPure_ARM64MULL ty k ax hr
  case ARM64UMULL => exact evalPure_ARM64UMULL ty k ax hr
  case ARM64DIV => exact evalPure_ARM64DIV ty k ax hr
  case ARM64UDIV => exact evalPure_ARM64UDIV ty k ax hr
  case ARM64DIVW => exact evalPure_ARM64DIVW ty k ax hr
  case ARM64UDIVW => exact evalPure_ARM64UDIVW ty k ax hr
  case ARM64MOD => exact evalPure_ARM64MOD ty k ax hr
  case ARM64UMOD => exact evalPure_ARM64UMOD ty k ax hr
  case ARM64MODW => exact evalPure_ARM64MODW ty k ax hr
  case ARM64UMODW => exact evalPure_ARM64UMODW ty k ax hr
  case ARM64MADD => exact evalPure_ARM64MADD ty k ax hr
  case ARM64MADDW => exact evalPure_ARM64MADDW ty k ax hr
  case ARM64MSUB => exact evalPure_ARM64MSUB ty k ax hr
  case ARM64MSUBW => exact evalPure_ARM64MSUBW ty k ax hr
  case ARM64NEG => exact evalPure_ARM64NEG ty k ax hr
  case ARM64MVN => exact evalPure_ARM64MVN ty k ax hr
  case ARM64AND => exact evalPure_ARM64AND ty k ax hr
  case ARM64ANDconst => exact evalPure_ARM64ANDconst ty k ax hr
  case ARM64OR => exact evalPure_ARM64OR ty k ax hr
  case ARM64ORconst => exact evalPure_ARM64ORconst ty k ax hr
  case ARM64XOR => exact evalPure_ARM64XOR ty k ax hr
  case ARM64XORconst => exact evalPure_ARM64XORconst ty k ax hr
  case ARM64BIC => exact evalPure_ARM64BIC ty k ax hr
  case ARM64EON => exact evalPure_ARM64EON ty k ax hr
  case ARM64ORN => exact evalPure_ARM64ORN ty k ax hr
  case ARM64SLL => exact evalPure_ARM64SLL ty k ax hr
  case ARM64SRL => exact evalPure_ARM64SRL ty k ax hr
  case ARM64SRA => exact evalPure_ARM64SRA ty k ax hr
  case ARM64ROR => exact evalPure_ARM64ROR ty k ax hr
  case ARM64RORW => exact evalPure_ARM64RORW ty k ax hr
  case ARM64SLLconst => exact evalPure_ARM64SLLconst ty k ax hr
  case ARM64SRLconst => exact evalPure_ARM64SRLconst ty k ax hr
  case ARM64SRAconst => exact evalPure_ARM64SRAconst ty k ax hr
  case ARM64RORconst => exact evalPure_ARM64RORconst ty k ax hr
  case ARM64RORWconst => exact evalPure_ARM64RORWconst ty k ax hr
  case ARM64EXTRconst => exact evalPure_ARM64EXTRconst ty k ax hr
  case ARM64EXTRWconst => exact evalPure_ARM64EXTRWconst ty k ax hr
  case ARM64MVNshiftLL => exact evalPure_ARM64MVNshiftLL ty k ax hr
  case ARM64MVNshiftRL => exact evalPure_ARM64MVNshiftRL ty k ax hr
  case ARM64MVNshiftRA => exact evalPure_ARM64MVNshiftRA ty k ax hr
  case ARM64MVNshiftRO => exact evalPure_ARM64MVNshiftRO ty k ax hr
  case ARM64NEGshiftLL => exact evalPure_ARM64NEGshiftLL ty k ax hr
  case ARM64NEGshiftRL => exact evalPure_ARM64NEGshiftRL ty k ax hr
  case ARM64NEGshiftRA => exact evalPure_ARM64NEGshiftRA ty k ax hr
  case ARM64ADDshiftLL => exact evalPure_ARM64ADDshiftLL ty k ax hr
  case ARM64ADDshiftRL => exact evalPure_ARM64ADDshiftRL ty k ax hr
  case ARM64ADDshiftRA => exact evalPure_ARM64ADDshiftRA ty k ax hr
  case ARM64SUBshiftLL => exact evalPure_ARM64SUBshiftLL ty k ax hr
  case ARM64SUBshiftRL => exact evalPure_ARM64SUBshiftRL ty k ax hr
  case ARM64SUBshiftRA => exact evalPure_ARM64SUBshiftRA ty k ax hr
  case ARM64ANDshiftLL => exact evalPure_ARM64ANDshiftLL ty k ax hr
  case ARM64ANDshiftRL => exact evalPure_ARM64ANDshiftRL ty k ax hr
  case ARM64ANDshiftRA => exact evalPure_ARM64ANDshiftRA ty k ax hr
  case ARM64ANDshiftRO => exact evalPure_ARM64ANDshiftRO ty k ax hr
  case ARM64ORshiftLL => exact evalPure_ARM64ORshiftLL ty k ax hr
  case ARM64ORshiftRL => exact evalPure_ARM64ORshiftRL ty k ax hr
  case ARM64ORshiftRA => exact evalPure_ARM64ORshiftRA ty k ax hr
  case ARM64ORshiftRO => exact evalPure_ARM64ORshiftRO ty k ax hr
  case ARM64XORshiftLL => exact evalPure_ARM64XORshiftLL ty k ax hr
  case ARM64XORshiftRL => exact evalPure_ARM64XORshiftRL ty k ax hr
  case ARM64XORshiftRA => exact evalPure_ARM64XORshiftRA ty k ax hr
  case ARM64XORshiftRO => exact evalPure_ARM64XORshiftRO ty k ax hr
  case ARM64BICshiftLL => exact evalPure_ARM64BICshiftLL ty k ax hr
  case ARM64BICshiftRL => exact evalPure_ARM64BICshiftRL ty k ax hr
  case ARM64BICshiftRA => exact evalPure_ARM64BICshiftRA ty k ax hr
  case ARM64BICshiftRO => exact evalPure_ARM64BICshiftRO ty k ax hr
  case ARM64EONshiftLL => exact evalPure_ARM64EONshiftLL ty k ax hr
  case ARM64EONshiftRL => exact evalPure_ARM64EONshiftRL ty k ax hr
  case ARM64EONshiftRA => exact evalPure_ARM64EONshiftRA ty k ax hr
  case ARM64EONshiftRO => exact evalPure_ARM64EONshiftRO ty k ax hr
  case ARM64ORNshiftLL => exact evalPure_ARM64ORNshiftLL ty k ax hr
  case ARM64ORNshiftRL => exact evalPure_ARM64ORNshiftRL ty k ax hr
  case ARM64ORNshiftRA => exact evalPure_ARM64ORNshiftRA ty k ax hr
  case ARM64ORNshiftRO => exact evalPure_ARM64ORNshiftRO ty k ax hr
  case ARM64UBFX => exact evalPure_ARM64UBFX ty k ax hr
  case ARM64SBFX => exact evalPure_ARM64SBFX ty k ax hr
  case ARM64UBFIZ => exact evalPure_ARM64UBFIZ ty k ax hr
  case ARM64SBFIZ => exact evalPure_ARM64SBFIZ ty k ax hr
  case ARM64BFI => exact evalPure_ARM64BFI ty k ax hr
  case ARM64BFXIL => exact evalPure_ARM64BFXIL ty k ax hr
  case ARM64CLZ => exact evalPure_ARM64CLZ ty k ax hr
  case ARM64CLZW => exact evalPure_ARM64CLZW ty k ax hr
  case ARM64RBIT => exact evalPure_ARM64RBIT ty k ax hr
  case ARM64RBITW => exact evalPure_ARM64RBITW ty k ax hr
  case ARM64REV => exact evalPure_ARM64REV ty k ax hr
  case ARM64REVW => exact evalPure_ARM64REVW ty k ax hr
  case ARM64REV16 => exact evalPure_ARM64REV16 ty k ax hr
  case ARM64REV16W => exact evalPure_ARM64REV16W ty k ax hr
  case ARM64MOVBreg => exact evalPure_ARM64MOVBreg ty k ax hr
  case ARM64MOVBUreg => exact evalPure_ARM64MOVBUreg ty k ax hr
  case ARM64MOVHreg => exact evalPure_ARM64MOVHreg ty k ax hr
  case ARM64MOVHUreg => exact evalPure_ARM64MOVHUreg ty k ax hr
  case ARM64MOVWreg => exact evalPure_ARM64MOVWreg ty k ax hr
  case ARM64MOVWUreg => exact evalPure_ARM64MOVWUreg ty k ax hr
  case ARM64MOVDconst => exact evalPure_ARM64MOVDconst ty k ax hr
  case ARM64ZERO => exact evalPure_ARM64ZERO ty k ax hr
  case ARM64CMP => exact evalPure_ARM64CMP ty k ax hr
  case ARM64CMPconst => exact evalPure_ARM64CMPconst ty k ax hr
  case ARM64CMPW => exact evalPure_ARM64CMPW ty k ax hr
  case ARM64CMPWconst => exact evalPure_ARM64CMPWconst ty k ax hr
  case ARM64CMN => exact evalPure_ARM64CMN ty k ax hr
  case ARM64CMNconst => exact evalPure_ARM64CMNconst ty k ax hr
  case ARM64CMNW => exact evalPure_ARM64CMNW ty k ax hr
  case ARM64CMNWconst => exact evalPure_ARM64CMNWconst ty k ax hr
  case ARM64TST => exact evalPure_ARM64TST ty k ax hr
  case ARM64TSTconst => exact evalPure_ARM64TSTconst ty k ax hr
  case ARM64TSTW => exact evalPure_ARM64TSTW ty k ax hr
  case ARM64TSTWconst => exact evalPure_ARM64TSTWconst ty k ax hr
  case ARM64CMPshiftLL => exact evalPure_ARM64CMPshiftLL ty k ax hr
  case ARM64CMPshiftRL => exact evalPure_ARM64CMPshiftRL ty k ax hr
  case ARM64CMPshiftRA => exact evalPure_ARM64CMPshiftRA ty k ax hr
  case ARM64CMNshiftLL => exact evalPure_ARM64CMNshiftLL ty k ax hr
  case ARM64CMNshiftRL => exact evalPure_ARM64CMNshiftRL ty k ax hr
  case ARM64CMNshiftRA => exact evalPure_ARM64CMNshiftRA ty k ax hr
  case ARM64TSTshiftLL => exact evalPure_ARM64TSTshiftLL ty k ax hr
  case ARM64TSTshiftRL => exact evalPure_ARM64TSTshiftRL ty k ax hr
  case ARM64TSTshiftRA => exact evalPure_ARM64TSTshiftRA ty k ax hr
  case ARM64TSTshiftRO => exact evalPure_ARM64TSTshiftRO ty k ax hr
  case ARM64FlagConstant => exact evalPure_ARM64FlagConstant ty k ax hr
  case ARM64InvertFlags => exact evalPure_ARM64InvertFlags ty k ax hr
  case ARM64CSEL => exact evalPure_ARM64CSEL ty k ax hr
  case ARM64CSEL0 => exact evalPure_ARM64CSEL0 ty k ax hr
  case ARM64CSINC => exact evalPure_ARM64CSINC ty k ax hr
  case ARM64CSINV => exact evalPure_ARM64CSINV ty k ax hr
  case ARM64CSNEG => exact evalPure_ARM64CSNEG ty k ax hr
  case ARM64CSETM => exact evalPure_ARM64CSETM ty k ax hr
  case ARM64Equal => exact evalPure_ARM64Equal ty k ax hr
  case ARM64NotEqual => exact evalPure_ARM64NotEqual ty k ax hr
  case ARM64LessThan => exact evalPure_ARM64LessThan ty k ax hr
  case ARM64LessEqual => exact evalPure_ARM64LessEqual ty k ax hr
  case ARM64GreaterThan => exact evalPure_ARM64GreaterThan ty k ax hr
  case ARM64GreaterEqual => exact evalPure_ARM64GreaterEqual ty k ax hr
  case ARM64LessThanU => exact evalPure_ARM64LessThanU ty k ax hr
  case ARM64LessEqualU => exact evalPure_ARM64LessEqualU ty k ax hr
  case ARM64GreaterThanU => exact evalPure_ARM64GreaterThanU ty k ax hr
  case ARM64GreaterEqualU => exact evalPure_ARM64GreaterEqualU ty k ax hr
  case ARM64LessThanF => exact evalPure_ARM64LessThanF ty k ax hr
  case ARM64LessEqualF => exact evalPure_ARM64LessEqualF ty k ax hr
  case ARM64GreaterThanF => exact evalPure_ARM64GreaterThanF ty k ax hr
  case ARM64GreaterEqualF => exact evalPure_ARM64GreaterEqualF ty k ax hr
  case ARM64NotLessThanF => exact evalPure_ARM64NotLessThanF ty k ax hr
  case ARM64NotLessEqualF => exact evalPure_ARM64NotLessEqualF ty k ax hr
  case ARM64NotGreaterThanF => exact evalPure_ARM64NotGreaterThanF ty k ax hr
  case ARM64NotGreaterEqualF => exact evalPure_ARM64NotGreaterEqualF ty k ax hr
  case ARM64LessThanNoov => exact evalPure_ARM64LessThanNoov ty k ax hr
  case ARM64GreaterEqualNoov => exact evalPure_ARM64GreaterEqualNoov ty k ax hr
  case ARM64FADDS => exact evalPure_ARM64FADDS ty k ax hr
  case ARM64FADDD => exact evalPure_ARM64FADDD ty k ax hr
  case ARM64FSUBS => exact evalPure_ARM64FSUBS ty k ax hr
  case ARM64FSUBD => exact evalPure_ARM64FSUBD ty k ax hr
  case ARM64FMULS => exact evalPure_ARM64FMULS ty k ax hr
  case ARM64FMULD => exact evalPure_ARM64FMULD ty k ax hr
  case ARM64FNMULS => exact evalPure_ARM64FNMULS ty k ax hr
  case ARM64FNMULD => exact evalPure_ARM64FNMULD ty k ax hr
  case ARM64FDIVS => exact evalPure_ARM64FDIVS ty k ax hr
  case ARM64FDIVD => exact evalPure_ARM64FDIVD ty k ax hr
  case ARM64FABSS => exact evalPure_ARM64FABSS ty k ax hr
  case ARM64FABSD => exact evalPure_ARM64FABSD ty k ax hr
  case ARM64FNEGS => exact evalPure_ARM64FNEGS ty k ax hr
  case ARM64FNEGD => exact evalPure_ARM64FNEGD ty k ax hr
  case ARM64FSQRTS => exact evalPure_ARM64FSQRTS ty k ax hr
  case ARM64FSQRTD => exact evalPure_ARM64FSQRTD ty k ax hr
  case ARM64FMINS => exact evalPure_ARM64FMINS ty k ax hr
  case ARM64FMIND => exact evalPure_ARM64FMIND ty k ax hr
  case ARM64FMAXS => exact evalPure_ARM64FMAXS ty k ax hr
  case ARM64FMAXD => exact evalPure_ARM64FMAXD ty k ax hr
  case ARM64FMADDS => exact evalPure_ARM64FMADDS ty k ax hr
  case ARM64FMADDD => exact evalPure_ARM64FMADDD ty k ax hr
  case ARM64FMSUBS => exact evalPure_ARM64FMSUBS ty k ax hr
  case ARM64FMSUBD => exact evalPure_ARM64FMSUBD ty k ax hr
  case ARM64FNMADDS => exact evalPure_ARM64FNMADDS ty k ax hr
  case ARM64FNMADDD => exact evalPure_ARM64FNMADDD ty k ax hr
  case ARM64FNMSUBS => exact evalPure_ARM64FNMSUBS ty k ax hr
  case ARM64FNMSUBD => exact evalPure_ARM64FNMSUBD ty k ax hr
  case ARM64FRINTAD => exact evalPure_ARM64FRINTAD ty k ax hr
  case ARM64FRINTMD => exact evalPure_ARM64FRINTMD ty k ax hr
  case ARM64FRINTND => exact evalPure_ARM64FRINTND ty k ax hr
  case ARM64FRINTPD => exact evalPure_ARM64FRINTPD ty k ax hr
  case ARM64FRINTZD => exact evalPure_ARM64FRINTZD ty k ax hr
  case ARM64LoweredRound32F => exact evalPure_ARM64LoweredRound32F ty k ax hr
  case ARM64LoweredRound64F => exact evalPure_ARM64LoweredRound64F ty k ax hr
  case ARM64FCMPS => exact evalPure_ARM64FCMPS ty k ax hr
  case ARM64FCMPD => exact evalPure_ARM64FCMPD ty k ax hr
  case ARM64FCMPS0 => exact evalPure_ARM64FCMPS0 ty k ax hr
  case ARM64FCMPD0 => exact evalPure_ARM64FCMPD0 ty k ax hr
  case ARM64FCVTSD => exact evalPure_ARM64FCVTSD ty k ax hr
  case ARM64FCVTDS => exact evalPure_ARM64FCVTDS ty k ax hr
  case ARM64SCVTFWS => exact evalPure_ARM64SCVTFWS ty k ax hr
  case ARM64SCVTFWD => exact evalPure_ARM64SCVTFWD ty k ax hr
  case ARM64UCVTFWS => exact evalPure_ARM64UCVTFWS ty k ax hr
  case ARM64UCVTFWD => exact evalPure_ARM64UCVTFWD ty k ax hr
  case ARM64SCVTFS => exact evalPure_ARM64SCVTFS ty k ax hr
  case ARM64SCVTFD => exact evalPure_ARM64SCVTFD ty k ax hr
  case ARM64UCVTFS => exact evalPure_ARM64UCVTFS ty k ax hr
  case ARM64UCVTFD => exact evalPure_ARM64UCVTFD ty k ax hr
  case ARM64FCVTZSSW => exact evalPure_ARM64FCVTZSSW ty k ax hr
  case ARM64FCVTZSDW => exact evalPure_ARM64FCVTZSDW ty k ax hr
  case ARM64FCVTZUSW => exact evalPure_ARM64FCVTZUSW ty k ax hr
  case ARM64FCVTZUDW => exact evalPure_ARM64FCVTZUDW ty k ax hr
  case ARM64FCVTZSS => exact evalPure_ARM64FCVTZSS ty k ax hr
  case ARM64FCVTZSD => exact evalPure_ARM64FCVTZSD ty k ax hr
  case ARM64FCVTZUS => exact evalPure_ARM64FCVTZUS ty k ax hr
  case ARM64FCVTZUD => exact evalPure_ARM64FCVTZUD ty k ax hr
  case ARM64FMOVSconst => exact evalPure_ARM64FMOVSconst ty k ax hr
  case ARM64FMOVDconst => exact evalPure_ARM64FMOVDconst ty k ax hr
  case ARM64FMOVDgpfp => exact evalPure_ARM64FMOVDgpfp ty k ax hr
  case ARM64FMOVDfpgp => exact evalPure_ARM64FMOVDfpgp ty k ax hr
  case ARM64FMOVSgpfp => exact evalPure_ARM64FMOVSgpfp ty k ax hr
  case ARM64FMOVSfpgp => exact evalPure_ARM64FMOVSfpgp ty k ax hr
  case ARM64LoweredWB => exact evalPure_ARM64LoweredWB ty k ax hr

end GoFV.Proof.Low.Mono
