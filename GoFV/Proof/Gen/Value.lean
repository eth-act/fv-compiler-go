import GoFV.Proof.Gen.Rel

/-!
# The values of slice G1's ops against the machine's words (`docs/plans/proofs3.md` §3)

Under `AddrAgree` (`Rel.lean`), each pure op G1 accepts (`Arm64.add`, `Arm64.sub`, `Arm64.addK`,
`Arm64.res` of a constant, `Arm64.cmp`, `Arm64.isZero`) computes, from arguments related to
machine words `X`, `Y` (`ValRel`) and of their register's width class (`Fits`), a value related
to the word the Prog computes (`X + Y`, …).

`Lo ι c z Z`: a 64-bit register result `z` agrees with the machine word `Z` on the low `c` bits
(a pointer: is `Z` under `ι` when `c = 64`). Arithmetic on arguments of classes at least `c`
gives `Lo` at class `c` (only the low bits of a narrow argument's register are known), and `Lo`
at the class of a non-boolean shape gives `ValRel` of the result read at that shape
(`valRel_retypeL_lo`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

variable {ι : Blk → Option (BitVec 64)}

/-- A 64-bit register result and the machine word on the low `c` bits. -/
def Lo (ι : Blk → Option (BitVec 64)) (c : Nat) : Val → BitVec 64 → Prop
  | .int .w64 z, Z => z.setWidth c = Z.setWidth c
  | .ptr p, Z => c < 64 ∨ PtrRel ι p Z
  | .poison, _ => True
  | _, _ => False

/-- `Lo` at 64 bits gives `Lo` at any class. -/
theorem Lo.mono {c : Nat} {z : Val} {Z : BitVec 64} (h : Lo ι 64 z Z) (hc : c ≤ 64) : Lo ι c z Z := by
  sorry

/-- A result agreeing on the low bits of the class of a non-boolean register shape is related
to the machine word when read at that shape. -/
theorem valRel_retypeL_lo (hA : AddrAgree ι) {t : Ty} {c : Nat} {z : Val} {Z : BitVec 64}
    (hc : cls t = some c) (ht : t ≠ .bool) (h : Lo ι c z Z) : ValRel ι (z.retypeL t) Z := by
  sorry

/-- The register of an argument of class `c` agrees with the machine word on the low `c` bits. -/
theorem reg_low (hA : AddrAgree ι) {c : Nat} {x : Val} {X x' : BitVec 64} (hx : ValRel ι x X)
    (hf : Fits c x) (hr : Arm64.reg x = some x') : x'.setWidth c = X.setWidth c := by
  sorry

/-- `ADD`: arguments of classes `ca`, `cb` at least the result's class `c ≥ 8`. -/
theorem lo_add (hA : AddrAgree ι) {t : Ty} {x y : Val} {X Y : BitVec 64} {c ca cb : Nat}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb) (ht : t ≠ .bool) :
    Lo ι c (Arm64.add t [x, y]) (X + Y) := by
  sorry

/-- `SUB`. -/
theorem lo_sub (hA : AddrAgree ι) {t : Ty} {x y : Val} {X Y : BitVec 64} {c ca cb : Nat}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb) (ht : t ≠ .bool) :
    Lo ι c (Arm64.sub t [x, y]) (X - Y) := by
  sorry

/-- `ADDconst`/`SUBconst` (`addK` with the constant or its negation). -/
theorem lo_addK (hA : AddrAgree ι) {t : Ty} {x : Val} {X k : BitVec 64} {c ca : Nat}
    (hx : ValRel ι x X) (hfx : Fits ca x) (h8 : 8 ≤ c) (hca : c ≤ ca) (ht : t ≠ .bool) :
    Lo ι c (Arm64.addK t k [x]) (X + k) := by
  sorry

/-- A constant of a register shape (a boolean constant is 0 or 1). -/
theorem valRel_res_const {t : Ty} {c : Nat} {K : BitVec 64} (hc : cls t = some c)
    (hb : c = 1 → K = 0 ∨ K = 1) : ValRel ι ((Arm64.res t K).retypeL t) K := by
  sorry

/-- `ZERO` read at a register shape is related to `XZR`. -/
theorem valRel_zero {t : Ty} {c : Nat} (hc : cls t = some c) :
    ValRel ι ((Arm64.res t 0).retypeL t) 0 := by
  sorry

/-- `CMP` of two 64-bit register contents neither of which is a pointer without a register:
the machine's `SUBS` flags, at the flags shape. -/
theorem flagsRel_cmp (hA : AddrAgree ι) {x y : Val} {X Y : BitVec 64}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits 64 x) (hfy : Fits 64 y)
    (hpx : ∀ p, x = .ptr p → (Arm64.ptrReg p).isSome) (hpy : ∀ p, y = .ptr p → (Arm64.ptrReg p).isSome) :
    FlagsRel ((Arm64.cmp x y).retypeL Ty.flags) (Arm64.subFlags X Y).2 := by
  sorry

/-- Flags related to `NZCV` read back at the flags shape are unchanged. -/
theorem flags_retypeL {f : Val} {nz : Flags} (h : FlagsRel f nz) : f.retypeL Ty.flags = f := by
  sorry

/-- `CBZ`'s test: a 64-bit or boolean register content that is not a pointer without a register
is zero exactly when its machine word is. -/
theorem isZero_eq (hA : AddrAgree ι) {x : Val} {X : BitVec 64} {z : Bool} (hx : ValRel ι x X)
    (hf : Fits 64 x ∨ Fits 1 x) (hp : ∀ p, x = .ptr p → (Arm64.ptrReg p).isSome)
    (h : Arm64.isZero x = some z) : z = (X == 0) := by
  sorry

end GoFV.Proof.Gen
