import GoFV.Proof.Low.Rules.Kit

/-!
# Flags of `CMP`/`CMPW` and the comparison rules (issue #385)

`SUBS x y` (`Arm64.subFlags`, `AddWithCarry(x, ¬y, 1)`) sets `Z` iff `x = y`, `C` iff `x ≥ y`
unsigned, and `N ≠ V` iff `x < y` signed (`sub_z`, `sub_lo`, `sub_lt64`, `sub_lt32`); the
conditions `Equal` … `LessEqualU` read them as Phase 1's comparisons (`cond_sub`). A generic
comparison of two `w`-bit integers is the `CSET` of the condition on their `CMP`/`CMPW` flags
(`refines_cmp`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low

/-! ## `SUBS` flags -/

theorem sub_res (n : Nat) (x y : BitVec n) :
    BitVec.ofNat n (x.toNat + (~~~y).toNat + 1) = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_not]
  have := y.isLt
  congr 1; omega

theorem sub_z (n : Nat) (x y : BitVec n) : (Arm64.subFlags x y).2.z = (x == y) := by
  simp only [Arm64.subFlags, addWithCarry, ite_true, sub_res]
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0#n := by
      intro h'; apply h
      exact (BitVec.sub_eq_iff_eq_add.mp h').trans (by simp)
    show (x - y == 0#n) = (x == y)
    rw [beq_false_of_ne this, beq_false_of_ne h]

theorem sub_lo (n : Nat) (x y : BitVec n) : (!(Arm64.subFlags x y).2.c) = x.ult y := by
  simp only [Arm64.subFlags, addWithCarry, ite_true, BitVec.toNat_ofNat, BitVec.toNat_not,
    BitVec.ult]
  have := y.isLt
  have := x.isLt
  by_cases h : x.toNat < y.toNat
  · have : (x.toNat + (2 ^ n - 1 - y.toNat) + 1) % 2 ^ n = x.toNat + (2 ^ n - 1 - y.toNat) + 1 :=
      Nat.mod_eq_of_lt (by omega)
    simp [this, h]
  · have : (x.toNat + (2 ^ n - 1 - y.toNat) + 1) % 2 ^ n ≠
        x.toNat + (2 ^ n - 1 - y.toNat) + 1 := by
      intro h'
      have := Nat.mod_lt (x.toNat + (2 ^ n - 1 - y.toNat) + 1) (Nat.two_pow_pos n)
      omega
    simp [this, h]

private theorem toInt_not64 (y : BitVec 64) : (~~~y).toInt = -y.toInt - 1 := by
  rw [BitVec.toInt_not, BitVec.toInt_eq_toNat_cond]
  have := y.isLt
  rw [Int.bmod_def]
  simp only [Nat.reducePow]
  split <;> split <;> omega

private theorem toInt_not32 (y : BitVec 32) : (~~~y).toInt = -y.toInt - 1 := by
  rw [BitVec.toInt_not, BitVec.toInt_eq_toNat_cond]
  have := y.isLt
  rw [Int.bmod_def]
  simp only [Nat.reducePow]
  split <;> split <;> omega

theorem sub_lt64 (x y : BitVec 64) :
    ((Arm64.subFlags x y).2.n != (Arm64.subFlags x y).2.v) = x.slt y := by
  simp only [Arm64.subFlags, addWithCarry, ite_true, sub_res, BitVec.slt, BitVec.msb_eq_toInt,
    toInt_not64, BitVec.toInt_sub]
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  have h3 := BitVec.le_toInt y
  have h4 := BitVec.toInt_lt (x := y)
  simp only [Nat.reducePow, Nat.reduceSub] at h1 h2 h3 h4 ⊢
  rw [Int.bmod_def]
  rw [Bool.eq_iff_iff]
  split <;> simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] <;> rw [Bool.eq_iff_iff] <;>
    simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] <;> omega

theorem sub_lt32 (x y : BitVec 32) :
    ((Arm64.subFlags x y).2.n != (Arm64.subFlags x y).2.v) = x.slt y := by
  simp only [Arm64.subFlags, addWithCarry, ite_true, sub_res, BitVec.slt, BitVec.msb_eq_toInt,
    toInt_not32, BitVec.toInt_sub]
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  have h3 := BitVec.le_toInt y
  have h4 := BitVec.toInt_lt (x := y)
  simp only [Nat.reducePow, Nat.reduceSub] at h1 h2 h3 h4 ⊢
  rw [Int.bmod_def]
  rw [Bool.eq_iff_iff]
  split <;> simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] <;> rw [Bool.eq_iff_iff] <;>
    simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] <;> omega

/-! ## Conditions on `SUBS` flags -/

/-- The conditions of `Equal` … `LessEqualU` on the flags of `SUBS x y`, as Phase 1's
comparisons, given the signed `N ≠ V` (`hlt`). -/
theorem cond_sub {n : Nat} (x y : BitVec n)
    (hlt : ((Arm64.subFlags x y).2.n != (Arm64.subFlags x y).2.v) = x.slt y) :
    Cond.eq.onVal (Arm64.subFlags x y).2.toVal = some (x == y) ∧
    Cond.ne.onVal (Arm64.subFlags x y).2.toVal = some (x != y) ∧
    Cond.lt.onVal (Arm64.subFlags x y).2.toVal = some (x.slt y) ∧
    Cond.le.onVal (Arm64.subFlags x y).2.toVal = some (x.sle y) ∧
    Cond.lo.onVal (Arm64.subFlags x y).2.toVal = some (x.ult y) ∧
    Cond.ls.onVal (Arm64.subFlags x y).2.toVal = some (x.ule y) := by
  have hz := sub_z n x y
  have hc := sub_lo n x y
  simp only [Cond.onVal, Flags.toVal, Val.flagBit, Cond.eval, Option.map_some, bind,
    Option.bind_some, pure]
  refine ⟨hz ▸ rfl, by rw [hz]; rfl, by rw [← hlt], ?_, by rw [← hc], ?_⟩
  · have hle : x.sle y = (x.slt y || x == y) := by
      rw [Bool.eq_iff_iff]
      simp only [BitVec.sle, BitVec.slt, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
        ← BitVec.toInt_inj]
      omega
    rw [hle, ← hlt, ← hz]
    cases (Arm64.subFlags x y).2.n <;> cases (Arm64.subFlags x y).2.v <;>
      cases (Arm64.subFlags x y).2.z <;> rfl
  · have hle : x.ule y = (x.ult y || x == y) := by
      rw [Bool.eq_iff_iff]
      simp only [BitVec.ule, BitVec.ult, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
        ← BitVec.toNat_inj]
      omega
    rw [hle, ← hc, ← hz]
    cases (Arm64.subFlags x y).2.c <;> cases (Arm64.subFlags x y).2.z <;> rfl

/-! ## `InvertFlags` -/

/-- The integer conditions and the ones `arm64Invert` swaps them with (`EQ NE` stay). -/
def _root_.GoFV.SSA.Sem.Cond.swapInt : Cond → Option Cond
  | .eq => some .eq
  | .ne => some .ne
  | .lt => some .gt
  | .gt => some .lt
  | .le => some .ge
  | .ge => some .le
  | .lo => some .hi
  | .hi => some .lo
  | .ls => some .hs
  | .hs => some .ls
  | _ => none

@[simp] theorem flagBit_ofFlagBit (o : Option Bool) : (Val.ofFlagBit o).flagBit = o := by
  cases o <;> rfl

/-- **An integer condition on `InvertFlags f` is its swapped condition on `f`**, whatever `f`
(the bits `invertFlags` cannot compute as a subtraction's are `poison`, so the condition is
undefined there). -/
theorem invertFlags_cond {c c' : Cond} (hs : c.swapInt = some c') {f : Val} {b : Bool}
    (h : c.onVal (invertFlags f) = some b) : c'.onVal f = some b := by
  unfold invertFlags at h
  split at h
  · rename_i n z cf v g
    simp only [Cond.onVal, flagBit_ofFlagBit] at h ⊢
    generalize n.flagBit = N at h ⊢; generalize z.flagBit = Z at h ⊢
    generalize cf.flagBit = C at h ⊢; generalize v.flagBit = V at h ⊢
    generalize g.flagBit = G at h ⊢
    cases c <;> simp only [Cond.swapInt, Option.some.injEq, reduceCtorEq] at hs <;> subst hs
    all_goals first
      | (rcases Z with _ | _ | _ <;> simp_all [Cond.eval]; done)
      | (rcases Z with _ | _ | _ <;> rcases C with _ | _ | _ <;> simp_all [Cond.eval]; done)
      | (rcases Z with _ | _ | _ <;> rcases G with _ | _ | _ <;> rcases N with _ | _ | _ <;>
          rcases V with _ | _ | _ <;> simp_all [Cond.eval])
  · simp [Cond.onVal] at h

/-- The result of `SUBS x y` is `x - y`. -/
theorem sub_fst {n : Nat} (x y : BitVec n) : (Arm64.subFlags x y).1 = x - y := by
  simp only [Arm64.subFlags, addWithCarry, ite_true, sub_res]

/-- `N` of `SUBS x y` is the sign of `x - y`. -/
theorem sub_n {n : Nat} (x y : BitVec n) : (Arm64.subFlags x y).2.n = (x - y).msb := by
  simp only [Arm64.subFlags, addWithCarry, ite_true, sub_res]

/-- **`InvertFlags` of the compare `y, x` is the compare `x, y`**, given the signed order of
both (`sub_lt64`, `sub_lt32`). -/
theorem invertFlags_sub {n : Nat} (x y : BitVec n)
    (hxy : ((Arm64.subFlags x y).2.n != (Arm64.subFlags x y).2.v) = x.slt y)
    (hyx : ((Arm64.subFlags y x).2.n != (Arm64.subFlags y x).2.v) = y.slt x) :
    invertFlags (Arm64.cmpRes (Arm64.subFlags y x)) = Arm64.cmpRes (Arm64.subFlags x y) := by
  have hg1 : (-(Arm64.subFlags y x).1).msb = (Arm64.subFlags x y).2.n := by
    rw [sub_fst, sub_n, BitVec.neg_sub, BitVec.add_comm, ← BitVec.sub_eq_add_neg]
  have hg2 : (-(Arm64.subFlags x y).1).msb = (Arm64.subFlags y x).2.n := by
    rw [sub_fst, sub_n, BitVec.neg_sub, BitVec.add_comm, ← BitVec.sub_eq_add_neg]
  have hzx := sub_z n x y; have hzy := sub_z n y x
  have hcx := sub_lo n x y; have hcy := sub_lo n y x
  have tri_u : (x.ult y && y.ult x) = false ∧ ((x == y) → (!x.ult y && !y.ult x) = true) ∧
      ((x == y) = false → (x.ult y || y.ult x) = true) := by
    simp only [BitVec.ult, beq_iff_eq, ← BitVec.toNat_inj]
    by_cases h1 : x.toNat < y.toNat <;> by_cases h2 : y.toNat < x.toNat <;> simp [h1, h2]
    all_goals first | omega | (apply BitVec.eq_of_toNat_eq; omega)
  have tri_s : (x.slt y && y.slt x) = false ∧ ((x == y) → (!x.slt y && !y.slt x) = true) ∧
      ((x == y) = false → (x.slt y || y.slt x) = true) := by
    simp only [BitVec.slt, beq_iff_eq, ← BitVec.toInt_inj]
    by_cases h1 : x.toInt < y.toInt <;> by_cases h2 : y.toInt < x.toInt <;> simp [h1, h2]
    all_goals first | omega | exact BitVec.toInt_inj.mp (by omega)
  have hyxe : (y == x) = (x == y) := Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)
  simp only [Arm64.cmpRes, Flags.toValSub, invertFlags, Val.flagBit]
  rw [hg1, hg2]
  generalize (Arm64.subFlags x y).2 = G at *
  generalize (Arm64.subFlags y x).2 = F at *
  obtain ⟨Gn, Gz, Gc, Gv⟩ := G
  obtain ⟨Fn, Fz, Fc, Fv⟩ := F
  simp only at *
  subst hzx hzy
  rw [hyxe]
  refine congrArg Val.agg ?_
  simp only [List.cons.injEq, and_true]
  refine ⟨rfl, rfl, ?_, ?_, rfl⟩
  · generalize x.ult y = A at *; generalize y.ult x = B at *; generalize (x == y) = E at *
    cases E <;> cases A <;> cases B <;> cases Gc <;> cases Fc <;> simp_all [Val.ofFlagBit]
  · generalize x.slt y = S at *; generalize y.slt x = T at *; generalize (x == y) = E at *
    cases E <;> cases S <;> cases T <;> cases Gn <;> cases Gv <;> cases Fn <;> cases Fv <;>
      simp_all [Val.ofFlagBit]

end GoFV.Proof.Low.Rules
