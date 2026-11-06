import GoFV.Opt.LateLowerCheck
import GoFV.Proof.FrameL

/-!
# `late lower`'s rewrites, value by value (issue #385)

The facts `GoFV.Proof.LateLowerL.lateLower_refinesL` needs of the values `lateB`
(`GoFV.Opt.LateLowerCheck`) relates: the bits of `Arm64.ext` (`getLsbD_ext`); what a producer
(`prodSig`: a narrow load, indexed or not, or an extension) leaves in its register under `runL`
(`prod_evalOpL`: `poison` or a result whose low `k` bits are extended, `RawExt`; at its lowered
shape, `ExtAt`); that dropping an extension of such a register changes nothing (`drop_eq`, by
`movd_fix` and `ext_drop`); that an immediate op is its register op on the materialized constant
(`imm_eval`), `SLLconst [1] x` is `ADD x x` (`sll1_eval`) and `ZERO` is `MOVDconst [0]`
(`zero_eval`).
-/

namespace GoFV.Proof.LateLowerL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.LateLowerCheck

/-! ## Extensions, bit by bit -/

theorem getLsbD_ext {s : Bool} {k : Nat} (hk0 : 0 < k) (hk : k ≤ 64) (x : BitVec 64) {i : Nat}
    (hi : i < 64) :
    (Arm64.ext s k x).getLsbD i = if i < k then x.getLsbD i else (s && x.getLsbD (k - 1)) := by
  unfold Arm64.ext
  cases s
  · simp only [Bool.false_eq_true, ite_false, Arm64.mask, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and, Bool.false_and]
    by_cases h : i < k <;> simp [h]
  · simp only [ite_true, Arm64.sext, Arm64.mask, if_neg (show ¬ (k = 0) by omega)]
    rw [BitVec.getLsbD_sshiftRight]
    by_cases h : i < k
    · have h1 : 64 - k + i < 64 := by omega
      simp only [h1, ite_true, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
        Nat.testBit_two_pow_sub_one, show 64 - k + i - (64 - k) = i by omega, h, hi,
        show ¬ (64 ≤ i) by omega, show ¬ (64 - k + i < 64 - k) by omega, decide_true, decide_false,
        Bool.true_and, Bool.and_true, Bool.not_false, ite_true]
    · have h1 : ¬ (64 - k + i < 64) := by omega
      simp only [h1, ite_false, h, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
        show 64 - 1 - (64 - k) = k - 1 by omega, show k - 1 < k by omega,
        show ¬ (64 - 1 < 64 - k) by omega, show 64 - 1 < 64 by omega,
        show ¬ (64 ≤ i) by omega, show k - 1 < 64 by omega, decide_true, decide_false,
        Bool.true_and, Bool.and_true, Bool.not_false]

/-- What `ext s k r = r` says of the bits of `r`. -/
theorem ext_fix_bits {s : Bool} {k : Nat} (hk0 : 0 < k) (hk : k ≤ 64) {r : BitVec 64}
    (h : Arm64.ext s k r = r) {i : Nat} (hi : i < 64) (hik : k ≤ i) :
    r.getLsbD i = (s && r.getLsbD (k - 1)) := by
  have := getLsbD_ext (s := s) hk0 hk r hi
  rw [h, if_neg (by omega)] at this
  exact this

theorem ext_idem {s : Bool} {k : Nat} (hk0 : 0 < k) (hk : k ≤ 64) (x : BitVec 64) :
    Arm64.ext s k (Arm64.ext s k x) = Arm64.ext s k x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ext hk0 hk _ hi, getLsbD_ext hk0 hk _ hi, getLsbD_ext hk0 hk _ (by omega)]
  by_cases h : i < k
  · simp [h]
  · simp [h, show k - 1 < k by omega]

/-- A `MOVDreg` of a producer's register at a `wb`-bit shape: the register. -/
theorem movd_fix {sP : Bool} {kP wb : Nat} (hk0 : 0 < kP) (hkw : kP ≤ wb) (hw : wb ≤ 64)
    {r : BitVec 64} (h : Arm64.ext sP kP r = r) :
    (if sP then (r.setWidth wb).signExtend 64 else (r.setWidth wb).setWidth 64) = r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases sP
  · simp only [Bool.false_eq_true, ite_false, BitVec.getLsbD_setWidth, hi, decide_true,
      Bool.true_and]
    by_cases hiw : i < wb
    · simp [hiw]
    · simp only [hiw, decide_false, Bool.false_and]
      rw [ext_fix_bits hk0 (by omega) h hi (by omega)]; rfl
  · simp only [ite_true, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth, hi, decide_true,
      Bool.true_and, BitVec.msb_eq_getLsbD_last]
    by_cases hiw : i < wb
    · simp [hiw]
    · simp only [hiw, decide_false, ite_false, show wb - 1 < wb by omega]
      rw [ext_fix_bits hk0 (by omega) h hi (by omega)]
      by_cases hkk : kP ≤ wb - 1
      · rw [ext_fix_bits hk0 (by omega) h (by omega) hkk]; simp
      · simp [show wb - 1 = kP - 1 by omega]

/-- The extension `(sE, kE)` of a producer's register read at a `wb`-bit shape: the register. -/
theorem ext_drop {sP sE : Bool} {kP kE wb : Nat} (hk0 : 0 < kP) (hkE : 0 < kE) (hkE' : kE ≤ 64)
    (hkw : kP ≤ wb) (hw : wb ≤ 64) (hsw : sP = true → kE ≤ wb)
    (hc : (if sP then sE && decide (kP ≤ kE) else if sE then decide (kP < kE) else decide (kP ≤ kE)) = true)
    {r : BitVec 64} (h : Arm64.ext sP kP r = r) :
    Arm64.ext sE kE ((r.setWidth wb).setWidth 64) = r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ext hkE hkE' _ hi]
  simp only [BitVec.getLsbD_setWidth, hi, show kE - 1 < 64 by omega, decide_true, Bool.true_and]
  cases sP <;> cases sE <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.and_true,
    Bool.true_and, decide_eq_true_eq] at hc
  · -- unsigned producer, unsigned extension
    by_cases hik : i < kE
    · by_cases hiw : i < wb
      · simp [hik, hiw]
      · simp only [hik, hiw, decide_false, Bool.false_and, ite_true]
        rw [ext_fix_bits hk0 (by omega) h hi (by omega)]; rfl
    · simp only [hik, ite_false, Bool.false_and]
      rw [ext_fix_bits hk0 (by omega) h hi (by omega)]; rfl
  · -- unsigned producer, signed extension of more bits
    by_cases hik : i < kE
    · by_cases hiw : i < wb
      · simp [hik, hiw]
      · simp only [hik, hiw, decide_false, Bool.false_and, ite_true]
        rw [ext_fix_bits hk0 (by omega) h hi (by omega)]; rfl
    · simp only [hik, ite_false, Bool.true_and]
      rw [ext_fix_bits hk0 (by omega) h hi (by omega),
        ext_fix_bits hk0 (by omega) h (by omega) (show kP ≤ kE - 1 by omega)]
      simp
  · simp at hc
  · -- signed producer, signed extension
    have hkw' := hsw rfl
    by_cases hik : i < kE
    · simp [hik, show i < wb by omega]
    · simp only [hik, ite_false, show kE - 1 < wb by omega, decide_true, Bool.true_and]
      rw [ext_fix_bits hk0 (by omega) h hi (by omega)]
      by_cases hkk : kP ≤ kE - 1
      · rw [ext_fix_bits hk0 (by omega) h (by omega) hkk]; try simp
      · simp [show kE - 1 = kP - 1 by omega]

/-- An extension of at least two bits of a boolean's register (0 or 1) changes nothing. -/
theorem ext_bool {sE : Bool} {kE : Nat} (hkE : 2 ≤ kE) (hkE' : kE ≤ 64) (b : Bool) :
    Arm64.ext sE kE (if b then 1 else 0) = (if b then 1 else 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ext (by omega) hkE' _ hi]
  by_cases hik : i < kE
  · simp [hik]
  · simp only [hik, ite_false]
    have h1 : ¬ (i = 0) := by omega
    have h2 : ¬ (kE - 1 = 0) := by omega
    cases b <;> cases sE <;> simp [h1, h2]

-- stand-ins for the bit lemmas (already checked in Bits.lean)
def RawExt (s : Bool) (k : Nat) (ty : Ty) (z : Val) : Prop :=
  z = .poison ∨ ∃ r, z = Arm64.res ty r ∧ Arm64.ext s k r = r

theorem rawExt_poison {s : Bool} {k : Nat} {ty : Ty} : RawExt s k ty .poison := .inl rfl

/-- A `k`-bit value zero-extended is its unsigned extension. -/
theorem ext_zext {k : Nat} (hk0 : 0 < k) (hk : k ≤ 64) (x : BitVec k) :
    Arm64.ext false k (x.setWidth 64) = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ext hk0 hk _ hi]
  by_cases h : i < k
  · simp [h]
  · simp [h, BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge x i (by omega)]

theorem ext_sext {k : Nat} (hk0 : 0 < k) (hk : k ≤ 64) (x : BitVec 64) :
    Arm64.ext true k (Arm64.sext k x) = Arm64.sext k x := by
  have := ext_idem (s := true) hk0 hk x
  simpa [Arm64.ext] using this

theorem load_int_cases (m : Mem) (p : Ptr) {w : Width} (hw : w ≠ .w64) :
    m.load (.int w) p = .poison ∨ ∃ x, m.load (.int w) p = .int w x := by
  simp only [Mem.load]
  cases m.read p (Ty.int w).size with
  | none => exact .inl rfl
  | some bs =>
    simp only [decodeLoad, decode, decodeInt]
    cases bytesNat? (bs.extract 0 (0 + w.bytes)) with
    | some k => exact .inr ⟨_, rfl⟩
    | none => cases w <;> first | exact absurd rfl hw | exact .inl rfl

theorem loadN_raw {ty : Ty} {n : Nat} {s : Bool} {m : Mem} {p : Ptr} (hn : n = 1 ∨ n = 2 ∨ n = 4) :
    RawExt s (8 * n) ty (Arm64.loadN ty n s m p) := by
  have key : ∀ (w : Width), w ≠ .w64 → 8 * n = w.bits →
      Width.ofSize? (n : Int) = some w →
      RawExt s (8 * n) ty (match m.load (.int w) p with
        | .int _ x =>
          let x : BitVec 64 := x.setWidth 64
          Arm64.res ty (if s then Arm64.sext (8 * n) x else x)
        | _ => .poison) := by
    intro w hw hb _
    rcases load_int_cases m p hw with h | ⟨x, h⟩
    · rw [h]; exact rawExt_poison
    · rw [h]
      refine .inr ⟨_, rfl, ?_⟩
      cases s
      · simp only [Bool.false_eq_true, ite_false]
        rw [hb]
        exact ext_zext (by cases w <;> simp_all [Width.bits]) (by cases w <;> simp [Width.bits]) x
      · simp only [ite_true]
        exact ext_sext (by omega) (by rw [hb]; cases w <;> simp [Width.bits]) _
  rcases hn with rfl | rfl | rfl
  · exact key .w8 (by decide) rfl rfl
  · exact key .w16 (by decide) rfl rfl
  · exact key .w32 (by decide) rfl rfl

theorem loadIdx_raw {ty : Ty} {n scale : Nat} {s : Bool} {args : List Val}
    (hn : n = 1 ∨ n = 2 ∨ n = 4) : RawExt s (8 * n) ty (Arm64.loadIdx ty n scale s args) := by
  unfold Arm64.loadIdx
  split
  · dsimp only
    split
    · exact loadN_raw hn
    · exact rawExt_poison
  · exact rawExt_poison

theorem op1ext_raw {ty : Ty} {s : Bool} {k : Nat} (hk0 : 0 < k) (hk : k ≤ 64) (args : List Val) :
    RawExt s k ty (Arm64.op1 ty (Arm64.ext s k) args) := by
  unfold Arm64.op1
  split
  · split
    · exact .inr ⟨_, rfl, ext_idem hk0 hk _⟩
    · exact rawExt_poison
  · exact rawExt_poison

/-! ## Tables -/

theorem find_mem {α : Type} {l : List (Op × α)} {o : Op} {a : α}
    (h : (l.find? (·.1 == o)).map (·.2) = some a) : (o, a) ∈ l := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some he
  have hp : e.1 = o := by simpa using List.find?_some he
  rw [← hp]
  exact hm

/-! ## Dispatch -/

theorem evalOpL_act {f : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hg : v.op.generic = false) (ha : GoFV.Opt.LowerTerm.actOp v.op = true) :
    evalOpL f env ctx fr v argv ty = arm64Op f env ctx fr v argv ty := by
  rw [evalOpL_eq]; simp [hg, ha]

theorem evalOpL_pure {f : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hg : v.op.generic = false) (ha : GoFV.Opt.LowerTerm.actOp v.op = false)
    (hr : isRoot v.op = false) :
    evalOpL f env ctx fr v argv ty = pure (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  rw [evalOpL_eq]; simp [hg, ha, hr]

/-- The narrow loads `arm64Op` reads (`ld`). -/
theorem arm64Op_ld {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} {argv : List Val} {ty : Ty}
    {n : Nat} {s : Bool}
    (hop : (u.op = .ARM64MOVBload ∧ n = 1 ∧ s = true) ∨ (u.op = .ARM64MOVBUload ∧ n = 1 ∧ s = false) ∨
      (u.op = .ARM64MOVHload ∧ n = 2 ∧ s = true) ∨ (u.op = .ARM64MOVHUload ∧ n = 2 ∧ s = false) ∨
      (u.op = .ARM64MOVWload ∧ n = 4 ∧ s = true) ∨ (u.op = .ARM64MOVWUload ∧ n = 4 ∧ s = false)) :
    arm64Op false env ctx fr u argv ty = (match argv with
      | [a, .mem m] => .ok ((symAddr ctx u a).elim .poison (Arm64.loadN ty n s m))
      | _ => .ok .poison) := by
  unfold arm64Op
  rcases hop with ⟨h, rfl, rfl⟩ | ⟨h, rfl, rfl⟩ | ⟨h, rfl, rfl⟩ | ⟨h, rfl, rfl⟩ | ⟨h, rfl, rfl⟩ |
    ⟨h, rfl, rfl⟩ <;>
  · simp only [show nilFaults false ctx u argv = none from rfl, h]
    rfl

theorem ld_raw {ctx : Ctx} {u : Value} {argv : List Val} {ty : Ty} {n : Nat} {s : Bool} {z : Val}
    (hn : n = 1 ∨ n = 2 ∨ n = 4)
    (h : (match argv with
      | [a, .mem m] => Res.ok ((symAddr ctx u a).elim Val.poison (Arm64.loadN ty n s m))
      | _ => Res.ok Val.poison) = .ok z) : RawExt s (8 * n) ty z := by
  split at h
  · cases h
    cases symAddr ctx u _
    · exact rawExt_poison
    · exact loadN_raw hn
  · cases h; exact rawExt_poison

/-- **What a producer evaluates to** (`runL`'s mode: memory ops do not fault): `poison` or a
result register holding its extension. -/
theorem prod_evalOpL {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} {argv : List Val} {ty : Ty}
    {s : Bool} {k : Nat} {z : Val} (hp : prodSig u.op = some (s, k))
    (h : evalOpL false env ctx fr u argv ty = .ok z) : RawExt s k ty z := by
  have hm := find_mem hp
  simp only [prodOps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  have pure_case : ∀ o : Op, u.op = o → o.generic = false → GoFV.Opt.LowerTerm.actOp o = false →
      isRoot o = false → RawExt s k ty (Arm64.evalPure o ty u.auxInt u.aux argv) →
      RawExt s k ty z := by
    intro o ho hg ha hr hR
    rw [evalOpL_pure (by rw [ho]; exact hg) (by rw [ho]; exact ha) (by rw [ho]; exact hr), ho] at h
    cases h; exact hR
  have ld_case : ∀ n s', (u.op = .ARM64MOVBload ∧ n = 1 ∧ s' = true) ∨
      (u.op = .ARM64MOVBUload ∧ n = 1 ∧ s' = false) ∨
      (u.op = .ARM64MOVHload ∧ n = 2 ∧ s' = true) ∨ (u.op = .ARM64MOVHUload ∧ n = 2 ∧ s' = false) ∨
      (u.op = .ARM64MOVWload ∧ n = 4 ∧ s' = true) ∨ (u.op = .ARM64MOVWUload ∧ n = 4 ∧ s' = false) →
      s' = s → 8 * n = k → RawExt s k ty z := by
    intro n s' hop hs hk
    have hg : u.op.generic = false := by
      rcases hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
    have ha : GoFV.Opt.LowerTerm.actOp u.op = true := by
      rcases hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
    have hn : n = 1 ∨ n = 2 ∨ n = 4 := by
      rcases hop with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
    rw [evalOpL_act hg ha, arm64Op_ld hop] at h
    subst hs hk
    exact ld_raw hn h
  rcases hm with ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ |
    ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ |
    ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ |
    ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ |
    ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩
  · exact ld_case 1 true (.inl ⟨ho, rfl, rfl⟩) rfl rfl
  · exact ld_case 1 false (.inr (.inl ⟨ho, rfl, rfl⟩)) rfl rfl
  · exact ld_case 2 true (.inr (.inr (.inl ⟨ho, rfl, rfl⟩))) rfl rfl
  · exact ld_case 2 false (.inr (.inr (.inr (.inl ⟨ho, rfl, rfl⟩)))) rfl rfl
  · exact ld_case 4 true (.inr (.inr (.inr (.inr (.inl ⟨ho, rfl, rfl⟩))))) rfl rfl
  · exact ld_case 4 false (.inr (.inr (.inr (.inr (.inr ⟨ho, rfl, rfl⟩))))) rfl rfl
  · exact pure_case .ARM64MOVBloadidx ho rfl rfl rfl
      (loadIdx_raw (ty := ty) (n := 1) (scale := 1) (s := true) (args := argv) (by omega))
  · exact pure_case .ARM64MOVBUloadidx ho rfl rfl rfl
      (loadIdx_raw (ty := ty) (n := 1) (scale := 1) (s := false) (args := argv) (by omega))
  · exact pure_case .ARM64MOVHloadidx ho rfl rfl rfl
      (loadIdx_raw (ty := ty) (n := 2) (scale := 1) (s := true) (args := argv) (by omega))
  · exact pure_case .ARM64MOVHUloadidx ho rfl rfl rfl
      (loadIdx_raw (ty := ty) (n := 2) (scale := 1) (s := false) (args := argv) (by omega))
  · exact pure_case .ARM64MOVHloadidx2 ho rfl rfl rfl
      (loadIdx_raw (ty := ty) (n := 2) (scale := 2) (s := true) (args := argv) (by omega))
  · exact pure_case .ARM64MOVHUloadidx2 ho rfl rfl rfl
      (loadIdx_raw (ty := ty) (n := 2) (scale := 2) (s := false) (args := argv) (by omega))
  · exact pure_case .ARM64MOVWloadidx ho rfl rfl rfl
      (loadIdx_raw (ty := ty) (n := 4) (scale := 1) (s := true) (args := argv) (by omega))
  · exact pure_case .ARM64MOVWUloadidx ho rfl rfl rfl
      (loadIdx_raw (ty := ty) (n := 4) (scale := 1) (s := false) (args := argv) (by omega))
  · exact pure_case .ARM64MOVWloadidx4 ho rfl rfl rfl
      (loadIdx_raw (ty := ty) (n := 4) (scale := 4) (s := true) (args := argv) (by omega))
  · exact pure_case .ARM64MOVWUloadidx4 ho rfl rfl rfl
      (loadIdx_raw (ty := ty) (n := 4) (scale := 4) (s := false) (args := argv) (by omega))
  · exact pure_case .ARM64MOVBreg ho rfl rfl rfl
      (op1ext_raw (ty := ty) (s := true) (k := 8) (by omega) (by omega) argv)
  · exact pure_case .ARM64MOVBUreg ho rfl rfl rfl
      (op1ext_raw (ty := ty) (s := false) (k := 8) (by omega) (by omega) argv)
  · exact pure_case .ARM64MOVHreg ho rfl rfl rfl
      (op1ext_raw (ty := ty) (s := true) (k := 16) (by omega) (by omega) argv)
  · exact pure_case .ARM64MOVHUreg ho rfl rfl rfl
      (op1ext_raw (ty := ty) (s := false) (k := 16) (by omega) (by omega) argv)
  · exact pure_case .ARM64MOVWreg ho rfl rfl rfl
      (op1ext_raw (ty := ty) (s := true) (k := 32) (by omega) (by omega) argv)
  · exact pure_case .ARM64MOVWUreg ho rfl rfl rfl
      (op1ext_raw (ty := ty) (s := false) (k := 32) (by omega) (by omega) argv)

/-! ## Evaluating a value of one or two arguments -/

/-- The arguments `evalValueL` reads. -/
abbrev argsL (fr : Frame) (v : Value) : Res (List Val) :=
  v.args.toList.mapM fun a => Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join

theorem evalValueL_of_args {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} (hm : argsL fr v = .ok argv) :
    evalValueL md env ctx fr v =
      (evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other)).bind
        (fun r => .ok (md.retype (ctx.tys[v.id]?.getD .other) r)) := by
  unfold evalValueL; simp only [argsL] at hm; rw [hm]; rfl

theorem evalValueL_ok_args {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValueL md env ctx fr v = .ok y) :
    ∃ argv, argsL fr v = .ok argv ∧ ∃ r, evalOpL md.faulting env ctx fr v argv
      (ctx.tys[v.id]?.getD .other) = .ok r ∧ y = md.retype (ctx.tys[v.id]?.getD .other) r := by
  cases hm : argsL fr v with
  | ok argv =>
    rw [evalValueL_of_args hm] at h
    cases he : evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [he] at h; cases h; exact ⟨argv, rfl, r, he, rfl⟩
    | panic e m => rw [he] at h; cases h
    | stuck msg => rw [he] at h; cases h
  | panic e m =>
    unfold evalValueL at h; simp only [argsL] at hm; rw [hm] at h; cases h
  | stuck msg =>
    unfold evalValueL at h; simp only [argsL] at hm; rw [hm] at h; cases h

theorem argsL_nil {fr : Frame} {v : Value} (h : v.args = #[]) : argsL fr v = .ok [] := by
  simp only [argsL, h]; rfl

theorem argsL_one {fr : Frame} {v : Value} {x : ID} {a : Val} (h : v.args = #[x])
    (hx : fr.regs[x]? = some (some a)) : argsL fr v = .ok [a] := by
  simp only [argsL, h]
  rw [List.mapM_cons, hx]; rfl

theorem argsL_two {fr : Frame} {v : Value} {x c : ID} {a b : Val} (h : v.args = #[x, c])
    (hx : fr.regs[x]? = some (some a)) (hc : fr.regs[c]? = some (some b)) :
    argsL fr v = .ok [a, b] := by
  simp only [argsL, h]
  rw [List.mapM_cons, hx]
  change Res.bind (List.mapM _ [c]) _ = _
  rw [List.mapM_cons, hc]; rfl

theorem argsL_one_inv {fr : Frame} {v : Value} {x : ID} {argv : List Val} (h : v.args = #[x])
    (hm : argsL fr v = .ok argv) : ∃ a, fr.regs[x]? = some (some a) ∧ argv = [a] := by
  simp only [argsL, h] at hm
  rw [List.mapM_cons] at hm
  cases hx : fr.regs[x]? with
  | none => rw [hx] at hm; cases hm
  | some o =>
    cases o with
    | none => rw [hx] at hm; cases hm
    | some a => rw [hx] at hm; cases hm; exact ⟨a, rfl, rfl⟩

/-! ## `MOVDreg`/`MOVDnop` -/

/-- `arm64Op`'s `MOVDreg x`/`MOVDnop x` of register `a` (`sx`: whether `x` sign-extends). -/
def movdVal (ty : Ty) (sx : Bool) : Val → Val
  | .int _ x => Arm64.res ty (if sx then x.signExtend 64 else x.setWidth 64)
  | a => Arm64.regVal ty a

theorem arm64Op_movd {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} {argv : List Val} {ty : Ty}
    (hop : w.op = .ARM64MOVDreg ∨ w.op = .ARM64MOVDnop) :
    arm64Op false env ctx fr w argv ty = (match argv with
      | [a] => .ok (movdVal ty
          (((w.args[0]?.bind ctx.f.value?).map (Arm64.signExtendsIn ctx.f.value?)).getD false) a)
      | _ => Res.ok Val.poison) := by
  unfold arm64Op
  rcases hop with h | h <;>
  · simp only [show nilFaults false ctx w argv = none from rfl, h]
    match argv with
    | [] => rfl
    | [a] => cases a <;> rfl
    | _ :: _ :: _ => rfl

theorem movd_generic {o : Op} (h : o = .ARM64MOVDreg ∨ o = .ARM64MOVDnop) : o.generic = false := by
  rcases h with rfl | rfl <;> rfl

theorem movd_act {o : Op} (h : o = .ARM64MOVDreg ∨ o = .ARM64MOVDnop) :
    GoFV.Opt.LowerTerm.actOp o = true := by
  rcases h with rfl | rfl <;> rfl

/-! ## Consumers -/

/-- A register holding extension `(s, k)` read at shape `t` (`Val.retypeL`): at an integer shape
its low bits, at a pointer shape the word, at `bool` a boolean, else `poison`. -/
def ExtAt (s : Bool) (k : Nat) : Ty → Val → Prop
  | .int w, y => y = .poison ∨ ∃ r : BitVec 64, y = .int w (r.setWidth w.bits) ∧ Arm64.ext s k r = r
  | .bool, y => y = .poison ∨ ∃ b, y = .bool b
  | .ptr _, y => y = .poison ∨ ∃ r : BitVec 64, y = .int .w64 r ∧ Arm64.ext s k r = r
  | _, y => y = .poison

theorem extAt_retypeL {s : Bool} {k : Nat} {ty : Ty} {z : Val} (h : RawExt s k ty z) :
    ExtAt s k ty (Val.retypeL ty z) := by
  rcases h with rfl | ⟨r, rfl, hr⟩
  · cases ty <;> simp [ExtAt, Val.retypeL, Val.widen, Val.retype]
  · cases ty with
    | int w =>
      right; refine ⟨r, ?_, hr⟩
      cases w <;> simp [Val.retypeL, Val.widen, Val.retype, Arm64.res, Width.bits]
    | bool => right; exact ⟨r.getLsbD 0, by simp [Val.retypeL, Val.widen, Val.retype, Arm64.res]⟩
    | ptr e => right; exact ⟨r, by simp [Val.retypeL, Val.widen, Val.retype, Arm64.res], hr⟩
    | _ => simp [ExtAt, Val.retypeL, Val.widen, Val.retype, Arm64.res]

/-- **What a producer's register holds** under `runL` (lowered, memory ops not faulting). -/
theorem prod_evalValueL {md : LMode} (hlow : md.low = true) (hfl : md.faulting = false)
    {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} {s : Bool} {k : Nat} {y : Val}
    (hp : prodSig u.op = some (s, k)) (h : evalValueL md env ctx fr u = .ok y) :
    ExtAt s k (ctx.tys[u.id]?.getD .other) y := by
  obtain ⟨argv, -, r, hr, rfl⟩ := evalValueL_ok_args h
  rw [hfl] at hr
  simp only [LMode.retype, hlow, ite_true]
  exact extAt_retypeL (prod_evalOpL hp hr)

/-- **Dropping an extension of a producer's register** (`dropOK`) changes nothing. -/
theorem drop_eq {sP sE : Bool} {kP kE : Nat} {tx ty : Ty} {a : Val} (hk0 : 0 < kP) (hk64 : kP ≤ 64)
    (hkE : 2 ≤ kE) (hkE' : kE ≤ 64) (hE : ExtAt sP kP tx a) (hd : dropOK sP kP sE kE tx = true) :
    Arm64.op1 ty (Arm64.ext sE kE) [a] = movdVal ty sP a := by
  unfold dropOK at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨hsh, hc⟩ := hd
  cases tx with
  | int w =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hsh
    obtain ⟨hkw, hsw⟩ := hsh
    have hw : w.bits ≤ 64 := by cases w <;> simp [Width.bits]
    rcases hE with rfl | ⟨r, rfl, hr⟩
    · rfl
    · simp only [Arm64.op1, Arm64.reg, movdVal]
      rw [ext_drop hk0 (by omega) hkE' hkw hw (fun h => by rcases hsw with h' | h' <;> simp_all) hc hr,
        movd_fix hk0 hkw hw hr]
  | bool =>
    rcases hE with rfl | ⟨b, rfl⟩
    · rfl
    · simp only [Arm64.op1, Arm64.reg, movdVal, Arm64.regVal]
      rw [ext_bool hkE hkE']
  | ptr e =>
    rcases hE with rfl | ⟨r, rfl, hr⟩
    · rfl
    · have h1 := ext_drop (wb := 64) hk0 (by omega) hkE' hk64 (Nat.le_refl 64) (fun _ => hkE') hc hr
      have h2 := movd_fix (wb := 64) hk0 hk64 (Nat.le_refl 64) hr
      simp only [BitVec.setWidth_eq] at h1 h2
      simp only [Arm64.op1, Arm64.reg, movdVal, BitVec.setWidth_eq, h1, h2]
  | _ => (first | (rw [hE]; rfl))

/-- A producer's first argument sign-extends as its signature says. -/
theorem prod_signExtends {o : Op} {s : Bool} {k : Nat} (h : prodSig o = some (s, k)) :
    Arm64.signExtends o = s ∧ o ≠ .Select0 ∧ o ≠ .Select1 := by
  have hm := find_mem h
  simp only [prodOps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  exact ⟨rfl, by decide, by decide⟩

theorem prod_bits {o : Op} {s : Bool} {k : Nat} (h : prodSig o = some (s, k)) : 0 < k ∧ k ≤ 64 := by
  have hm := find_mem h
  simp only [prodOps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  omega

/-- The extension ops: pure arm64 ops, `op1` of `ext`. -/
theorem ext_cases {o : Op} {s : Bool} {k : Nat} (h : extSig o = some (s, k)) :
    o.generic = false ∧ GoFV.Opt.LowerTerm.actOp o = false ∧ isRoot o = false ∧
      (∀ ty ai (ax : Option AuxRef) args, Arm64.evalPure o ty ai ax args = Arm64.op1 ty (Arm64.ext s k) args) ∧
      2 ≤ k ∧ k ≤ 64 := by
  have hm := find_mem h
  simp only [extOps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  exact ⟨rfl, rfl, by decide, fun _ _ _ _ => rfl, by omega, by omega⟩

theorem imm32_eq (k : Int64) : Arm64.imm32 k = (Arm64.imm k).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [Arm64.imm32, Arm64.imm, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

theorem reg_w64 (K : BitVec 64) : Arm64.reg (.int .w64 K) = some K := by simp [Arm64.reg]

theorem reg32_w64 (K : BitVec 64) : Arm64.reg32 (.int .w64 K) = some (K.setWidth 32) := by
  simp [Arm64.reg32, Arm64.reg]

theorem shl1 (x : BitVec 64) : x <<< 1 = x + x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]
  omega

theorem op2_const {ty : Ty} {f : BitVec 64 → BitVec 64 → BitVec 64} {a : Val} {K : BitVec 64} :
    Arm64.op2 ty f [a, .int .w64 K] = Arm64.op1 ty (fun x => f x K) [a] := by
  unfold Arm64.op2 Arm64.op1
  dsimp only; rw [reg_w64]; cases Arm64.reg a <;> rfl

theorem flags2_const {f : BitVec 64 → BitVec 64 → Flags} {a : Val} {K : BitVec 64} :
    Arm64.flags2 f [a, .int .w64 K] = Arm64.flags1 (fun x => f x K) [a] := by
  unfold Arm64.flags2 Arm64.flags1
  dsimp only; rw [reg_w64]; cases Arm64.reg a <;> rfl

theorem flags2w_const {f : BitVec 32 → BitVec 32 → Flags} {a : Val} {K : BitVec 64} :
    Arm64.flags2w f [a, .int .w64 K] = Arm64.flags1w (fun x => f x (K.setWidth 32)) [a] := by
  unfold Arm64.flags2w Arm64.flags1w
  dsimp only; rw [reg32_w64]; cases Arm64.reg32 a <;> rfl

theorem cmp2_const {f : BitVec 64 → BitVec 64 → BitVec 64 × Flags} {a : Val} {K : BitVec 64} :
    Arm64.cmp2 f [a, .int .w64 K] = Arm64.cmp1 (fun x => f x K) [a] := by
  unfold Arm64.cmp2 Arm64.cmp1
  dsimp only; rw [reg_w64]; cases Arm64.reg a <;> rfl

theorem cmp2w_const {f : BitVec 32 → BitVec 32 → BitVec 32 × Flags} {a : Val} {K : BitVec 64} :
    Arm64.cmp2w f [a, .int .w64 K] = Arm64.cmp1w (fun x => f x (K.setWidth 32)) [a] := by
  unfold Arm64.cmp2w Arm64.cmp1w
  dsimp only; rw [reg32_w64]; cases Arm64.reg32 a <;> rfl

theorem add_const {ty : Ty} {a : Val} {K : BitVec 64} :
    Arm64.add ty [a, .int .w64 K] = Arm64.addP ty a K := by
  cases a <;> simp [Arm64.add, Arm64.addP, Arm64.op2, Arm64.reg] <;> rfl

theorem sub_const {ty : Ty} {a : Val} {K : BitVec 64} :
    Arm64.sub ty [a, .int .w64 K] = Arm64.addP ty a (-K) := by
  cases a <;> simp [Arm64.sub, Arm64.addP, Arm64.op2, Arm64.reg, BitVec.sub_eq_add_neg] <;> rfl

theorem adds_const {ty : Ty} {a : Val} {k : Int64} :
    Arm64.adds ty [a, .int .w64 (Arm64.imm k)] = Arm64.addsConst ty k [a] := by
  unfold Arm64.adds Arm64.addsConst
  dsimp only; rw [reg_w64]; cases Arm64.reg a <;> rfl

/-- **An immediate op is its register op on the constant** (`ARM64latelower.rules:8-21`). -/
theorem imm_eval {o o' : Op} (h : immOf o = some o') :
    o.generic = false ∧ GoFV.Opt.LowerTerm.actOp o = false ∧ isRoot o = false ∧
      o'.generic = false ∧ GoFV.Opt.LowerTerm.actOp o' = false ∧ isRoot o' = false ∧
      ∀ ty k k' (ax ax' : Option AuxRef) a,
        Arm64.evalPure o' ty k' ax' [a, .int .w64 (Arm64.imm k)] = Arm64.evalPure o ty k ax [a] := by
  have hm := find_mem h
  simp only [immOps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    refine ⟨rfl, rfl, by decide, rfl, rfl, by decide, fun ty k k' ax ax' a => ?_⟩
  · exact add_const
  · exact sub_const
  · exact op2_const
  · exact op2_const
  · exact op2_const
  · exact flags2_const
  · dsimp only [Arm64.evalPure]; rw [flags2w_const, ← imm32_eq]
  · rfl
  · dsimp only [Arm64.evalPure]; rw [cmp2w_const, ← imm32_eq]
  · exact cmp2_const
  · dsimp only [Arm64.evalPure]; rw [cmp2w_const, ← imm32_eq]
  · exact adds_const

theorem sll1_eval (ty : Ty) (ax ax' : Option AuxRef) (k : Int64) (a : Val) :
    Arm64.evalPure .ARM64ADD ty k ax' [a, a] = Arm64.evalPure .ARM64SLLconst ty 1 ax [a] := by
  show Arm64.add ty [a, a] = Arm64.op1 ty (Arm64.Shift.ll.apply · (Arm64.amt 1)) [a]
  have h1 : Arm64.amt 1 = 1 := by decide
  rw [h1]
  cases a <;> simp [Arm64.add, Arm64.op1, Arm64.op2, Arm64.Shift.apply, shl1] <;>
    (cases Arm64.reg _ <;> simp [shl1])

theorem zero_eval (ty : Ty) (ax ax' : Option AuxRef) (k : Int64) (args : List Val) :
    Arm64.evalPure .ARM64ZERO ty k ax' args = Arm64.evalPure .ARM64MOVDconst ty 0 ax args := by
  show Arm64.res ty 0 = Arm64.res ty (Arm64.imm 0)
  rw [show Arm64.imm 0 = 0 by decide]

end GoFV.Proof.LateLowerL
