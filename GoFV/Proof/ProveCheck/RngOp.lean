import GoFV.Proof.ProveCheck.Den

variable [GoFV.SSA.Sem.Addrs]

/-!
# The range of an `ROp` node is sound (issue #24)

`rOpRng_mem`: if the node's value (its family function on its arguments' values `val`,
retyped at `int w`) is the `w`-bit integer `y`, and every argument's integer value lies in its
range (`R`), then `y` lies in `rOpRng R w c …`.
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ProveCheck

theorem retype_int_val {w : Width} {x y : BitVec w.bits} (h : (Val.int w x).retype (.int w) = .int w y) :
    x = y := by
  rw [retype_int_self] at h; cases h; rfl

theorem pow_le_pow_bits {a b : Width} (h : a.bits ≤ b.bits) : 2 ^ a.bits ≤ 2 ^ b.bits :=
  Nat.pow_le_pow_right (by decide) h

theorem bits_le_64 (w : Width) : w.bits ≤ 64 := by cases w <;> decide
theorem bits_ge_8 (w : Width) : 8 ≤ w.bits := by cases w <;> decide

/-- Unfold a unary family at a defined result. -/
theorem int1_res {a w : Width} {f : BitVec a.bits → Val} {argv : List Val} {y : BitVec w.bits}
    (h : (Sem.int1 a f argv).retype (.int w) = .int w y) :
    ∃ v x, argv = [v] ∧ v = .int a x ∧ (f x).retype (.int w) = .int w y := by
  have hne : Sem.int1 a f argv ≠ .poison := fun e => by rw [e, retype_poison'] at h; cases h
  obtain ⟨v, x, h1, h2, h3⟩ := int1_eq rfl hne
  exact ⟨v, x, h1, h2, by rw [h3]; exact h⟩

theorem int2_res {w : Width} {f : BitVec w.bits → BitVec w.bits → Val} {argv : List Val}
    {y : BitVec w.bits} (h : (Sem.int2 w f argv).retype (.int w) = .int w y) :
    ∃ u v x x', argv = [u, v] ∧ u = .int w x ∧ v = .int w x' ∧ (f x x').retype (.int w) = .int w y := by
  have hne : Sem.int2 w f argv ≠ .poison := fun e => by rw [e, retype_poison'] at h; cases h
  obtain ⟨u, v, x, x', h1, h2, h3, h4⟩ := int2_eq rfl hne
  exact ⟨u, v, x, x', h1, h2, h3, by rw [h4]; exact h⟩

theorem map_one {val : ID → Val} {args : Array ID} {v : Val} (h : args.toList.map val = [v]) :
    val (args[0]?.getD 0) = v := by
  rcases hl : args.toList with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rw [hl] at h <;> simp at h
  have : args[0]? = some a := by rw [← Array.getElem?_toList, hl]; rfl
  rw [this]; exact h

theorem map_two {val : ID → Val} {args : Array ID} {u v : Val} (h : args.toList.map val = [u, v]) :
    val (args[0]?.getD 0) = u ∧ val (args[1]?.getD 0) = v := by
  rcases hl : args.toList with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> rw [hl] at h <;> simp at h
  have h0 : args[0]? = some a := by rw [← Array.getElem?_toList, hl]; rfl
  have h1 : args[1]? = some b := by rw [← Array.getElem?_toList, hl]; rfl
  rw [h0, h1]; exact h

/-- **The range of a node.** -/
theorem rOpRng_mem {R : Width → ID → Rng} {val : ID → Val}
    (hR : ∀ (w : Width) (x : ID) (y : BitVec w.bits), val x = .int w y → (R w x).Mem y)
    {w : Width} {c : ROp} {ai : Int64} {args : Array ID} {y : BitVec w.bits}
    (h : (rOpEval c (some w) ai (args.toList.map val)).retype (.int w) = .int w y) :
    (rOpRng R w c ai args).Mem y := by
  have hn := Width.one_le w
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ := reading hn y
  cases c with
  | const w' =>
    simp only [rOpRng]
    split
    · rename_i e; simp only [beq_iff_eq] at e; subst e
      simp only [rOpEval, Conv.const] at h
      rw [← retype_int_val h]; exact Rng.mem_point _
    · exact Rng.mem_top hn y
  | zext a b =>
    simp only [rOpRng]
    split
    · rename_i e; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at e
      obtain ⟨rfl, hab⟩ := e
      obtain ⟨v, x, hv, rfl, hf⟩ := int1_res (a := a) h
      have hy := retype_int_val hf
      have hm := hR a _ x (map_one hv)
      obtain ⟨m1, m2, -, -⟩ := hm
      have hx : x.toNat < 2 ^ b.bits := Nat.lt_of_lt_of_le x.isLt (pow_le_pow_bits hab)
      have : y.toNat = x.toNat := by rw [← hy, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]
      exact Rng.mem_ofU hn (by omega) (by omega)
    · exact Rng.mem_top hn y
  | sext a b =>
    simp only [rOpRng]
    split
    · rename_i e; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at e
      obtain ⟨rfl, hab⟩ := e
      obtain ⟨v, x, hv, rfl, hf⟩ := int1_res (a := a) h
      have hy := retype_int_val hf
      have hm := hR a _ x (map_one hv)
      obtain ⟨-, -, m3, m4⟩ := hm
      have : y.toInt = x.toInt := by
        rw [← hy, BitVec.toInt_signExtend, Nat.min_eq_right hab]
        obtain ⟨Ha, a1, a2, a3, a4, a5, a6, a7⟩ := reading (Width.one_le a) x
        have l1 := BitVec.le_toInt x
        have l2 := BitVec.toInt_lt (x := x)
        rw [a4] at l1 l2
        exact Int.bmod_eq_of_le_mul_two (by rw [a1]; push_cast; omega) (by rw [a1]; push_cast; omega)
      exact Rng.mem_ofS hn (by omega) (by omega)
    · exact Rng.mem_top hn y
  | and w' =>
    simp only [rOpRng]
    split
    · rename_i e; simp only [beq_iff_eq] at e; subst e
      obtain ⟨u, v, x, x', hv, rfl, rfl, hf⟩ := int2_res h
      have hy := retype_int_val hf
      obtain ⟨hu, hv'⟩ := map_two hv
      obtain ⟨-, m2, -, -⟩ := hR _ _ x hu
      obtain ⟨-, n2, -, -⟩ := hR _ _ x' hv'
      have : y.toNat ≤ x.toNat ∧ y.toNat ≤ x'.toNat := by
        rw [← hy, BitVec.toNat_and]; exact ⟨Nat.and_le_left, Nat.and_le_right⟩
      exact Rng.mem_ofU hn (by omega) (by omega)
    · exact Rng.mem_top hn y
  | modu w' =>
    simp only [rOpRng]
    split
    · rename_i e; simp only [beq_iff_eq] at e; subst e
      split
      · rename_i hlo
        obtain ⟨u, v, x, x', hv, rfl, rfl, hf⟩ := int2_res h
        obtain ⟨hu, hv'⟩ := map_two hv
        obtain ⟨-, m2, -, -⟩ := hR _ _ x hu
        obtain ⟨n1, n2, -, -⟩ := hR _ _ x' hv'
        split at hf
        · rw [retype_poison'] at hf; cases hf
        · have hy := retype_int_val hf
          have hpos : 0 < x'.toNat := by omega
          have : y.toNat < x'.toNat ∧ y.toNat ≤ x.toNat := by
            rw [← hy, BitVec.toNat_umod]; exact ⟨Nat.mod_lt _ hpos, Nat.mod_le _ _⟩
          exact Rng.mem_ofU hn (by omega) (by omega)
      · exact Rng.mem_top hn y
    · exact Rng.mem_top hn y
  | add w' =>
    simp only [rOpRng]
    split
    · rename_i e; simp only [beq_iff_eq] at e; subst e
      obtain ⟨u, v, x, x', hv, rfl, rfl, hf⟩ := int2_res h
      have hy := retype_int_val hf
      obtain ⟨hu, hv'⟩ := map_two hv
      obtain ⟨m1, m2, m3, m4⟩ := hR _ _ x hu
      obtain ⟨n1, n2, n3, n4⟩ := hR _ _ x' hv'
      refine Rng.mem_meet ?_ ?_
      · split
        · rename_i hlt
          have : y.toNat = x.toNat + x'.toNat := by
            rw [← hy, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
          exact Rng.mem_ofU hn (by omega) (by omega)
        · exact Rng.mem_top hn y
      · split
        · rename_i hlt
          rw [h4] at hlt
          have : y.toInt = x.toInt + x'.toInt := by
            rw [← hy, BitVec.toInt_add]
            exact Int.bmod_eq_of_le_mul_two (by rw [h1]; push_cast; omega)
              (by rw [h1]; push_cast; omega)
          exact Rng.mem_ofS hn (by omega) (by omega)
        · exact Rng.mem_top hn y
    · exact Rng.mem_top hn y
  | sub w' =>
    simp only [rOpRng]
    split
    · rename_i e; simp only [beq_iff_eq] at e; subst e
      obtain ⟨u, v, x, x', hv, rfl, rfl, hf⟩ := int2_res h
      have hy := retype_int_val hf
      obtain ⟨hu, hv'⟩ := map_two hv
      obtain ⟨m1, m2, m3, m4⟩ := hR _ _ x hu
      obtain ⟨n1, n2, n3, n4⟩ := hR _ _ x' hv'
      refine Rng.mem_meet ?_ ?_
      · split
        · rename_i hle
          have : y.toNat = x.toNat - x'.toNat := by
            rw [← hy, BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega))]
          exact Rng.mem_ofU hn (by omega) (by omega)
        · exact Rng.mem_top hn y
      · split
        · rename_i hlt
          rw [h4] at hlt
          have : y.toInt = x.toInt - x'.toInt := by
            rw [← hy, BitVec.toInt_sub]
            exact Int.bmod_eq_of_le_mul_two (by rw [h1]; push_cast; omega)
              (by rw [h1]; push_cast; omega)
          exact Rng.mem_ofS hn (by omega) (by omega)
        · exact Rng.mem_top hn y
    · exact Rng.mem_top hn y
  | bitLen a =>
    simp only [rOpRng]
    obtain ⟨v, x, hv, rfl, hf⟩ := int1_res (a := a) h
    simp only [Sem.Int.count] at hf
    have hy := retype_int_val hf
    have hk : a.bits - x.clz.toNat ≤ a.bits := Nat.sub_le _ _
    have h64 := bits_le_64 a
    have h8 := bits_ge_8 w
    have hp : 256 ≤ 2 ^ w.bits := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) h8; simpa using this
    have : y.toNat = a.bits - x.clz.toNat := by
      rw [← hy, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Rng.mem_ofU hn (by omega) (by omega)
  | popCount a =>
    simp only [rOpRng]
    obtain ⟨v, x, hv, rfl, hf⟩ := int1_res (a := a) h
    simp only [Sem.Int.count] at hf
    have hy := retype_int_val hf
    have hk := BitVec.toNat_cpop_le x
    have h64 := bits_le_64 a
    have h8 := bits_ge_8 w
    have hp : 256 ≤ 2 ^ w.bits := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) h8; simpa using this
    have : y.toNat = x.cpop.toNat := by
      rw [← hy, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Rng.mem_ofU hn (by omega) (by omega)
  | b2u =>
    simp only [rOpRng]
    split
    · rename_i e; simp only [beq_iff_eq] at e; subst e
      simp only [rOpEval, Conv.boolToUint8] at h
      split at h
      · rename_i bv _
        cases hb : bv.asBool with
        | none => rw [hb, retype_poison'] at h; cases h
        | some bb =>
          rw [hb] at h
          have hy := retype_int_val h
          have : y.toNat ≤ 1 := by rw [← hy]; cases bb <;> decide
          exact Rng.mem_ofU hn (by omega) this
      · rw [retype_poison'] at h; cases h
    · exact Rng.mem_top hn y

end GoFV.Proof.ProveCheck
