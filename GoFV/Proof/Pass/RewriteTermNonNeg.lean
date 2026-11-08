import GoFV.Proof.Pass.RewriteTermDen

variable [GoFV.SSA.Sem.Addrs]

/-!
# `isNonNegative` on the definitions (issue #69)

The rewrite validator decides `isNonNegative(x)` (`rewrite.go`) structurally on the
definitions (`GoFV.Opt.RewriteCheck.nonNegD`). `nonNegD_den`: then every evaluation of `x` as a
term (`GoFV.Proof.Term.den`, any fuel, any atom valuation fixed by `retype` at the atoms'
shapes) is a nonnegative integer or `poison` (`Val.nonNeg`), which is `Rule.Sound`'s premise
`Pat.nonNegOK` at the leaf bound to `x`.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-- A nonnegative integer of width `w`, or `poison`. -/
def NNW (w : Width) (v : Val) : Prop :=
  v = .poison ∨ ∃ x : BitVec w.bits, v = .int w x ∧ x.msb = false

theorem nnw_retype {w : Width} {v : Val} (h : NNW w v) : (v.retype (.int w)).nonNeg = true := by
  rcases h with rfl | ⟨x, rfl, hx⟩
  · rfl
  · simp [Val.retype, Val.nonNeg, hx]

theorem msb_of_nonNeg {a : Val} {w : Width} {x : BitVec w.bits} (ha : a.nonNeg = true)
    (hx : a.asInt w = some x) : x.msb = false := by
  cases a with
  | int w' y =>
    simp only [Val.asInt] at hx
    split at hx
    · rename_i h; subst h; cases hx; simpa [Val.nonNeg] using ha
    · cases hx
  | _ => simp [Val.asInt] at hx

theorem nnw_int2 {w : Width} {f : BitVec w.bits → BitVec w.bits → Val} {args : List Val}
    (P : BitVec w.bits → BitVec w.bits → Prop)
    (hP : ∀ a b x y, args = [a, b] → a.asInt w = some x → b.asInt w = some y → P x y)
    (hf : ∀ x y, P x y → NNW w (f x y)) : NNW w (Sem.int2 w f args) := by
  unfold Sem.int2
  split
  · rename_i a b
    split
    · rename_i x y hx hy; exact hf x y (hP a b x y rfl hx hy)
    · exact .inl rfl
  · exact .inl rfl

/-- Both arguments of a binary op are nonnegative integers of width `w`. -/
theorem msb_all {w : Width} {args : List Val} (h : ∀ a ∈ args, a.nonNeg = true) :
    ∀ a b x y, args = [a, b] → a.asInt w = some x → b.asInt w = some y →
      x.msb = false ∧ y.msb = false := by
  rintro a b x y rfl hx hy
  exact ⟨msb_of_nonNeg (h a (by simp)) hx, msb_of_nonNeg (h b (by simp)) hy⟩

theorem nn_and (w : Width) (args : List Val) (h : ∃ a ∈ args, a.nonNeg = true) :
    NNW w (Sem.Int.and w args) := by
  refine nnw_int2 (fun x y => x.msb = false ∨ y.msb = false) ?_ ?_
  · rintro a b x y rfl hx hy
    obtain ⟨c, hc, hn⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact .inl (msb_of_nonNeg hn hx)
    · exact .inr (msb_of_nonNeg hn hy)
  · intro x y hm
    refine .inr ⟨_, rfl, ?_⟩
    rw [BitVec.msb_and]
    rcases hm with hm | hm <;> simp [hm]

theorem nn_or (w : Width) (args : List Val) (h : ∀ a ∈ args, a.nonNeg = true) :
    NNW w (Sem.Int.or w args) :=
  nnw_int2 (fun x y => x.msb = false ∧ y.msb = false) (msb_all h) fun _ _ hm =>
    .inr ⟨_, rfl, by rw [BitVec.msb_or, hm.1, hm.2]; rfl⟩

theorem nn_xor (w : Width) (args : List Val) (h : ∀ a ∈ args, a.nonNeg = true) :
    NNW w (Sem.Int.xor w args) :=
  nnw_int2 (fun x y => x.msb = false ∧ y.msb = false) (msb_all h) fun _ _ hm =>
    .inr ⟨_, rfl, by rw [BitVec.msb_xor, hm.1, hm.2]; rfl⟩

theorem nn_divs (w : Width) (fl : Bool) (args : List Val) (h : ∀ a ∈ args, a.nonNeg = true) :
    NNW w (Sem.Int.divs w fl args) := by
  refine nnw_int2 (fun x y => x.msb = false ∧ y.msb = false) (msb_all h) fun x y hm => ?_
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · refine .inr ⟨_, rfl, ?_⟩
      have : x.sdiv y = x / y := by simp [BitVec.sdiv, hm.1, hm.2, BitVec.udiv_eq]
      rw [this]; exact BitVec.msb_udiv_eq_false_of hm.1

theorem nn_mods (w : Width) (fl : Bool) (args : List Val) (h : ∀ a ∈ args, a.nonNeg = true) :
    NNW w (Sem.Int.mods w fl args) := by
  refine nnw_int2 (fun x y => x.msb = false ∧ y.msb = false) (msb_all h) fun x y hm => ?_
  split
  · exact .inl rfl
  · split
    · exact .inl rfl
    · refine .inr ⟨_, rfl, ?_⟩
      have : x.srem y = x % y := by simp [BitVec.srem, hm.1, hm.2, BitVec.umod_eq]
      rw [this]; exact BitVec.msb_umod_eq_false_of_left hm.1 y

theorem nn_rsh (w a : Width) (fl : Bool) (args : List Val)
    (h : ∀ x, args.head? = some x → x.nonNeg = true) : NNW w (Shift.rsh w a fl args) := by
  unfold Shift.rsh Shift.shift
  split
  · rename_i x s
    split
    · rename_i x' s' hx _
      split
      · exact .inl rfl
      · refine .inr ⟨_, rfl, ?_⟩
        rw [BitVec.msb_sshiftRight]; exact msb_of_nonNeg (h x rfl) hx
    · exact .inl rfl
  · exact .inl rfl

theorem bits_pos (w : Width) : 0 < w.bits := by cases w <;> decide

theorem nn_rshu (w : Width) (fl : Bool) (args : List Val)
    (h : ∀ s, args[1]? = some s → s = .poison ∨ ∃ s' : BitVec 64, s = .int .w64 s' ∧ 0 < s'.toNat) :
    NNW w (Shift.rshu w .w64 fl args) := by
  unfold Shift.rshu Shift.shift
  split
  · rename_i x s
    split
    · rename_i x' s' _ hs
      split
      · exact .inl rfl
      · refine .inr ⟨_, rfl, ?_⟩
        rw [BitVec.msb_ushiftRight]
        rcases h s rfl with rfl | ⟨s'', rfl, hp⟩
        · simp [Val.asInt] at hs
        · simp only [Val.asInt_int, Option.some.injEq] at hs
          subst hs
          have := bits_pos w
          simp only [Bool.and_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
            decide_eq_true_eq]
          exact .inl (by show 0 < min s''.toNat w.bits; omega)
    · exact .inl rfl
  · exact .inl rfl

theorem nn_signExt (w0 w : Width) (hw : w0.bits < w.bits) (args : List Val)
    (h : ∀ x, args.head? = some x → x.nonNeg = true) : NNW w (Conv.signExt w0 w args) := by
  unfold Conv.signExt Sem.int1
  split
  · rename_i a
    split
    · rename_i x hx
      refine .inr ⟨_, rfl, ?_⟩
      rw [BitVec.signExtend_eq_setWidth_of_msb_false (msb_of_nonNeg (h a rfl) hx),
        BitVec.msb_setWidth, BitVec.getLsbD_of_ge _ _ (by omega), Bool.and_false]
    · exact .inl rfl
  · exact .inl rfl

theorem nn_zeroExt (w0 w : Width) (hw : w0.bits < w.bits) (args : List Val) :
    NNW w (Conv.zeroExt w0 w args) := by
  unfold Conv.zeroExt Sem.int1
  split
  · split
    · refine .inr ⟨_, rfl, ?_⟩
      rw [BitVec.msb_setWidth, BitVec.getLsbD_of_ge _ _ (by omega), Bool.and_false]
    · exact .inl rfl
  · exact .inl rfl

theorem nnw_count (rw : Width) {n : Nat} (hn : n ≤ 64) : NNW rw (Sem.Int.count (some rw) n) := by
  refine .inr ⟨_, rfl, ?_⟩
  rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  have h1 := Nat.mod_le n (2 ^ rw.bits)
  have h2 : 128 ≤ 2 ^ (rw.bits - 1) := by cases rw <;> decide
  omega

theorem ctz_toNat_le {n : Nat} (x : BitVec n) : x.ctz.toNat ≤ n := by
  have h := BitVec.clz_le (x := x.reverse)
  rw [BitVec.le_def] at h
  simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat] at h
  unfold BitVec.ctz
  have := Nat.mod_le n (2 ^ n)
  omega

theorem w_bits_le (w : Width) : w.bits ≤ 64 := by cases w <;> decide

theorem nn_ctz (w : Width) (nz : Bool) (rw : Width) (args : List Val) :
    NNW rw (Sem.Int.ctz w nz (some rw) args) := by
  unfold Sem.Int.ctz Sem.int1
  split
  · split
    · rename_i x _
      dsimp only
      split
      · exact .inl rfl
      · exact nnw_count rw (by have := ctz_toNat_le x; have := w_bits_le w; omega)
    · exact .inl rfl
  · exact .inl rfl

theorem nn_bitLen (w : Width) (rw : Width) (args : List Val) :
    NNW rw (Sem.Int.bitLen w (some rw) args) := by
  unfold Sem.Int.bitLen Sem.int1
  split
  · split
    · exact nnw_count rw (by have := w_bits_le w; omega)
    · exact .inl rfl
  · exact .inl rfl

/-- A length or capacity: component 1 or 2 of a value of the string or a slice shape. -/
theorem nn_select (i : Nat) (hi : i = 1 ∨ i = 2) (args : List Val)
    (h : ∀ a, args.head? = some a → a.hasTy .str = true ∨ ∃ e, a.hasTy (.slice e) = true) :
    NNW .w64 (Comp.select i args) := by
  unfold Comp.select
  split
  · rename_i vs
    rcases h _ rfl with hs | ⟨e, hs⟩
    · rcases Val.hasTy_str hs with h0 | ⟨p, l, h0, hl, -⟩
      · cases h0
      · cases h0
        rcases hi with rfl | rfl
        · exact .inr ⟨l, rfl, hl⟩
        · exact .inl rfl
    · rcases Val.hasTy_slice hs with h0 | ⟨p, l, c, h0, hl, hc, -⟩
      · cases h0
      · cases h0
        rcases hi with rfl | rfl
        · exact .inr ⟨l, rfl, hl⟩
        · exact .inr ⟨c, rfl, hc⟩
  · exact .inl rfl

/-- What `nonNegD` relies on for an op of kind `k`. -/
def NNSem (op : Op) : NNKind → Prop
  | .const w => ∀ ty ai ax args, evalPure op ty ai ax args = Conv.const w ai
  | .always w? => ∀ rw ai ax args, w?.all (· == rw) = true →
      NNW rw (evalPure op (.int rw) ai ax args)
  | .rshuC w => ∀ ty ai ax args,
      (∀ s, args[1]? = some s → s = .poison ∨ ∃ s' : BitVec 64, s = .int .w64 s' ∧ 0 < s'.toNat) →
      NNW w (evalPure op ty ai ax args)
  | .arg0 w => ∀ ty ai ax args, (∀ x, args.head? = some x → x.nonNeg = true) →
      NNW w (evalPure op ty ai ax args)
  | .anyArg w => ∀ ty ai ax args, (∃ a ∈ args, a.nonNeg = true) →
      NNW w (evalPure op ty ai ax args)
  | .allArgs w => ∀ ty ai ax args, (∀ a ∈ args, a.nonNeg = true) →
      NNW w (evalPure op ty ai ax args)
  | .len => ∀ ty ai ax args,
      (∀ a, args.head? = some a → a.hasTy .str = true ∨ ∃ e, a.hasTy (.slice e) = true) →
      NNW .w64 (evalPure op ty ai ax args)

theorem nnTable_sound : ∀ p ∈ nnTable, NNSem p.1 p.2 ∧ GoFV.Proof.Rules.frameOp p.1 = false ∧
    termOp p.1 = true := by
  intro p hp
  simp only [nnTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals refine ⟨?_, rfl, rfl⟩
  all_goals dsimp only [NNSem]
  · exact fun _ _ _ _ => rfl
  · exact fun _ _ _ _ => rfl
  · exact fun _ _ _ _ => rfl
  · exact fun _ _ _ _ => rfl
  · intro rw _ _ args h; simp only [Option.all_some, beq_iff_eq] at h; subst h; exact nn_zeroExt .w8 .w64 (by decide) args
  · intro rw _ _ args h; simp only [Option.all_some, beq_iff_eq] at h; subst h; exact nn_zeroExt .w16 .w64 (by decide) args
  · intro rw _ _ args h; simp only [Option.all_some, beq_iff_eq] at h; subst h; exact nn_zeroExt .w32 .w64 (by decide) args
  · intro rw _ _ args h; simp only [Option.all_some, beq_iff_eq] at h; subst h; exact nn_zeroExt .w8 .w32 (by decide) args
  · intro rw _ _ args h; simp only [Option.all_some, beq_iff_eq] at h; subst h; exact nn_zeroExt .w16 .w32 (by decide) args
  · intro rw _ _ args h; simp only [Option.all_some, beq_iff_eq] at h; subst h; exact nn_zeroExt .w8 .w16 (by decide) args
  · exact fun rw _ _ args _ => nn_ctz .w64 false rw args
  · exact fun rw _ _ args _ => nn_ctz .w32 false rw args
  · exact fun rw _ _ args _ => nn_ctz .w16 false rw args
  · exact fun rw _ _ args _ => nn_ctz .w8 false rw args
  · exact fun rw _ _ args _ => nn_ctz .w64 true rw args
  · exact fun rw _ _ args _ => nn_ctz .w32 true rw args
  · exact fun rw _ _ args _ => nn_ctz .w16 true rw args
  · exact fun rw _ _ args _ => nn_ctz .w8 true rw args
  · exact fun rw _ _ args _ => nn_bitLen .w64 rw args
  · exact fun rw _ _ args _ => nn_bitLen .w32 rw args
  · exact fun rw _ _ args _ => nn_bitLen .w16 rw args
  · exact fun rw _ _ args _ => nn_bitLen .w8 rw args
  · exact fun _ _ _ args h => nn_rshu .w64 _ args h
  · exact fun _ _ _ args h => nn_rshu .w32 _ args h
  · exact fun _ _ _ args h => nn_rsh .w64 .w64 _ args h
  · exact fun _ _ _ args h => nn_rsh .w32 .w64 _ args h
  · exact fun _ _ _ args h => nn_rsh .w8 .w64 _ args h
  · exact fun _ _ _ args h => nn_rsh .w16 .w64 _ args h
  · exact fun _ _ _ args h => nn_rsh .w32 .w32 _ args h
  · exact fun _ _ _ args h => nn_rsh .w64 .w32 _ args h
  · exact fun _ _ _ args h => nn_signExt .w32 .w64 (by decide) args h
  · exact fun _ _ _ args h => nn_signExt .w16 .w64 (by decide) args h
  · exact fun _ _ _ args h => nn_signExt .w8 .w64 (by decide) args h
  · exact fun _ _ _ args h => nn_signExt .w16 .w32 (by decide) args h
  · exact fun _ _ _ args h => nn_signExt .w8 .w32 (by decide) args h
  · exact fun _ _ _ args h => nn_and .w64 args h
  · exact fun _ _ _ args h => nn_and .w32 args h
  · exact fun _ _ _ args h => nn_and .w16 args h
  · exact fun _ _ _ args h => nn_and .w8 args h
  · exact fun _ _ _ args h => nn_mods .w64 _ args h
  · exact fun _ _ _ args h => nn_mods .w32 _ args h
  · exact fun _ _ _ args h => nn_mods .w16 _ args h
  · exact fun _ _ _ args h => nn_mods .w8 _ args h
  · exact fun _ _ _ args h => nn_divs .w64 _ args h
  · exact fun _ _ _ args h => nn_divs .w32 _ args h
  · exact fun _ _ _ args h => nn_divs .w16 _ args h
  · exact fun _ _ _ args h => nn_divs .w8 _ args h
  · exact fun _ _ _ args h => nn_or .w64 args h
  · exact fun _ _ _ args h => nn_or .w32 args h
  · exact fun _ _ _ args h => nn_or .w16 args h
  · exact fun _ _ _ args h => nn_or .w8 args h
  · exact fun _ _ _ args h => nn_xor .w64 args h
  · exact fun _ _ _ args h => nn_xor .w32 args h
  · exact fun _ _ _ args h => nn_xor .w16 args h
  · exact fun _ _ _ args h => nn_xor .w8 args h
  · exact fun _ _ _ args h => nn_select 1 (.inl rfl) args h
  · exact fun _ _ _ args h => nn_select 1 (.inl rfl) args h
  · exact fun _ _ _ args h => nn_select 2 (.inr rfl) args h

theorem nonNegKind_mem {op : Op} {k : NNKind} (h : nonNegKind op = some k) : (op, k) ∈ nnTable := by
  unfold nonNegKind at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hb := List.find?_some hp
  simp only [beq_iff_eq] at hb
  rw [← hb]
  exact List.mem_of_find?_eq_some hp

theorem isIntW_eq {t : Ty} {w : Width} (h : isIntW t w = true) : t = .int w := by
  unfold isIntW at h
  split at h
  · rw [beq_iff_eq] at h; subst h; rfl
  · cases h

theorem head?_map_toList {α β : Type} (a : Array α) (f : α → β) :
    (a.toList.map f).head? = a[0]?.map f := by
  rcases a with ⟨l⟩; cases l <;> rfl

theorem getElem?_one_map_toList {α β : Type} (a : Array α) (f : α → β) :
    (a.toList.map f)[1]? = a[1]?.map f := by
  simp

/-- The value of a `Const64` node typed `int64` with a positive auxint, at any fuel. -/
theorem den_const64_pos {tabs : Tables} {D : ID → Option Value} {ρ : ID → Val} {b : ID}
    {bv : Value} (hD : D b = some bv) (hop : bv.op = .Const64) (hai : bv.auxInt > 0)
    (hty : isIntW (tabs.ty bv.type) .w64 = true) (n : Nat) :
    den D tabs ρ n b = .poison ∨ ∃ s' : BitVec 64, den D tabs ρ n b = .int .w64 s' ∧ 0 < s'.toNat := by
  cases n with
  | zero => exact .inl rfl
  | succ n =>
    right
    have ht : termOp bv.op = true := by rw [hop]; rfl
    have hf : GoFV.Proof.Rules.frameOp bv.op = false := by rw [hop]; rfl
    simp only [den, hD, ht, ite_true, GoFV.Proof.Rules.opVal_pure hf, isIntW_eq hty, hop]
    refine ⟨_, rfl, ?_⟩
    have h1 : 0 < bv.auxInt.toInt := Int64.lt_iff_toInt_lt.1 hai
    have h2 := Int64.toInt_lt bv.auxInt
    simp only [Conv.const, Val.retype, Width.bits, Nat.le_refl, ite_true, BitVec.setWidth_eq,
      BitVec.toNat_ofInt]
    omega

/-- **`isNonNegative` decided on the definitions is a fact about every evaluation** whose atoms
are fixed by `retype` at their shapes (`Typed`: a length read from a string or slice atom is
then nonnegative). -/
theorem nonNegD_den (tabs : Tables) (D : ID → Option Value) (ρ : ID → Val)
    (hT : Term.Typed D tabs ρ) : ∀ k n x, nonNegD tabs D k x = true → (den D tabs ρ n x).nonNeg = true
  | 0, _, _, h => by simp [nonNegD] at h
  | _ + 1, 0, _, _ => rfl
  | k + 1, n + 1, x, h => by
    unfold nonNegD at h
    cases hD : D x with
    | none => rw [hD] at h; cases h
    | some v =>
      rw [hD] at h
      dsimp only at h
      cases hk : nonNegKind v.op with
      | none => rw [hk] at h; simp at h
      | some kd =>
        rw [hk] at h
        obtain ⟨hsem, hfr, -⟩ := nnTable_sound _ (nonNegKind_mem hk)
        have IH := nonNegD_den tabs D ρ hT k n
        have ht : termOp v.op = true := by
          revert h; cases termOp v.op <;> simp
        simp only [ht, Bool.true_and] at h
        simp only [den, hD, ht, ite_true, GoFV.Proof.Rules.opVal_pure hfr]
        cases kd with
        | const w => rw [hsem]; exact h
        | always w? =>
          revert h
          cases hrw : tabs.ty v.type with
          | int rw => intro h; exact nnw_retype (hsem rw _ _ _ h)
          | _ => intro h; cases h
        | rshuC w =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨hw, h⟩ := h
          rw [isIntW_eq hw]
          refine nnw_retype (hsem _ _ _ _ fun s hs => ?_)
          rw [getElem?_one_map_toList] at hs
          cases hb : v.args[1]? with
          | none => rw [hb] at hs; cases hs
          | some b =>
            rw [hb] at hs h; cases hs
            simp only [Option.bind_some] at h
            cases hbD : D b with
            | none => rw [hbD] at h; cases h
            | some bv =>
              rw [hbD] at h
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
              exact den_const64_pos hbD h.1.1 h.1.2 h.2 n
        | arg0 w =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨hw, h⟩ := h
          rw [isIntW_eq hw]
          refine nnw_retype (hsem _ _ _ _ fun a ha => ?_)
          rw [head?_map_toList] at ha
          cases hb : v.args[0]? with
          | none => rw [hb] at ha; cases ha
          | some b =>
            rw [hb] at ha h; cases ha
            exact IH b h
        | anyArg w =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨hw, h⟩ := h
          rw [isIntW_eq hw]
          refine nnw_retype (hsem _ _ _ _ ?_)
          rw [← Array.any_toList, List.any_eq_true] at h
          obtain ⟨b, hb, hn⟩ := h
          exact ⟨_, List.mem_map_of_mem hb, IH b hn⟩
        | allArgs w =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨hw, h⟩ := h
          rw [isIntW_eq hw]
          refine nnw_retype (hsem _ _ _ _ ?_)
          rw [← Array.all_toList, List.all_eq_true] at h
          intro a ha
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
          exact IH b (h b hb)
        | len =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨hw, h⟩ := h
          rw [isIntW_eq hw]
          refine nnw_retype (hsem _ _ _ _ fun a ha => ?_)
          rw [head?_map_toList] at ha
          cases hb : v.args[0]? with
          | none => rw [hb] at ha; cases ha
          | some b =>
            rw [hb] at ha h; cases ha
            simp only [Option.bind_some] at h
            cases hbD : D b with
            | none => rw [hbD] at h; cases h
            | some bv =>
              rw [hbD] at h
              have hty := den_hasTy hT n hbD
              cases hs : tabs.ty bv.type with
              | str => rw [hs] at hty; exact .inl hty
              | slice e => rw [hs] at hty; exact .inr ⟨e, hty⟩
              | _ => simp [hs, lenShape] at h

/-- `nn_select` applies to the capacity of a defined slice (`len 2 ≤ cap 5`). -/
example : NNW .w64 (Comp.select 2 [.agg [.int .w64 0, .int .w64 2, .int .w64 5]]) :=
  nn_select 2 (.inr rfl) _ fun _ h => by
    cases h; exact .inr ⟨some 8, by decide⟩

end GoFV.Proof.Pass.Rewrite
