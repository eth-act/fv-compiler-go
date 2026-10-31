import GoFV.Proof.WF

/-!
# `check` establishes `WF`

`check_wf`: a passing `check ce f` gives `WF ce f`. The first block loop of `check` is followed
with the invariant `Loop1` (block marks are exactly the blocks visited, value marks exactly
their values, each visited block passed its crosslink and value checks), its value loop with
`Loop2`; the later loops (missing predecessors/successors, missing arguments/controls) and the
entry checks are read off pointwise. `checkValue_ok`/`checkAux_bool` extract the op-shape
facts of one value.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Check

namespace CheckFacts

theorem bind_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {b : β}
    (h : (x >>= g) = .ok b) : ∃ a, x = .ok a ∧ g a = .ok b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

theorem throw_bind_ne {ε α β : Type} {e : ε} {g : α → Except ε β} {b : β} :
    ((throw e : Except ε α) >>= g) ≠ .ok b := nofun

/-- Invariant rule for a `forIn` over a list whose body never stops early. -/
theorem forIn_list_inv {ε α σ : Type} {xs : List α} {init r : σ}
    {body : α → σ → Except ε (ForInStep σ)} (I : List α → σ → Prop) (h0 : I [] init)
    (hstep : ∀ pre x s s', I pre s → body x s = .ok s' → ∃ t, s' = .yield t ∧ I (pre ++ [x]) t)
    (h : forIn xs init body = .ok r) : I xs r := by
  suffices ∀ suf pre s, I pre s → forIn suf s body = .ok r → I (pre ++ suf) r by
    simpa using this xs [] init h0 h
  intro suf
  induction suf with
  | nil =>
    intro pre s hI h
    simp only [List.forIn_nil, List.append_nil] at h ⊢
    cases h; exact hI
  | cons x suf ih =>
    intro pre s hI h
    rw [List.forIn_cons] at h
    obtain ⟨s', h1, h2⟩ := bind_ok h
    obtain ⟨t, rfl, ht⟩ := hstep pre x s s' hI h1
    simpa using ih (pre ++ [x]) t ht h2

theorem forIn_array_inv {ε α σ : Type} {xs : Array α} {init r : σ}
    {body : α → σ → Except ε (ForInStep σ)} (I : List α → σ → Prop) (h0 : I [] init)
    (hstep : ∀ pre x s s', I pre s → body x s = .ok s' → ∃ t, s' = .yield t ∧ I (pre ++ [x]) t)
    (h : forIn xs init body = .ok r) : I xs.toList r := by
  rw [← Array.forIn_toList] at h
  exact forIn_list_inv I h0 hstep h

/-- A `PUnit` loop over an array that succeeded: every element passed its body. -/
theorem forIn_array_unit {ε α : Type} {xs : Array α} {body : α → Unit → Except ε (ForInStep Unit)}
    {r : Unit} (P : α → Prop)
    (hb : ∀ x s, body x () = .ok s → P x ∧ s = .yield ())
    (h : forIn xs () body = .ok r) : ∀ x ∈ xs, P x := by
  have := forIn_array_inv (fun pre _ => ∀ x ∈ pre, P x) (by simp)
    (by
      intro pre x s s' hI hs
      obtain ⟨hP, rfl⟩ := hb x s' hs
      refine ⟨(), rfl, ?_⟩
      simp only [List.mem_append, List.mem_singleton]
      rintro y (hy | rfl) <;> simp_all) h
  intro x hx
  exact this x (by simpa using hx)

theorem forIn'_list_unit {ε α : Type} {xs : List α}
    {body : (a : α) → a ∈ xs → Unit → Except ε (ForInStep Unit)} {r : Unit} (P : α → Prop)
    (hb : ∀ x hx s, body x hx () = .ok s → P x ∧ s = .yield ())
    (h : forIn' xs () body = .ok r) : ∀ x ∈ xs, P x := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    rw [List.forIn'_cons] at h
    obtain ⟨s, h1, h2⟩ := bind_ok h
    obtain ⟨hP, rfl⟩ := hb a _ s h1
    have := ih (fun x hx s hs => hb x (List.mem_cons_of_mem a hx) s hs) h2
    intro x hx
    cases hx with
    | head => exact hP
    | tail _ hx => exact this x hx

theorem forIn'_range_unit {ε : Type} {n : Nat}
    {body : (i : Nat) → i ∈ [:n] → Unit → Except ε (ForInStep Unit)} {r : Unit} (P : Nat → Prop)
    (hb : ∀ i hi s, body i hi () = .ok s → P i ∧ s = .yield ())
    (h : forIn' [:n] () body = .ok r) : ∀ i < n, P i := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at h
  have := forIn'_list_unit P (fun x hx s hs => hb x _ s hs) h
  intro i hi
  exact this i (by simp [Std.Legacy.Range.size, List.mem_range'_1]; omega)


theorem ite_ok {ε α : Type} {c : Prop} [Decidable c] {A B : Except ε α} {b : α}
    (h : (if c then A else B) = .ok b) (hA : ∀ b, A ≠ .ok b) : ¬c ∧ B = .ok b := by
  split at h
  · exact absurd h (hA b)
  · exact ⟨‹_›, h⟩

theorem ite_bind_ok {ε α : Type} {c : Prop} [Decidable c] {A : Except ε Unit}
    {g : Unit → Except ε α} {b : α}
    (h : (if c then A >>= g else g ()) = .ok b) : g () = .ok b := by
  split at h
  · obtain ⟨⟨⟩, -, h⟩ := bind_ok h; exact h
  · exact h

theorem checkValue_ok {e : CheckEnv} {f : Func} {b : Block} {v : Value}
    (h : checkValue e f b v = .ok ()) :
    (v.op.argLen ≠ -1 → (v.args.size : Int) = v.op.argLen) ∧ checkAux e v = .ok () ∧
      v.block = b.id ∧ (v.op = .Phi → v.args.size = b.preds.size) := by
  unfold checkValue at h
  obtain ⟨h1, h⟩ := ite_ok h (fun _ => throw_bind_ne)
  obtain ⟨⟨⟩, h2, h⟩ := bind_ok h
  have h := ite_bind_ok h
  obtain ⟨h3, h⟩ := ite_ok h (fun _ => throw_bind_ne)
  obtain ⟨h4, h⟩ := ite_ok h (fun _ => throw_bind_ne)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_and, Decidable.not_not]
    at h1 h3 h4
  exact ⟨h1, h2, h3, h4⟩


theorem checkAux_bool {e : CheckEnv} {v : Value} (h : checkAux e v = .ok ())
    (hb : v.op.auxType = .Bool) : 0 ≤ v.auxInt.toInt ∧ v.auxInt.toInt ≤ 1 := by
  unfold checkAux at h
  rw [hb] at h
  obtain ⟨h2, -⟩ := ite_ok h (fun _ => throw_bind_ne)
  simpa [Bool.and_eq_true, decide_eq_true_eq] using h2


theorem getElem!_bool (a : Array Bool) (i : Nat) : a[i]! = a[i]?.getD false := by
  by_cases h : i < a.size <;> simp [h]

theorem getD_set! (a : Array Bool) (i j : Nat) (x : Bool) (hi : i < a.size) :
    (a.set! i x)[j]?.getD false = if i = j then x else a[j]?.getD false := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h; simp [hi]
  · simp [h]

theorem getD_replicate (n x : Nat) : (Array.replicate n false)[x]?.getD false = false := by
  rw [Array.getElem?_replicate]; split <;> rfl

theorem lt_of_block? {f : Func} {bid : ID} {b : Block} (h : f.block? bid = some b) :
    bid < f.blockTab.size := by
  unfold Func.block? at h
  rcases Nat.lt_or_ge bid f.blockTab.size with hlt | hge
  · exact hlt
  · simp [Array.getElem?_eq_none hge] at h

theorem lt_of_value? {f : Func} {vid : ID} {v : Value} (h : f.value? vid = some v) :
    vid < f.valueTab.size := by
  unfold Func.value? at h
  rcases Nat.lt_or_ge vid f.valueTab.size with hlt | hge
  · exact hlt
  · simp [Array.getElem?_eq_none hge] at h

/-- What the first loop of `check` establishes for listed block `bid` with table entry `b`. -/
def BlockFacts (ce : CheckEnv) (f : Func) (bid : ID) (b : Block) : Prop :=
  b.id = bid ∧
    (∀ i (e : Edge), b.preds[i]? = some e →
      ∃ p, f.block? e.b = some p ∧ p.succs[e.i]? = some ⟨bid, i⟩) ∧
    (∀ j (e : Edge), b.succs[j]? = some e →
      ∃ c, f.block? e.b = some c ∧ c.preds[e.i]? = some ⟨bid, j⟩) ∧
    (∀ vid ∈ b.values, ∃ v, f.value? vid = some v ∧ v.id = vid ∧ checkValue ce f b v = .ok ()) ∧
    b.values.toList.Nodup

/-- Listed block `bid` is in the table and passed the first loop's checks. -/
def BlockOK (ce : CheckEnv) (f : Func) (bid : ID) : Prop :=
  ∃ b, f.block? bid = some b ∧ BlockFacts ce f bid b

/-- Invariant of the first (block) loop of `check`, after the listed blocks `pre`. -/
def Loop1 (ce : CheckEnv) (f : Func) (pre : List ID) (st : Array Bool × Array Bool) : Prop :=
  st.1.size = f.blockTab.size ∧ st.2.size = f.valueTab.size ∧ pre.Nodup ∧
    (∀ bid ∈ pre, BlockOK ce f bid) ∧ (∀ x, st.1[x]?.getD false = true ↔ x ∈ pre) ∧
    (∀ x, st.2[x]?.getD false = true ↔ ∃ bid ∈ pre, ∃ b, f.block? bid = some b ∧ x ∈ b.values) ∧
    (∀ bid1 ∈ pre, ∀ bid2 ∈ pre, ∀ b1 b2, f.block? bid1 = some b1 → f.block? bid2 = some b2 →
      ∀ vid ∈ b1.values, vid ∈ b2.values → bid1 = bid2)

/-- Invariant of the value loop of block `b` (entry marks `vm0`), after the listed values `pre`. -/
def Loop2 (ce : CheckEnv) (f : Func) (b : Block) (vm0 : Array Bool) (pre : List ID)
    (vm : Array Bool) : Prop :=
  vm.size = f.valueTab.size ∧ pre.Nodup ∧
    (∀ vid ∈ pre, ∃ v, f.value? vid = some v ∧ v.id = vid ∧ checkValue ce f b v = .ok ()) ∧
    (∀ x, vm[x]?.getD false = true ↔ vm0[x]?.getD false = true ∨ x ∈ pre) ∧
    (∀ x ∈ pre, vm0[x]?.getD false = false)

/-- Index facts proved for in-bounds indices hold for every `xs[i]? = some a`. -/
theorem idx {α : Type} {xs : Array α} {P : Nat → α → Prop}
    (h : ∀ i, i < xs.size → ∀ a, xs[i]? = some a → P i a) :
    ∀ i a, xs[i]? = some a → P i a := by
  intro i a ha
  rcases Nat.lt_or_ge i xs.size with hl | hl
  · exact h i hl a ha
  · simp [Array.getElem?_eq_none hl] at ha

end CheckFacts

open CheckFacts in
/-- A passing Go check (`checkGo`) establishes the well-formedness facts `WF`. -/
theorem checkGo_wf {ce : CheckEnv} {f : Func} (h : checkGo ce f = .ok ()) : WF ce f := by
  unfold checkGo at h
  obtain ⟨⟨bm, vm⟩, h1, h⟩ := bind_ok h
  have I1 := forIn_array_inv (Loop1 ce f) ?init ?step h1
  case init =>
    refine ⟨by simp, by simp, List.nodup_nil, by simp, ?_, ?_, by simp⟩ <;>
      intro x <;> simp [getD_replicate]
  case step =>
    rintro pre bid ⟨bm, vm⟩ s' ⟨hbs, hvs, hnd, hok, hbm, hvm, hon⟩ hs
    dsimp only at hbs hvs hbm hvm
    cases hb : f.block? bid with
    | none => rw [hb] at hs; exact absurd hs throw_bind_ne
    | some b =>
    rw [hb] at hs
    obtain ⟨hid, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
    obtain ⟨hmark, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
    obtain ⟨⟨⟩, hpred, hs⟩ := bind_ok hs
    obtain ⟨⟨⟩, hsucc, hs⟩ := bind_ok hs
    obtain ⟨⟨⟩, -, hs⟩ := bind_ok hs
    obtain ⟨vm', hval, hs⟩ := bind_ok hs
    cases Except.ok.inj hs
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hid
    rw [getElem!_bool, Bool.not_eq_true] at hmark
    have hP := forIn'_range_unit (fun i => ∀ e : Edge, b.preds[i]? = some e →
        ∃ p, f.block? e.b = some p ∧ p.succs[e.i]? = some ⟨bid, i⟩) ?_ hpred
    rotate_left
    · intro i hi s hs
      have hlt := hi.upper
      dsimp only at hs
      split at hs
      · rename_i se hse
        obtain ⟨hc, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
        refine ⟨?_, (Except.ok.inj hs).symm⟩
        intro e he
        rw [Array.getElem?_eq_getElem hlt] at he
        cases Option.some.inj he
        obtain ⟨p, hp, hps⟩ := Option.bind_eq_some_iff.1 hse
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hc
        obtain ⟨h1, h2⟩ := hc
        refine ⟨p, hp, ?_⟩
        rw [hps, ← h1, ← h2]
      · exact absurd hs throw_bind_ne
    have hS := forIn'_range_unit (fun i => ∀ e : Edge, b.succs[i]? = some e →
        ∃ c, f.block? e.b = some c ∧ c.preds[e.i]? = some ⟨bid, i⟩) ?_ hsucc
    rotate_left
    · intro i hi s hs
      have hlt := hi.upper
      dsimp only at hs
      split at hs
      · rename_i se hse
        obtain ⟨hc, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
        refine ⟨?_, (Except.ok.inj hs).symm⟩
        intro e he
        rw [Array.getElem?_eq_getElem hlt] at he
        cases Option.some.inj he
        obtain ⟨p, hp, hps⟩ := Option.bind_eq_some_iff.1 hse
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hc
        obtain ⟨h1, h2⟩ := hc
        refine ⟨p, hp, ?_⟩
        rw [hps, ← h1, ← h2]
      · exact absurd hs throw_bind_ne
    have I2 := forIn_array_inv (Loop2 ce f b vm) ?i2 ?s2 hval
    rotate_left
    · exact ⟨hvs, List.nodup_nil, by simp, by simp, by simp⟩
    · rintro pre2 vid vm2 s2 ⟨hs2, hnd2, hok2, hm2, hz2⟩ hs
      dsimp only at hs
      cases hv : f.value? vid with
      | none => rw [hv] at hs; exact absurd hs throw_bind_ne
      | some v =>
      rw [hv] at hs
      obtain ⟨hvid, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
      obtain ⟨⟨⟩, hcv, hs⟩ := bind_ok hs
      obtain ⟨hvm, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
      cases Except.ok.inj hs
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hvid
      rw [getElem!_bool, Bool.not_eq_true] at hvm
      have hlt : vid < vm2.size := hs2 ▸ lt_of_value? hv
      have hnot : vid ∉ pre2 := fun hm => by
        have := (hm2 vid).2 (Or.inr hm); rw [hvm] at this; exact absurd this nofun
      refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hs2]
      · exact List.nodup_append.2 ⟨hnd2, by simp,
          fun a ha c hc h => by simp at hc; subst hc; subst h; exact hnot ha⟩
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hok2 x hx
        · exact ⟨v, hv, hvid, hcv⟩
      · intro x
        rw [getD_set! _ _ _ _ hlt, List.mem_append, List.mem_singleton]
        by_cases hx : vid = x
        · subst hx; simp
        · simp only [hx, ↓reduceIte]; rw [hm2]; simp [Ne.symm hx]
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hz2 x hx
        · cases h0 : vm[x]?.getD false
          · rfl
          · have := (hm2 x).2 (Or.inl h0); rw [hvm] at this; exact absurd this nofun
    obtain ⟨hs2, hnd2, hok2, hm2, hz2⟩ := I2
    have hlt : bid < bm.size := hbs ▸ lt_of_block? hb
    have hnot : bid ∉ pre := fun hm => by
      have := (hbm bid).2 hm; rw [hmark] at this; exact absurd this nofun
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hbs]
    · exact hs2
    · exact List.nodup_append.2 ⟨hnd, by simp,
          fun a ha c hc h => by simp at hc; subst hc; subst h; exact hnot ha⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hok x hx
      · exact ⟨b, hb, hid, idx hP, idx hS, fun vid hv => hok2 vid (by simpa using hv), hnd2⟩
    · intro x
      rw [getD_set! _ _ _ _ hlt, List.mem_append, List.mem_singleton]
      by_cases hx : bid = x
      · subst hx; simp
      · simp only [hx, ↓reduceIte]; rw [hbm]; simp [Ne.symm hx]
    · intro x
      rw [hm2, hvm]
      constructor
      · rintro (⟨bid', hm, b', hb', hx⟩ | hx)
        · exact ⟨bid', by simp [hm], b', hb', hx⟩
        · exact ⟨bid, by simp, b, hb, by simpa using hx⟩
      · rintro ⟨bid', hm, b', hb', hx⟩
        simp only [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact Or.inl ⟨bid', hm, b', hb', hx⟩
        · rw [hb] at hb'; cases hb'; exact Or.inr (by simpa using hx)
    · have cross : ∀ bid1 ∈ pre, ∀ b1, f.block? bid1 = some b1 → ∀ vid ∈ b1.values,
          vid ∈ b.values → False := by
        intro bid1 h1 b1 hb1 vid hv1 hv2
        have := (hvm vid).2 ⟨bid1, h1, b1, hb1, hv1⟩
        rw [hz2 vid (by simpa using hv2)] at this
        exact absurd this nofun
      intro bid1 h1 bid2 h2 b1 b2 hb1 hb2 vid hv1 hv2
      simp only [List.mem_append, List.mem_singleton] at h1 h2
      rcases h1 with h1 | rfl <;> rcases h2 with h2 | rfl
      · exact hon bid1 h1 bid2 h2 b1 b2 hb1 hb2 vid hv1 hv2
      · rw [hb] at hb2; cases hb2; exact (cross bid1 h1 b1 hb1 vid hv1 hv2).elim
      · rw [hb] at hb1; cases hb1; exact (cross bid2 h2 b2 hb2 vid hv2 hv1).elim
      · rfl
  obtain ⟨-, -, hnd, hok, hbm, hvm, hon⟩ := I1
  obtain ⟨hentry, h⟩ := ite_ok h (fun _ => throw_bind_ne)
  obtain ⟨⟨⟩, hps, h⟩ := bind_ok h
  obtain ⟨hep, h⟩ := ite_ok h (fun _ => throw_bind_ne)
  obtain ⟨⟨⟩, hmiss, -⟩ := bind_ok h
  have hps := forIn_array_unit (fun b : Block =>
      (∀ c ∈ b.preds, bm[c.b]?.getD false = true) ∧ (∀ c ∈ b.succs, bm[c.b]?.getD false = true))
    ?_ hps
  rotate_left
  · intro x s hs
    obtain ⟨⟨⟩, h1, hs⟩ := bind_ok hs
    obtain ⟨⟨⟩, h2, hs⟩ := bind_ok hs
    cases Except.ok.inj hs
    refine ⟨⟨forIn_array_unit _ ?_ h1, forIn_array_unit _ ?_ h2⟩, rfl⟩ <;>
    · intro c s hs
      obtain ⟨hc, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
      exact ⟨by simpa using hc, (Except.ok.inj hs).symm⟩
  have hmiss := forIn_array_unit (fun b : Block =>
      (∀ vid ∈ b.values, ∀ v, f.value? vid = some v → ∀ a ∈ v.args, vm[a]?.getD false = true) ∧
        (∀ c ∈ b.controls, vm[c]?.getD false = true))
    ?_ hmiss
  rotate_left
  · intro x s hs
    obtain ⟨⟨⟩, h1, hs⟩ := bind_ok hs
    obtain ⟨⟨⟩, h2, hs⟩ := bind_ok hs
    cases Except.ok.inj hs
    refine ⟨⟨forIn_array_unit _ ?_ h1, forIn_array_unit _ ?_ h2⟩, rfl⟩
    · intro vid s hs
      split at hs
      · rename_i v hv
        obtain ⟨⟨⟩, h3, hs⟩ := bind_ok hs
        cases Except.ok.inj hs
        refine ⟨?_, rfl⟩
        intro v' hv' a ha
        rw [hv] at hv'; cases hv'
        have := forIn'_range_unit (fun i => ∀ a, v.args[i]? = some a → vm[a]?.getD false = true)
          ?_ h3
        · obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 ha
          exact idx this i a hi
        · intro i hi s hs
          obtain ⟨hc, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
          refine ⟨?_, (Except.ok.inj hs).symm⟩
          intro a ha
          rw [Array.getElem?_eq_getElem hi.upper] at ha
          cases Option.some.inj ha
          simpa using hc
      · rename_i hnone
        cases Except.ok.inj hs
        exact ⟨fun v hv => absurd hv (hnone v), rfl⟩
    · intro c s hs
      obtain ⟨hc, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
      exact ⟨by simpa using hc, (Except.ok.inj hs).symm⟩
  have inBlocks : ∀ bid b, BlockIn f bid b → b ∈ f.blocks.filterMap f.block? := by
    rintro bid b ⟨hm, hb⟩
    exact Array.mem_filterMap.2 ⟨bid, hm, hb⟩
  have ok' : ∀ bid b, BlockIn f bid b → BlockFacts ce f bid b := by
    rintro bid b ⟨hm, hb⟩
    obtain ⟨b', hb', h'⟩ := hok bid (by simpa using hm)
    rw [hb] at hb'; cases hb'; exact h'
  have val : ∀ bid b vid v, ValueIn f bid b vid v → checkValue ce f b v = .ok () := by
    rintro bid b vid v ⟨hin, hv, hval⟩
    obtain ⟨v', hv', -, hc⟩ := (ok' bid b hin).2.2.2.1 vid hv
    rw [hval] at hv'; cases hv'; exact hc
  have listed : ∀ a, vm[a]?.getD false = true → Listed f a := by
    intro a ha
    obtain ⟨bid, hm, b, hb, hx⟩ := (hvm a).1 ha
    exact ⟨bid, b, ⟨by simpa using hm, hb⟩, hx⟩
  have blk : ∀ x, bm[x]?.getD false = true → x ∈ f.blocks := fun x hx => by
    simpa using (hbm x).1 hx
  refine
    { blockId := ?_, blocksNodup := hnd, valueId := ?_, valuesNodup := ?_, valueOnce := ?_,
      predLink := ?_, succLink := ?_, arity := ?_, phiArity := ?_, boolAux := ?_,
      argListed := ?_, ctrlListed := ?_, entry := ?_, entryPreds := ?_ }
  · intro bid hm
    obtain ⟨b, hb, hid, -⟩ := hok bid (by simpa using hm)
    exact ⟨b, hb, hid⟩
  · intro bid b hin vid hv
    obtain ⟨hid, -, -, hV, -⟩ := ok' bid b hin
    obtain ⟨v, hv', hvid, hc⟩ := hV vid hv
    exact ⟨v, hv', hvid, (checkValue_ok hc).2.2.1.trans hid⟩
  · intro bid b hin
    exact (ok' bid b hin).2.2.2.2
  · rintro bid1 b1 bid2 b2 ⟨hm1, hb1⟩ ⟨hm2, hb2⟩ vid hv1 hv2
    exact hon bid1 (by simpa using hm1) bid2 (by simpa using hm2) b1 b2 hb1 hb2 vid hv1 hv2
  · intro bid b hin i e he
    exact ⟨blk _ ((hps b (inBlocks bid b hin)).1 e (Array.mem_of_getElem? he)),
      (ok' bid b hin).2.1 i e he⟩
  · intro bid b hin j e he
    exact ⟨blk _ ((hps b (inBlocks bid b hin)).2 e (Array.mem_of_getElem? he)),
      (ok' bid b hin).2.2.1 j e he⟩
  · intro bid b vid v hin
    exact (checkValue_ok (val bid b vid v hin)).1
  · intro bid b vid v hin
    exact (checkValue_ok (val bid b vid v hin)).2.2.2
  · intro bid b vid v hin
    exact checkAux_bool (checkValue_ok (val bid b vid v hin)).2.1
  · rintro bid b vid v ⟨hin, hv, hval⟩ a ha
    exact listed a ((hmiss b (inBlocks bid b hin)).1 vid hv v hval a ha)
  · intro bid b hin c hc
    exact listed c ((hmiss b (inBlocks bid b hin)).2 c hc)
  · exact blk _ (by simpa using hentry)
  · intro b hb
    rw [hb] at hep
    simpa using hep

open CheckFacts in
/-- A passing `check` establishes the well-formedness facts `WF`. -/
theorem check_wf {ce : CheckEnv} {f : Func} (h : check ce f = .ok ()) : WF ce f := by
  unfold check at h
  obtain ⟨⟨⟩, h1, -⟩ := bind_ok h
  exact checkGo_wf h1

open CheckFacts in
/-- A passing `check` has validated the dominator certificate. -/
theorem check_domCert {ce : CheckEnv} {f : Func} (h : check ce f = .ok ()) :
    DomCert.check f = .ok () := by
  unfold check at h
  obtain ⟨⟨⟩, -, h2⟩ := bind_ok h
  exact h2

end GoFV.Proof
