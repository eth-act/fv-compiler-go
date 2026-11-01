import GoFV.Proof.Pass.CopyElimChase

/-!
# `phielimSweep` and `phielim` keep `Inv`

One value of a sweep (`step_value`): the zero-size reset, `copyelimValue`, `phielimValue`. A
sweep (`sweep_spec`) keeps `Inv`, lowers the phi count when a phi changed, and when none did,
leaves every argument of every listed value a non-copy. `phielim` (`phielim_spec`) ends with a
sweep that changed nothing: the loop bound `vid.last + 2` exceeds the number of phis.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.Opt GoFV.Proof

/-- Invariant rule for a `forIn` over a list that may stop early (`D`: the state it stops in). -/
theorem forIn_list_inv' {ε α σ : Type} {xs : List α} {init r : σ}
    {body : α → σ → Except ε (ForInStep σ)} (I : List α → σ → Prop) (D : σ → Prop)
    (h0 : I [] init)
    (hstep : ∀ pre x suf s s', pre ++ x :: suf = xs → I pre s → body x s = .ok s' →
      (∃ t, s' = .yield t ∧ I (pre ++ [x]) t) ∨ (∃ t, s' = .done t ∧ D t))
    (h : forIn xs init body = .ok r) : I xs r ∨ D r := by
  suffices ∀ suf pre s, pre ++ suf = xs → I pre s → forIn suf s body = .ok r → I xs r ∨ D r from
    this xs [] init rfl h0 h
  intro suf
  induction suf with
  | nil =>
    intro pre s hp hI h
    simp only [List.forIn_nil, List.append_nil] at h hp
    cases h; subst hp; exact .inl hI
  | cons x suf ih =>
    intro pre s hp hI h
    rw [List.forIn_cons] at h
    obtain ⟨s', h1, h2⟩ := CheckFacts.bind_ok h
    rcases hstep pre x suf s s' hp hI h1 with ⟨t, rfl, ht⟩ | ⟨t, rfl, ht⟩
    · exact ih (pre ++ [x]) t (by simp [← hp]) ht h2
    · cases h2; exact .inr ht

theorem forIn_array_inv' {ε α σ : Type} {xs : Array α} {init r : σ}
    {body : α → σ → Except ε (ForInStep σ)} (I : List α → σ → Prop) (h0 : I [] init)
    (hstep : ∀ pre x suf s s', pre ++ x :: suf = xs.toList → I pre s → body x s = .ok s' →
      ∃ t, s' = .yield t ∧ I (pre ++ [x]) t)
    (h : forIn xs init body = .ok r) : I xs.toList r := by
  rw [← Array.forIn_toList] at h
  have := forIn_list_inv' I (fun _ => False) h0
    (fun pre x suf s s' hp hI hb => .inl (hstep pre x suf s s' hp hI hb)) h
  exact this.resolve_right id

section
variable {tabs : Tables} {ce : CheckEnv} {f F : Func}

/-- The arguments of all listed values are non-copies. -/
def Settled (f : Func) (V : ID → Option Value) : Prop :=
  ∀ x, Listed f x → ∀ u, V x = some u → ∀ c ∈ u.args, cstep V c = none

/-- After the zero-size step (`F1`), `copyelimValue` and `phielimValue`. -/
theorem step_core (hwf : WF ce f) (hfrag : CopyFrag tabs f) {F1 : Func} {v : ID}
    (hv : Listed f v) {fv : Value} (hfv : f.value? v = some fv) (hI1 : Inv tabs f F1)
    (hpr : Prsv (vw F) (vw F1))
    (hphi : ∀ x, (vw F1 x).any (·.op == .Phi) = true → (vw F x).any (·.op == .Phi) = true)
    (hemp : zeroSize tabs fv.type → (vw F1 v).map (·.op) = some .Empty) :
    Inv tabs f ((copyelimValue F1 v).phielimValue v).1 ∧
      AllSink (vw ((copyelimValue F1 v).phielimValue v).1) [v] ∧
      (((copyelimValue F1 v).phielimValue v).2 = false →
        Prsv (vw F) (vw ((copyelimValue F1 v).phielimValue v).1)) ∧
      phiN (vw ((copyelimValue F1 v).phielimValue v).1) f.valueTab.size +
          (if ((copyelimValue F1 v).phielimValue v).2 then 1 else 0) ≤
        phiN (vw F) f.valueTab.size := by
  obtain ⟨hI2, hpr2, hphi2, hops2, hs2⟩ := copyelimValue_spec hwf hfrag hI1 hv
  generalize copyelimValue F1 v = F2 at hI2 hpr2 hphi2 hops2 hs2 ⊢
  have hle2 : phiN (vw F2) f.valueTab.size ≤ phiN (vw F) f.valueTab.size :=
    phiN_le fun x hx => hphi x (hphi2 x hx)
  by_cases hz : zeroSize tabs fv.type
  · have hop : (F2.getV v).op = .Empty := by
      have h1 := (hops2 v).trans (hemp hz)
      cases h : vw F2 v with
      | none => rw [h] at h1; cases h1
      | some u =>
        rw [h, Option.map_some] at h1
        rw [(getV_of_vw h).1]; exact Option.some.inj h1
    have hp : F2.phielimValue v = (F2, false) := by
      rcases phielimValue_cases F2 v with h | ⟨w, hphi', -⟩
      · exact h
      · rw [hop] at hphi'; cases hphi'
    rw [hp]
    exact ⟨hI2, hs2, fun _ => hpr.trans hpr2, by simpa using hle2⟩
  · obtain ⟨hI3, hs3, hsame, hphi3, hstrict⟩ := inv_phielim hwf hfrag hI2 hv hfv hz hs2
    refine ⟨hI3, hs3, fun h => by rw [hsame h]; exact hpr.trans hpr2, ?_⟩
    cases hc : (F2.phielimValue v).2 with
    | false => rw [hsame hc]; simpa using hle2
    | true =>
      obtain ⟨h1, h2⟩ := hstrict hc
      have := phiN_lt (N := f.valueTab.size) hphi3 (CheckFacts.lt_of_value? hfv) h1 h2
      simp only [ite_true]
      omega

theorem type_getV (hI : Inv tabs f F) (hwf : WF ce f) {v : ID} (hv : Listed f v) {fv : Value}
    (hfv : f.value? v = some fv) : (F.getV v).type = fv.type := by
  obtain ⟨fv', u, hfv', hu, -⟩ := hI.value hwf hv
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨fv'', h1, -, h3⟩ := hI.keep_some hu
  rw [hfv] at h1; cases h1
  rw [(getV_of_vw hu).2.2, h3]

/-- One value of a sweep. -/
theorem step_value (hwf : WF ce f) (hfrag : CopyFrag tabs f) (hI : Inv tabs f F) {v : ID}
    (hv : Listed f v) {z : Bool} (hz : zeroSizeAggregate tabs (F.getV v).type = .ok z)
    {F1 : Func} (hF1 : F1 = if z = true then F.resetValue v .Empty else F) :
    Inv tabs f ((copyelimValue F1 v).phielimValue v).1 ∧
      AllSink (vw ((copyelimValue F1 v).phielimValue v).1) [v] ∧
      (((copyelimValue F1 v).phielimValue v).2 = false →
        Prsv (vw F) (vw ((copyelimValue F1 v).phielimValue v).1)) ∧
      phiN (vw ((copyelimValue F1 v).phielimValue v).1) f.valueTab.size +
          (if ((copyelimValue F1 v).phielimValue v).2 then 1 else 0) ≤
        phiN (vw F) f.valueTab.size := by
  obtain ⟨fv, hfv⟩ := listed_value hwf hv
  rw [type_getV hI hwf hv hfv] at hz
  cases z with
  | true =>
    simp only [ite_true] at hF1
    subst hF1
    obtain ⟨hI1, hpr, hphi⟩ := inv_empty hfrag hI hv hfv hz
    refine step_core hwf hfrag hv hfv hI1 hpr hphi fun _ => ?_
    rw [vw_resetValue, upd_self, Option.map_map]
    obtain ⟨u, hu, -⟩ := hI.mode v hv fv hfv
    rw [hu]; rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hF1
    subst hF1
    refine step_core hwf hfrag hv hfv hI (Prsv.refl _) (fun _ => id) fun h => ?_
    unfold zeroSize at h
    rw [hz] at h; cases h

/-- The sweep invariant over the processed values `xs`. -/
def SweepInv (tabs : Tables) (f F : Func) (xs : List ID) (s : Func × Bool) : Prop :=
  Inv tabs f s.1 ∧ phiN (vw s.1) f.valueTab.size + (if s.2 then 1 else 0) ≤ phiN (vw F) f.valueTab.size ∧
    (s.2 = false → AllSink (vw s.1) xs ∧ Prsv (vw F) (vw s.1))

theorem sweepInv_step {xs : List ID} {s : Func × Bool} {v : ID} {G : Func} {c : Bool}
    (hS : SweepInv tabs f F xs s)
    (h : Inv tabs f G ∧ AllSink (vw G) [v] ∧ (c = false → Prsv (vw s.1) (vw G)) ∧
      phiN (vw G) f.valueTab.size + (if c then 1 else 0) ≤ phiN (vw s.1) f.valueTab.size) :
    SweepInv tabs f F (xs ++ [v]) (G, c || s.2) := by
  obtain ⟨hI, hcnt, hset⟩ := hS
  obtain ⟨hI', hs', hpr', hcnt'⟩ := h
  refine ⟨hI', ?_, fun hc => ?_⟩
  · dsimp only
    have : (if (c || s.2) = true then 1 else 0) ≤
        (if c = true then 1 else 0) + (if s.2 = true then 1 else 0) := by
      cases c <;> cases s.2 <;> simp
    omega
  · simp only [Bool.or_eq_false_iff] at hc
    obtain ⟨hall, hpr⟩ := hset hc.2
    have hpr2 := hpr' hc.1
    exact ⟨(hall.prsv hpr2).append hs', hpr.trans hpr2⟩

theorem getB_of_inv (hI : Inv tabs f F) (b : ID) : F.getB b = f.getB b := by
  have := hI.skel
  simp only [CopyElim.skel, Prod.mk.injEq] at this
  unfold Func.getB Func.block?
  rw [this.2.2.2.1]

/-- The values of the listed blocks `bs`. -/
def valuesOf (f : Func) (bs : List ID) : List ID := (bs.map fun b => (f.getB b).values.toList).flatten

theorem sweep_spec (hwf : WF ce f) (hfrag : CopyFrag tabs f) (hI : Inv tabs f F) {G : Func}
    {c : Bool} (h : phielimSweep tabs F = .ok (G, c)) :
    Inv tabs f G ∧ phiN (vw G) f.valueTab.size + (if c then 1 else 0) ≤ phiN (vw F) f.valueTab.size ∧
      (c = false → Settled f (vw G)) := by
  have hsk := hI.skel
  simp only [CopyElim.skel, Prod.mk.injEq] at hsk
  unfold phielimSweep at h
  obtain ⟨s, h1, h2⟩ := CheckFacts.bind_ok h
  have hout := forIn_array_inv' (fun pre s => SweepInv tabs f F (valuesOf f pre) s)
    ⟨hI, by simp, fun _ => ⟨by simp [valuesOf, AllSink], Prsv.refl _⟩⟩ ?_ h1
  · cases h2
    obtain ⟨hIs, hcnt, hset⟩ := hout
    refine ⟨hIs, hcnt, fun hc => ?_⟩
    obtain ⟨hall, -⟩ := hset hc
    rintro x ⟨bid, b, ⟨hm, hb⟩, hxb⟩
    rw [← hsk.2.2.1] at hm
    refine hall x ?_
    simp only [valuesOf, List.mem_flatten, List.mem_map]
    refine ⟨_, ⟨bid, Array.mem_toList_iff.2 hm, rfl⟩, ?_⟩
    unfold Func.getB; rw [hb]; simpa using hxb
  intro pre b suf s s' hpb hS hb
  have hbm : b ∈ F.blocks := Array.mem_toList_iff.1 (by rw [← hpb]; simp)
  obtain ⟨s2, h3, h4⟩ := CheckFacts.bind_ok hb
  cases h4
  refine ⟨(s2.1, s2.2), rfl, ?_⟩
  have hin := forIn_array_inv'
    (fun pre' s => SweepInv tabs f F (valuesOf f pre ++ pre') s) (by simpa using hS) ?_ h3
  · rw [getB_of_inv hS.1] at hin
    simpa [valuesOf] using hin
  intro pre' v suf' t t' hpv hT hv
  have hvl : Listed f v := by
    rw [getB_of_inv hS.1] at hpv
    rw [hsk.2.2.1] at hbm
    obtain ⟨blk, hblk, -⟩ := hwf.blockId b hbm
    refine ⟨b, blk, ⟨hbm, hblk⟩, ?_⟩
    have : v ∈ (f.getB b).values.toList := by rw [← hpv]; simp
    unfold Func.getB at this; rw [hblk] at this; simpa using this
  obtain ⟨z, hz, h5⟩ := CheckFacts.bind_ok hv
  split at h5
  · simp only at h5; cases h5
    exact ⟨_, rfl, List.append_assoc .. ▸ sweepInv_step hT
      (step_value hwf hfrag hT.1 hvl hz (F1 := t.1.resetValue v .Empty) (by simp [*]))⟩
  · simp only at h5; cases h5
    exact ⟨_, rfl, List.append_assoc .. ▸ sweepInv_step hT (step_value hwf hfrag hT.1 hvl hz (F1 := t.1) (by simp [*]))⟩

theorem phiN_le_size (V : ID → Option Value) (N : Nat) : phiN V N ≤ N := by
  unfold phiN
  have := List.countP_le_length (p := fun x => (V x).any (·.op == .Phi)) (l := List.range N)
  simpa using this

/-- `phielim` ends after a sweep that changed nothing: `Inv` holds and every argument of a
listed value is a non-copy. -/
theorem phielim_spec (hwf : WF ce f) (hfrag : CopyFrag tabs f) {G : Func}
    (h : phielim tabs f = .ok G) : Inv tabs f G ∧ Settled f (vw G) := by
  unfold phielim at h
  obtain ⟨s, h1, h2⟩ := CheckFacts.bind_ok h
  cases h2
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h1
  have hres := forIn_list_inv'
    (fun pre G => Inv tabs f G ∧ phiN (vw G) f.valueTab.size + pre.length ≤ phiN (vw f) f.valueTab.size)
    (fun G => Inv tabs f G ∧ Settled f (vw G)) ⟨inv_init hwf hfrag, by simp⟩ ?_ h1
  · rcases hres with ⟨-, hcnt⟩ | hD
    · have := phiN_le_size (vw f) f.valueTab.size
      have := hfrag.size
      simp [Std.Legacy.Range.size] at hcnt
      omega
    · exact hD
  intro pre x suf t t' _ hT hb
  obtain ⟨⟨G', c⟩, hsw, h3⟩ := CheckFacts.bind_ok hb
  obtain ⟨hI', hcnt', hset'⟩ := sweep_spec hwf hfrag hT.1 hsw
  simp only at h3
  split at h3
  · cases h3
    rename_i hc
    simp only [Bool.not_eq_true'] at hc
    exact .inr ⟨_, rfl, hI', hset' hc⟩
  · cases h3
    rename_i hc
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
    refine .inl ⟨_, rfl, hI', ?_⟩
    rw [hc] at hcnt'
    simp only [ite_true, List.length_append, List.length_singleton] at hcnt' ⊢
    omega

end

end GoFV.Proof.CopyElim
