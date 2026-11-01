import GoFV.Proof.CheckFacts
import GoFV.SSA.WFCheck

/-!
# The slim input check establishes `WF` (issue #147)

`wfCheck_wf`: a passing `wfCheck f` gives `WF ce f` (for any `ce`: `WF` reads no tables);
`wfDomCheck_wf`/`wfDomCheck_domCert`: a passing `wfDomCheck f` gives `WF ce f` and a passing
dominator certificate. The proof follows `checkGo_wf`: the block loop with the invariant
`Loop1`, its value loop with `Loop2`, the listing loop read off pointwise; `valueOK_spec` gives
the op-shape facts of one value.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.WFCheck CheckFacts

namespace WFCheckFacts

theorem valueOK_spec {b : Block} {v : Value} (h : valueOK b v = true) :
    (v.op.argLen ≠ -1 → (v.args.size : Int) = v.op.argLen) ∧
      (v.op.auxType = .Bool → 0 ≤ v.auxInt.toInt ∧ v.auxInt.toInt ≤ 1) ∧
      v.block = b.id ∧ (v.op = .Phi → v.args.size = b.preds.size) := by
  simp only [valueOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1.resolve_left, fun hb => h2.resolve_left (Decidable.not_not.2 hb), h3,
    fun hp => h4.resolve_left (Decidable.not_not.2 hp)⟩

/-- What the block loop of `wfCheck` establishes for listed block `bid` with table entry `b`. -/
def BlockFacts (f : Func) (bid : ID) (b : Block) : Prop :=
  b.id = bid ∧
    (∀ i (e : Edge), b.preds[i]? = some e →
      ∃ p, f.block? e.b = some p ∧ p.succs[e.i]? = some ⟨bid, i⟩) ∧
    (∀ j (e : Edge), b.succs[j]? = some e →
      ∃ c, f.block? e.b = some c ∧ c.preds[e.i]? = some ⟨bid, j⟩) ∧
    (∀ vid ∈ b.values, ∃ v, f.value? vid = some v ∧ v.id = vid ∧ valueOK b v = true) ∧
    b.values.toList.Nodup

/-- Listed block `bid` is in the table and passed the block loop's checks. -/
def BlockOK (f : Func) (bid : ID) : Prop :=
  ∃ b, f.block? bid = some b ∧ BlockFacts f bid b

/-- Invariant of the block loop of `wfCheck`, after the listed blocks `pre`. -/
def Loop1 (f : Func) (pre : List ID) (st : Array Bool × Array Bool) : Prop :=
  st.1.size = f.blockTab.size ∧ st.2.size = f.valueTab.size ∧ pre.Nodup ∧
    (∀ bid ∈ pre, BlockOK f bid) ∧ (∀ x, st.1[x]?.getD false = true ↔ x ∈ pre) ∧
    (∀ x, st.2[x]?.getD false = true ↔ ∃ bid ∈ pre, ∃ b, f.block? bid = some b ∧ x ∈ b.values) ∧
    (∀ bid1 ∈ pre, ∀ bid2 ∈ pre, ∀ b1 b2, f.block? bid1 = some b1 → f.block? bid2 = some b2 →
      ∀ vid ∈ b1.values, vid ∈ b2.values → bid1 = bid2)

/-- Invariant of the value loop of block `b` (entry marks `vm0`), after the listed values `pre`. -/
def Loop2 (f : Func) (b : Block) (vm0 : Array Bool) (pre : List ID) (vm : Array Bool) : Prop :=
  vm.size = f.valueTab.size ∧ pre.Nodup ∧
    (∀ vid ∈ pre, ∃ v, f.value? vid = some v ∧ v.id = vid ∧ valueOK b v = true) ∧
    (∀ x, vm[x]?.getD false = true ↔ vm0[x]?.getD false = true ∨ x ∈ pre) ∧
    (∀ x ∈ pre, vm0[x]?.getD false = false)

end WFCheckFacts

open WFCheckFacts in
/-- A passing `wfCheck` establishes the well-formedness facts `WF`. -/
theorem wfCheck_wf {ce : CheckEnv} {f : Func} (h : wfCheck f = .ok ()) : WF ce f := by
  unfold wfCheck at h
  obtain ⟨⟨bm, vm⟩, h1, h⟩ := bind_ok h
  have I1 := forIn_array_inv (Loop1 f) ?init ?step h1
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
    have I2 := forIn_array_inv (Loop2 f b vm) ?i2 ?s2 hval
    rotate_left
    · exact ⟨hvs, List.nodup_nil, by simp, by simp, by simp⟩
    · rintro pre2 vid vm2 s2 ⟨hs2, hnd2, hok2, hm2, hz2⟩ hs
      dsimp only at hs
      cases hv : f.value? vid with
      | none => rw [hv] at hs; exact absurd hs throw_bind_ne
      | some v =>
      rw [hv] at hs
      obtain ⟨hvid, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
      obtain ⟨hcv, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hcv
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
  obtain ⟨hep, h⟩ := ite_ok h (fun _ => throw_bind_ne)
  obtain ⟨⟨⟩, hmiss, -⟩ := bind_ok h
  have hmiss := forIn_array_unit (fun bid => ∀ b : Block, f.block? bid = some b →
      (∀ c ∈ b.preds, bm[c.b]?.getD false = true) ∧ (∀ c ∈ b.succs, bm[c.b]?.getD false = true) ∧
      (∀ vid ∈ b.values, ∀ v, f.value? vid = some v → ∀ a ∈ v.args, vm[a]?.getD false = true) ∧
      (∀ c ∈ b.controls, vm[c]?.getD false = true))
    ?_ hmiss
  rotate_left
  · intro x s hs
    split at hs
    · rename_i b' hb'
      obtain ⟨⟨⟩, h1, hs⟩ := bind_ok hs
      obtain ⟨⟨⟩, h2, hs⟩ := bind_ok hs
      obtain ⟨⟨⟩, h3, hs⟩ := bind_ok hs
      obtain ⟨⟨⟩, h4, hs⟩ := bind_ok hs
      cases Except.ok.inj hs
      refine ⟨fun b hb => ?_, rfl⟩
      rw [hb'] at hb; cases hb
      refine ⟨forIn_array_unit _ ?_ h1, forIn_array_unit _ ?_ h2, ?_, forIn_array_unit _ ?_ h4⟩
      · intro c s hs
        obtain ⟨hc, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
        exact ⟨by simpa using hc, (Except.ok.inj hs).symm⟩
      · intro c s hs
        obtain ⟨hc, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
        exact ⟨by simpa using hc, (Except.ok.inj hs).symm⟩
      · refine forIn_array_unit (fun vid => ∀ v, f.value? vid = some v → ∀ a ∈ v.args,
          vm[a]?.getD false = true) ?_ h3
        intro vid s hs
        split at hs
        · rename_i v hv
          obtain ⟨⟨⟩, h5, hs⟩ := bind_ok hs
          cases Except.ok.inj hs
          refine ⟨fun v' hv' => ?_, rfl⟩
          rw [hv] at hv'; cases hv'
          refine forIn_array_unit _ ?_ h5
          intro a s hs
          obtain ⟨hc, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
          exact ⟨by simpa using hc, (Except.ok.inj hs).symm⟩
        · rename_i hn
          cases Except.ok.inj hs
          exact ⟨fun v hv => absurd hv (hn v), rfl⟩
      · intro c s hs
        obtain ⟨hc, hs⟩ := ite_ok hs (fun _ => throw_bind_ne)
        exact ⟨by simpa using hc, (Except.ok.inj hs).symm⟩
    · rename_i hn
      cases Except.ok.inj hs
      exact ⟨fun b hb => absurd hb (hn b), rfl⟩
  have ok' : ∀ bid b, BlockIn f bid b → BlockFacts f bid b := by
    rintro bid b ⟨hm, hb⟩
    obtain ⟨b', hb', h'⟩ := hok bid (by simpa using hm)
    rw [hb] at hb'; cases hb'; exact h'
  have val : ∀ bid b vid v, ValueIn f bid b vid v → valueOK b v = true := by
    rintro bid b vid v ⟨hin, hv, hval⟩
    obtain ⟨v', hv', -, hc⟩ := (ok' bid b hin).2.2.2.1 vid hv
    rw [hval] at hv'; cases hv'; exact hc
  have miss : ∀ bid b, BlockIn f bid b → _ := fun bid b (hin : BlockIn f bid b) =>
    hmiss bid hin.1 b hin.2
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
    exact ⟨v, hv', hvid, (valueOK_spec hc).2.2.1.trans hid⟩
  · intro bid b hin
    exact (ok' bid b hin).2.2.2.2
  · rintro bid1 b1 bid2 b2 ⟨hm1, hb1⟩ ⟨hm2, hb2⟩ vid hv1 hv2
    exact hon bid1 (by simpa using hm1) bid2 (by simpa using hm2) b1 b2 hb1 hb2 vid hv1 hv2
  · intro bid b hin i e he
    exact ⟨blk _ ((miss bid b hin).1 e (Array.mem_of_getElem? he)),
      (ok' bid b hin).2.1 i e he⟩
  · intro bid b hin j e he
    exact ⟨blk _ ((miss bid b hin).2.1 e (Array.mem_of_getElem? he)),
      (ok' bid b hin).2.2.1 j e he⟩
  · intro bid b vid v hin
    exact (valueOK_spec (val bid b vid v hin)).1
  · intro bid b vid v hin
    exact (valueOK_spec (val bid b vid v hin)).2.2.2
  · intro bid b vid v hin
    exact (valueOK_spec (val bid b vid v hin)).2.1
  · rintro bid b vid v ⟨hin, hv, hval⟩ a ha
    exact listed a ((miss bid b hin).2.2.1 vid hv v hval a ha)
  · intro bid b hin c hc
    exact listed c ((miss bid b hin).2.2.2 c hc)
  · exact blk _ (by simpa using hentry)
  · intro b hb
    rw [hb] at hep
    simpa using hep

/-- A passing `wfDomCheck` establishes the well-formedness facts `WF`. -/
theorem wfDomCheck_wf {ce : CheckEnv} {f : Func} (h : wfDomCheck f = .ok ()) : WF ce f := by
  unfold wfDomCheck at h
  obtain ⟨⟨⟩, h1, -⟩ := bind_ok h
  exact wfCheck_wf h1

/-- A passing `wfDomCheck` has validated the dominator certificate. -/
theorem wfDomCheck_domCert {f : Func} (h : wfDomCheck f = .ok ()) :
    DomCert.check f = .ok () := by
  unfold wfDomCheck at h
  obtain ⟨⟨⟩, -, h2⟩ := bind_ok h
  exact h2

end GoFV.Proof
