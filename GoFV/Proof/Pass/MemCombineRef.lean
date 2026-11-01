import GoFV.Proof.Pass.MemCombineComplete
import GoFV.Proof.Pass.KnownBitsTerm
import GoFV.Opt.MemCombine.Check

/-!
# memcombine: the values the checker relates (issue #35)

`mc_ref`: every value `M` relates (reached in `g` from atom arguments and controls through
terms, listed in both functions, `relMarks`) is refined, at `tgtFuel` times the fuel, by the same
value of `g`. By induction on the fuel: an unchanged value by `opVal_mono`, an atom by the
valuations; a combined load (`rootOK`) because an integer source value has its description's
bytes and valid loads (`symOf_step_sound`), the description's values are in `M` (so the target
has the same bytes and the source's loads), the target's loads are valid as the source's cover
them (`covered_loadOK`), and a target description with defined bytes and valid loads is that
integer (`symOf_complete`). `McFacts`: what `mcOK` establishes (its atoms `AtomSim.AtomsX` by
`atomsXOK_spec`).
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.MemCombine.Check GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim GoFV.Proof.Pass.Rewrite

/-! ## The target's loads -/

theorem extract_one {bs : Array Byte} {j : Nat} (hj : j < bs.size) :
    bs.extract j (j + 1) = #[bs[j]] := by
  apply Array.ext (by simp; omega)
  intro i h1 h2
  simp only [Array.size_extract] at h1
  have : i = 0 := by omega
  subst this
  simp [Array.getElem_extract]

theorem read_one {M : Mem} {Q : Ptr} {n : Nat} {bs : Array Byte} (h : M.read Q n = some bs)
    {j : Nat} (hj : j < n) : M.read (Q.add (BitVec.ofNat 64 j)) 1 = some #[bs[j]'(by
      rw [read_size h]; exact hj)] := by
  rw [read_extract h (j := j) (k := 1) (by omega), extract_one]

/-- **The target's loads are valid**: a load whose pointer, memory, base and index values are
refined from `V` to `V'`, and whose bytes the valid loads of `sf` cover (`coveredOK`). -/
theorem covered_loadOK {V V' : ID → Val} {sf : List LoadRec} (hs : ∀ s ∈ sf, LoadOK V s)
    {t : LoadRec} (ht : coveredOK sf t = true) (hids : ∀ y ∈ t.ids, Sem.Refines (V y) (V' y)) :
    LoadOK V' t := by
  unfold coveredOK at ht
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at ht
  obtain ⟨⟨s0, hs0, ⟨⟨⟨⟨hp0, hm0⟩, hb0⟩, hi0⟩, ho0⟩⟩, hcov⟩ := ht
  obtain ⟨M, P, I, bs0, hm, hp, hI, hq, hrd0, hc0⟩ := hs s0 hs0
  rw [hm0] at hm; rw [hb0] at hp; rw [hi0] at hI; rw [hp0, ho0] at hq
  have hmem : t.mem ∈ t.ids := by simp [LoadRec.ids]
  have hbas : t.base ∈ t.ids := by simp [LoadRec.ids]
  have hptr : t.ptr ∈ t.ids := by simp [LoadRec.ids]
  obtain ⟨M', hm', hMM⟩ := refines_mem (hm ▸ hids _ hmem)
  have hp' := refines_ptr (hp ▸ hids _ hbas)
  have hq' := refines_ptr (hq ▸ hids _ hptr)
  have hI' : idxVal V' t.idx = some I := by
    cases hti : t.idx with
    | none => rw [hti] at hI; exact hI
    | some j =>
      rw [hti] at hI
      exact asOffset_mono (hids j (by simp [LoadRec.ids, hti])) hI
  -- each byte of `t` is a concrete one-byte read of `M'`
  have hbyte : ∀ k < t.size, ∃ c, M'.read ((ptrAt P I t.off).add (BitVec.ofNat 64 k)) 1 =
      some #[.b c] := by
    intro k hk
    obtain ⟨s, hs', ⟨⟨⟨⟨hms, hbs⟩, his⟩, h1⟩, h2⟩, h3⟩ := hcov k hk
    obtain ⟨Ms, Ps, Is, bs, hm2, hp2, hI2, -, hrd, hc⟩ := hs s hs'
    rw [hms, hm] at hm2; cases hm2
    rw [hbs, hp] at hp2; cases hp2
    rw [his, hI] at hI2; cases hI2
    obtain ⟨bs', hrd', hb⟩ := Mem.Refines.read hMM hrd
    rw [concrete_mono hb hc] at hrd'
    have hj : (t.off + k - s.off).toNat < s.size := by omega
    have := read_one hrd' hj
    obtain ⟨c, hcc⟩ := concrete_getElem? hc (j := (t.off + k - s.off).toNat)
      (by rw [read_size hrd]; exact hj)
    rw [Array.getElem?_eq_getElem (by rw [read_size hrd]; exact hj)] at hcc
    have hcc' := Option.some.inj hcc
    refine ⟨c, ?_⟩
    rw [← ptrAt_add] at this
    rw [← ptrAt_add, show t.off + (k : _root_.Int) = s.off + ((t.off + k - s.off).toNat : _root_.Int)
      by omega, this, hcc']
  by_cases hz : t.size = 0
  · refine ⟨M', P, I, #[], hm', hp', hI', hq', by rw [hz]; rfl, fun x hx => by simp at hx⟩
  obtain ⟨bs, hrd⟩ := read_cover (m := M') (Q := ptrAt P I t.off) (n := t.size) (by omega)
    ((List.range t.size).map fun k => (k, 1))
    (fun r hr => by
      simp only [List.mem_map, List.mem_range] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      obtain ⟨c, hc⟩ := hbyte k hk
      exact ⟨_, hc⟩)
    (fun k hk => ⟨(k, 1), List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩, Nat.le_refl _, by simp⟩)
  refine ⟨M', P, I, bs, hm', hp', hI', hq', hrd, fun x hx => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [Array.length_toList] at hk
  have hk' : k < t.size := by rw [← read_size hrd]; exact hk
  obtain ⟨c, hc⟩ := hbyte k hk'
  rw [read_one hrd hk'] at hc
  have hc' := congrArg Array.toList (Option.some.inj hc)
  simp only [List.cons.injEq, and_true] at hc'
  exact ⟨c, by rw [Array.getElem_toList]; exact hc'⟩

/-! ## The checker's facts -/

/-- What `mcOK` establishes. -/
structure McFacts (tabs : Tables) (f g : Func) (R : Array Bool) : Prop where
  atoms : atomsXOK f g = true
  cf : closedOK f = true
  cg : closedOK g = true
  blocks : KnownBits.blocksOK f g = true
  reach : reachOK g R = true
  val : ∀ x, x < g.valueTab.size → valOK tabs f g R (relMarks f g R) x = true

theorem mcOK_spec {tabs : Tables} {f g : Func} (h : mcOK tabs f g = true) :
    McFacts tabs f g (reachMarks g) := by
  unfold mcOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨ha, hcf⟩, hcg⟩, hb⟩, hr, hv⟩ := h
  exact ⟨ha, hcf, hcg, hb, hr, hv⟩

theorem McFacts.blocks_eq {tabs : Tables} {f g : Func} {R : Array Bool} (K : McFacts tabs f g R) :
    f.blocks = g.blocks := (atomsXOK_spec K.atoms).blocks

theorem listedD_eq : listedD = listedDefs := rfl

/-- A value `M` marks: reached, listed in both. -/
def InM (f g : Func) (R : Array Bool) (x : ID) : Prop :=
  R.getD x false = true ∧ LM f x ∧ LM g x

theorem relMarks_getD {f g : Func} {R : Array Bool} {x : ID}
    (h : (relMarks f g R).getD x false = true) : InM f g R x := by
  unfold relMarks at h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray] at h
  rcases Nat.lt_or_ge x g.valueTab.size with hlt | hge
  · rw [List.getElem?_range hlt] at h
    simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · rw [List.getElem?_eq_none (by simp; omega)] at h
    cases h

/-- The definitions of a value `M` marks. -/
theorem inM_defs {f g : Func} {R : Array Bool} {x : ID} (h : InM f g R x) :
    ∃ u w, f.value? x = some u ∧ listedD f x = some u ∧ listedD g x = some w ∧
      x < g.valueTab.size := by
  obtain ⟨-, hf, hg⟩ := h
  have mf := listedMarks_sound f x hf
  have mg := listedMarks_sound g x hg
  obtain ⟨u, hu⟩ : ∃ u, f.value? x = some u := by
    obtain ⟨_, _, _, _, _, u, hu, _⟩ := mf; exact ⟨u, hu⟩
  obtain ⟨w, hw⟩ : ∃ w, g.value? x = some w := by
    obtain ⟨_, _, _, _, _, w, hw, _⟩ := mg; exact ⟨w, hw⟩
  exact ⟨u, w, hu, by rw [listedD_eq, listedDefs_of_marked mf, hu],
    by rw [listedD_eq, listedDefs_of_marked mg, hw], GoFV.Proof.CheckFacts.lt_of_value? hw⟩

theorem sameVal_spec {u w : Value} (h : sameVal u w = true) :
    u.op = w.op ∧ u.type = w.type ∧ u.auxInt = w.auxInt ∧ u.aux = w.aux ∧ u.args = w.args := by
  unfold sameVal at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem rootOK_spec {tabs : Tables} {f g : Func} {M : Array Bool} {x : ID} {u w : Value}
    (h : rootOK tabs f g M x u w = true) :
    (∃ wo, orW u.op = some wo) ∧ w.op = .Copy ∧ w.type = u.type ∧
    ∃ bs sf sg, symOf tabs f.value? false false srcFuel x = some (bs, sf) ∧
      symOf tabs (listedD g) true true tgtFuel x = some (bs, sg) ∧ (∀ s ∈ bs, s.vbId? ≠ some x) ∧
      (∀ t ∈ sg, coveredOK sf t = true) ∧ (∀ s ∈ bs, ∀ y ∈ s.ids, M.getD y false = true) ∧
      ∀ t ∈ sg, ∀ y ∈ t.ids, M.getD y false = true := by
  unfold rootOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨ho, hc⟩, -⟩, hty⟩, h⟩ := h
  obtain ⟨wo, hwo⟩ := Option.isSome_iff_exists.1 ho
  refine ⟨⟨wo, hwo⟩, hc, hty, ?_⟩
  split at h
  · rename_i bs sf bt sg hs ht
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨heq, hnv⟩, hcov⟩, hl⟩ := h
    subst heq
    unfold leavesIn at hl
    simp only [Bool.and_eq_true, List.all_eq_true] at hl
    exact ⟨bs, sf, sg, hs, ht, hnv, hcov, hl.1, hl.2⟩
  · cases h

theorem storeOK_op {tabs : Tables} {f g : Func} {M : Array Bool} {x : ID} {u w : Value}
    (h : storeOK tabs f g M x u w = true) : u.op = .Store ∧ w.op = .Store := by
  unfold storeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2⟩

/-! ## Values as terms -/

theorem or_cases (w : Width) (args : List Val) :
    Sem.Int.or w args = .poison ∨ ∃ Z, Sem.Int.or w args = .int w Z := by
  unfold Sem.Int.or Sem.int2
  split
  · split
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

/-- A value listed in a block of a well-formed function is listed (`listedD`). -/
theorem listed_of_wf {c : CheckEnv} {h : Func} (hw : WF c h) {b : ID} (hb : b ∈ h.blocks)
    {hb' : Block} (hbb : h.block? b = some hb') {x : ID} (hx : x ∈ hb'.values) {v : Value}
    (hv : h.value? x = some v) : listedD h x = some v := by
  obtain ⟨v', hv', -, hvb⟩ := hw.valueId b hb' ⟨hb, hbb⟩ x hx
  rw [hv] at hv'; cases hv'
  rw [listedD_eq, listedDefs_of_marked ⟨b, hb, hb', hbb, hx, v, hv, hvb⟩, hv]

/-- The arguments of a listed value of `g` that is an atom or marked are marked. -/
theorem reach_args {g : Func} {R : Array Bool} (hR : reachOK g R = true) {b : ID}
    (hb : b ∈ g.blocks) {gb : Block} (hgb : g.block? b = some gb) {x : ID} (hxv : x ∈ gb.values)
    {w : Value} (hw : listedD g x = some w) (hm : termOp w.op = false ∨ R.getD x false = true) :
    ∀ a ∈ w.args, R.getD a false = true := by
  unfold reachOK at hR
  have := (Array.all_eq_true_iff_forall_mem.1 hR) b hb
  rw [hgb] at this
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at this
  have h2 := this.2 x hxv
  rw [hw] at h2
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with ⟨h1, h2⟩ | h2
  · rcases hm with hm | hm
    · rw [hm] at h1; cases h1
    · rw [hm] at h2; cases h2
  · exact Array.all_eq_true_iff_forall_mem.1 h2

/-- The controls of `g` are marked. -/
theorem reach_ctrls {g : Func} {R : Array Bool} (hR : reachOK g R = true) {b : ID}
    (hb : b ∈ g.blocks) {gb : Block} (hgb : g.block? b = some gb) :
    ∀ c ∈ gb.controls, R.getD c false = true := by
  unfold reachOK at hR
  have := (Array.all_eq_true_iff_forall_mem.1 hR) b hb
  rw [hgb] at this
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at this
  exact this.1

section
variable {tabs : Tables} {f g : Func} {R : Array Bool} {ce ce' : CheckEnv}
  (hwf : WF ce f) (hwg : WF ce' g) (K : McFacts tabs f g R)
include hwf hwg K

/-- The arguments of a reached value `M` marks, unchanged, are marked. -/
theorem args_inM {x : ID} (hx : InM f g R x) {u w : Value} (hu : f.value? x = some u)
    (hw : listedD g x = some w) (hargs : u.args = w.args) : ∀ a ∈ w.args, InM f g R a := by
  obtain ⟨hr, hf, hg⟩ := hx
  obtain ⟨b, hb, gb, hgb, hxv, w', hw', -⟩ := listedMarks_sound g x hg
  have hww : w' = w := by
    rw [listedD_eq, listedDefs_of_marked (listedMarks_sound g x hg), hw'] at hw; cases hw; rfl
  subst hww
  obtain ⟨bf, hbf, fb, hfb, hxf, u', hu', -⟩ := listedMarks_sound f x hf
  rw [hu] at hu'; cases hu'
  intro a ha
  exact ⟨reach_args K.reach hb hgb hxv hw (.inr hr) a ha,
    (closedOK_facts K.cf bf hbf fb hfb).2 x hxf u hu a (hargs ▸ ha),
    (closedOK_facts K.cg b hb gb hgb).2 x hxv w' hw' a ha⟩

/-- **Values as terms**: each value `M` marks is refined, at `tgtFuel` times the fuel, by the same
value of `g`. -/
theorem mc_ref {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ') (hTf : Term.Typed f.value? tabs ρ)
    (hTg : Term.Typed (listedDefs g) tabs ρ') :
    ∀ n x, InM f g R x →
      Sem.Refines (den f.value? tabs ρ n x) (den (listedDefs g) tabs ρ' (tgtFuel * n) x)
  | 0, _, _ => .poison _
  | n + 1, x, hx => by
    obtain ⟨u, w, hu, hlu, hlw, hlt⟩ := inM_defs hx
    have hv := K.val x hlt
    unfold valOK at hv
    rw [hlw, hlu] at hv
    simp only at hv
    have hT : tgtFuel * (n + 1) = (tgtFuel * n + (tgtFuel - 1)) + 1 := by
      simp only [tgtFuel]; omega
    have hlw' : listedDefs g x = some w := by rw [← listedD_eq]; exact hlw
    -- an unchanged value
    have same : sameVal u w = true → Sem.Refines (den f.value? tabs ρ (n + 1) x)
        (den (listedDefs g) tabs ρ' (tgtFuel * (n + 1)) x) := fun hs => by
      obtain ⟨hop, hty, hai, hax, hargs⟩ := sameVal_spec hs
      rw [hT]
      by_cases ht : termOp u.op = true
      · rw [den_succ_term hu ht, den_succ_term hlw' (hop ▸ ht), hop, hty, hai, hax, hargs]
        apply retype_mono; apply GoFV.Proof.Rules.opVal_mono
        refine refinesList_map fun a ha => ?_
        exact Sem.Refines.trans (mc_ref hρ hTf hTg n a (args_inM hwf hwg K hx hu hlw hargs a
          (Array.mem_toList_iff.1 ha)))
          (den_fuel_mono _ _ _ _ _ _ (Nat.le_add_right _ _))
      · rw [den_succ_atom (KnownBits.not_term_of hu ht),
          den_succ_atom (KnownBits.not_term_of hlw' (hop ▸ ht))]
        exact hρ x
    split at hv
    · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hv
      rcases hv with (hv | hv) | hv
      · rw [hx.1] at hv; cases hv
      · exact same hv
      · -- a combined load
        obtain ⟨⟨wo, hwo⟩, -, -, bs, sf, sg, hs, ht, hnx, hcov, hlb, hls⟩ := rootOK_spec hv
        obtain ⟨vs, wt, hvs, htys, -⟩ := symOf_shape hs
        rw [hu] at hvs; cases hvs
        obtain ⟨hto, hfo, hev⟩ := orW_spec hwo
        by_cases hint : ∃ (w0 : Width) (X : BitVec w0.bits), den f.value? tabs ρ (n + 1) x = .int w0 X
        · obtain ⟨w0, X, hX⟩ := hint
          have hsd := symOf_step_sound hTf (N := 15) hs hnx hX
          have hIH : ∀ y, (relMarks f g R).getD y false = true →
              Sem.Refines (den f.value? tabs ρ n y) (den (listedDefs g) tabs ρ' (tgtFuel * n) y) :=
            fun y hy => mc_ref hρ hTf hTg n y (relMarks_getD hy)
          have hB := semL_mono' (fun s hs y hy => hIH y (hlb s hs y hy)) hsd.1
          have hL : ∀ t ∈ sg, LoadOK (den (listedDefs g) tabs ρ' (tgtFuel * n)) t := fun t htg =>
            covered_loadOK hsd.2 (hcov t htg) fun y hy => hIH y (hls t htg y hy)
          rw [listedD_eq] at ht
          obtain ⟨w1, Y, hY, hYb⟩ := symOf_complete hTg (tgtFuel * n) tgtFuel x (bs, sg) _ ht hB hL
          have hw := width_eq_of_bytes (by
            have := congrArg List.length hYb; simp only [bytesOf_length] at this; exact this)
          subst hw
          rw [bytesOf_inj hYb] at hY
          rw [hX, show tgtFuel * (n + 1) = tgtFuel * n + tgtFuel by simp only [tgtFuel]; omega, hY]
          exact Sem.Refines.refl _
        · -- an `Or` is an integer or `poison`
          have hd := den_term (tabs := tabs) (n := n) (ρ := ρ) hu hto hfo
          rw [hev, htys] at hd
          rcases or_cases wo (u.args.toList.map (den f.value? tabs ρ n)) with he | ⟨Z, he⟩
          · rw [hd, he, AtomSim.retype_poison]; exact .poison _
          · rw [he] at hd
            by_cases hle : wt.bits ≤ wo.bits
            · refine absurd ⟨wt, Z.setWidth wt.bits, ?_⟩ hint
              rw [hd]
              show (if wt.bits ≤ wo.bits then Val.int wt (Z.setWidth wt.bits) else .poison) = _
              rw [if_pos hle]
            · have : den f.value? tabs ρ (n + 1) x = .poison := by
                rw [hd]
                show (if wt.bits ≤ wo.bits then Val.int wt (Z.setWidth wt.bits) else .poison) = _
                rw [if_neg hle]
              rw [this]; exact .poison _
    · -- an atom of `g` (unchanged or a combined store) is an atom of `f`
      rename_i hwt
      have hut : ¬ termOp u.op = true := by
        simp only [Bool.or_eq_true] at hv
        rcases hv with hv | hv
        · rw [(sameVal_spec hv).1]; exact hwt
        · rw [(storeOK_op hv).1]; decide
      rw [hT, den_succ_atom (KnownBits.not_term_of hu hut),
        den_succ_atom (KnownBits.not_term_of hlw' hwt)]
      exact hρ x

theorem mc_termRef {x : ID} (hx : InM f g R x) :
    TermRef f.value? tabs x (listedDefs g) tabs x :=
  fun n => ⟨tgtFuel * n, fun _ _ hρ hTf hTg => mc_ref hwf hwg K hρ hTf hTg n x hx⟩

/-- **An unchanged atom's arguments** are refined as terms. -/
theorem mc_atomArgs_same {b : ID} (hb : b ∈ g.blocks) {gb : Block} (hgb : g.block? b = some gb)
    {fb : Block} (hfb : f.block? b = some fb) {a : ID} (ha : a ∈ gb.values) (haf : a ∈ fb.values)
    {u u' : Value} (hu : g.value? a = some u) (hu' : f.value? a = some u')
    (ht : termOp u.op = false) (hv : sameVal u' u = true) :
    ∀ i < u.args.size, TermRef f.value? tabs u'.args[i]! (listedDefs g) tabs u.args[i]! := by
  intro i hi
  have hbf : b ∈ f.blocks := K.blocks_eq ▸ hb
  have hlg := listed_of_wf hwg hb hgb ha hu
  have hargs := (sameVal_spec hv).2.2.2.2
  rw [hargs]
  have hmem : u.args[i]! ∈ u.args := by
    rw [getElem!_pos u.args i hi]; exact Array.getElem_mem hi
  exact mc_termRef hwf hwg K ⟨reach_args K.reach hb hgb ha hlg (.inl ht) _ hmem,
    (closedOK_facts K.cf b hbf fb hfb).2 a haf u' hu' _ (hargs ▸ hmem),
    (closedOK_facts K.cg b hb gb hgb).2 a ha u hu _ hmem⟩

/-- **Controls.** -/
theorem mc_controls : ControlsRef tabs f g := by
  intro b hb fb gb hfb hgb
  have hbf : b ∈ f.blocks := K.blocks_eq ▸ hb
  obtain ⟨gb', hgb', -, -, -, hctl, -⟩ := KnownBits.blocksOK_facts K.blocks hbf hfb
  rw [hgb] at hgb'; cases hgb'
  refine ⟨by rw [hctl], fun k hk => ?_⟩
  rw [← hctl]
  have hk' : k < fb.controls.size := hctl ▸ hk
  have hmem : fb.controls[k]! ∈ fb.controls := by
    rw [getElem!_pos fb.controls k hk']; exact Array.getElem_mem hk'
  exact mc_termRef hwf hwg K ⟨reach_ctrls K.reach hb hgb _ (hctl ▸ hmem),
    (closedOK_facts K.cf b hbf fb hfb).1 _ hmem,
    (closedOK_facts K.cg b hb gb hgb).1 _ (hctl ▸ hmem)⟩

end

end GoFV.Proof.MemCombine
