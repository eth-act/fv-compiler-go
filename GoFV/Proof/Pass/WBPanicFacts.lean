import GoFV.Proof.Pass.WBCov

variable [GoFV.SSA.Sem.Addrs]

/-!
# writebarrier: facts for a panicking block entry (issue #36)

`src_np`/`ncs_np`: a run's stores and dropped nil check are non-pure nodes of `B`.
`held_pure_args`: the in-block arguments of a held pure value listed in segment `j` are held and
listed in segment `j` (before it in the schedule) or earlier. `cov_of_runs`: the source facts of
the values of the segments up to `J` and the buffer blocks before `J`, when the runs before `J`
were evaluated. `localQ_mono`: `LocalQ` under a stronger property that only constrains values
outside the evaluated list. `panic_kept_step`, `panic_nc_step`: the target's copy of the
source's panicking node panics alike. `runMem_of_panic`: a dropped nil check that panics read
its run's memory. `filter_first`: the values before the first non-pure node are pure.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

theorem filter_first {p : ID → Bool} : ∀ {o : List ID} {y : ID} {ys : List ID},
    o.filter p = y :: ys → ∃ pre post, o = pre ++ y :: post ∧ ∀ x ∈ pre, p x = false := by
  intro o
  induction o with
  | nil => intro y ys h; simp at h
  | cons a o ih =>
    intro y ys h
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha] at h
      obtain ⟨rfl, -⟩ := List.cons.inj h
      exact ⟨[], o, rfl, by simp⟩
    · rw [List.filter_cons_of_neg ha] at h
      obtain ⟨pre, post, rfl, hp⟩ := ih h
      refine ⟨a :: pre, post, rfl, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · simpa using ha
      · exact hp x hx

theorem localQ_mono {env : Env} {ctx : Sem.Ctx} {fr0 : Frame} {Q Q' : ID → Val → Prop} {x : ID}
    (h : LocalQ env ctx fr0 Q x) (hQ' : ∀ a z, Q' a z → Q a z) (hx : ∀ z, Q x z → Q' x z) :
    LocalQ env ctx fr0 Q' x := by
  intro g hg hA
  obtain ⟨y, hy, hq⟩ := h g hg fun a ha => (hA a ha).imp fun _ h' => ⟨h'.1, hQ' _ _ h'.2⟩
  exact ⟨y, hy, hx y hq⟩

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

theorem src_np (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) {s : ID}
    (hs : s ∈ r.src) : npOf c.f B s = true := by
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsrc, -⟩ :=
    runOK_spec ((blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j r hr)
  obtain ⟨-, -, -, hsrcs, -⟩ := runOf_spec ((chainRuns_spec S.ch).1 j r hr).2.2.2
  obtain ⟨u, hu, hop, -⟩ := hsrcs k s hk
  unfold npOf
  simp only [Array.contains_iff_mem.2 (hsrc s hs).1, hu, Bool.true_and]
  rcases hop with h | h | h | h | h <;> rw [h] <;> decide

theorem ncs_np (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) {n : ID}
    (hn : n ∈ ncsOf c r) : npOf c.f B n = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnc⟩ :=
    runOK_spec ((blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j r hr)
  obtain ⟨hn', hK⟩ : r.nc = some n ∧ c.K.getD n false = false := by
    unfold ncsOf at hn
    cases h : r.nc with
    | none => simp only [h] at hn; cases hn
    | some m =>
      simp only [h] at hn
      split at hn
      · cases hn
      · rename_i hK
        obtain rfl := List.mem_singleton.1 hn
        exact ⟨rfl, by simpa using hK⟩
  obtain ⟨hnB, u, hu, hop⟩ := hnc n hn'
  unfold npOf
  simp only [Array.contains_iff_mem.2 (hnB.resolve_right (by rw [hK]; decide)), hu,
    Bool.true_and]
  rw [hop]; decide

private theorem bs_topo_before {D : ID → List ID} : ∀ {o : List ID}, TopoRem D o →
    ∀ {x a : ID}, x ∈ o → a ∈ D x → a ∈ o → Order.Before o a x
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | y :: s, ht, x, a, hx, ha, hao => by
    obtain ⟨h1, h2⟩ := ht
    rcases List.mem_cons.1 hx with rfl | hxs
    · exact absurd hao (h1 a ha)
    · rcases List.mem_cons.1 hao with rfl | haos
      · exact Order.before_cons.2 (.inl ⟨rfl, hxs⟩)
      · exact Order.before_cons.2 (.inr (bs_topo_before h2 hxs ha haos))

private theorem bs_np_of_rank (S : Setup c b B rs l) {x : ID} {q : Nat}
    (hq : NpRank c b rs x q) (hK : c.K.getD x false = false) : npOf c.f B x = true := by
  rcases hq with ⟨-, -, -, hK'⟩ | ⟨j, r, -, hr, hx | hx⟩
  · rw [hK] at hK'; cases hK'
  · exact S.ncs_np hr hx
  · exact S.src_np hr hx

private theorem bs_kept_same (S : Setup c b B rs l) {x : ID} (hK : c.K.getD x false = true)
    {u : Value} (hu : c.f.value? x = some u) :
    ∃ w, c.g.value? x = some w ∧ u.op = w.op ∧ u.args = w.args := by
  obtain ⟨u', w, hu', hw, hsame, -⟩ :=
    keptMarks_spec (by rw [← (ctxOf_spec S.ctx).2.2.2.1]; exact hK)
  rw [hu] at hu'; cases hu'
  unfold sameV at hsame
  simp only [Bool.and_eq_true, beq_iff_eq] at hsame
  exact ⟨w, hw, hsame.1.1.1.1.2, hsame.2⟩

/-- A held value listed in segment `j` is not a `Phi` of `g`, when its source is not one. -/
private theorem bs_held_nophi (S : Setup c b B rs l) {j : Nat} {s a : ID}
    (hs : (segsOf b rs)[j]? = some s) (ha : a ∈ vals c.g s) (hh : c.held a = true)
    (hap : ∀ va, c.f.value? a = some va → va.op ≠ .Phi) :
    ∃ v, c.g.value? a = some v ∧ v.op ≠ .Phi := by
  have hok := (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.2.1 j s hs a ha
  cases hv : c.g.value? a with
  | none => unfold Ctx.roleOK at hok; rw [hv] at hok; cases hok
  | some v =>
    refine ⟨v, rfl, fun hp => ?_⟩
    cases j with
    | zero =>
      obtain ⟨-, hK, -, u, hu, hsame, -⟩ := S.phi_seg0 hs ha hv hp
      obtain ⟨w, hw, hop, -⟩ := bs_kept_same S hK hu
      rw [hv] at hw; cases hw
      exact hap u hu (hop.trans hp)
    | succ k =>
      obtain ⟨r, -, -, hρ, -⟩ := S.phi_seg hs ha hv hp
      rcases role_of_held (rs := rs) hh with h | h | h <;> rw [hρ] at h <;> cases h

/-- The in-block arguments of a held pure value of segment `j`. -/
theorem held_pure_args (S : Setup c b B rs l) {j : Nat} {s x : ID}
    (hs : (segsOf b rs)[j]? = some s) (hx : x ∈ vals c.g s) (hh : c.held x = true)
    (hp : npOf c.f B x = false) {u : Value} (hu : c.f.value? x = some u) (hxp : u.op ≠ .Phi)
    {a : ID}
    (ha : a ∈ u.args) (haB : a ∈ B.values) (hap : ∀ va, c.f.value? a = some va → va.op ≠ .Phi) :
    c.held a = true ∧ ∃ j', j' ≤ j ∧ InSeg c b rs j' a ∧
      (j' = j → ∀ C oC, c.g.block? s = some C → schedule c.g C = some oC →
        Order.Before oC.toList a x) := by
  -- `x` is kept: a held value that is not is a run's store, non-pure
  have hK : c.K.getD x false = true := by
    cases hK : c.K.getD x false with
    | true => rfl
    | false =>
      exfalso
      rcases S.held_rank hs hx hh with hq | ⟨j', -, hq⟩
      · rw [bs_np_of_rank S hq hK] at hp; cases hp
      · rw [bs_np_of_rank S hq hK] at hp; cases hp
  obtain ⟨-, -, -, -, -, hlz⟩ := ctxOf_spec S.ctx
  have hok := (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.2.1 j s hs x hx
  obtain ⟨w, hw, hop, hargs⟩ := bs_kept_same S hK hu
  have hwa : c.isWbaddr x = false := by
    cases h : c.isWbaddr x with
    | false => rfl
    | true =>
      exfalso
      unfold Ctx.isWbaddr at h
      cases hz : c.lazy with
      | none => rw [hz] at h; cases h
      | some p =>
        obtain ⟨wa, c0⟩ := p
        rw [hz] at h hlz
        simp only [Option.any_some, beq_iff_eq] at h
        subst h
        rw [(lazyOK_not_held hlz).1] at hK; cases hK
  have hc0 : c.isConst0 x = false := by
    cases h : c.isConst0 x with
    | false => rfl
    | true =>
      exfalso
      unfold Ctx.isConst0 at h
      cases hz : c.lazy with
      | none => rw [hz] at h; cases h
      | some p =>
        obtain ⟨wa, c0⟩ := p
        rw [hz] at h hlz
        simp only [Option.any_some, beq_iff_eq] at h
        subst h
        obtain ⟨-, ⟨w', hw', -, -, hargs', -⟩, -⟩ := lazyOK_some hlz
        rw [hw] at hw'; cases hw'
        rw [hargs, hargs'] at ha
        simp at ha
  have hρ : c.roleOf rs x = .held := by
    simp only [Ctx.roleOf, hwa, hc0, hh, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨-, -, hH⟩ := roleOK_held hok hw hρ
  obtain ⟨-, u', hu', -, havail⟩ := hH.resolve_right (fun h => by rw [hK] at h; cases h.1)
  rw [hu] at hu'; cases hu'
  obtain ⟨hha, hin, -⟩ := availIn_spec (havail hxp a ha)
  obtain ⟨s', hs'm, has'⟩ := hin haB
  obtain ⟨j', hj'⟩ := List.getElem?_of_mem hs'm
  have hlt : j' < j + 1 := by
    have := (List.getElem?_eq_some_iff.1 hj').1
    rw [List.length_take] at this; omega
  rw [List.getElem?_take_of_lt hlt] at hj'
  refine ⟨hha, j', by omega, ⟨s', hj', has'⟩, fun hjj C oC hC hoC => ?_⟩
  subst hjj
  rw [hs] at hj'; cases hj'
  obtain ⟨-, -, -, hsb, -⟩ := S.seg_block hs
  obtain ⟨ce, hwg⟩ := S.wg
  obtain ⟨-, htopo, hmem⟩ :=
    schedule_topo (valuesOwn hwg hsb hC) (hwg.valuesNodup s C ⟨hsb, hC⟩) hoC
  rw [vals_of hC] at hx has'
  apply bs_topo_before htopo
  · exact (hmem x).2 ⟨hx, w, hw, hop ▸ hxp⟩
  · rw [argsF_of hw, ← hargs]; exact Array.mem_toList_iff.2 ha
  · obtain ⟨v, hv, hvp⟩ := bs_held_nophi S hs (by rw [vals_of hC]; exact has') hha hap
    exact (hmem a).2 ⟨has', v, hv, hvp⟩

private theorem bs_pos_roleOK (S : Setup c b B rs l) {J : Nat} {x : ID}
    (hpos : (∃ j, j ≤ J ∧ InSeg c b rs j x) ∨ (∃ j, j < J ∧ InT c rs j x)) :
    ∃ inT j, c.roleOK b B (segsOf b rs) rs inT j x = true ∧ (inT = false → j ≤ J) ∧
      (inT = true → j < J) := by
  rcases hpos with ⟨j, hj, s, hs, hx⟩ | ⟨j, hj, r, hr, hx⟩
  · exact ⟨false, j, (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.2.1 j s hs x hx, fun _ => hj,
      fun h => by cases h⟩
  · obtain ⟨-, -, ⟨T, hT, -, -, -, -, -, hall⟩, -⟩ :=
      runOK_spec ((blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j r hr)
    rw [vals_of hT] at hx
    exact ⟨true, j, hall x hx, ⟨fun h => absurd h (by decide), fun _ => hj⟩⟩

/-- **Source facts up to `J`**: the values of segments `j ≤ J` and of the buffer blocks `j < J`,
when the runs before `J` are in a closed set `P` of evaluated values and the held values in
question are too. -/
theorem cov_of_runs (S : Setup c b B rs l) {env : Env} {Gr : Frame} {P : ID → Prop}
    (hEv : ∀ x, P x → Ev env c Gr x) (hW : WbHelpers env)
    (hPcl : ∀ x a v, P x → c.f.value? x = some v → a ∈ v.args → a ∈ B.values →
      (∀ va, c.f.value? a = some va → va.op ≠ .Phi) → P a) (hout : OutEv env c B Gr)
    {J : Nat} (hruns : ∀ j r, j < J → rs[j]? = some r →
      (∀ s ∈ r.src, P s) ∧ (∀ n ∈ ncsOf c r, P n))
    {x : ID} (hpos : (∃ j, j ≤ J ∧ InSeg c b rs j x) ∨ (∃ j, j < J ∧ InT c rs j x))
    (hheld : c.roleOf rs x = .held → c.K.getD x false = true →
      (∀ u, c.f.value? x = some u → u.op ≠ .Phi) → P x) :
    Cov env c rs Gr x := by
  obtain ⟨inT, j, hok, hF, hT⟩ := bs_pos_roleOK S hpos
  obtain ⟨w, hw⟩ : ∃ w, c.g.value? x = some w := by
    cases hw : c.g.value? x with
    | none => unfold Ctx.roleOK at hok; rw [hw] at hok; cases hok
    | some w => exact ⟨w, rfl⟩
  refine S.cov_intro hEv hPcl hout hW hheld ?_ ?_
  · intro j' hρ r hr
    refine hruns j' r ?_ hr
    rcases hρ with ⟨k, hρ⟩ | hρ | hρ | hρ
    · obtain ⟨hi, hjj, -⟩ := roleOK_tgt hok hw hρ
      have := hF hi; omega
    · obtain ⟨hi, hjj, -⟩ := roleOK_ncEnd hok hw hρ
      have := hF hi; omega
    · obtain ⟨hi, hjj, -⟩ := roleOK_ncThen hok hw hρ
      have := hT hi; omega
    · obtain ⟨hi, hjj, -⟩ := roleOK_call hok hw hρ
      have := hT hi; omega
  · intro j' hρ
    obtain ⟨hi, hjj, -, -, -, -, r, hr, -⟩ := roleOK_wb hok hw hρ
    have hlt := hT hi
    obtain ⟨-, -, -, -, -, -, hpos', -⟩ :=
      runOK_spec ((blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j' r hr)
    have hs0 : r.src[0]? = some r.src[0] := List.getElem?_eq_getElem hpos'
    exact S.runMem_of_ev hr hs0
      (hEv _ ((hruns j' r (by omega) hr).1 _ (List.getElem_mem hpos')))

private theorem pk_runOK (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    c.runOK b B (segsOf b rs) rs j r = true :=
  (blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j r hr

private theorem pk_runOf (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    runOf? c.f c.g r.sp = some r :=
  ((chainRuns_spec S.ch).1 j r hr).2.2.2

/-- A kept panicking node is a held value. -/
private theorem pk_role (S : Setup c b B rs l) {r : ID} (hK : c.K.getD r false = true)
    {rv : Value} (hrv : c.f.value? r = some rv) (hrop : Panicking rv.op) :
    c.roleOf rs r = .held := by
  have hh : c.held r = true := by unfold Ctx.held; rw [hK]; rfl
  have hl := (ctxOf_spec S.ctx).2.2.2.2.2
  rcases role_of_held (rs := rs) hh with hρ | hρ | hρ
  · exact hρ
  · obtain ⟨c0, hz⟩ := lazy_of_wbaddr (roleOf_wbaddr_inv hρ)
    rw [hz] at hl
    have := (lazyOK_not_held hl).1
    rw [hK] at this; cases this
  · obtain ⟨wa, hz⟩ := lazy_of_const0 (roleOf_const0_inv hρ)
    rw [hz] at hl
    obtain ⟨-, ⟨w0, hw0, hop0, -⟩, -⟩ := lazyOK_some hl
    obtain ⟨u', w', hu', hw', hsame, -⟩ :=
      keptMarks_spec (by rw [← (ctxOf_spec S.ctx).2.2.2.1]; exact hK)
    rw [hrv] at hu'; cases hu'
    rw [hw0] at hw'; cases hw'
    simp only [sameV, Bool.and_eq_true, beq_iff_eq] at hsame
    have hop : rv.op = .Const32 := hsame.1.1.1.1.2.trans hop0
    rw [hop] at hrop
    rcases hrop with h | h
    · exact absurd h (by decide)
    · cases h

/-- **The kept panicking node**: on any frame whose argument registers satisfy `QR`, it panics as
the source's. -/
theorem panic_kept_step (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hG : GrOK c B rs Gr fr0) {k : Nat} {r : ID} (hr : InSeg c b rs k r)
    (hK : c.K.getD r false = true) {rv : Value} (hrv : c.f.value? r = some rv)
    (hrop : Panicking rv.op) {e : Panic} {m : Mem}
    (hpan : stepV env (Ctx.make c.tabs c.f) Gr r = .panic e m) :
    ∀ g' : Frame, g' = { fr0 with regs := g'.regs } →
      (∀ a ∈ argsF c.g r, ∃ z, g'.regs[a]? = some (some z) ∧ QR c rs Gr a z) →
      stepV env (Ctx.make c.tabs c.g) g' r = .panic e m := by
  obtain ⟨s, hs, hxs⟩ := hr
  have hρ := pk_role S hK hrv hrop
  obtain ⟨u', w, hu', hw, hsame, -⟩ :=
    keptMarks_spec (by rw [← (ctxOf_spec S.ctx).2.2.2.1]; exact hK)
  rw [hrv] at hu'; cases hu'
  have hok := (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.2.1 k s hs r hxs
  have hnp : rv.op ≠ .Phi := fun hp => by
    rw [hp] at hrop
    rcases hrop with h | h
    · exact absurd h (by decide)
    · cases h
  obtain ⟨-, hxB, ⟨-, u, hu, -, hnphi⟩ | ⟨hK', -⟩⟩ := roleOK_held hok hw hρ
  · rw [hrv] at hu; cases hu
    have hargsH : ∀ a ∈ rv.args, c.held a = true := fun a ha => (availIn_spec (hnphi hnp a ha)).1
    have huid : rv.id = r := by
      obtain ⟨ce, hwf⟩ := S.wf
      obtain ⟨v, hv, hvid, -⟩ := hwf.valueId b B ⟨S.hb, S.hB⟩ r hxB
      rw [hrv] at hv; cases hv; exact hvid
    rw [stepV_eq (ctx := Ctx.make c.tabs c.f) hrv] at hpan
    obtain ⟨L, hL, -⟩ := evalValue_inv_panic hpan
    intro g' hg' hA
    simp only [sameV, Bool.and_eq_true, beq_iff_eq] at hsame
    obtain ⟨⟨⟨⟨⟨hid, hop⟩, htyp⟩, hai⟩, haux⟩, hargsEq⟩ := hsame
    rw [stepV_eq (ctx := Ctx.make c.tabs c.g) hw, ← hpan]
    have hc := AtomSim.ctx_eq (tabs := c.tabs) S.own.symm
    refine evalValue_eq_of_args hop.symm haux.symm hai.symm hid.symm (by rw [hargsEq]) ?_ ?_ ?_
      (by rw [hc]) (by rw [hc]) (by rw [hc])
    · intro k' a hk
      have hka : rv.args.toList[k']? = some a := by simpa using hk
      obtain ⟨z1, -, hr1⟩ := regsAre_get hL hka
      have ha : a ∈ rv.args := Array.mem_toList_iff.1 (List.mem_of_getElem? hka)
      obtain ⟨z2, hz2, hq2⟩ := argQ hw hA (a := a) (by rw [← hargsEq]; exact ha)
      exact ⟨a, z1, by rw [← hargsEq]; exact hk, hr1,
        by rw [hz2, hG.held a z2 z1 (hargsH a ha) hq2 hr1]⟩
    · rw [hg', hG.fr]
    · rw [huid, tys_of_value hrv, tys_of_value hw, htyp]
  · rw [hK] at hK'; cases hK'

/-- The value of a run's dropped nil check. -/
private theorem pn_value (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) {n : ID}
    (hn : r.nc = some n) :
    ∃ nv, c.f.value? n = some nv ∧ nv.op = .NilCheck ∧ nv.args[1]? = some r.sp.mem := by
  obtain ⟨x0, v0, a, nv, hx0, hv0, -, ha, hnv, hnop, hm, hnid⟩ :=
    (runOf_spec (pk_runOf S hr)).2.2.2.2.1 n hn
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsrc, -⟩ := runOK_spec (pk_runOK S hr)
  have hx0B := (hsrc x0 (List.mem_of_getElem? hx0)).1
  have hau : a ∈ v0.args := Array.mem_iff_getElem?.2 ⟨0, ha⟩
  obtain ⟨bid, blk, hbin, hablk⟩ := hwf.argListed b B x0 v0 ⟨⟨S.hb, S.hB⟩, hx0B, hv0⟩ a hau
  obtain ⟨va, hva, hvid, -⟩ := hwf.valueId bid blk hbin a hablk
  rw [hnv] at hva; cases hva
  have han : a = n := hvid.symm.trans hnid
  subst han
  exact ⟨nv, hnv, hnop, hm⟩

/-- **A dropped nil check that panics** reads its run's memory, the panic's memory. -/
theorem runMem_of_panic (S : Setup c b B rs l) {env : Env} {Gr : Frame} {j : Nat} {r : Run}
    (hr : rs[j]? = some r) {n : ID} (hn : r.nc = some n) {e : Panic} {m : Mem}
    (hpan : stepV env (Ctx.make c.tabs c.f) Gr n = .panic e m) : RunMem Gr rs j m := by
  obtain ⟨nv, hnv, hnop, hm⟩ := pn_value S hr hn
  rw [stepV_eq (ctx := Ctx.make c.tabs c.f) hnv] at hpan
  obtain ⟨L, hL, hop0⟩ := evalValue_inv_panic hpan
  rw [DAE.evalOp_memRoot (.inr (.inr (.inr (.inr (.inr (.inr hnop))))))] at hop0
  obtain ⟨p, rfl⟩ := nilCheck_inv_panic hnop hop0
  obtain ⟨z, hz, hreg⟩ := regsAre_get hL (k := 1) (by simpa using hm)
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hz
  subst hz
  exact ⟨r, hr, hreg⟩

/-- The nil-check copy step, for one segment index. -/
private theorem pn_step (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hG : GrOK c B rs Gr fr0) {n : ID} {e : Panic} {m : Mem}
    (hpan : stepV env (Ctx.make c.tabs c.f) Gr n = .panic e m) {j' : Nat} {y mT : ID}
    (hy : NcCopy c B (segsOf b rs) j' n y mT) :
    ∀ g' : Frame, g' = { fr0 with regs := g'.regs } →
      (∀ a ∈ argsF c.g y, ∃ z, g'.regs[a]? = some (some z) ∧ QR c rs Gr a z) →
      g'.regs[mT]? = some (some (.mem m)) →
      stepV env (Ctx.make c.tabs c.g) g' y = .panic e m := by
  intro g' _ hA hmT
  obtain ⟨u, w, p, mS, hu, hw, hopu, hopw, -, hu2, hw2, hav⟩ := hy
  rw [stepV_eq (ctx := Ctx.make c.tabs c.f) hu] at hpan
  obtain ⟨L, hL, hop0⟩ := evalValue_inv_panic hpan
  rw [DAE.evalOp_memRoot (.inr (.inr (.inr (.inr (.inr (.inr hopu))))))] at hop0
  obtain ⟨zp, rfl⟩ := nilCheck_inv_panic hopu hop0
  rw [hu2] at hL
  obtain ⟨hzp, -, -⟩ := hL
  obtain ⟨tp, htp, hqp⟩ := argQ hw hA (a := p) (by rw [hw2]; simp)
  have := hG.held p tp zp (availIn_spec hav).1 hqp hzp
  subst this
  rw [stepV_eq (ctx := Ctx.make c.tabs c.g) hw,
    evalValue_of (L := [tp, .mem m]) (by rw [hw2]; exact ⟨htp, hmT, trivial⟩),
    DAE.evalOp_memRoot (.inr (.inr (.inr (.inr (.inr (.inr hopw)))))),
    (WB.nilCheck_panic hopu hopw hop0).2]
  rfl

/-- **A copy of the dropped nil check** panics as the source's, on any frame whose argument
registers hold the nil check's pointer (held) and the run's memory. -/
theorem panic_nc_step (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hG : GrOK c B rs Gr fr0) {j : Nat} {r : Run} (hr : rs[j]? = some r) {n : ID}
    (hn : r.nc = some n) {e : Panic} {m : Mem}
    (hpan : stepV env (Ctx.make c.tabs c.f) Gr n = .panic e m) {y mT : ID}
    (hy : NcCopy c B (segsOf b rs) j n y mT ∨ NcCopy c B (segsOf b rs) (j + 1) n y mT) :
    ∀ g' : Frame, g' = { fr0 with regs := g'.regs } →
      (∀ a ∈ argsF c.g y, ∃ z, g'.regs[a]? = some (some z) ∧ QR c rs Gr a z) →
      g'.regs[mT]? = some (some (.mem m)) →
      stepV env (Ctx.make c.tabs c.g) g' y = .panic e m := by
  rcases hy with hy | hy
  · exact pn_step S hG hpan hy
  · exact pn_step S hG hpan hy

end Setup

end GoFV.Proof.WB
