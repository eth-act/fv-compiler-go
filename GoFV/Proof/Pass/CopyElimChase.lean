import GoFV.Proof.Pass.CopyElimEdit
import Std.Tactic.Do

/-!
# `chase`, `copySource` and `copyelimValue` under `Inv`

Without copy cycles `chase` returns the end `w` of the chain and leaves the function alone
(`chase_spec`: the hare never meets the tortoise, since chain nodes are distinct, and the chain
is shorter than the loop bound). `copySource` then points every copy of the chain at `w`
(`copySource_spec`), and `copyelimValue` leaves every argument of the value a non-copy
(`copyelimValue_spec`).
-/

open Std.Do

set_option mvcgen.warning false

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.Opt GoFV.Proof

theorem copy_of_lt {F : Func} {x r : ID} {n k : Nat} (hs : Src (vw F) x r n) (hk : k < n) :
    (F.getV (node (vw F) k x)).op = .Copy ∧ (F.getV (node (vw F) k x)).args[0]! = node (vw F) (k + 1) x :=
  getV_cstep_some (hs.pt_step hk)

theorem lt_of_copy {F : Func} {x r : ID} {n k : Nat} (hs : Src (vw F) x r n) (hk : k ≤ n)
    (hop : (F.getV (node (vw F) k x)).op = .Copy) : k < n := by
  rcases Nat.lt_or_eq_of_le hk with h | rfl
  · exact h
  · rw [hs.pt_last] at hop; exact absurd hop (getV_cstep_none hs.end)

theorem chase_spec {F : Func} {w0 r : ID} {n : Nat} (hs : Src (vw F) w0 r n)
    (hn : n < 2 * (F.vidLast + 1) + 2) : CopyElim.chase F w0 = (F, r) := by
  generalize h : CopyElim.chase F w0 = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨cur, st⟩ => ⌜(cur.prefix.length ≤ n ∧ st = (node (vw F) cur.prefix.length w0,
      node (vw F) (cur.prefix.length / 2) w0, cur.prefix.length % 2 == 1, F)) ∨
      (st.2.2.2 = F ∧ st.1 = r)⌝
  case vc1 =>
    rename_i pref cur suff hxs b w s1 slow s2 adv f hop hinv
    rcases hinv with ⟨hk, rfl⟩ | ⟨hf, hw⟩
    · simp +zetaDelta only [bne_iff_ne, ne_eq] at *
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · exact absurd (copy_of_lt hs hlt).1 hop
      · exact .inr ⟨trivial, by rw [heq]; exact hs.pt_last⟩
    · simp +zetaDelta only at *
      exact .inr ⟨hf, hw⟩
  case vc2 =>
    rename_i pref cur suff hxs b w s1 slow s2 adv f hop w' heq hinv
    rcases hinv with ⟨hk, rfl⟩ | ⟨hf, hw⟩
    · simp +zetaDelta only [bne_iff_ne, ne_eq, Decidable.not_not, beq_iff_eq] at *
      have hlt := lt_of_copy hs hk hop
      rw [(copy_of_lt hs hlt).2] at heq
      have := hs.pt_inj (by omega) (by omega) heq
      omega
    · simp +zetaDelta only [bne_iff_ne, ne_eq, Decidable.not_not] at *
      rw [hf, hw] at hop
      exact absurd hop (getV_cstep_none hs.end)
  case vc3 =>
    rename_i pref cur suff hxs b w s1 slow s2 adv f hop w' heq jp hadv hinv
    rcases hinv with ⟨hk, rfl⟩ | ⟨hf, hw⟩
    · simp +zetaDelta only [bne_iff_ne, ne_eq, Decidable.not_not, beq_iff_eq] at *
      have hlt := lt_of_copy hs hk hop
      refine .inl ⟨by simp; omega, ?_⟩
      rw [(copy_of_lt hs hlt).2, (copy_of_lt hs (k := pref.length / 2) (by omega)).2]
      simp only [List.length_append, List.length_singleton, Prod.mk.injEq]
      refine ⟨trivial, ?_, ?_, trivial⟩
      · rw [show (pref.length + 1) / 2 = pref.length / 2 + 1 by omega]
      · have h2 : (pref.length + 1) % 2 = 0 := by omega
        simp [hadv, h2]
    · simp +zetaDelta only [bne_iff_ne, ne_eq, Decidable.not_not] at *
      rw [hf, hw] at hop
      exact absurd hop (getV_cstep_none hs.end)
  case vc4 =>
    rename_i pref cur suff hxs b w s1 slow s2 adv f hop w' heq jp hadv hinv
    rcases hinv with ⟨hk, rfl⟩ | ⟨hf, hw⟩
    · simp +zetaDelta only [bne_iff_ne, ne_eq, Decidable.not_not, beq_iff_eq] at *
      have hlt := lt_of_copy hs hk hop
      refine .inl ⟨by simp; omega, ?_⟩
      rw [(copy_of_lt hs hlt).2]
      simp only [List.length_append, List.length_singleton, Prod.mk.injEq]
      refine ⟨trivial, ?_, ?_, trivial⟩
      · rw [show (pref.length + 1) / 2 = pref.length / 2 by omega]
      · have h2 : (pref.length + 1) % 2 = 1 := by omega
        simp [hadv, h2]
    · simp +zetaDelta only [bne_iff_ne, ne_eq, Decidable.not_not] at *
      rw [hf, hw] at hop
      exact absurd hop (getV_cstep_none hs.end)
  case vc5 => exact .inl ⟨Nat.zero_le _, rfl⟩
  case vc6 =>
    rename_i st hinv
    rcases hinv with ⟨hk, -⟩ | ⟨hf, hw⟩
    · simp at hk; omega
    · rw [hf, hw]

theorem range_cursor {n cur : Nat} {pref suff : List Nat}
    (h : [0:n].toList = pref ++ cur :: suff) : cur = pref.length ∧ cur < n := by
  have h0 : [0:n].toList = List.range' 0 n := by simp [Std.Legacy.Range.toList]
  rw [h0] at h
  have h1 : (List.range' 0 n)[pref.length]? = some cur := by rw [h]; simp
  have hl := congrArg List.length h
  simp at hl
  rw [List.getElem?_range' (by omega)] at h1
  simp at h1; omega

section
variable {tabs : Tables} {ce : CheckEnv} {f F : Func}

theorem Inv.node_listed (hI : Inv tabs f F) {x r : ID} {n : Nat} (hx : Listed f x)
    (hs : Src (vw F) x r n) : ∀ k ≤ n, Listed f (node (vw F) k x)
  | 0, _ => hx
  | k + 1, hk => by
    obtain ⟨u, hu, -, ha⟩ := cstep_some_some (hs.pt_step (k := k) (by omega))
    exact hI.closed _ (hI.node_listed hx hs k (by omega)) u hu _ (by rw [ha]; simp)

theorem Inv.sizes (hI : Inv tabs f F) : F.valueTab.size = f.valueTab.size ∧ F.vidLast = f.vidLast := by
  have := hI.skel
  simp only [CopyElim.skel, Prod.mk.injEq] at this
  exact ⟨this.2.2.2.2.2.2, this.2.2.2.2.1⟩

/-- A chain from a listed value is shorter than `vid.last + 1`. -/
theorem Inv.chain_bound (hwf : WF ce f) (hfrag : CopyFrag tabs f) (hI : Inv tabs f F) {x r : ID}
    {n : Nat} (hx : Listed f x) (hs : Src (vw F) x r n) : n < F.vidLast + 1 := by
  have := hs.length_lt (N := f.valueTab.size) fun k hk => by
    obtain ⟨fv, hfv⟩ := listed_value hwf (hI.node_listed hx hs k hk)
    exact CheckFacts.lt_of_value? hfv
  have := hfrag.size
  rw [hI.sizes.2]
  omega

theorem cstep_eq_of_vw {G G' : Func} {x : ID} (h : vw G' x = vw G x) :
    cstep (vw G') x = cstep (vw G) x := by
  unfold cstep; rw [h]

theorem ops_setArg (G : Func) (v : ID) (i : Nat) (w x : ID) :
    (vw (G.setArg v i w) x).map (·.op) = (vw G x).map (·.op) := by
  rw [vw_setArg]
  unfold upd
  split
  · cases vw G x <;> rfl
  · rfl

/-- What `copySource`'s loop keeps (`G`: the current function). -/
structure CSInv (tabs : Tables) (f F : Func) (a : ID) (m : Nat) (G : Func) : Prop where
  inv : Inv tabs f G
  prsv : Prsv (vw F) (vw G)
  phi : ∀ x, (vw G x).any (·.op == .Phi) = true → (vw F x).any (·.op == .Phi) = true
  ops : ∀ x, (vw G x).map (·.op) = (vw F x).map (·.op)
  src : ∀ x r, (∃ n, Src (vw G) x r n) ↔ (∃ n, Src (vw F) x r n)
  other : ∀ x, (∀ j ≤ m, x ≠ node (vw F) j a) → vw G x = vw F x

theorem copySource_spec (hwf : WF ce f) (hfrag : CopyFrag tabs f) (hI : Inv tabs f F)
    {a y : ID} (ha : Listed f a) (hy : cstep (vw F) a = some (some y)) :
    ∃ w m, Src (vw F) a w (m + 1) ∧ (copySource F a).2 = w ∧
      CSInv tabs f F a m (copySource F a).1 := by
  obtain ⟨w, n0, hs⟩ := hI.acyc a ha
  cases hs with
  | sink h => rw [hy] at h; cases h
  | @step _ y' _ m hy' hs' =>
  rw [hy] at hy'; cases hy'
  have hs : Src (vw F) a w (m + 1) := .step hy hs'
  have hbound := hI.chain_bound hwf hfrag ha hs
  have hchase : CopyElim.chase F (F.getV a).args[0]! = (F, w) := by
    rw [(getV_cstep_some hy).2]
    exact chase_spec hs' (by omega)
  refine ⟨w, m, hs, ?_⟩
  generalize hres : copySource F a = res
  unfold copySource at hres
  rw [hchase] at hres
  apply Id.of_wp_run_eq hres
  mvcgen invariants
  · ⇓⟨cur, st⟩ => ⌜CSInv tabs f F a m st.1 ∧ ((cur.prefix.length ≤ m + 1 ∧
      st.2 = node (vw F) cur.prefix.length a ∧ ∀ j, cur.prefix.length ≤ j → j ≤ m + 1 →
        vw st.1 (node (vw F) j a) = vw F (node (vw F) j a)) ∨ st.2 = w)⌝
  case vc1 =>
    rename_i pref cur suff hxs b G v heq hinv
    simp +zetaDelta only [beq_iff_eq] at *
    exact ⟨hinv.1, .inr heq⟩
  case vc2 =>
    rename_i pref cur suff hxs b G v hne hinv
    simp +zetaDelta only [beq_iff_eq] at *
    obtain ⟨hP, hinv'⟩ := hinv
    obtain ⟨hk, hv, hlater⟩ := hinv'.resolve_right hne
    have hkm : pref.length ≤ m := by
      rcases Nat.lt_or_eq_of_le hk with h | h
      · omega
      · rw [h, hs.pt_last] at hv; exact absurd hv hne
    have hvF : vw b.1 b.2 = vw F b.2 := by rw [hv]; exact hlater _ (Nat.le_refl _) (by omega)
    have hstep := hs.pt_step (k := pref.length) (by omega)
    rw [← hv] at hstep
    obtain ⟨u, hu, -, hua⟩ := cstep_some_some hstep
    rw [← hvF] at hu
    have hvl : Listed f b.2 := by rw [hv]; exact hI.node_listed ha hs _ (by omega)
    have hn1 := hs.atNode (pref.length + 1) (by omega)
    obtain ⟨n', hn'⟩ := (hP.src _ _).2 ⟨_, hn1⟩
    obtain ⟨hI', hpr, hself, hphi, hsrc⟩ :=
      inv_setArg hwf hP.inv hvl hu (i := 0) (by rw [hua]; rfl) hn'
    have hrd : (b.1.getV b.2).args[0]! = node (vw F) (pref.length + 1) a := by
      rw [(getV_of_vw hu).2.1, hua]; rfl
    rw [hrd]
    have hoth : ∀ x, x ≠ b.2 → vw (b.1.setArg b.2 0 w) x = vw b.1 x := fun x hx => by
      rw [vw_setArg, upd_ne _ _ _ hx]
    refine ⟨⟨hI', hP.prsv.trans hpr, fun x hx => hP.phi x (hphi x hx), fun x => (ops_setArg _ _ _ _ x).trans (hP.ops x),
      fun x r => (hsrc x r).trans (hP.src x r), fun x hx => ?_⟩, .inl ⟨by simp; omega, by simp, ?_⟩⟩
    · rw [hoth x (by rw [hv]; exact hx _ hkm)]; exact hP.other x hx
    · intro j hj1 hj2
      simp only [List.length_append, List.length_singleton] at hj1
      rw [hoth _ (by
        rw [hv]; intro he
        have := hs.pt_inj hj2 (by omega) he
        omega)]
      exact hlater j (by omega) hj2
  case vc3 =>
    refine ⟨⟨hI, Prsv.refl _, fun _ => id, fun _ => rfl, fun _ _ => Iff.rfl, fun _ _ => rfl⟩,
      .inl ⟨Nat.zero_le _, rfl, fun _ _ _ => trivial⟩⟩
  case vc4 =>
    rename_i st hinv
    exact ⟨trivial, hinv.1⟩


/-- What `copyelimValue`'s loop keeps: arguments below `k` are non-copies. -/
structure CVInv (tabs : Tables) (f F : Func) (v : ID) (n k : Nat) (G : Func) : Prop where
  inv : Inv tabs f G
  prsv : Prsv (vw F) (vw G)
  phi : ∀ x, (vw G x).any (·.op == .Phi) = true → (vw F x).any (·.op == .Phi) = true
  ops : ∀ x, (vw G x).map (·.op) = (vw F x).map (·.op)
  size : ∃ u, vw G v = some u ∧ u.args.size = n
  sinks : ∀ u, vw G v = some u → ∀ j < k, ∀ c, u.args[j]? = some c → cstep (vw G) c = none

theorem copyelimValue_spec (hwf : WF ce f) (hfrag : CopyFrag tabs f) (hI : Inv tabs f F)
    {v : ID} (hv : Listed f v) :
    Inv tabs f (copyelimValue F v) ∧ Prsv (vw F) (vw (copyelimValue F v)) ∧
      (∀ x, (vw (copyelimValue F v) x).any (·.op == .Phi) = true →
        (vw F x).any (·.op == .Phi) = true) ∧
      (∀ x, (vw (copyelimValue F v) x).map (·.op) = (vw F x).map (·.op)) ∧
      AllSink (vw (copyelimValue F v)) [v] := by
  obtain ⟨fv, u0, hfv, hu0, -⟩ := hI.value hwf hv
  have hn : (F.getV v).args.size = u0.args.size := by rw [(getV_of_vw hu0).2.1]
  generalize hres : copyelimValue F v = res
  unfold copyelimValue at hres
  rw [hn] at hres
  apply Id.of_wp_run_eq hres
  mvcgen invariants
  · ⇓⟨cur, G⟩ => ⌜CVInv tabs f F v u0.args.size cur.prefix.length G⌝
  case vc1 =>
    rename_i pref cur suff hxs G a ha hcop hinv
    obtain ⟨rfl, hlt⟩ := range_cursor hxs
    obtain ⟨u, hu, hsz⟩ := hinv.size
    rw [(getV_of_vw hu).2.1] at ha
    have hal : Listed f a := hinv.inv.closed v hv u hu a (Array.mem_of_getElem? ha)
    obtain ⟨y, hy⟩ : ∃ y, cstep (vw G) a = some (some y) := by
      cases h : cstep (vw G) a with
      | none => exact absurd (by simpa using hcop) (getV_cstep_none h)
      | some o =>
        cases o with
        | some y => exact ⟨y, rfl⟩
        | none =>
          obtain ⟨r, n, hr⟩ := hinv.inv.acyc a hal
          exact absurd h (cstep_ne_some_none hr)
    obtain ⟨w, m, hs, hw2, hcs⟩ := copySource_spec hwf hfrag hinv.inv hal hy
    rw [hw2]
    have hnot : ∀ j ≤ m, v ≠ node (vw G) j a := by
      intro j hj he
      have hstep := hs.pt_step (k := j) (by omega)
      rw [← he] at hstep
      obtain ⟨u', hu', -, hua'⟩ := cstep_some_some hstep
      rw [hu] at hu'; cases hu'
      rw [hua'] at ha
      have ha0 : node (vw G) (j + 1) a = node (vw G) 0 a := by
        cases h : pref.length with
        | zero => rw [h] at ha; exact (by simpa using ha : node (vw G) (j + 1) a = a)
        | succ k => rw [h] at ha; simp at ha
      have := hs.pt_inj (by omega) (by omega) ha0
      omega
    have hu1 : vw (copySource G a).1 v = some u := by rw [hcs.other v hnot]; exact hu
    obtain ⟨n1, hs1⟩ := (hcs.src a w).2 ⟨m + 1, hs⟩
    obtain ⟨hI2, hpr2, hself2, hphi2, -⟩ := inv_setArg hwf hcs.inv hv hu1 ha hs1
    have hws : cstep (vw G) w = none := hs.end
    refine ⟨hI2, hinv.prsv.trans (hcs.prsv.trans hpr2),
      fun x hx => hinv.phi x (hcs.phi x (hphi2 x hx)),
      fun x => (ops_setArg _ _ _ _ x).trans ((hcs.ops x).trans (hinv.ops x)), ⟨_, hself2, by simp [hsz]⟩, ?_⟩
    intro u2 hu2 j hj c hc
    rw [hself2] at hu2; cases hu2
    simp only [List.length_append, List.length_singleton] at hj
    apply (hpr2.sinks c).2
    apply (hcs.prsv.sinks c).2
    by_cases hjc : pref.length = j
    · subst hjc
      dsimp only at hc
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self] at hc
      split at hc
      · cases hc; exact hws
      · cases hc
    · dsimp only at hc
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hjc] at hc
      exact hinv.sinks u hu j (by omega) c hc
  case vc2 =>
    rename_i pref cur suff hxs G a ha hncop hinv
    obtain ⟨rfl, hlt⟩ := range_cursor hxs
    obtain ⟨u, hu, hsz⟩ := hinv.size
    rw [(getV_of_vw hu).2.1] at ha
    have hal : Listed f a := hinv.inv.closed v hv u hu a (Array.mem_of_getElem? ha)
    have has : cstep (vw G) a = none := by
      cases h : cstep (vw G) a with
      | none => rfl
      | some o =>
        cases o with
        | some y => exact absurd (by simpa using (getV_cstep_some h).1) hncop
        | none =>
          obtain ⟨r, n, hr⟩ := hinv.inv.acyc a hal
          exact absurd h (cstep_ne_some_none hr)
    refine ⟨hinv.inv, hinv.prsv, hinv.phi, hinv.ops, hinv.size, ?_⟩
    intro u2 hu2 j hj c hc
    rw [hu] at hu2; cases hu2
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjc : j = pref.length
    · subst hjc; rw [ha] at hc; cases hc; exact has
    · exact hinv.sinks u hu j (by omega) c hc
  case vc3 =>
    rename_i pref cur suff hxs G o hno ho hinv
    obtain ⟨rfl, hlt⟩ := range_cursor hxs
    obtain ⟨u, hu, hsz⟩ := hinv.size
    rw [(getV_of_vw hu).2.1] at ho
    have : u.args[pref.length]? = some (u.args[pref.length]'(by omega)) := by simp
    rw [this] at ho
    exact absurd ho.symm (hno _)
  case vc4 =>
    exact ⟨hI, Prsv.refl _, fun _ => id, fun _ => rfl, ⟨u0, hu0, rfl⟩, fun _ _ j hj => absurd hj (by simp)⟩
  case vc5 =>
    rename_i G hinv
    have hl : [:u0.args.size].toList.length = u0.args.size := by simp [Std.Legacy.Range.toList]
    rw [hl] at hinv
    refine ⟨hinv.inv, hinv.prsv, hinv.phi, hinv.ops, ?_⟩
    intro x hx u hu c hc
    rw [List.mem_singleton] at hx
    subst hx
    obtain ⟨u', hu', hsz⟩ := hinv.size
    rw [hu] at hu'; cases hu'
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 hc
    exact hinv.sinks u hu j (by rw [← hsz]; exact (Array.getElem?_eq_some_iff.1 hj).1) c hj

end

end GoFV.Proof.CopyElim
