import GoFV.Proof.Pass.CopyElimInv

/-!
# The three edits keep `Inv`

`inv_setArg`: pointing argument `i` of a listed value at the end of that argument's chain;
`inv_empty`: resetting a zero-size listed value to `Empty`; `inv_phielim`: `phielimValue` of a
listed value whose arguments are non-copies.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.Opt GoFV.Proof

theorem keep_upd (V : ID → Option Value) (v : ID) (G : Value → Value)
    (hG : ∀ y, (G y).block = y.block ∧ (G y).type = y.type ∧ (G y).id = y.id) (x : ID) :
    (upd V v G x).map (fun u => (u.block, u.type, u.id)) =
      (V x).map (fun u => (u.block, u.type, u.id)) := by
  unfold upd
  split
  · cases V x with
    | none => rfl
    | some y => simp [hG y]
  · rfl

theorem phi_upd (V : ID → Option Value) (v : ID) (G : Value → Value)
    (hG : ∀ y, (G y).op = .Phi → y.op = .Phi) (x : ID) :
    (upd V v G x).any (·.op == .Phi) = true → (V x).any (·.op == .Phi) = true := by
  unfold upd
  split
  · cases V x with
    | none => simp
    | some y => simpa using hG y
  · exact id

theorem join_iff_of_src {V V' : ID → Option Value}
    (h : ∀ x r, (∃ n, Src V' x r n) ↔ (∃ n, Src V x r n)) {a c : ID} :
    Join V' a c ↔ Join V a c := by
  constructor
  · rintro ⟨r, n, m, h1, h2⟩
    obtain ⟨n', h1'⟩ := (h a r).1 ⟨n, h1⟩
    obtain ⟨m', h2'⟩ := (h c r).1 ⟨m, h2⟩
    exact ⟨r, n', m', h1', h2'⟩
  · rintro ⟨r, n, m, h1, h2⟩
    obtain ⟨n', h1'⟩ := (h a r).2 ⟨n, h1⟩
    obtain ⟨m', h2'⟩ := (h c r).2 ⟨m, h2⟩
    exact ⟨r, n', m', h1', h2'⟩

theorem cstep_ne_some_none {V : ID → Option Value} {x r : ID} {n : Nat} (h : Src V x r n) :
    cstep V x ≠ some none := by
  cases h with
  | sink h => rw [h]; simp
  | step h => rw [h]; simp

section
variable {tabs : Tables} {ce : CheckEnv} {f F : Func}

/-- Build `Inv` from facts about the view `V'` of `F'`. -/
theorem Inv.mk' {tabs : Tables} {f F' : Func} {V' : ID → Option Value} (hW : vw F' = V')
    (hs : CopyElim.skel F' = CopyElim.skel f)
    (keep : ∀ x, (V' x).map (fun u => (u.block, u.type, u.id)) =
      (vw f x).map (fun u => (u.block, u.type, u.id)))
    (mode : ∀ x, Listed f x → ∀ fv, f.value? x = some fv → ∃ v, V' x = some v ∧ Mode tabs V' fv v)
    (closed : ∀ x, Listed f x → ∀ v, V' x = some v → ∀ c ∈ v.args, Listed f c)
    (acyc : ∀ x, Listed f x → ∃ r n, Src V' x r n)
    (shape : ∀ x, Listed f x → ∀ w, cstep V' x = some (some w) →
      ∃ xv wv, f.value? x = some xv ∧ f.value? w = some wv ∧
        RetypeInto (tabs.ty wv.type) (tabs.ty xv.type))
    (ends : ∀ x r n, Src (vw f) x r n → NotPhi f r → ∃ m, Src V' x r m) :
    Inv tabs f F' := by
  subst hW; exact ⟨hs, keep, mode, closed, acyc, shape, ends⟩

/-! ## `setArg` to the end of the argument's chain -/

theorem inv_setArg (hwf : WF ce f) (hI : Inv tabs f F) {v : ID} (hv : Listed f v) {u : Value}
    (hu : vw F v = some u) {i : Nat} {c w : ID} (hc : u.args[i]? = some c) {n : Nat}
    (hcw : Src (vw F) c w n) :
    Inv tabs f (F.setArg v i w) ∧ Prsv (vw F) (vw (F.setArg v i w)) ∧
      vw (F.setArg v i w) v = some { u with args := u.args.set! i w } ∧
      (∀ x, (vw (F.setArg v i w) x).any (·.op == .Phi) = true →
        (vw F x).any (·.op == .Phi) = true) ∧
      (∀ x r, (∃ n, Src (vw (F.setArg v i w)) x r n) ↔ (∃ n, Src (vw F) x r n)) := by
  have hV' := vw_setArg F v i w
  generalize hG : (fun y : Value => { y with args := y.args.set! i w }) = G at hV'
  have hGu : ∀ y, G y = { y with args := y.args.set! i w } := fun y => by rw [← hG]
  generalize hW : vw (F.setArg v i w) = V' at hV' ⊢
  subst hV'
  have hself : upd (vw F) v G v = some (G u) := by rw [upd_self, hu]; rfl
  have hne : ∀ x, x ≠ v → cstep (upd (vw F) v G) x = cstep (vw F) x := fun x hx => cstep_upd_ne (vw F) v G hx
  have hcl : Listed f c := hI.closed v hv u hu c (Array.mem_of_getElem? hc)
  -- how the chains change
  obtain ⟨hsrc, hsink, hcopy⟩ : (∀ x r, (∃ n, Src (upd (vw F) v G) x r n) ↔ (∃ n, Src (vw F) x r n)) ∧
      (∀ x, cstep (upd (vw F) v G) x = none ↔ cstep (vw F) x = none) ∧
      (u.op = .Copy → u.args = #[c] ∧ i = 0 ∧ Src (vw F) v w (n + 1) ∧
        cstep (upd (vw F) v G) v = some (some w)) := by
    by_cases hop : u.op = .Copy
    · obtain ⟨r0, n0, hs0⟩ := hI.acyc v hv
      have hn := cstep_ne_some_none hs0
      unfold cstep at hn
      rw [hu] at hn
      simp only [hop, ite_true, ne_eq, Option.some.injEq] at hn
      obtain ⟨y, hy⟩ : ∃ y, cstep (vw F) v = some (some y) := by
        unfold cstep; rw [hu]; simp only [hop, ite_true]
        split
        · rename_i hs; exact ⟨u.args[0], by simp [hs]⟩
        · rename_i hs; exact absurd (ite_eq_right hs) hn
      obtain ⟨u', hu', -, ha⟩ := cstep_some_some hy
      rw [hu] at hu'; cases hu'
      rw [ha] at hc
      obtain ⟨rfl, rfl⟩ : i = 0 ∧ c = y := by
        cases i with
        | zero => simp at hc; exact ⟨rfl, hc.symm⟩
        | succ i => simp at hc
      have hvw : Src (vw F) v w (n + 1) := .step hy hcw
      have h' : cstep (upd (vw F) v G) v = some (some w) := by
        refine cstep_of_copy hself ?_ ?_
        · rw [← hG]; exact hop
        · rw [← hG]; simp [ha]
      refine ⟨fun x r => src_retarget hvw h' hne, fun x => ?_, fun _ => ⟨ha, rfl, hvw, h'⟩⟩
      by_cases hxv : x = v
      · subst hxv; rw [h', hy]; simp
      · rw [hne x hxv]
    · have h' : cstep (upd (vw F) v G) v = none := by
        refine cstep_of_ne hself ?_
        rw [← hG]; exact hop
      have hall : ∀ x, cstep (upd (vw F) v G) x = cstep (vw F) x := by
        intro x
        by_cases hxv : x = v
        · subst hxv; rw [h', cstep_of_ne hu hop]
        · exact hne x hxv
      refine ⟨fun x r => ⟨fun ⟨n, h⟩ => ⟨n, src_congr (fun y => (hall y).symm) h⟩,
        fun ⟨n, h⟩ => ⟨n, src_congr hall h⟩⟩, fun x => by rw [hall], fun h => absurd h hop⟩
  have hjoin : ∀ a c, Join (vw F) a c → Join (upd (vw F) v G) a c := fun a c h =>
    (join_iff_of_src hsrc).2 h
  have hwl : Listed f w := hI.src_listed hcl hcw
  have hargs : ∀ c' ∈ (G u).args, c' ∈ u.args ∨ c' = w := by
    intro c' h'
    rw [← hG] at h'
    exact Array.mem_or_eq_of_mem_setIfInBounds h'
  refine ⟨Inv.mk' hW ?_ ?_ ?_ ?_ ?_ ?_ ?_, ⟨hsink, ?_⟩, by rw [hself, ← hG], ?_, hsrc⟩
  · rw [skel_setArg]; exact hI.skel
  · intro x
    rw [keep_upd (vw F) v G (by intro y; rw [← hG]; exact ⟨rfl, rfl, rfl⟩)]
    exact hI.keep x
  · intro x hx fv hfv
    obtain ⟨u0, hu0, hm⟩ := hI.mode x hx fv hfv
    by_cases hxv : x = v
    · subst hxv
      rw [hu] at hu0; cases hu0
      refine ⟨G u, hself, ?_⟩
      rw [hGu u]
      cases hm with
      | same h1 h2 h3 h4 h5 =>
        refine .same h1 h2 h3 (by simp [h4]) fun k a c' ha hc' => ?_
        by_cases hk : i = k
        · subst hk
          dsimp only at hc'; rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self] at hc'
          split at hc'
          · cases hc'
            exact hjoin _ _ ((h5 i a c ha hc).trans_src hcw)
          · cases hc'
        · dsimp only at hc'; rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hk] at hc'
          exact hjoin _ _ (h5 k a c' ha hc')
      | phi w0 h1 h2 h3 h4 h5 =>
        rw [h3] at hc
        obtain ⟨rfl, rfl⟩ : i = 0 ∧ c = w0 := by
          cases i with
          | zero => simp at hc; exact ⟨rfl, hc.symm⟩
          | succ i => simp at hc
        refine .phi w h1 h2 (by simp [h3]) h4 fun a ha => hjoin _ _ ((h5 a ha).trans_src hcw)
      | empty h1 h2 h3 => rw [h3] at hc; simp at hc
    · refine ⟨u0, by rw [upd_ne (vw F) v G hxv]; exact hu0, hm.mono hjoin⟩
  · intro x hx u' hu' c' hc'
    by_cases hxv : x = v
    · subst hxv
      rw [hself] at hu'; cases hu'
      rcases hargs c' hc' with h | rfl
      · exact hI.closed _ hx u hu c' h
      · exact hwl
    · rw [upd_ne (vw F) v G hxv] at hu'
      exact hI.closed x hx u' hu' c' hc'
  · intro x hx
    obtain ⟨r, m, h⟩ := hI.acyc x hx
    obtain ⟨m', h'⟩ := (hsrc x r).2 ⟨m, h⟩
    exact ⟨r, m', h'⟩
  · intro x hx w' hw'
    by_cases hxv : x = v
    · subst hxv
      by_cases hop : u.op = .Copy
      · obtain ⟨-, -, hvw, h'⟩ := hcopy hop
        rw [h'] at hw'; cases hw'
        exact hI.src_shape hwf hx hvw
      · have h' := (hsink x).2 (cstep_of_ne hu hop)
        rw [h'] at hw'; cases hw'
    · rw [hne x hxv] at hw'
      exact hI.shape x hx w' hw'
  · intro x r n h hr
    obtain ⟨m, h'⟩ := hI.ends x r n h hr
    exact (hsrc x r).2 ⟨m, h'⟩
  · intro x u' hu' c' hc'
    by_cases hxv : x = v
    · subst hxv
      rw [hself] at hu'; cases hu'
      rcases hargs c' hc' with h | rfl
      · exact .inl ⟨u, hu, h⟩
      · exact .inr ((hsink _).2 hcw.end)
    · rw [upd_ne (vw F) v G hxv] at hu'
      exact .inl ⟨u', hu', hc'⟩
  · exact phi_upd (vw F) v G (by intro y; rw [← hG]; exact id)

/-! ## The zero-size reset -/

theorem inv_empty (hfrag : CopyFrag tabs f) (hI : Inv tabs f F) {v : ID}
    (hv : Listed f v) {fv : Value} (hfv : f.value? v = some fv) (hz : zeroSize tabs fv.type) :
    Inv tabs f (F.resetValue v .Empty) ∧ Prsv (vw F) (vw (F.resetValue v .Empty)) ∧
      (∀ x, (vw (F.resetValue v .Empty) x).any (·.op == .Phi) = true →
        (vw F x).any (·.op == .Phi) = true) := by
  have hV' := vw_resetValue F v .Empty
  generalize hG :
      (fun y : Value => { y with op := .Empty, args := #[], auxInt := 0, aux := none }) = G at hV'
  have hGu : ∀ y, G y = { y with op := .Empty, args := #[], auxInt := 0, aux := none } :=
    fun y => by rw [← hG]
  obtain ⟨u, hu, hm⟩ := hI.mode v hv fv hfv
  generalize hW : vw (F.resetValue v .Empty) = V' at hV' ⊢
  subst hV'
  have hself : upd (vw F) v G v = some (G u) := by rw [upd_self, hu]; rfl
  have hop : u.op ≠ .Copy := by
    cases hm with
    | same h1 =>
      rw [h1]; intro hc
      exact hfrag.copyNZ v hv fv hfv hc hz
    | phi _ _ _ _ h4 => exact absurd hz h4
    | empty _ h2 => rw [h2]; decide
  have hall : ∀ x, cstep (upd (vw F) v G) x = cstep (vw F) x := by
    intro x
    by_cases hxv : x = v
    · subst hxv
      rw [cstep_of_ne hself (by rw [hGu]; exact (by decide : Op.Empty ≠ Op.Copy)), cstep_of_ne hu hop]
    · exact cstep_upd_ne (vw F) v G hxv
  have hsrc : ∀ x r, (∃ n, Src (upd (vw F) v G) x r n) ↔ (∃ n, Src (vw F) x r n) := fun x r =>
    ⟨fun ⟨n, h⟩ => ⟨n, src_congr (fun y => (hall y).symm) h⟩,
      fun ⟨n, h⟩ => ⟨n, src_congr hall h⟩⟩
  have hjoin : ∀ a c, Join (vw F) a c → Join (upd (vw F) v G) a c := fun a c h =>
    (join_iff_of_src hsrc).2 h
  have hnil : (G u).args = #[] := by rw [← hG]
  refine ⟨Inv.mk' hW ?_ ?_ ?_ ?_ ?_ ?_ ?_, ⟨fun x => by rw [hall], ?_⟩, ?_⟩
  · rw [skel_resetValue]; exact hI.skel
  · intro x
    rw [keep_upd (vw F) v G (by intro y; rw [← hG]; exact ⟨rfl, rfl, rfl⟩)]
    exact hI.keep x
  · intro x hx fv' hfv'
    by_cases hxv : x = v
    · subst hxv
      rw [hfv] at hfv'; cases hfv'
      exact ⟨G u, hself, .empty hz (by rw [← hG]) hnil⟩
    · obtain ⟨u0, hu0, hm0⟩ := hI.mode x hx fv' hfv'
      exact ⟨u0, by rw [upd_ne (vw F) v G hxv]; exact hu0, hm0.mono hjoin⟩
  · intro x hx u' hu' c' hc'
    by_cases hxv : x = v
    · subst hxv
      rw [hself] at hu'; cases hu'
      rw [hnil] at hc'; simp at hc'
    · rw [upd_ne (vw F) v G hxv] at hu'
      exact hI.closed x hx u' hu' c' hc'
  · intro x hx
    obtain ⟨r, m, h⟩ := hI.acyc x hx
    obtain ⟨m', h'⟩ := (hsrc x r).2 ⟨m, h⟩
    exact ⟨r, m', h'⟩
  · intro x hx w' hw'
    rw [hall] at hw'
    exact hI.shape x hx w' hw'
  · intro x r n h hr
    obtain ⟨m, h'⟩ := hI.ends x r n h hr
    exact (hsrc x r).2 ⟨m, h'⟩
  · intro x u' hu' c' hc'
    by_cases hxv : x = v
    · subst hxv
      rw [hself] at hu'; cases hu'
      rw [hnil] at hc'; simp at hc'
    · rw [upd_ne (vw F) v G hxv] at hu'
      exact .inl ⟨u', hu', hc'⟩
  · exact phi_upd (vw F) v G (by intro y; rw [← hG]; intro h; cases h)

/-! ## The phi-to-copy step -/

/-- The step of `phielimValue`'s fold. -/
def phiStep (v : ID) (w : Option (Option ID)) (a : ID) : Option (Option ID) :=
  if a == v then w else
  match w with
  | none => some (some a)
  | some (some w') => if a == w' then w else some none
  | some none => w

theorem phiStep_fold (v w : ID) : ∀ (l : List ID) (init : Option (Option ID)),
    l.foldl (phiStep v) init = some (some w) →
      init ≠ some none ∧ (∀ a ∈ l, a = v ∨ a = w) ∧ (init = none → w ≠ v ∧ w ∈ l) ∧
      (∀ w0, init = some (some w0) → w = w0)
  | [], init, h => by
    simp only [List.foldl_nil] at h
    subst h
    refine ⟨by simp, by simp, by simp, fun w0 h0 => ?_⟩
    simpa using h0
  | a :: l, init, h => by
    rw [List.foldl_cons] at h
    obtain ⟨h1, h2, h3, h4⟩ := phiStep_fold v w l _ h
    by_cases hav : a = v
    · have he : phiStep v init a = init := by simp [phiStep, hav]
      rw [he] at h1 h3 h4
      refine ⟨h1, ?_, fun hn => ?_, h4⟩
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact .inl hav
        · exact h2 b hb
      · obtain ⟨h5, h6⟩ := h3 hn
        exact ⟨h5, List.mem_cons_of_mem _ h6⟩
    · have hav' : (a == v) = false := by simpa using hav
      match init, h1, h2, h3, h4 with
      | none, h1, h2, h3, h4 =>
        have hw : w = a := h4 a (by simp [phiStep, hav'])
        subst hw
        refine ⟨by simp, ?_, fun _ => ⟨hav, List.mem_cons_self⟩, fun w0 h0 => by cases h0⟩
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact .inr rfl
        · exact h2 b hb
      | some (some w1), h1, h2, h3, h4 =>
        by_cases haw : a = w1
        · subst haw
          have he : phiStep v (some (some a)) a = some (some a) := by simp [phiStep, hav']
          rw [he] at h4
          have hw : w = a := h4 a rfl
          subst hw
          refine ⟨by simp, ?_, (fun h0 => by cases h0), fun w0 h0 => by simpa using h0⟩
          intro b hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact .inr rfl
          · exact h2 b hb
        · have haw' : (a == w1) = false := by simpa using haw
          have he : phiStep v (some (some w1)) a = some none := by simp [phiStep, hav', haw']
          exact absurd he h1
      | some none, h1, _, _, _ =>
        exact absurd (by simp [phiStep, hav']) h1

theorem phielimValue_cases (F : Func) (v : ID) :
    F.phielimValue v = (F, false) ∨
    ∃ w, (F.getV v).op = .Phi ∧ w ∈ (F.getV v).args ∧ w ≠ v ∧
      (∀ a ∈ (F.getV v).args, a = v ∨ a = w) ∧
      F.phielimValue v = ((F.modV v fun y => { y with op := .Copy }).setArgs1 v w, true) := by
  unfold Func.phielimValue
  dsimp only
  split
  · exact .inl rfl
  · rename_i hop
    split
    · rename_i w heq
      have hf := phiStep_fold v w (F.getV v).args.toList none
        (by rw [Array.foldl_toList]; exact heq)
      obtain ⟨-, h2, h3, -⟩ := hf
      obtain ⟨h5, h6⟩ := h3 rfl
      refine .inr ⟨w, by simpa using hop, by simpa using h6, h5, fun a ha => h2 a (by simpa using ha),
        rfl⟩
    · exact .inl rfl

theorem inv_phielim (hwf : WF ce f) (hfrag : CopyFrag tabs f) (hI : Inv tabs f F) {v : ID}
    (hv : Listed f v) {fv : Value} (hfv : f.value? v = some fv) (hz : ¬ zeroSize tabs fv.type)
    (hs : AllSink (vw F) [v]) :
    Inv tabs f (F.phielimValue v).1 ∧ AllSink (vw (F.phielimValue v).1) [v] ∧
      ((F.phielimValue v).2 = false → (F.phielimValue v).1 = F) ∧
      (∀ x, (vw (F.phielimValue v).1 x).any (·.op == .Phi) = true →
        (vw F x).any (·.op == .Phi) = true) ∧
      ((F.phielimValue v).2 = true → (vw F v).any (·.op == .Phi) = true ∧
        (vw (F.phielimValue v).1 v).any (·.op == .Phi) = false) := by
  rcases phielimValue_cases F v with h | ⟨w, hop, hw, hwv, hall, h⟩
  · rw [h]
    exact ⟨hI, hs, fun _ => rfl, fun _ => id, fun h => by cases h⟩
  rw [h]
  dsimp only
  obtain ⟨u, hu, hm⟩ := hI.mode v hv fv hfv
  obtain ⟨hgo, hga, -⟩ := getV_of_vw hu
  rw [hgo] at hop
  rw [hga] at hw hall
  have hV' := vw_toCopy F v w
  generalize hG : (fun y : Value => { y with op := .Copy, args := #[w] }) = G at hV'
  have hGu : ∀ y, G y = { y with op := .Copy, args := #[w] } := fun y => by rw [← hG]
  generalize hW : vw ((F.modV v fun y => { y with op := .Copy }).setArgs1 v w) = V' at hV' ⊢
  subst hV'
  have hself : upd (vw F) v G v = some (G u) := by rw [upd_self, hu]; rfl
  have hne : ∀ x, x ≠ v → cstep (upd (vw F) v G) x = cstep (vw F) x := fun x hx =>
    cstep_upd_ne (vw F) v G hx
  have hvs : cstep (vw F) v = none := cstep_of_ne hu (by rw [hop]; decide)
  have hws : cstep (vw F) w = none := hs v (List.mem_singleton_self v) u hu w hw
  have hws' : cstep (upd (vw F) v G) w = none := by rw [hne w hwv]; exact hws
  have h' : cstep (upd (vw F) v G) v = some (some w) := cstep_of_copy hself (by rw [hGu])
    (by rw [hGu])
  have hjoin : ∀ a c, Join (vw F) a c → Join (upd (vw F) v G) a c := fun a c h =>
    join_link hvs hws hwv h' hne h
  have hlink : ∀ {x r n}, Src (vw F) x r n → ∃ n', Src (upd (vw F) v G) x (if r = v then w else r) n' :=
    fun h => src_link hvs hws hwv h' hne h
  -- `v` was a phi in the `same` mode
  obtain ⟨h1, h4, h5⟩ : u.op = fv.op ∧ u.args.size = fv.args.size ∧
      ∀ (k : Nat) (a c : ID), fv.args[k]? = some a → u.args[k]? = some c → Join (vw F) a c := by
    cases hm with
    | same h1 _ _ h4 h5 => exact ⟨h1, h4, h5⟩
    | phi _ _ h2 => rw [hop] at h2; cases h2
    | empty _ h2 => rw [hop] at h2; cases h2
  have hfop : fv.op = .Phi := h1 ▸ hop
  -- every argument of `fv` joins `w` afterwards
  have hjw : ∀ a ∈ fv.args, Join (upd (vw F) v G) a w := by
    intro a ha
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha
    obtain ⟨c, hc⟩ : ∃ c, u.args[k]? = some c := by
      have : k < fv.args.size := (Array.getElem?_eq_some_iff.1 hk).1
      exact ⟨u.args[k]'(by omega), by simp⟩
    have hj := h5 k a c hk hc
    rcases hall c (Array.mem_of_getElem? hc) with rfl | rfl
    · obtain ⟨n, hn⟩ := hj.sink hvs
      obtain ⟨n', hn'⟩ := hlink hn
      rw [ite_eq_left (Eq.refl _)] at hn'
      exact ⟨w, n', 0, hn', .sink hws'⟩
    · exact hjoin _ _ hj
  have hwl : Listed f w := hI.closed v hv u hu w hw
  -- a `Stable` phi is not turned into a copy: its two chain ends would both be `w`
  have notStable : ¬ Stable f fv := by
    rintro ⟨a₁, ha₁, a₂, ha₂, r₁, r₂, n₁, n₂, hs₁, hs₂, hne₁₂, hp₁, hp₂⟩
    have hend : ∀ a ∈ fv.args, ∀ r n, Src f.value? a r n → NotPhi f r → r = w := by
      intro a ha r n hs hp
      obtain ⟨m, hm⟩ := hI.ends a r n (src_congr (by intro y; rw [cstep_vw]) hs) hp
      obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha
      obtain ⟨c, hc⟩ : ∃ c, u.args[k]? = some c := by
        have : k < fv.args.size := (Array.getElem?_eq_some_iff.1 hk).1
        exact ⟨u.args[k]'(by omega), by simp⟩
      have hj := h5 k a c hk hc
      rcases hall c (Array.mem_of_getElem? hc) with rfl | rfl
      · obtain ⟨n', hn'⟩ := hj.sink hvs
        have := (hm.unique hn').1
        subst this
        exact absurd hfop (hp fv hfv)
      · obtain ⟨n', hn'⟩ := hj.sink hws
        exact (hm.unique hn').1
    exact hne₁₂ ((hend a₁ ha₁ r₁ n₁ hs₁ hp₁).trans (hend a₂ ha₂ r₂ n₂ hs₂ hp₂).symm)
  refine ⟨Inv.mk' hW ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_, (fun h => by cases h), ?_, fun _ => ⟨?_, ?_⟩⟩
  · rw [skel_toCopy]; exact hI.skel
  · intro x
    rw [keep_upd (vw F) v G (by intro y; rw [hGu]; exact ⟨rfl, rfl, rfl⟩)]
    exact hI.keep x
  · intro x hx fv' hfv'
    by_cases hxv : x = v
    · subst hxv
      rw [hfv] at hfv'; cases hfv'
      exact ⟨G u, hself, .phi w hfop (by rw [hGu]) (by rw [hGu]) hz hjw⟩
    · obtain ⟨u0, hu0, hm0⟩ := hI.mode x hx fv' hfv'
      exact ⟨u0, by rw [upd_ne (vw F) v G hxv]; exact hu0, hm0.mono hjoin⟩
  · intro x hx u' hu' c' hc'
    by_cases hxv : x = v
    · subst hxv
      rw [hself] at hu'; cases hu'
      rw [hGu] at hc'
      simp only [List.mem_toArray, List.mem_singleton] at hc'
      subst hc'; exact hwl
    · rw [upd_ne (vw F) v G hxv] at hu'
      exact hI.closed x hx u' hu' c' hc'
  · intro x hx
    obtain ⟨r, m, hr⟩ := hI.acyc x hx
    obtain ⟨m', hr'⟩ := hlink hr
    exact ⟨_, m', hr'⟩
  · intro x hx w' hw'
    by_cases hxv : x = v
    · subst hxv
      rw [h'] at hw'; cases hw'
      obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 hw
      obtain ⟨a, ha⟩ : ∃ a, fv.args[k]? = some a := by
        have : k < u.args.size := (Array.getElem?_eq_some_iff.1 hk).1
        exact ⟨fv.args[k]'(by omega), by simp⟩
      obtain ⟨n, hn⟩ := (h5 k a w ha hk).sink hws
      obtain ⟨bid, b, hb, hxb⟩ := hx
      have hal : Listed f a := hwf.argListed bid b x fv ⟨hb, hxb, hfv⟩ a (Array.mem_of_getElem? ha)
      obtain ⟨av, wv, hav, hwv', hty⟩ := hI.src_shape hwf hal hn
      obtain ⟨av', hav', hty'⟩ := hfrag.shape x ⟨bid, b, hb, hxb⟩ fv hfv
        (.inr ⟨hfop, fun hst => notStable hst⟩) a (Array.mem_of_getElem? ha)
      rw [hav] at hav'; cases hav'
      exact ⟨fv, wv, hfv, hwv', hty.trans hty'⟩
    · rw [hne x hxv] at hw'
      exact hI.shape x hx w' hw'
  · intro x r n hs hr
    obtain ⟨m, hm⟩ := hI.ends x r n hs hr
    obtain ⟨m', hm'⟩ := hlink hm
    have hrv : r ≠ v := fun he => hr fv (he ▸ hfv) hfop
    simp only [hrv, ↓reduceIte] at hm'
    exact ⟨m', hm'⟩
  · intro x hx u' hu' c' hc'
    rw [List.mem_singleton] at hx
    subst hx
    rw [hself] at hu'; cases hu'
    rw [hGu] at hc'
    simp only [List.mem_toArray, List.mem_singleton] at hc'
    subst hc'; exact hws'
  · exact phi_upd (vw F) v G (by intro y; rw [hGu]; intro h; cases h)
  · rw [hu]; simp [hop]
  · rw [hself, hGu]; rfl

end

end GoFV.Proof.CopyElim
