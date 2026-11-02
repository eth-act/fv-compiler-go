import GoFV.Proof.Pass.RewriteTermReplay
import GoFV.Proof.Rules.DecShape

/-!
# Replaying a selection of a `Make` (issue #17)

A rule event accepted by `RewriteCheck.makeSelOK` (a selection rule over a `Make` with a copy
result, `makeSelShape`: `(ITab (IMake itab _)) => itab`, the variadic `(StructSelect [i]
x:(StructMake ___)) => x.Args[i]` of `dec.rules:106`/`generic.rules:973`, …) redefines the
selection `v` of component `k` of `s` as `Copy a` of argument `k` of the `Make` that `s`
resolves to (`selRes`: through compatible copies, `den_copy`, and selections of a `Make`'s
argument, `SAFacts.den_le`; `selRes_den`: the resolved value's denotation refines `s`'s, issue
#17). `MSFacts.step`: on a set closed under arguments, every denotation after the event refines
the one before at the same fuel (`select_retype_make_get` at `v`: component `k` of the retyped
`Make` is `a` retyped at the field's shape, which keeps `a`'s denotation since `a`'s shape is
the field's and `v`'s, or `a` is a 64-bit integer word (`intWord`: an integer, a global
pointer, or a `Convert`/`Copy` of one; `intWord_den`) under word shapes (`retype_word`);
monotonicity elsewhere). `ReplayInv.makeSel`: the event keeps the replay invariant.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim

/-- A selection op (`selIndex?`) is a pure term op selecting its component `k`. -/
theorem sel_facts {op : Op} {ai : Int64} {k : Nat} (h : selIndex? op ai = some k) :
    termOp op = true ∧ GoFV.Proof.Rules.frameOp op = false ∧
      ∀ ty aux args, evalPure op ty ai aux args = Comp.select k args := by
  cases op <;> simp only [selIndex?, reduceCtorEq, Option.some.injEq] at h
  all_goals first
    | (subst h; exact ⟨by decide, by decide, fun _ _ _ => rfl⟩)
    | (refine ⟨by decide, by decide, fun _ _ args => ?_⟩
       show Comp.selectAux ai args = _
       unfold Comp.selectAux
       split at h
       · cases h
       · rename_i hn
         simp only [Option.some.injEq] at h
         subst h
         simp [hn])

/-- A `Make` op is a pure term op building its arguments' aggregate. -/
theorem make_facts {op : Op} (h : GoFV.Proof.Rules.makeOp op = true) :
    termOp op = true ∧ GoFV.Proof.Rules.frameOp op = false ∧
      ∀ ty ai aux args, evalPure op ty ai aux args = Comp.make args := by
  cases op <;> simp only [GoFV.Proof.Rules.makeOp, reduceCtorEq] at h
  all_goals exact ⟨by decide, by decide, fun _ _ _ _ => rfl⟩

/-- What `selArg tabs M r x = some a` establishes: `x` selects component `k` of `s`, `r s` is a
`Make` `y` whose argument `k` is `a`, with the shape conditions. -/
structure SAFacts (tabs : Tables) (M : Defs) (r : ID → ID) (x : Value) (a : ID) where
  s : ID
  y : Value
  k : Nat
  w : Value
  hxargs : x.args.toList = [s]
  hk : selIndex? x.op x.auxInt = some k
  hy : M.get? (r s) = some y
  ha : y.args[k]? = some a
  hw : M.get? a = some w
  hyop : GoFV.Proof.Rules.makeOp y.op = true
  hsh : ∀ fk, GoFV.Proof.Rules.fieldShape? (tabs.ty y.type) k = some fk →
    (GoFV.Proof.Rules.shapeSub (tabs.ty w.type) fk = true ∧
      GoFV.Proof.Rules.shapeSub (tabs.ty w.type) (tabs.ty x.type) = true) ∨
    (intWord tabs M 4 a = true ∧ wordTy fk = true ∧ wordTy (tabs.ty x.type) = true)

theorem saFacts {tabs : Tables} {M : Defs} {r : ID → ID} {x : Value} {a : ID}
    (h : selArg tabs M r x = some a) : Nonempty (SAFacts tabs M r x a) := by
  unfold selArg at h
  split at h
  · rename_i s k hxargs hk
    split at h
    · rename_i y hy
      split at h
      · rename_i a' ha
        split at h
        · rename_i w hw
          split at h
          · rename_i hc
            cases h
            unfold selArgOK at hc
            simp only [Bool.and_eq_true] at hc
            obtain ⟨hyop, hsh⟩ := hc
            refine ⟨⟨s, y, k, w, hxargs, hk, hy, ha, hw, hyop, fun fk hf => ?_⟩⟩
            rw [hf] at hsh
            simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, and_assoc] using hsh
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- What `makeSelOK` establishes about an event `(v, [u])`: `v`'s selection `x` reads `a`
(`selArg`, its argument resolved by `selRes`), and `u` is `v` as `Copy a` at `a`'s type. -/
structure MSFacts (tabs : Tables) (M : Defs) (v : ID) (u : Value) where
  x : Value
  a : ID
  hx : M.get? v = some x
  sa : SAFacts tabs M (selRes tabs M selFuel) x a
  hid : u.id = v
  huop : u.op = .Copy
  huargs : u.args = #[a]
  huty : u.type = sa.w.type

theorem msFacts {tabs : Tables} {M : Defs} {v : ID} {defs : List Value}
    (h : makeSelOK tabs M v defs = true) : ∃ u, defs = [u] ∧ Nonempty (MSFacts tabs M v u) := by
  unfold makeSelOK at h
  split at h
  · rename_i x u hx
    split at h
    · rename_i a hsa
      split at h
      · rename_i w hw
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨hid, huop⟩, huargs⟩, huty⟩ := h
        obtain ⟨F⟩ := saFacts hsa
        have hww : F.w = w := Option.some.inj (F.hw.symm.trans hw)
        exact ⟨u, rfl, ⟨⟨x, a, hx, F, hid, huop, huargs, hww ▸ huty⟩⟩⟩
      · cases h
    · cases h
  · cases h

section SA

variable {tabs : Tables} {M : Defs} {r : ID → ID} {x : Value} {a : ID}

theorem SAFacts.y_term (F : SAFacts tabs M r x a) : termOp F.y.op = true :=
  (make_facts F.hyop).1

/-- The selected argument is in a set closed under arguments that holds `x`'s arguments, if the
resolver stays in it. -/
theorem SAFacts.a_mem (F : SAFacts tabs M r x a) {C : ID → Prop} (hC : DefClosed M C)
    (hr : ∀ z, C z → C (r z)) (hargs : ∀ b ∈ x.args, C b) : C a := by
  have hs : C F.s := hargs _ (Array.mem_toList_iff.1 (by rw [F.hxargs]; exact List.mem_singleton_self _))
  obtain ⟨m', hm', hargs'⟩ := hC _ (hr _ hs)
  rw [F.hy] at hm'; cases hm'
  exact hargs' _ (Array.mem_of_getElem? F.ha)

/-- At the resolved `Make`: its selection is refined by `a`'s denotation. -/
theorem SAFacts.sel_ref (F : SAFacts tabs M r x a) {ρ : ID → Val}
    (hT : Term.Typed M.get? tabs ρ) (m : Nat) {z : Val} (hz : Sem.Refines (den M.get? tabs ρ m a) z) :
    Sem.Refines ((Comp.select F.k [den M.get? tabs ρ (m + 1) (r F.s)]).retype
      (tabs.ty x.type)) (z.retype (tabs.ty F.w.type)) := by
  rw [den_succ_term F.hy F.y_term, GoFV.Proof.Rules.opVal_pure (make_facts F.hyop).2.1,
    (make_facts F.hyop).2.2]
  rcases GoFV.Proof.Rules.select_retype_make_get (tabs.ty F.y.type) F.k
      (F.y.args.toList.map (den M.get? tabs ρ m)) with h | ⟨f, z', hf, hz', he⟩
  · rw [h, retype_poison]; exact .poison _
  · rw [he]
    have hz'' : z' = den M.get? tabs ρ m a := by
      rw [List.getElem?_map, Array.getElem?_toList, F.ha] at hz'
      simp only [Option.map_some, Option.some.injEq] at hz'
      exact hz'.symm
    subst hz''
    have hfix : (den M.get? tabs ρ m a).retype (tabs.ty F.w.type) = den M.get? tabs ρ m a := by
      rw [← shape_of (tabs := tabs) F.hw]
      exact den_retype hT m a (by rw [F.hw]; rfl)
    have hkeep : ((den M.get? tabs ρ m a).retype f).retype (tabs.ty x.type) =
        den M.get? tabs ρ m a := by
      rcases F.hsh f hf with ⟨h1, h2⟩ | ⟨hi, h1, h2⟩
      · have hty : (den M.get? tabs ρ m a).hasTy (tabs.ty F.w.type) = true := by
          rw [← hfix]; exact Val.retype_hasTy _ _
        rw [GoFV.Proof.Rules.retype_of_shapeSub hty h1, GoFV.Proof.Rules.retype_of_shapeSub hty h2]
      · have hg := intWord_den (tabs := tabs) (ρ := ρ) hT 4 a m hi
        rw [retype_word h1 hg, retype_word h2 hg]
    rw [hkeep, ← hfix]
    exact retype_mono _ hz

/-- The selection `x` at `n + 1` is refined by its value at the resolved argument, if the
resolver refines denotations: `Comp.select` of a larger aggregate. -/
theorem SAFacts.sel_mono (F : SAFacts tabs M r x a) {ρ : ID → Val}
    (hr : ∀ k z, Sem.Refines (den M.get? tabs ρ k z) (den M.get? tabs ρ k (r z))) (n : Nat) :
    Sem.Refines ((GoFV.Proof.Rules.opVal tabs x.op (tabs.ty x.type) x.auxInt x.aux
        (x.args.toList.map (den M.get? tabs ρ n))).retype (tabs.ty x.type))
      ((Comp.select F.k [den M.get? tabs ρ n (r F.s)]).retype (tabs.ty x.type)) := by
  have h := retype_mono (tabs.ty x.type) (GoFV.Proof.Rules.opVal_mono tabs x.op (tabs.ty x.type)
    x.auxInt x.aux (refinesList_map (l := [F.s]) (f := den M.get? tabs ρ n)
      (g := fun z => den M.get? tabs ρ n (r z)) fun z _ => hr n z))
  rw [F.hxargs]
  simp only [GoFV.Proof.Rules.opVal_pure (sel_facts F.hk).2.1, (sel_facts F.hk).2.2,
    List.map_cons, List.map_nil] at h ⊢
  exact h

/-- A value defined as the selection `x` has a smaller denotation than the selected argument
`a`, at the same fuel. -/
theorem SAFacts.den_le (F : SAFacts tabs M r x a) {ρ : ID → Val} (hT : Term.Typed M.get? tabs ρ)
    (hr : ∀ k z, Sem.Refines (den M.get? tabs ρ k z) (den M.get? tabs ρ k (r z)))
    {v : ID} (hv : M.get? v = some x) : ∀ n, Sem.Refines (den M.get? tabs ρ n v) (den M.get? tabs ρ n a)
  | 0 => .poison _
  | n + 1 => by
    rw [den_succ_term hv (sel_facts F.hk).1]
    refine (F.sel_mono hr n).trans ?_
    cases n with
    | zero =>
      rw [show Comp.select F.k [den M.get? tabs ρ 0 (r F.s)] = .poison from rfl, retype_poison]
      exact .poison _
    | succ m =>
      have h := F.sel_ref hT m (Sem.Refines.refl _)
      have hfix : (den M.get? tabs ρ m a).retype (tabs.ty F.w.type) = den M.get? tabs ρ m a := by
        rw [← shape_of (tabs := tabs) F.hw]
        exact den_retype hT m a (by rw [F.hw]; rfl)
      rw [hfix] at h
      exact h.trans (den_fuel_mono _ _ _ m (m + 2) _ (by omega))

end SA

/-- `selRes` stays in a set closed under arguments. -/
theorem selRes_closed {tabs : Tables} {M : Defs} {C : ID → Prop} (hC : DefClosed M C) :
    ∀ (n : Nat) (a : ID), C a → C (selRes tabs M n a)
  | 0, _, ha => ha
  | n + 1, a, ha => by
    unfold selRes
    split
    · rename_i x hx
      obtain ⟨m, hm, hargs⟩ := hC a ha
      rw [hx] at hm; cases hm
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact selRes_closed hC n _ (hargs _ (Array.mem_toList_iff.1 (by
          rw [toList_of_size_one hc.1.2]; exact List.mem_singleton_self _)))
      · split
        · rename_i b hb
          obtain ⟨F⟩ := saFacts hb
          exact selRes_closed hC n _ (F.a_mem hC (selRes_closed hC n) hargs)
        · exact ha
    · exact ha

/-- A value `selRes` resolves to has a larger denotation at the same fuel. -/
theorem selRes_den {tabs : Tables} {M : Defs} {ρ : ID → Val} (hT : Term.Typed M.get? tabs ρ) :
    ∀ (n : Nat) (k : Nat) (a : ID),
      Sem.Refines (den M.get? tabs ρ k a) (den M.get? tabs ρ k (selRes tabs M n a))
  | 0, _, _ => Sem.Refines.refl _
  | n + 1, k, a => by
    unfold selRes
    split
    · rename_i x hx
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] at hc
        obtain ⟨⟨hop, hsz⟩, y, hy, hcc⟩ := hc
        refine Sem.Refines.trans ?_ (selRes_den hT n k _)
        cases k with
        | zero => exact .poison _
        | succ k =>
          rw [den_copy hT hx hop hsz hy hcc k]
          exact den_fuel_mono _ _ _ k (k + 1) _ (by omega)
      · split
        · rename_i b hb
          obtain ⟨F⟩ := saFacts hb
          exact (F.den_le hT (fun k z => selRes_den hT n k z) hx k).trans (selRes_den hT n k b)
        · exact Sem.Refines.refl _
    · exact Sem.Refines.refl _

section MS

variable {tabs : Tables} {M : Defs} {v : ID} {u : Value}

theorem MSFacts.get_v (F : MSFacts tabs M v u) : (putAll M [u]).get? v = some u := by
  simp [putAll, get?_put, F.hid]

theorem MSFacts.get_other (F : MSFacts tabs M v u) {y : ID} (hy : y ≠ v) :
    (putAll M [u]).get? y = M.get? y := by
  simp [putAll, get?_put, F.hid, hy]

theorem MSFacts.x_term (F : MSFacts tabs M v u) : termOp F.x.op = true := (sel_facts F.sa.hk).1

theorem MSFacts.u_term (F : MSFacts tabs M v u) : termOp u.op = true := by
  rw [F.huop]; rfl

theorem MSFacts.isTerm_iff (F : MSFacts tabs M v u) (y : ID) :
    IsTerm (putAll M [u]).get? y ↔ IsTerm M.get? y := by
  by_cases hyv : y = v
  · subst hyv
    exact ⟨fun _ => ⟨_, F.hx, F.x_term⟩, fun _ => ⟨_, F.get_v, F.u_term⟩⟩
  · simp only [IsTerm, F.get_other hyv]

theorem MSFacts.typed (F : MSFacts tabs M v u) {ρ : ID → Val}
    (hT : Term.Typed M.get? tabs ρ) : Term.Typed (putAll M [u]).get? tabs ρ := by
  intro y ht hsome
  have hyv : y ≠ v := fun h => ht ((F.isTerm_iff y).2 (h ▸ ⟨_, F.hx, F.x_term⟩))
  have hget := F.get_other hyv
  have hs : shape (putAll M [u]).get? tabs y = shape M.get? tabs y := by simp only [shape, hget]
  rw [hs]
  exact hT y (fun h => ht ((F.isTerm_iff y).2 h)) (by rw [← hget]; exact hsome)

/-- The selected argument is in a set closed under arguments that holds `v`. -/
theorem MSFacts.a_mem (F : MSFacts tabs M v u) {C : ID → Prop} (hC : DefClosed M C) (hv : C v) :
    C F.a := by
  obtain ⟨m, hm, hargs⟩ := hC v hv
  rw [F.hx] at hm; cases hm
  exact F.sa.a_mem hC (selRes_closed hC selFuel) hargs

theorem MSFacts.closed (F : MSFacts tabs M v u) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (putAll M [u]) C := by
  intro y hy
  by_cases hyv : y = v
  · subst hyv
    refine ⟨u, F.get_v, fun b hb => ?_⟩
    rw [F.huargs] at hb
    simp only [List.mem_toArray, List.mem_singleton] at hb
    subst hb
    exact F.a_mem hC hy
  · obtain ⟨m, hm, hargs⟩ := hC y hy
    exact ⟨m, by rw [F.get_other hyv, hm], hargs⟩

/-- **A selection event refines the denotations of a closed set**, at the same fuel. -/
theorem MSFacts.step (F : MSFacts tabs M v u) {C : ID → Prop} (hC : DefClosed M C)
    {ρ : ID → Val} (hT : Term.Typed M.get? tabs ρ) : ∀ n y, C y →
      Sem.Refines (den M.get? tabs ρ n y) (den (putAll M [u]).get? tabs ρ n y)
  | 0, _, _ => .poison _
  | n + 1, y, hy => by
    obtain ⟨m, hm, hargs⟩ := hC y hy
    have ih : ∀ a, C a → Sem.Refines (den M.get? tabs ρ n a) (den (putAll M [u]).get? tabs ρ n a) :=
      fun a ha => MSFacts.step F hC hT n a ha
    by_cases hyv : y = v
    · subst hyv
      rw [F.hx] at hm; cases hm
      have iha := ih F.a (F.a_mem hC hy)
      rw [den_succ_term F.hx F.x_term, den_succ_term F.get_v F.u_term, F.huop, F.huargs,
        F.huty, GoFV.Proof.Rules.opVal_pure (op := .Copy) rfl]
      refine (F.sa.sel_mono (fun k z => selRes_den hT selFuel k z) n).trans ?_
      show Sem.Refines _ ((den (putAll M [u]).get? tabs ρ n F.a).retype _)
      cases n with
      | zero => rw [show Comp.select F.sa.k [den M.get? tabs ρ 0 _] = .poison from rfl,
          retype_poison]; exact .poison _
      | succ m =>
        exact F.sa.sel_ref hT m ((den_fuel_mono _ _ _ m (m + 1) _ (by omega)).trans iha)
    · have hget := F.get_other hyv
      by_cases ht : termOp m.op = true
      · rw [den_succ_term hm ht, den_succ_term (by rw [hget]; exact hm) ht]
        exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_map fun a ha =>
          ih a (hargs a (Array.mem_toList_iff.1 ha))))
      · have h1 : ¬ IsTerm M.get? y := fun ⟨w, hw, hwt⟩ => by
          rw [hm] at hw; cases hw; exact ht hwt
        have h2 : ¬ IsTerm (putAll M [u]).get? y := fun h => h1 ((F.isTerm_iff y).1 h)
        rw [den_succ_atom h1, den_succ_atom h2]
        exact Sem.Refines.refl _

theorem ReplayInv.makeSel {D₀ : ID → Option Value} {C₀ C : ID → Prop}
    (hI : ReplayInv tabs D₀ C₀ M C) (F : MSFacts tabs M v u) :
    ReplayInv tabs D₀ C₀ (putAll M [u]) C where
  closed := F.closed hI.closed
  sub := hI.sub
  typed := fun ρ h => F.typed (hI.typed ρ h)
  denRef := fun y hy => den_compose (g := id) (hI.denRef y hy) hI.typed
    fun _ hρ n => F.step hI.closed hρ n y (hI.sub y hy)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hsz, hrest⟩ := hI.atoms y a hy ha hargs
    have hyv : y ≠ v := fun h => by
      rw [h, F.hx] at ha'; cases ha'; rw [F.x_term] at hat; cases hat
    refine ⟨a', by rw [F.get_other hyv]; exact ha', hat, hsz, fun i hi => ⟨(hrest i hi).1, ?_⟩⟩
    exact den_compose (g := id) (hrest i hi).2 hI.typed
      fun _ hρ n => F.step hI.closed hρ n _ (hrest i hi).1

end MS

end GoFV.Proof.Pass.Rewrite
