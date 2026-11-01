import GoFV.Proof.Pass.RewriteTermReplay
import GoFV.Proof.Rules.DecShape

/-!
# Replaying a selection of a `Make` (issue #17)

A rule event accepted by `RewriteCheck.makeSelOK` (a selection rule over a `Make` with a copy
result, `makeSelShape`: `(ITab (IMake itab _)) => itab`, the variadic `(StructSelect [i]
x:(StructMake ___)) => x.Args[i]` of `dec.rules:106`/`generic.rules:973`, …) redefines the
selection `v` of component `k` of `s = Make …` as `Copy a` of the `Make`'s argument `k`.
`MSFacts.step`: on a set closed under arguments, every denotation after the event refines the
one before at the same fuel (`select_retype_make_get` at `v`: component `k` of the retyped
`Make` is `a` retyped at the field's shape, which keeps `a`'s denotation since `a`'s shape is
the field's and `v`'s, or `a` is an `Addr`, a global pointer without a concrete address, under
word shapes: `addr_den`, `retype_word`; monotonicity elsewhere). `ReplayInv.makeSel`: the event
keeps the replay invariant.
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

/-- A word shape keeps `poison` and a pointer without a concrete address. -/
theorem retype_word {t : Ty} (ht : wordTy t = true) {z : Val}
    (hz : z = .poison ∨ ∃ p, z = .ptr p ∧ p.addr? = none) : z.retype t = z := by
  rcases hz with rfl | ⟨p, rfl, hp⟩
  · exact retype_poison _
  · cases t with
    | int w => cases w <;> simp [wordTy] at ht; simp [Val.retype, hp]
    | ptr e => rfl
    | _ => simp [wordTy] at ht

/-- An `Addr` denotes `poison` or a global pointer, which has no concrete address. -/
theorem addr_den {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {a : ID} {w : Value}
    (hw : D a = some w) (hop : w.op = .Addr) :
    ∀ m, den D tabs ρ m a = .poison ∨ ∃ p, den D tabs ρ m a = .ptr p ∧ p.addr? = none
  | 0 => .inl rfl
  | m + 1 => by
    rw [den_succ_term hw (by rw [hop]; rfl), hop, GoFV.Proof.Rules.opVal_addr]
    unfold GoFV.Proof.Rules.addrVal
    split
    · generalize tabs.ty w.type = t
      cases t with
      | int w => cases w <;> first | exact .inl rfl | exact .inr ⟨_, rfl, rfl⟩
      | ptr e => exact .inr ⟨_, rfl, rfl⟩
      | _ => exact .inl rfl
    · exact .inl (retype_poison _)

/-- What `makeSelOK` establishes about an event `(v, [u])`. -/
structure MSFacts (tabs : Tables) (M : Defs) (v : ID) (u : Value) where
  x : Value
  s : ID
  y : Value
  k : Nat
  a : ID
  w : Value
  hx : M.get? v = some x
  hxargs : x.args.toList = [s]
  hk : selIndex? x.op x.auxInt = some k
  hy : M.get? s = some y
  ha : y.args[k]? = some a
  hw : M.get? a = some w
  hyop : GoFV.Proof.Rules.makeOp y.op = true
  hid : u.id = v
  huop : u.op = .Copy
  huargs : u.args = #[a]
  huty : u.type = w.type
  hsh : ∀ fk, GoFV.Proof.Rules.fieldShape? (tabs.ty y.type) k = some fk →
    (GoFV.Proof.Rules.shapeSub (tabs.ty w.type) fk = true ∧
      GoFV.Proof.Rules.shapeSub (tabs.ty w.type) (tabs.ty x.type) = true) ∨
    (w.op = .Addr ∧ wordTy fk = true ∧ wordTy (tabs.ty x.type) = true)

theorem msFacts {tabs : Tables} {M : Defs} {v : ID} {defs : List Value}
    (h : makeSelOK tabs M v defs = true) : ∃ u, defs = [u] ∧ Nonempty (MSFacts tabs M v u) := by
  unfold makeSelOK at h
  split at h
  · rename_i x u hx
    split at h
    · rename_i s k hxargs hk
      split at h
      · rename_i y hy
        split at h
        · rename_i a ha
          split at h
          · rename_i w hw
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            obtain ⟨⟨⟨⟨⟨hyop, hid⟩, huop⟩, huargs⟩, huty⟩, hsh⟩ := h
            refine ⟨u, rfl, ⟨⟨x, s, y, k, a, w, hx, hxargs, hk, hy, ha, hw, hyop, hid, huop,
              huargs, huty, fun fk hf => ?_⟩⟩⟩
            rw [hf] at hsh
            simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, and_assoc] using hsh
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

section MS

variable {tabs : Tables} {M : Defs} {v : ID} {u : Value}

theorem MSFacts.get_v (F : MSFacts tabs M v u) : (putAll M [u]).get? v = some u := by
  simp [putAll, get?_put, F.hid]

theorem MSFacts.get_other (F : MSFacts tabs M v u) {y : ID} (hy : y ≠ v) :
    (putAll M [u]).get? y = M.get? y := by
  simp [putAll, get?_put, F.hid, hy]

theorem MSFacts.x_term (F : MSFacts tabs M v u) : termOp F.x.op = true := (sel_facts F.hk).1

theorem MSFacts.u_term (F : MSFacts tabs M v u) : termOp u.op = true := by
  rw [F.huop]; rfl

theorem MSFacts.y_term (F : MSFacts tabs M v u) : termOp F.y.op = true := (make_facts F.hyop).1

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
  have hs : C F.s := hargs _ (Array.mem_toList_iff.1 (by rw [F.hxargs]; exact List.mem_singleton_self _))
  obtain ⟨m', hm', hargs'⟩ := hC F.s hs
  rw [F.hy] at hm'; cases hm'
  exact hargs' _ (Array.mem_of_getElem? F.ha)

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

/-- At `v`: the selection of the `Make`'s argument `k` is refined by `a`'s denotation. -/
theorem MSFacts.sel_ref (F : MSFacts tabs M v u) {ρ : ID → Val} (hT : Term.Typed M.get? tabs ρ)
    (m : Nat) {z : Val} (hz : Sem.Refines (den M.get? tabs ρ m F.a) z) :
    Sem.Refines ((Comp.select F.k [den M.get? tabs ρ (m + 1) F.s]).retype
      (tabs.ty F.x.type)) (z.retype (tabs.ty F.w.type)) := by
  rw [den_succ_term F.hy F.y_term, GoFV.Proof.Rules.opVal_pure (make_facts F.hyop).2.1,
    (make_facts F.hyop).2.2]
  rcases GoFV.Proof.Rules.select_retype_make_get (tabs.ty F.y.type) F.k
      (F.y.args.toList.map (den M.get? tabs ρ m)) with h | ⟨f, z', hf, hz', he⟩
  · rw [h, retype_poison]; exact .poison _
  · rw [he]
    have hz'' : z' = den M.get? tabs ρ m F.a := by
      rw [List.getElem?_map, Array.getElem?_toList, F.ha] at hz'
      simp only [Option.map_some, Option.some.injEq] at hz'
      exact hz'.symm
    subst hz''
    have hfix : (den M.get? tabs ρ m F.a).retype (tabs.ty F.w.type) = den M.get? tabs ρ m F.a := by
      rw [← shape_of (tabs := tabs) F.hw]
      exact den_retype hT m F.a (by rw [F.hw]; rfl)
    have hkeep : ((den M.get? tabs ρ m F.a).retype f).retype (tabs.ty F.x.type) =
        den M.get? tabs ρ m F.a := by
      rcases F.hsh f hf with ⟨h1, h2⟩ | ⟨hop, h1, h2⟩
      · have hty : (den M.get? tabs ρ m F.a).hasTy (tabs.ty F.w.type) = true := by
          rw [← hfix]; exact Val.retype_hasTy _ _
        rw [GoFV.Proof.Rules.retype_of_shapeSub hty h1, GoFV.Proof.Rules.retype_of_shapeSub hty h2]
      · have hg := addr_den (tabs := tabs) (ρ := ρ) F.hw hop m
        rw [retype_word h1 hg, retype_word h2 hg]
    rw [hkeep, ← hfix]
    exact retype_mono _ hz

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
        F.huty, GoFV.Proof.Rules.opVal_pure (sel_facts F.hk).2.1, (sel_facts F.hk).2.2,
        GoFV.Proof.Rules.opVal_pure (op := .Copy) rfl, F.hxargs]
      show Sem.Refines ((Comp.select F.k [den M.get? tabs ρ n F.s]).retype _)
        ((den (putAll M [u]).get? tabs ρ n F.a).retype _)
      cases n with
      | zero => rw [show Comp.select F.k [den M.get? tabs ρ 0 F.s] = .poison from rfl,
          retype_poison]; exact .poison _
      | succ m =>
        exact F.sel_ref hT m ((den_fuel_mono _ _ _ m (m + 1) _ (by omega)).trans iha)
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
