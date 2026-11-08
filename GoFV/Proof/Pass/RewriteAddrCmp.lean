import GoFV.Proof.Pass.RewriteIMake
import GoFV.Proof.PtrAddr

variable [GoFV.SSA.Sem.Addrs]

/-!
# Replaying a comparison of symbol addresses (issue #69)

A rule event accepted by `RewriteCheck.addrCmpOK` (`(EqPtr (Addr {x} _) (Addr {y} _)) =>
(ConstBool [x == y])`, `generic.rules:1648`, and its `NeqPtr` form `:1651`;
`GoFV.Proof.Rules.addrCmpShape`) redefines `v = EqPtr a b` (or `NeqPtr`), `a` and `b` `Addr`s of
the symbols `na` and `nb`, as the `ConstBool` of whether the names are equal (differ). An `Addr`
denotes the pointer to offset 0 of the global block its symbol names
(`GoFV.Proof.Rules.addrVal`), and two such pointers are equal iff the names are (`Ptr.eq`), so
the constant refines `v` at every fuel (`ACFacts.step`). `ReplayInv.addrCmp`: the event keeps the
replay invariant.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim

/-- What `addrCmpOK` establishes about an event `(v, [u])`. -/
structure ACFacts (tabs : Tables) (M : Defs) (v : ID) (u0 u : Value) where
  x : Value
  a : ID
  b : ID
  na : String
  nb : String
  hx : M.get? v = some x
  hxargs : x.args.toList = [a, b]
  ha : addrSymOf tabs M a = some na
  hb : addrSymOf tabs M b = some nb
  hxop : x.op = .EqPtr ∨ x.op = .NeqPtr
  hid0 : u0.id = v
  hid : u.id = v
  huop : u.op = .ConstBool
  huargs : u.args = #[]
  huty : u.type = x.type
  hai : u.auxInt = if (na == nb) != (x.op == .NeqPtr) then 1 else 0

theorem acFacts {tabs : Tables} {M : Defs} {v : ID} {defs : List Value}
    (h : addrCmpOK tabs M v defs = true) :
    ∃ u0 u, defs = [u0, u] ∧ Nonempty (ACFacts tabs M v u0 u) := by
  unfold addrCmpOK at h
  split at h
  next x u0 u hx =>
    split at h
    next a b hxargs =>
      split at h
      next na nb ha hb =>
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Array.isEmpty_iff] at h
        obtain ⟨⟨⟨⟨⟨⟨hxop, hid0⟩, hid⟩, huop⟩, huargs⟩, huty⟩, hai⟩ := h
        exact ⟨u0, u, rfl, ⟨⟨x, a, b, na, nb, hx, hxargs, ha, hb, hxop, hid0, hid, huop, huargs,
          huty, hai⟩⟩⟩
      next => simp at h
    next => simp at h
  next => simp at h

/-- An `Addr` operand's symbol: its definition and the pointer it denotes. -/
theorem addrSymOf_spec {tabs : Tables} {M : Defs} {a : ID} {n : String}
    (h : addrSymOf tabs M a = some n) :
    ∃ y, M.get? a = some y ∧ y.op = .Addr ∧
      GoFV.Proof.Rules.addrVal tabs y.aux = .ptr ⟨.global n, 0⟩ := by
  unfold addrSymOf at h
  split at h
  next y hy =>
    split at h
    next hop =>
      refine ⟨y, hy, by simpa using hop, ?_⟩
      unfold addrName? at h
      unfold GoFV.Proof.Rules.addrVal
      split at h
      next hk =>
        rw [hk]
        simp only [Option.some.injEq] at h
        subst h
        rfl
      next => cases h
    next => cases h
  next => cases h

/-- A pointer retyped at any shape is read as that pointer or as no pointer word (`poison`
outside its window). -/
theorem ptr_retype_word (t : Ty) (p : Ptr) :
    ((Val.ptr p).retype t).asPtrWord = none ∨ ((Val.ptr p).retype t).asPtrWord = some p := by
  have hw : p.word.asPtrWord = none ∨ p.word.asPtrWord = some p := by
    cases h : p.inWindow
    · exact .inl (by rw [Ptr.word_of_not_inWindow h]; rfl)
    · exact .inr (Ptr.word_asPtrWord h)
  cases t with
  | int w => cases w <;> first | exact hw | exact .inl rfl
  | ptr _ => exact hw
  | _ => exact .inl rfl

/-- The comparison of two global pointers at offset 0 is the comparison of their names. -/
theorem eqPtr_globals (neg : Bool) (ta tb T : Ty) (na nb : String) :
    Sem.Refines ((PtrOps.eqPtr neg [(Val.ptr ⟨.global na, 0⟩).retype ta,
        (Val.ptr ⟨.global nb, 0⟩).retype tb]).retype T)
      ((Val.bool ((na == nb) != neg)).retype T) := by
  unfold PtrOps.eqPtr
  rcases ptr_retype_word ta ⟨.global na, 0⟩ with h | h <;>
    rcases ptr_retype_word tb ⟨.global nb, 0⟩ with h' | h' <;> simp only [h, h']
  all_goals try (rw [retype_poison]; exact .poison _)
  have : Ptr.eq ⟨.global na, 0⟩ ⟨.global nb, 0⟩ = (na == nb) := by
    unfold Ptr.eq
    by_cases e : na = nb
    · subst e; simp
    · have h1 : (Blk.global na == Blk.global nb) = false := by simp [e]
      have h2 : (na == nb) = false := by simp [e]
      rw [h1, h2]; rfl
  rw [this]
  exact Sem.Refines.refl _

section AC

variable {tabs : Tables} {M : Defs} {v : ID} {u0 u : Value}

theorem ACFacts.get_v (F : ACFacts tabs M v u0 u) : (putAll M [u0, u]).get? v = some u := by
  simp [putAll, get?_put, F.hid0, F.hid]

theorem ACFacts.get_other (F : ACFacts tabs M v u0 u) {y : ID} (hy : y ≠ v) :
    (putAll M [u0, u]).get? y = M.get? y := by
  simp [putAll, get?_put, F.hid0, F.hid, hy]

theorem ACFacts.x_term (F : ACFacts tabs M v u0 u) : termOp F.x.op = true := by
  rcases F.hxop with h | h <;> rw [h] <;> rfl

theorem ACFacts.u_term (F : ACFacts tabs M v u0 u) : termOp u.op = true := by
  rw [F.huop]; rfl

theorem ACFacts.isTerm_iff (F : ACFacts tabs M v u0 u) (y : ID) :
    IsTerm (putAll M [u0, u]).get? y ↔ IsTerm M.get? y := by
  by_cases hyv : y = v
  · subst hyv
    exact ⟨fun _ => ⟨_, F.hx, F.x_term⟩, fun _ => ⟨_, F.get_v, F.u_term⟩⟩
  · simp only [IsTerm, F.get_other hyv]

theorem ACFacts.typed (F : ACFacts tabs M v u0 u) {ρ : ID → Val}
    (hT : Term.Typed M.get? tabs ρ) : Term.Typed (putAll M [u0, u]).get? tabs ρ := by
  intro y ht hsome
  have hyv : y ≠ v := fun h => ht ((F.isTerm_iff y).2 (h ▸ ⟨_, F.hx, F.x_term⟩))
  have hget := F.get_other hyv
  have hs : shape (putAll M [u0, u]).get? tabs y = shape M.get? tabs y := by simp only [shape, hget]
  rw [hs]
  exact hT y (fun h => ht ((F.isTerm_iff y).2 h)) (by rw [← hget]; exact hsome)

theorem ACFacts.closed (F : ACFacts tabs M v u0 u) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (putAll M [u0, u]) C := by
  intro y hy
  by_cases hyv : y = v
  · subst hyv
    refine ⟨u, F.get_v, fun b hb => ?_⟩
    rw [F.huargs] at hb
    simp at hb
  · obtain ⟨m, hm, hargs⟩ := hC y hy
    exact ⟨m, by rw [F.get_other hyv, hm], hargs⟩

/-- The comparison's value at positive fuel: the folded constant refines it. -/
theorem ACFacts.v_ref (F : ACFacts tabs M v u0 u) (ρ : ID → Val) (n : Nat) :
    Sem.Refines (den M.get? tabs ρ (n + 1) v) (den (putAll M [u0, u]).get? tabs ρ (n + 1) v) := by
  have hc : ∀ (ty : Ty) (ai : Int64) (ax : Option AuxRef) (l : List Val),
      evalPure .ConstBool ty ai ax l = .bool (ai != 0) := fun _ _ _ _ => rfl
  rw [den_succ_term F.hx F.x_term, den_succ_term F.get_v F.u_term, F.huop, F.huargs, F.huty,
    GoFV.Proof.Rules.opVal_pure (op := .ConstBool) rfl, F.hxargs]
  simp only [List.toList_toArray, List.map_nil, List.map_cons, hc, F.hai]
  have hneg : ∀ args : List Val, GoFV.Proof.Rules.opVal tabs F.x.op (tabs.ty F.x.type)
      F.x.auxInt F.x.aux args = PtrOps.eqPtr (F.x.op == .NeqPtr) args := by
    intro args
    rcases F.hxop with h | h <;> rw [h] <;> rfl
  rw [hneg]
  have hb : ((if (F.na == F.nb) != (F.x.op == .NeqPtr) then (1 : Int64) else 0) != 0) =
      ((F.na == F.nb) != (F.x.op == .NeqPtr)) := by
    split <;> rename_i h <;> simp only [h] <;> decide
  rw [hb]
  cases n with
  | zero =>
    simp only [den, PtrOps.eqPtr, Val.asPtrWord, retype_poison]
    exact .poison _
  | succ k =>
    obtain ⟨ya, hya, hyaop, hva⟩ := addrSymOf_spec F.ha
    obtain ⟨yb, hyb, hybop, hvb⟩ := addrSymOf_spec F.hb
    rw [den_succ_term hya (by rw [hyaop]; rfl), den_succ_term hyb (by rw [hybop]; rfl), hyaop,
      hybop, GoFV.Proof.Rules.opVal_addr, GoFV.Proof.Rules.opVal_addr, hva, hvb]
    exact eqPtr_globals _ _ _ _ _ _

/-- **A comparison-of-symbol-addresses event refines the denotations of a closed set**, at the
same fuel. -/
theorem ACFacts.step (F : ACFacts tabs M v u0 u) {C : ID → Prop} (hC : DefClosed M C)
    {ρ : ID → Val} : ∀ n y, C y →
      Sem.Refines (den M.get? tabs ρ n y) (den (putAll M [u0, u]).get? tabs ρ n y)
  | 0, _, _ => .poison _
  | n + 1, y, hy => by
    obtain ⟨m, hm, hargs⟩ := hC y hy
    by_cases hyv : y = v
    · subst hyv; exact F.v_ref ρ n
    · have hget := F.get_other hyv
      have ih : ∀ a, C a → Sem.Refines (den M.get? tabs ρ n a) (den (putAll M [u0, u]).get? tabs ρ n a) :=
        fun a ha => ACFacts.step F hC n a ha
      by_cases ht : termOp m.op = true
      · rw [den_succ_term hm ht, den_succ_term (by rw [hget]; exact hm) ht]
        exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_map fun a ha =>
          ih a (hargs a (Array.mem_toList_iff.1 ha))))
      · have h1 : ¬ IsTerm M.get? y := fun ⟨w, hw, hwt⟩ => by
          rw [hm] at hw; cases hw; exact ht hwt
        have h2 : ¬ IsTerm (putAll M [u0, u]).get? y := fun h => h1 ((F.isTerm_iff y).1 h)
        rw [den_succ_atom h1, den_succ_atom h2]
        exact Sem.Refines.refl _

theorem ReplayInv.addrCmp {D₀ : ID → Option Value} {C₀ C : ID → Prop}
    (hI : ReplayInv tabs D₀ C₀ M C) (F : ACFacts tabs M v u0 u) :
    ReplayInv tabs D₀ C₀ (putAll M [u0, u]) C where
  closed := F.closed hI.closed
  sub := hI.sub
  typed := fun ρ h => F.typed (hI.typed ρ h)
  denRef := fun y hy => den_compose (g := id) (hI.denRef y hy) hI.typed
    fun _ _ n => F.step hI.closed n y (hI.sub y hy)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hsz, hrest⟩ := hI.atoms y a hy ha hargs
    have hyv : y ≠ v := fun h => by
      rw [h, F.hx] at ha'; cases ha'; rw [F.x_term] at hat; cases hat
    refine ⟨a', by rw [F.get_other hyv]; exact ha', hat, hsz, fun i hi => ⟨(hrest i hi).1, ?_⟩⟩
    exact den_compose (g := id) (hrest i hi).2 hI.typed
      fun _ _ n => F.step hI.closed n _ (hrest i hi).1

end AC

end GoFV.Proof.Pass.Rewrite
