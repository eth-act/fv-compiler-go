import GoFV.Proof.Pass.CopyElimView
import GoFV.Proof.CheckFacts

/-!
# The invariant of copyelim's sweeps

`Inv tabs f F`: the current function `F` has `f`'s skeleton, value blocks and types; every
listed value of `f` is in one of three modes (`Mode`: same op with arguments that `Join` `f`'s,
a phi turned into a copy of a value all of its arguments join, or a zero-size value turned
`Empty`); arguments stay listed; every listed value's copy chain ends; copies keep their
argument's type shape; a copy chain of `f` that ends at a non-phi ends there in `F` too (so a
`Stable` phi never becomes a copy). Each of the three edits keeps it: `setArg` of an argument
to the end of its chain (`inv_setArg`), the zero-size reset (`inv_empty`) and the phi-to-copy
step (`inv_phielim`). `Prsv`: an edit keeps the non-copies, and every new argument is old or a
non-copy (so arguments that were non-copies stay so, `AllSink`).
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.Opt GoFV.Proof

/-- How a listed value `fv` of the input appears in the current table (as `v`). -/
inductive Mode (tabs : Tables) (V : ID → Option Value) (fv v : Value) : Prop where
  | same : v.op = fv.op → v.aux = fv.aux → v.auxInt = fv.auxInt → v.args.size = fv.args.size →
      (∀ (k : Nat) (a c : ID), fv.args[k]? = some a → v.args[k]? = some c → Join V a c) →
      Mode tabs V fv v
  | phi (w : ID) : fv.op = .Phi → v.op = .Copy → v.args = #[w] → ¬ zeroSize tabs fv.type →
      (∀ a ∈ fv.args, Join V a w) → Mode tabs V fv v
  | empty : zeroSize tabs fv.type → v.op = .Empty → v.args = #[] → Mode tabs V fv v

/-- The invariant of the sweeps (current function `F`, input `f`). -/
structure Inv (tabs : Tables) (f F : Func) : Prop where
  skel : skel F = skel f
  keep : ∀ x, (vw F x).map (fun u => (u.block, u.type, u.id)) =
    (vw f x).map (fun u => (u.block, u.type, u.id))
  mode : ∀ x, Listed f x → ∀ fv, f.value? x = some fv → ∃ v, vw F x = some v ∧ Mode tabs (vw F) fv v
  closed : ∀ x, Listed f x → ∀ v, vw F x = some v → ∀ c ∈ v.args, Listed f c
  acyc : ∀ x, Listed f x → ∃ r n, Src (vw F) x r n
  shape : ∀ x, Listed f x → ∀ w, cstep (vw F) x = some (some w) →
    ∃ xv wv, f.value? x = some xv ∧ f.value? w = some wv ∧
      RetypeInto (tabs.ty wv.type) (tabs.ty xv.type)
  ends : ∀ x r n, Src (vw f) x r n → NotPhi f r → ∃ m, Src (vw F) x r m

/-- The non-copies are kept, and each argument is old or a non-copy. -/
structure Prsv (V V' : ID → Option Value) : Prop where
  sinks : ∀ x, cstep V' x = none ↔ cstep V x = none
  args : ∀ x u', V' x = some u' → ∀ c ∈ u'.args, (∃ u, V x = some u ∧ c ∈ u.args) ∨ cstep V' c = none

/-- The arguments of the values `xs` are non-copies. -/
def AllSink (V : ID → Option Value) (xs : List ID) : Prop :=
  ∀ x ∈ xs, ∀ u, V x = some u → ∀ c ∈ u.args, cstep V c = none

theorem Prsv.refl (V : ID → Option Value) : Prsv V V :=
  ⟨fun _ => Iff.rfl, fun _ u' h _ hc => .inl ⟨u', h, hc⟩⟩

theorem Prsv.trans {V1 V2 V3 : ID → Option Value} (h1 : Prsv V1 V2) (h2 : Prsv V2 V3) :
    Prsv V1 V3 := by
  refine ⟨fun x => (h2.sinks x).trans (h1.sinks x), fun x u3 hx c hc => ?_⟩
  rcases h2.args x u3 hx c hc with ⟨u2, hx2, hc2⟩ | h
  · rcases h1.args x u2 hx2 c hc2 with h | h
    · exact .inl h
    · exact .inr ((h2.sinks c).2 h)
  · exact .inr h

theorem AllSink.prsv {V V' : ID → Option Value} {xs : List ID} (h : AllSink V xs)
    (hp : Prsv V V') : AllSink V' xs := by
  intro x hx u' hu c hc
  rcases hp.args x u' hu c hc with ⟨u, hu0, hc0⟩ | h'
  · exact (hp.sinks c).2 (h x hx u hu0 c hc0)
  · exact h'

theorem AllSink.append {V : ID → Option Value} {xs ys : List ID} (h1 : AllSink V xs)
    (h2 : AllSink V ys) : AllSink V (xs ++ ys) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h1 x hx
  · exact h2 x hx

theorem Mode.mono {tabs : Tables} {V V' : ID → Option Value} {fv v : Value}
    (hj : ∀ a c, Join V a c → Join V' a c) : Mode tabs V fv v → Mode tabs V' fv v
  | .same h1 h2 h3 h4 h5 => .same h1 h2 h3 h4 fun k a c ha hc => hj _ _ (h5 k a c ha hc)
  | .phi w h1 h2 h3 h4 h5 => .phi w h1 h2 h3 h4 fun a ha => hj _ _ (h5 a ha)
  | .empty h1 h2 h3 => .empty h1 h2 h3

/-! ## Facts under the invariant -/

section
variable {tabs : Tables} {ce : CheckEnv} {f F : Func}

theorem listed_value (hwf : WF ce f) {x : ID} (hx : Listed f x) : ∃ fv, f.value? x = some fv := by
  obtain ⟨bid, b, hb, hxb⟩ := hx
  obtain ⟨v, hv, -⟩ := hwf.valueId bid b hb x hxb
  exact ⟨v, hv⟩

theorem Inv.value (hwf : WF ce f) (hI : Inv tabs f F) {x : ID} (hx : Listed f x) :
    ∃ fv v, f.value? x = some fv ∧ vw F x = some v ∧ Mode tabs (vw F) fv v := by
  obtain ⟨fv, hfv⟩ := listed_value hwf hx
  obtain ⟨v, hv, hm⟩ := hI.mode x hx fv hfv
  exact ⟨fv, v, hfv, hv, hm⟩

/-- Chains from listed values stay listed. -/
theorem Inv.src_listed (hI : Inv tabs f F) :
    ∀ {x r n}, Listed f x → Src (vw F) x r n → Listed f r
  | _, _, _, hx, .sink _ => hx
  | _, _, _, hx, .step (y := y) hxy hs => by
    obtain ⟨u, hu, -, ha⟩ := cstep_some_some hxy
    exact hI.src_listed (hI.closed _ hx u hu y (by rw [ha]; simp)) hs

/-- Chains keep the type shape. -/
theorem Inv.src_shape (hwf : WF ce f) (hI : Inv tabs f F) :
    ∀ {x r n}, Listed f x → Src (vw F) x r n →
      ∃ xv rv, f.value? x = some xv ∧ f.value? r = some rv ∧
        RetypeInto (tabs.ty rv.type) (tabs.ty xv.type)
  | _, _, _, hx, .sink _ => by
    obtain ⟨fv, hfv⟩ := listed_value hwf hx
    exact ⟨fv, fv, hfv, hfv, .refl _⟩
  | _, _, _, hx, .step (y := y) hxy hs => by
    obtain ⟨u, hu, -, ha⟩ := cstep_some_some hxy
    have hy := hI.closed _ hx u hu y (by rw [ha]; simp)
    obtain ⟨xv, yv, h1, h2, h3⟩ := hI.shape _ hx _ hxy
    obtain ⟨yv', rv, h1', h2', h3'⟩ := hI.src_shape hwf hy hs
    rw [h2] at h1'; cases h1'
    exact ⟨xv, rv, h1, h2', h3'.trans h3⟩

theorem Inv.keep_some (hI : Inv tabs f F) {x : ID} {v : Value} (hv : vw F x = some v) :
    ∃ fv, f.value? x = some fv ∧ v.block = fv.block ∧ v.type = fv.type ∧ v.id = fv.id := by
  have := hI.keep x
  rw [hv] at this
  cases hf : f.value? x with
  | none => rw [vw, hf] at this; cases this
  | some fv =>
    rw [vw, hf] at this
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
    exact ⟨fv, rfl, this.1, this.2.1, this.2.2⟩

/-- `Inv` holds initially. -/
theorem inv_init (hwf : WF ce f) (hfrag : CopyFrag tabs f) : Inv tabs f f := by
  have hsrc : ∀ x, Listed f x → ∃ r n, Src (vw f) x r n := by
    intro x hx
    obtain ⟨r, n, h⟩ := hfrag.acyclic x hx
    exact ⟨r, n, src_congr (by intro y; rw [cstep_vw]) h⟩
  refine ⟨rfl, fun _ => rfl, ?_, ?_, hsrc, ?_, fun _ _ n h _ => ⟨n, h⟩⟩
  · intro x hx fv hfv
    refine ⟨strip fv, vw_of_value? hfv, .same rfl rfl rfl rfl fun k a c ha hc => ?_⟩
    have hc' : fv.args[k]? = some c := hc
    rw [ha] at hc'; cases hc'
    obtain ⟨bid, b, hb, hxb⟩ := hx
    obtain ⟨r, n, h⟩ := hsrc a (hwf.argListed bid b x fv ⟨hb, hxb, hfv⟩ a
      (Array.mem_of_getElem? ha))
    exact ⟨r, n, n, h, h⟩
  · intro x hx v hv c hc
    obtain ⟨fv, hfv, rfl⟩ := vw_eq_some hv
    obtain ⟨bid, b, hb, hxb⟩ := hx
    exact hwf.argListed bid b x fv ⟨hb, hxb, hfv⟩ c hc
  · intro x hx w hw
    rw [cstep_vw] at hw
    obtain ⟨u, hu, hop, ha⟩ := cstep_some_some hw
    obtain ⟨wv, hwv, hty⟩ := hfrag.shape x hx u hu (.inl hop) w (by rw [ha]; simp)
    exact ⟨u, wv, hu, hwv, hty⟩

end

/-! ## Phi count -/

/-- The number of phis among the first `N` values. -/
def phiN (V : ID → Option Value) (N : Nat) : Nat :=
  (List.range N).countP fun x => (V x).any (·.op == .Phi)

theorem phiN_le {V V' : ID → Option Value} {N : Nat}
    (h : ∀ x, (V' x).any (·.op == .Phi) = true → (V x).any (·.op == .Phi) = true) :
    phiN V' N ≤ phiN V N :=
  List.countP_mono_left fun x _ hx => h x hx

theorem countP_range_lt {p q : Nat → Bool} (h : ∀ x, q x = true → p x = true) {v : Nat} :
    ∀ {N}, v < N → p v = true → q v = false →
      (List.range N).countP q < (List.range N).countP p
  | 0, hv, _, _ => absurd hv (Nat.not_lt_zero _)
  | N + 1, hv, h1, h2 => by
    rw [List.range_succ, List.countP_append, List.countP_append]
    have hm := List.countP_mono_left (l := List.range N) fun x _ hx => h x hx
    have h3 : List.countP q [N] ≤ List.countP p [N] := List.countP_mono_left fun x _ hx => h x hx
    by_cases hvN : v = N
    · subst hvN
      have h4 : List.countP q [v] = 0 := by simp [h2]
      have h5 : List.countP p [v] = 1 := by simp [h1]
      omega
    · have := countP_range_lt h (N := N) (by omega) h1 h2
      omega

theorem phiN_lt {V V' : ID → Option Value} {N : Nat}
    (h : ∀ x, (V' x).any (·.op == .Phi) = true → (V x).any (·.op == .Phi) = true)
    {v : ID} (hv : v < N) (h1 : (V v).any (·.op == .Phi) = true)
    (h2 : (V' v).any (·.op == .Phi) = false) : phiN V' N < phiN V N :=
  countP_range_lt h hv h1 h2

end GoFV.Proof.CopyElim
