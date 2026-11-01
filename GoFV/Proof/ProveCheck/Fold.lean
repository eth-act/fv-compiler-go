import GoFV.Proof.ProveCheck.DecideSound

/-!
# prove's validator: constant-folded arguments (issue #24)

`fold_ref`: under assumptions `A` that hold, an argument `a` that `foldOK` lets become the
constant `c` of the output is refined by it, at every fuel. A boolean `a` is `poison` or the
value `decides` says (`decides_sound`); an integer `a` is `poison` or the single point of its
range (`rng_sound`), never a pointer word (`intOnly_not_ptr`: a range-table node evaluates to
an integer or `poison`, a side of a comparison fact eventually to an integer).
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck GoFV.Proof.Term
  GoFV.Proof.AtomSim

/-- `v` is not a pointer word. -/
def NoPtr (v : Val) : Prop := ∀ p, v ≠ .ptr p

theorem noPtr_int (w : Width) (x : BitVec w.bits) : NoPtr (.int w x) := fun _ h => by cases h

theorem noPtr_poison : NoPtr .poison := fun _ h => by cases h

theorem noPtr_int1 {w : Width} {f : BitVec w.bits → Val} (hf : ∀ x, NoPtr (f x)) (args : List Val) :
    NoPtr (Sem.int1 w f args) := by
  unfold Sem.int1
  split
  · split
    · exact hf _
    · exact noPtr_poison
  · exact noPtr_poison

theorem noPtr_int2 {w : Width} {f : BitVec w.bits → BitVec w.bits → Val} (hf : ∀ x y, NoPtr (f x y))
    (args : List Val) : NoPtr (Sem.int2 w f args) := by
  unfold Sem.int2
  split
  · split
    · exact hf _ _
    · exact noPtr_poison
  · exact noPtr_poison

theorem noPtr_count (rw : Option Width) (n : Nat) : NoPtr (Sem.Int.count rw n) := by
  unfold Sem.Int.count
  split
  · exact noPtr_int _ _
  · exact noPtr_poison

/-- The range-table families evaluate to integers or `poison`. -/
theorem rOpEval_noPtr (c : ROp) (wo : Option Width) (ai : Int64) (args : List Val) :
    NoPtr (rOpEval c wo ai args) := by
  cases c with
  | const w => exact noPtr_int _ _
  | zext a b => exact noPtr_int1 (fun _ => noPtr_int _ _) _
  | sext a b => exact noPtr_int1 (fun _ => noPtr_int _ _) _
  | and w => exact noPtr_int2 (fun _ _ => noPtr_int _ _) _
  | modu w =>
    refine noPtr_int2 (fun _ _ => ?_) _
    split
    · exact noPtr_poison
    · exact noPtr_int _ _
  | add w => exact noPtr_int2 (fun _ _ => noPtr_int _ _) _
  | sub w => exact noPtr_int2 (fun _ _ => noPtr_int _ _) _
  | bitLen w => exact noPtr_int1 (fun _ => noPtr_count _ _) _
  | popCount w => exact noPtr_int1 (fun _ => noPtr_count _ _) _
  | b2u =>
    show NoPtr (Conv.boolToUint8 args)
    unfold Conv.boolToUint8
    split
    · split
      · exact noPtr_int _ _
      · exact noPtr_poison
    · exact noPtr_poison

theorem noPtr_retype_int {w : Width} {z : Val} (h : NoPtr z) : NoPtr (z.retype (.int w)) := by
  intro p hp
  cases z with
  | int w' x =>
    simp only [Val.retype] at hp
    split at hp <;> cases hp
  | ptr q => exact h q rfl
  | _ => cases w <;> simp [Val.retype] at hp

theorem refines_ptr {p : Ptr} {v : Val} (h : Sem.Refines (.ptr p) v) : v = .ptr p := by
  cases h; rfl

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {A : Asm}

/-- The value of a term or a typed atom has its shape. -/
theorem den_hasTy (hty : Term.Typed D tabs ρ) {a : ID} {u : Value} (hu : D a = some u) :
    ∀ n, (den D tabs ρ n a).hasTy (tabs.ty u.type) = true
  | 0 => rfl
  | n + 1 => by
    by_cases ht : termOp u.op = true
    · rw [den_succ_term hu ht]; exact Val.retype_hasTy _ _
    · have hat : ¬ IsTerm D a := fun ⟨v, hv, hv'⟩ => by rw [hu] at hv; cases hv; exact ht hv'
      rw [den_succ_atom hat]
      have := hty a hat (by rw [hu]; rfl)
      have hs : shape D tabs a = tabs.ty u.type := by simp [shape, hu]
      rw [hs] at this
      rw [← this]; exact Val.retype_hasTy _ _

/-- A value `intOnly` admits, of integer shape, is never a pointer word. -/
theorem intOnly_not_ptr (hA : AsmHolds D tabs ρ A) {a : ID} {av : Value} (hav : D a = some av)
    {w : Width} (hw : tabs.ty av.type = .int w) (h : intOnly D tabs A a = true) (n : Nat) :
    NoPtr (den D tabs ρ n a) := by
  unfold intOnly at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [hav] at h
    simp only [Option.any_some, Bool.and_eq_true] at h
    obtain ⟨ht, hr⟩ := h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hr
    cases n with
    | zero => exact noPtr_poison
    | succ n =>
      rw [den_succ_term hav ht, rTab_eval hc, hw]
      exact noPtr_retype_int (rOpEval_noPtr _ _ _ _)
  · obtain ⟨⟨c, v⟩, hf, hm⟩ := List.any_eq_true.1 h
    split at hm
    · rename_i x y w' r hr
      intro p hp
      obtain ⟨N, hN⟩ := relOf_sound hA hf hr
      obtain ⟨xa, xb, h1, h2, -⟩ := hN (max N n) (Nat.le_max_left _ _)
      have hk := refines_ptr (hp ▸ den_fuel_mono D tabs ρ n (max N n) a (Nat.le_max_right _ _))
      simp only [Bool.or_eq_true, beq_iff_eq] at hm
      rcases hm with rfl | rfl
      · rw [h1] at hk; cases hk
      · rw [h2] at hk; cases hk
    · cases hm

theorem listedDefs_of {g : Func} {c : ID} {cv : Value} (hc : g.value? c = some cv)
    (hl : g.blocks.contains cv.block = true ∧ (g.block? cv.block).any (·.values.contains c) = true) :
    listedDefs g c = some cv := by
  simp only [listedDefs, hc, Option.filter, hl.1, hl.2, Bool.and_self, ↓reduceIte]

theorem constOp_eval (w : Width) (aux : Option AuxRef) (ai : Int64) :
    (evalPure (constOp w) (.int w) ai aux []).retype (.int w) =
      .int w (BitVec.ofInt w.bits ai.toInt) := by
  cases w
  all_goals exact retype_int_self _ _

/-- **A constant-folded argument refines.** -/
theorem fold_ref {g : Func} {ρ' : ID → Val} (hA : AsmHolds D tabs ρ A) {a c : ID}
    (h : foldOK D tabs A g a c = true) :
    ∀ n, Sem.Refines (den D tabs ρ n a) (den (listedDefs g) tabs ρ' n c)
  | 0 => .poison _
  | n + 1 => by
    unfold foldOK at h
    cases hav : D a with
    | none => rw [hav] at h; cases h
    | some av =>
    cases hcv : g.value? c with
    | none => rw [hav, hcv] at h; cases h
    | some cv =>
    rw [hav, hcv] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hl, ht⟩, hargs⟩, hk⟩ := h
    have hL := listedDefs_of hcv hl
    have hargs' : cv.args = #[] := Array.isEmpty_iff.1 hargs
    rw [den_succ_term hL ht, hargs']
    simp only [List.map_nil]
    have hT := den_hasTy hA.typed hav (n + 1)
    split at hk
    · rename_i hta htc
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨hop, hdec⟩ := hk
      rw [hop, htc]
      rw [hta] at hT
      generalize hd : den D tabs ρ (n + 1) a = z at hT
      cases z with
      | poison => exact .poison _
      | bool bb =>
        cases decides_sound hA rngFuel a _ hdec (n + 1) bb hd
        exact .bool _
      | _ => simp [Val.hasTy] at hT
    · rename_i w w' hta htc
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨⟨⟨rfl, hop⟩, hio⟩, hpt, hval⟩ := hk
      rw [hop, htc, constOp_eval]
      rw [hta] at hT
      have hnp := intOnly_not_ptr hA hav hta hio (n + 1)
      generalize hd : den D tabs ρ (n + 1) a = z at hT hnp
      cases z with
      | poison => exact .poison _
      | int w2 y =>
        simp only [Val.hasTy, beq_iff_eq] at hT
        subst hT
        obtain ⟨m1, m2, -, -⟩ := rng_sound hA rngFuel w2 a (n + 1) y hd
        have hy : y = BitVec.ofInt w2.bits cv.auxInt.toInt := BitVec.eq_of_toNat_eq (by omega)
        rw [hy]; exact .int _ _
      | ptr p => exact absurd rfl (hnp p)
      | _ => simp [Val.hasTy] at hT
    · cases hk


/-! ## The relation's definitions -/

theorem defOK_cases {D : ID → Option Value} {tabs : Tables} {F : Array (List (ID × Bool))}
    {inv : List (ID × Width × Rng)} {A : Asm} {g : Func} {fb : Block} {fv gv : Value}
    (h : defOK D tabs F inv A g fb fv gv = true) :
    sameDef fv gv = true ∨ valueOK D tabs A fv gv = true ∨
      (argsOK D tabs F inv A g fb fv gv = true ∧
        (sameDef fv { gv with args := fv.args } = true ∨
          valueOK D tabs A fv { gv with args := fv.args } = true)) := by
  unfold defOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (h | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)

theorem argsOK_spec {D : ID → Option Value} {tabs : Tables} {F : Array (List (ID × Bool))}
    {inv : List (ID × Width × Rng)} {A : Asm} {g : Func} {fb : Block} {fv gv : Value}
    (h : argsOK D tabs F inv A g fb fv gv = true) :
    gv.args.size = fv.args.size ∧ ∀ i < fv.args.size, fv.args[i]! = gv.args[i]! ∨
      foldOK D tabs (argAsm F inv A fb fv i) g fv.args[i]! gv.args[i]! = true := by
  unfold argsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  exact ⟨h.1, fun i hi => h.2 i hi⟩

theorem argAsm_of_not_phi {F : Array (List (ID × Bool))} {inv : List (ID × Width × Rng)}
    {A : Asm} {fb : Block} {fv : Value} (h : fv.op ≠ .Phi) (i : Nat) : argAsm F inv A fb fv i = A := by
  have : (fv.op == .Phi) = false := by simpa using h
  simp [argAsm, this]

theorem argAsm_of_phi {F : Array (List (ID × Bool))} {inv : List (ID × Width × Rng)}
    {A : Asm} {fb : Block} {fv : Value} (h : fv.op = .Phi) {i : Nat} {e : Edge}
    (he : fb.preds[i]? = some e) : argAsm F inv A fb fv i = { facts := factsAt F e.b, inv } := by
  simp [argAsm, h, he]

theorem refinesList_zip {f g : ID → Val} : ∀ {l1 l2 : List ID}, l1.length = l2.length →
    (∀ i (h1 : i < l1.length) (h2 : i < l2.length), Sem.Refines (f l1[i]) (g l2[i])) →
    RefinesList (l1.map f) (l2.map g)
  | [], [], _, _ => .nil
  | a :: l1, b :: l2, hl, h =>
    .cons (h 0 (by simp) (by simp)) (refinesList_zip (by simpa using hl)
      fun i h1 h2 => h (i + 1) (by simp; omega) (by simp; omega))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

end

end GoFV.Proof.ProveCheck
