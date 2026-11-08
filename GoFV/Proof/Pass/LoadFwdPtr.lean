import GoFV.Proof.PtrAddr
import GoFV.Proof.Pass.LoadFwdMem
import GoFV.Proof.Pass.RewriteTermDen

/-!
# Load-of-Store forwarding: pointers that evaluate alike (issue #151)

The validator's pointer relations, for a valuation `ρ` that is typed (`Term.Typed`) and whose
memory roots and `LocalAddr`s hold their definitions (`AtomSim.MemAtoms`), at every fuel:

* `ptrBase_den`: a pointer that evaluates to `P` is its base's pointer plus the offset
  (`RewriteCheck.ptrBase`: `OffPtr`s and `Copy`s at pointer shapes);
* `baseBlk_den`: a `LocalAddr`/`Addr` evaluates to the start of its allocation;
* `baseSame_den`, `samePtr_den`: pointers `baseSameB`/`samePtrB` relates are equal where both
  are pointers;
* `offSep_sep`: offsets `offSep` separates address separate bytes (`CSE.Mem.Sep`) from one base,
  so a `Load` reads through a `Store` at the other one (`load_write_sep`; `disjoint_sep` in
  `LoadFwdArg`).
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.CSE.Mem GoFV.Proof.Pass.Rewrite

theorem toList_one {a : Array ID} (h : a.size = 1) : a.toList = [a[0]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, l⟩⟩⟩ <;> simp_all

theorem toList_two {a : Array ID} (h : a.size = 2) : a.toList = [a[0]!, a[1]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩⟩ <;> simp_all

theorem toList_three {a : Array ID} (h : a.size = 3) : a.toList = [a[0]!, a[1]!, a[2]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨z', l⟩⟩⟩⟩⟩ <;> simp_all

theorem not_term_of {D : ID → Option Value} {x : ID} {v : Value} (hv : D x = some v)
    (ht : ¬ termOp v.op = true) : ¬ IsTerm D x := fun ⟨w, hw, hw'⟩ => by
  rw [hv] at hw; cases hw; exact ht hw'

theorem evalPure_copy (ty : Ty) (ai : Int64) (aux : Option AuxRef) (y : Val) :
    evalPure .Copy ty ai aux [y] = y := rfl

theorem evalPure_load (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val) :
    evalPure .Load ty ai aux args = loadOp ty args := rfl

theorem evalPure_offPtr (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val) :
    evalPure .OffPtr ty ai aux args = PtrOps.offPtr ai args := rfl

theorem evalPure_addPtr (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val) :
    evalPure .AddPtr ty ai aux args = PtrOps.addPtr args := rfl

theorem evalPure_ptrIndex (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val) :
    evalPure .PtrIndex ty ai aux args =
      PtrOps.ptrIndex (match ty with | .ptr e => e | _ => none) args := rfl

/-- A value retyped at a pointer shape is a pointer when it stays one: retyping keeps a
pointer's allocation and offset (a pointer's word is the pointer or its address). -/
theorem retype_ptr_eq {q P : Ptr} {t : Ty} (h : (Val.ptr q).retype t = .ptr P) : P = q := by
  have hw : q.word = .ptr P := by
    cases t with
    | int w => cases w <;> first | exact h | simp [Val.retype] at h
    | ptr e => exact h
    | _ => simp [Val.retype] at h
  rcases Ptr.word_cases q with ⟨-, h'⟩ | ⟨-, a, -, h'⟩ | ⟨-, h'⟩ <;> rw [h'] at hw <;> cases hw
  rfl

/-- Retyping at pointer shapes forgets the element size. -/
theorem retype_ptr_elem (e e' : Option Nat) (v : Val) :
    v.retype (.ptr e) = v.retype (.ptr e') := by
  cases v with
  | int w x => cases w <;> rfl
  | _ => rfl

/-- A value fixed by retyping at a pointer shape is `poison`, an integer word or a pointer. -/
theorem ptr_fixed {t : Ty} (ht : isPtrTy t = true) {w : Val} (h : w.retype t = w) :
    w = .poison ∨ (∃ x, w = .int .w64 x) ∨ ∃ p, w = .ptr p := by
  cases t with
  | ptr e =>
    cases w with
    | poison => exact .inl rfl
    | ptr p => exact .inr (.inr ⟨p, rfl⟩)
    | int w x => cases w <;> first | exact .inr (.inl ⟨x, rfl⟩) | simp [Val.retype] at h
    | _ => simp [Val.retype] at h
  | _ => simp [isPtrTy] at ht

theorem ptr_add_zero (p : Ptr) : p.add 0 = p := by
  simp [Ptr.add]

theorem ptr_add_add (p : Ptr) (a b : BitVec 64) : (p.add a).add b = p.add (a + b) := by
  simp [Ptr.add, BitVec.add_assoc]

/-- Two fuels of one pointer-word term read the same pointer. -/
theorem den_ptr_fuel {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {x : ID}
    {k k' : Nat} {p q : Ptr} (h : (den D tabs ρ k x).asPtrWord = some p)
    (h' : (den D tabs ρ k' x).asPtrWord = some q) : p = q := by
  rcases Nat.le_total k k' with hk | hk
  · have := Refines.asPtrWord (den_fuel_mono D tabs ρ k k' x hk) h
    rw [h'] at this; cases this; rfl
  · have := Refines.asPtrWord (den_fuel_mono D tabs ρ k' k x hk) h'
    rw [h] at this; cases this; rfl

/-- A retyped composite is `poison` or the composite of its retyped components. -/
theorem retypeFields_getD : ∀ {fs : List (Nat × Ty)} {vs vs' : List Val},
    Val.retypeFields fs vs = some vs' →
      ∀ i, ∃ t', vs'.getD i .poison = (vs.getD i .poison).retype t'
  | [], [], _, h, i => by
    simp only [Val.retypeFields, Option.some.injEq] at h
    subst h
    exact ⟨.bool, by simp [retype_poison]⟩
  | (_, t) :: fs, v :: vs, vs', h, i => by
    simp only [Val.retypeFields, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    cases i with
    | zero => exact ⟨t, rfl⟩
    | succ i => exact retypeFields_getD hws i
  | [], _ :: _, _, h, _ => by simp [Val.retypeFields] at h
  | _ :: _, [], _, h, _ => by simp [Val.retypeFields] at h

theorem word_ne_agg (p : Ptr) (vs : List Val) : p.word ≠ .agg vs := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp

/-- Only a composite retypes to a composite, componentwise. -/
theorem retype_eq_agg {v : Val} {t : Ty} {vs' : List Val} (h : v.retype t = .agg vs') :
    ∃ vs, v = .agg vs ∧ ∀ i, ∃ t', vs'.getD i .poison = (vs.getD i .poison).retype t' := by
  cases v with
  | agg vs =>
    refine ⟨vs, rfl, ?_⟩
    cases t with
    | agg fs n =>
      simp only [Val.retype] at h
      split at h
      · next ws hws => cases h; exact retypeFields_getD hws
      · cases h
    | str =>
      match vs, h with
      | [p, l], h =>
        simp only [Val.retype, Val.ofStr] at h
        split at h
        · cases h
          intro i
          match i with
          | 0 => exact ⟨.ptr none, Val.retypePtr_eq none p⟩
          | 1 => exact ⟨.int .w64, Val.retypeI64_eq l⟩
          | _ + 2 => exact ⟨.bool, by simp [retype_poison]⟩
        · cases h
    | slice e =>
      match vs, h with
      | [p, l, c], h =>
        simp only [Val.retype, Val.ofSlice] at h
        split at h
        · cases h
          intro i
          match i with
          | 0 => exact ⟨.ptr e, Val.retypePtr_eq e p⟩
          | 1 => exact ⟨.int .w64, Val.retypeI64_eq l⟩
          | 2 => exact ⟨.int .w64, Val.retypeI64_eq c⟩
          | _ + 3 => exact ⟨.bool, by simp [retype_poison]⟩
        · cases h
    | _ => simp [Val.retype] at h
  | poison => rw [retype_poison] at h; cases h
  | int w x =>
    cases t with
    | int w' => simp only [Val.retype] at h; split at h <;> cases h
    | ptr e => cases w <;> simp [Val.retype] at h
    | _ => simp [Val.retype] at h
  | ptr p =>
    cases t with
    | int w => cases w <;> simp [Val.retype, word_ne_agg] at h
    | ptr e => simp [Val.retype, word_ne_agg] at h
    | _ => simp [Val.retype] at h
  | tuple vs =>
    cases t with
    | tuple ts => simp only [Val.retype] at h; split at h <;> cases h
    | _ => simp [Val.retype] at h
  | blob bs =>
    cases t with
    | blob n => simp only [Val.retype] at h; split at h <;> cases h
    | _ => simp [Val.retype] at h
  | bool b => cases t <;> simp [Val.retype] at h
  | mem m => cases t <;> simp [Val.retype] at h
  | empty => cases t <;> simp [Val.retype] at h

/-- A value whose retype at any shape reads as a pointer reads as that pointer: the two word
shapes keep the word (`Val.retype_ptr_eq_i64`), and no other shape has a pointer word
(`Val.retype_hasTy`). -/
theorem asPtrWord_of_retype {v : Val} {t : Ty} {p : Ptr} (h : (v.retype t).asPtrWord = some p) :
    v.asPtrWord = some p := by
  have hty := Val.retype_hasTy t v
  cases t with
  | ptr e => exact Val.asPtrWord_of_retype_ptr h
  | int w =>
    cases w with
    | w64 =>
      rw [← Val.retype_ptr_eq_i64 v none] at h
      exact Val.asPtrWord_of_retype_ptr h
    | _ =>
      generalize v.retype _ = r at h hty
      cases r with
      | int w' y => cases w' <;> simp_all [Val.asPtrWord, Val.hasTy]
      | _ => simp_all [Val.asPtrWord, Val.hasTy]
  | _ =>
    generalize v.retype _ = r at h hty
    cases r with
    | int w' y => cases w' <;> simp_all [Val.asPtrWord, Val.hasTy]
    | _ => simp_all [Val.asPtrWord, Val.hasTy]

section
variable {tabs : Tables} {f : Func} {ρ : ID → Val}

/-- The value of a defined node is fixed by retyping at its shape. -/
theorem den_fix (hT : Term.Typed f.value? tabs ρ) {x : ID} {v : Value} (hv : f.value? x = some v)
    (k : Nat) : (den f.value? tabs ρ k x).retype (tabs.ty v.type) = den f.value? tabs ρ k x := by
  cases k with
  | zero => simp [den, Val.retype]
  | succ k =>
    by_cases ht : IsTerm f.value? x
    · obtain ⟨w, hw, hwt⟩ := ht
      rw [hv] at hw; cases hw
      rw [den_succ_term hv hwt, Val.retype_idem]
    · rw [den_succ_atom ht]
      have := hT x ht (by rw [hv]; rfl)
      simpa [shape, hv] using this

/-- **A constant term denotes its value** at the fuel of its depth and above (`den_succ_term`;
a `SliceLen`/`SliceCap` of a `SliceMake` by `AtomSim.opVal_sliceComp`). -/
theorem termConst_den :
    ∀ (k : Nat) (a : ID) (y : Val), termConst tabs f k a = some y →
      ∀ n, k ≤ n → den f.value? tabs ρ n a = y
  | 0, _, _, h, _, _ => by simp [termConst] at h
  | k + 1, a, y, h, n + 1, hn => by
    simp only [termConst] at h
    split at h
    next v hv =>
      split at h
      next hs =>
        cases k with
        | zero => cases h
        | succ j =>
        dsimp only at h
        split at h
        next l c hlc =>
          split at h
          next lv cv hl hc =>
            cases h
            obtain ⟨hop, m, mv, e, hva, hmv, hmop, hma, hty⟩ := AtomSim.sliceMakeLC_spec hlc
            have ht : termOp v.op = true := by rcases hop with h | h <;> rw [h] <;> rfl
            have htm : termOp mv.op = true := by rw [hmop]; rfl
            obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
            rw [den_succ_term hv ht, hva]
            simp only [List.map_toArray, List.map_cons, List.map_nil]
            rw [den_succ_term hmv htm, hty, hma]
            simp only [List.map_toArray, List.map_cons, List.map_nil]
            rw [termConst_den j l lv hl n' (by omega), termConst_den j c cv hc n' (by omega),
              hmop, AtomSim.opVal_sliceComp _ _ _ _ _ _ _ _ _ _ _ hop]
          next => cases h
        next => cases h
      next =>
        split at h
        next ht =>
          obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 h
          have hl : ∀ (l : List ID) (cs : List Val), l.mapM (termConst tabs f k) = some cs →
              l.map (den f.value? tabs ρ n) = cs := by
            intro l
            induction l with
            | nil => intro cs h; simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; simp [h]
            | cons b l ih =>
              intro cs h
              rw [List.mapM_cons] at h
              cases hc : termConst tabs f k b with
              | none => rw [hc] at h; cases h
              | some c =>
                cases hcs' : l.mapM (termConst tabs f k) with
                | none => rw [hc, hcs'] at h; cases h
                | some cs' =>
                  rw [hc, hcs'] at h
                  cases h
                  rw [List.map_cons, termConst_den k b c hc n (by omega), ih cs' hcs']
          rw [den_succ_term hv ht, hl _ cs hcs]
        next => cases h
    next => cases h
  | _ + 1, _, _, _, 0, hn => absurd hn (by omega)

theorem constIdx_spec {i : ID} {kk : BitVec 64} (h : constIdx? tabs f i = some kk) :
    termConst tabs f 4 i = some (.int .w64 kk) := by
  unfold constIdx? at h
  split at h
  · next hk => cases h; exact hk
  · cases h

/-- A `PtrIndex` by a constant index: the pointer word's pointer plus the index times the
element size (at a fuel where the index term is evaluated, `termConst_den`; `den` only grows
with the fuel, `den_fuel_mono`). -/
theorem ptrIndex_den {a : ID} {u : Value} (hu : f.value? a = some u) (hop : u.op = .PtrIndex)
    (hsz : u.args.size = 2) {e : Nat} (hty : tabs.ty u.type = .ptr (some e))
    {kk : BitVec 64} (hci : constIdx? tabs f u.args[1]! = some kk) {k : Nat} {p : Ptr}
    (h : (den f.value? tabs ρ k a).asPtrWord = some p) :
    ∃ k' q, (den f.value? tabs ρ k' u.args[0]!).asPtrWord = some q ∧
      p = q.add (kk * BitVec.ofNat 64 e) := by
  have ht : termOp u.op = true := by rw [hop]; rfl
  have hfo : GoFV.Proof.Rules.frameOp u.op = false := by rw [hop]; rfl
  have hK : (den f.value? tabs ρ (max k 4 + 1) a).asPtrWord = some p :=
    (den_fuel_mono f.value? tabs ρ k (max k 4 + 1) a (by omega)).asPtrWord h
  rw [den_succ_term hu ht, toList_two hsz, List.map_cons, List.map_cons, List.map_nil,
    GoFV.Proof.Rules.opVal_pure hfo, hop, evalPure_ptrIndex, hty, PtrOps.ptrIndex_retype_ptr,
    PtrOps.ptrIndex_asPtrWord,
    termConst_den 4 _ _ (constIdx_spec hci) (max k 4) (Nat.le_max_right _ _)] at hK
  cases hq : (den f.value? tabs ρ (max k 4) u.args[0]!).asPtrWord with
  | none => rw [hq] at hK; cases hK
  | some q =>
    rw [hq] at hK
    simp only [Option.bind_some, asOffset, Ptr.step?] at hK
    refine ⟨max k 4, q, hq, ?_⟩
    split at hK <;> cases hK
    rw [BitVec.signExtend_eq]

/-- A `wordStep?` (`Convert`, `ITab` of `IMake`): the argument's pointer word. -/
theorem wordStep_den {a c : ID} {u : Value} (hu : f.value? a = some u)
    (hs : wordStep? tabs f u = some c) {k : Nat} {p : Ptr}
    (h : (den f.value? tabs ρ k a).asPtrWord = some p) :
    ∃ k', (den f.value? tabs ρ k' c).asPtrWord = some p := by
  unfold wordStep? at hs
  split at hs
  · cases hs
  rename_i hpt
  obtain ⟨e, he⟩ : ∃ e, tabs.ty u.type = .ptr e := by
    revert hpt; cases tabs.ty u.type <;> simp [isPtrTy]
  cases k with
  | zero => simp [den, Val.asPtrWord] at h
  | succ k =>
  split at hs
  · -- `Convert` to a pointer type: the identity on the word
    rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hop, hsz⟩ := hc
    cases hs
    have ht : termOp u.op = true := by rw [hop]; rfl
    have hfo : GoFV.Proof.Rules.frameOp u.op = false := by rw [hop]; rfl
    rw [den_succ_term hu ht, toList_two hsz, List.map_cons, List.map_cons, List.map_nil,
      GoFV.Proof.Rules.opVal_pure hfo, he] at h
    replace h := asPtrWord_of_retype h
    rw [hop] at h
    exact ⟨k, h⟩
  · split at hs
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hop, hsz⟩ := hc
      split at hs
      · next m hm =>
        split at hs
        · -- `ITab (IMake x _)`: `x` retyped as the interface's first field, then as a pointer
          rename_i hc'
          simp only [Bool.and_eq_true, beq_iff_eq] at hc'
          obtain ⟨hmop, hmsz⟩ := hc'
          cases hs
          have ht : termOp u.op = true := by rw [hop]; rfl
          have hfo : GoFV.Proof.Rules.frameOp u.op = false := by rw [hop]; rfl
          rw [den_succ_term hu ht, toList_one hsz, List.map_cons, List.map_nil,
            GoFV.Proof.Rules.opVal_pure hfo, he] at h
          replace h := asPtrWord_of_retype h
          rw [hop] at h
          change (Comp.select 0 [den f.value? tabs ρ k u.args[0]!]).asPtrWord = some p at h
          cases k with
          | zero => simp [den, Comp.select, Val.asPtrWord] at h
          | succ k =>
          have hmt : termOp m.op = true := by rw [hmop]; rfl
          have hmfo : GoFV.Proof.Rules.frameOp m.op = false := by rw [hmop]; rfl
          rw [den_succ_term hm hmt, toList_two hmsz, List.map_cons, List.map_cons, List.map_nil,
            GoFV.Proof.Rules.opVal_pure hmfo, hmop] at h
          change (Comp.select 0 [(Val.agg [den f.value? tabs ρ k m.args[0]!,
            den f.value? tabs ρ k m.args[1]!]).retype (tabs.ty m.type)]).asPtrWord = some p at h
          generalize hr : (Val.agg _).retype _ = r at h
          cases r with
          | agg vs' =>
            obtain ⟨vs, hvs, hc⟩ := retype_eq_agg hr
            cases hvs
            obtain ⟨t', ht'⟩ := hc 0
            simp only [Comp.select] at h
            rw [ht'] at h
            exact ⟨k, asPtrWord_of_retype h⟩
          | _ => simp [Comp.select, Val.asPtrWord] at h
        · cases hs
      · cases hs
    · cases hs

/-- One `ptrStep?`: the argument's pointer plus the offset. -/
theorem ptrStep_den {a c : ID} {o : BitVec 64} (hs : ptrStep? tabs f a = some (c, o)) {k : Nat}
    {p : Ptr} (h : (den f.value? tabs ρ k a).asPtrWord = some p) :
    ∃ k' q, (den f.value? tabs ρ k' c).asPtrWord = some q ∧ p = q.add o := by
  unfold ptrStep? at hs
  cases hu : f.value? a with
  | none => rw [hu] at hs; cases hs
  | some u =>
  rw [hu] at hs
  dsimp only at hs
  split at hs
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨hop, hsz⟩, hpt⟩, -⟩ := hc
    obtain ⟨e, he⟩ : ∃ e, tabs.ty u.type = .ptr e := by
      revert hpt; cases tabs.ty u.type <;> simp [isPtrTy]
    have ht : termOp u.op = true := by rcases hop with h | h <;> rw [h] <;> rfl
    have hfo : GoFV.Proof.Rules.frameOp u.op = false := by
      rcases hop with h | h <;> rw [h] <;> rfl
    cases k with
    | zero => simp [den, Val.asPtrWord] at h
    | succ k =>
    refine ⟨k, ?_⟩
    rw [den_succ_term hu ht, toList_one hsz, List.map_cons, List.map_nil,
      GoFV.Proof.Rules.opVal_pure hfo, he] at h
    replace h := asPtrWord_of_retype h
    rcases hop with hop | hop
    · rw [hop, evalPure_offPtr, PtrOps.offPtr_asPtrWord] at h
      cases hq : (den f.value? tabs ρ k u.args[0]!).asPtrWord with
      | none => rw [hq] at h; cases h
      | some q =>
        rw [hq] at h
        simp only [Option.bind_some, Ptr.step?] at h
        refine ⟨q, rfl, ?_⟩
        split at h <;> cases h
        rw [hop]; rfl
    · rw [hop, evalPure_copy] at h
      refine ⟨p, h, ?_⟩
      rw [hop]
      exact (ptr_add_zero p).symm
  · split at hs
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hop, hsz⟩, -⟩ := hc
      split at hs
      · next e kk hty hci =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ptrIndex_den hu hop hsz hty hci h
      · cases hs
    · cases hw : wordStep? tabs f u with
      | none => rw [hw] at hs; cases hs
      | some c' =>
        rw [hw] at hs
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨k', hk'⟩ := wordStep_den hu hw h
        exact ⟨k', p, hk', (ptr_add_zero p).symm⟩

/-- **Base and offset**: a pointer word reads as its `ptrBase`'s pointer plus the offset. -/
theorem ptrBase_den :
    ∀ (n : Nat) (a : ID) (k : Nat) (p : Ptr), (den f.value? tabs ρ k a).asPtrWord = some p →
      ∃ k' q, (den f.value? tabs ρ k' (ptrBase tabs f n a).1).asPtrWord = some q ∧
        p = q.add (ptrBase tabs f n a).2
  | 0, a, k, p, h => ⟨k, p, h, (ptr_add_zero p).symm⟩
  | n + 1, a, k, p, h => by
    cases hs : ptrStep? tabs f a with
    | none =>
      simp only [ptrBase, hs]
      exact ⟨k, p, h, (ptr_add_zero p).symm⟩
    | some co =>
      obtain ⟨c, o⟩ := co
      simp only [ptrBase, hs]
      obtain ⟨k0, q0, h0, rfl⟩ := ptrStep_den hs h
      obtain ⟨k', q, hq, rfl⟩ := ptrBase_den n c k0 q0 h0
      exact ⟨k', q, hq, ptr_add_add q _ o⟩

/-- A pointer-shaped `LocalAddr` or word-shaped `Addr` with a known allocation (`baseBlk?`) reads
as its start. -/
theorem baseBlk_den (hM : MemAtoms f.value? tabs ρ) {a : ID} {B : Blk}
    (hB : baseBlk? tabs f a = some B) {k : Nat} {P : Ptr}
    (h : (den f.value? tabs ρ k a).asPtrWord = some P) : P = ⟨B, 0⟩ := by
  unfold baseBlk? at hB
  cases hu : f.value? a with
  | none => rw [hu] at hB; cases hB
  | some u =>
    rw [hu] at hB
    dsimp only at hB
    cases k with
    | zero => simp [den, Val.asPtrWord] at h
    | succ k =>
    split at hB
    · rename_i hl
      simp only [Bool.and_eq_true, beq_iff_eq] at hl
      obtain ⟨hl, hpt⟩ := hl
      obtain ⟨e, he⟩ : ∃ e, tabs.ty u.type = .ptr e := by
        revert hpt; cases tabs.ty u.type <;> simp [isPtrTy]
      have hat : ¬ IsTerm f.value? a := not_term_of hu (by rw [hl]; decide)
      rw [den_succ_atom hat] at h
      obtain ⟨N, hN⟩ := hM a u hu (by rw [hl]; rfl) (by intro h0; rw [h0] at h; cases h)
      obtain ⟨y, hy, hρ⟩ := hN N (Nat.le_refl _)
      unfold memDef at hy
      rw [hl] at hy
      simp only [Option.some.injEq] at hy
      subst hy
      cases hax : u.aux with
      | none => rw [hax] at hB; cases hB
      | some n =>
        rw [hax] at hB; cases hB
        have hsh : shape f.value? tabs a = .ptr e := by simp [shape, hu, he]
        rw [hρ, hax, hsh] at h
        replace h := asPtrWord_of_retype h
        simp only [Option.map_some, Option.getD_some, Val.asPtrWord, Option.some.injEq] at h
        exact h.symm
    · split at hB
      · rename_i _ hd
        simp only [Bool.and_eq_true, beq_iff_eq] at hd
        obtain ⟨hd, hpt⟩ := hd
        have ht : termOp u.op = true := by rw [hd]; rfl
        rw [den_succ_term hu ht, hd, GoFV.Proof.Rules.opVal_addr] at h
        replace h := asPtrWord_of_retype h
        unfold GoFV.Proof.Rules.addrVal at h
        split at hB
        · rename_i name _ _ _ hax
          cases hB
          rw [hax] at h
          simp only [Val.asPtrWord, Option.some.injEq] at h
          exact h.symm
        · cases hB
      · cases hB

/-- `termEqB`: the two terms evaluate equally, at every fuel. -/
theorem termEq_den : ∀ (n : Nat) (a b : ID), termEqB tabs f n a b = true →
    ∀ k, den f.value? tabs ρ k a = den f.value? tabs ρ k b
  | 0, a, b, h, k => by simp only [termEqB, beq_iff_eq] at h; rw [h]
  | n + 1, a, b, h, k => by
    unfold termEqB at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · rfl
    split at h
    · rename_i u w hu hw
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨ht, hop⟩, hty⟩, hai⟩, hax⟩, hsz⟩, hargs⟩ := h
      cases k with
      | zero => rfl
      | succ k =>
        rw [den_succ_term hu ht, den_succ_term hw (hop ▸ ht), ← hop, ← tyEq_sound hty, hai, hax]
        congr 2
        apply List.ext_getElem (by simp [hsz])
        intro i h1 h2
        simp only [List.getElem_map, Array.getElem_toList]
        have h1' : i < u.args.size := by simpa using h1
        have h2' : i < w.args.size := by simpa using h2
        refine termEq_den n _ _ (hargs (u.args[i], w.args[i]) ?_) k
        have hz : i < (u.args.toList.zip w.args.toList).length := by
          simp only [List.length_zip, Array.length_toList]; omega
        have := List.getElem_mem hz
        simpa [List.getElem_zip] using this
    · cases h

/-- Offsets of `idxSame` indices agree where both are integers. -/
theorem idxSame_den {i j : ID} (h : idxSame tabs f i j = true) {k k' : Nat} {o o' : BitVec 64}
    (hi : asOffset (den f.value? tabs ρ k i) = some o)
    (hj : asOffset (den f.value? tabs ρ k' j) = some o') : o = o' := by
  have hint : ∀ {v w : Val}, Sem.Refines v w → ∀ {o}, asOffset v = some o → asOffset w = some o :=
    fun hr _ ho => by cases hr <;> first | rfl | (simp [asOffset] at ho; done) | exact ho
  rw [← termEq_den 4 i j h k'] at hj
  rcases Nat.le_total k k' with hk | hk
  · have := hint (den_fuel_mono _ _ _ _ _ _ hk) hi
    rw [hj] at this; cases this; rfl
  · have := hint (den_fuel_mono _ _ _ _ _ _ hk) hj
    rw [hi] at this; cases this; rfl

/-- `AddPtr`/`PtrIndex` at a pointer shape reads as a pointer that depends only on its operand's
pointer and its index's offset. -/
theorem evalPure_ptrArith {op : Op} (hop : op = .AddPtr ∨ op = .PtrIndex) {e : Option Nat}
    {ai : Int64} {ax : Option AuxRef} {x i : Val} {P : Ptr}
    (h : (evalPure op (.ptr e) ai ax [x, i]).asPtrWord = some P) :
    ∃ p o, x.asPtrWord = some p ∧ asOffset i = some o ∧ ∀ x' i', x'.asPtrWord = some p →
      asOffset i' = some o → (evalPure op (.ptr e) ai ax [x', i']).asPtrWord = some P := by
  cases hx : x.asPtrWord with
  | none =>
    rcases hop with rfl | rfl
    · rw [evalPure_addPtr, PtrOps.addPtr_asPtrWord, hx] at h; cases h
    · rw [evalPure_ptrIndex, PtrOps.ptrIndex_asPtrWord, hx] at h; cases h
  | some p =>
  cases hi : asOffset i with
  | none =>
    rcases hop with rfl | rfl
    · rw [evalPure_addPtr, PtrOps.addPtr_asPtrWord, hx, hi] at h; cases h
    · rw [evalPure_ptrIndex, PtrOps.ptrIndex_asPtrWord, hx, hi] at h
      simp at h
  | some o =>
  refine ⟨p, o, rfl, rfl, fun x' i' hx' hi' => ?_⟩
  rcases hop with rfl | rfl
  · rw [evalPure_addPtr, PtrOps.addPtr_asPtrWord, hx, hi] at h
    rw [evalPure_addPtr, PtrOps.addPtr_asPtrWord, hx', hi']; exact h
  · rw [evalPure_ptrIndex, PtrOps.ptrIndex_asPtrWord, hx, hi] at h
    rw [evalPure_ptrIndex, PtrOps.ptrIndex_asPtrWord, hx', hi']; exact h

/-- **Equal bases** where both read as pointers. -/
theorem baseSame_den (hM : MemAtoms f.value? tabs ρ) :
    ∀ (n : Nat) (a b : ID), baseSameB tabs f n a b = true → ∀ {k k' : Nat} {p q : Ptr},
      (den f.value? tabs ρ k a).asPtrWord = some p →
        (den f.value? tabs ρ k' b).asPtrWord = some q → p = q
  | 0, a, b, h, k, k', p, q, ha, hb => by
    simp only [baseSameB, beq_iff_eq] at h
    subst h; exact den_ptr_fuel ha hb
  | n + 1, a, b, h, k, k', p, q, ha, hb => by
    unfold baseSameB at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ⟨h | h⟩ | h
    · subst h; exact den_ptr_fuel ha hb
    · split at h
      · rename_i x y hx hy
        rw [beq_iff_eq] at h; subst h
        rw [baseBlk_den hM hx ha, baseBlk_den hM hy hb]
      · cases h
    · cases hu : f.value? a with
      | none => rw [hu] at h; cases h
      | some u =>
      cases hw : f.value? b with
      | none => rw [hu, hw] at h; cases h
      | some w =>
      rw [hu, hw] at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hop, hop'⟩, hsu⟩, hsw⟩, hty⟩, hai⟩, hax⟩, -⟩, -⟩, hoff⟩, hbase⟩,
        hidx⟩, hpt⟩ := h
      obtain ⟨e, he⟩ : ∃ e, tabs.ty u.type = .ptr e := by
        revert hpt; cases tabs.ty u.type <;> simp [isPtrTy]
      have hwe : tabs.ty w.type = .ptr e := by rw [← tyEq_sound hty, he]
      have ht : termOp u.op = true := by rcases hop with h | h <;> rw [h] <;> rfl
      have hfo : GoFV.Proof.Rules.frameOp u.op = false := by
        rcases hop with h | h <;> rw [h] <;> rfl
      have hargs : ∀ {v : Value}, v.args.size = 2 → v.args.toList = [v.args[0]!, v.args[1]!] :=
        fun hs => toList_two hs
      cases k with
      | zero => simp [den, Val.asPtrWord] at ha
      | succ k =>
      cases k' with
      | zero => simp [den, Val.asPtrWord] at hb
      | succ k' =>
      rw [den_succ_term hu ht, hargs hsu, List.map_cons, List.map_cons, List.map_nil,
        GoFV.Proof.Rules.opVal_pure hfo, he] at ha
      replace ha := asPtrWord_of_retype ha
      rw [den_succ_term hw (hop' ▸ ht), hargs hsw, List.map_cons, List.map_cons, List.map_nil,
        GoFV.Proof.Rules.opVal_pure (hop' ▸ hfo), hwe] at hb
      replace hb := asPtrWord_of_retype hb
      obtain ⟨pa, oa, hpa, hoa, hia⟩ := evalPure_ptrArith hop ha
      obtain ⟨pb, ob, hpb, hob, -⟩ := evalPure_ptrArith (hop' ▸ hop) hb
      have hab : pa = pb := by
        obtain ⟨k1, qa, h1, e1⟩ := ptrBase_den 8 _ k pa hpa
        obtain ⟨k2, qb, h2, e2⟩ := ptrBase_den 8 _ k' pb hpb
        rw [e1, e2, hoff, baseSame_den hM n _ _ hbase h1 h2]
      have hoo : oa = ob := idxSame_den hidx hoa hob
      have := hia _ _ (hab ▸ hpb) (hoo ▸ hob)
      rw [← hop', ← hai, ← hax] at hb
      rw [this] at hb; cases hb; rfl

/-- **Equal pointers** (`samePtrB`) where both are pointers. -/
theorem samePtr_den (hM : MemAtoms f.value? tabs ρ) {a b : ID}
    (h : samePtrB tabs f a b = true) {k k' : Nat} {p q : Ptr}
    (ha : (den f.value? tabs ρ k a).asPtrWord = some p)
    (hb : (den f.value? tabs ρ k' b).asPtrWord = some q) : p = q := by
  unfold samePtrB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨k1, qa, h1, e1⟩ := ptrBase_den 8 a k p ha
  obtain ⟨k2, qb, h2, e2⟩ := ptrBase_den 8 b k' q hb
  rw [e1, e2, h.1, baseSame_den hM 8 _ _ h.2 h1 h2]

/-- Offsets `offSep` separates, from one base. -/
theorem offSep_sep {B : Ptr} {o o' : BitVec 64} {n k : Nat} (h : offSep o n o' k = true) :
    Sep (B.add o) n (B.add o') k := by
  unfold offSep at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  right; right; right
  simp only [Ptr.add, BitVec.toNat_add, BitVec.toNat_sub] at h ⊢
  have hB := B.off.isLt
  have ho := o.isLt
  have ho' := o'.isLt
  omega

end

/-- A `Load` after a write separate from it reads what it read before. -/
theorem load_write_sep {m m' : Mem} {q p : Ptr} {bs : Array Byte} {t : Ty}
    (hw : m.write q bs = some m') (hs : Sep p t.size q bs.size) : m'.load t p = m.load t p := by
  unfold Mem.load
  split <;> first | rfl | rw [read_write_sep hw hs]

end GoFV.Proof.Pass.LoadFwd
