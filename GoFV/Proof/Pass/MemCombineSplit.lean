import GoFV.Proof.Pass.MemCombineSem
import GoFV.Proof.AtomSimRef

/-!
# memcombine: pointers taken apart (issue #35)

`splitP_sound`: if `splitP` takes `p` apart into `base + idx + off` (`base` pointer-typed),
`p`'s value is a pointer `Q` and the index so far has a value, then `base` is a pointer `P`, the
new index has a value `I` and `Q + idx + off = P + I + off'` (`ptrAt`). The values are those of
`den` at one fuel (`V n := den D tabs ρ n`); values defined at a lower fuel keep their value at a
higher one (`den_lift_ptr`, `den_lift_int`).
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.MemCombine.Check GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}

theorem den_lift_ptr {n m : Nat} {x : ID} {P : Ptr} (hle : n ≤ m)
    (h : den D tabs ρ n x = .ptr P) : den D tabs ρ m x = .ptr P :=
  refines_ptr (h ▸ den_fuel_mono D tabs ρ n m x hle)

theorem den_lift_int {n m : Nat} {x : ID} {w : Width} {X : BitVec w.bits} (hle : n ≤ m)
    (h : den D tabs ρ n x = .int w X) : den D tabs ρ m x = .int w X :=
  refines_int (h ▸ den_fuel_mono D tabs ρ n m x hle)

theorem idxVal_lift {n m : Nat} (hle : n ≤ m) {i : Option ID} {I : BitVec 64}
    (h : idxVal (den D tabs ρ n) i = some I) : idxVal (den D tabs ρ m) i = some I :=
  idxVal_mono (fun y => den_fuel_mono D tabs ρ n m y hle) h

theorem retype_ptr_cases (t : Option Nat) (v : Val) :
    v.retype (.ptr t) = .poison ∨ ∃ P, v.retype (.ptr t) = .ptr P := by
  cases v with
  | int w x => cases w <;> first | exact .inl rfl | exact .inr ⟨_, rfl⟩
  | ptr p => exact .inr ⟨_, rfl⟩
  | _ => exact .inl rfl

/-- A pointer-typed value is a pointer or `poison`. -/
theorem den_ptrTyped (hT : Term.Typed D tabs ρ) {p : ID} (hp : ptrTyped tabs D p = true) (n : Nat) :
    den D tabs ρ n p = .poison ∨ ∃ P, den D tabs ρ n p = .ptr P := by
  unfold ptrTyped at hp
  cases hD : D p with
  | none => rw [hD] at hp; cases hp
  | some v =>
    rw [hD] at hp
    dsimp only at hp
    split at hp
    · rename_i t ht
      cases n with
      | zero => exact .inl rfl
      | succ n =>
        by_cases hte : termOp v.op = true
        · rw [den_succ_term hD hte, ht]; exact retype_ptr_cases _ _
        · have hat : ¬ IsTerm D p := fun ⟨v', hv', ht'⟩ => by
            rw [hD] at hv'; cases hv'; exact hte ht'
          rw [den_succ_atom hat]
          have hty := hT p hat (by rw [hD]; rfl)
          simp only [shape, hD, Option.map_some, Option.getD_some, ht] at hty
          rw [← hty]; exact retype_ptr_cases _ _
    · cases hp

theorem args_one {α : Type} {a : Array ID} (h : a.size = 1) (F : ID → α) :
    a.toList.map F = [F a[0]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, l⟩⟩⟩ <;> simp_all

theorem args_two {α : Type} {a : Array ID} (h : a.size = 2) (F : ID → α) :
    a.toList.map F = [F a[0]!, F a[1]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩⟩ <;> simp_all

/-- `splitP` stops at a value that is not pointer-typed. -/
theorem splitP_self {p : ID} (hp : ptrTyped tabs D p = false) (N : Nat) (i : Option ID) (o : Int) :
    splitP tabs D N p i o = (p, i, o) := by
  cases N with
  | zero => rfl
  | succ N =>
    unfold splitP
    cases hD : D p with
    | none => rfl
    | some v => simp [hp]

theorem den_term {n : Nat} {x : ID} {v : Value} (hD : D x = some v) (ht : termOp v.op = true)
    (hf : GoFV.Proof.Rules.frameOp v.op = false) :
    den D tabs ρ (n + 1) x = (evalPure v.op (tabs.ty v.type) v.auxInt v.aux
      (v.args.toList.map (den D tabs ρ n))).retype (tabs.ty v.type) := by
  rw [den_succ_term hD ht, GoFV.Proof.Rules.opVal_pure hf]

theorem retype_ptrTy_ptr {t : Ty} {v : Val} {Q : Ptr} (ht : ∃ e, t = .ptr e)
    (h : v.retype t = .ptr Q) : v = .ptr Q ∨ ∃ w x, v = .int w x := by
  obtain ⟨e, rfl⟩ := ht
  cases v with
  | ptr p => cases h; exact .inl rfl
  | int w x => exact .inr ⟨w, x, rfl⟩
  | _ => cases h

theorem ptrRes_eq {p Q : Ptr} (h : PtrOps.ptrRes p = .ptr Q) : p = Q := by
  unfold PtrOps.ptrRes at h; split at h <;> cases h; rfl

theorem asInt_eq {w : Width} {v : Val} {x : BitVec w.bits} (h : v.asInt w = some x) :
    v = .int w x := by
  cases v with
  | int w' y =>
    by_cases hw : w' = w
    · subst hw; simp only [Val.asInt, dite_true, Option.some.injEq] at h; rw [h]
    · simp [Val.asInt, hw] at h
  | _ => cases h

/-- The value of a `Const64` with a 64-bit shape. -/
theorem den_const64 {n : Nat} {x : ID} {c : Int} (h : const64 tabs D x = some c) :
    den D tabs ρ (n + 1) x = .int .w64 (BitVec.ofInt 64 c) := by
  unfold const64 at h
  cases hD : D x with
  | none => rw [hD] at h; cases h
  | some v =>
    rw [hD] at h
    dsimp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hop, hw⟩ := hc
      have hty : tabs.ty v.type = .int .w64 := by
        unfold intW at hw; split at hw <;> cases hw; assumption
      rw [den_term hD (by rw [hop]; decide) (by rw [hop]; decide), hop, hty]
      change (Conv.const .w64 v.auxInt).retype (.int .w64) = _
      simp [Conv.const, Val.retype]
    · cases h

/-- **`Add64 (Const64 c) j`** has the value `c + j`. -/
theorem addConst_sound {y j : ID} {c : Int} {n : Nat} {K : BitVec 64}
    (h : addConst tabs D y = some (c, j)) (hK : asOffset (den D tabs ρ n y) = some K) :
    ∃ J, asOffset (den D tabs ρ n j) = some J ∧ K = BitVec.ofInt 64 c + J := by
  sorry -- WIP: draft in tmp/addConst_sound_draft.lean hits a kernel type mismatch (simp on `Val.retype`)

/-- **`splitP` is sound**: `p` (its value at fuel `n`) plus the index (values at fuel `m ≥ n`)
and offset so far is `base + idx' + off'`. -/
theorem splitP_sound (hT : Term.Typed D tabs ρ) {m : Nat} : ∀ (N n : Nat) (p : ID)
    (i : Option ID) (o : Int) {b : ID} {i' : Option ID} {o' : Int} {Q : Ptr} {I : BitVec 64},
    n ≤ m → splitP tabs D N p i o = (b, i', o') → ptrTyped tabs D b = true →
    den D tabs ρ n p = .ptr Q → idxVal (den D tabs ρ m) i = some I →
    ∃ P I', den D tabs ρ m b = .ptr P ∧ idxVal (den D tabs ρ m) i' = some I' ∧
      ptrAt P I' o' = ptrAt Q I o
  | 0, n, p, i, o, b, i', o', Q, I, hle, hs, _, hp, hI => by
    cases hs; exact ⟨Q, I, den_lift_ptr hle hp, hI, rfl⟩
  | N + 1, n, p, i, o, b, i', o', Q, I, hle, hs, hb, hp, hI => by
    have stop : (b, i', o') = (p, i, o) → ∃ P I', den D tabs ρ m b = .ptr P ∧
        idxVal (den D tabs ρ m) i' = some I' ∧ ptrAt P I' o' = ptrAt Q I o := fun h => by
      cases h; exact ⟨Q, I, den_lift_ptr hle hp, hI, rfl⟩
    unfold splitP at hs
    cases hD : D p with
    | none => rw [hD] at hs; exact stop hs.symm
    | some v =>
      rw [hD] at hs
      dsimp only at hs
      by_cases hpt : ptrTyped tabs D p = true
      · simp only [hpt, Bool.not_true, Bool.false_eq_true, ite_false] at hs
        have hpty : ∃ e, tabs.ty v.type = .ptr e := by
          unfold ptrTyped at hpt; rw [hD] at hpt; dsimp only at hpt
          split at hpt
          · exact ⟨_, ‹_›⟩
          · cases hpt
        -- `p`'s value comes from its arguments at a lower fuel
        cases n with
        | zero => cases hp
        | succ n =>
        by_cases hoff : (v.op == .OffPtr && v.args.size == 1) = true
        · simp only [hoff, ite_true] at hs
          simp only [Bool.and_eq_true, beq_iff_eq] at hoff
          obtain ⟨hop, hsz⟩ := hoff
          have hp' := hp
          rw [den_term hD (by rw [hop]; decide) (by rw [hop]; decide), hop, args_one hsz] at hp'
          change (PtrOps.offPtr v.auxInt [den D tabs ρ n v.args[0]!]).retype _ = _ at hp'
          -- the argument is pointer-typed (else `splitP` stops at it, which is not)
          by_cases hat : ptrTyped tabs D v.args[0]! = true
          · rcases den_ptrTyped hT hat n with h0 | ⟨Q', h0⟩
            · rw [h0] at hp'
              change Val.retype _ .poison = _ at hp'
              rw [retype_poison] at hp'; cases hp'
            · rw [h0] at hp'
              obtain ⟨e, he⟩ := hpty
              rw [he] at hp'
              have hQ : Q'.add (BitVec.ofInt 64 v.auxInt.toInt) = Q := by
                change (PtrOps.ptrRes _).retype _ = _ at hp'
                unfold PtrOps.ptrRes at hp'
                split at hp' <;> cases hp'; rfl
              obtain ⟨P, I', h1, h2, h3⟩ := splitP_sound hT N n _ i _ (by omega) hs hb h0 hI
              refine ⟨P, I', h1, h2, ?_⟩
              rw [h3, ← hQ]
              simp only [ptrAt, Ptr.add, BitVec.ofInt_add]
              congr 1
              ac_rfl
          · rw [splitP_self (Bool.eq_false_iff.2 hat)] at hs
            cases hs; exact absurd hb hat
        · simp only [Bool.not_eq_true] at hoff
          simp only [hoff, Bool.false_eq_true, ite_false] at hs
          by_cases hadd : (v.op == .AddPtr && v.args.size == 2 && i.isNone) = true
          · simp only [hadd, ite_true] at hs
            simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hadd
            obtain ⟨⟨hop, hsz⟩, rfl⟩ := hadd
            have hI0 : I = 0 := by cases hI; rfl
            subst hI0
            have hp' := hp
            rw [den_term hD (by rw [hop]; decide) (by rw [hop]; decide), hop, args_two hsz] at hp'
            change (PtrOps.addPtr [den D tabs ρ n v.args[0]!, den D tabs ρ n v.args[1]!]).retype _ = _
              at hp'
            by_cases hat : ptrTyped tabs D v.args[0]! = true
            · rcases den_ptrTyped hT hat n with h0 | ⟨Q', h0⟩
              · rw [h0] at hp'
                change Val.retype _ .poison = _ at hp'
                rw [retype_poison] at hp'; cases hp'
              · rw [h0] at hp'
                obtain ⟨e, he⟩ := hpty
                rw [he] at hp'
                cases hk : asOffset (den D tabs ρ n v.args[1]!) with
                | none =>
                  simp only [PtrOps.addPtr, hk] at hp'
                  rw [retype_poison] at hp'; cases hp'
                | some K =>
                  have hQ : Q'.add K = Q := by
                    simp only [PtrOps.addPtr, hk] at hp'
                    unfold PtrOps.ptrRes at hp'
                    split at hp' <;> cases hp'; rfl
                  have hK : idxVal (den D tabs ρ m) (some v.args[1]!) = some K :=
                    idxVal_lift (n := n) (m := m) (i := some v.args[1]!) (by omega) hk
                  cases hac : addConst tabs D v.args[1]! with
                  | none =>
                    rw [hac] at hs
                    dsimp only at hs
                    obtain ⟨P, I', h1, h2, h3⟩ :=
                      splitP_sound hT N n _ (some v.args[1]!) o (by omega) hs hb h0 hK
                    refine ⟨P, I', h1, h2, ?_⟩
                    rw [h3, ← hQ]
                    simp only [ptrAt, Ptr.add]
                    congr 1
                    simp
                  | some cj =>
                    obtain ⟨c, j⟩ := cj
                    rw [hac] at hs
                    dsimp only at hs
                    obtain ⟨J, hJ, hKJ⟩ := addConst_sound hac hk
                    obtain ⟨P, I', h1, h2, h3⟩ := splitP_sound hT N n _ (some j) (o + c)
                      (by omega) hs hb h0 (idxVal_lift (n := n) (m := m) (i := some j) (by omega) hJ)
                    refine ⟨P, I', h1, h2, ?_⟩
                    rw [h3, ← hQ, hKJ]
                    simp only [ptrAt, Ptr.add, BitVec.add_zero, BitVec.ofInt_add]
                    congr 1
                    ac_rfl
            · have hself := splitP_self (tabs := tabs) (D := D) (Bool.eq_false_iff.2 hat) N
              cases hac : addConst tabs D v.args[1]! with
              | none =>
                rw [hac] at hs; dsimp only at hs; rw [hself] at hs; cases hs; exact absurd hb hat
              | some cj =>
                obtain ⟨c, j⟩ := cj
                rw [hac] at hs; dsimp only at hs; rw [hself] at hs; cases hs; exact absurd hb hat
          · simp only [Bool.not_eq_true] at hadd
            simp only [hadd, Bool.false_eq_true, ite_false] at hs
            exact stop hs.symm
      · simp only [Bool.not_eq_true] at hpt
        simp only [hpt, Bool.not_false, ite_true] at hs
        exact stop hs.symm

end

end GoFV.Proof.MemCombine
