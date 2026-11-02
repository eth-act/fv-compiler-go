import GoFV.Proof.Pass.MemCombineSem
import GoFV.Proof.AtomSimRef
import GoFV.Proof.PtrAddr

/-!
# memcombine: pointers taken apart (issue #35)

`splitP_sound`: if `splitP` takes `p` apart into `base + idx + off` (`base` pointer-typed),
`p`'s value reads as a pointer `Q` (a pointer word, `Val.asPtrWord`) and the index so far has a
value, then `base` reads as a pointer `P`, the new index has a value `I` and
`Q + idx + off = P + I + off'` (`ptrAt`). Pointer arithmetic reads its operand as a pointer word
(`PtrOps.offPtr_asPtrWord`, `PtrOps.addPtr_asPtrWord`), so an integer word steps like the pointer
at its address. The values are those of `den` at one fuel (`V n := den D tabs ρ n`); values
defined at a lower fuel keep their value at a higher one (`den_lift_ptr`, `den_lift_int`).
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.MemCombine.Check GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}

theorem den_lift_ptr {n m : Nat} {x : ID} {P : Ptr} (hle : n ≤ m)
    (h : (den D tabs ρ n x).asPtrWord = some P) : (den D tabs ρ m x).asPtrWord = some P :=
  (den_fuel_mono D tabs ρ n m x hle).asPtrWord h

theorem den_lift_int {n m : Nat} {x : ID} {w : Width} {X : BitVec w.bits} (hle : n ≤ m)
    (h : den D tabs ρ n x = .int w X) : den D tabs ρ m x = .int w X :=
  refines_int (h ▸ den_fuel_mono D tabs ρ n m x hle)

theorem idxVal_lift {n m : Nat} (hle : n ≤ m) {i : Option ID} {I : BitVec 64}
    (h : idxVal (den D tabs ρ n) i = some I) : idxVal (den D tabs ρ m) i = some I :=
  idxVal_mono (fun y => den_fuel_mono D tabs ρ n m y hle) h

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

/-- A step of pointer arithmetic that stays in its window adds. -/
theorem step?_add_eq {p q : Ptr} {k : BitVec 64} (h : p.step? k = some q) : p.add k = q := by
  unfold Ptr.step? at h; split at h <;> cases h; rfl

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
  unfold addConst at h
  cases hD : D y with
  | none => rw [hD] at h; cases h
  | some v =>
    rw [hD] at h
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hop, hsz⟩, hw⟩ := hc
      have hty : tabs.ty v.type = .int .w64 := by
        unfold intW at hw; split at hw <;> cases hw; assumption
      cases n with
      | zero => cases hK
      | succ n =>
      rw [den_term hD (by rw [hop]; decide) (by rw [hop]; decide), hop, hty, args_two hsz] at hK
      change asOffset ((Sem.Int.add .w64 [den D tabs ρ n v.args[0]!, den D tabs ρ n v.args[1]!]).retype
        (.int .w64)) = some K at hK
      cases h0 : (den D tabs ρ n v.args[0]!).asInt .w64 with
      | none => simp [Sem.Int.add, int2, h0, retype_poison, asOffset] at hK
      | some x =>
      cases h1 : (den D tabs ρ n v.args[1]!).asInt .w64 with
      | none => simp [Sem.Int.add, int2, h0, h1, retype_poison, asOffset] at hK
      | some y' =>
      have e0 := asInt_eq h0
      have e1 := asInt_eq h1
      have hK' : K = x + y' := by
        rw [e0, e1] at hK
        have h2 : some (((x + y').setWidth 64).signExtend 64) = some K := hK
        rw [BitVec.setWidth_eq, BitVec.signExtend_eq] at h2
        exact (Option.some.inj h2).symm
      cases n with
      | zero => cases e0
      | succ n =>
      split at h
      · rename_i c' hc'
        cases h
        rw [den_const64 hc'] at e0
        cases e0
        refine ⟨y', ?_, hK'⟩
        rw [den_lift_int (Nat.le_succ _) e1]
        show some ((y' : BitVec 64).signExtend 64) = some y'
        rw [BitVec.signExtend_eq]
      · rename_i c' hc0 hc'
        cases h
        rw [den_const64 hc'] at e1
        cases e1
        refine ⟨x, ?_, by rw [hK', BitVec.add_comm]⟩
        rw [den_lift_int (Nat.le_succ _) e0]
        show some ((x : BitVec 64).signExtend 64) = some x
        rw [BitVec.signExtend_eq]
      · cases h
    · cases h

/-- **`splitP` is sound**: `p` (its value at fuel `n`, read as a pointer word) plus the index
(values at fuel `m ≥ n`) and offset so far is `base + idx' + off'`. -/
theorem splitP_sound {m : Nat} : ∀ (N n : Nat) (p : ID)
    (i : Option ID) (o : Int) {b : ID} {i' : Option ID} {o' : Int} {Q : Ptr} {I : BitVec 64},
    n ≤ m → splitP tabs D N p i o = (b, i', o') → ptrTyped tabs D b = true →
    (den D tabs ρ n p).asPtrWord = some Q → idxVal (den D tabs ρ m) i = some I →
    ∃ P I', (den D tabs ρ m b).asPtrWord = some P ∧ idxVal (den D tabs ρ m) i' = some I' ∧
      ptrAt P I' o' = ptrAt Q I o
  | 0, n, p, i, o, b, i', o', Q, I, hle, hs, _, hp, hI => by
    cases hs; exact ⟨Q, I, den_lift_ptr hle hp, hI, rfl⟩
  | N + 1, n, p, i, o, b, i', o', Q, I, hle, hs, hb, hp, hI => by
    have stop : (b, i', o') = (p, i, o) → ∃ P I', (den D tabs ρ m b).asPtrWord = some P ∧
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
        obtain ⟨e, he⟩ : ∃ e, tabs.ty v.type = .ptr e := by
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
          rw [den_term hD (by rw [hop]; decide) (by rw [hop]; decide), hop, args_one hsz, he]
            at hp'
          change ((PtrOps.offPtr v.auxInt [den D tabs ρ n v.args[0]!]).retype _).asPtrWord = _
            at hp'
          rw [Val.asPtrWord_retype_ptr, PtrOps.offPtr_asPtrWord] at hp'
          obtain ⟨Q', h0, hQ⟩ := Option.bind_eq_some_iff.1 hp'
          have hQ := step?_add_eq hQ
          -- the argument is pointer-typed (else `splitP` stops at it, which is not)
          by_cases hat : ptrTyped tabs D v.args[0]! = true
          · obtain ⟨P, I', h1, h2, h3⟩ := splitP_sound N n _ i _ (by omega) hs hb h0 hI
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
            rw [den_term hD (by rw [hop]; decide) (by rw [hop]; decide), hop, args_two hsz, he]
              at hp'
            change ((PtrOps.addPtr [den D tabs ρ n v.args[0]!, den D tabs ρ n v.args[1]!]).retype
              _).asPtrWord = _ at hp'
            rw [Val.asPtrWord_retype_ptr, PtrOps.addPtr_asPtrWord] at hp'
            obtain ⟨Q', h0, hp''⟩ := Option.bind_eq_some_iff.1 hp'
            obtain ⟨K, hk, hQ⟩ := Option.bind_eq_some_iff.1 hp''
            have hQ := step?_add_eq hQ
            by_cases hat : ptrTyped tabs D v.args[0]! = true
            · have hK : idxVal (den D tabs ρ m) (some v.args[1]!) = some K :=
                idxVal_lift (n := n) (m := m) (i := some v.args[1]!) (by omega) hk
              cases hac : addConst tabs D v.args[1]! with
              | none =>
                rw [hac] at hs
                dsimp only at hs
                obtain ⟨P, I', h1, h2, h3⟩ :=
                  splitP_sound N n _ (some v.args[1]!) o (by omega) hs hb h0 hK
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
                obtain ⟨P, I', h1, h2, h3⟩ := splitP_sound N n _ (some j) (o + c)
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
