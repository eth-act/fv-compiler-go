import GoFV.Proof.RunMono
import GoFV.Proof.Frame

variable [GoFV.SSA.Sem.Addrs]

/-!
# The `Phi` collection of `enterBlock` is monotone in refinement

On refined registers, `phiStep` gives the same `Phi`s with refined values (`phiStep_mono`), so
does the collection over a block's values (`phis_mono`), and setting them keeps the registers
refined (`setPhis_mono`).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- Collected `Phi`s refined: the same value IDs, refined values. -/
inductive PhiRefines : Option (ID × Val) → Option (ID × Val) → Prop where
  | none : PhiRefines none none
  | some (z : ID) {x y : Val} : Sem.Refines x y → PhiRefines (some (z, x)) (some (z, y))

/-- Lists of collected `Phi`s refined pointwise. -/
inductive PhisRefine : List (ID × Val) → List (ID × Val) → Prop where
  | nil : PhisRefine [] []
  | cons (z : ID) {x y : Val} {ps ps' : List (ID × Val)} : Sem.Refines x y → PhisRefine ps ps' →
      PhisRefine ((z, x) :: ps) ((z, y) :: ps')

theorem RegsRefine.join {r r' : Array (Option Val)} (h : RegsRefine r r') (a : ID) :
    ((r[a]?).join = none) ∨ ∃ x y, (r[a]?).join = some x ∧ (r'[a]?).join = some y ∧ Sem.Refines x y := by
  cases hx : (r[a]?).join with
  | none => exact .inl rfl
  | some x =>
    obtain ⟨y, hy, hxy⟩ := h.2 a x hx
    exact .inr ⟨x, y, rfl, hy, hxy⟩

/-- **One `Phi` step is monotone** (same function and value types). -/
theorem phiStep_mono (ctx : Ctx) {fr fr' : Frame} (h : RegsRefine fr.regs fr'.regs) (i : Nat)
    (z : ID) : Res.Rel PhiRefines (phiStep ctx fr i z) (phiStep ctx fr' i z) := by
  unfold phiStep
  split
  · split
    · split
      · next a _ =>
        rcases h.join a with hx | ⟨x, y, hx, hy, hxy⟩
        · rw [hx]; exact .stuck _ _
        · rw [hx, hy]; exact .ok (.some z (retype_mono _ hxy))
      · exact .stuck _ _
    · exact .ok .none
  · exact .stuck _ _

/-- **The `Phi` collection is monotone.** -/
theorem phis_mono (ctx : Ctx) {fr fr' : Frame} (h : RegsRefine fr.regs fr'.regs) (i : Nat) :
    ∀ l : List ID, Res.Rel PhisRefine (l.filterMapM (phiStep ctx fr i)) (l.filterMapM (phiStep ctx fr' i))
  | [] => by rw [List.filterMapM_nil, List.filterMapM_nil]; exact .ok .nil
  | z :: l => by
    rw [List.filterMapM_cons, List.filterMapM_cons]
    have hz := phiStep_mono ctx h i z
    revert hz
    generalize phiStep ctx fr i z = o
    generalize phiStep ctx fr' i z = o'
    intro hz
    cases hz with
    | ok hp =>
      cases hp with
      | none => exact phis_mono ctx h i l
      | some z hxy =>
        change Res.Rel PhisRefine ((List.filterMapM (phiStep ctx fr i) l).bind fun r => .ok (_ :: r))
          ((List.filterMapM (phiStep ctx fr' i) l).bind fun r => .ok (_ :: r))
        exact Res.Rel.bind (phis_mono ctx h i l) fun ps ps' hps => .ok (.cons z hxy hps)
    | panic e hm => exact .panic e hm
    | stuck msg r => exact .stuck _ _

theorem RegsRefine.set {r r' : Array (Option Val)} (h : RegsRefine r r') (z : ID) {x y : Val}
    (hxy : Sem.Refines x y) : RegsRefine (r.set! z (some x)) (r'.set! z (some y)) := by
  refine ⟨by simp [h.1], fun a v hv => ?_⟩
  by_cases hza : z = a
  · subst hza
    by_cases hlt : z < r.size
    · have hlt' : z < r'.size := h.1 ▸ hlt
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt,
        Array.getElem?_setIfInBounds_self_of_lt hlt', Option.join_some, Option.some.injEq] at hv ⊢
      subst hv; exact ⟨y, rfl, hxy⟩
    · have hlt' : ¬ z < r'.size := h.1 ▸ hlt
      simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt, hlt', dite_false] at hv ⊢
      exact h.2 z v hv
  · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hza] at hv ⊢
    exact h.2 a v hv

/-- **Setting the collected `Phi`s keeps the registers refined.** -/
theorem setPhis_mono : ∀ {ps ps' : List (ID × Val)} {r r' : Array (Option Val)},
    PhisRefine ps ps' → RegsRefine r r' → RegsRefine (setPhis ps r) (setPhis ps' r')
  | _, _, _, _, .nil, h => h
  | _, _, r, r', .cons (x := x) (y := y) (ps := ps) (ps' := ps') z hxy t, h => by
    show RegsRefine (setPhis ps (r.set! z (some x))) (setPhis ps' (r'.set! z (some y)))
    exact setPhis_mono t (h.set z hxy)

end GoFV.Proof
