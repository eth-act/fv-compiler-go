import GoFV.Proof.Cong
import GoFV.Opt.NumberLines
import Std.Tactic.Do

/-!
# `number lines` refines its input

`numberLines` only rewrites value and block positions (statement marks) and the CFG caches
(`numberLines_eraseF`), which `run` never reads (`run_congr`): the target's runs are the
source's. No well-formedness hypothesis is needed.
-/

open Std.Do

set_option mvcgen.warning false

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.NumberLines

theorem map_modify_of {α β : Type} (a : Array α) (i : Nat) (g : α → α) (h : α → β)
    (hg : ∀ x, h (g x) = h x) : (a.modify i g).map h = a.map h := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_map, Array.getElem_modify]
    split <;> simp [hg]

theorem eraseF_setVPos (f : Func) (v : ID) (p : Pos) : eraseF (setVPos f v p) = eraseF f := by
  simp only [eraseF, setVPos]
  rw [map_modify_of]
  intro o; cases o <;> rfl

theorem eraseF_setBPos (f : Func) (b : ID) (p : Pos) : eraseF (setBPos f b p) = eraseF f := by
  simp only [eraseF, setBPos]
  rw [map_modify_of]
  intro o; cases o <;> rfl

theorem eraseF_postorder (f : Func) : eraseF f.postorder.2 = eraseF f := by
  unfold Func.postorder
  split <;> rfl

theorem eraseF_cache (f : Func) (c : Caches) : eraseF { f with cache := c } = eraseF f := rfl

/-- `numberLines` changes only positions and caches. Every loop keeps the function's erasure
(the `Pos`-only loops over predecessors keep nothing). -/
theorem numberLines_eraseF (f : Func) : eraseF (numberLines f) = eraseF f := by
  generalize h : numberLines f = r
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨_, st⟩ => ⌜eraseF st.1 = eraseF f⌝
  · ⇓⟨_, st⟩ => ⌜eraseF st.1 = eraseF f⌝
  · ⇓⟨_, st⟩ => ⌜eraseF st.1 = eraseF f⌝
  · ⇓⟨_, st⟩ => ⌜eraseF st = eraseF f⌝
  · ⇓⟨_, st⟩ => ⌜eraseF st.1 = eraseF f⌝
  · ⇓_ => ⌜True⌝
  · ⇓⟨_, st⟩ => ⌜eraseF st.1 = eraseF f⌝
  · ⇓⟨_, st⟩ => ⌜eraseF st.1 = eraseF f⌝
  · ⇓⟨_, st⟩ => ⌜eraseF st = eraseF f⌝
  · ⇓⟨_, st⟩ => ⌜eraseF st.1 = eraseF f⌝
  · ⇓_ => ⌜True⌝
  with simp_all +zetaDelta [eraseF_setVPos, eraseF_setBPos, eraseF_postorder]

/-- **`number lines` refines its input** (every function, every environment). -/
theorem numberLines_refines {penv : PassEnv} {f : Func} {out : PassOut}
    (h : numberLinesPass penv f = .ok out) : Refines out.tables out.func penv.tables f := by
  simp only [numberLinesPass, Pass.ofFunc, pure, Except.pure, bind, Except.bind] at h
  cases h
  exact Refines.of_eraseF (numberLines_eraseF f)

end GoFV.Proof
