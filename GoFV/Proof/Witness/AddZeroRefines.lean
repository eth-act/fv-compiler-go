import GoFV.Proof.Witness.AddZero
import GoFV.Proof.Pass.Rewrite

/-!
# Witness of `checkedRewrite_refines`: `addZero`

`checkedRewrite_refines` with the sound one-rule set `{(Add64 (Const64 [0]) x) => x}` on the
hand-written `addZero(n) = 0 + n`: the pass rewrites (`addZero_checkedRewrite`, kernel
evaluation), both functions pass `check`, and with `Env.p1` the output returns `addZero(7) = 7`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

theorem addZero_refines (hr : Term.RetypeShapes) :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet azRules) azPassEnv addZero = .ok out ∧
      (out.func.value? 5).map (·.args) = some #[2, 1] ∧
      RefinesUnder Env.Mono out.tables out.func azTabs addZero ∧
      ∃ fuel m, run Env.p1 out.tables out.func [.i64 7] {} fuel = .returned [.i64 7] m := by
  obtain ⟨out, hc, -, h5, -, hf, hg⟩ := addZero_checkedRewrite
  have hR := GoFV.Proof.Pass.Rewrite.checkedRewrite_refines azRules_allSound hr hc hf hg
  refine ⟨out, hc, h5, hR, ?_⟩
  obtain ⟨m, hm⟩ := returnsInt_iff.1 addZero_checks.2.2
  obtain ⟨fuel', ho⟩ := hR Env.p1 Env.p1_mono [.i64 7] {} 1 (by rw [show azPassEnv.tables = azTabs from rfl, hm]; trivial)
  rw [show azPassEnv.tables = azTabs from rfl, hm] at ho
  refine ⟨fuel', ?_⟩
  generalize run Env.p1 out.tables out.func [.i64 7] {} fuel' = o at ho ⊢
  cases ho with
  | returned hl =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨_, rfl⟩

end GoFV.Proof.Witness
