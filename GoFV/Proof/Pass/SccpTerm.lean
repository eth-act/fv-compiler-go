import GoFV.Proof.Pass.SccpInv
import GoFV.Proof.Pass.KnownBitsTerm

/-!
# sccp: atoms' arguments and terminators as terms (issue #32)

The premises `AtomArgsRefP` and `StepRefsP` of the atom simulation under sccp's invariant
`sccpInv`. For valuations whose atoms satisfy their claims, every value satisfies its claim as a
term too (`sc_den`), so a value with a constant cell denotes `poison` or that constant. Hence each
value listed in `f` is refined, one fuel later, by the same value listed in `g` (`sc_ref`):
unchanged, or the constant term `repOK` allows. Atoms of `g` are unchanged atoms of `f`, and
blocks keep their kinds, successors and controls (`blocksOK`).
-/

namespace GoFV.Proof.Sccp

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Sccp GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim GoFV.Proof.Pass.Rewrite GoFV.Proof.KnownBits

section
variable {tabs : Tables} {f g : Func} {C : Array (Option Lat)} {vis : Array Edge} {R : Array Bool}
  {ce : CheckEnv} (hwf : WF ce f) (K : Facts tabs f g C vis R)
include hwf K

/-- Every value satisfies its claim as a term if the atoms satisfy theirs. -/
theorem sc_den {ρ : ID → Val} (hP : ∀ a, ¬ IsTerm f.value? a → Claim tabs f C a (ρ a)) :
    ∀ n x, Claim tabs f C x (den f.value? tabs ρ n x)
  | 0, x => Claim.poison _ _ _ x
  | n + 1, x => by
    by_cases ht : IsTerm f.value? x
    · obtain ⟨v, hv, hop⟩ := ht
      rw [den_succ_term hv hop]
      exact sc_term hwf K hv hop _ fun a _ => sc_den hP n a
    · rw [den_succ_atom ht]; exact hP x ht

/-- **Values as terms**: each value listed in `f` is refined, one fuel later, by the same value
listed in `g`, for valuations whose atoms satisfy their claims. -/
theorem sc_ref {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ')
    (hP : ∀ a, ¬ IsTerm f.value? a → Claim tabs f C a (ρ a)) :
    ∀ n x, LM f x → Sem.Refines (den f.value? tabs ρ n x) (den (listedDefs g) tabs ρ' (n + 1) x)
  | 0, _, _ => .poison _
  | n + 1, x, hx => by
    obtain ⟨b, hb, fb, hfb, hxv, u, hu, hub⟩ := listedMarks_sound f x hx
    have hrep := K.rep x (lt_of_value? hu)
    unfold repOK at hrep
    rw [hu] at hrep
    cases hw : g.value? x with
    | none => rw [hw] at hrep; cases hrep
    | some w =>
      rw [hw] at hrep
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrep
      obtain ⟨⟨-, hblk⟩, hrep⟩ := hrep
      obtain ⟨gb, hgb, hxg, hmg⟩ := marked_g K.atoms K.blocks hb hfb hxv hw (hblk.trans hub)
      have hL : listedDefs g x = some w := by rw [listedDefs_of_marked hmg, hw]
      rcases hrep with ⟨⟨⟨⟨hop, hty⟩, hai⟩, hax⟩, hargs⟩ | ⟨⟨⟨ht, hnil⟩, hty⟩, hc⟩
      · by_cases ht : termOp u.op = true
        · rw [den_succ_term hu ht, den_succ_term hL (hop ▸ ht), hop, hty, hai, hax, hargs]
          apply retype_mono; apply evalPure_mono
          refine refinesList_map fun a ha => sc_ref hρ hP n a ?_
          exact (closedOK_facts K.cf b hb fb hfb).2 x hxv u hu a (Array.mem_toList_iff.1 ha)
        · rw [den_succ_atom (not_term_of hu ht), den_succ_atom (not_term_of hL (hop ▸ ht))]
          exact hρ x
      · -- `x` became a constant term of its claimed value
        split at hc
        · rename_i c hcx
          have hnil' : w.args = #[] := Array.isEmpty_iff.1 hnil
          rw [den_succ_term hL ht, hnil', Array.toList_empty, List.map_nil, scalarEq_eq hc]
          exact sc_den hwf K hP (n + 1) x c hcx
        · cases hc

theorem sc_termRefP {x : ID} (hx : LM f x) (b : ID) :
    TermRefP ((sccpInv hwf K).P b) (SAnc f b) f.value? tabs x (listedDefs g) tabs x :=
  fun n => ⟨n + 1, fun _ _ hρ _ _ hP _ => sc_ref hwf K hρ hP n x hx⟩

/-- **Atoms' arguments.** -/
theorem sc_atomArgs : AtomArgsRefP (sccpInv hwf K) g := by
  intro b hb gb hgb a ha u hu ht
  obtain ⟨fb, hfb, -, hatoms⟩ := atomsOK_facts K.atoms b hb gb hgb
  obtain ⟨haf, u', hu', hop, hty, hai, hax, hsz⟩ := hatoms a ha u hu ht
  refine ⟨u', hu', hop, hty, hai, hax, hsz, fun i hi => ?_⟩
  have hrep := K.rep a (lt_of_value? hu')
  unfold repOK at hrep
  rw [hu', hu] at hrep
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrep
  have hargs : u.args = u'.args := by
    rcases hrep.2 with ⟨-, h⟩ | ⟨⟨⟨h, -⟩, -⟩, -⟩
    · exact h
    · rw [h] at ht; cases ht
  have hbf : b ∈ f.blocks := blocks_eq K.atoms ▸ hb
  have hi' : i < u'.args.size := hargs ▸ hi
  rw [hargs]
  exact sc_termRefP hwf K ((closedOK_facts K.cf b hbf fb hfb).2 a haf u' hu' _
    (by rw [getElem!_pos u'.args i hi']; exact Array.getElem_mem hi')) b

/-- **Controls.** -/
theorem sc_controls : ControlsRefP (sccpInv hwf K) g := by
  intro b hb fb gb hfb hgb
  have hbf : b ∈ f.blocks := blocks_eq K.atoms ▸ hb
  obtain ⟨gb', hgb', -, -, -, hctl, -⟩ := blocksOK_facts K.blocks hbf hfb
  rw [hgb] at hgb'; cases hgb'
  refine ⟨by rw [hctl], fun k hk => ?_⟩
  rw [← hctl]
  have hk' : k < fb.controls.size := hctl ▸ hk
  exact sc_termRefP hwf K ((closedOK_facts K.cf b hbf fb hfb).1 _
    (by rw [getElem!_pos fb.controls k hk']; exact Array.getElem_mem hk')) b

/-- **Terminators**. -/
theorem sc_steps : StepRefsP (sccpInv hwf K) g :=
  steps_of_controls K.atoms K.blocks (sc_controls hwf K)

end

end GoFV.Proof.Sccp
