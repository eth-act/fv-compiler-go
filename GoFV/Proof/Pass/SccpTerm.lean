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

/-! ## Blocks -/

theorem blocksOK_facts {tabs : Tables} {f g : Func} {C : Array (Option Lat)}
    (h : blocksOK tabs f g C = true) {b : ID} (hb : b ∈ f.blocks) {fb : Block}
    (hfb : f.block? b = some fb) :
    ∃ gb, g.block? b = some gb ∧ fb.id = gb.id ∧ (∀ x ∈ fb.values, x ∈ gb.values) ∧
      ((fb.kind = gb.kind ∧ fb.succs = gb.succs ∧ fb.controls = gb.controls) ∨
        firstOK tabs f C fb gb = true) := by
  unfold blocksOK at h
  have := (Array.all_eq_true_iff_forall_mem.1 h) b hb
  rw [hfb] at this
  cases hgb : g.block? b with
  | none => rw [hgb] at this; cases this
  | some gb =>
    rw [hgb] at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
    obtain ⟨⟨hid, hv⟩, hk⟩ := this
    refine ⟨gb, rfl, hid, fun x hx => ?_, ?_⟩
    · rw [hv] at hx
      obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 hx
      exact Array.getElem_mem _
    · rcases hk with ⟨⟨h1, h2⟩, h3⟩ | h
      · exact .inl ⟨h1, h2, h3⟩
      · exact .inr h

theorem firstOK_spec {tabs : Tables} {f : Func} {C : Array (Option Lat)} {fb gb : Block}
    (h : firstOK tabs f C fb gb = true) :
    fb.kind = .If ∧ gb.kind = .First ∧ gb.controls = #[] ∧ (∀ e ∈ fb.succs, e ∈ gb.succs) ∧
      ∃ c t e, fb.controls[0]? = some c ∧ cval tabs f C c = some (.bool t) ∧
        fb.succs[if t then 0 else 1]? = some e ∧ gb.succs[0]? = some e := by
  unfold firstOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Array.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, Array.isEmpty_iff.1 h3, h4, ?_⟩
  cases hc : fb.controls[0]? with
  | none => simp [hc] at h5
  | some c =>
    simp only [hc, Option.bind_some] at h5
    split at h5
    · rename_i t ht
      simp only [Bool.and_eq_true, beq_iff_eq] at h5
      obtain ⟨hs, he⟩ := h5
      obtain ⟨e, he'⟩ := Option.isSome_iff_exists.1 hs
      exact ⟨c, t, e, rfl, ht, he', he.trans he'⟩
    · cases h5

theorem marked_g {tabs : Tables} {f g : Func} {C : Array (Option Lat)}
    (hA : atomsOK f g = true) (hB : blocksOK tabs f g C = true) {x : ID}
    {b : ID} (hb : b ∈ f.blocks) {fb : Block} (hfb : f.block? b = some fb)
    (hx : x ∈ fb.values) {w : Value} (hw : g.value? x = some w) (hwb : w.block = b) :
    ∃ gb, g.block? b = some gb ∧ x ∈ gb.values ∧ Marked g x := by
  obtain ⟨gb, hgb, -, hsub, -⟩ := blocksOK_facts hB hb hfb
  have hxg := hsub x hx
  exact ⟨gb, hgb, hxg, b, blocks_eq hA ▸ hb, gb, hgb, hxg, w, hw, hwb⟩

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
      obtain ⟨gb, hgb, hxg, hmg⟩ := Sccp.marked_g K.atoms K.blocks hb hfb hxv hw (hblk.trans hub)
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

theorem sc_termRefP {x : ID} (hx : LM f x) (b : ID) (S : ID → Prop) :
    TermRefP ((sccpInv hwf K).P b) S f.value? tabs x (listedDefs g) tabs x :=
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
  have hx := (closedOK_facts K.cf b hbf fb hfb).2 a haf u' hu' u'.args[i]!
    (by rw [getElem!_pos u'.args i hi']; exact Array.getElem_mem hi')
  exact ⟨fun _ => sc_termRefP hwf K hx b _, fun _ p _ _ _ _ _ => sc_termRefP hwf K hx p _⟩

/-- The controls of a block of `g` as terms. -/
theorem sc_controlRef {b : ID} (hb : b ∈ f.blocks) {fb : Block} (hfb : f.block? b = some fb)
    {k : Nat} (hk : k < fb.controls.size) :
    TermRefP ((sccpInv hwf K).P b) (SAnc f b) f.value? tabs fb.controls[k]! (listedDefs g) tabs
      fb.controls[k]! :=
  sc_termRefP hwf K ((closedOK_facts K.cf b hb fb hfb).1 _
    (by rw [getElem!_pos fb.controls k hk]; exact Array.getElem_mem hk)) b _

/-- An `If` turned `First` towards the successor its constant control picks. -/
theorem sc_first {b : ID} {fb gb : Block} (hF : firstOK tabs f C fb gb = true) :
    StepRefP ((sccpInv hwf K).P b) (SAnc f b) f.value? tabs fb (listedDefs g) gb := by
  obtain ⟨hkf, hkg, hcg, -, c, t, e, hc, hcv, he, he0⟩ := firstOK_spec hF
  intro n
  refine ⟨0, fun ρ ρ' _ _ _ hP _ => ?_⟩
  have hcl := sc_den hwf K hP n c (.bool t) hcv
  have hT : stepVals gb (gb.controls.toList.map (den (listedDefs g) tabs ρ' 0)) = .ok (.goto e) := by
    unfold stepVals; rw [hkg]; unfold succ; rw [he0]; rfl
  rw [hT]
  have hcs : (fb.controls.toList.map (den f.value? tabs ρ n))[0]? = some (den f.value? tabs ρ n c) := by
    simp [hc]
  unfold stepVals
  rw [hkf]
  simp only [ctlV, hcs, bind, Res.bind]
  rcases refines_scalar (.inr ⟨t, rfl⟩) hcl with h0 | h0 <;> rw [h0]
  · exact .stuck _ _
  · cases t
    · have : (Sem.succ fb 1) = .ok (.goto e) := by unfold succ; rw [show (1 : Nat) = if false = true then 0 else 1 from rfl, he]; rfl
      simp only [this]; exact .ok (.goto e)
    · have : (Sem.succ fb 0) = .ok (.goto e) := by unfold succ; rw [show (0 : Nat) = if true = true then 0 else 1 from rfl, he]; rfl
      simp only [this]; exact .ok (.goto e)

/-- **Terminators.** -/
theorem sc_steps : StepRefsP (sccpInv hwf K) g := by
  intro b hb fb gb hfb hgb
  have hbf : b ∈ f.blocks := blocks_eq K.atoms ▸ hb
  obtain ⟨gb', hgb', hid, -, hk⟩ := blocksOK_facts K.blocks hbf hfb
  rw [hgb] at hgb'; cases hgb'
  rcases hk with ⟨hk, hs, hctl⟩ | hF
  · refine ⟨fun e he => hs ▸ he, stepRefP_of_controls hk.symm hs.symm hid.symm (by rw [hctl])
      fun k hk' => ?_⟩
    rw [← hctl]
    exact sc_controlRef hwf K hbf hfb (hctl ▸ hk')
  · exact ⟨(firstOK_spec hF).2.2.2.1, sc_first hwf K hF⟩

end

end GoFV.Proof.Sccp
