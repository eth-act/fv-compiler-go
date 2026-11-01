import GoFV.Proof.ProveCheck.Inv
import GoFV.Proof.ProveCheck.Fold
import GoFV.Proof.Pass.RewriteTerm
import GoFV.Proof.TermStep

/-!
# prove's validator: the premises of the atom simulation (issue #24)

Under prove's source invariant (`proveInv`), the output `g` of an accepted `proveRel` satisfies
the premises of `AtomSim.atomSimInv_refines`:

* `den_ref`: every value listed in `f` in an ancestor of `b0` is refined, as a term, by the same
  value listed in `g`, for valuations under which `b0`'s assumptions hold (`AsmHolds`). A kept
  definition is monotone; a value rewrite (`valueOK`) refines by `valueOK_ref` and a
  constant-folded argument by `fold_ref`, under the assumptions of the value's own block, a
  subset of `b0`'s (`facts_of_anc`).
* `asm_of_premises`: the premises of `TermRefP`/`StepRefP` under `PInv` at `b` give `b`'s
  assumptions (facts are terms of strict ancestors, `Phi` invariants hold of the atoms).
* `prove_atomArgs` (`AtomArgsRefP`): atoms keep their op and fields; each argument is kept,
  listed in an ancestor of the atom's block (`uses`) or, for a `Phi`, of the predecessor
  (`phiUse`), or folded to a constant under that block's assumptions (`fold_termRefP`).
* `prove_steps` (`StepRefsP`): a kept terminator by `stepRefP_of_controls`; a removed branch
  (`branchOK`) goes along the successor its control is decided to take (`decides_sound`).
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck
  GoFV.Proof GoFV.Proof.Dom GoFV.Proof.Term GoFV.Proof.AtomSim GoFV.Proof.Pass.Rewrite

/-- An accepted value rewrite is of a term into a term of the same type, with the same arguments
or none. -/
theorem valueOK_shape {D : ID → Option Value} {tabs : Tables} {A : Asm} {fv gv : Value}
    (hv : valueOK D tabs A fv gv = true) :
    termOp fv.op = true ∧ termOp gv.op = true ∧ fv.type = gv.type ∧
      (gv.args = fv.args ∨ gv.args = #[]) := by
  unfold valueOK at hv
  simp only [Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨⟨hty, -⟩, hv⟩ := hv
  split at hv
  · rename_i hf hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    exact ⟨shTab_term hf, shTab_term hg, hty, .inl hv.1.1.1.1.symm⟩
  · split at hv
    · rename_i hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      exact ⟨(opTab_term hk).1, (opTab_term hk).2, hty, .inl hv.1.2.symm⟩
    · rename_i hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      exact ⟨(opTab_term hk).1, (opTab_term hk).2, hty, .inl hv.1.2.symm⟩
    · rename_i hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      exact ⟨(opTab_term hk).1, (opTab_term hk).2, hty, .inl hv.1.2.symm⟩
    · simp only [Bool.and_eq_true, beq_iff_eq] at hv
      obtain ⟨⟨⟨hop, hargs⟩, -⟩, hw⟩ := hv
      split at hw
      · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hw
        refine ⟨by rw [hop]; rfl, ?_, hty, .inr (Array.isEmpty_iff.1 hargs)⟩
        rcases hw.1 with ⟨hg, -⟩ | ⟨hg, -⟩ <;> rw [hg] <;> rfl
      · cases hw

private theorem not_isTerm {D : ID → Option Value} {x : ID} {v : Value} (hv : D x = some v)
    (ht : ¬ termOp v.op = true) : ¬ IsTerm D x := fun ⟨w, hw, hw'⟩ => by
  rw [hv] at hw; cases hw; exact ht hw'

section
variable {tabs : Tables} {f g : Func} {ce : CheckEnv} {F : Array (List (ID × Bool))}
  {inv : List (ID × Width × Rng)} {RB : Array (List (ID × ID × Width × Int))}

/-- The relations of a block include those of its ancestors. -/
theorem rels_of_anc (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) {a b : ID}
    (h : Anc (make f) a b) (hb : b ∈ f.blocks) : ∀ r ∈ relsAt RB a, r ∈ relsAt RB b :=
  table_of_anc (T := relsAt RB) (fun p hp ht hne => ⟨(hR.hF.up p hp ht hne).1,
    hR.hrels.up p hp ht hne⟩) hc.parents h hb

/-- **Values as terms**: under `b0`'s assumptions, each value listed in `f` in an ancestor of
`b0` is refined by the same value listed in `g`. -/
theorem den_ref (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) {b0 : ID} (hb0 : b0 ∈ f.blocks)
    {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ')
    (hA : AsmHolds f.value? tabs ρ (asmAt F inv RB b0)) :
    ∀ n x, LM f x → Anc (make f) (blockOf f x) b0 →
      Sem.Refines (den f.value? tabs ρ n x) (den (listedDefs g) tabs ρ' n x)
  | 0, _, _, _ => .poison _
  | n + 1, x, hx, hanc => by
    obtain ⟨b, hb, fb, hfb, hxv, fv, hfv, rfl⟩ := listedMarks_sound f x hx
    have hpl : Placed f x fv := ⟨hfv, hb, fb, hfb, hxv⟩
    rw [blockOf_placed hpl] at hanc
    obtain ⟨gb, hgb, -, hvals⟩ := hR.blocks _ hb fb hfb
    obtain ⟨hxg, fv', gv, hfv', hgv, hblk, hdef⟩ := hvals x hxv
    rw [hfv] at hfv'; cases hfv'
    have hL : listedDefs g x = some gv := by
      rw [listedDefs_of_marked ⟨fv.block, (atomsOK_spec hR.atoms).blocks ▸ hb, gb, hgb, hxg, gv,
        hgv, hblk⟩, hgv]
    have hargs : termOp fv.op = true → ∀ a ∈ fv.args.toList,
        Sem.Refines (den f.value? tabs ρ n a) (den (listedDefs g) tabs ρ' n a) := by
      intro ht a ha
      have ha' := Array.mem_toList_iff.1 ha
      refine den_ref hc hR hb0 hρ hA n a ((closedOK_facts hR.closedF _ hb fb hfb).2 x hxv fv hfv a ha') ?_
      have hnp : fv.op ≠ .Phi := fun e => by rw [e, termOp_phi] at ht; cases ht
      exact (uses hc hb hfb (by simpa [Cert.inTree] using hR.tree _ hb) hxv hfv hnp ha').trans
        hc.parents hanc
    have hAx : AsmHolds f.value? tabs ρ (asmAt F inv RB fv.block) :=
      ⟨fun c v hcv => hA.facts c v (facts_of_anc hR.hF hc.parents hanc hb0 _ hcv), hA.inv,
        fun z y w c hr => hA.rels z y w c (rels_of_anc hc hR hanc hb0 _ hr), hA.typed⟩
    by_cases ht : termOp fv.op = true
    · have hnp : fv.op ≠ .Phi := fun e => by rw [e, termOp_phi] at ht; cases ht
      -- arguments kept or folded to constants
      have hfold : argsOK f.value? tabs F inv RB (asmAt F inv RB fv.block) g fb fv gv = true →
          RefinesList (fv.args.toList.map (den f.value? tabs ρ n))
            (gv.args.toList.map (den (listedDefs g) tabs ρ' n)) := fun hao => by
        obtain ⟨hsz, hi⟩ := argsOK_spec hao
        refine refinesList_zip (by simp [hsz]) fun i h1 h2 => ?_
        simp only [Array.length_toList] at h1 h2
        simp only [Array.getElem_toList]
        have hi' := hi i h1
        rw [getElem!_pos fv.args i h1, getElem!_pos gv.args i h2, argAsm_of_not_phi hnp] at hi'
        rcases hi' with e | hf
        · rw [← e]; exact hargs ht _ (Array.mem_toList_iff.2 (Array.getElem_mem h1))
        · exact fold_ref hAx hf n
      obtain ⟨htg, hty, L, h1, h2⟩ : termOp gv.op = true ∧ fv.type = gv.type ∧ ∃ L,
          Sem.Refines
            (GoFV.Proof.Rules.opVal tabs fv.op (tabs.ty fv.type) fv.auxInt fv.aux
              (fv.args.toList.map (den f.value? tabs ρ n)))
            (GoFV.Proof.Rules.opVal tabs gv.op (tabs.ty fv.type) gv.auxInt gv.aux L) ∧
          RefinesList L (gv.args.toList.map (den (listedDefs g) tabs ρ' n)) := by
        rcases defOK_cases hdef with hs | hok | ⟨hao, hs | hok⟩
        · unfold sameDef at hs
          simp only [Bool.and_eq_true, beq_iff_eq] at hs
          obtain ⟨⟨⟨⟨hop, hty⟩, hai⟩, hax⟩, has⟩ := hs
          refine ⟨hop ▸ ht, hty, _, by rw [hop, hai, hax]; exact .refl _, ?_⟩
          rw [← has]; exact refinesList_map (hargs ht)
        · obtain ⟨-, htg, hty, hga⟩ := valueOK_shape hok
          refine ⟨htg, hty, _, valueOK_refT hAx hok n, ?_⟩
          rcases hga with e | e
          · rw [e]; exact refinesList_map (hargs ht)
          · rw [e]; exact .nil
        · unfold sameDef at hs
          simp only [Bool.and_eq_true, beq_iff_eq] at hs
          obtain ⟨⟨⟨⟨hop, hty⟩, hai⟩, hax⟩, -⟩ := hs
          exact ⟨hop ▸ ht, hty, _, by rw [hop, hai, hax]; exact .refl _, hfold hao⟩
        · obtain ⟨-, htg, hty, -⟩ := valueOK_shape hok
          exact ⟨htg, hty, _, valueOK_refT hAx hok n, hfold hao⟩
      rw [den_succ_term hfv ht, den_succ_term hL htg, ← hty]
      exact retype_mono _ (h1.trans (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ h2))
    · have htg : ¬ termOp gv.op = true := by
        rcases defOK_cases hdef with hs | hok | ⟨-, hs | hok⟩
        · unfold sameDef at hs
          simp only [Bool.and_eq_true, beq_iff_eq] at hs
          exact hs.1.1.1.1 ▸ ht
        · exact absurd (valueOK_shape hok).1 ht
        · unfold sameDef at hs
          simp only [Bool.and_eq_true, beq_iff_eq] at hs
          exact hs.1.1.1.1 ▸ ht
        · exact absurd (valueOK_shape hok).1 ht
      rw [den_succ_atom (not_isTerm hfv ht), den_succ_atom (not_isTerm hL htg)]
      exact hρ x

/-- The premises of `TermRefP`/`StepRefP` under `PInv` and `QRel` at `b` give `b`'s
assumptions, if the facts of `b` are in `S`. -/
theorem asm_of_premises (hR : RelSpec tabs f g F inv RB) {b : ID} (hb : b ∈ f.blocks)
    {S : ID → Prop} (hS : ∀ c v, (c, v) ∈ factsAt F b → S c) {ρ : ID → Val}
    (hT : Term.Typed f.value? tabs ρ)
    (hP : ∀ a, ¬ IsTerm f.value? a → PInv tabs f F inv b a (ρ a))
    (hSP : ∀ a, S a → ∃ N, ∀ k, N ≤ k → PInv tabs f F inv b a (den f.value? tabs ρ k a))
    (hQ : QRel tabs f RB b ρ) :
    AsmHolds f.value? tabs ρ (asmAt F inv RB b) := by
  refine ⟨fun c v hcv => ?_, fun z w r hz n y hd => ?_, hQ hb, hT⟩
  · obtain ⟨N, hN⟩ := hSP c (hS c v hcv)
    exact ⟨N, fun k hk => (hN k hk).2.1 hb v hcv⟩
  · obtain ⟨zv, hzv, hph⟩ := inv_phi hR hz
    have hat : ¬ IsTerm f.value? z := fun ⟨u, hu, ht⟩ => by
      rw [hzv] at hu; cases hu; rw [hph, termOp_phi] at ht; cases ht
    cases n with
    | zero => simp [den] at hd
    | succ n =>
      rw [den_succ_atom hat] at hd
      exact (hP z hat).2.2 w r hz y hd

/-- A value listed in `f` in an ancestor of `b` refines as a term under `PInv` and `QRel` at
`b`. -/
theorem prove_termRefP (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) {b : ID}
    (hb : b ∈ f.blocks) {S : ID → Prop}
    (hS : ∀ c v, (c, v) ∈ factsAt F b → S c) {x : ID}
    (hx : LM f x) (hanc : Anc (make f) (blockOf f x) b) :
    TermRefP (PInv tabs f F inv b) (QRel tabs f RB b) S f.value? tabs x (listedDefs g) tabs x :=
  fun n => ⟨n, fun _ _ hρ hT _ hP hSP hQ =>
    den_ref hc hR hb hρ (asm_of_premises hR hb hS hT hP hSP hQ) n x hx hanc⟩

/-- A constant fold justified under `b`'s assumptions refines as a term under `PInv` and `QRel`
at `b`. -/
theorem fold_termRefP (hR : RelSpec tabs f g F inv RB) {b : ID} (hb : b ∈ f.blocks)
    {S : ID → Prop} (hS : ∀ c v, (c, v) ∈ factsAt F b → S c) {a c : ID}
    (h : foldOK f.value? tabs (asmAt F inv RB b) g a c = true) :
    TermRefP (PInv tabs f F inv b) (QRel tabs f RB b) S f.value? tabs a (listedDefs g) tabs c :=
  fun n => ⟨n, fun _ _ _ hT _ hP hSP hQ =>
    fold_ref (asm_of_premises hR hb hS hT hP hSP hQ) h n⟩

theorem facts_sanc (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) {b : ID} {bb : Block}
    (hb : b ∈ f.blocks) (hbb : f.block? b = some bb) :
    ∀ c v, (c, v) ∈ factsAt F b → SAnc f b c := fun _ _ hcv =>
  let ⟨cv, hpl, hne, hanc, _⟩ := fact_placed hc hR hb hbb hcv
  ⟨cv, hpl, hanc, hne⟩

theorem facts_ancV (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) {b : ID} {bb : Block}
    (hb : b ∈ f.blocks) (hbb : f.block? b = some bb) :
    ∀ c v, (c, v) ∈ factsAt F b → AncV f b c := fun _ _ hcv =>
  let ⟨cv, hpl, _, hanc, _⟩ := fact_placed hc hR hb hbb hcv
  ⟨cv, hpl, hanc⟩

/-- **Atoms' arguments.** -/
theorem prove_atomArgs (hwf : WF ce f) (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) :
    AtomArgsRefP (proveInv hwf hc hR) g := by
  intro b hb gb hgb a ha u hu ht
  have hbf : b ∈ f.blocks := (atomsOK_spec hR.atoms).blocks ▸ hb
  obtain ⟨fb, gb', hfb, hgb', BA⟩ := (atomsOK_spec hR.atoms).block b hbf
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨haf, u', hu', hop, hty, hai, hax, hsz, -, -⟩ := BA.sub a ha u hu ht
  obtain ⟨gb2, -, -, hvals⟩ := hR.blocks b hbf fb hfb
  obtain ⟨-, fv, gv, hfv, hgv, -, hdef⟩ := hvals a haf
  rw [hu'] at hfv; cases hfv
  rw [hu] at hgv; cases hgv
  have htree : ((make f).depthOf b).isSome := by simpa [Cert.inTree] using hR.tree _ hbf
  -- every argument kept or folded to a constant (a value rewrite is of a term)
  have hper : ∀ i < u'.args.size, u'.args[i]! = u.args[i]! ∨
      foldOK f.value? tabs (argAsm F inv RB (asmAt F inv RB b) fb u' i) g u'.args[i]!
        u.args[i]! = true := by
    rcases defOK_cases hdef with hs | hok | ⟨hao, hs | hok⟩
    · unfold sameDef at hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      exact fun i _ => .inl (by rw [hs.2])
    · have := (valueOK_shape hok).2.1
      rw [ht] at this; cases this
    · exact (argsOK_spec hao).2
    · have := (valueOK_shape hok).2.1
      simp only at this
      rw [ht] at this; cases this
  refine ⟨u', hu', hop, hty, hai, hax, hsz, fun i hi => ?_⟩
  have hi' : i < u'.args.size := hsz ▸ hi
  have hmem : u'.args[i]! ∈ u'.args := by
    rw [getElem!_pos u'.args i hi']; exact Array.getElem_mem hi'
  have hLM := (closedOK_facts hR.closedF b hbf fb hfb).2 a haf u' hu' _ hmem
  refine ⟨fun hnp => ?_, fun hph p pb k hp hpb hk => ?_⟩
  · rcases hper i hi' with e | hf
    · rw [← e]
      exact prove_termRefP hc hR hbf (facts_sanc hc hR hbf hfb) hLM
        (uses hc hbf hfb htree haf hu' (hop ▸ hnp) hmem)
    · rw [argAsm_of_not_phi (hop ▸ hnp)] at hf
      exact fold_termRefP hR hbf (facts_sanc hc hR hbf hfb) hf
  · obtain ⟨-, cb, hcb, hpred⟩ := hwf.succLink p pb ⟨hp, hpb⟩ k _ hk
    rw [hfb] at hcb; cases hcb
    rcases hper i hi' with e | hf
    · rw [← e]
      have hpt : ((make f).depthOf p).isSome := by simpa [Cert.inTree] using hR.tree _ hp
      have hget : u'.args[i]? = some u'.args[i]! := by
        rw [getElem!_pos u'.args i hi']; exact Array.getElem?_eq_getElem hi'
      exact prove_termRefP hc hR hp (facts_ancV hc hR hp hpb) hLM
        (phiUse hc hbf hfb htree haf hu' (hop ▸ hph) hget hpred hpt)
    · rw [argAsm_of_phi (hop ▸ hph) hpred] at hf
      exact fold_termRefP hR hp (facts_ancV hc hR hp hpb) hf

/-- A removed branch: the `If`'s control, when not `poison`, takes the kept successor. -/
theorem branch_step (hR : RelSpec tabs f g F inv RB) {b : ID} (hb : b ∈ f.blocks)
    {S : ID → Prop} (hS : ∀ c v, (c, v) ∈ factsAt F b → S c) {fb gb : Block}
    (hbr : branchOK f.value? tabs (asmAt F inv RB b) fb gb = true) :
    (∀ e ∈ fb.succs, e ∈ gb.succs) ∧
      StepRefP (PInv tabs f F inv b) (QRel tabs f RB b) S f.value? tabs fb (listedDefs g) gb := by
  unfold branchOK at hbr
  simp only [Bool.and_eq_true, beq_iff_eq] at hbr
  obtain ⟨⟨⟨hkf, hkg⟩, hgc⟩, hm⟩ := hbr
  split at hm
  · rename_i c e0 e1 hcl hsl
    have hfc : fb.controls = #[c] := by apply Array.ext'; rw [hcl]
    have hfs : fb.succs = #[e0, e1] := by apply Array.ext'; rw [hsl]
    have hgc' : gb.controls = #[] := Array.isEmpty_iff.1 hgc
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
    refine ⟨?_, fun n => ⟨0, fun ρ ρ' _ hT _ hP hSP hQ => ?_⟩⟩
    · intro e he
      rw [hfs] at he
      rcases hm with ⟨hgs, -⟩ | ⟨hgs, -⟩ <;> rw [hgs] <;> simp only [List.mem_toArray,
        List.mem_cons, List.not_mem_nil, or_false] at he ⊢
      · exact he
      · exact he.symm
    · have hA := asm_of_premises hR hb hS hT hP hSP hQ
      rw [hfc, hgc']
      have hdec := fun v (h : decides f.value? tabs (asmAt F inv RB b) rngFuel rngFuel c v
        = true) => decides_sound hA rngFuel c v h n
      simp only [stepVals, hkf, hkg, List.map_cons, List.map_nil, ctlV, List.getElem?_cons_zero]
      cases hd : den f.value? tabs ρ n c with
      | bool bb =>
        rcases hm with ⟨hgs, hd1⟩ | ⟨hgs, hd0⟩
        · cases hdec true hd1 bb hd
          simp [bind, Sem.succ, hfs, hgs, Res.ofOption]
          exact .ok (.goto _)
        · cases hdec false hd0 bb hd
          simp [bind, Sem.succ, hfs, hgs, Res.ofOption]
          exact .ok (.goto _)
      | _ => exact .stuck _ _
  · cases hm

/-- **Terminators.** -/
theorem prove_steps (hwf : WF ce f) (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) :
    StepRefsP (proveInv hwf hc hR) g := by
  intro b hb fb gb hfb hgb
  have hbf : b ∈ f.blocks := (atomsOK_spec hR.atoms).blocks ▸ hb
  obtain ⟨gb', hgb', hterm, -⟩ := hR.blocks b hbf fb hfb
  rw [hgb] at hgb'; cases hgb'
  rcases hterm with ⟨hk, hctl, hs⟩ | hbr
  · obtain ⟨fb', gb', hfb', hgb', BA⟩ := (atomsOK_spec hR.atoms).block b hbf
    rw [hfb] at hfb'; cases hfb'
    rw [hgb] at hgb'; cases hgb'
    have htree : ((make f).depthOf b).isSome := by simpa [Cert.inTree] using hR.tree _ hbf
    refine ⟨fun e he => hs ▸ he, stepRefP_of_controls hk.symm hs.symm BA.id.symm (by rw [hctl])
      fun k hk' => ?_⟩
    rw [← hctl]
    have hk2 : k < fb.controls.size := hctl ▸ hk'
    have hcm : fb.controls[k]! ∈ fb.controls := by
      rw [getElem!_pos fb.controls k hk2]; exact Array.getElem_mem hk2
    exact prove_termRefP hc hR hbf (facts_sanc hc hR hbf hfb)
      ((closedOK_facts hR.closedF b hbf fb hfb).1 _ hcm) (ctrlUse hc hbf hfb htree hcm)
  · exact branch_step hR hbf (facts_sanc hc hR hbf hfb) hbr

end

end GoFV.Proof.ProveCheck
