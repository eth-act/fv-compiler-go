import GoFV.Proof.Pass.RewriteCases
import GoFV.Proof.Pass.RewriteTerm
import GoFV.Proof.AtomSim
import GoFV.Proof.TabsAgree
import GoFV.Proof.Pass.NilSim
import GoFV.Proof.Pass.LoadFwd
import GoFV.Proof.Pass.StructStoreSim
import GoFV.Proof.Pass.CopyRelCheck
import GoFV.Proof.Pass.CopyElim
import GoFV.Proof.Pass.SegSim
import GoFV.Proof.Pass.PhiSelSim
import GoFV.Proof.Pass.PhiConst
import GoFV.Proof.Pass.PhiNotSim
import GoFV.Proof.Checked
import GoFV.Proof.MemOpsPre
import GoFV.Proof.RoImage
import GoFV.Proof.Rules.Proven
import GoFV.Opt.Opt

/-!
# The checked rewrite passes refine their input (issue #113)

`checkedRewrite_refines`: for a rule set all of whose value rules are sound (`RuleSet.AllSound`,
one `Rule.Sound` lemma per rule), the checked rewrite pass (`GoFV.Opt.checkedRewrite`: the
rewrite pass with its log, kept only if `RewriteCheck.validate` accepts it) refines its input
`f` under `RwPre penv.tables penv.frontend f` (monotone contracts, `Env.Mono`; malloc-family
contracts that return non-nil pointers and non-nil dictionary arguments, `NilPre`, for the
nil-check eliminations of issue #151; the runtime's `memclrNoHeapPointers`/`memmove` contracts,
if any, `Env.MemOps`; the read-only symbols `f`'s `Addr`s name and those the frontend defines in
the initial memory, kept by the contracts, `RoImage`; malloc-family contracts that return
all-zero heap blocks, `Env.AllocZero`; inputs without pointers into frame temporaries,
`InitAvoids`), in the pass's extended tables. A rejected result is the input
(`RefinesUnder.refl`); an accepted one relates the atoms' arguments and the controls as terms in
the extended tables (`validate_termRef`), which the atom simulation lifts to the function
(`AtomSim.atomSim_refines`), and the input runs alike in both tables (`tabsAgree`,
`refinesFrom_of_tabsAgree`). The log's nil-check eliminations, Load-of-Store forwardings and
struct-store splits (issue #151) are applied to the input first, each by its own refinement
(`Nil.refinesFrom_of_rel`, `LoadFwd.fwd_refines`, `StructStore.ss_refines`). The log is
validated in segments between its phi eliminations (issue #69, `segs_refines`): each segment
ends at the function logged at the elimination, which the function with the `Phi` turned copy
refines by copyelim's simulation (`CopyRelCheck.copyOK_spec`, `CopyElim.refines_of_rel`).

The instances depend on the proven-rule sets explicitly: `opt_refines` (also `middle opt` and
`late opt`, the same pass under another name) is about `optChecked`, the pass with the rules of
`Proven.generic` (`scripts/rule-proofs.py proven`: the generic rules with a merged lemma) and its
proof is `generic_allSound`; likewise `divisible_refines`/`divmod_refines`. Adding lemmas grows
these sets (and what the checked passes optimise); the theorems stay as stated.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof GoFV.Proof.Rules

/-- **The validator alone** (issue #17): a rewrite of `f` into `g` that `RewriteCheck.validate`
accepts in the tables `tabs'` with a sound rule table, both checked, refines in `tabs'`; with
`tabsAgree tabs tabs' f` the source may run in its own tables `tabs`. For a rewrite step whose
log has no nil-check eliminations or Load forwardings (the dec rules: decompose builtin, run with
`removeDead := false`), `RewriteCheck.accepts` is `tabsAgree` and `validate`. -/
theorem validate_refines {s : RuleSet} (hs : s.AllSound) {tabs tabs' : Tables} {f g : Func}
    {log : Array RwEvent} {ce ce' : CheckEnv}
    (hv : RewriteCheck.validate tabs' (Interp.Table.ofRuleSet s) f g log = true)
    (hta : tabsAgree tabs tabs' f = true)
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ()) :
    RefinesUnder Env.Mono tabs' g tabs f := by
  obtain ⟨hA, hcf, hcg⟩ := validate_parts hv
  obtain ⟨h1, h2⟩ := validate_termRef hv hs
  exact refinesUnder_of_tabsAgree hta (AtomSim.atomSim_refines hf hg hA hcf hcg h1 h2)

/-- The precondition of the checked rewrite passes on `f` in the tables `tabs` with the frontend
tables `fe`: monotone contracts, malloc-family contracts that return non-nil pointers, non-nil
dictionary arguments (`NilPre`: the nil-check eliminations `generic.rules:1367`/`:1372`/`:1384`,
issue #151), and `runtime.memclrNoHeapPointers`/`runtime.memmove` contracts that are the
runtime's, if present (`Env.MemOps`: for the `Zero`/`Move` of such calls,
`generic.rules:1638`/`:1730`), the read-only symbols `f`'s `Addr`s name and those `fe` defines
holding their exported bytes in the memory with the global image, kept by the contracts
(`RoImage` of `RewriteCheck.roPass`: for `Move`s from them, `generic.rules:1743`, and fixed
loads, also from a symbol a pass took from the frontend), and malloc-family contracts asked for
a positive size that return an all-zero heap block (`Env.AllocZero`: for the `Zero`s and zero
`Store`s of a fresh allocation, `generic.rules:1352`/`:1357`/`:1362`, issue #69), inputs that
hold no pointer into a frame temporary (`InitAvoids`: a frame temporary's `LocalAddr` and an
argument's pointer address disjoint bytes, `RewriteCheck.disjointB`, issue #69),
`runtime.growslice` contracts that return a slice of the requested length (`Env.GrowLen`: for
the lengths of their results, `generic.rules:2128`, issue #69), and `runtime.ifaceeq`/`efaceeq`
contracts that return the pointer equality of their data words on the descriptor symbols of
`tabs` and `fe` whose types are direct-interface and comparable (`Env.IfaceEq` of
`RewriteCheck.eqPass`: for the folds `generic.rules:2279`/`:2287`, issues #69, #189). It depends
on `f` only through its dictionary parameters (`Opt.NilCheck.dictParams`) and its read-only
symbols (`RewriteCheck.roSyms`). -/
def RwPre (tabs fe : Tables) (f : Func) (env : Env) (args : List Val) (mem : Mem) : Prop :=
  env.Mono ∧ NilPre tabs f env args mem ∧ env.MemOps ∧ env.AllocZero ∧
    RoImage (RewriteCheck.roPass tabs fe f) env mem ∧ InitAvoids env args mem ∧ env.GrowLen ∧
    env.IfaceEq (RewriteCheck.eqPass tabs fe)

/-- The byte is no fragment of a pointer into a frame temporary. -/
def byteNoTemp : Byte → Bool
  | .frag p _ => !RewriteCheck.tempBlk p.blk
  | _ => true

/-- `InitAvoids` from an empty memory, for arguments that hold no pointer into a frame temporary
and a global image without fragments of such pointers (`byteNoTemp`, decidable). -/
theorem initAvoids_empty {env : Env} {args : List Val}
    (hargs : ∀ v ∈ args, ∀ a n, v.Avoids (· = .temp a n))
    (hg : env.globals.all (fun g => g.2.data.all byteNoTemp) = true) : InitAvoids env args {} := by
  intro a n
  refine ⟨fun v hv => hargs v hv a n, fun _ _ h => ?_, rfl, fun g hg' x hx => ?_⟩
  · simp at h
  · have h1 := List.all_eq_true.1 hg g hg'
    rw [Array.all_eq_true_iff_forall_mem] at h1
    have h2 := h1 x (Array.mem_toList_iff.1 hx)
    cases x with
    | frag p k =>
      intro he
      simp only [byteNoTemp, he, RewriteCheck.tempBlk, Bool.not_true, Bool.false_eq_true] at h2
    | _ => trivial

/-- `RwPre` holds on `Env.p1` (no malloc-family, memory or interface-equality runtime contract)
for a function without dictionary parameters and read-only symbols, from inputs without
pointers into frame temporaries. -/
theorem RwPre.p1 {tabs fe : Tables} {f : Func} (h : NilCheck.dictParams tabs f = [])
    (hro : RewriteCheck.roPass tabs fe f = []) {args : List Val} {mem : Mem}
    (hinit : InitAvoids Env.p1 args mem) : RwPre tabs fe f Env.p1 args mem :=
  ⟨Env.p1_mono, ⟨Env.p1_allocNonNil, by rw [h]; exact DictArgs.nil args⟩, Env.p1_memOps,
    Env.p1_allocZero, by rw [hro]; exact RoImage.nil Env.p1_keepsRo mem, hinit, Env.p1_growLen,
    Env.p1_ifaceEq _⟩

theorem RefinesUnder.toRw {tabs₀ fe₀ tabs tabs' : Tables} {f₀ f f' : Func}
    (h : RefinesUnder Env.Mono tabs' f' tabs f) : RefinesFrom (RwPre tabs₀ fe₀ f₀) tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => hp.1) h.from

/-- **The layers refine**: each step of a `LayerChain` from a checked function refines it under
`RwPre` of the pass's input `f0` (nil-check eliminations: nilcheckelim's relation with the rewrite
passes' seeds, `Nil.refinesFrom_of_rel`; forwardings: `LoadFwd.fwd_refines`; struct-load
expansions: the validator and the atom simulation; struct-store splits:
`StructStore.ss_refines`; segment rewrites: `Seg.seg_refines`; selections of `Phi`s of
`SliceMake`s: `PhiSel.ps_refines`; constant `Phi`s: `PhiConst.pc_refines`; `Phi`s of `Not`s:
`PhiNot.pn_refines`), and its end is checked. -/
theorem chain_refines {s : RuleSet} (hs : s.AllSound) {penv : PassEnv} {tabs : Tables}
    {f0 f g : Func} (hc : LayerChain penv tabs f0 (Interp.Table.ofRuleSet s) f g) {ce : CheckEnv}
    (hf : check ce f = .ok ()) :
    ∃ ce', check ce' g = .ok () ∧ RefinesFrom (RwPre penv.tables penv.frontend f0) tabs g tabs f := by
  induction hc generalizing ce with
  | refl f => exact ⟨ce, hf, RefinesUnder.toRw (RefinesUnder.refl _ _ _)⟩
  | @nil f f' g hL _ ih =>
    simp only [RewriteCheck.nilOK, Bool.and_eq_true, beq_iff_eq] at hL
    obtain ⟨⟨hr, hck⟩, hd⟩ := hL
    obtain ⟨ce', hg, R'⟩ := ih (checkOK_sound hck)
    refine ⟨ce', hg, RefinesFrom.trans (RefinesFrom.mono (fun env args mem hp => ?_)
      (Nil.refinesFrom_of_rel ⟨ce, check_wf hf⟩ (Dom.certOK_of_check (check_domCert hf))
        (Nil.nrel_sound hr))) R'⟩
    unfold NilPre
    rw [hd]
    exact hp.2.1
  | @fwd f f' g hr hro hck _ ih =>
    have hf' := checkOK_sound hck
    obtain ⟨ce', hg, R'⟩ := ih hf'
    exact ⟨ce', hg, (RefinesFrom.mono (fun _ _ _ hp => ⟨hp.1, hp.2.2.2.1, hp.2.2.2.2⟩)
      (LoadFwd.fwd_refines hf hf' hr hro)).trans R'⟩
  | @rw f f' g evs hv hck _ ih =>
    have hf' := checkOK_sound hck
    obtain ⟨hA, hcf, hcg⟩ := validate_parts hv
    obtain ⟨h1, h2⟩ := validate_termRef hv hs
    obtain ⟨ce', hg, R'⟩ := ih hf'
    exact ⟨ce', hg,
      (RefinesUnder.toRw (AtomSim.atomSim_refines hf hf' hA hcf hcg h1 h2)).trans R'⟩
  | @ss f f' g hr hck _ ih =>
    have hf' := checkOK_sound hck
    obtain ⟨ce', hg, R'⟩ := ih hf'
    exact ⟨ce', hg, (RefinesUnder.toRw (StructStore.ss_refines hf hf' hr)).trans R'⟩
  | @seg f f' g hr hro hck _ ih =>
    have hf' := checkOK_sound hck
    obtain ⟨ce', hg, R'⟩ := ih hf'
    exact ⟨ce', hg, (RefinesFrom.mono (fun _ _ _ hp => ⟨hp.1, hp.2.2.1, hp.2.2.2.2.1⟩)
      (Seg.seg_refines hf hf' hr hro)).trans R'⟩
  | @ps f f' g hr hck _ ih =>
    have hf' := checkOK_sound hck
    obtain ⟨ce', hg, R'⟩ := ih hf'
    exact ⟨ce', hg, (RefinesUnder.toRw (PhiSel.ps_refines hf hf' hr)).trans R'⟩
  | @pc f f' g hr hck _ ih =>
    have hf' := checkOK_sound hck
    obtain ⟨ce', hg, R'⟩ := ih hf'
    exact ⟨ce', hg, (RefinesUnder.toRw (PhiConst.pc_refines hf hf' hr)).trans R'⟩
  | @pn f f' g hr hck _ ih =>
    have hf' := checkOK_sound hck
    obtain ⟨ce', hg, R'⟩ := ih hf'
    exact ⟨ce', hg, (RefinesUnder.toRw (PhiNot.pn_refines hf hf' hr)).trans R'⟩

/-- **Layers without nil-check eliminations and forwardings refine** under monotone contracts
alone (issue #17, the decompose builtin rewrite step, `RewriteCheck.decLayers`): each layer
`layersOK` takes is related by its own refinement (struct-load and value-rule `Load` expansions
the validator and the atom simulation; splits `StructStore.ss_refines`), and the output to the
last layer's function by `validate`. -/
theorem layersOK_refines {s : RuleSet} (hs : s.AllSound) {penv : PassEnv} {f0 : Func}
    {out : PassOut} {ce' : CheckEnv} (hg : check ce' out.func = .ok ()) :
    ∀ (Ls : List RewriteCheck.Layer),
      (∀ sel, RewriteCheck.Layer.nil sel ∉ Ls ∧ RewriteCheck.Layer.fwd sel ∉ Ls) →
      (∀ sel, RewriteCheck.Layer.seg sel ∉ Ls) →
      ∀ (f : Func) (log : Array RwEvent) {ce : CheckEnv}, check ce f = .ok () →
      RewriteCheck.layersOK penv (Interp.Table.ofRuleSet s) f0 out Ls f log = true →
      RefinesUnder Env.Mono out.tables out.func out.tables f
  | [], _, _, f, log, ce, hf, h => by
    rw [RewriteCheck.layersOK] at h
    obtain ⟨hA, hcf, hcg⟩ := validate_parts h
    obtain ⟨h1, h2⟩ := validate_termRef h hs
    exact AtomSim.atomSim_refines hf hg hA hcf hcg h1 h2
  | L :: Ls, hn, hns, f, log, ce, hf, h => by
    have hn' : ∀ sel, RewriteCheck.Layer.nil sel ∉ Ls ∧ RewriteCheck.Layer.fwd sel ∉ Ls :=
      fun sel => ⟨fun hm => (hn sel).1 (List.mem_cons_of_mem _ hm),
        fun hm => (hn sel).2 (List.mem_cons_of_mem _ hm)⟩
    have hns' : ∀ sel, RewriteCheck.Layer.seg sel ∉ Ls :=
      fun sel hm => hns sel (List.mem_cons_of_mem _ hm)
    rw [RewriteCheck.layersOK] at h
    split at h
    next f' log' _ =>
    split at h
    · exact layersOK_refines hs hg Ls hn' hns' f log hf h
    · rw [Bool.and_eq_true] at h
      obtain ⟨hL, hr⟩ := h
      cases L with
      | nil sel => exact absurd List.mem_cons_self (hn sel).1
      | fwd sel => exact absurd List.mem_cons_self (hn sel).2
      | sl =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        have hf' := checkOK_sound hL.2
        obtain ⟨hA, hcf, hcg⟩ := validate_parts hL.1
        obtain ⟨h1, h2⟩ := validate_termRef hL.1 hs
        exact (AtomSim.atomSim_refines hf hf' hA hcf hcg h1 h2).trans
          (layersOK_refines hs hg Ls hn' hns' f' log' hf' hr)
      | ld =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        have hf' := checkOK_sound hL.2
        obtain ⟨hA, hcf, hcg⟩ := validate_parts hL.1
        obtain ⟨h1, h2⟩ := validate_termRef hL.1 hs
        exact (AtomSim.atomSim_refines hf hf' hA hcf hcg h1 h2).trans
          (layersOK_refines hs hg Ls hn' hns' f' log' hf' hr)
      | ss =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        have hf' := checkOK_sound hL.2
        exact (StructStore.ss_refines hf hf' hL.1).trans
          (layersOK_refines hs hg Ls hn' hns' f' log' hf' hr)
      | seg sel => exact absurd List.mem_cons_self (hns sel)
      | ps =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        have hf' := checkOK_sound hL.2
        exact (PhiSel.ps_refines hf hf' hL.1).trans
          (layersOK_refines hs hg Ls hn' hns' f' log' hf' hr)
      | pc =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        have hf' := checkOK_sound hL.2
        exact (PhiConst.pc_refines hf hf' hL.1).trans
          (layersOK_refines hs hg Ls hn' hns' f' log' hf' hr)
      | pn =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        have hf' := checkOK_sound hL.2
        exact (PhiNot.pn_refines hf hf' hL.1).trans
          (layersOK_refines hs hg Ls hn' hns' f' log' hf' hr)

/-- **One segment of the log**: what `layersOK` accepts (with a table of the rule set's value and
block rules) from a checked function to a checked one refines it. -/
theorem layers_refines {s : RuleSet} (hs : s.AllSound) {T : Interp.Table}
    (hvs : T.values = (Interp.Table.ofRuleSet s).values)
    (hbs : T.blocks = (Interp.Table.ofRuleSet s).blocks) {penv : PassEnv} {f0 f : Func}
    {out : PassOut} {log : Array RwEvent} {ce ce' : CheckEnv}
    (h : RewriteCheck.layersOK penv T f0 out RewriteCheck.layers f log = true)
    (hf : check ce f = .ok ()) (hg : check ce' out.func = .ok ()) :
    RefinesFrom (RwPre penv.tables penv.frontend f0) out.tables out.func out.tables f := by
  obtain ⟨g, log', hc, hv⟩ := layersOK_cases _ _ _ h
  rw [validate_congr hvs hbs] at hv
  obtain ⟨hA, hcf, hcg⟩ := validate_parts hv
  obtain ⟨h1, h2⟩ := validate_termRef hv hs
  -- the layers (nil-check eliminations, forwardings, struct-load expansions, struct-store splits)
  obtain ⟨ce₃, hf₃, hL⟩ := chain_refines hs (hc.congr hvs hbs) hf
  -- then the validated rewrite
  exact hL.trans (RefinesUnder.toRw (AtomSim.atomSim_refines hf₃ hg hA hcf hcg h1 h2))

/-- **The segments of the log** between its phi eliminations and snapshots (issue #69): each
segment refines (`layers_refines`), at each phi elimination the function with the `Phi` turned
copy refines the logged function by copyelim's simulation, and at a snapshot the next segment
starts from the logged function. -/
theorem segs_refines {s : RuleSet} (hs : s.AllSound) {T : Interp.Table}
    (hvs : T.values = (Interp.Table.ofRuleSet s).values)
    (hbs : T.blocks = (Interp.Table.ofRuleSet s).blocks) {penv : PassEnv} {f0 : Func}
    {out : PassOut} {ce' : CheckEnv} (hg : check ce' out.func = .ok ()) :
    ∀ (evs : List RwEvent) (f : Func) (seg : Array RwEvent) {ce : CheckEnv},
      check ce f = .ok () → RewriteCheck.segsOK penv T f0 out f seg evs = true →
      RefinesFrom (RwPre penv.tables penv.frontend f0) out.tables out.func out.tables f
  | [], _, _, _, hf, h => layers_refines hs hvs hbs h hf hg
  | ev :: evs, f, seg, _, hf, h => by
    cases ev with
    | phielim v d pre =>
      simp only [RewriteCheck.segsOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      have hh := checkOK_sound h2
      have hh' := checkOK_sound h4
      obtain ⟨hrel, hfr⟩ := CopyRelCheck.copyOK_spec h3
      have R2 := CopyElim.refines_of_rel (tabs := out.tables)
        ⟨⟨_, check_wf hh⟩, ⟨_, check_wf hh'⟩, Dom.certOK_of_check (check_domCert hh),
          Dom.certOK_of_check (check_domCert hh'), hrel, hfr⟩
      exact ((layers_refines (out := { out with func := RewriteCheck.dropInvalid pre }) hs hvs hbs
        h1 hf hh).trans (RefinesUnder.toRw (R2.under Env.Mono))).trans
        (segs_refines hs hvs hbs hg evs _ #[] hh' h5)
    | snap pre =>
      simp only [RewriteCheck.segsOK, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hh := checkOK_sound h2
      exact (layers_refines (out := { out with func := RewriteCheck.dropInvalid pre }) hs hvs hbs
        h1 hf hh).trans (segs_refines hs hvs hbs hg evs _ #[] hh h3)
    | _ =>
      simp only [RewriteCheck.segsOK] at h
      exact segs_refines hs hvs hbs hg evs f _ hf h

theorem checkedRewrite_refines {s : RuleSet} (hs : s.AllSound)
    {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : checkedRewrite (Interp.Table.ofRuleSet s) penv f = .ok out)
    (hf : check ce f = .ok ()) (hg : check ce' out.func = .ok ()) :
    RefinesFrom (RwPre penv.tables penv.frontend f) out.tables out.func penv.tables f := by
  rcases checkedRewrite_cases h with ⟨he, ht⟩ | ⟨hta, T, hvs, hbs, log, hseg⟩
  · rw [he, ht]; exact RefinesUnder.toRw (RefinesUnder.refl _ _ _)
  exact refinesFrom_of_tabsAgree hta (segs_refines hs hvs hbs hg _ f #[] hf hseg)

/-- `opt`, `middle opt` and `late opt` with the proven generic rules, validated. -/
theorem opt_refines {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : optChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesFrom (RwPre penv.tables penv.frontend f) out.tables out.func penv.tables f :=
  checkedRewrite_refines generic_allSound h hf hg

/-- `divisible` with its proven rules, validated. -/
theorem divisible_refines {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : divisibleChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesFrom (RwPre penv.tables penv.frontend f) out.tables out.func penv.tables f :=
  checkedRewrite_refines divisible_allSound h hf hg

/-- `divmod` with its proven rules, validated. -/
theorem divmod_refines {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : divmodChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesFrom (RwPre penv.tables penv.frontend f) out.tables out.func penv.tables f :=
  checkedRewrite_refines divmod_allSound h hf hg

end GoFV.Proof.Pass.Rewrite
