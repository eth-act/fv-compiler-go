import GoFV.Proof.AtomSimLoop

/-!
# Block entries of the atom simulation (issue #113)

`BRel frS frT b i`: the source and target frames at the entry of block `b` along edge `i`
(the same block and edge in both runs): the same activation inputs, typed registers, `b` a tree
block of both dominator trees, every atom of `g` the target holds refined from the source's
register, and sets `VS`/`VT` with `DenOK` that contain the values of the strict ancestors of `b`
and the `Phi` arguments along edge `i`.

Here: the static facts of one block (`BlockData`), the `Phi`s (`tgt_phis`: the target collects
its `Phi`s, each refining the source's), `DenOK` after the `Phi`s (`denOK_phisS/T`) and after
the source's schedule prefix (`src_eval`).
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.Dom GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-- The frame relation at a block entry. -/
structure BRel (tabs : Tables) (f g : Func) (I : SrcInv tabs f) (frS frT : Frame) (b : ID) (i : Nat) :
    Prop where
  fr : frT = { frS with regs := frT.regs }
  szS : frS.regs.size = f.valueTab.size
  szT : frT.regs.size = g.valueTab.size
  tyS : Proof.Typed (Ctx.make tabs f) frS
  tyT : Proof.Typed (Ctx.make tabs g) frT
  mem : b ∈ f.blocks
  treeS : ((make f).depthOf b).isSome
  treeT : ((make g).depthOf b).isSome
  atoms : ∀ a w, Placed g a w → termOp w.op = false → ∀ y', frT.regs[a]? = some (some y') →
    ∃ y, frS.regs[a]? = some (some y) ∧ Sem.Refines y y'
  den : ∃ VS VT, DenOK f.value? tabs frS VS ∧ DenOK (listedDefs g) tabs frT VT ∧
    (∀ x, VT x → ∃ w, Placed g x w) ∧ (∀ x, SAnc f b x → VS x) ∧ (∀ x, SAnc g b x → VT x) ∧
    PhiArgs f b i VS ∧ PhiArgs g b i VT ∧ MemDefs f.value? tabs frS VS
  live : I.L b i
  inv : ∀ a, I.P b a (rv frS a)
  phis : PhisP tabs f I.P frS b i
  qinv : PhisQ tabs f I.Q frS b i
  /-- The `Phi` arguments along edge `i` are read in the frame at the end of the predecessor
  `p` (none at the entry): `p`'s invariants hold of it and its values in ancestors of `p` are
  their terms. -/
  pre : PhiArgs f b i (fun _ => False) ∨ ∃ (p : ID) (pb : Block) (k : Nat) (VP : ID → Prop), p ∈ f.blocks ∧ f.block? p = some pb ∧
    pb.succs[k]? = some (⟨b, i⟩ : Edge) ∧ (∀ a, I.P p a (rv frS a)) ∧ I.Q p (rv frS) ∧
    DenOK f.value? tabs frS VP ∧ (∀ x, AncV f p x → VP x) ∧ PhiArgs f b i VP ∧
    MemDefs f.value? tabs frS VP

/-- The static facts of block `b`. -/
structure BlockData (f g : Func) (b : ID) (fb gb : Block) (of og : Array ID) : Prop where
  hfb : f.block? b = some fb
  hgb : g.block? b = some gb
  ba : BlockAtoms f g fb gb
  bmS : b ∈ f.blocks
  bmT : b ∈ g.blocks
  idS : fb.id = b
  idT : gb.id = b
  vS : fb.values.toList.Nodup
  vT : gb.values.toList.Nodup
  sS : schedule f fb = some of
  sT : schedule g gb = some og
  fl : of.toList.filter (rootP f) = og.toList.filter (rootP g)
  ndS : of.toList.Nodup
  tpS : TopoRem (argsF f) of.toList
  mS : ∀ x, x ∈ of.toList ↔ x ∈ fb.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi
  ndT : og.toList.Nodup
  tpT : TopoRem (argsF g) og.toList
  mT : ∀ x, x ∈ og.toList ↔ x ∈ gb.values ∧ ∃ v, g.value? x = some v ∧ v.op ≠ .Phi

theorem blockData {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {b : ID} {fb : Block} (hb : b ∈ f.blocks) (hfb : f.block? b = some fb) :
    ∃ gb of og, BlockData f g b fb gb of og := by
  obtain ⟨fb', gb, hfb', hgb, ba⟩ := H.ok.block b hb
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨of, og, hof, hog, hfl⟩ := ba.sched
  have hbT : b ∈ g.blocks := H.ok.blocks ▸ hb
  obtain ⟨fb', hfb', hidS⟩ := H.wf.blockId b hb
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨gb', hgb', hidT⟩ := H.wg.blockId b hbT
  rw [hgb] at hgb'; cases hgb'
  have hndS := H.wf.valuesNodup b fb ⟨hb, hfb⟩
  have hndT := H.wg.valuesNodup b gb ⟨hbT, hgb⟩
  obtain ⟨n1, t1, m1⟩ := schedule_topo (valuesOwn H.wf hb hfb) hndS hof
  obtain ⟨n2, t2, m2⟩ := schedule_topo (valuesOwn H.wg hbT hgb) hndT hog
  exact ⟨gb, of, og, hfb, hgb, ba, hb, hbT, hidS, hidT, hndS, hndT, hof, hog, hfl, n1, t1, m1, n2,
    t2, m2⟩

theorem sched_eq {tabs : Tables} {h : Func} {b : ID} {hb : Block} (hbb : h.block? b = some hb)
    (hid : hb.id = b) : ((Ctx.make tabs h).sched[hb.id]?).join = schedule h hb := by
  rw [hid]; exact sched_of_block hbb

/-! ## Registers refined through `TermRef` -/

/-- `TermRefP` between registers of two frames whose atoms are refined, the source's registers
satisfying the invariant at block `b`. -/
theorem termRef_regs {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f}
    (H : Hyp tabs f g ce ce' I) {b : ID}
    {G T : Frame} {VS VT : ID → Prop}
    (hDS : DenOK f.value? tabs G VS) (hMS : MemDefs f.value? tabs G VS)
    (hDT : DenOK (listedDefs g) tabs T VT)
    (hVT : ∀ a, VT a → ∃ w, Placed g a w)
    (hrel : ∀ a, VT a → VS a → ¬ IsTerm f.value? a → ¬ IsTerm (listedDefs g) a →
      Sem.Refines (rv G a) (rv T a))
    (htyS : Proof.Typed (Ctx.make tabs f) G) (htyT : Proof.Typed (Ctx.make tabs g) T)
    {S : ID → Prop} (hinv : ∀ a, I.P b a (rv G a)) (hq : I.Q b (rv G)) (hSV : ∀ a, S a → VS a)
    {x y : ID} (hT : TermRefP (I.P b) (I.Q b) S f.value? tabs x (listedDefs g) tabs y) (hx : VS x)
    (hy : VT y) :
    Sem.Refines (rv G x) (rv T y) := by
  have htyS' : ∀ a, VS a → ¬ IsTerm f.value? a →
      (rv G a).retype (shape f.value? tabs a) = rv G a := fun a ha _ => by
    rw [← tys_shape]; exact htyS a _ (reg_rv (hDS a ha).1)
  refine termRef_apply hT hDS hx hDT hy (fun a h1 h2 h3 h4 => hrel a h3 h1 h2 h4) htyS'
    (fun a ha _ => ?_) (fun a ha hat hat' hdef _ => ?_) hinv (I.poisonAtom b) hSV
    (fun ρ hρ => I.qpois b _ ρ hq hρ) hMS
  · obtain ⟨v, hp⟩ := hVT a ha
    have : shape (listedDefs g) tabs a = shape g.value? tabs a := by
      simp [shape, placed_listed hp, hp.1]
    rw [this, ← tys_shape]; exact htyT a _ (reg_rv (hDT a ha).1)
  · rw [shape_atom_def H hat' hdef]; exact htyS' a ha hat

/-- `StepRefP`'s terminators between two frames whose atoms are refined. -/
theorem termStepRef_regs {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f}
    (H : Hyp tabs f g ce ce' I) {b : ID}
    {G T : Frame} {VS VT : ID → Prop}
    (hDS : DenOK f.value? tabs G VS) (hMS : MemDefs f.value? tabs G VS)
    (hDT : DenOK (listedDefs g) tabs T VT)
    (hVT : ∀ a, VT a → ∃ w, Placed g a w)
    (hrel : ∀ a, VT a → VS a → ¬ IsTerm f.value? a → ¬ IsTerm (listedDefs g) a →
      Sem.Refines (rv G a) (rv T a))
    (htyS : Proof.Typed (Ctx.make tabs f) G) (htyT : Proof.Typed (Ctx.make tabs g) T)
    (hinv : ∀ a, I.P b a (rv G a)) (hq : I.Q b (rv G)) (hSV : ∀ a, SAnc f b a → VS a)
    {fb gb : Block} (hT : StepRefP (I.P b) (I.Q b) (SAnc f b) f.value? tabs fb (listedDefs g) gb)
    (hx : ∀ c ∈ fb.controls, VS c) (hy : ∀ c ∈ gb.controls, VT c) :
    Res.Rel Next.Refines (stepTerm G fb) (stepTerm T gb) := by
  have htyS' : ∀ a, VS a → ¬ IsTerm f.value? a →
      (rv G a).retype (shape f.value? tabs a) = rv G a := fun a ha _ => by
    rw [← tys_shape]; exact htyS a _ (reg_rv (hDS a ha).1)
  refine termStepRef_apply hT hDS hx hDT hy (fun a h1 h2 h3 h4 => hrel a h3 h1 h2 h4) htyS'
    (fun a ha _ => ?_) (fun a ha hat hat' hdef _ => ?_) hinv (I.poisonAtom b) hSV
    (fun ρ hρ => I.qpois b _ ρ hq hρ) hMS
  · obtain ⟨v, hp⟩ := hVT a ha
    have : shape (listedDefs g) tabs a = shape g.value? tabs a := by
      simp [shape, placed_listed hp, hp.1]
    rw [this, ← tys_shape]; exact htyT a _ (reg_rv (hDT a ha).1)
  · rw [shape_atom_def H hat' hdef]; exact htyS' a ha hat

/-- The atoms the entry frames both hold are refined. -/
theorem BRel.rel {tabs : Tables} {f g : Func} {I : SrcInv tabs f} {frS frT : Frame} {b : ID} {i : Nat}
    (R : BRel tabs f g I frS frT b i) {VT VS : ID → Prop}
    (hDT : DenOK (listedDefs g) tabs frT VT) (hVT : ∀ a, VT a → ∃ w, Placed g a w) :
    ∀ a, VT a → VS a → ¬ IsTerm f.value? a → ¬ IsTerm (listedDefs g) a →
      Sem.Refines (rv frS a) (rv frT a) := fun a ha _ _ hat => by
  obtain ⟨w, hp⟩ := hVT a ha
  have ht : termOp w.op = false := by
    cases h : termOp w.op
    · rfl
    · exact absurd ⟨w, placed_listed hp, h⟩ hat
  obtain ⟨y, hy, hyy⟩ := R.atoms a w hp ht _ (reg_rv (hDT a ha).1)
  rw [rv_of hy]; exact hyy

/-! ## `Phi`s -/

theorem phiStep_nonphi {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID} {v : Value}
    (hv : ctx.f.value? z = some v) (hp : v.op ≠ .Phi) : phiStep ctx fr i z = .ok none := by
  unfold phiStep; rw [hv]; simp [hp]

theorem phiStep_phi {ctx : Ctx} {fr : Frame} {i : Nat} {z a : ID} {v : Value} {y : Val}
    (hv : ctx.f.value? z = some v) (hp : v.op = .Phi) (ha : v.args[i]? = some a)
    (hy : fr.regs[a]? = some (some y)) :
    phiStep ctx fr i z = .ok (some (z, y.retype (ctx.tys[z]?.getD .other))) := by
  unfold phiStep; rw [hv]; simp [hp, ha, hy]

/-- **The target's `Phi`s**, each refining the source's. -/
theorem tgt_phis {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {frS frT : Frame} {b : ID} {i : Nat} (R : BRel tabs f g I frS frT b i) {fb gb : Block}
    {of og : Array ID} (B : BlockData f g b fb gb of og) {psS : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok psS) :
    ∃ psT, gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok psT ∧
      ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
        ∃ y y', (setPhis psS frS.regs)[z]? = some (some y) ∧
          (setPhis psT frT.regs)[z]? = some (some y') ∧ Sem.Refines y y' := by
  obtain ⟨VS, VT, hDS, hDT, hVT, hsS, -, hPS, hPT, -⟩ := R.den
  obtain ⟨-, -, -, hphS⟩ := phis_spec B.vS hps
  -- each `Phi` of `g`: its argument in the target and the refinement
  have key : ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
      ∃ a', w.args[i]? = some a' ∧ Reg frT a' ∧ ∃ y, (setPhis psS frS.regs)[z]? = some (some y) ∧
        Sem.Refines y ((rv frT a').retype ((Ctx.make tabs g).tys[z]?.getD .other)) := by
    intro z hz w hw hph
    obtain ⟨hpw, hwb, -⟩ := placed_in H.wg B.bmT B.hgb hz hw
    have ht : termOp w.op = false := by rw [hph]; exact termOp_phi
    obtain ⟨u, hpu, hs⟩ := gatom_f H hpw ht
    obtain ⟨hop, hty, -, -, hsz, hblk, -⟩ := hs
    have hzf : z ∈ fb.values := by
      obtain ⟨-, -, blk, hblk', hzv⟩ := hpu
      rw [hblk, hwb, B.hfb] at hblk'; cases hblk'; exact hzv
    obtain ⟨a, y, ha, hy, hset⟩ := hphS z hzf u hpu.1 (hop.trans hph)
      (by rw [R.szS]; exact lt_of_value? hpu.1)
    have hi : i < u.args.size := (Array.getElem?_eq_some_iff.1 ha).1
    obtain ⟨a', ha'⟩ : ∃ a', w.args[i]? = some a' := ⟨w.args[i], by simp [← hsz, hi]⟩
    have hVTa : VT a' := hPT gb B.hgb z hz w hw hph a' ha'
    refine ⟨a', ha', (hDT a' hVTa).1, _, hset, ?_⟩
    rw [show (Ctx.make tabs g).tys[z]?.getD .other = (Ctx.make tabs f).tys[z]?.getD .other by
      rw [tys_of_value hw, tys_of_value hpu.1, hty]]
    refine retype_mono _ ?_
    obtain ⟨-, hwb', blk, hblk', hzv⟩ := hpw
    obtain ⟨u', hu', -, -, -, -, -, hTR⟩ := H.args w.block hwb' blk hblk' z hzv w hw ht
    rw [hpu.1] at hu'; cases hu'
    rcases R.pre with hno | ⟨p, pb, k, VP, hpm, hpb, hk, hinvP, hqP, hDP, hAncP, hPhiP, hMP⟩
    · exact (hno fb B.hfb z hzf u hpu.1 (hop.trans hph) a ha).elim
    have hTR' := (hTR i (hsz ▸ hi)).2 hph p pb k hpm hpb (by rw [hwb]; exact hk)
    rw [getElem!_pos u.args i hi, getElem!_pos w.args i (hsz ▸ hi)] at hTR'
    rw [← rv_of hy]
    have hai : u.args[i] = a := (Array.getElem?_eq_some_iff.1 ha).2
    have hai' : w.args[i]'(hsz ▸ hi) = a' := (Array.getElem?_eq_some_iff.1 ha').2
    rw [hai, hai'] at hTR'
    exact termRef_regs H hDP hMP hDT hVT (R.rel hDT hVT) R.tyS R.tyT hinvP hqP hAncP hTR'
      (hPhiP fb B.hfb z hzf u hpu.1 (hop.trans hph) a ha) hVTa
  obtain ⟨psT, hpsT⟩ := filterMapM_phi_ok (ctx := Ctx.make tabs g) (fr := frT) (i := i)
    (l := gb.values.toList) fun z hz => by
      have hz' := Array.mem_toList_iff.1 hz
      obtain ⟨w, hw, -, -⟩ := H.wg.valueId b gb ⟨B.bmT, B.hgb⟩ z hz'
      by_cases hph : w.op = .Phi
      · obtain ⟨a', ha', hreg, -⟩ := key z hz' w hw hph
        exact ⟨_, phiStep_phi hw hph ha' (reg_rv hreg)⟩
      · exact ⟨_, phiStep_nonphi hw hph⟩
  refine ⟨psT, hpsT, fun z hz w hw hph => ?_⟩
  obtain ⟨a', ha', hreg, y, hy, hyy⟩ := key z hz w hw hph
  obtain ⟨-, -, -, hphT⟩ := phis_spec B.vT hpsT
  obtain ⟨a'', y'', ha'', hy'', hset⟩ := hphT z hz w hw hph (by rw [R.szT]; exact lt_of_value? hw)
  rw [ha'] at ha''; cases ha''
  rw [reg_rv hreg] at hy''; cases hy''
  exact ⟨y, _, hy, hset, hyy⟩

end GoFV.Proof.AtomSim
