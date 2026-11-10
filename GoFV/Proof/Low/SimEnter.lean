import GoFV.Proof.Low.SimSet

variable [GoFV.SSA.Sem.Addrs]

/-!
# Block entries of the lowered atom simulation (issue #385)

Phase 1's `AtomSimBlock`/`AtomSimEnter`/`AtomSimNoPanic`/`AtomSimPanic` over `runL`, with the
trivial source invariant. `BRel frS frT b i`: the source and target frames at the entry of block
`b` along edge `i`: the same activation inputs, registers typed in each function's mode, `b` a
tree block of both dominator trees, every atom of `g` the target holds where `f` has no term
refined from the source's register, the frame addresses and the source's stack pointer those of
activation 0 (`RegsFrame`, `RegsFrameL`), and sets `VS`/`VT` with `DenOKL` that contain the
values of the strict ancestors of `b` and the `Phi` arguments along edge `i`. `enter_ok`: a source
block entry without panic is matched by the target's, the frames afterwards related (`EndRel`);
`enter_panic`: a panicking one by a target panic with a refined memory.
-/

namespace GoFV.Proof.Low.Sim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof GoFV.Proof.Dom GoFV.Proof.Low
  GoFV.Proof.Term GoFV.Proof.AtomSim GoFV.Opt.LowerCheck GoFV.Opt.LowerTerm

/-- The frame relation at a block entry. -/
structure BRel (tabs : Tables) (f g : Func) (frS frT : Frame) (b : ID) (i : Nat) : Prop where
  fr : frT = { frS with regs := frT.regs }
  szS : frS.regs.size = f.valueTab.size
  szT : frT.regs.size = g.valueTab.size
  tyS : RegsTyped ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frS
  tyT : RegsTyped ⟨g.lowered, false⟩ (Ctx.makeL tabs g) frT
  mem : b ∈ f.blocks
  treeS : ((make f).depthOf b).isSome
  treeT : ((make g).depthOf b).isSome
  atoms : ∀ a w, Placed g a w → termVL tabs w = false → ¬ IsTermL tabs f.value? a →
    (f.value? a).isSome = true →
    ∀ y', frT.regs[a]? = some (some y') → ∃ y, frS.regs[a]? = some (some y) ∧ Sem.Refines y y'
  frames : RegsFrame tabs 0 f.value? frS
  framesT : RegsFrameL tabs 0 g.value? frT
  den : ∃ VS VT, DenOKL f.lowered f.value? tabs frS VS ∧
    DenOKL g.lowered (listedDefs g) tabs frT VT ∧
    (∀ x, VT x → ∃ w, Placed g x w) ∧ (∀ x, SAnc f b x → VS x) ∧ (∀ x, SAnc g b x → VT x) ∧
    PhiArgs f b i VS ∧ PhiArgs g b i VT

/-- The static facts of block `b`. -/
structure BlockData (tabs : Tables) (f g : Func) (b : ID) (fb gb : Block) (of og : Array ID) :
    Prop where
  hfb : f.block? b = some fb
  hgb : g.block? b = some gb
  ba : BlockAtomsL tabs f g fb gb
  bmS : b ∈ f.blocks
  bmT : b ∈ g.blocks
  idS : fb.id = b
  idT : gb.id = b
  vS : fb.values.toList.Nodup
  vT : gb.values.toList.Nodup
  sS : schedule f fb = some of
  sT : schedule g gb = some og
  fl : of.toList.filter (rootL f) = og.toList.filter (rootAtL tabs f g)
  ndS : of.toList.Nodup
  tpS : TopoRem (argsF f) of.toList
  mS : ∀ x, x ∈ of.toList ↔ x ∈ fb.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi
  ndT : og.toList.Nodup
  tpT : TopoRem (argsF g) og.toList
  mT : ∀ x, x ∈ og.toList ↔ x ∈ gb.values ∧ ∃ v, g.value? x = some v ∧ v.op ≠ .Phi

section
variable {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
include H

theorem blockData {b : ID} {fb : Block} (hb : b ∈ f.blocks) (hfb : f.block? b = some fb) :
    ∃ gb of og, BlockData tabs f g b fb gb of og := by
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

end

theorem atomL_of_not_term {tabs : Tables} {g : Func} {a : ID} {w : Value} (hp : Placed g a w)
    (hat : ¬ IsTermL tabs (listedDefs g) a) : termVL tabs w = false := by
  cases h : termVL tabs w
  · rfl
  · exact absurd ⟨w, placed_listed hp, h⟩ hat

/-- The atoms the entry frames both hold are refined (`poison` in the source where `f` has no
value, `RegsFrame`). -/
theorem BRel.rel {tabs : Tables} {f g : Func} {frS frT : Frame} {b : ID} {i : Nat}
    (R : BRel tabs f g frS frT b i) {VT VS : ID → Prop}
    (hDT : DenOKL g.lowered (listedDefs g) tabs frT VT) (hVT : ∀ a, VT a → ∃ w, Placed g a w) :
    ∀ a, VT a → VS a → ¬ IsTermL tabs f.value? a → ¬ IsTermL tabs (listedDefs g) a →
      Sem.Refines (rv frS a) (rv frT a) := fun a ha _ hnf hat => by
  cases hfa : f.value? a with
  | none => rw [R.frames.rv_none hfa]; exact .poison _
  | some _ =>
    obtain ⟨w, hp⟩ := hVT a ha
    obtain ⟨y, hy, hyy⟩ := R.atoms a w hp (atomL_of_not_term hp hat) hnf (by rw [hfa]; rfl) _
      (reg_rv (hDT a ha).1)
    rw [rv_of hy]; exact hyy

/-! ## `Phi`s -/

theorem phiStepL_nonphi {md : LMode} {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID} {v : Value}
    (hv : ctx.f.value? z = some v) (hp : v.op ≠ .Phi) : phiStepL md ctx fr i z = .ok none := by
  unfold phiStepL; rw [hv]; simp [hp]

theorem phiStepL_phi {md : LMode} {ctx : Ctx} {fr : Frame} {i : Nat} {z a : ID} {v : Value}
    {y : Val} (hv : ctx.f.value? z = some v) (hp : v.op = .Phi) (ha : v.args[i]? = some a)
    (hy : fr.regs[a]? = some (some y)) :
    phiStepL md ctx fr i z = .ok (some (z, md.retype (ctx.tys[z]?.getD .other) y)) := by
  unfold phiStepL; rw [hv]; simp [hp, ha, hy]

/-- **The target's `Phi`s**, each refining the source's. -/
theorem tgt_phis {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    {frS frT : Frame} {b : ID} {i : Nat} (R : BRel tabs f g frS frT b i) {fb gb : Block}
    {of og : Array ID} (B : BlockData tabs f g b fb gb of og) {psS : List (ID × Val)}
    (hps : fb.values.toList.filterMapM
      (phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frS i) = .ok psS) :
    ∃ psT, gb.values.toList.filterMapM
        (phiStepL ⟨g.lowered, false⟩ (Ctx.makeL tabs g) frT i) = .ok psT ∧
      ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
        ∃ y y', (setPhis psS frS.regs)[z]? = some (some y) ∧
          (setPhis psT frT.regs)[z]? = some (some y') ∧ Sem.Refines y y' := by
  obtain ⟨VS, VT, hDS, hDT, hVT, -, -, hPS, hPT⟩ := R.den
  obtain ⟨-, -, -, hphS⟩ := phisL_spec B.vS hps
  rw [makeL_f] at hphS
  have key : ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
      ∃ a', w.args[i]? = some a' ∧ Reg frT a' ∧ ∃ y, (setPhis psS frS.regs)[z]? = some (some y) ∧
        Sem.Refines y (rty g.lowered ((Ctx.makeL tabs g).tys[z]?.getD .other) (rv frT a')) := by
    intro z hz w hw hph
    obtain ⟨hpw, hwb, -⟩ := placed_in H.wg B.bmT B.hgb hz hw
    have ht : termVL tabs w = false := termVL_phi hph
    obtain ⟨u, hpu, hut, hs⟩ := gatomL H hpw ht (not_termL_f_of_op H hpw ht (by rw [hph]; decide))
      (.inr (by rw [hph]; rfl))
    have huph : u.op = .Phi := (atomPair_phi hs).1 hph
    obtain ⟨-, hty, hblk, -⟩ := atomPair_spec hs
    have hnpb : pbLower u w = false := by
      cases hb : pbLower u w
      · rfl
      · exact absurd huph (pbLower_ops hb).1
    have hsz : u.args.size = w.args.size := atomPair_size hs (by
      cases hal : addrLower tabs u w
      · rfl
      · exact absurd huph (addrLower_ops hal).1) hnpb (by
      cases hix : idxLower tabs u w
      · rfl
      · exact absurd huph (idxLower_ops hix).1) (by
      cases hq : moveQLower tabs u w
      · rfl
      · exact absurd huph (moveQLower_ops hq).1) (by
      cases hq : moveQ2Lower u w
      · rfl
      · exact absurd huph (moveQ2Lower_ops hq).1) (by
      cases hz : zeroLower tabs u w
      · rfl
      · rw [(zeroLower_facts hz).1] at huph; cases huph) (by
      cases hz : zero2Lower u w
      · rfl
      · rw [(zero2Lower_facts hz).1] at huph; cases huph) (by
      cases hz : zeroIdxLower u w
      · rfl
      · rw [(zeroIdxLower_facts hz).1] at huph; cases huph)
    have hzf : z ∈ fb.values := by
      obtain ⟨-, -, blk, hblk', hzv⟩ := hpu
      rw [hblk, hwb, B.hfb] at hblk'; cases hblk'; exact hzv
    obtain ⟨a, y, ha, hy, hset⟩ := hphS z hzf u hpu.1 huph
      (by rw [R.szS]; exact lt_of_value? hpu.1)
    have hi : i < u.args.size := (Array.getElem?_eq_some_iff.1 ha).1
    have hi' : i < w.args.size := hsz ▸ hi
    obtain ⟨a', ha'⟩ : ∃ a', w.args[i]? = some a' := ⟨w.args[i], by simp [hi']⟩
    have hVTa : VT a' := hPT gb B.hgb z hz w hw hph a' ha'
    have hVSa : VS a := hPS fb B.hfb z hzf u hpu.1 huph a ha
    refine ⟨a', ha', (hDT a' hVTa).1, _, hset, ?_⟩
    have hai : u.args[i]! = a := by
      rw [getElem!_pos u.args i hi]; exact (Array.getElem?_eq_some_iff.1 ha).2
    have hai' : w.args[i]! = a' := by
      rw [getElem!_pos w.args i hi']; exact (Array.getElem?_eq_some_iff.1 ha').2
    have hr := (atom_ref H hDS hDT hVT (R.rel hDT hVT) R.tyS R.tyT R.frames R.framesT R.fr hpw
      hpu.1 ht hut).2.1
      hph i hi'
      (by rw [argIx_of_not hnpb, hai]; exact hVSa) (by rw [hai']; exact hVTa)
    rw [argIx_of_not hnpb, hai, hai', rv_of hy] at hr
    have hshape : (Ctx.makeL tabs g).tys[z]?.getD .other = (Ctx.makeL tabs f).tys[z]?.getD .other := by
      rw [tysL_of_value hw, tysL_of_value hpu.1, H.shp z u hpu.1, hty]
    have hshf : (Ctx.makeL tabs f).tys[z]?.getD .other = shpL tabs w.type := by
      rw [tysL_of_value hpu.1, H.shp z u hpu.1, hty, H.glow]; rfl
    rw [hshape, hshf]
    exact hr
  obtain ⟨psT, hpsT⟩ := filterMapM_phiL_ok (md := ⟨g.lowered, false⟩) (ctx := Ctx.makeL tabs g)
    (fr := frT) (i := i) (l := gb.values.toList) fun z hz => by
      have hz' := Array.mem_toList_iff.1 hz
      obtain ⟨w, hw, -, -⟩ := H.wg.valueId b gb ⟨B.bmT, B.hgb⟩ z hz'
      have hw' : (Ctx.makeL tabs g).f.value? z = some w := by rw [makeL_f]; exact hw
      by_cases hph : w.op = .Phi
      · obtain ⟨a', ha', hreg, -⟩ := key z hz' w hw hph
        exact ⟨_, phiStepL_phi hw' hph ha' (reg_rv hreg)⟩
      · exact ⟨_, phiStepL_nonphi hw' hph⟩
  refine ⟨psT, hpsT, fun z hz w hw hph => ?_⟩
  obtain ⟨a', ha', hreg, y, hy, hyy⟩ := key z hz w hw hph
  obtain ⟨-, -, -, hphT⟩ := phisL_spec B.vT hpsT
  rw [makeL_f] at hphT
  obtain ⟨a'', y'', ha'', hy'', hset⟩ := hphT z hz w hw hph (by rw [R.szT]; exact lt_of_value? hw)
  rw [ha'] at ha''; cases ha''
  rw [reg_rv hreg] at hy''; cases hy''
  exact ⟨y, _, hy, hset, hyy⟩

/-- **`DenOKL` after the `Phi`s.** -/
theorem denOKL_phis {ce : CheckEnv} {h : Func} (hwf : WF ce h) {b : ID} {hb : Block}
    (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb) {low : Bool} {D : ID → Option Value}
    {tabs : Tables} {md : LMode} {ctx : Ctx} (hctx : ctx.f = h) {fr : Frame} {V : ID → Prop}
    {i : Nat} {ps : List (ID × Val)}
    (hD : DenOKL low D tabs fr V) (hsub : ∀ x, SAnc h b x → V x) (hcl : ClosedL tabs D (SAnc h b))
    (hnt : ∀ x v, h.value? x = some v → v.op = .Phi → ¬ IsTermL tabs D x)
    (hsz : fr.regs.size = h.valueTab.size)
    (hps : hb.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps) :
    DenOKL low D tabs { fr with regs := setPhis ps fr.regs } (V1 h b hb) := by
  obtain ⟨-, -, hkeep, hphi⟩ := phisL_spec (hwf.valuesNodup b hb ⟨hbm, hbb⟩) hps
  rw [hctx] at hkeep hphi
  refine ((hD.restrict hsub hcl).frame (fr' := { fr with regs := setPhis ps fr.regs })
    (fun a ha => hkeep a (.inl (sanc_not_mem hwf hbm hbb ha)))).extend (W := PhiOf h hb)
    (fun _ _ => rfl) fun x ⟨hx, v, hv, hph⟩ _ => ⟨hnt x v hv hph, ?_⟩
  obtain ⟨a, y, -, -, hset⟩ := hphi x hx v hv hph (by rw [hsz]; exact lt_of_value? hv)
  exact ⟨_, hset⟩

theorem phiL_not_term_f {tabs : Tables} {f : Func} :
    ∀ x v, f.value? x = some v → v.op = .Phi → ¬ IsTermL tabs f.value? x :=
  fun x v hv hph ⟨v', hv', ht⟩ => by
    rw [hv] at hv'; cases hv'; rw [termVL_phi hph] at ht; cases ht

theorem phiL_not_term_g {tabs : Tables} {g : Func} :
    ∀ x v, g.value? x = some v → v.op = .Phi → ¬ IsTermL tabs (listedDefs g) x :=
  fun x v hv hph ⟨v', hv', ht⟩ => by
    rw [(listed_placed hv').1] at hv; cases hv; rw [termVL_phi hph] at ht; cases ht

/-! ## The source's schedule prefix -/

theorem termsOKL_of_topo {f : Func} {tabs : Tables} {low : Bool} {G : Frame} :
    ∀ {L : List ID} {V : ID → Prop}, TopoRem (argsF f) L → (∀ x ∈ L, Reg G x) →
      (∀ x ∈ L, ∀ v, f.value? x = some v → termVL tabs v = true →
        (∀ a ∈ v.args, V a ∨ a ∈ L) ∧ G.regs[x]? = some (some (rty low (shp low tabs v.type)
          (opValL tabs v.op (shp low tabs v.type) v.auxInt v.aux (v.args.toList.map (rv G)))))) →
      TermsOKL low f.value? tabs G V L
  | [], _, _, _, _ => trivial
  | x :: s, V, ⟨ht1, ht2⟩, hreg, hterm => by
    refine ⟨hreg x List.mem_cons_self, fun v hv hop => ?_, termsOKL_of_topo ht2
      (fun y hy => hreg y (List.mem_cons_of_mem _ hy)) fun y hy v hv hop => ?_⟩
    · obtain ⟨hargs, hr⟩ := hterm x List.mem_cons_self v hv hop
      refine ⟨fun a ha => (hargs a ha).resolve_right
        (ht1 a (by rw [argsF_of hv]; exact Array.mem_toList_iff.2 ha)), hr⟩
    · obtain ⟨hargs, hr⟩ := hterm y (List.mem_cons_of_mem _ hy) v hv hop
      refine ⟨fun a ha => ?_, hr⟩
      rcases hargs a ha with h | h
      · exact .inl (.inl h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inl (.inr rfl)
        · exact .inr h

section
variable {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
  {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData tabs f g b fb gb of og)
include H B

/-- The source schedule's values are own non-`Phi` values of the block. -/
theorem sched_ownL : ∀ x ∈ of.toList, ∀ v, f.value? x = some v → v.id = x ∧ v.op ≠ .Phi ∧ x ∈ fb.values :=
  fun x hx v hv => by
    obtain ⟨hxb, v', hv', hph⟩ := (B.mS x).1 hx
    rw [hv] at hv'; cases hv'
    exact ⟨(placed_in H.wf B.bmS B.hfb hxb hv).2.2, hph, hxb⟩

/-- The arguments of the values of a prefix `P` of the source's schedule are in `V1` or `P`. -/
theorem src_argsL (htree : ((make f).depthOf b).isSome) {P Q : List ID}
    (hPQ : of.toList = P ++ Q) :
    ∀ x ∈ P, ∀ v, f.value? x = some v → ∀ a ∈ v.args, V1 f b fb a ∨ a ∈ P := by
  intro x hx v hv a ha
  have hnd : P.Nodup := (List.nodup_append.1 (hPQ ▸ B.ndS)).1
  have hxof : x ∈ of.toList := by rw [hPQ]; exact List.mem_append_left _ hx
  rcases sched_args H.wf H.cf B.bmS B.hfb htree B.mS x hxof v hv a ha with h | h
  · exact .inl h
  · rw [hPQ] at h
    rcases List.mem_append.1 h with h | h
    · exact .inr h
    · exfalso
      obtain ⟨d, s, hd⟩ := List.append_of_mem hx
      have htop := hPQ ▸ B.tpS
      rw [hd, List.append_assoc, List.cons_append] at htop
      have := topoRem_mid htop a (by rw [argsF_of hv]; exact Array.mem_toList_iff.2 ha)
      exact this (List.mem_cons_of_mem _ (by rw [hd] at hnd; exact List.mem_append_right _ h))

/-- **The source's schedule prefix `P`**, from the frame after the `Phi`s. -/
theorem src_evalL {env : Env} (htree : ((make f).depthOf b).isSome) {frP G : Frame} {P Q : List ID}
    (hPQ : of.toList = P ++ Q) (hD : DenOKL f.lowered f.value? tabs frP (V1 f b fb))
    (hsz : frP.regs.size = f.valueTab.size)
    (hty : RegsTyped ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frP)
    (hev : evalAllL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) frP P = .ok G) :
    G = { frP with regs := G.regs } ∧ G.regs.size = frP.regs.size ∧
      RegsTyped ⟨f.lowered, false⟩ (Ctx.makeL tabs f) G ∧
      DenOKL f.lowered f.value? tabs G (fun a => V1 f b fb a ∨ a ∈ P) ∧
      (∀ z, z ∉ P → G.regs[z]? = frP.regs[z]?) ∧
      (∀ x ∈ P, ∃ u y, f.value? x = some u ∧ G.regs[x]? = some (some y) ∧
        evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) G u = .ok y) := by
  have hnd : P.Nodup := (List.nodup_append.1 (hPQ ▸ B.ndS)).1
  have htp : TopoRem (argsF f) P := topoRem_prefix (hPQ ▸ B.tpS)
  have hPof : ∀ x ∈ P, x ∈ of.toList := fun x hx => by rw [hPQ]; exact List.mem_append_left _ hx
  obtain ⟨e1, e2, e3, e4⟩ := evalAllL_spec hnd (by rw [makeL_f]; exact htp)
    (by rw [makeL_f]; exact hsz) hev
  rw [makeL_f] at e4
  have hown : ∀ x ∈ P, ∀ v, f.value? x = some v → v.id = x ∧ v.op ≠ .Phi ∧ x ∈ fb.values :=
    fun x hx v hv => sched_ownL H B x (hPof x hx) v hv
  have hdisj : ∀ x, V1 f b fb x → x ∉ P := fun x hV hx => by
    obtain ⟨hxb, v, hv, hph⟩ := (B.mS x).1 (hPof x hx)
    rcases hV with h | ⟨-, v', hv', hph'⟩
    · exact sanc_not_mem H.wf B.bmS B.hfb h hxb
    · rw [hv] at hv'; cases hv'; exact hph hph'
  refine ⟨e1, e2, regsTyped_evalAllL hty (fun x hx v hv => (hown x hx v (by
      rw [makeL_f] at hv; exact hv)).1) e3 (by rw [makeL_f]; exact e4),
    denOKL_terms (hD.frame fun a ha => e3 a (hdisj a ha)) ?_, e3, e4⟩
  have hargs := src_argsL H B htree hPQ
  refine termsOKL_of_topo htp (fun x hx => ?_) fun x hx v hv hop => ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨v, y, -, hy, -⟩ := e4 x hx; exact ⟨y, hy⟩
  · rcases hargs x hx v hv a ha with h | h
    · exact .inl h
    · exact .inr h
  · obtain ⟨v', y, hv', hy, hevy⟩ := e4 x hx
    rw [hv] at hv'; cases hv'
    have hy' := evalValueL_termL (ctx := Ctx.makeL tabs f) (by rw [makeL_tabs]; exact hop)
      (makeL_act tabs f) hevy
    rw [makeL_tabs, (hown x hx v hv).1, tysL_of_value hv] at hy'
    rw [hy, hy']; rfl

/-- A scheduled atom of `g` where `f` has no term, a value, is scheduled in `f`, as a
corresponding atom. -/
theorem atomL_sched {x : ID} (hx : x ∈ og.toList) {w : Value} (hw : g.value? x = some w)
    (ht : termVL tabs w = false) (hnf : ¬ IsTermL tabs f.value? x)
    (hfs : (f.value? x).isSome = true) :
    ∃ u, f.value? x = some u ∧ termVL tabs u = false ∧ atomPair tabs u w = true ∧ x ∈ of.toList ∧
      Placed g x w := by
  obtain ⟨hxb, w', hw', hph⟩ := (B.mT x).1 hx
  rw [hw] at hw'; cases hw'
  have hpw := (placed_in H.wg B.bmT B.hgb hxb hw).1
  rcases B.ba.sub x hxb w hw ht with ⟨hxf, u, hu, hut, hs, -⟩ | hfa | hco
  · exact ⟨u, hu, hut, hs, (B.mS x).2 ⟨hxf, u, hu, fun h => hph ((atomPair_phi hs).2 h)⟩, hpw⟩
  · exact absurd (frameAtomG_cases hfa).2.2.2 hnf
  · obtain ⟨hf, -⟩ := compOKL_cases hco
    rw [hf] at hfs; cases hfs

/-- The outer of two stores lowering a `Move` or a `Zero` reads, as its memory, a value of the
schedule (`q2OKL`). -/
theorem q2_last_og {x : ID} (hx : x ∈ og.toList) {u w : Value} (hu : f.value? x = some u)
    (hw : g.value? x = some w) (hq2 : st2Lower u w = true) :
    w.args[w.args.size - 1]! ∈ og.toList := by
  obtain ⟨hxb, w', hw', -⟩ := (B.mT x).1 hx
  rw [hw] at hw'; cases hw'
  have ht : termVL tabs w = false := termVL_qzStore (st2Lower_store hq2)
  rcases B.ba.sub x hxb w hw ht with ⟨-, u', hu', -, -, hq⟩ | hfa | hco
  · rw [hu] at hu'; cases hu'
    rw [B.sT] at hq
    simp only [Option.map_some, Option.getD_some, q2OKL, hq2, Bool.not_true, Bool.false_or,
      beq_iff_eq] at hq
    obtain ⟨A, B', C, hsplit, -⟩ := nextAtomL_spec hq
    rw [hsplit]; simp
  · have := st2Lower_store hq2
    rw [(frameAtomG_cases hfa).1] at this; cases this
  · obtain ⟨hf, -⟩ := compOKL_cases hco
    rw [hu] at hf; cases hf

/-- The inner store of two stores lowering a `Move` or a `Zero` (`compOKL`, `f` has no value at
`x`) and its owner `v`: the next atom of the schedule, a root of `f` and an atom of `g`
(`rootAtL`), the outer store reading `x` as its memory. -/
theorem comp_owner {x : ID} (hx : x ∈ og.toList) {w : Value} (hw : g.value? x = some w)
    (ht : termVL tabs w = false) (hfn : f.value? x = none) :
    ∃ v u wv A B' C, og.toList = A ++ x :: (B' ++ v :: C) ∧
      (∀ y ∈ B', (g.value? y).any (!termVL tabs ·) = false) ∧ f.value? v = some u ∧
      Placed g v wv ∧ st2Lower u wv = true ∧ wv.args[wv.args.size - 1]! = x ∧
      rootAtL tabs f g v = true := by
  obtain ⟨hxb, w', hw', -⟩ := (B.mT x).1 hx
  rw [hw] at hw'; cases hw'
  rcases B.ba.sub x hxb w hw ht with ⟨-, u, hu, -⟩ | hfa | hco
  · rw [hfn] at hu; cases hu
  · obtain ⟨v, hv, -⟩ := (frameAtomG_cases hfa).2.2.2
    rw [hfn] at hv; cases hv
  · rw [B.sT] at hco
    simp only [Option.map_some, Option.getD_some] at hco
    obtain ⟨-, -, -, v, u, wv, hnext, hu, hwv, hq2, -, hlast⟩ := compOKL_cases hco
    obtain ⟨A, B', C, hsplit, -, hB', -⟩ := nextAtomL_spec hnext
    have hvog : v ∈ og.toList := by rw [hsplit]; simp
    obtain ⟨hvb, wv', hwv', -⟩ := (B.mT v).1 hvog
    rw [hwv] at hwv'; cases hwv'
    refine ⟨v, u, wv, A, B', C, hsplit, hB', hu, (placed_in H.wg B.bmT B.hgb hvb hwv).1, hq2,
      hlast, ?_⟩
    have hr : isRoot u.op = true := by
      rcases st2Lower_cases hq2 with h | h
      · rw [(moveQ2Lower_facts h).1]; rfl
      · rw [(zero2Lower_facts h).1]; rfl
    have ht' := termVL_qzStore (tabs := tabs) (st2Lower_store hq2)
    simp [rootAtL, rootL, hu, hwv, hr, ht']

/-- Atoms placed outside `b` where `f` has no term, a value, keep their registers through block
`b`, in `f` too. -/
theorem atomL_out {a : ID} {w : Value} (hp : Placed g a w) (ht : termVL tabs w = false)
    (hnf : ¬ IsTermL tabs f.value? a) (hfs : (f.value? a).isSome = true) (hne : w.block ≠ b) :
    a ∉ gb.values ∧ a ∉ fb.values := by
  obtain ⟨u, hpu, -, hs⟩ := gatomL H hp ht hnf (.inl hfs)
  exact ⟨not_mem_of_placed H.wg hp B.bmT B.hgb hne,
    not_mem_of_placed H.wf hpu B.bmS B.hfb ((atomPair_spec hs).2.2.1 ▸ hne)⟩

/-- **The source's frame addresses and stack pointer after a schedule prefix** `P`, evaluated
from the frame after the `Phi`s: a `LocalAddr` (`SP`) of `P` evaluates to its address word
(`evalValueL_localAddr`, `evalValueL_sp`), the others keep their registers from the block entry
(`setPhis` writes only `Phi`s); the IDs `f` does not define are in no block's values. -/
theorem regsFrame_eval {env : Env} {frS G : Frame} {P : List ID} {psS : List (ID × Val)}
    (hfrS : RegsFrame tabs 0 f.value? frS) (hPof : ∀ x ∈ P, x ∈ of.toList)
    (hphi : ∀ z, (z ∉ fb.values ∨ ∃ v, f.value? z = some v ∧ v.op ≠ .Phi) →
      (setPhis psS frS.regs)[z]? = frS.regs[z]?)
    (hkeep : ∀ z, z ∉ P → G.regs[z]? = (setPhis psS frS.regs)[z]?)
    (hev : ∀ x ∈ P, ∃ u y, f.value? x = some u ∧ G.regs[x]? = some (some y) ∧
      evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) G u = .ok y) :
    RegsFrame tabs 0 f.value? G := by
  refine ⟨fun a l n y hl hop hax hy => ?_, fun a s y hs hop hy => ?_, fun a y ha hy => ?_⟩
  · by_cases haP : a ∈ P
    · obtain ⟨u, y', hu, hy', hevu⟩ := hev a haP
      rw [hl] at hu; cases hu
      rw [hy] at hy'; cases hy'
      have h := evalValueL_localAddr hop hax hevu
      rw [makeL_tabs, makeL_act, (sched_ownL H B a (hPof a haP) l hl).1, tysL_of_value hl,
        H.shp a l hl, H.glow] at h
      exact h
    · rw [hkeep a haP, hphi a (.inr ⟨l, hl, by rw [hop]; decide⟩)] at hy
      exact hfrS.1 a l n y hl hop hax hy
  · by_cases haP : a ∈ P
    · obtain ⟨u, y', hu, hy', hevu⟩ := hev a haP
      rw [hs] at hu; cases hu
      rw [hy] at hy'; cases hy'
      have h := evalValueL_sp hop hevu
      rw [makeL_act, (sched_ownL H B a (hPof a haP) s hs).1, tysL_of_value hs, H.shp a s hs,
        H.glow] at h
      exact h
    · rw [hkeep a haP, hphi a (.inr ⟨s, hs, by rw [hop]; decide⟩)] at hy
      exact hfrS.2.1 a s y hs hop hy
  · by_cases haP : a ∈ P
    · obtain ⟨u, -, hu, -⟩ := hev a haP
      rw [ha] at hu; cases hu
    · have hab : a ∉ fb.values := fun hm => by
        obtain ⟨w, hw, -⟩ := H.wf.valueId b fb ⟨B.bmS, B.hfb⟩ a hm
        rw [ha] at hw; cases hw
      rw [hkeep a haP, hphi a (.inl hab)] at hy
      exact hfrS.2.2 a y ha hy

end

/-- The target's frame addresses after the `Phi`s (`setPhis` writes only `Phi`s). -/
theorem regsFrameL_phis {tabs : Tables} {g : Func} {frT : Frame} {gb : Block}
    {ps : List (ID × Val)} (h : RegsFrameL tabs 0 g.value? frT)
    (hphi : ∀ z, (z ∉ gb.values ∨ ∃ v, g.value? z = some v ∧ v.op ≠ .Phi) →
      (setPhis ps frT.regs)[z]? = frT.regs[z]?) :
    RegsFrameL tabs 0 g.value? { frT with regs := setPhis ps frT.regs } :=
  fun a w n y hw hwn hy => by
    have hop := (frameAuxL_eq_some.1 hwn).1
    change (setPhis ps frT.regs)[a]? = _ at hy
    rw [hphi a (.inr ⟨w, hw, by rw [hop]; decide⟩)] at hy
    exact h a w n y hw hwn hy

/-- The frames after a block entry. -/
structure EndRel (tabs : Tables) (f g : Func) (b : ID) (fb gb : Block) (of og : Array ID)
    (FS FT : Frame) : Prop where
  fr : FT = { FS with regs := FT.regs }
  szS : FS.regs.size = f.valueTab.size
  szT : FT.regs.size = g.valueTab.size
  tyS : RegsTyped ⟨f.lowered, false⟩ (Ctx.makeL tabs f) FS
  tyT : RegsTyped ⟨g.lowered, false⟩ (Ctx.makeL tabs g) FT
  dS : DenOKL f.lowered f.value? tabs FS (fun a => V1 f b fb a ∨ a ∈ of.toList)
  dT : DenOKL g.lowered (listedDefs g) tabs FT (fun a => V1 g b gb a ∨ a ∈ og.toList)
  rel : ∀ a, (V1 g b gb a ∨ a ∈ og.toList) → (V1 f b fb a ∨ a ∈ of.toList) →
    ¬ IsTermL tabs f.value? a → ¬ IsTermL tabs (listedDefs g) a → Sem.Refines (rv FS a) (rv FT a)
  atoms : ∀ a w, Placed g a w → termVL tabs w = false → ¬ IsTermL tabs f.value? a →
    (f.value? a).isSome = true →
    ∀ y', FT.regs[a]? = some (some y') → ∃ y, FS.regs[a]? = some (some y) ∧ Sem.Refines y y'
  frames : RegsFrame tabs 0 f.value? FS
  framesT : RegsFrameL tabs 0 g.value? FT

/-- The frames after the `Phi`s, and their relation. -/
private theorem after_phis {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (H : Hyp tabs f g ce ce') {frS frT : Frame} {b : ID} {i : Nat} (R : BRel tabs f g frS frT b i)
    {fb gb : Block} {of og : Array ID} (B : BlockData tabs f g b fb gb of og)
    {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM
      (phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frS i) = .ok psS) :
    ∃ psT, gb.values.toList.filterMapM
        (phiStepL ⟨g.lowered, false⟩ (Ctx.makeL tabs g) frT i) = .ok psT ∧
      DenOKL f.lowered f.value? tabs { frS with regs := setPhis psS frS.regs } (V1 f b fb) ∧
      DenOKL g.lowered (listedDefs g) tabs { frT with regs := setPhis psT frT.regs } (V1 g b gb) ∧
      RegsTyped ⟨f.lowered, false⟩ (Ctx.makeL tabs f) { frS with regs := setPhis psS frS.regs } ∧
      RegsTyped ⟨g.lowered, false⟩ (Ctx.makeL tabs g) { frT with regs := setPhis psT frT.regs } ∧
      (setPhis psS frS.regs).size = frS.regs.size ∧ (setPhis psT frT.regs).size = frT.regs.size ∧
      (∀ z, (z ∉ fb.values ∨ ∃ v, f.value? z = some v ∧ v.op ≠ .Phi) →
        (setPhis psS frS.regs)[z]? = frS.regs[z]?) ∧
      (∀ z, (z ∉ gb.values ∨ ∃ v, g.value? z = some v ∧ v.op ≠ .Phi) →
        (setPhis psT frT.regs)[z]? = frT.regs[z]?) ∧
      (∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
        ∃ y y', (setPhis psS frS.regs)[z]? = some (some y) ∧
          (setPhis psT frT.regs)[z]? = some (some y') ∧ Sem.Refines y y') ∧
      -- the atoms both frames hold after the `Phi`s, where `f` has a value and no term
      (∀ a, V1 g b gb a → ¬ IsTermL tabs f.value? a → ¬ IsTermL tabs (listedDefs g) a →
        (f.value? a).isSome = true →
        ∃ y, (setPhis psS frS.regs)[a]? = some (some y) ∧ a ∉ of.toList ∧
          Sem.Refines y (rv { frT with regs := setPhis psT frT.regs } a)) := by
  obtain ⟨psT, hpsT, hphis⟩ := tgt_phis H R B hpsS
  obtain ⟨VS, VT, hDS, hDT, hVT, hsS, hsT, -, -⟩ := R.den
  have hS1 := denOKL_phis H.wf B.bmS B.hfb (makeL_f tabs f) hDS hsS
    (closedL_sanc_f H.wf H.cf tabs b) phiL_not_term_f R.szS hpsS
  have hT1 := denOKL_phis H.wg B.bmT B.hgb (makeL_f tabs g) hDT hsT
    (closedL_sanc_g H.wg H.cg tabs b) phiL_not_term_g R.szT hpsT
  obtain ⟨pS1, pS2, pS3, pS4⟩ := phisL_spec B.vS hpsS
  obtain ⟨pT1, pT2, pT3, pT4⟩ := phisL_spec B.vT hpsT
  have htyPS := regsTyped_phis (frP := { frS with regs := setPhis psS frS.regs }) R.tyS pS1 pS3 pS4 pS2
  have htyPT := regsTyped_phis (frP := { frT with regs := setPhis psT frT.regs }) R.tyT pT1 pT3 pT4 pT2
  rw [makeL_f] at pS3 pT3
  refine ⟨psT, hpsT, hS1, hT1, htyPS, htyPT, pS1, pT1, pS3, pT3, hphis,
    fun a ha hnf hatE hfs => ?_⟩
  obtain ⟨w, hpw⟩ := v1_placed H.wg B.bmT B.hgb a ha
  have hwt := atomL_of_not_term hpw hatE
  rcases ha with ⟨w', hpw', hanc, hne⟩ | ⟨haz, w', hw', hph⟩
  · have hww := placed_val hpw' hpw.1; subst hww
    obtain ⟨hnT, hnS⟩ := atomL_out H B hpw hwt hnf hfs hne
    have hreg := reg_rv (hT1 a (.inl ⟨w, hpw, hanc, hne⟩)).1
    change (setPhis psT frT.regs)[a]? = _ at hreg
    rw [pT3 a (.inl hnT)] at hreg
    obtain ⟨y, hy, hyy⟩ := R.atoms a w hpw hwt hnf hfs _ hreg
    have hof : a ∉ of.toList := fun hm => hnS ((B.mS a).1 hm).1
    refine ⟨y, (pS3 a (.inl hnS)).trans hy, hof, ?_⟩
    unfold rv; change Sem.Refines y (((setPhis psT frT.regs)[a]?).join.getD .poison)
    rw [pT3 a (.inl hnT), hreg]; exact hyy
  · obtain ⟨y, y', hy, hy', hyy⟩ := hphis a haz w' hw' hph
    have hof : a ∉ of.toList := fun hm => by
      obtain ⟨-, u, hu, hph'⟩ := (B.mS a).1 hm
      obtain ⟨u', hpu, -, hs⟩ := gatomL H hpw hwt hnf (.inl hfs)
      rw [placed_val hpw hw'] at hph
      rw [hpu.1] at hu; cases hu; exact hph' ((atomPair_phi hs).1 hph)
    refine ⟨y, hy, hof, ?_⟩
    show Sem.Refines y (rv { frT with regs := setPhis psT frT.regs } a)
    rw [rv_of hy']; exact hyy

/-- **A block entry without panic.** -/
theorem enter_ok {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    {env : Env} (hE : env.Mono) {frS frT : Frame} {b : ID} {i : Nat}
    (R : BRel tabs f g frS frT b i) {fb gb : Block} {of og : Array ID}
    (B : BlockData tabs f g b fb gb of og) {FS : Frame}
    (he : enterBlockL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) frS fb i = .ok FS) :
    ∃ FT, enterBlockL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) frT gb i = .ok FT ∧
      EndRel tabs f g b fb gb of og FS FT := by
  obtain ⟨psS, o, hpsS, ho, hevS⟩ := enterBlockL_ok_split he
  rw [schedL_of_block B.hfb B.idS, B.sS] at ho; cases ho
  obtain ⟨psT, hpsT, hS1, hT1, htyPS, htyPT, pS1, pT1, pS3, pT3, hphis, hat0⟩ :=
    after_phis H R B hpsS
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := src_evalL H B R.treeS (P := of.toList) (Q := [])
    (by simp) hS1 (by rw [pS1, R.szS]) htyPS hevS
  have hfrT : { frT with regs := setPhis psT frT.regs } =
      { FS with regs := ({ frT with regs := setPhis psT frT.regs } : Frame).regs } :=
    frame_trans (frame_trans rfl R.fr) (frame_symm (frame_trans g1 rfl))
  have hfrFS := regsFrame_eval H B R.frames (P := of.toList) (fun x hx => hx) pS3 g5 g6
  have hrel0 : ∀ a, V1 g b gb a → (V1 f b fb a ∨ a ∈ of.toList) → ¬ IsTermL tabs f.value? a →
      ¬ IsTermL tabs (listedDefs g) a →
      Sem.Refines (rv FS a) (rv { frT with regs := setPhis psT frT.regs } a) := by
    intro a ha _ hnf hatE
    cases hfa : f.value? a with
    | none => rw [hfrFS.rv_none hfa]; exact .poison _
    | some _ =>
      obtain ⟨y, hy, hof, hyy⟩ := hat0 a ha hnf hatE (by rw [hfa]; rfl)
      rw [rv_of (show FS.regs[a]? = some (some y) by rw [g5 a hof]; exact hy)]
      exact hyy
  obtain ⟨FT, hevT, l1, l2, l3, l4, l5, l6, l7, -⟩ := tgt_loop H hE (og := og.toList)
    (L := og.toList) (M := []) (P := of.toList) (by simp) hfrT (by rw [pT1, R.szT]) g3 htyPT g4
    hfrFS (regsFrameL_phis R.framesT pT3) hT1
    (v1_placed H.wg B.bmT B.hgb) (v1_disj H.wg B.bmT B.hgb B.mT) hrel0 B.ndT B.tpT
    (fun x hx => by
      obtain ⟨hxb, w, hw, hph⟩ := (B.mT x).1 hx
      obtain ⟨hp, -, hid⟩ := placed_in H.wg B.bmT B.hgb hxb hw
      exact ⟨w, hp, hid, hph⟩)
    (sched_args H.wg H.cg B.bmT B.hgb R.treeT B.mT)
    (fun a ha _ hnf hat hfs => by
      obtain ⟨hxb, w, hw, -⟩ := (B.mT a).1 ha
      obtain ⟨-, -, -, -, hof, -⟩ := atomL_sched H B ha hw (atomL_of_not_term
        (placed_in H.wg B.bmT B.hgb hxb hw).1 hat) hnf hfs
      exact hof)
    (fun x hx w hw ht hnf hfs => by
      obtain ⟨u, hu, -, -, hof, -⟩ := atomL_sched H B hx hw ht hnf hfs
      refine ⟨u, hu, fun _ => ⟨fun a ha => sched_args H.wf H.cf B.bmS B.hfb R.treeS B.mS x hof
        u hu a ha, ?_⟩, fun h => absurd hof h⟩
      obtain ⟨u', y, hu', hy, hev⟩ := g6 x hof
      rw [hu] at hu'; cases hu'
      exact ⟨y, hy, hev⟩)
    (fun x hx u w hu hw hq2 => q2_last_og H B hx hu hw hq2)
    (fun x hx w hw ht hfn => by
      obtain ⟨v, u, wv, A, B', C, hsplit, -, hu, hpv, hq2, hlast, hroot⟩ :=
        comp_owner H B hx hw ht hfn
      have hvog : v ∈ og.toList := by rw [hsplit]; simp
      have hvof : v ∈ of.toList := by
        have : v ∈ og.toList.filter (rootAtL tabs f g) := List.mem_filter.2 ⟨hvog, hroot⟩
        rw [← B.fl] at this
        exact (List.mem_filter.1 this).1
      exact ⟨v, u, wv, hvof, hu, hpv, hq2, hlast⟩)
    (fun v hv => by
      obtain ⟨u, y, hu, hy, hev⟩ := g6 v hv
      exact ⟨u, hu, fun a ha => sched_args H.wf H.cf B.bmS B.hfb R.treeS B.mS v hv u hu a ha, y,
        hy, hev⟩)
  refine ⟨FT, enterBlockL_of hpsT (by rw [schedL_of_block B.hgb B.idT, B.sT]) hevT, ?_⟩
  have hfr : FT = { FS with regs := FT.regs } := frame_trans l1 hfrT
  refine ⟨hfr, by rw [g2, pS1, R.szS], by rw [l2, pT1, R.szT], g3, l3, g4, l4,
    fun a h1 h2 h3 h4 => l6 a h1 h2 h3 h4, fun a w hpw hwt hnf hfs y' hy' => ?_, hfrFS, l7⟩
  by_cases hwb : w.block = b
  · have haz : a ∈ gb.values := by
      obtain ⟨-, -, blk, hblk, hx⟩ := hpw
      rw [hwb, B.hgb] at hblk; cases hblk; exact hx
    by_cases hph : w.op = .Phi
    · obtain ⟨y, y'', hy, hy'', hyy⟩ := hphis a haz w hpw.1 hph
      have hog : a ∉ og.toList := fun hm => by
        obtain ⟨-, w', hw', hph'⟩ := (B.mT a).1 hm
        rw [hpw.1] at hw'; cases hw'; exact hph' hph
      rw [l5 a hog, hy''] at hy'; cases hy'
      have hof : a ∉ of.toList := fun hm => by
        obtain ⟨-, u, hu, hph'⟩ := (B.mS a).1 hm
        obtain ⟨u', hpu, -, hs⟩ := gatomL H hpw hwt hnf (.inl hfs)
        rw [hpu.1] at hu; cases hu; exact hph' ((atomPair_phi hs).1 hph)
      exact ⟨y, by rw [g5 a hof]; exact hy, hyy⟩
    · have hog : a ∈ og.toList := (B.mT a).2 ⟨haz, w, hpw.1, hph⟩
      obtain ⟨u, hu, -, -, hof, -⟩ := atomL_sched H B hog hpw.1 hwt hnf hfs
      have hr := l6 a (.inr hog) (.inr hof) hnf
        (fun ⟨w', hw', ht'⟩ => by rw [placed_listed hpw] at hw'; cases hw'; rw [hwt] at ht'; cases ht')
      obtain ⟨u', y, hu', hy, -⟩ := g6 a hof
      rw [rv_of hy, rv_of hy'] at hr
      exact ⟨y, hy, hr⟩
  · obtain ⟨hnT, hnS⟩ := atomL_out H B hpw hwt hnf hfs hwb
    have hog : a ∉ og.toList := fun hm => hnT ((B.mT a).1 hm).1
    have hof : a ∉ of.toList := fun hm => hnS ((B.mS a).1 hm).1
    rw [l5 a hog] at hy'
    change (setPhis psT frT.regs)[a]? = _ at hy'
    rw [pT3 a (.inl hnT)] at hy'
    obtain ⟨y, hy, hyy⟩ := R.atoms a w hpw hwt hnf hfs y' hy'
    exact ⟨y, by rw [g5 a hof]; exact (pS3 a (.inl hnS)).trans hy, hyy⟩

/-! ## A panicking block entry -/

theorem prio_of_panickingL {op : Op} (h : PanickingL false op) : prio op ≠ 0 := by
  unfold prio isRoot
  rcases h with h | h | ⟨h, -⟩
  · cases hn : op.nilCheck <;> simp [h, hn]
  · simp [h]
  · cases h

/-- An `Arg`/`ArgIntReg` of the source schedule comes before its panicking root. -/
theorem arg_beforeL {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData tabs f g b fb gb of og)
    {pre post : List ID} {r : ID} (hof : of.toList = pre ++ r :: post) {ur : Value}
    (hur : f.value? r = some ur) (hrp : prio ur.op ≠ 0) {x : ID} (hx : x ∈ of.toList) (hxr : x ≠ r)
    {u : Value} (hu : f.value? x = some u) (harg : u.op = .Arg ∨ u.op = .ArgIntReg) : x ∈ pre := by
  have hspec := schedule_spec B.sS
  have hown := valuesOwn H.wf B.bmS B.hfb
  obtain ⟨hxb, u', hu', hph⟩ := (B.mS x).1 hx
  rw [hu] at hu'; cases hu'
  have hrof : r ∈ of.toList := by rw [hof]; simp
  obtain ⟨hrb, ur', hur', hrph⟩ := (B.mS r).1 hrof
  rw [hur] at hur'; cases hur'
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  have hk : of.toList[pre.length]? = some r := by rw [hof]; simp
  rcases Nat.lt_trichotomy j pre.length with hlt | heq | hgt
  · rw [hof, List.getElem?_append_left hlt] at hj
    exact List.mem_of_getElem? hj
  · subst heq; rw [hk] at hj; cases hj; exact absurd rfl hxr
  · exfalso
    have hnr := nodeOf_schedNodes hown B.vS hrb hur hrph
    have hnx := nodeOf_schedNodes hown B.vS hxb hu hph
    obtain ⟨a, ha, -⟩ := hspec.pureFirst pre.length j r x hgt hk hj
      (fun hp => hrp (hp _ hnr)) (fun n hn => by
        rw [hnx] at hn; cases hn
        rcases harg with h | h <;> rw [h] <;> rfl)
    rw [argsOf_schedNodes hown B.vS hxb hu hph] at ha
    have har := H.wf.arity b fb x u ⟨⟨B.bmS, B.hfb⟩, hxb, hu⟩
      (by rcases harg with h | h <;> rw [h] <;> decide)
    have h0 : u.args.size = 0 := by
      have hA : Op.argLen .Arg = 0 := by decide
      have hB : Op.argLen .ArgIntReg = 0 := by decide
      rcases harg with h | h
      · rw [h, hA] at har; omega
      · rw [h, hB] at har; omega
    rw [Array.size_eq_zero_iff.1 h0] at ha
    cases ha

/-- A corresponding atom of a generic op of `g` has the same op in `f`. -/
theorem atomPair_op_of_generic {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true)
    (hg : w.op.generic = true) : u.op = w.op := by
  rcases (atomPair_spec h).1 with ⟨⟨h | h, -⟩ | h | h, -⟩ | h | h | h | h | h | h | h | h
  · exact h
  · exfalso
    rcases renameOp_cases h with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ |
        ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | h9 <;> first
      | (rw [h2] at hg; exact absurd hg (by decide))
      | (rw [(atomicRen_facts h9).2.1] at hg; cases hg)
  · exfalso
    obtain ⟨-, -, -, n, hs, -⟩ := memLower_cases h
    generalize w.op = o at hs hg; cases hs <;> exact absurd hg (by decide)
  · exfalso
    rcases bulkLower_op h with h2 | h2 | h2 | h2 <;> rw [h2] at hg <;> exact absurd hg (by decide)
  · exfalso
    rw [(addrLower_cases h).2.1] at hg; exact absurd hg (by decide)
  · exfalso
    obtain ⟨-, -, -, ks, hks, -⟩ := pbLower_cases h
    rcases pbKeep_cases hks with ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h2] at hg <;> exact absurd hg (by decide)
  · exfalso
    obtain ⟨-, -, -, -, -, p, s, -, hp, -⟩ := idxLower_cases h
    rw [(idxStore_facts hp).1] at hg; cases hg
  · exfalso
    rcases (Sim.moveQLower_cases h).2 with hw | hw <;> rw [hw.2.1] at hg <;> cases hg
  · exfalso
    rcases qStore_cases (moveQ2Lower_qStore h) with h2 | h2 <;> rw [h2] at hg <;> cases hg
  · exfalso
    have hz := (zeroLower_facts h).2.2.2.2.1
    unfold zStore at hz
    simp only [Bool.or_eq_true, beq_iff_eq] at hz
    rcases hz with (((h2 | h2) | h2) | h2) | h2 <;> rw [h2] at hg <;> cases hg
  · exfalso
    obtain ⟨-, so, -, hso, -⟩ := zero2Op_cases (zero2Lower_facts h).2.2.2.choose_spec.choose_spec
    rcases hso with ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h2] at hg <;> cases hg
  · exfalso
    obtain ⟨-, -, -, -, -, o, k, s, -, hp⟩ := zeroIdxLower_facts h
    rw [(idxStore_facts hp).1] at hg; cases hg

/-- A split of a list without duplicates around `x` is unique. -/
private theorem split_unique {x : ID} :
    ∀ {A P s t : List ID}, A ++ x :: s = P ++ x :: t → x ∉ A → x ∉ P → A = P ∧ s = t
  | [], [], _, _, h, _, _ => ⟨rfl, (List.cons.inj h).2⟩
  | [], p :: P, _, _, h, _, hP => by
    obtain ⟨rfl, -⟩ := List.cons.inj h
    exact absurd (List.mem_cons_self) hP
  | a :: A, [], _, _, h, hA, _ => by
    obtain ⟨rfl, -⟩ := List.cons.inj h
    exact absurd (List.mem_cons_self) hA
  | a :: A, p :: P, _, _, h, hA, hP => by
    obtain ⟨rfl, h'⟩ := List.cons.inj h
    obtain ⟨rfl, rfl⟩ := split_unique h' (fun hm => hA (List.mem_cons_of_mem _ hm))
      (fun hm => hP (List.mem_cons_of_mem _ hm))
    exact ⟨rfl, rfl⟩

/-- In a list without duplicates split as `A ++ x :: (B ++ v :: C)` and as `P ++ r :: Q` with
`x ∈ P` and `r ∉ B`, `v` is in `P` or is `r`. -/
private theorem mem_before {l A B C P Q : List ID} {x v r : ID} (h1 : l = A ++ x :: (B ++ v :: C))
    (h2 : l = P ++ r :: Q) (hnd : l.Nodup) (hx : x ∈ P) (hr : r ∉ B) : v ∈ P ∨ v = r := by
  obtain ⟨P1, D, rfl⟩ := List.append_of_mem hx
  have e : A ++ x :: (B ++ v :: C) = P1 ++ x :: (D ++ r :: Q) := by rw [← h1, h2]; simp
  have hxA : x ∉ A := fun hm => by
    rw [h1] at hnd; exact (List.nodup_append.1 hnd).2.2 x hm x List.mem_cons_self rfl
  have hxP : x ∉ P1 := fun hm => by
    rw [h2] at hnd
    have hnd' : (P1 ++ x :: (D ++ r :: Q)).Nodup := by simpa using hnd
    exact (List.nodup_append.1 hnd').2.2 x hm x List.mem_cons_self rfl
  obtain ⟨-, e2⟩ := split_unique e hxA hxP
  rcases List.append_eq_append_iff.1 e2 with ⟨a', hD, hv⟩ | ⟨c', hB, hr'⟩
  · cases a' with
    | nil => exact .inr (List.cons.inj hv).1
    | cons b a'' =>
      obtain ⟨rfl, -⟩ := List.cons.inj hv
      exact .inl (by rw [hD]; simp)
  · cases c' with
    | nil => exact .inr (List.cons.inj hr').1.symm
    | cons b c'' =>
      obtain ⟨rfl, -⟩ := List.cons.inj hr'
      exact absurd (by rw [hB]; simp) hr

/-- **A panicking block entry.** -/
theorem enter_panic {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    {env : Env} (hE : env.Mono) {frS frT : Frame} {b : ID} {i : Nat}
    (R : BRel tabs f g frS frT b i) {fb gb : Block} {of og : Array ID}
    (B : BlockData tabs f g b fb gb of og) {e : Panic} {m : Mem}
    (he : enterBlockL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) frS fb i = .panic e m) :
    ∃ m', enterBlockL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) frT gb i = .panic e m' ∧
      Mem.Refines m m' := by
  obtain ⟨psS, o, hpsS, ho, hevS⟩ := enterBlockL_panic he
  rw [schedL_of_block B.hfb B.idS, B.sS] at ho; cases ho
  obtain ⟨pre, r, post, G, hof, hpre, hstep⟩ := evalAllL_panic_split hevS
  -- the panicking root, in both schedules
  obtain ⟨ur, hur, hevr⟩ : ∃ ur, f.value? r = some ur ∧
      evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) G ur = .panic e m := by
    unfold stepVL at hstep
    rw [makeL_f] at hstep
    cases h : f.value? r with
    | none => rw [h] at hstep; cases hstep
    | some ur => rw [h] at hstep; exact ⟨ur, rfl, hstep⟩
  have hrp : prio ur.op ≠ 0 := prio_of_panickingL (evalValueL_panic_op hevr)
  have hrof : r ∈ of.toList := by rw [hof]; simp
  have hrS : rootL f r = true := by simp [rootL, hur, isRoot_of_prio hrp]
  have hrog : r ∈ og.toList ∧ rootAtL tabs f g r = true := by
    have : r ∈ of.toList.filter (rootL f) := List.mem_filter.2 ⟨hrof, hrS⟩
    rw [B.fl] at this; exact List.mem_filter.1 this
  obtain ⟨preT, postT, hog⟩ := List.append_of_mem hrog.1
  have hrpre : r ∉ pre := fun hm => by
    have := B.ndS; rw [hof] at this
    exact (List.nodup_append.1 this).2.2 r hm r List.mem_cons_self rfl
  have hrpreT : r ∉ preT := fun hm => by
    have := B.ndT; rw [hog] at this
    exact (List.nodup_append.1 this).2.2 r hm r List.mem_cons_self rfl
  have hfl : pre.filter (rootL f) = preT.filter (rootAtL tabs f g) := by
    have := B.fl; rw [hof, hog] at this
    exact filter_prefix this hrS hrog.2 hrpre hrpreT
  obtain ⟨wr, hwr, hwrt⟩ : ∃ wr, g.value? r = some wr ∧ termVL tabs wr = false := by
    have := hrog.2; simp only [rootAtL, Bool.and_eq_true] at this
    have h2 := this.2
    cases h : g.value? r with
    | none => rw [h] at h2; cases h2
    | some wr => rw [h] at h2; exact ⟨wr, rfl, by simpa using h2⟩
  have hnfr : ¬ IsTermL tabs f.value? r := fun ⟨v, hv, hvt⟩ => by
    rw [hur] at hv; cases hv
    exact evalValueL_termL_ne_panic (ctx := Ctx.makeL tabs f) (by rw [makeL_tabs]; exact hvt)
      (makeL_act tabs f) hevr
  obtain ⟨u, hu, hurt, hpair, -, hpwr⟩ := atomL_sched H B hrog.1 hwr hwrt hnfr (by rw [hur]; rfl)
  rw [hur] at hu; cases hu
  -- the `Phi`s and the frames after them
  obtain ⟨psT, hpsT, hS1, hT1, htyPS, htyPT, pS1, pT1, pS3, pT3, -, hat0⟩ := after_phis H R B hpsS
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := src_evalL H B R.treeS (P := pre) (Q := r :: post)
    hof hS1 (by rw [pS1, R.szS]) htyPS hpre
  have hfrT : { frT with regs := setPhis psT frT.regs } =
      { G with regs := ({ frT with regs := setPhis psT frT.regs } : Frame).regs } :=
    frame_trans (frame_trans rfl R.fr) (frame_symm (frame_trans g1 rfl))
  have hpreof : ∀ x ∈ pre, x ∈ of.toList := fun x hx => by
    rw [hof]; exact List.mem_append_left _ hx
  -- arguments of source values of `pre` and of `r` are in `V1` or `pre`
  have hargsS : ∀ x, (x ∈ pre ∨ x = r) → ∀ u, f.value? x = some u → ∀ a ∈ u.args,
      V1 f b fb a ∨ a ∈ pre := by
    intro x hx u hu a ha
    have hxof : x ∈ of.toList := hx.elim (hpreof x) fun h => h ▸ hrof
    rcases sched_args H.wf H.cf B.bmS B.hfb R.treeS B.mS x hxof u hu a ha with h | h
    · exact .inl h
    · right
      have hfa : a ∈ argsF f x := by rw [argsF_of hu]; exact Array.mem_toList_iff.2 ha
      rcases hx with hx | rfl
      · obtain ⟨d, s, hd⟩ := List.append_of_mem hx
        have htop := B.tpS
        rw [hof, hd, List.append_assoc, List.cons_append] at htop
        rw [hof, hd, List.append_assoc, List.cons_append] at h
        have := topoRem_before htop hfa h
        rw [hd]; exact List.mem_append_left _ this
      · have htop := B.tpS; rw [hof] at htop
        rw [hof] at h
        exact topoRem_before htop hfa h
  have hfrG := regsFrame_eval H B R.frames (P := pre) hpreof pS3 g5 g6
  have hrelT0 : ∀ a, V1 g b gb a → (V1 f b fb a ∨ a ∈ pre) → ¬ IsTermL tabs f.value? a →
      ¬ IsTermL tabs (listedDefs g) a →
      Sem.Refines (rv G a) (rv { frT with regs := setPhis psT frT.regs } a) := by
    intro a ha _ hnf hatE
    cases hfa : f.value? a with
    | none => rw [hfrG.rv_none hfa]; exact .poison _
    | some _ =>
      obtain ⟨y, hy, hof', hyt⟩ := hat0 a ha hnf hatE (by rw [hfa]; rfl)
      have hnpre : a ∉ pre := fun hm => hof' (hpreof a hm)
      rw [rv_of (show G.regs[a]? = some (some y) by rw [g5 a hnpre]; exact hy)]
      exact hyt
  have hogpre : ∀ x ∈ preT, x ∈ og.toList := fun x hx => by
    rw [hog]; exact List.mem_append_left _ hx
  -- a `Move` does not panic
  have hnmove : ur.op ≠ .Move := fun hm => by
    have hp := evalValueL_panic_op hevr
    rw [hm] at hp
    rcases hp with h | h | ⟨h, -⟩
    · revert h; decide
    · revert h; decide
    · exact absurd h (by simp)
  -- nor does a `Zero`
  have hnzero : ur.op ≠ .Zero := fun hm => by
    have hp := evalValueL_panic_op hevr
    rw [hm] at hp
    rcases hp with h | h | ⟨h, -⟩
    · revert h; decide
    · revert h; decide
    · exact absurd h (by simp)
  have hnst2 : ∀ w, st2Lower ur w = false := fun w => by
    cases h : st2Lower ur w
    · rfl
    · rcases st2Lower_cases h with h | h
      · exact absurd (moveQ2Lower_facts h).1 hnmove
      · exact absurd (zero2Lower_facts h).1 hnzero
  obtain ⟨T, hevT, l1, l2, l3, l4, l5, l6, l7, -⟩ := tgt_loop H hE (og := og.toList) (L := preT)
    (M := r :: postT) (P := pre) hog hfrT (by rw [pT1, R.szT]) g3 htyPT g4 hfrG
    (regsFrameL_phis R.framesT pT3) hT1
    (v1_placed H.wg B.bmT B.hgb) (v1_disj H.wg B.bmT B.hgb B.mT) hrelT0 B.ndT B.tpT
    (fun x hx => by
      obtain ⟨hxb, w, hw, hph⟩ := (B.mT x).1 hx
      obtain ⟨hp, -, hid⟩ := placed_in H.wg B.bmT B.hgb hxb hw
      exact ⟨w, hp, hid, hph⟩)
    (sched_args H.wg H.cg B.bmT B.hgb R.treeT B.mT)
    (fun a ha hVS hnf hat hfs => by
      rcases hVS with h | h
      · exfalso
        obtain ⟨hxb, w, hw, -⟩ := (B.mT a).1 ha
        obtain ⟨-, -, -, -, hof', -⟩ := atomL_sched H B ha hw (atomL_of_not_term
          (placed_in H.wg B.bmT B.hgb hxb hw).1 hat) hnf hfs
        exact v1_disj H.wf B.bmS B.hfb B.mS a hof' h
      · exact h)
    (fun x hx w hw ht hnf hfs => by
      obtain ⟨u, hu, -, hs', hxof, -⟩ := atomL_sched H B (hogpre x hx) hw ht hnf hfs
      refine ⟨u, hu, fun hxp => ⟨hargsS x (.inl hxp) u hu, ?_⟩, fun hxp => ?_⟩
      · obtain ⟨u', y, hu', hy, hev⟩ := g6 x hxp
        rw [hu] at hu'; cases hu'
        exact ⟨y, hy, hev⟩
      · have hxr : x ≠ r := fun h => hrpreT (h ▸ hx)
        have hargOp : ∀ o : Op, o.generic = true → w.op = o → u.op = o := fun o ho hwo => by
          rw [atomPair_op_of_generic hs' (by rw [hwo]; exact ho), hwo]
        refine ⟨?_, fun ha => hxp (arg_beforeL H B hof hur hrp hxof hxr hu
            (.inl (hargOp _ (by decide) ha))),
          fun ha => hxp (arg_beforeL H B hof hur hrp hxof hxr hu
            (.inr (hargOp _ (by decide) ha)))⟩
        cases hroot : isRoot w.op
        · rfl
        · exfalso
          have : x ∈ preT.filter (rootAtL tabs f g) := List.mem_filter.2 ⟨hx, by
            simp [rootAtL, rootL, hw, hu, ht, atomPair_root hs' hroot]⟩
          rw [← hfl] at this
          exact hxp (List.mem_filter.1 this).1)
    (fun x hx u w hu hw hq2 => q2_last_og H B (hogpre x hx) hu hw hq2)
    (fun x hx w hw ht hfn => by
      obtain ⟨v, u, wv, A, B', C, hsplit, hB', hu, hpv, hq2, hlast, hroot⟩ :=
        comp_owner H B (hogpre x hx) hw ht hfn
      have hrB : r ∉ B' := fun hm => by
        have := hB' r hm
        rw [hwr] at this
        simp [hwrt] at this
      rcases mem_before hsplit hog B.ndT hx hrB with hv | rfl
      · have : v ∈ preT.filter (rootAtL tabs f g) := List.mem_filter.2 ⟨hv, hroot⟩
        rw [← hfl] at this
        exact ⟨v, u, wv, (List.mem_filter.1 this).1, hu, hpv, hq2, hlast⟩
      · rw [hur] at hu; cases hu
        rw [hnst2] at hq2; cases hq2)
    (fun v hv => by
      obtain ⟨u, y, hu, hy, hev⟩ := g6 v hv
      exact ⟨u, hu, hargsS v (.inl hv) u hu, y, hy, hev⟩)
  -- the root `r` in the target
  have hwrph : wr.op ≠ .Phi := by
    obtain ⟨-, w', hw', hph⟩ := (B.mT r).1 hrog.1
    rw [hwr] at hw'; cases hw'; exact hph
  have hrT := (atom_ref H g4 l4
    (fun a ha => ha.elim (v1_placed H.wg B.bmT B.hgb a) fun hm => by
      obtain ⟨hxb, w, hw, -⟩ := (B.mT a).1 (hogpre a hm)
      exact ⟨w, (placed_in H.wg B.bmT B.hgb hxb hw).1⟩)
    l6 g3 l3 hfrG l7 (frame_trans l1 hfrT) hpwr hur hwrt hurt).2.2 env hE (hargsS r (.inr rfl) ur hur)
    (fun a ha => by
      rcases sched_args H.wg H.cg B.bmT B.hgb R.treeT B.mT r hrog.1 wr hwr a ha with h | h
      · exact .inl h
      · right
        have htop := B.tpT; rw [hog] at htop h
        exact topoRem_before htop (by rw [argsF_of hwr]; exact Array.mem_toList_iff.2 ha) h)
    hwrph fun hq2 => by rw [hnst2] at hq2; cases hq2
  rw [hevr] at hrT
  obtain ⟨m', hT', hm⟩ := res_panic_of_refines hrT
  refine ⟨m', enterBlockL_of hpsT (by rw [schedL_of_block B.hgb B.idT, B.sT]) ?_, hm⟩
  rw [hog, evalAllL_append, hevT]
  show evalAllL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) T (r :: postT) = _
  rw [evalAllL_cons, stepVL_of (by rw [makeL_f]; exact hwr)]
  simp only [hT']

end GoFV.Proof.Low.Sim
