import GoFV.Proof.AtomSimBlock

/-!
# Value sets along a block of the atom simulation (issue #113)

In a tree block `b` of a checked function: the values of strict ancestors and the block's
`Phi`s (`V1`) after the `Phi`s are set (`denOK_phis`); the arguments of the scheduled values,
the controls and, for a successor, its strict ancestors' values and its `Phi` arguments lie in
`V1` or the schedule (`sched_args`, `ctrl_in`, `next_sets`); the source's schedule prefix
(`src_eval`).
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.Dom GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-- Placed in a strict ancestor of `b` or a `Phi` of `hb`. -/
def V1 (h : Func) (b : ID) (hb : Block) (x : ID) : Prop := SAnc h b x ∨ PhiOf h hb x

section
variable {ce : CheckEnv} {h : Func} (hwf : WF ce h) (hc : CertOK h) {b : ID} {hb : Block}
  (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb)
include hwf hbm hbb

theorem sanc_not_mem {x : ID} (hx : SAnc h b x) : x ∉ hb.values := by
  obtain ⟨v, hp, -, hne⟩ := hx
  exact not_mem_of_placed hwf hp hbm hbb hne

omit hwf hbm in
/-- A value placed in an ancestor of `b` is in `V1` or the block's schedule. -/
theorem anc_in {o : Array ID}
    (hmem : ∀ x, x ∈ o.toList ↔ x ∈ hb.values ∧ ∃ v, h.value? x = some v ∧ v.op ≠ .Phi)
    {x : ID} {v : Value} (hp : Placed h x v) (ha : Anc (make h) v.block b) :
    V1 h b hb x ∨ x ∈ o.toList := by
  by_cases hvb : v.block = b
  · have hx : x ∈ hb.values := by
      obtain ⟨-, -, blk, hblk, hx⟩ := hp
      rw [hvb, hbb] at hblk; cases hblk; exact hx
    by_cases hph : v.op = .Phi
    · exact .inl (.inr ⟨hx, v, hp.1, hph⟩)
    · exact .inr ((hmem x).2 ⟨hx, v, hp.1, hph⟩)
  · exact .inl (.inl ⟨v, hp, ha, hvb⟩)

include hc in
/-- The arguments of a scheduled value are in `V1` or the schedule. -/
theorem sched_args (ht : ((make h).depthOf b).isSome) {o : Array ID}
    (hmem : ∀ x, x ∈ o.toList ↔ x ∈ hb.values ∧ ∃ v, h.value? x = some v ∧ v.op ≠ .Phi) :
    ∀ x ∈ o.toList, ∀ v, h.value? x = some v → ∀ a ∈ v.args, V1 h b hb a ∨ a ∈ o.toList := by
  intro x hx v hv a ha
  obtain ⟨hxb, v', hv', hph⟩ := (hmem x).1 hx
  rw [hv] at hv'; cases hv'
  obtain ⟨hp, hvb, -⟩ := placed_in hwf hbm hbb hxb hv
  obtain ⟨va, hpa, hanc⟩ := arg_anc hwf hc hp (hvb ▸ ht) hph ha
  exact anc_in hbb hmem hpa (hvb ▸ hanc)

include hc in
/-- The controls are in `V1` or the schedule. -/
theorem ctrl_in (ht : ((make h).depthOf b).isSome) {o : Array ID}
    (hmem : ∀ x, x ∈ o.toList ↔ x ∈ hb.values ∧ ∃ v, h.value? x = some v ∧ v.op ≠ .Phi)
    {x : ID} (hx : x ∈ hb.controls) : (V1 h b hb x ∨ x ∈ o.toList) ∧ ∃ v, Placed h x v := by
  have hu := ctrlUse hc hbm hbb ht hx
  obtain ⟨v, hp, hbo⟩ := placed_of_listed hwf (hwf.ctrlListed b hb ⟨hbm, hbb⟩ x hx)
  rw [hbo] at hu
  exact ⟨anc_in hbb hmem hp hu, v, hp⟩

include hc in
/-- At a successor: its strict ancestors' values and its `Phi` arguments along the edge. -/
theorem next_sets (ht : ((make h).depthOf b).isSome) {o : Array ID}
    (hmem : ∀ x, x ∈ o.toList ↔ x ∈ hb.values ∧ ∃ v, h.value? x = some v ∧ v.op ≠ .Phi)
    {e : Edge} (he : e ∈ hb.succs) :
    (∀ x, SAnc h e.b x → V1 h b hb x ∨ x ∈ o.toList) ∧
      PhiArgs h e.b e.i (fun x => V1 h b hb x ∨ x ∈ o.toList) ∧
      ((make h).depthOf e.b).isSome ∧ e.b ∈ h.blocks := by
  obtain ⟨-, het, hup⟩ := edge hc hbm hbb ht he
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
  obtain ⟨hebm, c, hcb, hcp⟩ := hwf.succLink b hb ⟨hbm, hbb⟩ j e hj
  refine ⟨fun x ⟨v, hp, hanc, hne⟩ => ?_, fun c' hc' z hz v hv hph a ha => ?_, het, hebm⟩
  · exact anc_in hbb hmem hp (Anc.trans hc.parents (hanc.up hc.parents hne) hup)
  · rw [hcb] at hc'; cases hc'
    have hu := phiUse hc hebm hcb het hz hv hph ha hcp ht
    obtain ⟨va, hpa, hbo⟩ := placed_of_listed hwf
      (hwf.argListed _ _ _ _ ⟨⟨hebm, hcb⟩, hz, hv⟩ a (Array.mem_of_getElem? ha))
    rw [hbo] at hu
    exact anc_in hbb hmem hpa hu

/-- **`DenOK` after the `Phi`s.** -/
theorem denOK_phis {D : ID → Option Value} {tabs : Tables} {ctx : Ctx} (hctx : ctx.f = h)
    {fr : Frame} {V : ID → Prop} {i : Nat} {ps : List (ID × Val)}
    (hD : DenOK D tabs fr V) (hsub : ∀ x, SAnc h b x → V x) (hcl : Closed D (SAnc h b))
    (hnt : ∀ x v, h.value? x = some v → v.op = .Phi → ¬ IsTerm D x)
    (hsz : fr.regs.size = h.valueTab.size)
    (hps : hb.values.toList.filterMapM (phiStep ctx fr i) = .ok ps) :
    DenOK D tabs { fr with regs := setPhis ps fr.regs } (V1 h b hb) := by
  obtain ⟨-, -, hkeep, hphi⟩ := phis_spec (hwf.valuesNodup b hb ⟨hbm, hbb⟩) hps
  rw [hctx] at hkeep hphi
  refine ((hD.restrict hsub hcl).frame (fr' := { fr with regs := setPhis ps fr.regs })
    (fun a ha => hkeep a (.inl (sanc_not_mem hwf hbm hbb ha)))).extend (W := PhiOf h hb)
    (fun _ _ => rfl) fun x ⟨hx, v, hv, hph⟩ _ => ⟨hnt x v hv hph, ?_⟩
  obtain ⟨a, y, -, -, hset⟩ := hphi x hx v hv hph (by rw [hsz]; exact lt_of_value? hv)
  exact ⟨_, hset⟩

include hc in
/-- **`MemDefs` after the `Phi`s**: the strict ancestors' memory roots keep their registers and
arguments (`Phi`s are no memory roots). -/
theorem memDefs_phis {tabs : Tables} {ctx : Ctx} (hctx : ctx.f = h)
    {fr : Frame} {V : ID → Prop} {i : Nat} {ps : List (ID × Val)}
    (hM : MemDefs h.value? tabs fr V) (hsub : ∀ x, SAnc h b x → V x)
    (hps : hb.values.toList.filterMapM (phiStep ctx fr i) = .ok ps) :
    MemDefs h.value? tabs { fr with regs := setPhis ps fr.regs } (V1 h b hb) := by
  obtain ⟨-, -, hkeep, -⟩ := phis_spec (hwf.valuesNodup b hb ⟨hbm, hbb⟩) hps
  rw [hctx] at hkeep
  have hcl : ∀ x, SAnc h b x → ∀ v, h.value? x = some v → memOp v.op = true →
      ∀ c ∈ v.args, SAnc h b c := by
    intro x ⟨v, hp, hanc, hne⟩ w hw hm c hc'
    rw [hp.1] at hw; cases hw
    have hphi : v.op ≠ .Phi := fun he => by rw [he] at hm; cases hm
    obtain ⟨va, hpa, hanc'⟩ := arg_anc hwf hc hp (Anc.left hc.parents hanc) hphi hc'
    refine ⟨va, hpa, Anc.trans hc.parents hanc' hanc, fun he => ?_⟩
    rw [he] at hanc'
    exact hne (Anc.antisymm hc.parents hanc hanc')
  refine (((hM.restrict hsub hcl).frame (fr' := { fr with regs := setPhis ps fr.regs })
    (fun a ha => hkeep a (.inl (sanc_not_mem hwf hbm hbb ha)))).union (W := PhiOf h hb)
    fun x ⟨_, v, hv, hph⟩ _ w hw hm => ?_).iff fun _ => Iff.rfl
  rw [hv] at hw; cases hw; rw [hph] at hm; cases hm

include hc in
/-- **`RDefs` after the `Phi`s**: the strict ancestors' non-`Phi` atoms keep their registers and
arguments. -/
theorem rDefs_phis {ctx : Ctx} (hctx : ctx.f = h)
    {R : Value → List Val → Val → Prop} {fr : Frame} {V : ID → Prop} {i : Nat}
    {ps : List (ID × Val)} (hM : RDefs R h.value? fr V) (hsub : ∀ x, SAnc h b x → V x)
    (hps : hb.values.toList.filterMapM (phiStep ctx fr i) = .ok ps) :
    RDefs R h.value? { fr with regs := setPhis ps fr.regs } (V1 h b hb) := by
  obtain ⟨-, -, hkeep, -⟩ := phis_spec (hwf.valuesNodup b hb ⟨hbm, hbb⟩) hps
  rw [hctx] at hkeep
  have hcl : ∀ x, SAnc h b x → ∀ v, h.value? x = some v → termOp v.op = false → v.op ≠ .Phi →
      ∀ c ∈ v.args, SAnc h b c := by
    intro x ⟨v, hp, hanc, hne⟩ w hw _ hphi c hc'
    rw [hp.1] at hw; cases hw
    obtain ⟨va, hpa, hanc'⟩ := arg_anc hwf hc hp (Anc.left hc.parents hanc) hphi hc'
    refine ⟨va, hpa, Anc.trans hc.parents hanc' hanc, fun he => ?_⟩
    rw [he] at hanc'
    exact hne (Anc.antisymm hc.parents hanc hanc')
  refine (((hM.restrict hsub hcl).frame (fr' := { fr with regs := setPhis ps fr.regs })
    (fun a ha => hkeep a (.inl (sanc_not_mem hwf hbm hbb ha)))).union (W := PhiOf h hb)
    fun x ⟨_, v, hv, hph⟩ _ w hw _ hp => ?_).iff fun _ => Iff.rfl
  rw [hv] at hw; cases hw; exact absurd hph hp

end

theorem phi_not_term_f {f : Func} : ∀ x v, f.value? x = some v → v.op = .Phi → ¬ IsTerm f.value? x :=
  fun x v hv hph ⟨v', hv', ht⟩ => by
    rw [hv] at hv'; cases hv'; rw [hph, termOp_phi] at ht; cases ht

theorem phi_not_term_g {g : Func} :
    ∀ x v, g.value? x = some v → v.op = .Phi → ¬ IsTerm (listedDefs g) x :=
  fun x v hv hph ⟨v', hv', ht⟩ => by
    rw [(listed_placed hv').1] at hv; cases hv; rw [hph, termOp_phi] at ht; cases ht

/-! ## The source's schedule prefix -/

theorem termsOK_of_topo {f : Func} {tabs : Tables} {G : Frame} :
    ∀ {L : List ID} {V : ID → Prop}, TopoRem (argsF f) L → (∀ x ∈ L, Reg G x) →
      (∀ x ∈ L, ∀ v, f.value? x = some v → termOp v.op = true →
        (∀ a ∈ v.args, V a ∨ a ∈ L) ∧ G.regs[x]? = some (some ((GoFV.Proof.Rules.opVal tabs v.op (tabs.ty v.type)
          v.auxInt v.aux (v.args.toList.map (rv G))).retype (tabs.ty v.type)))) →
      TermsOK f.value? tabs G V L
  | [], _, _, _, _ => trivial
  | x :: s, V, ⟨ht1, ht2⟩, hreg, hterm => by
    refine ⟨hreg x List.mem_cons_self, fun v hv hop => ?_, termsOK_of_topo ht2
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

/-- **The source's schedule prefix `P`**, from the frame after the `Phi`s. -/
theorem src_eval {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {env : Env} {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData f g b fb gb of og)
    (htree : ((make f).depthOf b).isSome) {frP G : Frame} {P Q : List ID}
    (hPQ : of.toList = P ++ Q) (hD : DenOK f.value? tabs frP (V1 f b fb))
    (hsz : frP.regs.size = f.valueTab.size) (hty : Proof.Typed (Ctx.make tabs f) frP)
    (hev : evalAll env (Ctx.make tabs f) frP P = .ok G) :
    G = { frP with regs := G.regs } ∧ G.regs.size = frP.regs.size ∧
      Proof.Typed (Ctx.make tabs f) G ∧ DenOK f.value? tabs G (fun a => V1 f b fb a ∨ a ∈ P) ∧
      (∀ z, z ∉ P → G.regs[z]? = frP.regs[z]?) ∧
      (∀ x ∈ P, ∃ u y, f.value? x = some u ∧ G.regs[x]? = some (some y) ∧
        evalValue env (Ctx.make tabs f) G u = .ok y) := by
  have hnd : P.Nodup := (List.nodup_append.1 (hPQ ▸ B.ndS)).1
  have htp : TopoRem (argsF f) P := topoRem_prefix (hPQ ▸ B.tpS)
  have hPof : ∀ x ∈ P, x ∈ of.toList := fun x hx => by rw [hPQ]; exact List.mem_append_left _ hx
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec hnd (by exact htp) hsz hev
  have hown : ∀ x ∈ P, ∀ v, f.value? x = some v → v.id = x ∧ v.op ≠ .Phi ∧ x ∈ fb.values :=
    fun x hx v hv => by
      obtain ⟨hxb, v', hv', hph⟩ := (B.mS x).1 (hPof x hx)
      rw [hv] at hv'; cases hv'
      exact ⟨(placed_in H.wf B.bmS B.hfb hxb hv).2.2, hph, hxb⟩
  have hdisj : ∀ x, V1 f b fb x → x ∉ P := fun x hV hx => by
    obtain ⟨hxb, v, hv, hph⟩ := (B.mS x).1 (hPof x hx)
    rcases hV with h | ⟨-, v', hv', hph'⟩
    · exact sanc_not_mem H.wf B.bmS B.hfb h hxb
    · rw [hv] at hv'; cases hv'; exact hph hph'
  refine ⟨e1, e2, typed_evalAll hty (fun x hx v hv => (hown x hx v hv).1) e3 e4,
    denOK_terms (hD.frame fun a ha => e3 a (hdisj a ha)) ?_, e3, e4⟩
  have hargs := sched_args H.wf H.cf B.bmS B.hfb htree B.mS
  refine termsOK_of_topo htp (fun x hx => ?_) fun x hx v hv hop => ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨v, y, -, hy, -⟩ := e4 x hx; exact ⟨y, hy⟩
  · rcases hargs x (hPof x hx) v hv a ha with h | h
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
  · obtain ⟨v', y, hv', hy, hevy⟩ := e4 x hx
    change f.value? x = some v' at hv'
    rw [hv] at hv'; cases hv'
    rw [hy, evalValue_term hop hevy, (hown x hx v hv).1, tys_of_value hv]; rfl

/-- The arguments of the values of a prefix `P` of the source's schedule are in `V1` or `P`. -/
theorem src_args {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f}
    (H : Hyp tabs f g ce ce' I) {b : ID} {fb gb : Block} {of og : Array ID}
    (B : BlockData f g b fb gb of og) (htree : ((make f).depthOf b).isSome) {P Q : List ID}
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

/-- **`MemDefs` along the source's schedule prefix `P`**: each memory root evaluated holds the
write of its arguments' registers (`evalValue_memOp`), which are evaluated before it. -/
theorem src_eval_mem {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f}
    (H : Hyp tabs f g ce ce' I)
    {env : Env} {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData f g b fb gb of og)
    (htree : ((make f).depthOf b).isSome) {frP G : Frame} {P Q : List ID}
    (hPQ : of.toList = P ++ Q) (hD : DenOK f.value? tabs frP (V1 f b fb))
    (hM : MemDefs f.value? tabs frP (V1 f b fb))
    (hsz : frP.regs.size = f.valueTab.size) (hty : Proof.Typed (Ctx.make tabs f) frP)
    (hev : evalAll env (Ctx.make tabs f) frP P = .ok G) :
    MemDefs f.value? tabs G (fun a => V1 f b fb a ∨ a ∈ P) := by
  obtain ⟨-, -, -, -, e3, e4⟩ := src_eval H B htree hPQ hD hsz hty hev
  have hPof : ∀ x ∈ P, x ∈ of.toList := fun x hx => by rw [hPQ]; exact List.mem_append_left _ hx
  have hdisj : ∀ x, V1 f b fb x → x ∉ P := fun x hV hx => by
    obtain ⟨hxb, v, hv, hph⟩ := (B.mS x).1 (hPof x hx)
    rcases hV with h | ⟨-, v', hv', hph'⟩
    · exact sanc_not_mem H.wf B.bmS B.hfb h hxb
    · rw [hv] at hv'; cases hv'; exact hph hph'
  refine (hM.frame fun a ha => e3 a (hdisj a ha)).union fun x hx _ v hv hm => ?_
  obtain ⟨v', y, hv', hy, hevy⟩ := e4 x hx
  change f.value? x = some v' at hv'
  rw [hv] at hv'; cases hv'
  obtain ⟨hxb, v', hv', -⟩ := (B.mS x).1 (hPof x hx)
  rw [hv] at hv'; cases hv'
  have hid : v.id = x := (placed_in H.wf B.bmS B.hfb hxb hv).2.2
  obtain ⟨r, hr, rfl⟩ := evalValue_memOp rfl hm hevy
  refine ⟨src_args H B htree hPQ x hx v hv, r, hr, ?_⟩
  rw [rv_of hy, hid, tys_shape]

/-- **`RDefs` along the source's schedule prefix `P`**: each non-`Phi` atom evaluated is related
to its arguments' registers (`SrcInv.rstep`), which are evaluated before it. -/
theorem src_eval_rdefs {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f}
    (H : Hyp tabs f g ce ce' I)
    {env : Env} {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData f g b fb gb of og)
    (htree : ((make f).depthOf b).isSome) {frP G : Frame} {P Q : List ID}
    (hPQ : of.toList = P ++ Q) (hD : DenOK f.value? tabs frP (V1 f b fb))
    (hM : RDefs I.R f.value? frP (V1 f b fb)) (hE : I.E env frP.mem0 frP.images)
    (hsz : frP.regs.size = f.valueTab.size) (hty : Proof.Typed (Ctx.make tabs f) frP)
    (hev : evalAll env (Ctx.make tabs f) frP P = .ok G) :
    RDefs I.R f.value? G (fun a => V1 f b fb a ∨ a ∈ P) := by
  obtain ⟨e1, -, -, -, e3, e4⟩ := src_eval H B htree hPQ hD hsz hty hev
  have hPof : ∀ x ∈ P, x ∈ of.toList := fun x hx => by rw [hPQ]; exact List.mem_append_left _ hx
  have hdisj : ∀ x, V1 f b fb x → x ∉ P := fun x hV hx => by
    obtain ⟨hxb, v, hv, hph⟩ := (B.mS x).1 (hPof x hx)
    rcases hV with h | ⟨-, v', hv', hph'⟩
    · exact sanc_not_mem H.wf B.bmS B.hfb h hxb
    · rw [hv] at hv'; cases hv'; exact hph hph'
  refine (hM.frame fun a ha => e3 a (hdisj a ha)).union fun x hx _ v hv ht hp => ?_
  obtain ⟨v', y, hv', hy, hevy⟩ := e4 x hx
  change f.value? x = some v' at hv'
  rw [hv] at hv'; cases hv'
  obtain ⟨hxb, v', hv', -⟩ := (B.mS x).1 (hPof x hx)
  rw [hv] at hv'; cases hv'
  have hid : v.id = x := (placed_in H.wf B.bmS B.hfb hxb hv).2.2
  have hEG : I.E env G.mem0 G.images := by rw [e1]; exact hE
  refine ⟨src_args H B htree hPQ x hx v hv, ?_⟩
  rw [rv_of hy]
  exact I.rstep x v hv hid ht hp env G hEG y hevy

/-! ## The source-side invariant along a block entry -/

theorem rv_set {T : Frame} {x a : ID} {y : Val} :
    rv (T.set x y) a = if x = a ∧ x < T.regs.size then y else rv T a := by
  by_cases h : x = a
  · subst h
    by_cases hlt : x < T.regs.size
    · simp only [hlt, and_self, ite_true]; unfold rv; rw [Frame.set_regs_self hlt]; rfl
    · simp only [hlt, and_false, ite_false]
      unfold rv
      simp [Frame.set, Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
  · simp only [h, false_and, ite_false]; unfold rv; rw [Frame.set_regs_ne h]

/-- The `Phi`s keep the invariant. -/
theorem inv_phis {tabs : Tables} {f : Func} {I : SrcInv tabs f} {fr : Frame} {b : ID} {i : Nat}
    {fb : Block} (hfb : f.block? b = some fb) (hnd : fb.values.toList.Nodup)
    {ps : List (ID × Val)} (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps)
    (hsz : fr.regs.size = f.valueTab.size)
    (hinv : ∀ a, I.P b a (rv fr a)) (hph : PhisP tabs f I.P fr b i) :
    ∀ a, I.P b a (rv { fr with regs := setPhis ps fr.regs } a) := by
  obtain ⟨-, p2, p3, p4⟩ := phis_spec hnd hps
  have hkeep : ∀ z, (z ∉ fb.values ∨ ∃ v, f.value? z = some v ∧ v.op ≠ .Phi) →
      rv { fr with regs := setPhis ps fr.regs } z = rv fr z := fun z hz => by
    unfold rv; exact congrArg (fun o => (Option.join o).getD .poison) (p3 z hz)
  intro z
  by_cases hz : z ∈ fb.values
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (p2 z hz)
    by_cases hop : v.op = .Phi
    · obtain ⟨a, y, ha, hy, hset⟩ := p4 z hz v hv hop (by rw [hsz]; exact lt_of_value? hv)
      have h := hph fb hfb z hz v hv hop a ha
      rw [rv_of hy, ← Option.getD_some (a := tabs.ty v.type) (b := Sem.Ty.other),
        ← tys_of_value hv] at h
      rwa [rv_of hset]
    · rw [hkeep z (.inr ⟨v, hv, hop⟩)]; exact hinv z
  · rw [hkeep z (.inl hz)]; exact hinv z

/-- Evaluating values of block `b` keeps the invariants. -/
theorem inv_evalAll {tabs : Tables} {f : Func} {I : SrcInv tabs f} {env : Env} {b : ID} {fb : Block}
    (hb : b ∈ f.blocks) (hfb : f.block? b = some fb) :
    ∀ {L : List ID} {fr G : Frame}, I.E env fr.mem0 fr.images →
      (∀ x ∈ L, ∀ v, f.value? x = some v → v.id = x ∧ v.op ≠ .Phi ∧ x ∈ fb.values) →
      evalAll env (Ctx.make tabs f) fr L = .ok G →
      (∀ a, I.P b a (rv fr a)) → I.Q b (rv fr) → (∀ a, I.P b a (rv G a)) ∧ I.Q b (rv G)
  | [], _, _, _, _, h, hinv, hq => by cases h; exact ⟨hinv, hq⟩
  | x :: L, fr, G, hEI, hL, h, hinv, hq => by
    rw [evalAll_cons] at h
    unfold stepV at h
    change (match (match f.value? x with
      | none => Res.stuck s!"v{x} is not in the function"
      | some v => evalValue env (Ctx.make tabs f) fr v) with
      | .ok y => evalAll env (Ctx.make tabs f) (fr.set x y) L
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg) = .ok G at h
    cases hv : f.value? x with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h; dsimp only at h
      obtain ⟨hid, hph, hxb⟩ := hL x List.mem_cons_self v hv
      cases he : evalValue env (Ctx.make tabs f) fr v with
      | panic e m => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h
      | ok y =>
        rw [he] at h
        have hty : (Ctx.make tabs f).tys[v.id]?.getD .other = tabs.ty v.type := by
          rw [hid, tys_of_value hv]; rfl
        have hy : I.P b x y := by
          cases ht : termOp v.op with
          | true =>
            rw [evalValue_term ht he, hty]
            exact I.term b fb hfb x hxb v hv ht (rv fr) fun a _ => hinv a
          | false =>
            have := evalValue_typed he
            rw [hty] at this
            rw [← this]; exact I.atom b fb hfb x hxb v hv ht hph y
        refine inv_evalAll hb hfb (fr := fr.set x y) hEI (fun z hz => hL z (List.mem_cons_of_mem _ hz)) h
          (fun a => ?_)
          (I.qstep b fb hb hfb x hxb v hv hid hph env fr hEI y he hinv hq)
        rw [rv_set]
        split
        · next hh => obtain ⟨rfl, -⟩ := hh; exact hy
        · exact hinv a

/-- The source schedule's values are own non-`Phi` values of the block. -/
theorem sched_own {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f}
    (H : Hyp tabs f g ce ce' I) {b : ID} {fb gb : Block} {of og : Array ID}
    (B : BlockData f g b fb gb of og) :
    ∀ x ∈ of.toList, ∀ v, f.value? x = some v → v.id = x ∧ v.op ≠ .Phi ∧ x ∈ fb.values :=
  fun x hx v hv => by
    obtain ⟨hxb, v', hv', hph⟩ := (B.mS x).1 hx
    rw [hv] at hv'; cases hv'
    exact ⟨(placed_in H.wf B.bmS B.hfb hxb hv).2.2, hph, hxb⟩

end GoFV.Proof.AtomSim
