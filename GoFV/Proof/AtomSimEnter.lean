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
        (∀ a ∈ v.args, V a ∨ a ∈ L) ∧ G.regs[x]? = some (some ((evalPure v.op (tabs.ty v.type)
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
theorem src_eval {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
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
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec hnd htp hsz hev
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

end GoFV.Proof.AtomSim
