import GoFV.Proof.FrameL
import GoFV.Proof.Avail

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lemma (D) over `runL`: available values hold their re-evaluation

`GoFV.Proof.Avail` for the lowered runner (any mode `md`): in a run of a function that passes
`check`, after block `p` has executed, every value placed in an ancestor of `p` in the
dominator tree has a register, and a non-`Phi` one re-evaluates (`evalValueL md`) in the
current frame to it (`DInvL`). `dinvL_enter_rel` / `dinvL_enter`: entering a tree block with the
strict ancestors available makes all its ancestors available; `dinvL_edge`: after `p`, the
strict ancestors of a successor are available; `dinvL_entry`: at the entry nothing is needed.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom

/-- **Lemma (D)** for `runL` and the blocks `A`: every value placed in a block of `A` has a
register, and a non-`Phi` one re-evaluates to it. -/
def DInvL (md : LMode) (env : Env) (ctx : Ctx) (A : ID → Prop) (fr : Frame) : Prop :=
  ∀ x v, Placed ctx.f x v → A v.block →
    ∃ y, fr.regs[x]? = some (some y) ∧ (v.op ≠ .Phi → evalValueL md env ctx fr v = .ok y)

theorem DInvL.mono {md : LMode} {env : Env} {ctx : Ctx} {A B : ID → Prop} {fr : Frame}
    (h : DInvL md env ctx A fr) (hBA : ∀ a, B a → A a) : DInvL md env ctx B fr :=
  fun x v hx hb => h x v hx (hBA _ hb)

/-- At the entry block no value is a strict dominator's. -/
theorem dinvL_entry_rel {md : LMode} {env : Env} {ctx : Ctx} {f : Func} {T : ID → Prop}
    {A : ID → ID → Prop} (hD : DomRel f T A) (fr : Frame) :
    DInvL md env ctx (fun a => A a f.entry ∧ a ≠ f.entry) fr :=
  fun _ _ _ ⟨ha, hne⟩ => absurd (hD.entry_anc ha) hne

/-- After block `p`, the strict dominators of a successor dominate `p`. -/
theorem dinvL_edge_rel {md : LMode} {env : Env} {ctx : Ctx} {f : Func} {T : ID → Prop}
    {A : ID → ID → Prop} (hD : DomRel f T A) {fr : Frame} {p : ID} {blk : Block}
    (hp : p ∈ f.blocks) (hb : f.block? p = some blk) (ht : T p) {e : Edge} (he : e ∈ blk.succs)
    (h : DInvL md env ctx (fun a => A a p) fr) :
    DInvL md env ctx (fun a => A a e.b ∧ a ≠ e.b) fr :=
  h.mono fun a ⟨ha, hne⟩ => (hD.edge hp hb ht he).2 a ha hne

/-- **Entering a lowered block preserves lemma (D)**, for any dominance relation. -/
theorem dinvL_enter_rel {md : LMode} {ce : CheckEnv} {tabs : Tables} {f : Func} {env : Env}
    {T : ID → Prop} {A : ID → ID → Prop} (hwf : WF ce f) (hD : DomRel f T A) {b : ID}
    {blk : Block} (hb : b ∈ f.blocks) (hbb : f.block? b = some blk) {fr fr' : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hup : DInvL md env (Ctx.makeL tabs f) (fun a => A a b ∧ a ≠ b) fr)
    (h : enterBlockL md env (Ctx.makeL tabs f) fr blk i = .ok fr') :
    DInvL md env (Ctx.makeL tabs f) (fun a => A a b) fr' ∧
      fr' = { fr with regs := fr'.regs } ∧ fr'.regs.size = fr.regs.size := by
  have hnd := hwf.valuesNodup b blk ⟨hb, hbb⟩
  have hown := valuesOwn hwf hb hbb
  obtain ⟨b', hb', hid⟩ := hwf.blockId b hb
  rw [hbb] at hb'; cases hb'
  obtain ⟨frP, o, ho, hev, hP, hPs, -, hkeep, hphi⟩ := enterBlockL_spec hnd h
  rw [hid, sched_of_blockL hbb] at ho
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hnd ho
  have hcf : (Ctx.makeL tabs f).f = f := makeL_f tabs f
  obtain ⟨e1, e2, e3, e4⟩ := evalAllL_spec ond (by rw [hcf]; exact otopo)
    (by rw [hPs, hs, hcf]) hev
  rw [hcf] at hkeep hphi e4
  have hfr' : fr' = { fr with regs := fr'.regs } := by rw [e1, hP]
  -- registers outside the block do not change
  have hout : ∀ z, z ∉ blk.values → fr'.regs[z]? = fr.regs[z]? := fun z hz => by
    rw [e3 z (fun hm => hz ((omem z).1 hm).1), hkeep z (.inl hz)]
  refine ⟨fun x v hx hanc => ?_, hfr', by rw [e2, hPs]⟩
  rw [hcf] at hx
  obtain ⟨hv, hvb, blk', hblk', hxv⟩ := hx
  by_cases hxb : v.block = b
  · rw [hxb, hbb] at hblk'; cases hblk'
    by_cases hph : v.op = .Phi
    · have hlt : x < fr.regs.size := hs ▸ lt_of_value? hv
      obtain ⟨a, y, -, -, hy⟩ := hphi x hxv v hv hph hlt
      have hxo : x ∉ o.toList := fun hm => by
        obtain ⟨-, v', hv', hne⟩ := (omem x).1 hm
        rw [hv] at hv'; cases hv'; exact hne hph
      exact ⟨_, by rw [e3 x hxo, hy], fun hne => absurd hph hne⟩
    · obtain ⟨v', y, hv', hy, hev'⟩ := e4 x ((omem x).2 ⟨hxv, v, hv, hph⟩)
      rw [hv] at hv'; cases hv'
      exact ⟨y, hy, fun _ => hev'⟩
  · obtain ⟨y, hy, hevy⟩ := hup x v (by rw [hcf]; exact ⟨hv, hvb, blk', hblk', hxv⟩) ⟨hanc, hxb⟩
    have hxn : x ∉ blk.values := fun hm => by
      obtain ⟨v', hv', -, hvb'⟩ := hwf.valueId b blk ⟨hb, hbb⟩ x hm
      rw [hv] at hv'; cases hv'; exact hxb hvb'
    refine ⟨y, by rw [hout x hxn, hy], fun hne => ?_⟩
    have hna : ∀ a ∈ v.args, a ∉ blk.values := fun a ha hm => by
      have hua := hD.uses hvb hblk' (hD.left hanc) hxv hv hne ha
      obtain ⟨va, hva, -, hvab⟩ := hwf.valueId b blk ⟨hb, hbb⟩ a hm
      have hba : blockOf f a = b := by unfold blockOf; rw [hva]; exact hvab
      rw [hba] at hua
      exact hxb (hD.antisymm hanc hua)
    rw [← hevy hne]
    exact (evalValueL_congr hfr' fun a ha => (hout a (hna a ha)).symm).symm

/-- At the entry block no value is a strict ancestor's. -/
theorem dinvL_entry {md : LMode} {env : Env} {ctx : Ctx} {f : Func} (hc : CertOK f)
    (fr : Frame) : DInvL md env ctx (fun a => Anc (make f) a f.entry ∧ a ≠ f.entry) fr :=
  dinvL_entry_rel hc.domRel fr

/-- After block `p`, the strict ancestors of a successor are ancestors of `p`. -/
theorem dinvL_edge {md : LMode} {env : Env} {ctx : Ctx} {f : Func} (hc : CertOK f) {fr : Frame}
    {p : ID} {blk : Block} (hp : p ∈ f.blocks) (hb : f.block? p = some blk)
    (ht : ((make f).depthOf p).isSome) {e : Edge} (he : e ∈ blk.succs)
    (h : DInvL md env ctx (fun a => Anc (make f) a p) fr) :
    DInvL md env ctx (fun a => Anc (make f) a e.b ∧ a ≠ e.b) fr :=
  dinvL_edge_rel hc.domRel hp hb ht he h

/-- **Entering a tree block preserves lemma (D)** (`runL`). -/
theorem dinvL_enter {md : LMode} {ce : CheckEnv} {tabs : Tables} {f : Func} {env : Env}
    (hwf : WF ce f) (hc : CertOK f) {b : ID} {blk : Block} (hb : b ∈ f.blocks)
    (hbb : f.block? b = some blk) {fr fr' : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hup : DInvL md env (Ctx.makeL tabs f) (fun a => Anc (make f) a b ∧ a ≠ b) fr)
    (h : enterBlockL md env (Ctx.makeL tabs f) fr blk i = .ok fr') :
    DInvL md env (Ctx.makeL tabs f) (fun a => Anc (make f) a b) fr' ∧
      fr' = { fr with regs := fr'.regs } ∧ fr'.regs.size = fr.regs.size :=
  dinvL_enter_rel hwf hc.domRel hb hbb hs hup h

end GoFV.Proof
