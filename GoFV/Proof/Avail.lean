import GoFV.Proof.Eval
import GoFV.Proof.DomRel

/-!
# Lemma (D): available values hold their re-evaluation

In a run of a function that passes `check`, after block `p` has executed, every value placed in
an ancestor of `p` in the (certified) dominator tree is *available*: it has a register, and a
non-`Phi` one evaluates, in the current frame, to its register (`DInv`). This is clifv's lemma
(D) (`docs/contracts/midend.md`, "Pass invariants"); value-moving passes use it to replace a
value by another one that the run holds equal.

`dinv_enter`: entering a tree block `b` with the strict ancestors of `b` available makes all
ancestors of `b` available. `dinv_edge`: after `p`, the strict ancestors of a successor are
available (`Dom.edge`). `dinv_entry`: at the entry nothing is needed. The `_rel` forms hold for
any dominance relation (`Dom.DomRel`: the certified tree or path dominance); the plain forms are
their instances for the certified tree.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom

/-- Value `x` (table entry `v`) is listed in its block `v.block`, a listed block. -/
def Placed (f : Func) (x : ID) (v : Value) : Prop :=
  f.value? x = some v ∧ v.block ∈ f.blocks ∧ ∃ blk, f.block? v.block = some blk ∧ x ∈ blk.values

/-- **Lemma (D)** for the blocks `A`: every value placed in a block of `A` has a register, and
a non-`Phi` one re-evaluates to it. -/
def DInv (env : Env) (ctx : Ctx) (A : ID → Prop) (fr : Frame) : Prop :=
  ∀ x v, Placed ctx.f x v → A v.block →
    ∃ y, fr.regs[x]? = some (some y) ∧ (v.op ≠ .Phi → evalValue env ctx fr v = .ok y)

theorem DInv.mono {env : Env} {ctx : Ctx} {A B : ID → Prop} {fr : Frame}
    (h : DInv env ctx A fr) (hBA : ∀ a, B a → A a) : DInv env ctx B fr :=
  fun x v hx hb => h x v hx (hBA _ hb)

theorem placed_of_mem {ce : CheckEnv} {f : Func} (hwf : WF ce f) {b : ID} {blk : Block}
    (hb : b ∈ f.blocks) (hbb : f.block? b = some blk) {x : ID} (hx : x ∈ blk.values) :
    ∃ v, Placed f x v ∧ v.block = b ∧ v.id = x := by
  obtain ⟨v, hv, hvid, hvb⟩ := hwf.valueId b blk ⟨hb, hbb⟩ x hx
  exact ⟨v, ⟨hv, hvb ▸ hb, blk, hvb ▸ hbb, hx⟩, hvb, hvid⟩

theorem valuesOwn {ce : CheckEnv} {f : Func} (hwf : WF ce f) {b : ID} {blk : Block}
    (hb : b ∈ f.blocks) (hbb : f.block? b = some blk) : ValuesOwn f blk := by
  intro x hx
  obtain ⟨v, hv, hvid, -⟩ := hwf.valueId b blk ⟨hb, hbb⟩ x hx
  exact ⟨v, hv, hvid⟩

/-- The block of a placed value is its block in the sense of `blockOf`. -/
theorem blockOf_placed {f : Func} {x : ID} {v : Value} (h : Placed f x v) :
    blockOf f x = v.block := by
  unfold blockOf; rw [h.1]; rfl

/-- At the entry block no value is a strict dominator's. -/
theorem dinv_entry_rel {env : Env} {ctx : Ctx} {f : Func} {T : ID → Prop} {A : ID → ID → Prop}
    (hD : DomRel f T A) (fr : Frame) : DInv env ctx (fun a => A a f.entry ∧ a ≠ f.entry) fr :=
  fun _ _ _ ⟨ha, hne⟩ => absurd (hD.entry_anc ha) hne

/-- After block `p`, the strict dominators of a successor dominate `p`. -/
theorem dinv_edge_rel {env : Env} {ctx : Ctx} {f : Func} {T : ID → Prop} {A : ID → ID → Prop}
    (hD : DomRel f T A) {fr : Frame} {p : ID} {blk : Block} (hp : p ∈ f.blocks)
    (hb : f.block? p = some blk) (ht : T p) {e : Edge} (he : e ∈ blk.succs)
    (h : DInv env ctx (fun a => A a p) fr) : DInv env ctx (fun a => A a e.b ∧ a ≠ e.b) fr :=
  h.mono fun a ⟨ha, hne⟩ => (hD.edge hp hb ht he).2 a ha hne

/-- **Entering a block preserves lemma (D)**, for any dominance relation. -/
theorem dinv_enter_rel {ce : CheckEnv} {tabs : Tables} {f : Func} {env : Env} {T : ID → Prop}
    {A : ID → ID → Prop} (hwf : WF ce f) (hD : DomRel f T A) {b : ID} {blk : Block}
    (hb : b ∈ f.blocks) (hbb : f.block? b = some blk) {fr fr' : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hup : DInv env (Ctx.make tabs f) (fun a => A a b ∧ a ≠ b) fr)
    (h : enterBlock env (Ctx.make tabs f) fr blk i = .ok fr') :
    DInv env (Ctx.make tabs f) (fun a => A a b) fr' ∧
      fr' = { fr with regs := fr'.regs } ∧ fr'.regs.size = fr.regs.size := by
  have hnd := hwf.valuesNodup b blk ⟨hb, hbb⟩
  have hown := valuesOwn hwf hb hbb
  obtain ⟨b', hb', hid⟩ := hwf.blockId b hb
  rw [hbb] at hb'; cases hb'
  obtain ⟨frP, o, ho, hev, hP, hPs, -, hkeep, hphi⟩ := enterBlock_spec hnd h
  rw [hid, sched_of_block hbb] at ho
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hnd ho
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec ond (by exact otopo) (by rw [hPs, hs]; rfl) hev
  have hcf : (Ctx.make tabs f).f = f := rfl
  rw [hcf] at hkeep hphi e4
  have hfr' : fr' = { fr with regs := fr'.regs } := by rw [e1, hP]
  -- registers outside the block do not change
  have hout : ∀ z, z ∉ blk.values → fr'.regs[z]? = fr.regs[z]? := fun z hz => by
    rw [e3 z (fun hm => hz ((omem z).1 hm).1), hkeep z (.inl hz)]
  refine ⟨fun x v hx hanc => ?_, hfr', by rw [e2, hPs]⟩
  change Placed f x v at hx
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
  · obtain ⟨y, hy, hevy⟩ := hup x v ⟨hv, hvb, blk', hblk', hxv⟩ ⟨hanc, hxb⟩
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
    exact (evalValue_congr hfr' fun a ha => (hout a (hna a ha)).symm).symm

/-- At the entry block no value is a strict ancestor's. -/
theorem dinv_entry {env : Env} {ctx : Ctx} {f : Func} (hc : CertOK f) (fr : Frame) :
    DInv env ctx (fun a => Anc (make f) a f.entry ∧ a ≠ f.entry) fr :=
  dinv_entry_rel hc.domRel fr

/-- After block `p`, the strict ancestors of a successor are ancestors of `p`. -/
theorem dinv_edge {env : Env} {ctx : Ctx} {f : Func} (hc : CertOK f) {fr : Frame} {p : ID}
    {blk : Block} (hp : p ∈ f.blocks) (hb : f.block? p = some blk)
    (ht : ((make f).depthOf p).isSome) {e : Edge} (he : e ∈ blk.succs)
    (h : DInv env ctx (fun a => Anc (make f) a p) fr) :
    DInv env ctx (fun a => Anc (make f) a e.b ∧ a ≠ e.b) fr :=
  dinv_edge_rel hc.domRel hp hb ht he h

/-- **Entering a tree block preserves lemma (D).** -/
theorem dinv_enter {ce : CheckEnv} {tabs : Tables} {f : Func} {env : Env}
    (hwf : WF ce f) (hc : CertOK f) {b : ID} {blk : Block} (hb : b ∈ f.blocks)
    (hbb : f.block? b = some blk) {fr fr' : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hup : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a b ∧ a ≠ b) fr)
    (h : enterBlock env (Ctx.make tabs f) fr blk i = .ok fr') :
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a b) fr' ∧
      fr' = { fr with regs := fr'.regs } ∧ fr'.regs.size = fr.regs.size :=
  dinv_enter_rel hwf hc.domRel hb hbb hs hup h

/-- Setting the `Phi`s keeps the registers typed. -/
theorem typed_phis {ctx : Ctx} {blk : Block} {fr frP : Frame} {i : Nat}
    (ht : Typed ctx fr) (hPs : frP.regs.size = fr.regs.size)
    (hkeep : ∀ z, (z ∉ blk.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi) →
      frP.regs[z]? = fr.regs[z]?)
    (hphi : ∀ z ∈ blk.values, ∀ v, ctx.f.value? z = some v → v.op = .Phi → z < fr.regs.size →
      ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
        frP.regs[z]? = some (some (y.retype (ctx.tys[z]?.getD .other))))
    (hall : ∀ z ∈ blk.values, (ctx.f.value? z).isSome) : Typed ctx frP := by
  intro z y hz
  by_cases hph : z ∈ blk.values ∧ ∃ v, ctx.f.value? z = some v ∧ v.op = .Phi
  · obtain ⟨hzb, v, hv, hp⟩ := hph
    have hlt : z < fr.regs.size := by
      rw [← hPs]
      rcases Nat.lt_or_ge z frP.regs.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hz; cases hz
    obtain ⟨a, y0, -, -, hy⟩ := hphi z hzb v hv hp hlt
    rw [hz] at hy; cases hy
    exact retype_idem _ _
  · have hk : z ∉ blk.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi := by
      by_cases hzb : z ∈ blk.values
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hall z hzb)
        exact .inr ⟨v, hv, fun hp => hph ⟨hzb, v, hv, hp⟩⟩
      · exact .inl hzb
    rw [hkeep z hk] at hz
    exact ht z y hz

/-- Evaluating values with their own IDs keeps the registers typed. -/
theorem typed_evalAll {env : Env} {ctx : Ctx} {o : List ID} {fr fr' : Frame}
    (ht : Typed ctx fr) (hown : ∀ x ∈ o, ∀ v, ctx.f.value? x = some v → v.id = x)
    (e3 : ∀ z, z ∉ o → fr'.regs[z]? = fr.regs[z]?)
    (e4 : ∀ x ∈ o, ∃ v y, ctx.f.value? x = some v ∧ fr'.regs[x]? = some (some y) ∧
      evalValue env ctx fr' v = .ok y) : Typed ctx fr' := by
  intro z y hz
  by_cases hzo : z ∈ o
  · obtain ⟨v, y', hv, hy', hev'⟩ := e4 z hzo
    rw [hz] at hy'; cases hy'
    have := evalValue_typed hev'
    rwa [hown z hzo v hv] at this
  · rw [e3 z hzo] at hz
    exact ht z y hz

/-- **Entering a block keeps every register typed.** -/
theorem typed_enter {ce : CheckEnv} {tabs : Tables} {f : Func} {env : Env} (hwf : WF ce f)
    {b : ID} {blk : Block} (hb : b ∈ f.blocks) (hbb : f.block? b = some blk) {fr fr' : Frame}
    {i : Nat} (hs : fr.regs.size = f.valueTab.size) (ht : Typed (Ctx.make tabs f) fr)
    (h : enterBlock env (Ctx.make tabs f) fr blk i = .ok fr') : Typed (Ctx.make tabs f) fr' := by
  have hnd := hwf.valuesNodup b blk ⟨hb, hbb⟩
  have hown := valuesOwn hwf hb hbb
  obtain ⟨b', hb', hid⟩ := hwf.blockId b hb
  rw [hbb] at hb'; cases hb'
  obtain ⟨frP, o, ho, hev, -, hPs, hall, hkeep, hphi⟩ := enterBlock_spec hnd h
  rw [hid, sched_of_block hbb] at ho
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hnd ho
  obtain ⟨-, -, e3, e4⟩ := evalAll_spec ond (by exact otopo) (by rw [hPs, hs]; rfl) hev
  refine typed_evalAll (typed_phis ht hPs hkeep hphi hall) (fun x hx v hv => ?_) e3 e4
  obtain ⟨v', hv', hvid⟩ := hown x ((omem x).1 hx).1
  change f.value? x = some v at hv
  rw [hv] at hv'; cases hv'; exact hvid

end GoFV.Proof
