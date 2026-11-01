import GoFV.Proof.Pass.ECLoop
import GoFV.Proof.Pass.ECTyped

/-!
# Block entries of the conversion simulation (issue #28)

`SimAt frS frT b i`: the source and target frames at the entry of block `b` along edge `i`:
the same activation inputs, every source register refined (through its conversion) by the
target's, the source's lemma (D) for the strict ancestors (`CSE.Pre`), after the entry
block has run, the target's entry values with registers and its new entry values holding
their evaluations (`EntryOK`), and the shapes of the source's registers (`RegsOK`).

`enter_ok`: a block the source enters to `GS` the target enters to some `GT` whose registers
refine the conversions of `GS`'s. `enter_panic` (`ECPanic`): a panic alike.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.AtomSim GoFV.Proof.Order

/-- The entry block has run: its values have registers, its new values their evaluations. -/
def EntryOK (env : Env) (tabs : Tables) (g : Func) (isNew : ID → Bool) (T : Frame) : Prop :=
  (∀ z, EntryVal g z → Reg T z) ∧
    NewCons env (Ctx.make tabs g) isNew T (fun z => EntryVal g z ∧ isNew z = true)

/-- The simulation relation at the entry of block `bid` along edge `i`. -/
structure SimAt (env : Env) (tabs : Tables) (f g : Func) (cv : Cv) (isNew : ID → Bool)
    (frS frT : Frame) (bid : ID) (i : Nat) : Prop where
  frame : frT = { frS with regs := frT.regs }
  szS : frS.regs.size = f.valueTab.size
  szT : frT.regs.size = g.valueTab.size
  img : frT.images.size = (Ctx.make tabs g).params.size
  rel : ∀ x y, frS.regs[x]? = some (some y) →
    ∃ y', frT.regs[x]? = some (some y') ∧ Sem.Refines (cv x y) y'
  listed : ∀ x y, frS.regs[x]? = some (some y) → Listed f x
  pre : CSE.Pre env tabs f #[] frS bid i
  entry : bid = f.entry ∨ EntryOK env tabs g isNew frT
  ok : RegsOK (Ctx.make tabs f) frS

section
variable {tabs : Tables} {f g : Func} {cv : Cv} {isNew : ID → Bool} {front : ID → List ID}
  {RR : List Val → Mem → List Val → Mem → Prop} {ce ce' : CheckEnv}

/-- The facts of the two functions the block lemmas use. -/
structure Hyp (tabs : Tables) (f g : Func) (cv : Cv) (isNew : ID → Bool) (front : ID → List ID)
    (RR : List Val → Mem → List Val → Mem → Prop) (ce ce' : CheckEnv) : Prop where
  rel : CvRel tabs f g cv isNew front RR
  wf : WF ce f
  wg : WF ce' g
  cf : CertOK f
  cg : CertOK g

theorem Hyp.make_eq (H : Hyp tabs f g cv isNew front RR ce ce') : make g = make f :=
  CopyElim.make_eq H.rel.cfg

theorem Hyp.blocks_eq (H : Hyp tabs f g cv isNew front RR ce ce') : g.blocks = f.blocks :=
  CopyElim.cfgView_blocks H.rel.cfg

theorem Hyp.entry_eq (H : Hyp tabs f g cv isNew front RR ce ce') : g.entry = f.entry :=
  CopyElim.cfgView_entry H.rel.cfg

/-- The block of `g` with the ID of a block of `f`, and its `CvBlock`. -/
theorem Hyp.block (H : Hyp tabs f g cv isNew front RR ce ce') {b : ID} (hb : b ∈ f.blocks)
    {fb : Block} (hfb : f.block? b = some fb) :
    ∃ gb, g.block? b = some gb ∧ CvBlock tabs f g cv isNew front RR fb gb := H.rel.block b hb fb hfb

/-- A value listed in `g` that is not new is listed in the same block of `f`. -/
theorem Hyp.common_of_listed (H : Hyp tabs f g cv isNew front RR ce ce') {a : ID} {wa : Value}
    (hp : Placed g a wa) (hn : isNew a = false) :
    ∃ fc, f.block? wa.block = some fc ∧ wa.block ∈ f.blocks ∧ a ∈ fc.values := by
  obtain ⟨-, hbm, gc, hgc, hac⟩ := hp
  have hbm' : wa.block ∈ f.blocks := H.blocks_eq ▸ hbm
  obtain ⟨fc, hfc, -⟩ := H.wf.blockId _ hbm'
  obtain ⟨gc', hgc', B⟩ := H.block hbm' hfc
  rw [hgc] at hgc'; cases hgc'
  refine ⟨fc, hfc, hbm', Classical.byContradiction fun hm => ?_⟩
  rw [B.fresh a hac hm] at hn; cases hn

/-- Every argument of an entry value is an entry value. -/
theorem Hyp.entry_args (H : Hyp tabs f g cv isNew front RR ce ce') {z : ID} (hz : EntryVal g z)
    {w : Value} (hw : g.value? z = some w) : ∀ a ∈ w.args, EntryVal g a := by
  intro a ha
  obtain ⟨eb, heb, hzv⟩ := hz
  have hem := H.wg.entry
  by_cases hph : w.op = .Phi
  · have h1 := H.wg.phiArity _ _ _ _ ⟨⟨hem, heb⟩, hzv, hw⟩ hph
    rw [H.wg.entryPreds eb heb] at h1
    rw [Array.size_eq_zero_iff.1 h1] at ha; simp at ha
  · have ht : ((make g).depthOf g.entry).isSome := by simp [entry_depth H.cg.parents]
    have hu := uses H.cg hem heb ht hzv hw hph ha
    obtain ⟨wa, hpa, hba⟩ := placed_of_listed H.wg (H.wg.argListed _ _ _ _ ⟨⟨hem, heb⟩, hzv, hw⟩ a ha)
    rw [hba] at hu
    have he := anc_of_entry H.cg.parents hu
    obtain ⟨-, -, c, hc, hac⟩ := hpa
    rw [he, heb] at hc; cases hc
    exact ⟨eb, heb, hac⟩

/-- An argument outside the block of a target value has a register at the block's entry. -/
theorem out_arg_reg (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} {frS frT : Frame}
    {b : ID} {i : Nat} (hA : SimAt env tabs f g cv isNew frS frT b i) {fb gb : Block}
    (hfb : f.block? b = some fb) (hgb : g.block? b = some gb)
    (B : CvBlock tabs f g cv isNew front RR fb gb) {x : ID} (hx : x ∈ gb.values) {w : Value}
    (hw : g.value? x = some w) (hph : w.op ≠ .Phi) {a : ID} (ha : a ∈ w.args)
    (hag : a ∉ gb.values) : Reg frT a := by
  have hbt := CSE.pre_tree H.wf H.cf hA.pre
  have hbm' : b ∈ g.blocks := H.blocks_eq ▸ hbt.1
  have htg : ((make g).depthOf b).isSome := by rw [H.make_eq]; exact hbt.2
  obtain ⟨wa, hpa, hba⟩ := placed_of_listed H.wg (H.wg.argListed _ _ _ _ ⟨⟨hbm', hgb⟩, hx, hw⟩ a ha)
  have hu := uses H.cg hbm' hgb htg hx hw hph ha
  rw [hba, H.make_eq] at hu
  have hne : wa.block ≠ b := fun he => by
    obtain ⟨-, -, c, hc, hac⟩ := hpa
    rw [he, hgb] at hc; cases hc; exact hag hac
  cases hn : isNew a with
  | true =>
    rcases B.newArgs x hx w hw a ha hn with h | hE
    · exact absurd h hag
    · rcases hA.entry with he | ⟨hreg, -⟩
      · exfalso
        obtain ⟨eb, heb, hae⟩ := hE
        rw [H.entry_eq, ← he, hgb] at heb; cases heb; exact hag hae
      · exact hreg a hE
  | false =>
    obtain ⟨fc, hfc, hcm, hac⟩ := H.common_of_listed hpa hn
    obtain ⟨ua, hpu, hub, -⟩ := placed_of_mem H.wf hcm hfc hac
    obtain ⟨y, hy, -⟩ := (CSE.pre_strict H.cf hA.pre).1 a ua hpu ⟨hub ▸ hu, hub ▸ hne⟩
    obtain ⟨y', hy', -⟩ := hA.rel a y hy
    exact ⟨y', hy'⟩

end

end GoFV.Proof.EC
