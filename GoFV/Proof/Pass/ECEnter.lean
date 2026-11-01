import GoFV.Proof.Pass.ECLoop
import GoFV.Proof.Pass.ECTyped

/-!
# Block entries of the conversion simulation (issue #28)

`SimAt frS frT b i`: the source and target frames at the entry of block `b` along edge `i`:
the same activation inputs, every source register refined (through its conversion) by the
target's, the source's lemma (D) for the strict ancestors (`CSE.Pre`) and the target's
(`dinvT`), and the shapes of the source's registers (`RegsOK`).

`enter_ok`: a block the source enters to `GS` the target enters to some `GT` whose registers
refine the conversions of `GS`'s. `enter_panic` (`ECPanic`): a panic alike.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.AtomSim GoFV.Proof.Order

/-- The simulation relation at the entry of block `bid` along edge `i`. -/
structure SimAt (env : Env) (tabs : Tables) (f g : Func) (cv : Cv)
    (frS frT : Frame) (bid : ID) (i : Nat) : Prop where
  frame : frT = { frS with regs := frT.regs }
  szS : frS.regs.size = f.valueTab.size
  szT : frT.regs.size = g.valueTab.size
  img : frT.images.size = (Ctx.make tabs g).params.size
  rel : ∀ x y, frS.regs[x]? = some (some y) →
    ∃ y', frT.regs[x]? = some (some y') ∧ Sem.Refines (cv x y) y'
  listed : ∀ x y, frS.regs[x]? = some (some y) → Listed f x
  pre : CSE.Pre env tabs f #[] frS bid i
  dinvT : DInv env (Ctx.make tabs g) (fun a => Anc (make g) a bid ∧ a ≠ bid) frT
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

/-- An argument outside the block of a target value has a register at the block's entry: it is
placed in a strict dominator (lemma (D) on the target, `SimAt.dinvT`). -/
theorem out_arg_reg (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} {frS frT : Frame}
    {b : ID} {i : Nat} (hA : SimAt env tabs f g cv frS frT b i) {gb : Block}
    (hgb : g.block? b = some gb) {x : ID} (hx : x ∈ gb.values) {w : Value}
    (hw : g.value? x = some w) (hph : w.op ≠ .Phi) {a : ID} (ha : a ∈ w.args)
    (hag : a ∉ gb.values) : Reg frT a := by
  have hbt := CSE.pre_tree H.wf H.cf hA.pre
  have hbm' : b ∈ g.blocks := H.blocks_eq ▸ hbt.1
  have htg : ((make g).depthOf b).isSome := by rw [H.make_eq]; exact hbt.2
  obtain ⟨wa, hpa, hba⟩ := placed_of_listed H.wg (H.wg.argListed _ _ _ _ ⟨⟨hbm', hgb⟩, hx, hw⟩ a ha)
  have hu := uses H.cg hbm' hgb htg hx hw hph ha
  rw [hba] at hu
  have hne : wa.block ≠ b := fun he => by
    obtain ⟨-, -, c, hc, hac⟩ := hpa
    rw [he, hgb] at hc; cases hc; exact hag hac
  obtain ⟨y, hy, -⟩ := hA.dinvT a wa hpa ⟨hu, hne⟩
  exact ⟨y, hy⟩

end

end GoFV.Proof.EC
