import GoFV.Proof.Pass.CSERel
import GoFV.Proof.Avail

/-!
# cse: what one block's evaluation gives (the statement)

`RepInv f rw fr P`: in frame `fr`, every value placed in a block satisfying `P` holds the register
of its representative. `BlockOK`: entering a tree block, after its `Phi`s (frame `F0`, the same
for source and target) with lemma (D) and `RepInv` for the strict ancestors and `RepInv` for the
block's `Phi`s, the target's evaluation of its schedule ends in the source's frame (and `RepInv`
then holds for all ancestors), or panics alike. Proved in `CSEBlock` (`blockOK`).
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.CopyElim Dom

/-- Values placed in blocks `P` hold their representatives' registers. -/
def RepInv (f : Func) (rw : Array (Option ID)) (fr : Frame) (P : ID → Prop) : Prop :=
  ∀ x v, Placed f x v → P v.block → fr.regs[Opt.CSE.rep rw x]? = fr.regs[x]?

/-- One tree block's evaluation (after its `Phi`s) in source and target. -/
def BlockOK (env : Env) (tabs : Tables) (f g : Func) (rw : Array (Option ID)) : Prop :=
  ∀ (bid : ID) (fb gb : Block) (F0 : Frame) (oS oT : Array ID),
    Tree f bid → f.block? bid = some fb → g.block? bid = some gb →
    F0.regs.size = f.valueTab.size →
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) F0 →
    RepInv f rw F0 (fun a => Anc (make f) a bid ∧ a ≠ bid) →
    (∀ z ∈ fb.values, ∀ v, f.value? z = some v → v.op = .Phi →
      ∃ y, F0.regs[z]? = some (some y)) →
    (∀ z v, Placed f z v → v.block = bid → v.op = .Phi →
      F0.regs[Opt.CSE.rep rw z]? = F0.regs[z]?) →
    schedule f fb = some oS → schedule g gb = some oT →
    oT.toList.filter (Opt.CSE.rootNode f) = oS.toList.filter (Opt.CSE.rootNode f) →
    (∀ G, evalAll env (Ctx.make tabs f) F0 oS.toList = .ok G →
      evalAll env (Ctx.make tabs g) F0 oT.toList = .ok G ∧
        RepInv f rw G (fun a => Anc (make f) a bid)) ∧
    (∀ e m, evalAll env (Ctx.make tabs f) F0 oS.toList = .panic e m →
      evalAll env (Ctx.make tabs g) F0 oT.toList = .panic e m)

end GoFV.Proof.CSE
