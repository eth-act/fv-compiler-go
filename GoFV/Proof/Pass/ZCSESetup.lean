import GoFV.Proof.Pass.ZCSERel
import GoFV.Proof.Pass.CopyElimSim

/-!
# zcse: what the simulation uses

`Setup tabs f g`: both functions are well-formed, `f`'s dominator certificate holds, `g` is
related to `f` by `ZRel`, and the side-effecting roots of `f`'s tree blocks are pairwise
dependency-ordered (`Chained`, the `chained` half of copyelim's `SimFrag`). Consequences: the
target block of every block of `f`, and its schedule nodes (`nodeT`: the source's, less the
argument-free values of `g`'s entry, which are nodes of the entry only).
-/

namespace GoFV.Proof.ZCSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ZCSE Dom

/-- The side-effecting roots (priority 2) of every tree block of `f` are pairwise ordered by
dependency (`SimFrag.chained`). -/
def Chained (f : Func) : Prop :=
  ∀ bid ∈ f.blocks, ((make f).depthOf bid).isSome → ∀ fb, f.block? bid = some fb →
    ∀ x y, NodeIn (schedNodes f fb).toList x → NodeIn (schedNodes f fb).toList y →
      ¬ NilIn (schedNodes f fb).toList x → ¬ NilIn (schedNodes f fb).toList y → x ≠ y →
      Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) x y ∨
      Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) y x

/-- Everything the simulation uses about zcse's input `f` and output `g`. -/
structure Setup (tabs : Tables) (f g : Func) : Prop where
  wf : ∃ ce, WF ce f
  wg : ∃ ce, WF ce g
  cf : CertOK f
  rel : ZRel tabs f g
  chained : Chained f

variable {tabs : Tables} {f g : Func}

namespace Setup

variable (S : Setup tabs f g)
include S

theorem blocks : g.blocks = f.blocks := CopyElim.cfgView_blocks S.rel.cfg
theorem entry : g.entry = f.entry := CopyElim.cfgView_entry S.rel.cfg

theorem params : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

theorem paramTys : (Ctx.make tabs g).paramTys = (Ctx.make tabs f).paramTys := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

theorem outs : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

theorem locals : (Ctx.make tabs g).locals = (Ctx.make tabs f).locals := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

/-- The target block of a block of `f`. -/
theorem block {b : ID} (hb : b ∈ f.blocks) {fb : Block} (hfb : f.block? b = some fb) :
    ∃ gb, g.block? b = some gb ∧ gb.id = fb.id ∧ gb.succs = fb.succs ∧ gb.preds = fb.preds ∧
      gb.kind = fb.kind ∧ gb.controls = fb.controls ∧
      (∀ x ∈ fb.values, x ∈ gb.values ∨ EA g x) ∧ (∀ x ∈ gb.values, x ∈ fb.values ∨ EA g x) := by
  obtain ⟨gb, hgb, h1, h2, h3⟩ := CopyElim.cfgView_block S.rel.cfg hfb
  obtain ⟨gb', hgb', h4, h5, h6, h7⟩ := S.rel.block b hb fb hfb
  rw [hgb] at hgb'; cases hgb'
  exact ⟨gb, hgb, h1, h2, h3, h4, h5, h6, h7⟩

/-- The target version of a value of `f`. -/
theorem value {x : ID} {fv : Value} (hfv : f.value? x = some fv) :
    ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧ gv.op = fv.op ∧ gv.aux = fv.aux ∧
      gv.auxInt = fv.auxInt ∧ gv.type = fv.type ∧ gv.args.size = fv.args.size ∧
      ∀ (k : Nat) (fa : ID), fv.args[k]? = some fa →
        ∃ ga, gv.args[k]? = some ga ∧ (ga = fa ∨ EA g ga ∧ Same f g fa ga) :=
  S.rel.value x fv hfv

/-- Shapes agree on values of `f`. -/
theorem tys {x : ID} {fv : Value} (hfv : f.value? x = some fv) :
    (Ctx.make tabs g).tys[x]? = (Ctx.make tabs f).tys[x]? := by
  obtain ⟨gv, hgv, -, -, -, -, hty, -⟩ := S.value hfv
  rw [tys_of_value hfv, tys_of_value hgv, hty]

/-- An `EA g` value is listed in `g`'s entry and in no other block of `g`. -/
theorem ea_block {x : ID} (hx : EA g x) {b : ID} (hb : b ∈ f.blocks) {gb : Block}
    (hgb : g.block? b = some gb) (hxb : x ∈ gb.values) : b = f.entry := by
  obtain ⟨ce, hwg⟩ := S.wg
  obtain ⟨gE, hgE, hxE, -⟩ := ea_iff.1 hx
  have hEm : g.entry ∈ g.blocks := hwg.entry
  rw [← S.entry]
  exact hwg.valueOnce b gb g.entry gE ⟨by rw [S.blocks]; exact hb, hgb⟩ ⟨hEm, hgE⟩ x hxb hxE

/-- **The target's schedule nodes of a block**: the source's that are not `EA g`, and in the
entry the `EA g` values. -/
theorem nodeT {b : ID} (hb : b ∈ f.blocks) {fb gb : Block} (hfb : f.block? b = some fb)
    (hgb : g.block? b = some gb) {x : ID} :
    NodeIn (schedNodes g gb).toList x ↔
      (NodeIn (schedNodes f fb).toList x ∧ ¬ EA g x) ∨ (EA g x ∧ b = f.entry) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : b ∈ g.blocks := by rw [S.blocks]; exact hb
  obtain ⟨gb', hgb', -, -, -, -, -, hfg, hgf⟩ := S.block hb hfb
  rw [hgb] at hgb'; cases hgb'
  rw [nodeIn_schedNodes (valuesOwn hwg hbg hgb), nodeIn_schedNodes (valuesOwn hwf hb hfb)]
  constructor
  · rintro ⟨hxg, gv, hgv, hgn⟩
    by_cases hea : EA g x
    · exact .inr ⟨hea, S.ea_block hea hb hgb hxg⟩
    · refine .inl ⟨⟨(hgf x hxg).resolve_right hea, ?_⟩, hea⟩
      obtain ⟨fv, hfv, -, -⟩ := hwf.valueId b fb ⟨hb, hfb⟩ x ((hgf x hxg).resolve_right hea)
      obtain ⟨gv', hgv', -, hop, -⟩ := S.value hfv
      rw [hgv] at hgv'; cases hgv'
      exact ⟨fv, hfv, by rw [← hop]; exact hgn⟩
  · rintro (⟨⟨hxf, fv, hfv, hfn⟩, hea⟩ | ⟨hea, rfl⟩)
    · obtain ⟨gv, hgv, -, hop, -⟩ := S.value hfv
      exact ⟨(hfg x hxf).resolve_right hea, gv, hgv, by rw [hop]; exact hfn⟩
    · obtain ⟨gE, hgE, hxE, v, hv, -, hvn⟩ := ea_iff.1 hea
      rw [S.entry, hgb] at hgE; cases hgE
      exact ⟨hxE, v, hv, hvn⟩

end Setup

end GoFV.Proof.ZCSE
