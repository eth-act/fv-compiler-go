import GoFV.Proof.Pass.DecPhiRel
import GoFV.Proof.Pass.CopyElimSim
import GoFV.Proof.Pass.CSESim
import GoFV.Proof.AtomSimLoop
import GoFV.Proof.AtomSimBlock
import GoFV.Proof.Avail

/-!
# Decompose's phi splitting: one block entry (issue #17)

The simulation relates the source frame `S` and the target frame `T` at block entries by the
meanings of `decPhiCheck` (`MRel`): every value `z` of `g` with meaning `(s, π)` holds a
refinement of component `π` of the source's register of `s` (source values: themselves). Values
are placed in the block of their meaning's source value, so a block entry re-establishes the
relation for exactly its own values:

* `tgt_phis`: the target's `Phi`s (the source's unchanged ones, and the component `Phi`s of a
  split source `Phi` `s`, whose argument `j` means component `π` of `s`'s argument `j`) hold
  refinements of their meanings in the source's `Phi`s;
* `tgt_loop`: along the target's schedule, against the source's frame `G` after the block, an
  unchanged value evaluates to a refinement (`eval_same`), a split `Phi` or a new `Make` to a
  `Make` of refined components (`refines_make`), an extractor to the refined component
  (`ext_snoc`), `Empty` to `.empty`.
-/

namespace GoFV.Proof.DecPhi

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ECCheck GoFV.Opt.DecPhiCheck GoFV.Proof.AtomSim

/-- The meanings `decPhiCheck` computes. -/
abbrev mean (tabs : Tables) (f g : Func) : Array (Option Mean) := meanOf (typeShapes tabs) f g

/-- The facts of the two functions. -/
structure Hyp (tabs : Tables) (f g : Func) (ce ce' : CheckEnv) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  blk : ∀ bid ∈ f.blocks, DecPhiCheck.blockOK (typeShapes tabs) f g (mean tabs f g) bid = true
  wf : WF ce f
  wg : WF ce' g

/-- Every listed value `z` of `g` with meaning `(s, π)` holds in `T` a refinement of component
`π` of `s`'s register in `S`. -/
def MRel (m : Array (Option Mean)) (g : Func) (S T : Frame) : Prop :=
  ∀ z, Listed g z → ∀ s π, meanAt m z = some (s, π) → ∀ y, S.regs[s]? = some (some y) →
    ∃ y', T.regs[z]? = some (some y') ∧ Sem.Refines (ext π y) y'

/-- The simulation relation at the entry of block `b`. -/
structure SimAt (tabs : Tables) (f g : Func) (S T : Frame) (b : ID) : Prop where
  frame : T = { S with regs := T.regs }
  szS : S.regs.size = f.valueTab.size
  szT : T.regs.size = g.valueTab.size
  mem : b ∈ f.blocks
  rel : MRel (mean tabs f g) g S T
  typed : Typed (Ctx.make tabs f) S

section
variable {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}

theorem Hyp.blocks_eq (H : Hyp tabs f g ce ce') : g.blocks = f.blocks :=
  CopyElim.cfgView_blocks H.cfg

theorem Hyp.entry_eq (H : Hyp tabs f g ce ce') : g.entry = f.entry :=
  CopyElim.cfgView_entry H.cfg

/-- The facts of block `b`. -/
theorem Hyp.block (H : Hyp tabs f g ce ce') {b : ID} (hb : b ∈ f.blocks) {fb : Block}
    (hfb : f.block? b = some fb) :
    ∃ gb, g.block? b = some gb ∧ gb.kind = fb.kind ∧ gb.controls = fb.controls ∧
      (∀ x ∈ fb.values, x ∈ gb.values) ∧
      (∀ z ∈ gb.values, ∃ w, g.value? z = some w ∧ w.id = z ∧
        (∀ u, f.value? z = some u → z ∈ fb.values ∧
          srcOK (typeShapes tabs) g (mean tabs f g) u w = true) ∧
        (f.value? z = none → newOK (typeShapes tabs) f g (mean tabs f g) fb w = true)) ∧
      ∃ of og, schedule f fb = some of ∧ schedule g gb = some og ∧
        of.toList.filter (npOf f fb) = og.toList.filter (npOf f fb) :=
  blockOK_spec (H.blk b hb) hfb

/-- A listed source value means itself. -/
theorem Hyp.mean_src (H : Hyp tabs f g ce ce') {x : ID} (hx : Listed f x) :
    meanAt (mean tabs f g) x = some (x, []) := by
  obtain ⟨b, fb, ⟨hb, hfb⟩, hxf⟩ := hx
  obtain ⟨gb, -, -, -, hsub, hval, -⟩ := H.block hb hfb
  obtain ⟨w, -, -, hsrc, -⟩ := hval x (hsub x hxf)
  obtain ⟨u, hu, hid, -⟩ := H.wf.valueId b fb ⟨hb, hfb⟩ x hxf
  have := (srcOK_spec (hsrc u hu).2).2.1
  rwa [hid] at this

/-- A listed value of `g` whose meaning's source value is listed in block `b` of `f` is listed
in block `b` of `g`. -/
theorem Hyp.inBlock (H : Hyp tabs f g ce ce') {b : ID} (hb : b ∈ f.blocks) {fb gb : Block}
    (hfb : f.block? b = some fb) (hgb : g.block? b = some gb) {a s : ID} {π : Path}
    (ha : Listed g a) (hm : meanAt (mean tabs f g) a = some (s, π)) (hs : s ∈ fb.values) :
    a ∈ gb.values := by
  obtain ⟨b', gb', ⟨hb', hgb'⟩, hag⟩ := ha
  have hbf : b' ∈ f.blocks := H.blocks_eq ▸ hb'
  obtain ⟨fb', hfb', -⟩ := H.wf.blockId b' hbf
  obtain ⟨gb'', hgb'', -, -, -, hval, -⟩ := H.block hbf hfb'
  rw [hgb'] at hgb''; cases hgb''
  obtain ⟨w, hw, hwid, hsrc, hnew⟩ := hval a hag
  have hs' : s ∈ fb'.values := by
    cases hfa : f.value? a with
    | some u =>
      obtain ⟨hafb, hok⟩ := hsrc u hfa
      obtain ⟨u', hu', hid, -⟩ := H.wf.valueId b' fb' ⟨hbf, hfb'⟩ a hafb
      rw [hfa] at hu'; cases hu'
      have := (srcOK_spec hok).2.1
      rw [hid, hm] at this; cases this; exact hafb
    | none =>
      obtain ⟨s', π', hm', -, -, hs', -⟩ := newOK_spec (hnew hfa)
      rw [hwid, hm] at hm'; cases hm'; exact hs'
  have := H.wf.valueOnce b' fb' b fb ⟨hbf, hfb'⟩ ⟨hb, hfb⟩ s hs' hs
  subst this
  rw [hgb] at hgb'; cases hgb'; exact hag

/-- The shape `evalValue` uses for a value of `g`. -/
theorem tys_g {tabs : Tables} {g : Func} (z : ID) :
    (Ctx.make tabs g).tys[z]?.getD .other = shapeOf (typeShapes tabs) g z :=
  (EC.shapeOf_eq tabs g z).symm

theorem selIdx_phi {w : Value} (h : w.op = .Phi) : selIdx? w = none := by
  unfold selIdx?; rw [h]

/-- **The target's `Phi`s**: each holds a refinement of its meaning in the source's `Phi`s. -/
theorem tgt_phis (H : Hyp tabs f g ce ce') {S T : Frame} {b : ID} {i : Nat}
    (hA : SimAt tabs f g S T b) {fb gb : Block} (hfb : f.block? b = some fb)
    (hgb : g.block? b = some gb) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) S i) = .ok ps) :
    ∃ psT, gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) T i) = .ok psT ∧
      ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
        ∃ y', (setPhis psT T.regs)[z]? = some (some y') ∧
          ∀ s π, meanAt (mean tabs f g) z = some (s, π) →
            ∀ y, (setPhis ps S.regs)[s]? = some (some y) → Sem.Refines (ext π y) y' := by
  have hb := hA.mem
  have hbg : b ∈ g.blocks := H.blocks_eq ▸ hb
  obtain ⟨gb', hgb', -, -, -, hval, -⟩ := H.block hb hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨-, -, -, hphS⟩ := phis_spec (H.wf.valuesNodup b fb ⟨hb, hfb⟩) hps
  have key : ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
      ∃ c yc, w.args[i]? = some c ∧ T.regs[c]? = some (some yc) ∧
        ∀ s π, meanAt (mean tabs f g) z = some (s, π) →
          ∀ y, (setPhis ps S.regs)[s]? = some (some y) →
            Sem.Refines (ext π y) (yc.retype ((Ctx.make tabs g).tys[z]?.getD .other)) := by
    intro z hz w hw hph
    obtain ⟨w', hw', hwid, hsrc, hnew⟩ := hval z hz
    rw [hw] at hw'; cases hw'
    have hcl : ∀ c ∈ w.args, Listed g c :=
      H.wg.argListed b gb z w ⟨⟨hbg, hgb⟩, hz, hw⟩
    cases hfz : f.value? z with
    | none =>
      obtain ⟨s, π, hm, hne, hsh, hs, hcls⟩ := newOK_spec (hnew hfz)
      rw [hwid] at hm hsh
      rcases hcls with hc | hc | hc | hc
      · obtain ⟨k, -, -, hk, -⟩ := selOK_spec hc
        rw [selIdx_phi hph] at hk; cases hk
      · obtain ⟨-, u, hu, hup, hsz, hargs⟩ := phiOK_spec hc
        obtain ⟨a, ya, ha, hya, hset⟩ := hphS s hs u hu hup
          (by rw [hA.szS]; exact lt_of_value? hu)
        have hi : i < w.args.size := by rw [hsz]; exact (Array.getElem?_eq_some_iff.1 ha).1
        obtain ⟨c, hc⟩ : ∃ c, w.args[i]? = some c := ⟨w.args[i], by simp [hi]⟩
        obtain ⟨hmc, hshc⟩ := hargs i c a hc ha
        obtain ⟨yc, hyc, hext⟩ := hA.rel c (hcl c (Array.mem_of_getElem? hc)) a π hmc ya hya
        refine ⟨c, yc, hc, hyc, fun s' π' hm' y hy => ?_⟩
        rw [hm] at hm'; cases hm'
        rw [hset] at hy; cases hy
        -- the source's `Phi` holds its argument unchanged (same shapes)
        have hty : ya.retype ((Ctx.make tabs f).tys[s]?.getD .other) = ya := by
          have := hA.typed a ya hya
          rwa [← EC.shapeOf_eq, hshc, EC.shapeOf_eq] at this
        rw [hty]
        obtain ⟨⟨k, t⟩, hl⟩ : ∃ p, π.getLast? = some p := by
          cases h : π.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
          | some p => exact ⟨p, rfl⟩
        have ht : (Ctx.make tabs g).tys[z]?.getD .other = t := by
          rw [tys_g, hsh]; unfold meanTy; rw [hl]
        rw [ht, ← Val.retype_of_hasTy (ext_hasTy hl ya)]
        exact retype_mono t hext
      · have := (makeOK_spec hc).1
        rw [hph] at this; cases this
      · have := (emptyOK_spec hc).1
        rw [hph] at this; cases this
    | some u =>
      obtain ⟨hzf, hok⟩ := hsrc u hfz
      obtain ⟨u', hu', huid, -⟩ := H.wf.valueId b fb ⟨hb, hfb⟩ z hzf
      rw [hfz] at hu'; cases hu'
      obtain ⟨-, hmz, hcls⟩ := srcOK_spec hok
      rw [huid] at hmz
      have hsame : sameOK u w = true := by
        rcases hcls with h | ⟨-, -, h | h⟩
        · exact h
        · have := (makeOK_spec h).1; rw [hph] at this; cases this
        · have := (emptyOK_spec h).1; rw [hph] at this; cases this
      obtain ⟨hop, hty, -, -, hargs⟩ := sameOK_spec hsame
      have hup : u.op = .Phi := hop.symm.trans hph
      obtain ⟨a, ya, ha, hya, hset⟩ := hphS z hzf u hfz hup
        (by rw [hA.szS]; exact lt_of_value? hfz)
      have haf : Listed f a :=
        H.wf.argListed b fb z u ⟨⟨hb, hfb⟩, hzf, hfz⟩ a (Array.mem_of_getElem? ha)
      have hwa : w.args[i]? = some a := by rw [hargs]; exact ha
      obtain ⟨yc, hyc, hext⟩ := hA.rel a (hcl a (Array.mem_of_getElem? hwa)) a []
        (H.mean_src haf) ya hya
      refine ⟨a, yc, hwa, hyc, fun s π hm y hy => ?_⟩
      rw [hmz] at hm; cases hm
      rw [hset] at hy; cases hy
      have : (Ctx.make tabs g).tys[z]?.getD .other = (Ctx.make tabs f).tys[z]?.getD .other := by
        rw [tys_of_value hw, tys_of_value hfz, hty]
      rw [this]
      exact retype_mono _ hext
  obtain ⟨psT, hpsT⟩ := filterMapM_phi_ok (ctx := Ctx.make tabs g) (fr := T) (i := i)
    (l := gb.values.toList) fun z hz => by
      have hz' := Array.mem_toList_iff.1 hz
      obtain ⟨w, hw, -, -, -⟩ := hval z hz'
      by_cases hph : w.op = .Phi
      · obtain ⟨c, yc, hc, hyc, -⟩ := key z hz' w hw hph
        exact ⟨_, phiStep_phi hw hph hc hyc⟩
      · exact ⟨_, phiStep_nonphi hw hph⟩
  refine ⟨psT, hpsT, fun z hz w hw hph => ?_⟩
  obtain ⟨c, yc, hc, hyc, hrel⟩ := key z hz w hw hph
  obtain ⟨-, -, -, hphT⟩ := phis_spec (H.wg.valuesNodup b gb ⟨hbg, hgb⟩) hpsT
  obtain ⟨c', yc', hc', hyc', hset⟩ := hphT z hz w hw hph (by rw [hA.szT]; exact lt_of_value? hw)
  rw [hc] at hc'; cases hc'
  rw [hyc] at hyc'; cases hyc'
  exact ⟨_, hset, hrel⟩

/-! ## Evaluating the target's values -/

/-- **An unchanged value** evaluates to a refinement on refined arguments. -/
theorem eval_same {env : Env} (hE : env.Mono) (hown : g.ownAux = f.ownAux) {x : ID}
    {u w : Value} (hu : f.value? x = some u) (hw : g.value? x = some w) (hux : u.id = x)
    (hwx : w.id = x) (hs : sameOK u w = true) {frS T : Frame}
    (hT : T = { frS with regs := T.regs })
    (hfr : ∀ a ∈ u.args.toList, ∀ y, frS.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines y y') :
    Res.Refines (evalValue env (Ctx.make tabs f) frS u) (evalValue env (Ctx.make tabs g) T w) := by
  obtain ⟨hop, hty, hai, hax, hargs⟩ := sameOK_spec hs
  have hwu : w = { u with pos := w.pos, uses := w.uses, block := w.block, type := w.type } := by
    have hid : w.id = u.id := hwx.trans hux.symm
    cases w; cases u
    simp only at hop hai hax hargs hid ⊢
    subst hop hai hax hargs hid; rfl
  unfold evalValue
  rw [hargs]
  have hrel := EC.mapM_regs_refines u.args.toList hfr
    (fun (a : ID) => s!"v{u.id}: argument v{a} has no value")
  have hmsg : (fun (a : ID) => Res.ofOption s!"v{w.id}: argument v{a} has no value"
      (T.regs[a]?).join) =
      (fun (a : ID) => Res.ofOption s!"v{u.id}: argument v{a} has no value" (T.regs[a]?).join) := by
    rw [hux, hwx]
  rw [hmsg]
  have htys : (Ctx.make tabs g).tys[w.id]?.getD .other =
      (Ctx.make tabs f).tys[u.id]?.getD .other := by
    rw [hux, hwx, tys_of_value hu, tys_of_value hw, hty]
  rw [htys]
  revert hrel
  generalize u.args.toList.mapM (fun a => Res.ofOption s!"v{u.id}: argument v{a} has no value"
    (frS.regs[a]?).join) = rS
  generalize u.args.toList.mapM (fun a => Res.ofOption s!"v{u.id}: argument v{a} has no value"
    (T.regs[a]?).join) = rT
  intro hrel
  cases hrel with
  | stuck msg r => exact .stuck _ _
  | panic e hm => exact .panic e hm
  | @ok argv argv' hl =>
    show Res.Refines (Res.bind (Res.ok argv) _) (Res.bind (Res.ok argv') _)
    simp only [Res.bind_ok]
    have hev : evalOp env (Ctx.make tabs g) T w argv' ((Ctx.make tabs f).tys[u.id]?.getD .other) =
        evalOp env (Ctx.make tabs g) T u argv' ((Ctx.make tabs f).tys[u.id]?.getD .other) := by
      rw [hwu]; exact EC.evalOp_upd _ _ _ u _ _ _ _ _ _
    rw [hev]
    have hctx := AtomSim.ctx_eq (tabs := tabs) hown.symm
    have hm := evalOp_mono env hE (Ctx.make tabs f) (Ctx.make tabs g) hctx frS T
      (by rw [hT]) (by rw [hT]) (by rw [hT]) (by rw [hT]) u
      ((Ctx.make tabs f).tys[u.id]?.getD .other) hl
    revert hm
    generalize evalOp env (Ctx.make tabs f) frS u argv _ = r
    generalize evalOp env (Ctx.make tabs g) T u argv' _ = r'
    intro hm
    cases hm with
    | ok h => exact .ok (retype_mono _ h)
    | panic e hm => exact .panic e hm
    | stuck msg r => exact .stuck _ _

/-- A `Make` whose arguments hold refinements of the components of `y` (a value of the
`Make`'s shape, whose aggregate layout has fields `fs`) evaluates to a refinement of `y`. -/
theorem eval_make {env : Env} {T : Frame} {x : ID} {w : Value} (hwx : w.id = x)
    (hmk : isMake w.op = true) {fs : List (Nat × Ty)} {n : Nat}
    (hsh : (shapeOf (typeShapes tabs) g x).asAgg = .agg fs n) (hsz : w.args.size = fs.length)
    (hreg : ∀ a ∈ w.args, Reg T a) {y : Val}
    (hy : y.hasTy (shapeOf (typeShapes tabs) g x) = true)
    (harg : ∀ k (hk : k < fs.length) (hk' : k < w.args.size), ∃ y',
      T.regs[w.args[k]]? = some (some y') ∧
        Sem.Refines ((Comp.select k [y]).retype fs[k].2) y') :
    ∃ y', evalValue env (Ctx.make tabs g) T w = .ok y' ∧ Sem.Refines y y' := by
  refine ⟨_, EC.ecT_eval_make hmk hreg, ?_⟩
  rw [hwx, tys_g, retype_asAgg, hsh]
  have hy' : y.hasTy (.agg fs n) = true := by rw [← hsh]; exact Val.hasTy_asAgg hy
  conv => lhs; rw [← Val.checkLen_of_hasTy hy]
  refine Val.checkLen_mono _ (refines_make hy' (by simp [hsz]) fun k hk hk' => ?_)
  obtain ⟨y', hy', hyy⟩ := harg k hk (by rw [hsz]; exact hk)
  simp only [List.getElem_map, Array.getElem_toList]
  rw [rv_of hy']
  exact hyy

/-- `Empty` evaluates to a refinement of a zero-sized value. -/
theorem eval_empty {env : Env} {T : Frame} {x : ID} {w : Value} (hwx : w.id = x)
    (hop : w.op = .Empty) (hargs : w.args = #[]) (hsh : shapeOf (typeShapes tabs) g x = .empty)
    {y : Val} (hy : y.hasTy .empty = true) :
    ∃ y', evalValue env (Ctx.make tabs g) T w = .ok y' ∧ Sem.Refines y y' := by
  refine ⟨_, EC.ecT_eval_empty hop (by rw [hargs]; nofun), ?_⟩
  rw [hwx, tys_g, hsh]
  exact refines_empty hy

/-- An extractor of component `k` evaluates to the component, retyped. -/
theorem eval_sel {env : Env} {T : Frame} {x a : ID} {w : Value} (hwx : w.id = x) {k : Nat}
    (hk : selIdx? w = some k) (ha : w.args.toList = [a]) (hreg : Reg T a) :
    evalValue env (Ctx.make tabs g) T w =
      .ok ((Comp.select k [rv T a]).retype (shapeOf (typeShapes tabs) g x)) := by
  obtain ⟨ht, hfr, hev⟩ := EC.ec_sel hk
  have hr : ∀ b ∈ w.args, Reg T b := fun b hb => by
    rw [← Array.mem_toList_iff, ha, List.mem_singleton] at hb
    rw [hb]; exact hreg
  rw [EC.ecT_eval_term ht hfr hr, hev, ha, hwx, tys_g]
  rfl

/-! ## The target's schedule -/

/-- The invariant along the target's schedule prefix `d`. -/
def LInv (m : Array (Option Mean)) (G T1 : Frame) (d : List ID) (T : Frame) : Prop :=
  T = { T1 with regs := T.regs } ∧ T.regs.size = T1.regs.size ∧
    (∀ a, a ∉ d → T.regs[a]? = T1.regs[a]?) ∧ (∀ z ∈ d, Reg T z) ∧
    (∀ z ∈ d, ∀ s π, meanAt m z = some (s, π) → ∀ y, G.regs[s]? = some (some y) →
      ∃ y', T.regs[z]? = some (some y') ∧ Sem.Refines (ext π y) y')

/-- The facts about block `b`, the target's schedule `og` of it, the target's frame `T1` after
its `Phi`s and the source's reference frame `G`. -/
structure BH (tabs : Tables) (f g : Func) (ce ce' : CheckEnv) (b : ID) (fb gb : Block)
    (og : Array ID) (G T1 : Frame) : Prop where
  H : Hyp tabs f g ce ce'
  hb : b ∈ f.blocks
  hfb : f.block? b = some fb
  hgb : g.block? b = some gb
  hsg : schedule g gb = some og
  hT1 : T1 = { G with regs := T1.regs }
  hsz : T1.regs.size = g.valueTab.size
  hout : ∀ z, Listed g z → z ∉ og.toList → ∀ s π, meanAt (mean tabs f g) z = some (s, π) →
    ∀ y, G.regs[s]? = some (some y) →
      ∃ y', T1.regs[z]? = some (some y') ∧ Sem.Refines (ext π y) y'
  hphi : ∀ z ∈ gb.values, z ∉ og.toList → Reg T1 z
  hGt : Typed (Ctx.make tabs f) G

theorem BH.bg {b : ID} {fb gb : Block} {og : Array ID} {G T1 : Frame}
    (B : BH tabs f g ce ce' b fb gb og G T1) : b ∈ g.blocks := B.H.blocks_eq ▸ B.hb

theorem BH.og {b : ID} {fb gb : Block} {og : Array ID} {G T1 : Frame}
    (B : BH tabs f g ce ce' b fb gb og G T1) :
    og.toList.Nodup ∧ TopoRem (argsF g) og.toList ∧
      ∀ x, x ∈ og.toList ↔ x ∈ gb.values ∧ ∃ w, g.value? x = some w ∧ w.op ≠ .Phi :=
  schedule_topo (valuesOwn B.H.wg B.bg B.hgb) (B.H.wg.valuesNodup b gb ⟨B.bg, B.hgb⟩) B.hsg

/-- An argument of the schedule's value `x`, after the prefix `d`: it holds refinements of its
meanings, and has a register if it is listed in the block. -/
theorem BH.arg {b : ID} {fb gb : Block} {og : Array ID} {G T1 : Frame}
    (B : BH tabs f g ce ce' b fb gb og G T1) {d s : List ID} {x : ID}
    (hog : og.toList = d ++ x :: s) {T : Frame} (hI : LInv (mean tabs f g) G T1 d T) {w : Value}
    (hw : g.value? x = some w) {a : ID} (ha : a ∈ w.args) :
    Listed g a ∧ (a ∈ gb.values → Reg T a) ∧
      ∀ sb π, meanAt (mean tabs f g) a = some (sb, π) → ∀ y, G.regs[sb]? = some (some y) →
        ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (ext π y) y' := by
  obtain ⟨-, htopo, hmem⟩ := B.og
  obtain ⟨-, -, hk, hreg, hrel⟩ := hI
  have hxog : x ∈ og.toList := by rw [hog]; simp
  obtain ⟨hxgb, w', hw', -⟩ := (hmem x).1 hxog
  rw [hw] at hw'; cases hw'
  have hl : Listed g a := B.H.wg.argListed b gb x w ⟨⟨B.bg, B.hgb⟩, hxgb, hw⟩ a ha
  by_cases hm : a ∈ og.toList
  · have had : a ∈ d := by
      rw [hog] at hm htopo
      exact topoRem_before htopo (by rw [argsF_of hw]; exact Array.mem_toList_iff.2 ha) hm
    exact ⟨hl, fun _ => hreg a had, hrel a had⟩
  · have had : a ∉ d := fun h => hm (by rw [hog]; exact List.mem_append_left _ h)
    refine ⟨hl, fun hag => ?_, fun sb π hma y hy => ?_⟩
    · rw [Reg, hk a had]; exact B.hphi a hag hm
    · rw [hk a had]; exact B.hout a hl hm sb π hma y hy

/-- **A split `Phi` or a new value of the schedule** evaluates, to a refinement of its
meaning. -/
theorem BH.tgt_new {env : Env} {b : ID} {fb gb : Block} {og : Array ID} {G T1 : Frame}
    (B : BH tabs f g ce ce' b fb gb og G T1) {d s : List ID} {x : ID}
    (hog : og.toList = d ++ x :: s) {T : Frame} (hI : LInv (mean tabs f g) G T1 d T)
    (hnot : ∀ u, f.value? x = some u → u.op = .Phi) :
    ∃ y', stepV env (Ctx.make tabs g) T x = .ok y' ∧
      ∀ sb π, meanAt (mean tabs f g) x = some (sb, π) → ∀ y, G.regs[sb]? = some (some y) →
        Sem.Refines (ext π y) y' := by
  obtain ⟨-, -, hmem⟩ := B.og
  have hxog : x ∈ og.toList := by rw [hog]; simp
  obtain ⟨hxgb, w, hw, hwph⟩ := (hmem x).1 hxog
  obtain ⟨gb', hgb', -, -, -, hval, -⟩ := B.H.block B.hb B.hfb
  rw [B.hgb] at hgb'; cases hgb'
  obtain ⟨w', hw', hwx, hsrc, hnew⟩ := hval x hxgb
  rw [hw] at hw'; cases hw'
  have hstep : stepV env (Ctx.make tabs g) T x = evalValue env (Ctx.make tabs g) T w := by
    unfold stepV; rw [show (Ctx.make tabs g).f = g from rfl, hw]
  rw [hstep]
  -- the arguments with a meaning based in `fb` are listed in `gb`
  have hargIn : ∀ a ∈ w.args, ∀ sb π, meanAt (mean tabs f g) a = some (sb, π) → sb ∈ fb.values →
      a ∈ gb.values := fun a ha sb π hm hs =>
    B.H.inBlock B.hb B.hfb B.hgb (B.arg hog hI hw ha).1 hm hs
  -- a `Make`/`Empty` of meaning `(sb, π)` with `sb ∈ fb`, its base value `yb` of its shape
  have mk : ∀ sb π, sb ∈ fb.values → (makeOK (typeShapes tabs) g (mean tabs f g) w sb π = true ∨
      emptyOK (typeShapes tabs) g w = true) →
      ∃ y', evalValue env (Ctx.make tabs g) T w = .ok y' ∧ ∀ y, G.regs[sb]? = some (some y) →
        (ext π y).hasTy (shapeOf (typeShapes tabs) g x) = true → Sem.Refines (ext π y) y' := by
    intro sb π hs hc
    rcases hc with hc | hc
    · obtain ⟨hmk, fs, n, hsh, hsz, hma⟩ := makeOK_spec hc
      rw [hwx] at hsh
      have hreg : ∀ a ∈ w.args, Reg T a := fun a ha => by
        obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem ha
        exact (B.arg hog hI hw ha).2.1
          (hargIn _ ha sb _ (hma k (by rw [← hsz]; exact hk) hk) hs)
      have hev := EC.ecT_eval_make (env := env) (ctx := Ctx.make tabs g) hmk hreg
      refine ⟨_, hev, fun y hy hty => ?_⟩
      obtain ⟨y', hev', hyy⟩ := eval_make (env := env) hwx hmk hsh hsz hreg hty
        fun k hk hk' => by
          obtain ⟨-, -, hrel⟩ := B.arg hog hI hw (Array.getElem_mem hk')
          obtain ⟨y', hy', hyy⟩ := hrel sb _ (hma k hk hk') y hy
          rw [ext_snoc] at hyy
          exact ⟨y', hy', hyy⟩
      rw [hev] at hev'; cases hev'
      exact hyy
    · obtain ⟨hop, hargs, hsh⟩ := emptyOK_spec hc
      rw [hwx] at hsh
      obtain ⟨y', hev, -⟩ := eval_empty (env := env) (T := T) (y := .poison) hwx hop hargs hsh rfl
      refine ⟨y', hev, fun y _ hty => ?_⟩
      rw [hsh] at hty
      obtain ⟨y'', hev', hyy⟩ := eval_empty (env := env) (T := T) hwx hop hargs hsh hty
      rw [hev] at hev'; cases hev'
      exact hyy
  cases hfx : f.value? x with
  | some u =>
    -- a split `Phi`: meaning `(x, [])`
    have hup := hnot u hfx
    obtain ⟨hxf, hok⟩ := hsrc u hfx
    obtain ⟨u', hu', huid, -⟩ := B.H.wf.valueId b fb ⟨B.hb, B.hfb⟩ x hxf
    rw [hfx] at hu'; cases hu'
    obtain ⟨-, hmx, hcls⟩ := srcOK_spec hok
    rw [huid] at hmx hcls
    rcases hcls with hc | ⟨-, hty, hc⟩
    · exact absurd ((sameOK_spec hc).1.trans hup) hwph
    · obtain ⟨y', hev, hrel⟩ := mk x [] hxf hc
      refine ⟨y', hev, fun sb π hm y hy => ?_⟩
      rw [hmx] at hm; cases hm
      refine hrel y hy ?_
      have := B.hGt x y hy
      rw [← this, ← EC.shapeOf_eq]
      have hsx : shapeOf (typeShapes tabs) f x = shapeOf (typeShapes tabs) g x := by
        show valueTy _ (f.value? x) = valueTy _ (g.value? x)
        rw [hfx, hw]; simp only [valueTy, hty]
      rw [hsx]; exact Val.retype_hasTy _ _
  | none =>
    obtain ⟨sb, π, hm, hne, hsh, hs, hcls⟩ := newOK_spec (hnew hfx)
    rw [hwx] at hm hsh
    rcases hcls with hc | hc | hc | hc
    · obtain ⟨k, a, t, hk, ha, hl, hma⟩ := selOK_spec hc
      have ham : a ∈ w.args := by rw [← Array.mem_toList_iff, ha]; exact List.mem_singleton_self a
      obtain ⟨-, hreg, hrel⟩ := B.arg hog hI hw ham
      have hra := hreg (hargIn a ham sb _ hma hs)
      refine ⟨_, eval_sel hwx hk ha hra, fun sb' π' hm' y hy => ?_⟩
      rw [hm] at hm'; cases hm'
      obtain ⟨ya, hya, hyy⟩ := hrel sb _ hma y hy
      have ht : shapeOf (typeShapes tabs) g x = t := by rw [hsh]; unfold meanTy; rw [hl]
      rw [ht, ← dropLast_append_of_getLast? hl, ext_snoc, rv_of hya]
      exact retype_mono t (EC.ec_select_mono k hyy)
    · exact absurd (phiOK_spec hc).1 hwph
    · obtain ⟨y', hev, hrel⟩ := mk sb π hs (.inl hc)
      refine ⟨y', hev, fun sb' π' hm' y hy => ?_⟩
      rw [hm] at hm'; cases hm'
      obtain ⟨⟨k, t⟩, hl⟩ : ∃ p, π.getLast? = some p := by
        cases h : π.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
        | some p => exact ⟨p, rfl⟩
      refine hrel y hy ?_
      rw [hsh]; unfold meanTy; rw [hl]; exact ext_hasTy hl y
    · obtain ⟨y', hev, hrel⟩ := mk sb π hs (.inr hc)
      refine ⟨y', hev, fun sb' π' hm' y hy => ?_⟩
      rw [hm] at hm'; cases hm'
      obtain ⟨⟨k, t⟩, hl⟩ : ∃ p, π.getLast? = some p := by
        cases h : π.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
        | some p => exact ⟨p, rfl⟩
      refine hrel y hy ?_
      rw [hsh]; unfold meanTy; rw [hl]; exact ext_hasTy hl y

/-- **An unchanged value of the schedule** evaluates to a refinement of the source's
evaluation (or panics alike). -/
theorem BH.tgt_src {env : Env} (hE : env.Mono) {b : ID} {fb gb : Block} {og : Array ID}
    {G T1 : Frame} (B : BH tabs f g ce ce' b fb gb og G T1) {d s : List ID} {x : ID}
    (hog : og.toList = d ++ x :: s) {T : Frame} (hI : LInv (mean tabs f g) G T1 d T) {u : Value}
    (hu : f.value? x = some u) (hup : u.op ≠ .Phi) :
    Res.Refines (evalValue env (Ctx.make tabs f) G u) (stepV env (Ctx.make tabs g) T x) := by
  obtain ⟨-, -, hmem⟩ := B.og
  have hxog : x ∈ og.toList := by rw [hog]; simp
  obtain ⟨hxgb, w, hw, -⟩ := (hmem x).1 hxog
  obtain ⟨gb', hgb', -, -, -, hval, -⟩ := B.H.block B.hb B.hfb
  rw [B.hgb] at hgb'; cases hgb'
  obtain ⟨w', hw', hwx, hsrc, -⟩ := hval x hxgb
  rw [hw] at hw'; cases hw'
  obtain ⟨hxf, hok⟩ := hsrc u hu
  obtain ⟨u', hu', hux, -⟩ := B.H.wf.valueId b fb ⟨B.hb, B.hfb⟩ x hxf
  rw [hu] at hu'; cases hu'
  obtain ⟨-, -, hcls⟩ := srcOK_spec hok
  have hs : sameOK u w = true := by
    rcases hcls with hc | ⟨hp, -⟩
    · exact hc
    · exact absurd hp hup
  have hargs := (sameOK_spec hs).2.2.2.2
  have hstep : stepV env (Ctx.make tabs g) T x = evalValue env (Ctx.make tabs g) T w := by
    unfold stepV; rw [show (Ctx.make tabs g).f = g from rfl, hw]
  rw [hstep]
  have hTG : T = { G with regs := T.regs } := by rw [hI.1, B.hT1]
  refine eval_same hE B.H.ownAux hu hw hux hwx hs hTG fun a ha y hy => ?_
  have ha' : a ∈ w.args := by rw [hargs]; exact Array.mem_toList_iff.1 ha
  have haf : Listed f a := B.H.wf.argListed b fb x u ⟨⟨B.hb, B.hfb⟩, hxf, hu⟩ a
    (Array.mem_toList_iff.1 ha)
  exact (B.arg hog hI hw ha').2.2 a [] (B.H.mean_src haf) y hy

/-- **The target's schedule prefix `L`** against the source's frame `G`, which holds the
evaluation of every unchanged value of `L`. -/
theorem BH.tgt_loop {env : Env} (hE : env.Mono) {b : ID} {fb gb : Block} {og : Array ID}
    {G T1 : Frame} (B : BH tabs f g ce ce' b fb gb og G T1) {L M : List ID}
    (hog : og.toList = L ++ M)
    (hsrc : ∀ x ∈ L, ∀ u, f.value? x = some u → u.op ≠ .Phi →
      ∃ y, G.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y) :
    ∃ T, evalAll env (Ctx.make tabs g) T1 L = .ok T ∧ LInv (mean tabs f g) G T1 L T := by
  obtain ⟨hnd, -, hmem⟩ := B.og
  refine evalAll_induct L (LInv (mean tabs f g) G T1) ?_ L [] T1 rfl
    ⟨by cases T1; rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩
  intro d x s T hL hI
  have hog' : og.toList = d ++ x :: (s ++ M) := by rw [hog, hL]; simp
  have hxog : x ∈ og.toList := by rw [hog']; simp
  have hxd : x ∉ d := fun hm => by
    have := hnd; rw [hog'] at this
    exact (List.nodup_append.1 this).2.2 x hm x List.mem_cons_self rfl
  obtain ⟨-, w, hw, -⟩ := (hmem x).1 hxog
  have hxlt : x < T.regs.size := by rw [hI.2.1, B.hsz]; exact lt_of_value? hw
  -- the value and its relation
  obtain ⟨y', hy', hrel⟩ : ∃ y', stepV env (Ctx.make tabs g) T x = .ok y' ∧
      ∀ sb π, meanAt (mean tabs f g) x = some (sb, π) → ∀ y, G.regs[sb]? = some (some y) →
        Sem.Refines (ext π y) y' := by
    cases hfx : f.value? x with
    | some u =>
      by_cases hup : u.op = .Phi
      · exact B.tgt_new hog' hI fun u' hu' => by rw [hfx] at hu'; cases hu'; exact hup
      · obtain ⟨yG, hyG, hevG⟩ := hsrc x (by rw [hL]; simp) u hfx hup
        have hr := B.tgt_src hE hog' hI hfx hup
        rw [hevG] at hr
        generalize stepV env (Ctx.make tabs g) T x = r at hr ⊢
        cases hr with
        | @ok _ y' hyy =>
          refine ⟨y', rfl, fun sb π hm y hy => ?_⟩
          have hxf : Listed f x := by
            obtain ⟨gb', hgb', -, -, -, hval, -⟩ := B.H.block B.hb B.hfb
            rw [B.hgb] at hgb'; cases hgb'
            obtain ⟨_, -, -, hsrc', -⟩ := hval x ((hmem x).1 hxog).1
            exact ⟨b, fb, ⟨B.hb, B.hfb⟩, (hsrc' u hfx).1⟩
          rw [B.H.mean_src hxf] at hm; cases hm
          rw [hyG] at hy; cases hy
          exact hyy
    | none => exact B.tgt_new hog' hI fun u hu => by rw [hfx] at hu; cases hu
  refine ⟨y', hy', ?_⟩
  obtain ⟨hTf, hTs, hTk, hTr, hTm⟩ := hI
  refine ⟨by rw [hTf]; rfl, by simp [Frame.set, hTs], fun a ha => ?_, fun a ha => ?_,
    fun z hz sb π hm y hy => ?_⟩
  · have hxa : x ≠ a := fun he => ha (by simp [he])
    rw [Frame.set_regs_ne hxa]; exact hTk a fun hm => ha (List.mem_append_left _ hm)
  · rcases List.mem_append.1 ha with ha | ha
    · have hxa : x ≠ a := fun he => hxd (he ▸ ha)
      rw [Reg, Frame.set_regs_ne hxa]; exact hTr a ha
    · rw [List.mem_singleton.1 ha]; exact ⟨y', Frame.set_regs_self hxlt⟩
  · rcases List.mem_append.1 hz with hz | hz
    · have hxz : x ≠ z := fun he => hxd (he ▸ hz)
      rw [Frame.set_regs_ne hxz]; exact hTm z hz sb π hm y hy
    · rw [List.mem_singleton.1 hz] at hm ⊢
      exact ⟨y', Frame.set_regs_self hxlt, hrel sb π hm y hy⟩

end

end GoFV.Proof.DecPhi
