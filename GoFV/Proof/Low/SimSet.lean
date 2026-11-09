import GoFV.Proof.Low.SimMem
import GoFV.Proof.Pass.RewriteTermDen

variable [GoFV.SSA.Sem.Addrs]

/-!
# Hypotheses, atoms and the target's schedule of the lowered atom simulation (issue #385)

`AtomsL`: what `LowerCheck.atomsOKL` says (`atomsOKL_spec`): the same entry, blocks and own aux,
per block the same ID, every atom listed in `g` listed in the same block of `f` as a
corresponding atom (`atomPair`) or a lowered frame address where `f` has a term (`frameAtomG`),
and both schedules listing `f`'s roots, atoms of `g`, in the same sequence (`rootAtL`; a lowered
`Zero` is not a root of `g`, which evaluates it earlier, and never fails there, `evalOpL_safeL`;
a lowered frame address always evaluates, to its variable's word, `evalValueL_frameAuxL`).
`Hyp`: both functions well formed with certified dominator trees, `AtomsL`, the validator's term
relations (`AtomArgsRefL`, `TermStepRefL`), `f`'s mode implies `g`'s, `f`'s atoms are generic
and `f`'s values have the same shape in both modes.

`atom_ref` is the only consumer of `AtomArgsRefL`: corresponding atoms' arguments refine (as
registers), and corresponding non-`Phi` atoms evaluate to refinements (`atomPair_eval`), given
the frames' relation and the target's frame addresses (`RegsFrameL`). `tgt_loop`: the target
evaluates a prefix of its schedule against a source reference frame (Phase 1's
`AtomSim.tgt_loop`, trivial source invariant).
-/

namespace GoFV.Proof.Low.Sim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof GoFV.Proof.Dom GoFV.Proof.Low
  GoFV.Proof.Term GoFV.Proof.AtomSim GoFV.Opt.LowerCheck GoFV.Opt.LowerTerm

theorem makeL_act (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).act = 0 := by
  unfold Ctx.makeL; split <;> rfl

/-! ## What `atomsOKL` says -/

/-- `x` is a root of `h` (the schedules' filter in `atomsOKL`). -/
def rootL (h : Func) (x : ID) : Bool := (h.value? x).any (Sem.isRoot ·.op)

/-- `x` is a root of `f` and an atom of `g` (the filter of `g`'s schedule in `atomsOKL`). -/
def rootAtL (tabs : Tables) (f g : Func) (x : ID) : Bool :=
  rootL f x && (g.value? x).any (fun w => !termVL tabs w)

/-- One block of `atomsOKL`. -/
structure BlockAtomsL (tabs : Tables) (f g : Func) (fb gb : Block) : Prop where
  id : fb.id = gb.id
  sub : ∀ x ∈ gb.values, ∀ w, g.value? x = some w → termVL tabs w = false →
    (x ∈ fb.values ∧ ∃ u, f.value? x = some u ∧ termVL tabs u = false ∧ atomPair tabs u w = true) ∨
      frameAtomG tabs f x w = true
  sched : ∃ of og, schedule f fb = some of ∧ schedule g gb = some og ∧
    of.toList.filter (rootL f) = og.toList.filter (rootAtL tabs f g)

/-- `atomsOKL` as propositions. -/
structure AtomsL (tabs : Tables) (f g : Func) : Prop where
  entry : f.entry = g.entry
  blocks : f.blocks = g.blocks
  ownAux : f.ownAux = g.ownAux
  block : ∀ b ∈ f.blocks, ∃ fb gb, f.block? b = some fb ∧ g.block? b = some gb ∧
    BlockAtomsL tabs f g fb gb

theorem mem_atomsOfL {tabs : Tables} {h : Func} {b : Block} {x : ID} :
    x ∈ atomsOfL tabs h b ↔ x ∈ b.values ∧ ∃ v, h.value? x = some v ∧ termVL tabs v = false := by
  unfold atomsOfL
  rw [List.mem_filter, Array.mem_toList_iff]
  constructor
  · rintro ⟨hx, h2⟩
    refine ⟨hx, ?_⟩
    split at h2
    · rename_i v hv; exact ⟨v, hv, by simpa [isAtomL] using h2⟩
    · cases h2
  · rintro ⟨hx, v, hv, ht⟩
    refine ⟨hx, ?_⟩
    rw [hv]; simpa [isAtomL] using ht

theorem atomsOKL_spec {tabs : Tables} {f g : Func} (h : atomsOKL tabs f g = true) :
    AtomsL tabs f g := by
  unfold atomsOKL at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨he, hb⟩, ho⟩, hall⟩ := h
  refine ⟨he, hb, ho, fun b hbm => ?_⟩
  have h := hall b hbm
  split at h
  · rename_i fb gb hfb hgb
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨hid, ⟨hsub, -⟩, hsch⟩ := h
    refine ⟨fb, gb, hfb, hgb, hid, fun x hx w hw ht => ?_, ?_⟩
    · have hm : x ∈ atomsOfL tabs g gb := mem_atomsOfL.2 ⟨hx, w, hw, ht⟩
      have h2 := hsub x hm
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h2
      rcases h2 with ⟨hxf, h2⟩ | hfa
      · obtain ⟨hxb, u, hu, hut⟩ := mem_atomsOfL.1 hxf
        refine .inl ⟨hxb, u, hu, hut, ?_⟩
        rw [hu, hw] at h2
        simp only [Bool.and_eq_true] at h2
        exact h2.1
      · rw [hw] at hfa
        exact .inr (by simpa using hfa)
    · split at hsch
      · rename_i of og hof hog
        exact ⟨of, og, hof, hog, beq_iff_eq.1 hsch⟩
      · cases hsch
  · cases h

/-- What `constArg` says. -/
theorem constArg_cases {tabs : Tables} {f : Func} {u : Value} {i : Nat} {k : Int} (h : constArg tabs f u i k = true) :
    ∃ y, f.value? u.args[i]! = some y ∧ y.op = .Const64 ∧ y.auxInt.toInt = k ∧ y.args.size = 0 ∧
      shp f.lowered tabs y.type = .int .w64 := by
  unfold constArg at h
  split at h
  · rename_i y hy
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨y, hy, h1, h2, h3, ?_⟩
    revert h4; cases shp f.lowered tabs y.type <;> simp
    rename_i w; cases w <;> simp
  · cases h

/-- A register holding a `Const64` (at the 64-bit integer shape) holds the constant. -/
theorem rv_const64 {tabs : Tables} {low : Bool} {D : ID → Option Value} {fr : Frame} {V : ID → Prop}
    (hD : DenOKL low D tabs fr V) {y : ID} {v : Value} (hy : V y) (hv : D y = some v)
    (hop : v.op = .Const64) (hs : shp low tabs v.type = .int .w64) :
    rv fr y = .i64 (BitVec.ofInt 64 v.auxInt.toInt) := by
  obtain ⟨-, h⟩ := hD y hy
  obtain ⟨N, hN⟩ := h (rv fr) (fun _ _ _ => rfl)
  have hg : Op.Const64.generic = true := by decide
  have ht' : GoFV.Opt.RewriteCheck.termOp .Const64 = true := by decide
  have ht : termVL tabs v = true := by unfold termVL; simp only [hop, hg, ht', ite_true]
  have e1 : ∀ args, opValL tabs .Const64 (.int .w64) v.auxInt v.aux args =
      .int .w64 (BitVec.ofInt 64 v.auxInt.toInt) := fun args => by
    simp only [opValL, hg, ite_true]
    rw [GoFV.Proof.Rules.opVal_pure (by decide)]; rfl
  rw [← hN (N + 1) (by omega), denL_succ_term hv ht, hs, hop, e1]
  cases low <;> simp [rty, Val.retypeL, Val.widen, Val.retype]

/-! ## The hypotheses -/

/-- The hypotheses of the lowered atom simulation. -/
structure Hyp (tabs : Tables) (f g : Func) (ce ce' : CheckEnv) : Prop where
  wf : WF ce f
  wg : WF ce' g
  cf : CertOK f
  cg : CertOK g
  ok : AtomsL tabs f g
  args : AtomArgsRefL tabs f g
  ctrls : TermStepRefL tabs f g
  low : f.lowered = true → g.lowered = true
  glow : g.lowered = true
  gen : ∀ x u, f.value? x = some u → termVL tabs u = false → u.op.generic = true
  shp : ∀ x u, f.value? x = some u → shp f.lowered tabs u.type = shp g.lowered tabs u.type

section
variable {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
include H

/-- An atom placed in `g` is placed in the same block of `f` as a corresponding atom, or is a
lowered frame address where `f` has a term (`frameAtomG`). -/
theorem gatom_cases {a : ID} {w : Value} (hp : Placed g a w) (ht : termVL tabs w = false) :
    (∃ u, Placed f a u ∧ termVL tabs u = false ∧ atomPair tabs u w = true) ∨
      frameAtomG tabs f a w = true := by
  obtain ⟨hw, hbm, blk, hblk, hx⟩ := hp
  have hbm' : w.block ∈ f.blocks := by rw [H.ok.blocks]; exact hbm
  obtain ⟨fc, gc, hfc, hgc, hBA⟩ := H.ok.block w.block hbm'
  rw [hblk] at hgc; cases hgc
  rcases hBA.sub a hx w hw ht with ⟨hxf, u, hu, hut, hs⟩ | hfa
  · have hub : u.block = w.block := (atomPair_spec hs).2.2.1
    exact .inl ⟨u, ⟨hu, by rw [hub]; exact hbm', fc, by rw [hub]; exact hfc, hxf⟩, hut, hs⟩
  · exact .inr hfa

/-- An atom placed in `g` where `f` has no term is placed in the same block of `f`, as a
corresponding atom. -/
theorem gatomL {a : ID} {w : Value} (hp : Placed g a w) (ht : termVL tabs w = false)
    (hnf : ¬ IsTermL tabs f.value? a) :
    ∃ u, Placed f a u ∧ termVL tabs u = false ∧ atomPair tabs u w = true :=
  (gatom_cases H hp ht).resolve_right fun hfa => hnf (frameAtomG_cases hfa).2.2.2

/-- An atom placed in `g` where `f` has a term is a lowered frame address (`frameAtomG`). -/
theorem gatom_frame {a : ID} {w : Value} (hp : Placed g a w) (ht : termVL tabs w = false)
    (hf : IsTermL tabs f.value? a) : frameAtomG tabs f a w = true :=
  (gatom_cases H hp ht).resolve_left fun ⟨_, hpu, hut, _⟩ => by
    obtain ⟨v, hv, hvt⟩ := hf
    rw [hpu.1] at hv; cases hv; rw [hut] at hvt; cases hvt

/-- `f` has no term where `g` has an atom other than a `MOVDaddr`. -/
theorem not_termL_f_of_op {a : ID} {w : Value} (hp : Placed g a w) (ht : termVL tabs w = false)
    (hop : w.op ≠ .ARM64MOVDaddr) : ¬ IsTermL tabs f.value? a := fun hf =>
  hop (frameAtomG_cases (gatom_frame H hp ht hf)).1

/-- An atom the target defines, where the source has no term, has the source's shape. -/
theorem shapeL_atom_def {a : ID} (hnf : ¬ IsTermL tabs f.value? a)
    (hat : ¬ IsTermL tabs (listedDefs g) a) (hdef : (listedDefs g a).isSome) :
    shapeL g.lowered (listedDefs g) tabs a = shapeL f.lowered f.value? tabs a := by
  cases hl : listedDefs g a with
  | none => rw [hl] at hdef; cases hdef
  | some w =>
    have ht : termVL tabs w = false := by
      cases h : termVL tabs w
      · rfl
      · exact absurd ⟨w, hl, h⟩ hat
    obtain ⟨u, hpu, -, hs⟩ := gatomL H (listed_placed hl) ht hnf
    simp only [shapeL, hl, hpu.1, Option.map_some, Option.getD_some]
    rw [H.shp a u hpu.1, (atomPair_spec hs).2.1]

/-- A corresponding atom of a lowered frame address (`argFree`) is the `LocalAddr` it lowers. -/
theorem addrLower_of_argFree {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hut : termVL tabs u = false) (hpair : atomPair tabs u w = true)
    (hf : argFree tabs w = true) : addrLower tabs u w = true := by
  cases hal : addrLower tabs u w
  · exfalso
    rcases (atomPair_spec hpair).1 with ⟨⟨hop | hop, -⟩ | hm | hz, -⟩ | ha | hb | hb | hq
    · have hg := H.gen x u hu hut
      rw [hop, (argFree_cases hf).1] at hg; exact absurd hg (by decide)
    · have hw' := (argFree_cases hf).1
      rcases renameOp_cases hop with ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ |
          ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | h9 <;> first
        | (rw [h2] at hw'; cases hw')
        | exact (atomicRen_facts h9).2.2.2.2.2.2.2.2.1 hw'
    · obtain ⟨-, -, -, n, hs, -⟩ := memLower_cases hm
      rw [(argFree_cases hf).1] at hs; cases hs
    · have hzw := bulkLower_op hz
      rw [(argFree_cases hf).1] at hzw; rcases hzw with h | h | h | h <;> cases h
    · rw [hal] at ha; cases ha
    · obtain ⟨-, -, -, ks, hks, -⟩ := pbLower_cases hb
      rw [(argFree_cases hf).1] at hks; cases hks
    · obtain ⟨-, -, -, -, -, p, s, -, hp, -⟩ := idxLower_cases hb
      exact (idxStore_facts hp).2.2.2.2.2.1 (argFree_cases hf).1
    · rcases (Sim.moveQLower_cases hq).2 with hw | hw <;>
        exact absurd ((argFree_cases hf).1.symm.trans hw.2.1) (by decide)
  · rfl

/-! ## Registers related through the term relations -/

section
variable {G T : Frame} {VS VT : ID → Prop}
  (hDS : DenOKL f.lowered f.value? tabs G VS) (hDT : DenOKL g.lowered (listedDefs g) tabs T VT)
  (hVT : ∀ a, VT a → ∃ w, Placed g a w)
  (hrel : ∀ a, VT a → VS a → ¬ IsTermL tabs f.value? a → ¬ IsTermL tabs (listedDefs g) a →
    Sem.Refines (rv G a) (rv T a))
  (htyS : RegsTyped ⟨f.lowered, false⟩ (Ctx.makeL tabs f) G)
  (htyT : RegsTyped ⟨g.lowered, false⟩ (Ctx.makeL tabs g) T)
include hDS hDT hVT hrel htyS htyT

private theorem tyS' : ∀ a, VS a → ¬ IsTermL tabs f.value? a →
    rty f.lowered (shapeL f.lowered f.value? tabs a) (rv G a) = rv G a := fun a ha _ => by
  rw [← tysL_shape]; exact htyS a _ (reg_rv (hDS a ha).1)

private theorem tyT' : ∀ a, VT a → ¬ IsTermL tabs (listedDefs g) a →
    rty g.lowered (shapeL g.lowered (listedDefs g) tabs a) (rv T a) = rv T a := fun a ha _ => by
  obtain ⟨v, hp⟩ := hVT a ha
  have : shapeL g.lowered (listedDefs g) tabs a = shapeL g.lowered g.value? tabs a := by
    simp [shapeL, placed_listed hp, hp.1]
  rw [this, ← tysL_shape]; exact htyT a _ (reg_rv (hDT a ha).1)

/-- The target's lowered frame addresses hold their words (`RegsFrameL`), and the source's
register of a corresponding atom (the `LocalAddr` lowered, `RegsFrame`) refines the word. -/
private theorem frameT_of (hfrS : RegsFrame tabs 0 f.value? G)
    (hfrT : RegsFrameL tabs 0 g.value? T) :
    ∀ a w n, listedDefs g a = some w → frameAuxL tabs w = some n →
      (VT a → rv T a = (framePtr tabs 0 n).word) ∧
      (VS a → ¬ IsTermL tabs f.value? a → Sem.Refines (rv G a) (framePtr tabs 0 n).word) := by
  intro a w n hl hwn
  obtain ⟨hop, hax, hwt, -, -⟩ := frameAuxL_eq_some.1 hwn
  have hpw := listed_placed hl
  refine ⟨fun ha => ?_, fun ha hnf => ?_⟩
  · obtain ⟨y, hy⟩ := (hDT a ha).1
    rw [rv_of hy]; exact hfrT a w n y hpw.1 hwn hy
  · obtain ⟨u, hpu, hut, hpair⟩ := gatomL H hpw hwt hnf
    have hal := addrLower_of_argFree H hpu.1 hut hpair
      (by unfold argFree; simp [hop, (movDaddr_atom hop hwt).1])
    obtain ⟨hlo, -, -, hwu, -, -⟩ := addrLower_cases hal
    obtain ⟨y, hy⟩ := (hDS a ha).1
    rw [rv_of hy]
    rcases hfrS.1 a u n y hpu.1 hlo (hwu.symm.trans hax) hy with h | ⟨h, -⟩
    · rw [h]; exact .poison _
    · rw [h]; exact Sem.Refines.refl _

/-- `ArgTermRefL` between registers of two frames whose atoms are refined, the frame addresses
those of activation 0 (`RegsFrame`, `RegsFrameL`). -/
theorem argTermRefL_regs (hfrS : RegsFrame tabs 0 f.value? G)
    (hfrT : RegsFrameL tabs 0 g.value? T) {o : Option (Int64 × Option AuxRef)} {x y : ID}
    (hT : ArgTermRefL o f.lowered f.value? tabs x g.lowered (listedDefs g) tabs y) (hx : VS x)
    (hy : VT y) : ArgRel tabs 0 o (rv G x) (rv T y) :=
  argTermRefL_apply H.low hDS hDT (fun a h1 h2 h3 h4 => hrel a h3 h1 h2 h4)
    (tyS' H hDS hDT hVT hrel htyS htyT) (tyT' H hDS hDT hVT hrel htyS htyT)
    (fun a _ hnf hat' hdef _ => shapeL_atom_def H hnf hat' hdef)
    (frameT_of H hDS hDT hVT hrel htyS htyT hfrS hfrT) H.glow hfrS hT hx hy

/-- `ArgTermFitL` between registers of two frames whose atoms are refined, the frame addresses
those of activation 0 (`RegsFrame`, `RegsFrameL`). -/
theorem argTermFitL_regs (hfrS : RegsFrame tabs 0 f.value? G)
    (hfrT : RegsFrameL tabs 0 g.value? T) {t : Ty} {x y : ID}
    (hT : ArgTermFitL t f.lowered f.value? tabs x g.lowered (listedDefs g) tabs y) (hx : VS x)
    (hy : VT y) : Sem.Refines (fitPiece t (rv G x)) (fitPiece t (rv T y)) :=
  argTermFitL_apply H.low hDS hDT (fun a h1 h2 h3 h4 => hrel a h3 h1 h2 h4)
    (tyS' H hDS hDT hVT hrel htyS htyT) (tyT' H hDS hDT hVT hrel htyS htyT)
    (fun a _ hnf hat' hdef _ => shapeL_atom_def H hnf hat' hdef)
    (frameT_of H hDS hDT hVT hrel htyS htyT hfrS hfrT) H.glow hfrS hT hx hy

/-- `ArgTermIdxL` between registers of two frames whose atoms are refined, the frame addresses
those of activation 0 (`RegsFrame`, `RegsFrameL`). -/
theorem argTermIdxL_regs (hfrS : RegsFrame tabs 0 f.value? G)
    (hfrT : RegsFrameL tabs 0 g.value? T) {s : Nat} {x y z : ID}
    (hT : ArgTermIdxL s f.lowered f.value? tabs x g.lowered (listedDefs g) tabs y z) (hx : VS x)
    (hy : VT y) (hz : VT z) : AddrRef tabs 0 none 0 (rv G x) (idxAddr s (rv T y) (rv T z)) :=
  argTermIdxL_apply H.low hDS hDT (fun a h1 h2 h3 h4 => hrel a h3 h1 h2 h4)
    (tyS' H hDS hDT hVT hrel htyS htyT) (tyT' H hDS hDT hVT hrel htyS htyT)
    (fun a _ hnf hat' hdef _ => shapeL_atom_def H hnf hat' hdef)
    (frameT_of H hDS hDT hVT hrel htyS htyT hfrS hfrT) H.glow hfrS hT hx hy hz

/-- `ArgTermQL` between registers of two frames whose atoms are refined, the frame addresses
those of activation 0 (`RegsFrame`, `RegsFrameL`). -/
theorem argTermQL_regs (hfrS : RegsFrame tabs 0 f.value? G)
    (hfrT : RegsFrameL tabs 0 g.value? T) {i : Nat} {s m y : ID}
    (hT : ArgTermQL i f.lowered f.value? tabs s m g.lowered (listedDefs g) tabs y) (hs : VS s)
    (hm : VS m) (hy : VT y) : Sem.Refines (qPart i (rv G s) (rv G m)) (rv T y) :=
  argTermQL_apply H.low hDS hDT (fun a h1 h2 h3 h4 => hrel a h3 h1 h2 h4)
    (tyS' H hDS hDT hVT hrel htyS htyT) (tyT' H hDS hDT hVT hrel htyS htyT)
    (fun a _ hnf hat' hdef _ => shapeL_atom_def H hnf hat' hdef)
    (frameT_of H hDS hDT hVT hrel htyS htyT hfrS hfrT) H.glow hfrS hT hs hm hy

/-- The terminators between two frames whose atoms are refined, the frame addresses those of
activation 0 (`RegsFrame`, `RegsFrameL`). -/
theorem termStepRefL_regs (hfrS : RegsFrame tabs 0 f.value? G)
    (hfrT : RegsFrameL tabs 0 g.value? T) {b : ID} (hb : b ∈ g.blocks)
    {fb gb : Block} (hfb : f.block? b = some fb) (hgb : g.block? b = some gb)
    (hx : ∀ c ∈ fb.controls, VS c) (hy : ∀ c ∈ gb.controls, VT c) :
    Res.Rel Next.Refines (stepTermL G fb) (stepTermL T gb) :=
  termStepRefL_apply H.low hDS hDT (fun a h1 h2 h3 h4 => hrel a h3 h1 h2 h4)
    (tyS' H hDS hDT hVT hrel htyS htyT) (tyT' H hDS hDT hVT hrel htyS htyT)
    (fun a _ hnf hat' hdef _ => shapeL_atom_def H hnf hat' hdef)
    (frameT_of H hDS hDT hVT hrel htyS htyT hfrS hfrT) H.glow hfrS
    (H.ctrls b hb fb gb hfb hgb).2 hx hy

/-- **Corresponding atoms, given the frames' relation** (the only use of `AtomArgsRefL`): the
arguments' registers of corresponding `Phi`s, read at the `Phi`'s shape, refine where both frames
hold them as terms over the atoms, and a non-`Phi` pair whose arguments the frames hold evaluates
to refinements (`atomPair_eval`, `addr_lower_eval`, `idx_atom_eval`). -/
theorem atom_ref (hfrS : RegsFrame tabs 0 f.value? G) (hfrT : RegsFrameL tabs 0 g.value? T)
    (hfr : T = { G with regs := T.regs }) {x : ID} {u w : Value} (hpw : Placed g x w)
    (hu : f.value? x = some u) (ht : termVL tabs w = false) (hut : termVL tabs u = false) :
    atomPair tabs u w = true ∧
    (w.op = .Phi → ∀ i < w.args.size,
      VS u.args[argIx u w i]! → VT w.args[i]! →
      Sem.Refines (rty f.lowered (shpL tabs w.type) (rv G u.args[argIx u w i]!))
        (rty g.lowered (shpL tabs w.type) (rv T w.args[i]!))) ∧
    (∀ env : Env, env.Mono → (∀ a ∈ u.args, VS a) → (∀ a ∈ w.args, VT a) → w.op ≠ .Phi →
      Res.Refines (evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) G u)
        (evalValueL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) T w)) := by
  obtain ⟨hw, hbm, blk, hblk, hx⟩ := hpw
  obtain ⟨u', hu', hpair, hpc, hTR⟩ := (H.args w.block hbm blk hblk x hx w hw ht).resolve_left
    fun hfa => by
      obtain ⟨v, hv, hvt⟩ := (frameAtomG_cases hfa).2.2.2
      rw [hu] at hv; cases hv; rw [hut] at hvt; cases hvt
  rw [hu] at hu'; cases hu'
  obtain ⟨-, hty, -, hid⟩ := atomPair_spec hpair
  have hargs2 : w.op ≠ .Phi → argFree tabs w = false → idxLower tabs u w = false →
      moveQLower tabs u w = false →
      ∀ i < w.args.size, VS u.args[argIx u w i]! → VT w.args[i]! →
      ArgRel tabs 0 (stArg u w i) (rv G u.args[argIx u w i]!) (rv T w.args[i]!) ∨
      ∃ t, atomFitTy tabs w i = some t ∧
        Sem.Refines (fitPiece t (rv G u.args[argIx u w i]!)) (fitPiece t (rv T w.args[i]!)) :=
    fun hph hf hix hmq i hi h1 h2 => by
    rcases hTR with hf' | ⟨-, -, hTR⟩ | ⟨hix', -⟩ | ⟨hmq', -⟩
    · rw [hf] at hf'; cases hf'
    · rcases hTR i hi with hTR | ⟨t, htf, hTR⟩
      · exact .inl (argTermRefL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT hTR h1 h2)
      · rw [argFitTy_atom ht hph] at htf
        exact .inr ⟨t, htf, argTermFitL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT hTR h1 h2⟩
    · rw [hix] at hix'; cases hix'
    · rw [hmq] at hmq'; cases hmq'
  have hargs : callLead w.op = none → (∀ j, stFitTy w.op j = none) → w.op ≠ .Phi →
      argFree tabs w = false → idxLower tabs u w = false → moveQLower tabs u w = false →
      ∀ i < w.args.size, VS u.args[argIx u w i]! → VT w.args[i]! →
      ArgRel tabs 0 (stArg u w i) (rv G u.args[argIx u w i]!) (rv T w.args[i]!) :=
    fun hcl hsv hph hf hix hmq i hi h1 h2 => (hargs2 hph hf hix hmq i hi h1 h2).resolve_right
      (by rintro ⟨t, ht, -⟩; simp [atomFitTy, hcl, hsv] at ht)
  have hphi : w.op = .Phi → ∀ i < w.args.size, VS u.args[argIx u w i]! → VT w.args[i]! →
      Sem.Refines (rty f.lowered (shpL tabs w.type) (rv G u.args[argIx u w i]!))
        (rty g.lowered (shpL tabs w.type) (rv T w.args[i]!)) := fun hph i hi h1 h2 => by
    have hf : argFree tabs w = false := by
      cases hf : argFree tabs w
      · rfl
      · exact absurd hph (by rw [(argFree_cases hf).1]; decide)
    have hix : idxLower tabs u w = false := by
      cases hix : idxLower tabs u w
      · rfl
      · exact absurd hph (idxLower_ops hix).2.1
    have huph : u.op = .Phi := (atomPair_phi hpair).1 hph
    rcases hTR with hf' | ⟨-, -, hTR⟩ | ⟨hix', -⟩ | ⟨hmq', -⟩
    · rw [hf] at hf'; cases hf'
    · rcases hTR i hi with hTR | ⟨t, htf, hTR⟩
      · have hr := argTermRefL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT hTR h1 h2
        rw [stArg_of_ne (by rw [huph]; decide)] at hr
        exact rty_le H.low _ hr
      · -- a `Phi`'s argument fitted to its shape: read at the shape (`retypeL_fitPiece`)
        rcases argFitTy_cases htf with ⟨hk, -⟩ | ⟨-, rfl⟩ | ⟨hr, -⟩ | ⟨-, hst⟩
        · rw [hph] at hk; cases hk
        · have hr := argTermFitL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT hTR h1 h2
          have hle : ∀ l (y : Val), Sem.Refines (rty l (shpL tabs w.type) y)
              (y.retypeL (shpL tabs w.type)) := fun l y => by
            cases l
            · simp only [rty, Bool.false_eq_true, ite_false]; exact retype_le_retypeL _ _
            · exact Sem.Refines.refl _
          rw [H.glow]
          refine (hle _ _).trans ?_
          show Sem.Refines _ ((rv T w.args[i]!).retypeL _)
          rw [← retypeL_fitPiece _ (rv G _), ← retypeL_fitPiece _ (rv T _)]
          exact retypeL_mono _ hr
        · rw [hph] at hr; cases hr
        · rcases stFitTy_ops hst with h | h | h | h | h | h | h | h <;> rw [hph] at h <;> cases h
    · rw [hix] at hix'; cases hix'
    · exact absurd hph (moveQLower_ops hmq').2.1
  refine ⟨hpair, hphi, fun env hE hS hT hnph => ?_⟩
  obtain ⟨w', hw', hwid, -⟩ := H.wg.valueId w.block blk ⟨hbm, hblk⟩ x hx
  rw [hw] at hw'; cases hw'
  have hty' : (Ctx.makeL tabs g).tys[w.id]?.getD .other =
      (Ctx.makeL tabs f).tys[u.id]?.getD .other := by
    rw [hid, hwid, tysL_of_value hw, tysL_of_value hu, H.shp x u hu, hty]
  cases hmq : moveQLower tabs u w
  case true =>
    rcases hTR with hf' | ⟨-, hmq', -⟩ | ⟨hix', -⟩ | ⟨-, hA, hV, hM⟩
    · rcases (Sim.moveQLower_cases hmq).2 with hw | hw <;>
        exact absurd ((argFree_cases hf').1.symm.trans hw.2.1) (by decide)
    · rw [hmq] at hmq'; cases hmq'
    · obtain ⟨hu', -⟩ := Sim.moveQLower_cases hmq
      rw [(idxLower_cases hix').1] at hu'; cases hu'
    · have h3 : u.args.size = 3 := by
        unfold moveQLower at hmq; simp only [Bool.and_eq_true, beq_iff_eq] at hmq
        exact hmq.1.1.1.2
      have hw3 : 3 ≤ w.args.size := by
        rcases (Sim.moveQLower_cases hmq).2 with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
      have hu : ∀ i < 3, VS u.args[i]! := fun i hi => hS _ (getElem!_mem' (by omega))
      have hw : ∀ i < w.args.size, VT w.args[i]! := fun i hi => hT _ (getElem!_mem' hi)
      exact moveQ_atom_eval H.glow hmq hty' (fun a ha => (hDS a (hS a ha)).1)
        (fun a ha => (hDT a (hT a ha)).1)
        (argTermRefL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT hA (hu 0 (by omega))
          (hw 0 (by omega)))
        (fun i hi => argTermQL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT (hV i hi)
          (hu 1 (by omega)) (hu 2 (by omega)) (hw _ (by omega)))
        (argTermRefL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT hM (hu 2 (by omega))
          (hw _ (by omega)))
  cases hix : idxLower tabs u w
  case true =>
    obtain ⟨-, h3, h4, -, -, p, s, -, hp, -⟩ := idxLower_cases hix
    rcases hTR with hf' | ⟨hix', -⟩ | ⟨-, hI, hV, hM⟩ | ⟨hmq', -⟩
    · exact absurd (argFree_cases hf').1 (idxStore_facts hp).2.2.2.2.2.1
    · rw [hix] at hix'; cases hix'
    · have hu : ∀ i < 3, VS u.args[i]! := fun i hi => hS _ (getElem!_mem' (by omega))
      have hw : ∀ i < 4, VT w.args[i]! := fun i hi => hT _ (getElem!_mem' (by omega))
      exact idx_atom_eval H.glow hix hty' (fun a ha => (hDS a (hS a ha)).1)
        (fun a ha => (hDT a (hT a ha)).1)
        (by rw [makeL_act]
            exact argTermIdxL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT hI (hu 0 (by omega))
              (hw 0 (by omega)) (hw 1 (by omega)))
        (by
          rcases hV with hV | ⟨t, htf, hV⟩
          · exact .inl (argTermRefL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT hV
              (hu 1 (by omega))
              (hw 2 (by omega)))
          · rw [argFitTy_atom ht hnph] at htf
            rcases atomFitTy_cases htf with ⟨hk, -⟩ | ⟨-, hst⟩
            · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hk
              rcases callLead_some hk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
                rw [h] at hp <;> cases hp
            · obtain ⟨wd, rfl, ⟨h12, -⟩ | ⟨-, hwd⟩⟩ := stFitTy_cases hst
              · cases h12
              · exact .inr ⟨wd, hwd, argTermFitL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT hV
                  (hu 1 (by omega)) (hw 2 (by omega))⟩)
        (argTermRefL_regs H hDS hDT hVT hrel htyS htyT hfrS hfrT hM (hu 2 (by omega))
          (hw 3 (by omega)))
    · rw [hmq] at hmq'; cases hmq'
  cases hal : addrLower tabs u w
  · have hf : argFree tabs w = false := by
      cases hf : argFree tabs w
      · rfl
      · rw [addrLower_of_argFree H hu hut hpair hf] at hal; cases hal
    cases hpb : pbLower u w
    · have hsz := atomPair_size hpair hal hpb hix hmq
      refine atomPair_eval hE H.ok.ownAux H.low H.glow hfr hpair hal hpb hix hmq (H.gen x u hu hut)
        hty' (fun a ha => (hDS a (hS a ha)).1) (fun a ha => (hDT a (hT a ha)).1) fun i hi => ?_
      have hi' : i < w.args.size := hsz ▸ hi
      rw [makeL_act]
      have := hargs2 hnph hf hix hmq i hi' (by rw [argIx_of_not hpb]; exact hS _ (getElem!_mem' hi))
        (hT _ (getElem!_mem' hi'))
      rwa [argIx_of_not hpb] at this
    · -- a bounds panic with constant operands
      obtain ⟨hu3, h3, -, ks, hks, hsz⟩ := pbLower_cases hpb
      have hpc' : ∃ l, pbConsts tabs w = some l ∧ ∀ p ∈ l, constArg tabs f u p.1 p.2 = true := by
        unfold pbConstOK at hpc
        rw [hpb] at hpc
        simp only [Bool.not_true, Bool.false_or] at hpc
        split at hpc
        · rename_i l hl
          exact ⟨l, hl, fun p hp => List.all_eq_true.1 hpc p hp⟩
        · cases hpc
      obtain ⟨l, hl, hcl⟩ := hpc'
      refine pb_lower_eval H.low H.glow hpb hty' (fun a ha => (hDS a (hS a ha)).1)
        (fun a ha => (hDT a (hT a ha)).1) (fun i hi => ?_) hl fun p hp => ?_
      · have hik : i < ks.length := hsz ▸ hi
        have hk3 := pbKeep_lt hks hik
        have hcl : callLead w.op = none := by
          cases hc : callLead w.op with
          | none => rfl
          | some k =>
            rcases callLead_some hc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hks <;> cases hks
        have hsv : ∀ j, stFitTy w.op j = none := fun j => by
          rcases pbKeep_cases hks with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
            simp [stFitTy, stValW, stIdxValW, h]
        have := hargs hcl hsv hnph hf hix hmq i hi
          (hS _ (getElem!_mem' (by rw [argIx_of_pb hpb hks hik, h3]; exact hk3)))
          (hT _ (getElem!_mem' hi))
        rwa [stArg_of_ne (by rw [hu3]; decide)] at this
      · obtain ⟨y, hy, hop, hk, -, hs⟩ := constArg_cases (hcl p hp)
        have hp3 : p.1 < u.args.size := by
          obtain ⟨a, -, hcase⟩ := pbConsts_cases hl
          rcases hcase with ⟨-, k, -, rfl⟩ | ⟨-, k, -, rfl⟩ | ⟨-, kx, ky, -, rfl⟩ <;>
            simp at hp <;> rcases hp with rfl | rfl <;> simp [h3]
        rw [rv_const64 hDS (hS _ (getElem!_mem' hp3)) hy hop hs, hk]
        exact Sem.Refines.refl _
  · exact addr_lower_eval H.ok.ownAux H.glow hal hty'
      (fun a ha => (hDS a (hS a ha)).1) (fun a ha => (hDT a (hT a ha)).1)

end

/-! ## Evaluating atoms the source did not -/

/-- A non-root atom of `g` other than `Arg`/`ArgIntReg` evaluates. -/
theorem evalOpL_safeL {env : Env} {ctx : Ctx} {fr : Frame} {u w : Value} {argv : List Val} {ty : Ty}
    (hp : atomPair tabs u w = true) (hgen : u.op.generic = true) (hr : isRoot w.op = false)
    (ha : w.op ≠ .Arg) (hai : w.op ≠ .ArgIntReg) :
    ∃ y, evalOpL false env ctx fr w argv ty = .ok y := by
  cases hz : bulkLower u w
  case true => exact evalOpL_bulk hz
  have hr' : isRoot u.op = false := by
    rcases atomPair_isRoot hp with h | h
    · rw [← h]; exact hr
    · rw [hz] at h; cases h
  rcases (atomPair_spec hp).1 with ⟨⟨hop | hop, -⟩ | hm | hz', -⟩ | ha | hb | hx | hq
  · rw [evalOpL_generic _ _ _ _ _ _ (hop ▸ hgen)]
    exact evalOp_safe hr ha hai
  · rcases evalOpL_rename (env := env) (ctx := ctx) (fr := fr) (argv := argv) (ty := ty) hop with
      ⟨k, hk, -⟩ | ⟨ho, he⟩ | ⟨ho, -⟩ | ⟨hat, -⟩
    · rcases hk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hr' <;> exact absurd hr' (by decide)
    · rw [he]
      rcases ho with ho | ho | ho | ho
      · rw [ho] at hr'; exact absurd hr' (by decide)
      · exact evalOp_safe (v := { w with op := u.op }) (by rw [ho]; decide)
          (by rw [ho]; decide) (by rw [ho]; decide)
      · exact evalOp_safe (v := { w with op := u.op }) (by rw [ho]; decide)
          (by rw [ho]; decide) (by rw [ho]; decide)
      · rw [ho] at hr'; exact absurd hr' (by decide)
    · rcases ho with ho | ho <;> rw [ho] at hr' <;> exact absurd hr' (by decide)
    · have := (atomicRen_facts hat).2.2.2.2.2.1
      rw [hr] at this; cases this
  · obtain ⟨-, -, hu, -⟩ := memLower_cases hm
    rw [hu] at hr'; exact absurd hr' (by decide)
  · rw [hz] at hz'; cases hz'
  · exact evalOpL_movDaddr_ok (addrLower_cases ha).2.1
  · obtain ⟨hu, -⟩ := pbLower_cases hb
    rw [hu] at hr'; exact absurd hr' (by decide)
  · obtain ⟨hu, -⟩ := idxLower_cases hx
    rw [hu] at hr'; exact absurd hr' (by decide)
  · obtain ⟨hu, -⟩ := Sim.moveQLower_cases hq
    rw [hu] at hr'; exact absurd hr' (by decide)

end

/-! ## Value sets -/

theorem closedL_sanc {ce : CheckEnv} {h : Func} (hwf : WF ce h) (hc : CertOK h) {tabs : Tables}
    {b : ID} {D : ID → Option Value} (hD : ∀ x v w, Placed h x v → D x = some w → w = v) :
    ClosedL tabs D (SAnc h b) := by
  intro x ⟨v, hp, hanc, hne⟩ w hw ht a ha
  have hwv := hD x v w hp hw
  subst hwv
  have hphi : w.op ≠ .Phi := fun he => by rw [termVL_phi he] at ht; cases ht
  obtain ⟨va, hpa, hanc'⟩ := arg_anc hwf hc hp (Anc.left hc.parents hanc) hphi ha
  refine ⟨va, hpa, Anc.trans hc.parents hanc' hanc, fun he => ?_⟩
  rw [he] at hanc'
  exact hne (Anc.antisymm hc.parents hanc hanc')

theorem closedL_sanc_f {ce : CheckEnv} {f : Func} (hwf : WF ce f) (hc : CertOK f) (tabs : Tables)
    (b : ID) : ClosedL tabs f.value? (SAnc f b) :=
  closedL_sanc hwf hc fun _ _ _ hp hw => placed_val hp hw

theorem closedL_sanc_g {ce : CheckEnv} {g : Func} (hwf : WF ce g) (hc : CertOK g) (tabs : Tables)
    (b : ID) : ClosedL tabs (listedDefs g) (SAnc g b) :=
  closedL_sanc hwf hc fun _ _ _ hp hw => by rw [placed_listed hp] at hw; cases hw; rfl

theorem stepTermL_goto_mem {fr : Frame} {b : Block} {e : Edge}
    (h : stepTermL fr b = .ok (.goto e)) : e ∈ b.succs := by
  unfold stepTermL at h
  split at h
  · split at h
    · cases hc : Sem.control fr b 0 with
      | ok v =>
        rw [hc] at h
        simp only [bind, Res.bind] at h
        split at h
        · exact succ_mem h
        · cases h
      | panic e m => rw [hc] at h; cases h
      | stuck msg => rw [hc] at h; cases h
    · cases hc : Sem.control fr b 0 with
      | ok v =>
        rw [hc] at h
        simp only [bind, Res.bind] at h
        split at h
        · exact succ_mem h
        · exact succ_mem h
        · cases h
      | panic e m => rw [hc] at h; cases h
      | stuck msg => rw [hc] at h; cases h
  · exact stepTerm_goto_mem h

/-! ## The target's schedule against a source reference frame -/

/-- Induction along `evalAllL` with an invariant of the evaluated prefix. -/
theorem evalAllL_induct {md : LMode} {env : Env} {ctx : Ctx} (L : List ID)
    (Inv : List ID → Frame → Prop)
    (hstep : ∀ d x s T, L = d ++ x :: s → Inv d T →
      ∃ y, stepVL md env ctx T x = .ok y ∧ Inv (d ++ [x]) (T.set x y)) :
    ∀ s d T, L = d ++ s → Inv d T → ∃ T', evalAllL md env ctx T s = .ok T' ∧ Inv L T'
  | [], d, T, hL, hI => ⟨T, rfl, by rw [hL, List.append_nil]; exact hI⟩
  | x :: s, d, T, hL, hI => by
    obtain ⟨y, hy, hI'⟩ := hstep d x s T hL hI
    rw [evalAllL_cons, hy]
    exact evalAllL_induct L Inv hstep s (d ++ [x]) _ (by rw [hL]; simp) hI'

/-- The loop invariant. -/
def LoopInvL (tabs : Tables) (f g : Func) (G T0 : Frame) (VS VT1 : ID → Prop) (d : List ID)
    (T : Frame) : Prop :=
  T = { T0 with regs := T.regs } ∧ T.regs.size = T0.regs.size ∧
    RegsTyped ⟨g.lowered, false⟩ (Ctx.makeL tabs g) T ∧
    DenOKL g.lowered (listedDefs g) tabs T (fun a => VT1 a ∨ a ∈ d) ∧
    (∀ a, a ∉ d → T.regs[a]? = T0.regs[a]?) ∧
    (∀ a, (VT1 a ∨ a ∈ d) → VS a → ¬ IsTermL tabs f.value? a → ¬ IsTermL tabs (listedDefs g) a →
      Sem.Refines (rv G a) (rv T a)) ∧
    RegsFrameL tabs 0 g.value? T

/-- **The target's schedule prefix `L`.** -/
theorem tgt_loop {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    {env : Env} (hE : env.Mono) {G T0 : Frame} {VS VT1 : ID → Prop} {og L M P : List ID}
    (hog : og = L ++ M) (hfr : T0 = { G with regs := T0.regs })
    (hsz : T0.regs.size = g.valueTab.size)
    (htyS : RegsTyped ⟨f.lowered, false⟩ (Ctx.makeL tabs f) G)
    (htyT : RegsTyped ⟨g.lowered, false⟩ (Ctx.makeL tabs g) T0)
    (hDS : DenOKL f.lowered f.value? tabs G VS) (hfrS : RegsFrame tabs 0 f.value? G)
    (hfrT0 : RegsFrameL tabs 0 g.value? T0)
    (hDT : DenOKL g.lowered (listedDefs g) tabs T0 VT1)
    (hVT1 : ∀ a, VT1 a → ∃ w, Placed g a w) (hdisj : ∀ x ∈ og, ¬ VT1 x)
    (hrel0 : ∀ a, VT1 a → VS a → ¬ IsTermL tabs f.value? a → ¬ IsTermL tabs (listedDefs g) a →
      Sem.Refines (rv G a) (rv T0 a))
    (hnd : og.Nodup) (htopo : TopoRem (argsF g) og)
    (hplaced : ∀ x ∈ og, ∃ w, Placed g x w ∧ w.id = x ∧ w.op ≠ .Phi)
    (hargsT : ∀ x ∈ og, ∀ w, g.value? x = some w → ∀ a ∈ w.args, VT1 a ∨ a ∈ og)
    (hVSog : ∀ a ∈ og, VS a → ¬ IsTermL tabs f.value? a → ¬ IsTermL tabs (listedDefs g) a →
      a ∈ P)
    (hatom : ∀ x ∈ L, ∀ w, g.value? x = some w → termVL tabs w = false →
      ¬ IsTermL tabs f.value? x →
      ∃ u, f.value? x = some u ∧
        (x ∈ P → (∀ a ∈ u.args, VS a) ∧
          ∃ y, G.regs[x]? = some (some y) ∧
            evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) G u = .ok y) ∧
        (x ∉ P → isRoot w.op = false ∧ w.op ≠ .Arg ∧ w.op ≠ .ArgIntReg)) :
    ∃ T', evalAllL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) T0 L = .ok T' ∧
      LoopInvL tabs f g G T0 VS VT1 L T' := by
  refine evalAllL_induct L (LoopInvL tabs f g G T0 VS VT1) ?_ L [] T0 rfl
    ⟨by cases T0; rfl, rfl, htyT,
      hDT.iff fun a => ⟨.inl, fun h => h.elim id fun h => absurd h List.not_mem_nil⟩,
      fun _ _ => rfl, fun a ha => hrel0 a (ha.elim id fun h => absurd h List.not_mem_nil), hfrT0⟩
  intro d x s T hL ⟨hTf, hTs, hTt, hTD, hTk, hTr, hTF⟩
  have hog' : og = d ++ x :: (s ++ M) := by rw [hog, hL]; simp
  have hxog : x ∈ og := by rw [hog']; simp
  have hxL : x ∈ L := by rw [hL]; simp
  have hxd : x ∉ d := fun hm => by
    rw [hog'] at hnd
    exact (List.nodup_append.1 hnd).2.2 x hm x List.mem_cons_self rfl
  have hxV : ¬ (VT1 x ∨ x ∈ d) := fun h => h.elim (hdisj x hxog) hxd
  obtain ⟨w, hpw, hwid, hwphi⟩ := hplaced x hxog
  have hw := hpw.1
  have hxlt : x < T.regs.size := by rw [hTs, hsz]; exact lt_of_value? hw
  have hargs : ∀ a ∈ w.args, VT1 a ∨ a ∈ d := fun a ha => by
    rcases hargsT x hxog w hw a ha with h | h
    · exact .inl h
    · rw [hog'] at htopo h
      exact .inr (topoRem_before htopo (by rw [argsF_of hw]; exact Array.mem_toList_iff.2 ha) h)
  have hreg : ∀ a ∈ w.args, Reg T a := fun a ha => (hTD a (hargs a ha)).1
  have hstepV : stepVL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) T x =
      evalValueL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) T w := by
    rw [stepVL_of (by rw [makeL_f]; exact hw)]
  have hty : (Ctx.makeL tabs g).tys[w.id]?.getD .other = shp g.lowered tabs w.type := by
    rw [hwid, tysL_of_value hw]; rfl
  -- the common part of the invariant after setting `x`
  have common : ∀ y, rty g.lowered (shp g.lowered tabs w.type) y = y →
      (T.set x y = { T0 with regs := (T.set x y).regs }) ∧ (T.set x y).regs.size = T0.regs.size ∧
      RegsTyped ⟨g.lowered, false⟩ (Ctx.makeL tabs g) (T.set x y) ∧
      (∀ a, a ∉ d ++ [x] → (T.set x y).regs[a]? = T0.regs[a]?) := fun y hy => by
    refine ⟨by rw [hTf]; rfl, by simp [Frame.set, hTs],
      regsTyped_set hTt (by rw [← hwid, hty]; exact hy), fun a ha => ?_⟩
    have hxa : x ≠ a := fun he => ha (by simp [he])
    rw [Frame.set_regs_ne hxa]; exact hTk a (fun hm => ha (by simp [hm]))
  have hkeep : ∀ y a, (VT1 a ∨ a ∈ d) → (T.set x y).regs[a]? = T.regs[a]? := fun y a ha =>
    Frame.set_regs_ne fun he => hxV (he ▸ ha)
  have hiff : ∀ a, ((VT1 a ∨ a ∈ d) ∨ a = x) ↔ (VT1 a ∨ a ∈ d ++ [x]) := fun a => by
    simp only [List.mem_append, List.mem_singleton, or_assoc]
  cases hterm : termVL tabs w with
  | true =>
    have hev : evalValueL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) T w =
        .ok (rty g.lowered (shp g.lowered tabs w.type) (opValL tabs w.op (shp g.lowered tabs w.type)
          w.auxInt w.aux (w.args.toList.map (rv T)))) := by
      have := evalValueL_termL_eq (low := g.lowered) (env := env) (ctx := Ctx.makeL tabs g)
        (by rw [makeL_tabs]; exact hterm) (makeL_act tabs g) hreg
      rw [makeL_tabs, hty] at this
      exact this
    have hF' : ∀ y, RegsFrameL tabs 0 g.value? (T.set x y) := fun y a w' n y0 hw' hwn hy => by
      by_cases hax : x = a
      · subst hax
        rw [hw] at hw'; cases hw'
        rw [(frameAuxL_eq_some.1 hwn).2.2.1] at hterm; cases hterm
      · rw [Frame.set_regs_ne hax] at hy; exact hTF a w' n y0 hw' hwn hy
    refine ⟨_, by rw [hstepV, hev], ?_⟩
    obtain ⟨c1, c2, c3, c4⟩ := common _ (rty_idem _ _ _)
    refine ⟨c1, c2, c3, ?_, c4, fun a ha hVS hatD hatE => ?_, hF' _⟩
    · exact (hTD.term (hkeep _) hxV (placed_listed hpw) hterm hargs
        (Frame.set_regs_self hxlt)).iff hiff
    · have hax : x ≠ a := fun he => hatE (he ▸ ⟨w, placed_listed hpw, hterm⟩)
      rw [rv_set_ne hax]
      refine hTr a ?_ hVS hatD hatE
      rcases (hiff a).2 ha with h | h
      · exact h
      · exact absurd h.symm hax
  | false =>
    have hatE : ¬ IsTermL tabs (listedDefs g) x := fun ⟨w', hw', ht'⟩ => by
      rw [placed_listed hpw] at hw'; cases hw'; rw [hterm] at ht'; cases ht'
    -- the target's value and its refinement where the source evaluated `x` as an atom
    obtain ⟨y', hev, hy'⟩ : ∃ y', evalValueL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) T w = .ok y' ∧
        (¬ IsTermL tabs f.value? x → x ∈ P → ∃ y, G.regs[x]? = some (some y) ∧ Sem.Refines y y') := by
      by_cases hfx : IsTermL tabs f.value? x
      · -- a lowered frame address where `f` has a term (`frameAtomG`): it evaluates
        have hop := (frameAtomG_cases (gatom_frame H hpw hterm hfx)).1
        obtain ⟨r, hr'⟩ := evalOpL_movDaddr_ok (env := env) (ctx := Ctx.makeL tabs g) (fr := T)
          (argv := w.args.toList.map (rv T)) (ty := (Ctx.makeL tabs g).tys[w.id]?.getD .other) hop
        refine ⟨rty g.lowered ((Ctx.makeL tabs g).tys[w.id]?.getD .other) r, ?_,
          fun h => absurd hfx h⟩
        rw [evalValueL_of_regs hreg]
        change ((evalOpL false env (Ctx.makeL tabs g) T w _ _).bind _) = _
        rw [hr']; rfl
      obtain ⟨u, hu, hin, hout⟩ := hatom x hxL w hw hterm hfx
      obtain ⟨u2, hpu2, hut2, hpair⟩ := gatomL H hpw hterm hfx
      obtain rfl : u2 = u := by rw [hpu2.1] at hu; exact Option.some.inj hu
      by_cases hxP : x ∈ P
      · obtain ⟨hargsS, y, hGy, hevS⟩ := hin hxP
        have hVTd : ∀ a, (VT1 a ∨ a ∈ d) → ∃ w, Placed g a w := fun a ha => by
          rcases ha with ha | ha
          · exact hVT1 a ha
          · obtain ⟨w, hp, -⟩ := hplaced a (by rw [hog']; exact List.mem_append_left _ ha)
            exact ⟨w, hp⟩
        have hr := (atom_ref H hDS hTD hVTd (fun a h1 h2 h3 h4 => hTr a h1 h2 h3 h4) htyS hTt
          hfrS hTF (by rw [hTf, hfr]) hpw hpu2.1 hterm hut2).2.2 env hE hargsS hargs hwphi
        rw [hevS] at hr
        obtain ⟨y', hT, hyy⟩ := res_ok_of_refines hr
        exact ⟨y', hT, fun _ _ => ⟨y, hGy, hyy⟩⟩
      · obtain ⟨hr, ha, hai⟩ := hout hxP
        obtain ⟨r, hr'⟩ := evalOpL_safeL H (env := env) (ctx := Ctx.makeL tabs g) (fr := T)
          (argv := w.args.toList.map (rv T)) (ty := (Ctx.makeL tabs g).tys[w.id]?.getD .other)
          hpair (H.gen x u2 hpu2.1 hut2) hr ha hai
        refine ⟨rty g.lowered ((Ctx.makeL tabs g).tys[w.id]?.getD .other) r, ?_,
          fun _ h => absurd h hxP⟩
        rw [evalValueL_of_regs hreg]
        change ((evalOpL false env (Ctx.makeL tabs g) T w _ _).bind _) = _
        rw [hr']; rfl
    refine ⟨y', by rw [hstepV, hev], ?_⟩
    have hyt : rty g.lowered (shp g.lowered tabs w.type) y' = y' := by
      rw [← hty]; exact evalValueL_typed hev
    obtain ⟨c1, c2, c3, c4⟩ := common y' hyt
    -- a lowered frame address holds its word
    have hF' : RegsFrameL tabs 0 g.value? (T.set x y') := fun a w' n y hw' hwn hy => by
      by_cases hax : x = a
      · subst hax
        rw [hw] at hw'; cases hw'
        rw [Frame.set_regs_self hxlt] at hy; cases hy
        have hev' := hev
        rw [H.glow] at hev'
        have := evalValueL_frameAuxL (ctx := Ctx.makeL tabs g) (by rw [makeL_tabs]; exact hwn)
          (makeL_act tabs g) (by rw [makeL_tabs, hty, H.glow]; try rfl) hev'
        rwa [makeL_tabs] at this
      · rw [Frame.set_regs_ne hax] at hy; exact hTF a w' n y hw' hwn hy
    refine ⟨c1, c2, c3, ?_, c4, fun a ha hVS hatD hatE' => ?_, hF'⟩
    · exact (hTD.extend (W := fun a => a = x) (hkeep _) fun a ha _ => by
        subst ha; exact ⟨hatE, _, Frame.set_regs_self hxlt⟩).iff hiff
    · by_cases hax : x = a
      · subst hax
        obtain ⟨y, hGy, hyy⟩ := hy' hatD (hVSog x hxog hVS hatD hatE)
        rw [rv_of hGy, rv_of (Frame.set_regs_self hxlt)]; exact hyy
      · rw [rv_set_ne hax]
        refine hTr a ?_ hVS hatD hatE'
        rcases (hiff a).2 ha with h | h
        · exact h
        · exact absurd h.symm hax

end GoFV.Proof.Low.Sim
