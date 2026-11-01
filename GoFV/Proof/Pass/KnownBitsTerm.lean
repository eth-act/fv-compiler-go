import GoFV.Proof.Pass.KnownBitsInv
import GoFV.Proof.Pass.RewriteTerm

/-!
# known bits: atoms' arguments and controls as terms (issue #26)

The premises `AtomArgsRefP` and `ControlsRefP` of the atom simulation under known bits'
invariant `kbInv`. For valuations whose atoms have the bits their entries claim, every value
has them as a term too (`kb_den`, by the transfer functions' soundness, `kb_term`), so a value
whose entry is fully known denotes `poison` or that constant (`const_ref`). Hence each value
listed in `f` (`LM f`, closed under arguments by `closedOK f`) is refined, one fuel later, by the
same value in `g` (`kb_ref`): unchanged, or `Copy` of the constant `repOK` allows. Atoms of `g`
are unchanged atoms of `f` and controls are equal (`blocksOK`).
-/

namespace GoFV.Proof.KnownBits

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.KnownBits GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim GoFV.Proof.Pass.Rewrite

/-! ## Constants -/

theorem const_int_eq {w : Width} {x : BitVec w.bits} {ai : Int64}
    (h : x.signExtend 64 = ai.toBitVec) : (Conv.const w ai).retype (.int w) = .int w x := by
  have hle := width_le w
  have hx : BitVec.ofInt w.bits ai.toInt = x := by
    rw [Int64.toInt, ← h, BitVec.toInt_signExtend_of_le hle, BitVec.ofInt_toInt]
  simp [Conv.const, Val.retype, hx]

theorem constBool_eq {b : Bool} {ai : Int64}
    (h : (if b then (1 : BitVec 64) else 0) = ai.toBitVec) :
    (Conv.constBool ai).retype .bool = .bool b := by
  have hb : (ai != 0) = b := by
    cases b
    · have : ai = 0 := Int64.toBitVec_inj.1 (by simpa using h.symm)
      simp [this]
    · have : ai = 1 := Int64.toBitVec_inj.1 (by simpa using h.symm)
      simp [this]
  simp [Conv.constBool, Val.retype, hb]

theorem ref_const_int {w : Width} {y : Val} {z : BitVec 64} {ai : Int64}
    (hy : y.hasTy (.int w) = true) (hz : rep y = some z) (hai : ai.toBitVec = z) :
    Sem.Refines y ((Conv.const w ai).retype (.int w)) := by
  cases y with
  | int w' x =>
    simp only [Val.hasTy, beq_iff_eq] at hy
    subst hy
    simp only [rep, Option.some.injEq] at hz
    rw [const_int_eq (hz.trans hai.symm)]
    exact Sem.Refines.refl _
  | bool b => simp [Val.hasTy] at hy
  | _ => simp [rep] at hz

theorem ref_const_bool {y : Val} {z : BitVec 64} {ai : Int64}
    (hy : y.hasTy .bool = true) (hz : rep y = some z) (hai : ai.toBitVec = z) :
    Sem.Refines y ((Conv.constBool ai).retype .bool) := by
  cases y with
  | bool b =>
    simp only [rep, Option.some.injEq] at hz
    rw [constBool_eq (hz.trans hai.symm)]
    exact Sem.Refines.refl _
  | int w x => simp [Val.hasTy] at hy
  | _ => simp [rep] at hz

/-- What `constOK` establishes: a term constant without arguments of shape `t`, refined by every
value of shape `t` that has all bits of `val`. -/
theorem const_ref {tabs : Tables} {g : Func} {t : Ty} {val : BitVec 64} {c : ID}
    (hc : constOK tabs g t val c = true) :
    ∃ cv, g.value? c = some cv ∧ termOp cv.op = true ∧ GoFV.Proof.Rules.frameOp cv.op = false ∧
      cv.args = #[] ∧ tabs.ty cv.type = t ∧
      ∀ y : Val, y.hasTy t = true → Gam (val, BitVec.allOnes 64) y →
        Sem.Refines y ((evalPure cv.op t cv.auxInt cv.aux []).retype t) := by
  unfold constOK at hc
  cases hcv : g.value? c with
  | none => rw [hcv] at hc; cases hc
  | some cv =>
    rw [hcv] at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨hargs, -⟩, hty⟩, hai⟩, hop⟩ := hc
    replace hty := Pass.Rewrite.tyEq_sound hty
    refine ⟨cv, rfl, ?_, ?_, Array.isEmpty_iff.1 hargs, hty, fun y hy hG => ?_⟩
    · split at hop <;> first | (cases hop; done) | (rename_i h; rw [h]; decide)
    · split at hop <;> first | (cases hop; done) | (rename_i h; rw [h]; decide)
    rcases hG with rfl | hk | ⟨z, hz, ha⟩
    · exact .poison _
    · simp at hk
    have hz' := eq_of_full ha
    subst hz'
    split at hop
    all_goals first
      | (cases hop; done)
      | skip
    all_goals
      rename_i hco
      rw [hco]
      first
        | exact ref_const_int hy hz hai
        | exact ref_const_bool hy hz hai

/-! ## Denotations -/

theorem evalPure_copy (ty : Ty) (ai : Int64) (aux : Option AuxRef) (y : Val) :
    evalPure .Copy ty ai aux [y] = y := rfl

theorem not_term_of {D : ID → Option Value} {x : ID} {v : Value} (hv : D x = some v)
    (ht : ¬ termOp v.op = true) : ¬ IsTerm D x := fun ⟨w, hw, hw'⟩ => by
  rw [hv] at hw; cases hw; exact ht hw'

theorem blocks_eq {f g : Func} (hA : atomsOK f g = true) : f.blocks = g.blocks := by
  unfold atomsOK at hA
  simp only [Bool.and_eq_true, beq_iff_eq] at hA
  exact hA.1.1.2

theorem blocksOK_facts {f g : Func} (h : blocksOK f g = true) {b : ID} (hb : b ∈ f.blocks)
    {fb : Block} (hfb : f.block? b = some fb) :
    ∃ gb, g.block? b = some gb ∧ fb.kind = gb.kind ∧ fb.succs = gb.succs ∧ fb.id = gb.id ∧
      fb.controls = gb.controls ∧ ∀ x ∈ fb.values, x ∈ gb.values := by
  unfold blocksOK at h
  have := (Array.all_eq_true_iff_forall_mem.1 h) b hb
  rw [hfb] at this
  cases hgb : g.block? b with
  | none => rw [hgb] at this; cases this
  | some gb =>
    rw [hgb] at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨⟨⟨hk, hs⟩, hid⟩, hc⟩, hv⟩ := this
    refine ⟨gb, rfl, hk, hs, hid, hc, fun x hx => ?_⟩
    rw [hv] at hx
    obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 hx
    exact Array.getElem_mem _

/-- A value listed in `f` is listed in `g`, as `g`'s value. -/
theorem marked_g {f g : Func} (hA : atomsOK f g = true) (hB : blocksOK f g = true) {x : ID}
    {b : ID} (hb : b ∈ f.blocks) {fb : Block} (hfb : f.block? b = some fb)
    (hx : x ∈ fb.values) {w : Value} (hw : g.value? x = some w) (hwb : w.block = b) :
    ∃ gb, g.block? b = some gb ∧ x ∈ gb.values ∧ Marked g x := by
  obtain ⟨gb, hgb, -, -, -, -, hsub⟩ := blocksOK_facts hB hb hfb
  have hxg := hsub x hx
  exact ⟨gb, hgb, hxg, b, blocks_eq hA ▸ hb, gb, hgb, hxg, w, hw, hwb⟩

/-- Same kinds, successors and IDs (`blocksOK`) and controls refining as terms: the
terminators refine. -/
theorem steps_of_controls {tabs : Tables} {f g : Func} {I : SrcInv tabs f}
    (hA : atomsOK f g = true) (hB : blocksOK f g = true) (h : ControlsRefP I g) :
    StepRefsP I g :=
  ControlsRefP.toStepRefsP h fun b hb fb gb hfb hgb => by
    obtain ⟨gb', hgb', hk, hs, hid, -⟩ := blocksOK_facts hB (blocks_eq hA ▸ hb) hfb
    rw [hgb] at hgb'; cases hgb'
    exact ⟨hk.symm, hs.symm, hid.symm⟩

section
variable {tabs : Tables} {f g : Func} {E : Array (Int64 × Int64)} {R : Array Bool} {ce : CheckEnv}
  (hwf : WF ce f) (K : KbFacts tabs f g E R)
include hwf K

/-- Every value has, as a term, the bits its entry claims if the atoms have theirs. -/
theorem kb_den {ρ : ID → Val} (hP : ∀ a, ¬ IsTerm f.value? a → Gam (ent E a) (ρ a)) :
    ∀ n x, Gam (ent E x) (den f.value? tabs ρ n x)
  | 0, _ => Gam.poison _
  | n + 1, x => by
    by_cases ht : IsTerm f.value? x
    · obtain ⟨v, hv, hop⟩ := ht
      rw [den_succ_term hv hop]
      exact kb_term hwf K hv hop _ fun a _ => kb_den hP n a
    · rw [den_succ_atom ht]; exact hP x ht

/-- **Values as terms**: each value listed in `f` is refined, one fuel later, by the same value
listed in `g`, for valuations whose atoms have the bits their entries claim. -/
theorem kb_ref {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ') (hT : Term.Typed f.value? tabs ρ)
    (hP : ∀ a, ¬ IsTerm f.value? a → Gam (ent E a) (ρ a)) :
    ∀ n x, LM f x → Sem.Refines (den f.value? tabs ρ n x) (den (listedDefs g) tabs ρ' (n + 1) x)
  | 0, _, _ => .poison _
  | n + 1, x, hx => by
    obtain ⟨b, hb, fb, hfb, hxv, u, hu, hub⟩ := listedMarks_sound f x hx
    have hrep := K.rep x (lt_of_value? hu)
    unfold repOK at hrep
    rw [hu] at hrep
    cases hw : g.value? x with
    | none => rw [hw] at hrep; cases hrep
    | some w =>
      rw [hw] at hrep
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrep
      obtain ⟨⟨-, hblk⟩, hrep⟩ := hrep
      obtain ⟨gb, hgb, hxg, hmg⟩ := marked_g K.atoms K.blocks hb hfb hxv hw (hblk.trans hub)
      have hL : listedDefs g x = some w := by rw [listedDefs_of_marked hmg, hw]
      rcases hrep with ⟨⟨⟨⟨hop, hty⟩, hai⟩, hax⟩, hargs⟩ | ⟨⟨⟨⟨hop, hsz⟩, hfull⟩, hty⟩, hc⟩
      · by_cases ht : termOp u.op = true
        · rw [den_succ_term hu ht, den_succ_term hL (hop ▸ ht), hop, hty, hai, hax, hargs]
          apply retype_mono; apply GoFV.Proof.Rules.opVal_mono
          refine refinesList_map fun a ha => kb_ref hρ hT hP n a ?_
          exact (closedOK_facts K.cf b hb fb hfb).2 x hxv u hu a (Array.mem_toList_iff.1 ha)
        · rw [den_succ_atom (not_term_of hu ht), den_succ_atom (not_term_of hL (hop ▸ ht))]
          exact hρ x
      · -- `x` became `Copy c` of a constant `c` of its fully known entry
        have hty := Pass.Rewrite.tyEq_sound hty
        obtain ⟨cv, hcv, hct, hcf, hcargs, hcty, hcref⟩ := const_ref hc
        have hc0 : w.args.toList = [w.args[0]?.getD 0] := by
          have h0 : 0 < w.args.size := by omega
          rw [Array.getElem?_eq_getElem h0, Option.getD_some]
          apply List.ext_getElem (by simp [hsz])
          intro i h1 h2
          have : i = 0 := by simp [hsz] at h1; omega
          subst this; simp
        have hcm : LM g (w.args[0]?.getD 0) := by
          refine (closedOK_facts K.cg b (blocks_eq K.atoms ▸ hb) gb hgb).2 x hxg w hw _ ?_
          rw [← Array.mem_toList_iff, hc0]; exact List.mem_cons_self
        have hLc : listedDefs g (w.args[0]?.getD 0) = some cv := by
          rw [listedDefs_of_marked (listedMarks_sound g _ hcm), hcv]
        have hcopy : termOp Op.Copy = true := by decide
        rw [den_succ_term hL (hop ▸ hcopy), hop, hc0, List.map_cons, List.map_nil,
          den_succ_term hLc hct, hcargs, hcty, hty]
        simp only [GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, GoFV.Proof.Rules.opVal_pure hcf,
          evalPure_copy, Array.toList_empty, List.map_nil, Val.retype_idem]
        -- the source's value has shape `t` and all bits of the entry
        have hG := kb_den hwf K hP (n + 1) x
        have hE : ent E x = ((ent E x).1, BitVec.allOnes 64) := Prod.ext rfl hfull
        rw [hE] at hG
        refine hcref _ ?_ hG
        by_cases ht : termOp u.op = true
        · rw [den_succ_term hu ht]; exact Val.retype_hasTy _ _
        · rw [den_succ_atom (not_term_of hu ht)]
          have h1 := hT x (not_term_of hu ht) (by rw [hu]; rfl)
          simp only [shape, hu, Option.map_some, Option.getD_some] at h1
          rw [← h1]; exact Val.retype_hasTy _ _

theorem kb_termRefP {x : ID} (hx : LM f x) (b : ID) (Q : (ID → Val) → Prop) (S : ID → Prop) :
    TermRefP ((kbInv hwf K).P b) Q S f.value? tabs x (listedDefs g) tabs x :=
  fun _ _ hρ hT _ hP _ _ _ n => ⟨n + 1, kb_ref hwf K hρ hT hP n x hx⟩

/-- **Atoms' arguments.** -/
theorem kb_atomArgs : AtomArgsRefP (kbInv hwf K) g := by
  intro b hb gb hgb a ha u hu ht
  obtain ⟨fb, hfb, -, hatoms⟩ := atomsOK_facts K.atoms b hb gb hgb
  obtain ⟨haf, u', hu', hop, hty, hai, hax, hsz⟩ := hatoms a ha u hu ht
  refine ⟨u', hu', hop, hty, hai, hax, hsz, fun i hi => ?_⟩
  have hrep := K.rep a (lt_of_value? hu')
  unfold repOK at hrep
  rw [hu', hu] at hrep
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrep
  have hargs : u.args = u'.args := by
    rcases hrep.2 with ⟨-, h⟩ | ⟨⟨⟨⟨h, -⟩, -⟩, -⟩, -⟩
    · exact h
    · rw [h] at ht; cases ht
  have hbf : b ∈ f.blocks := blocks_eq K.atoms ▸ hb
  have hi' : i < u'.args.size := hargs ▸ hi
  rw [hargs]
  have hx := (closedOK_facts K.cf b hbf fb hfb).2 a haf u' hu' u'.args[i]!
    (by rw [getElem!_pos u'.args i hi']; exact Array.getElem_mem hi')
  exact ⟨fun _ => kb_termRefP hwf K hx b _ _, fun _ p _ _ _ _ _ => kb_termRefP hwf K hx p _ _⟩

/-- **Controls.** -/
theorem kb_controls : ControlsRefP (kbInv hwf K) g := by
  intro b hb fb gb hfb hgb
  have hbf : b ∈ f.blocks := blocks_eq K.atoms ▸ hb
  obtain ⟨gb', hgb', -, -, -, hctl, -⟩ := blocksOK_facts K.blocks hbf hfb
  rw [hgb] at hgb'; cases hgb'
  refine ⟨by rw [hctl], fun k hk => ?_⟩
  rw [← hctl]
  have hk' : k < fb.controls.size := hctl ▸ hk
  exact kb_termRefP hwf K ((closedOK_facts K.cf b hbf fb hfb).1 _
    (by rw [getElem!_pos fb.controls k hk']; exact Array.getElem_mem hk')) b _ _

/-- **Terminators**. -/
theorem kb_steps : StepRefsP (kbInv hwf K) g := steps_of_controls K.atoms K.blocks (kb_controls hwf K)

end

end GoFV.Proof.KnownBits
