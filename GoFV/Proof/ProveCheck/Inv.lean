import GoFV.Proof.ProveCheck.Spec
import GoFV.Proof.AtomSimSet
import GoFV.Proof.Merge

/-!
# The source-side invariant of prove's validator (issue #24)

`proveInv`: while the source runs block `b`, every register `a` holds a value `y` that is
fixed by `retype` at `a`'s shape, is `.bool v` for every path fact `(a, v)` of `b`, and lies
in `r` for every `Phi` invariant `(a, w, r)` (`PInv`). It holds at the entry (no facts), is
kept by evaluating values (a block's own values are never its facts, `Phi`s are never terms),
and along each edge: the target's facts are the source block's plus the branch just taken, and
each `Phi`'s new value lies in its invariant's range because the range analysis is sound
(`rng_sound`) under the source block's facts (`InvSpec`). Its frame-level part (`QRel`): the
relations of `b` hold of the registers. Poisoning registers keeps them (`den` is monotone,
`qrel_pois`); evaluating a value of `b` keeps them, since neither the `Phi` nor the values of
strict ancestors are touched (`qrel_step`); along an edge the target's relations are the source
block's or are re-derived for the target's `Phi`s by `diffDecides` (`qrel_edge`).
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck
  GoFV.Proof GoFV.Proof.Dom GoFV.Proof.Term GoFV.Proof.AtomSim

/-- The invariant at block `b` of register `a` holding `y`. -/
def PInv (tabs : Tables) (f : Func) (F : Array (List (ID × Bool))) (inv : List (ID × Width × Rng))
    (b a : ID) (y : Val) : Prop :=
  y.retype (shape f.value? tabs a) = y ∧
  (b ∈ f.blocks → ∀ v, (a, v) ∈ factsAt F b → y = .bool v) ∧
  (∀ w r, (a, w, r) ∈ inv → ∀ yv : BitVec w.bits, y = .int w yv → r.Mem yv)

section
variable {tabs : Tables} {f g : Func} {ce : CheckEnv} {F : Array (List (ID × Bool))}
  {inv : List (ID × Width × Rng)} {RB : Array (List (ID × ID × Width × Int))}

theorem shape_of {x : ID} {v : Value} (h : f.value? x = some v) :
    shape f.value? tabs x = tabs.ty v.type := by simp [shape, h]

/-- A fact of a block of `f` is not one of its values. -/
theorem fact_not_mem (hwf : WF ce f) (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) {b : ID} {bb : Block}
    (hb : b ∈ f.blocks) (hbb : f.block? b = some bb) {x : ID} (hx : x ∈ bb.values) {v : Bool}
    (hf : (x, v) ∈ factsAt F b) : False :=
  (factOK_spec (hR.hF.fact b hb (hR.tree b hb) bb hbb x v hf) hc.parents).1 hx

/-- A fact is a term placed in a strict ancestor. -/
theorem fact_placed (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) {b : ID} {bb : Block}
    (hb : b ∈ f.blocks) (hbb : f.block? b = some bb) {x : ID} {v : Bool}
    (hf : (x, v) ∈ factsAt F b) :
    ∃ cv, Placed f x cv ∧ cv.block ≠ b ∧ Anc (make f) cv.block b ∧ termOp cv.op = true :=
  (factOK_spec (hR.hF.fact b hb (hR.tree b hb) bb hbb x v hf) hc.parents).2

theorem inv_phi (hR : RelSpec tabs f g F inv RB) {z : ID} {w : Width} {r : Rng}
    (hz : (z, w, r) ∈ inv) : ∃ zv, f.value? z = some zv ∧ zv.op = .Phi :=
  let ⟨zv, h1, h2, _⟩ := hR.hinv z w r hz; ⟨zv, h1, h2⟩

/-- The edge taken by a terminator, and its own fact. -/
theorem edge_taken {fr : Frame} {pb : Block} {e : Edge} (h : stepTerm fr pb = .ok (.goto e)) :
    ∃ k, pb.succs[k]? = some e ∧ ∀ c v, (c, v) ∈ ownFact pb k → fr.regs[c]? = some (some (.bool v)) := by
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 (GoFV.Proof.stepTerm_goto_mem h)
  unfold ownFact
  by_cases hkind : pb.kind = .If
  · simp only [hkind, beq_self_eq_true, ite_true]
    rcases hl : pb.controls.toList with _ | ⟨c, _ | ⟨c', l⟩⟩
    · exact ⟨k, hk, fun _ _ hm => by simp at hm⟩
    · have hc : pb.controls = #[c] := by
        apply Array.ext'; rw [hl]
      obtain ⟨b, e', hreg, he', hn⟩ := GoFV.Proof.stepTerm_if hkind hc h
      cases hn
      refine ⟨if b then 0 else 1, he', fun c0 v hm => ?_⟩
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      cases b <;> simpa using hreg
    · exact ⟨k, hk, fun _ _ hm => by simp at hm⟩
  · have : (pb.kind == .If) = false := by simpa using hkind
    simp only [this, Bool.false_eq_true, ite_false]
    exact ⟨k, hk, fun _ _ hm => by simp at hm⟩

/-- The relations of block `b` hold for `ρ`. -/
def QRel (tabs : Tables) (f : Func) (RB : Array (List (ID × ID × Width × Int))) (b : ID)
    (ρ : ID → Val) : Prop :=
  b ∈ f.blocks → ∀ z y w c, (z, y, w, c) ∈ relsAt RB b → RelDen f.value? tabs ρ z y w c

/-- `den` is monotone in the valuation. -/
theorem den_valRef {D : ID → Option Value} {ρ ρ' : ID → Val} (h : ValRef ρ ρ') :
    ∀ n x, Sem.Refines (den D tabs ρ n x) (den D tabs ρ' n x)
  | 0, _ => .poison _
  | n + 1, x => by
    by_cases ht : IsTerm D x
    · obtain ⟨v, hx, hv⟩ := ht
      rw [den_succ_term hx hv, den_succ_term hx hv]
      exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _
        (refinesList_map fun a _ => den_valRef h n a))
    · rw [den_succ_atom ht, den_succ_atom ht]; exact h x

/-- Poisoning registers keeps the relations. -/
theorem qrel_pois {b : ID} {ρ ρ' : ID → Val} (hQ : QRel tabs f RB b ρ)
    (hρ : ∀ a, ρ' a = ρ a ∨ ρ' a = .poison) : QRel tabs f RB b ρ' := by
  have hv : ValRef ρ' ρ := fun a => (hρ a).elim (fun e => e ▸ Sem.Refines.refl _)
    (fun e => e ▸ Sem.Refines.poison _)
  intro hb z y w c hr n Z Y hZ hY hnn
  exact hQ hb z y w c hr n Z Y (refines_int (hZ ▸ den_valRef hv n z))
    (refines_int (hY ▸ den_valRef hv n y)) hnn

/-- What `relHere` says: `z` is a `Phi` of shape `int w`, `y` is placed in a strict ancestor. -/
theorem relHere_spec (hc : CertOK f) {b z y : ID} {w : Width} {c : Int}
    (h : relHere f tabs (make f) b (z, y, w, c) = true) :
    (∃ zv, f.value? z = some zv ∧ zv.op = .Phi ∧ intAt tabs zv w = true) ∧ SAnc f b y := by
  unfold relHere at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · cases hzv : f.value? z with
    | none => rw [hzv] at h1; cases h1
    | some zv =>
      rw [hzv] at h1
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h1
      exact ⟨zv, rfl, h1.1, h1.2⟩
  · cases hpl : placed? f y with
    | none => rw [hpl] at h2; cases h2
    | some e =>
      rw [hpl] at h2
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Array.contains_iff_mem] at h2
      obtain ⟨⟨hne, hanc⟩, hin⟩ := h2
      obtain ⟨yv, blk, hyv, hb, hblk, hyb⟩ := placed?_spec hpl
      subst hb
      exact ⟨yv, ⟨hyv, hin, blk, hblk, hyb⟩, (anc_iff hc.parents).1 hanc, hne⟩

theorem phi_not_term {z : ID} {zv : Value} (hzv : f.value? z = some zv) (hph : zv.op = .Phi) :
    ¬ IsTerm f.value? z := fun ⟨u, hu, ht⟩ => by
  rw [hzv] at hu; cases hu; rw [hph, termOp_phi] at ht; cases ht

/-- Evaluating a non-`Phi` value of block `b` keeps `b`'s relations. -/
theorem qrel_step (hwf : WF ce f) (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) {b : ID}
    {bb : Block} (hbb : f.block? b = some bb) {x : ID} (hx : x ∈ bb.values) {v : Value}
    (hv : f.value? x = some v) (hph : v.op ≠ .Phi) {fr : Frame} (y : Val)
    (hQ : QRel tabs f RB b (rv fr)) : QRel tabs f RB b (rv (fr.set x y)) := by
  intro hb z y' w c hr
  obtain ⟨⟨zv, hzv, hzph, -⟩, hy⟩ := relHere_spec hc (hR.hrels.here b hb (hR.tree b hb) _ hr)
  have hxz : x ≠ z := fun e => by subst e; rw [hv] at hzv; cases hzv; exact hph hzph
  have hzt := phi_not_term hzv hzph
  have hdz : ∀ n, den f.value? tabs (rv (fr.set x y)) n z = den f.value? tabs (rv fr) n z := by
    intro n
    cases n with
    | zero => rfl
    | succ n => rw [den_succ_atom hzt, den_succ_atom hzt]; unfold rv; rw [Frame.set_regs_ne hxz]
  have hdy : ∀ n, den f.value? tabs (rv (fr.set x y)) n y' = den f.value? tabs (rv fr) n y' :=
    fun n => den_congr (closed_sanc_f hwf hc b) (fun a ha _ => by
      have hxa : x ≠ a := by
        rintro rfl
        obtain ⟨u, hpu, -, hne⟩ := ha
        obtain ⟨-, hvb, -⟩ := placed_in hwf hb hbb hx hv
        rw [← placed_val hpu hv] at hne
        exact hne hvb
      unfold rv; rw [Frame.set_regs_ne hxa]) n y' hy
  intro n Z Y hZ hY hnn
  rw [hdz] at hZ
  rw [hdy] at hY
  exact hQ hb z y' w c hr n Z Y hZ hY hnn

/-- **The relations after an edge's `Phi`s**, given the assumptions along the edge. -/
theorem qrel_edge (hwf : WF ce f) (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) {p : ID}
    {pb : Block} (hp : p ∈ f.blocks) (hpb : f.block? p = some pb) {fr : Frame} {k : Nat}
    {e : Edge} (hk : pb.succs[k]? = some e) {V : ID → Prop} (hD : DenOK f.value? tabs fr V)
    (hPhi : PhiArgs f e.b e.i V) (hsz : fr.regs.size = f.valueTab.size)
    (hty : ∀ a, (rv fr a).retype (shape f.value? tabs a) = rv fr a)
    (hA : ∀ y w, (∀ n (Y : BitVec w.bits), den f.value? tabs (rv fr) n y = .int w Y → 0 ≤ Y.toInt) →
      AsmHolds f.value? tabs (rv fr) (edgeAsm F inv RB p pb k y w))
    (hQ : QRel tabs f RB p (rv fr)) : PhisQ tabs f (QRel tabs f RB) fr e.b e.i := by
  intro eb ps heb hps heb' z y w c hr
  obtain ⟨eb', heb'', hall⟩ := hR.hrels.edge p hp (hR.tree p hp) pb hpb k e hk
  rw [heb] at heb''; cases heb''
  obtain ⟨⟨zv, hzv, hzph, hzw⟩, hy⟩ :=
    relHere_spec hc (hR.hrels.here e.b heb' (hR.tree e.b heb') _ hr)
  obtain ⟨-, -, p3, p4⟩ := phis_spec (hwf.valuesNodup e.b eb ⟨heb', heb⟩) hps
  have hkeep : ∀ a, a ∉ eb.values → rv { fr with regs := setPhis ps fr.regs } a = rv fr a :=
    fun a ha => by unfold rv; exact congrArg (fun o => (Option.join o).getD .poison) (p3 a (.inl ha))
  have hdy : ∀ n, den f.value? tabs (rv { fr with regs := setPhis ps fr.regs }) n y =
      den f.value? tabs (rv fr) n y :=
    fun n => den_congr (closed_sanc_f hwf hc e.b) (fun a ha _ => hkeep a fun hm => by
      obtain ⟨u, hpu, -, hne⟩ := ha
      obtain ⟨-, hub, -⟩ := placed_in hwf heb' heb hm hpu.1
      exact hne hub) n y hy
  have hzt := phi_not_term hzv hzph
  intro n Z Y hZ hY hnn
  rw [hdy] at hY
  rcases relEdgeOK_spec (hall _ hr) with ⟨hz, zv', a, av, hzv', ha, hav, haw, hdd⟩ | ⟨hz, hrp⟩
  · rw [hzv] at hzv'; cases hzv'
    cases n with
    | zero => simp [den] at hZ
    | succ n =>
      rw [den_succ_atom hzt] at hZ
      obtain ⟨a', y0, ha', hy0, hset⟩ := p4 z hz zv hzv hzph (by rw [hsz]; exact lt_of_value? hzv)
      rw [ha] at ha'; cases ha'
      rw [rv_of (fr := { fr with regs := setPhis ps fr.regs }) hset, tys_of_value hzv] at hZ
      have hshz : tabs.ty zv.type = .int w := width_some (by simpa [intAt] using hzw)
      have hsha : shape f.value? tabs a = .int w := by
        rw [shape_of hav]; exact width_some (by simpa [intAt] using haw)
      have hra : rv fr a = .int w Z := by
        have := hty a
        rw [hsha] at this
        rw [← this, rv_of hy0]
        simpa [hshz] using hZ
      obtain ⟨N, hN⟩ := (hD a (hPhi eb heb z hz zv hzv hzph a ha)).2 (rv fr) fun _ _ _ => rfl
      have hAs := hA y w fun n' Y' hY' => by
        cases den_int_unique hY hY'
        exact hnn
      exact diffDecides_sound hAs hdd ((hN _ (Nat.le_max_left N (n + 1))).trans hra)
        (den_stable_int hY (Nat.le_max_right N (n + 1)))
  · have hdz : den f.value? tabs (rv { fr with regs := setPhis ps fr.regs }) n z =
        den f.value? tabs (rv fr) n z := by
      cases n with
      | zero => rfl
      | succ n => rw [den_succ_atom hzt, den_succ_atom hzt, hkeep z hz]
    rw [hdz] at hZ
    exact hQ hp z y w c hrp n Z Y hZ hY hnn

/-- **The invariant.** -/
def proveInv (hwf : WF ce f) (hc : CertOK f) (hR : RelSpec tabs f g F inv RB) : SrcInv tabs f where
  P := PInv tabs f F inv
  L b _ := b ∈ f.blocks
  Q := QRel tabs f RB
  start := ⟨hwf.entry, fun a => ⟨retype_poison' _, fun _ v (hv : (a, v) ∈ factsAt F f.entry) => (by
    rw [hR.hF.entry] at hv; cases hv), fun _ _ _ _ h => (by cases h)⟩⟩
  qstart _ _ _ _ _ _ n Z _ hZ := by
    cases n with
    | zero => simp [den] at hZ
    | succ n =>
      obtain ⟨⟨zv, hzv, hzph, -⟩, -⟩ := relHere_spec hc
        (hR.hrels.here f.entry hwf.entry (hR.tree _ hwf.entry) _ ‹_›)
      rw [den_succ_atom (phi_not_term hzv hzph)] at hZ; cases hZ
  qpois _ _ _ hQ hρ := qrel_pois hQ hρ
  qstep _ _ hbb x hx v hv _ hph _ _ y _ _ hQ := qrel_step hwf hc hR hbb hx hv hph y hQ
  poisonAtom b a hat := ⟨retype_poison' _, fun hb v hv => by
      obtain ⟨bb, hbb, -⟩ := hwf.blockId b hb
      obtain ⟨cv, hp, -, -, ht⟩ := fact_placed hc hR hb hbb hv
      exact absurd ⟨cv, hp.1, ht⟩ hat,
    fun _ _ _ _ h => by cases h⟩
  term b bb hbb x hx v hv ht ρ _ := by
    refine ⟨by rw [shape_of hv, Val.retype_idem], fun hb v' hf => (fact_not_mem hwf hc hR hb hbb hx hf).elim,
      fun w r hz => ?_⟩
    obtain ⟨zv, hzv, hph⟩ := inv_phi hR hz
    rw [hv] at hzv; cases hzv
    rw [hph, termOp_phi] at ht; cases ht
  atom b bb hbb x hx v hv _ hnp y := by
    refine ⟨by rw [shape_of hv, Val.retype_idem], fun hb v' hf => (fact_not_mem hwf hc hR hb hbb hx hf).elim,
      fun w r hz => ?_⟩
    obtain ⟨zv, hzv, hph⟩ := inv_phi hR hz
    rw [hv] at hzv; cases hzv
    exact absurd hph hnp
  edge p ip pb fr e V hpb hp hP hQ _ hsz hD hAnc hPhi hst := by
    obtain ⟨k, hk, hown⟩ := edge_taken hst
    have hpt := hR.tree p hp
    obtain ⟨heb, -, hsub⟩ := hR.hF.succ p hp hpt pb hpb k e hk
    -- the source block's facts and the branch taken, at the end of `p`
    have hfacts : ∀ c v, ((c, v) ∈ factsAt F p ∨ (c, v) ∈ ownFact pb k) → rv fr c = .bool v ∧ V c := by
      intro c v hcv
      rcases hcv with hcv | hcv
      · refine ⟨(hP c).2.1 hp v hcv, hAnc c ?_⟩
        obtain ⟨cv, hpl, -, hanc, -⟩ := fact_placed hc hR hp hpb hcv
        exact ⟨cv, hpl, hanc⟩
      · refine ⟨rv_of (hown c v hcv), hAnc c ?_⟩
        have hcm : c ∈ pb.controls := by
          unfold ownFact at hcv
          split at hcv
          · split at hcv
            · rename_i c0 hl
              simp only [List.mem_singleton, Prod.mk.injEq] at hcv
              obtain ⟨rfl, -⟩ := hcv
              rw [← Array.mem_toList_iff, hl]; exact List.mem_singleton_self _
            · cases hcv
          · cases hcv
        obtain ⟨cv, hpl, hbo⟩ := placed_of_listed hwf (hwf.ctrlListed p pb ⟨hp, hpb⟩ c hcm)
        refine ⟨cv, hpl, ?_⟩
        rw [← hbo]
        exact ctrlUse hc hp hpb (by simpa [Cert.inTree] using hpt) hcm
    -- the assumptions of the edge hold of the frame
    have hA : AsmHolds f.value? tabs (rv fr)
        { facts := ownFact pb k ++ factsAt F p, inv, rels := relsAt RB p } := by
      refine ⟨fun c v hcv => ?_, fun z' w' r' hz' n yv' hd => ?_, hQ hp, fun a' _ _ => (hP a').1⟩
      · have hcv' : (c, v) ∈ factsAt F p ∨ (c, v) ∈ ownFact pb k := by
          rcases List.mem_append.1 hcv with h | h
          · exact .inr h
          · exact .inl h
        obtain ⟨hcr, hcV⟩ := hfacts c v hcv'
        obtain ⟨N, hN⟩ := (hD c hcV).2 (rv fr) fun _ _ _ => rfl
        exact ⟨N, fun n hn => (hN n hn).trans hcr⟩
      · obtain ⟨zv', hzv', hph'⟩ := inv_phi hR hz'
        cases n with
        | zero => simp [den] at hd
        | succ n =>
          rw [den_succ_atom (phi_not_term hzv' hph')] at hd
          exact (hP z').2.2 w' r' hz' yv' hd
    refine ⟨heb, fun a => ⟨(hP a).1, fun _ v hv => (hfacts a v (hsub _ hv)).1, (hP a).2.2⟩, ?_,
      qrel_edge hwf hc hR hp hpb hk hD hPhi hsz (fun a => (hP a).1) (fun y w hnn => ?_) hQ⟩
    · intro bb hbb z hz v hv hph a ha
      refine ⟨by rw [shape_of hv, Val.retype_idem],
        fun hb v' hf => (fact_not_mem hwf hc hR hb hbb hz hf).elim, fun w r hzi yv hyv => ?_⟩
      obtain ⟨zv, hzv, -, hzw, hedges⟩ := hR.hinv z w r hzi
      rw [hv] at hzv; cases hzv
      have hty : tabs.ty v.type = .int w := width_some (by simpa [intAt] using hzw)
      -- the incoming edge is one of `phiEdges`
      obtain ⟨-, cb, hcb, hpred⟩ := hwf.succLink p pb ⟨hp, hpb⟩ k e hk
      rw [hbb] at hcb
      rw [← Option.some.inj hcb] at hpred
      obtain ⟨v', hv', -, hvb⟩ := hwf.valueId e.b bb ⟨heb, hbb⟩ z hz
      rw [hv] at hv'; cases hv'
      have hm := mem_phiEdges (F := F) (C := make f) hv hvb hbb hz hpred ha hpt hpb
      obtain ⟨⟨av, hav, haw⟩, hsubr⟩ := hedges a _ hm
      have hshA : shape f.value? tabs a = .int w := by
        rw [shape_of hav]; exact width_some (by simpa [intAt] using haw)
      have hra : rv fr a = .int w yv := by
        have := (hP a).1
        rw [hshA] at this
        rw [← this]; rw [hty] at hyv; exact hyv
      have hA' : AsmHolds f.value? tabs (rv fr) { facts := ownFact pb k ++ factsAt F p, inv } :=
        ⟨hA.facts, hA.inv, fun _ _ _ _ h => (by cases h), hA.typed⟩
      obtain ⟨N, hN⟩ := (hD a (hPhi bb hbb z hz v hv hph a ha)).2 (rv fr) fun _ _ _ => rfl
      have hden : den f.value? tabs (rv fr) N a = .int w yv := (hN N (Nat.le_refl N)).trans hra
      exact Rng.mem_of_sub hsubr (rng_sound hA' rngFuel w a N yv hden)
    · refine ⟨hA.facts, fun z' w' r' hz' n yv' hd => ?_, hA.rels, hA.typed⟩
      rcases List.mem_cons.1 hz' with e' | hz'
      · simp only [Prod.mk.injEq] at e'
        obtain ⟨rfl, rfl, rfl⟩ := e'
        exact Rng.mem_nonneg (Width.one_le _) (hnn n yv' hd)
      · exact hA.inv z' w' r' hz' n yv' hd

end

end GoFV.Proof.ProveCheck
