import GoFV.Proof.AtomSimStep
import GoFV.Proof.RunMono

/-!
# Terminators as functions of their controls' terms (issues #113, #151)

`stepVals b cs` is `Sem.stepTerm` with the control values `cs` instead of registers
(`stepTerm_eq_stepVals`). `TermStepRef tabs f g`: every block of `g` keeps the successors of `f`'s
block (as a set) and its terminator, as a function of its controls' terms over the atoms
(`GoFV.Proof.Term.den`), refines `f`'s. It replaces "same kind, successors and refined
controls" in the atom simulation, so that a rewrite may change a block's kind, controls and
successor order (block rules, issue #151: `If (Not c)` with swapped successors, `If` on a
constant becoming `First`) as long as the terminator goes along the same edge.
`termStepRef_apply` applies it to frames, as `termRef_apply` does for values.
-/

namespace GoFV.Proof.Term

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.AtomSim

/-- Control `k` of `b` among the values `cs` (`Sem.control`). -/
def ctlV (b : Block) (cs : List Val) (k : Nat) : Res Val :=
  match cs[k]? with
  | some v => .ok v
  | none => .stuck s!"b{b.id}: missing control {k}"

/-- The terminator of `b` (`Sem.stepTerm`) on the control values `cs`. -/
def stepVals (b : Block) (cs : List Val) : Res Next :=
  match b.kind with
  | .Plain | .First => succ b 0
  | .If => do
    match ← ctlV b cs 0 with
    | .bool true => succ b 0
    | .bool false => succ b 1
    | _ => .stuck s!"b{b.id}: If on poison or non-bool"
  | .JumpTable => do
    match ← ctlV b cs 0 with
    | .int _ x => succ b x.toNat
    | _ => .stuck s!"b{b.id}: JumpTable on poison or non-int"
  | .Ret => do
    match ← ctlV b cs 0 with
    | .tuple vs =>
      match vs.getLast?, vs.dropLast with
      | some (.mem m), rs =>
        if rs.any (fun | .poison => true | _ => false) then .stuck s!"b{b.id}: poison result"
        else .ok (.ret rs m)
      | _, _ => .stuck s!"b{b.id}: Ret without memory"
    | _ => .stuck s!"b{b.id}: Ret control is not a MakeResult"
  | .Exit => .stuck s!"b{b.id}: Exit reached (a non-returning call returned)"
  | k => .stuck s!"b{b.id}: block kind {k.name} is not in phase P1"

theorem control_eq_ctlV {fr : Frame} {b : Block} (h : ∀ c ∈ b.controls, Reg fr c) (k : Nat) :
    Sem.control fr b k = ctlV b (b.controls.toList.map (rv fr)) k := by
  unfold Sem.control ctlV
  rw [List.getElem?_map, Array.getElem?_toList]
  cases hk : b.controls[k]? with
  | none => rfl
  | some c =>
    obtain ⟨y, hy⟩ := h c (Array.mem_of_getElem? hk)
    simp [hy, rv, Res.ofOption]

/-- With every control in a register, the terminator is `stepVals` of the registers. -/
theorem stepTerm_eq_stepVals {fr : Frame} {b : Block} (h : ∀ c ∈ b.controls, Reg fr c) :
    stepTerm fr b = stepVals b (b.controls.toList.map (rv fr)) := by
  unfold stepTerm stepVals
  simp only [control_eq_ctlV h]
  cases b.kind <;> rfl

/-! ## Monotonicity -/

theorem RefinesList.trans' : ∀ {as bs cs : List Val}, RefinesList as bs → RefinesList bs cs →
    RefinesList as cs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons (h.trans h') (RefinesList.trans' t t')

theorem _root_.GoFV.Proof.Next.Refines.trans {a b c : Next} (h1 : Next.Refines a b) (h2 : Next.Refines b c) :
    Next.Refines a c := by
  cases h1 with
  | goto e => exact h2
  | ret hl hm =>
    cases h2 with
    | ret hl' hm' => exact .ret (RefinesList.trans' hl hl') (hm.trans hm')

theorem Res.Rel.trans_next {x y z : Res Next} (h1 : Res.Rel Next.Refines x y)
    (h2 : Res.Rel Next.Refines y z) : Res.Rel Next.Refines x z := by
  cases h1 with
  | ok h => cases h2 with
    | ok h' => exact .ok (h.trans h')
  | panic e hm => cases h2 with
    | panic e hm' => exact .panic e (hm.trans hm')
  | stuck msg => exact .stuck msg _

theorem refinesList_getElem? : ∀ {as bs : List Val}, RefinesList as bs → ∀ k : Nat,
    (as[k]? = none ∧ bs[k]? = none) ∨ ∃ a b, as[k]? = some a ∧ bs[k]? = some b ∧ Sem.Refines a b
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons h _, 0 => .inr ⟨_, _, rfl, rfl, h⟩
  | _, _, .cons _ t, k + 1 => refinesList_getElem? t k

theorem ctlV_mono {b b' : Block} (hid : b'.id = b.id) {cs cs' : List Val} (h : RefinesList cs cs')
    (k : Nat) : Res.Refines (ctlV b cs k) (ctlV b' cs' k) := by
  unfold ctlV
  rcases refinesList_getElem? h k with ⟨h1, -⟩ | ⟨a, a', h1, h2, ha⟩
  · rw [h1]; exact .stuck _ _
  · rw [h1, h2]; exact .ok ha

/-- **`stepVals` is monotone** in the controls, for blocks with the same kind, successors and ID. -/
theorem stepVals_mono {b b' : Block} (hk : b'.kind = b.kind) (hs : b'.succs = b.succs)
    (hid : b'.id = b.id) {cs cs' : List Val} (h : RefinesList cs cs') :
    Res.Rel Next.Refines (stepVals b cs) (stepVals b' cs') := by
  have hsucc : ∀ k, Sem.succ b' k = Sem.succ b k := fun k => by unfold Sem.succ; rw [hs, hid]
  have hc := ctlV_mono hid h
  unfold stepVals
  rw [hk]
  simp only [hsucc, hid]
  split
  · exact succ_refl b 0
  · exact succ_refl b 0
  · refine Res.Rel.bind (hc 0) fun x y hxy => ?_
    cases hxy with
    | bool c => cases c <;> exact succ_refl b _
    | _ => exact .stuck _ _
  · refine Res.Rel.bind (hc 0) fun x y hxy => ?_
    cases hxy with
    | int w x => exact succ_refl b _
    | _ => exact .stuck _ _
  · refine Res.Rel.bind (hc 0) fun x y hxy => ?_
    cases hxy with
    | tuple hl =>
      dsimp only
      rcases hl.getLast? with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
      · rw [h1]; exact .stuck _ _
      · rw [h1, h2]
        cases ha with
        | mem hm =>
          dsimp only
          split
          · exact .stuck _ _
          · next hp =>
            have hq := RefinesList.any_false ?pf hl.dropLast (Bool.eq_false_iff.2 hp)
            case pf => intro a b hab ha; cases hab <;> simp_all
            simp only [hq, Bool.false_eq_true, ↓reduceIte]
            exact .ok (.ret hl.dropLast hm)
        | _ => exact .stuck _ _
    | _ => exact .stuck _ _
  · exact .stuck _ _
  · exact .stuck _ _

/-- A relation into `stepVals` carries over to refined controls. -/
theorem stepVals_right {x : Res Next} {b : Block} {cs cs' : List Val}
    (h : Res.Rel Next.Refines x (stepVals b cs)) (hc : RefinesList cs cs') :
    Res.Rel Next.Refines x (stepVals b cs') :=
  Res.Rel.trans_next h (stepVals_mono rfl rfl rfl hc)

/-! ## The relation -/

/-- The terminator of every block of `g`, as a function of its controls' terms over the atoms,
refines that of `f`'s block, and the successors of `f`'s block are successors of `g`'s. -/
def TermStepRef (tabs : Tables) (f g : Func) : Prop :=
  ∀ b ∈ g.blocks, ∀ fb gb, f.block? b = some fb → g.block? b = some gb →
    (∀ e ∈ fb.succs, e ∈ gb.succs) ∧
    ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → Typed f.value? tabs ρ → Typed (listedDefs g) tabs ρ' →
      Res.Rel Next.Refines (stepVals fb (fb.controls.toList.map (den f.value? tabs ρ n)))
        (stepVals gb (gb.controls.toList.map (den (listedDefs g) tabs ρ' m)))

/-- `TermStepRef` for source valuations satisfying a source-side invariant `P` (at the atoms,
and eventually at the denotations of the values of `S`), the frame-level invariant `Q` and
`MemAtoms`, as `AtomSim.TermRefP`. -/
def StepRefP (P : ID → Val → Prop) (Q : (ID → Val) → Prop) (S : ID → Prop)
    (D : ID → Option Value) (tabs : Tables) (fb : Block) (E : ID → Option Value) (gb : Block) :
    Prop :=
  ∀ ρ ρ', ValRef ρ ρ' → Typed D tabs ρ → Typed E tabs ρ' →
    (∀ a, ¬ IsTerm D a → P a (ρ a)) → (∀ a, S a → ∃ N, ∀ k, N ≤ k → P a (den D tabs ρ k a)) →
    Q ρ → AtomSim.MemAtoms D tabs ρ → ∀ n, ∃ m,
      Res.Rel Next.Refines (stepVals fb (fb.controls.toList.map (den D tabs ρ n)))
        (stepVals gb (gb.controls.toList.map (den E tabs ρ' m)))

theorem TermStepRef.toP {tabs : Tables} {f g : Func} (h : TermStepRef tabs f g) {b : ID}
    (hb : b ∈ g.blocks) {fb gb : Block} (hfb : f.block? b = some fb) (hgb : g.block? b = some gb)
    (P : ID → Val → Prop) (Q : (ID → Val) → Prop) (S : ID → Prop) :
    StepRefP P Q S f.value? tabs fb (listedDefs g) gb := fun ρ ρ' h1 h2 h3 _ _ _ _ n =>
  let ⟨m, hm⟩ := (h b hb fb gb hfb hgb).2 n
  ⟨m, hm ρ ρ' h1 h2 h3⟩

/-- **`StepRefP` on frames** (as `termRef_apply`): if every control's register is its term's
value over the atoms (`DenOK`) on both sides, the terminators are related. -/
theorem termStepRef_apply {P : ID → Val → Prop} {Q : (ID → Val) → Prop} {S : ID → Prop}
    {D E : ID → Option Value} {tabs : Tables} {fb gb : Block} (hT : StepRefP P Q S D tabs fb E gb)
    {FS FT : Frame} {VS VT : ID → Prop}
    (hS : DenOK D tabs FS VS) (hxS : ∀ c ∈ fb.controls, VS c) (hG : DenOK E tabs FT VT)
    (hyT : ∀ c ∈ gb.controls, VT c)
    (hrel : ∀ a, VS a → ¬ IsTerm D a → VT a → ¬ IsTerm E a → Sem.Refines (rv FS a) (rv FT a))
    (htyS : ∀ a, VS a → ¬ IsTerm D a → (rv FS a).retype (shape D tabs a) = rv FS a)
    (htyT : ∀ a, VT a → ¬ IsTerm E a → (rv FT a).retype (shape E tabs a) = rv FT a)
    (hsh : ∀ a, VS a → ¬ IsTerm D a → ¬ IsTerm E a → (E a).isSome → ¬ VT a →
      (rv FS a).retype (shape E tabs a) = rv FS a)
    (hP : ∀ a, P a (rv FS a)) (hpois : ∀ a, ¬ IsTerm D a → P a .poison) (hSV : ∀ a, S a → VS a)
    (hQ : ∀ ρ : ID → Val, (∀ a, ρ a = rv FS a ∨ ρ a = .poison) → Q ρ)
    (hMS : AtomSim.MemDefs D tabs FS VS) :
    Res.Rel Next.Refines (stepTerm FS fb) (stepTerm FT gb) := by
  classical
  let ρ : ID → Val := fun a => if VS a ∧ ¬ IsTerm D a then rv FS a else .poison
  let ρ' : ID → Val := fun a => if VT a ∧ ¬ IsTerm E a then rv FT a else ρ a
  obtain ⟨N, hN⟩ := hS.list (ρ := ρ) (fun a ha hat => by simp [ρ, ha, hat])
    (l := fb.controls.toList) fun a ha => hxS a (Array.mem_toList_iff.1 ha)
  obtain ⟨M, hM⟩ := hG.list (ρ := ρ') (fun a ha hat => by simp [ρ', ha, hat])
    (l := gb.controls.toList) fun a ha => hyT a (Array.mem_toList_iff.1 ha)
  have hval : ValRef ρ ρ' := fun a => by
    by_cases h1 : VT a ∧ ¬ IsTerm E a
    · by_cases h2 : VS a ∧ ¬ IsTerm D a
      · simp only [ρ', ρ, h1, h2]
        exact hrel a h2.1 h2.2 h1.1 h1.2
      · simp only [ρ', ρ, h1, h2, ite_false]
        exact .poison _
    · simp only [ρ', h1, ite_false]; exact Sem.Refines.refl _
  have htD : Term.Typed D tabs ρ := fun a hat _ => by
    by_cases h2 : VS a
    · simp only [ρ, h2, hat, not_false_eq_true, and_self, ite_true]; exact htyS a h2 hat
    · simp only [ρ, h2, false_and, ite_false]; exact retype_poison _
  have htE : Term.Typed E tabs ρ' := fun a hat hdef => by
    by_cases h1 : VT a
    · simp only [ρ', h1, hat, not_false_eq_true, and_self, ite_true]; exact htyT a h1 hat
    · simp only [ρ', h1, false_and, ite_false]
      by_cases h2 : VS a ∧ ¬ IsTerm D a
      · simp only [ρ, h2]; exact hsh a h2.1 h2.2 hat hdef h1
      · simp only [ρ, h2, ite_false]; exact retype_poison _
  have hPρ : ∀ a, ¬ IsTerm D a → P a (ρ a) := fun a hat => by
    by_cases h2 : VS a
    · simp only [ρ, h2, hat, not_false_eq_true, and_self, ite_true]; exact hP a
    · simp only [ρ, h2, false_and, ite_false]; exact hpois a hat
  have hPS : ∀ a, S a → ∃ N, ∀ k, N ≤ k → P a (den D tabs ρ k a) := fun a ha => by
    obtain ⟨N', hN'⟩ := (hS a (hSV a ha)).2 ρ fun b hb hbt => by simp [ρ, hb, hbt]
    exact ⟨N', fun k hk => by rw [hN' k hk]; exact hP a⟩
  have hQρ : Q ρ := hQ ρ fun a => by
    by_cases h2 : VS a ∧ ¬ IsTerm D a
    · exact .inl (ite_eq_left h2)
    · exact .inr (ite_eq_right h2)
  have hMA : AtomSim.MemAtoms D tabs ρ := AtomSim.memAtoms_of hS hMS
    (fun a ha hat => by simp [ρ, ha, hat]) fun a hat hne => by
      by_cases h2 : VS a ∧ ¬ IsTerm D a
      · exact h2.1
      · exact absurd (ite_eq_right h2) hne
  obtain ⟨m, h⟩ := hT ρ ρ' hval htD htE hPρ hPS hQρ hMA N
  rw [hN N (Nat.le_refl N)] at h
  have h2 := stepVals_right h (RefinesList.map _ _
    (fun c => den_fuel_mono E tabs ρ' m (max m M) c (Nat.le_max_left m M)) gb.controls.toList)
  rw [hM (max m M) (Nat.le_max_right m M)] at h2
  rw [stepTerm_eq_stepVals (fun c hc => (hS c (hxS c hc)).1),
    stepTerm_eq_stepVals (fun c hc => (hG c (hyT c hc)).1)]
  exact h2

/-- Same kind, successors and ID, and controls refining as terms: the terminators refine. -/
theorem stepRefP_of_controls {P : ID → Val → Prop} {Q : (ID → Val) → Prop} {S : ID → Prop}
    {D E : ID → Option Value}
    {tabs : Tables} {fb gb : Block} (hk : gb.kind = fb.kind) (hs : gb.succs = fb.succs)
    (hid : gb.id = fb.id) (hsz : fb.controls.size = gb.controls.size)
    (hc : ∀ k < gb.controls.size,
      TermRefP P Q S D tabs fb.controls[k]! E tabs gb.controls[k]!) :
    StepRefP P Q S D tabs fb E gb := by
  intro ρ ρ' hv ht ht' hp hps hq hma n
  have hall : ∀ (l : List Nat), (∀ k ∈ l, k < gb.controls.size) → ∃ m, ∀ k ∈ l,
      Sem.Refines (den D tabs ρ n fb.controls[k]!) (den E tabs ρ' m gb.controls[k]!) := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨0, fun k hk => nomatch hk⟩
    | cons k l ih =>
      intro hl
      obtain ⟨m1, h1⟩ := hc k (hl k List.mem_cons_self) ρ ρ' hv ht ht' hp hps hq hma n
      obtain ⟨m2, h2⟩ := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      refine ⟨max m1 m2, fun j hj => ?_⟩
      rcases List.mem_cons.1 hj with rfl | hj
      · exact h1.trans (den_fuel_mono E tabs ρ' _ _ _ (Nat.le_max_left _ _))
      · exact (h2 j hj).trans (den_fuel_mono E tabs ρ' _ _ _ (Nat.le_max_right _ _))
  obtain ⟨m, hm⟩ := hall (List.range gb.controls.size) (fun k hk => List.mem_range.1 hk)
  refine ⟨m, stepVals_mono hk hs hid ?_⟩
  refine refinesList_idx (by simp [hsz]) fun k a a' ha ha' => ?_
  rw [Array.getElem?_toList] at ha ha'
  obtain ⟨h1, rfl⟩ := Array.getElem?_eq_some_iff.1 ha
  obtain ⟨h2, rfl⟩ := Array.getElem?_eq_some_iff.1 ha'
  have := hm k (List.mem_range.2 h2)
  rwa [getElem!_pos fb.controls k h1, getElem!_pos gb.controls k h2] at this

/-- Controls refining as terms in blocks of the same kind, successors and ID give `TermStepRef`. -/
theorem ControlsRef.toTermStepRef {tabs : Tables} {f g : Func} (h : ControlsRef tabs f g)
    (hk : ∀ b ∈ g.blocks, ∀ fb gb, f.block? b = some fb → g.block? b = some gb →
      gb.kind = fb.kind ∧ gb.succs = fb.succs ∧ gb.id = fb.id) : TermStepRef tabs f g := by
  intro b hb fb gb hfb hgb
  obtain ⟨hk, hs, hid⟩ := hk b hb fb gb hfb hgb
  obtain ⟨hsz, hc⟩ := h b hb fb gb hfb hgb
  refine ⟨fun e he => hs ▸ he, fun n => ?_⟩
  have hall : ∀ (l : List Nat), (∀ k ∈ l, k < gb.controls.size) → ∃ m, ∀ ρ ρ', ValRef ρ ρ' →
      Typed f.value? tabs ρ → Typed (listedDefs g) tabs ρ' → ∀ k ∈ l,
        Sem.Refines (den f.value? tabs ρ n fb.controls[k]!)
          (den (listedDefs g) tabs ρ' m gb.controls[k]!) := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨0, fun _ _ _ _ _ k hk => nomatch hk⟩
    | cons k l ih =>
      intro hl
      obtain ⟨m1, h1⟩ := hc k (hl k List.mem_cons_self) n
      obtain ⟨m2, h2⟩ := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      refine ⟨max m1 m2, fun ρ ρ' hv ht ht' j hj => ?_⟩
      rcases List.mem_cons.1 hj with rfl | hj
      · exact (h1 ρ ρ' hv ht ht').trans
          (den_fuel_mono (listedDefs g) tabs ρ' _ _ _ (Nat.le_max_left _ _))
      · exact (h2 ρ ρ' hv ht ht' j hj).trans
          (den_fuel_mono (listedDefs g) tabs ρ' _ _ _ (Nat.le_max_right _ _))
  obtain ⟨m, hm⟩ := hall (List.range gb.controls.size) (fun k hk => List.mem_range.1 hk)
  refine ⟨m, fun ρ ρ' hv ht ht' => stepVals_mono hk hs hid ?_⟩
  refine refinesList_idx (by simp [hsz]) fun k a a' ha ha' => ?_
  rw [Array.getElem?_toList] at ha ha'
  obtain ⟨h1, rfl⟩ := Array.getElem?_eq_some_iff.1 ha
  obtain ⟨h2, rfl⟩ := Array.getElem?_eq_some_iff.1 ha'
  have := hm ρ ρ' hv ht ht' k (List.mem_range.2 h2)
  rwa [getElem!_pos fb.controls k h1, getElem!_pos gb.controls k h2] at this

end GoFV.Proof.Term
