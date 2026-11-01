import GoFV.Proof.Pass.RewriteTermReplay
import GoFV.Proof.TermStep
import GoFV.Proof.Rules.Block

/-!
# Replaying block rules (issue #151)

A block-rule event (`RewriteCheck.blockOK`) rewrites the replayed terminator of an `If` block on
one boolean control `c`: the block rule's control rule (`BlockRule.ctrlRule`) fires at `c` as a
value rule, with the definition `Not nc`, `Copy nc` or a `ConstBool` of `c` (`ctrlDefs`), and
the terminator becomes `If nc` (successors swapped for the `Not`) or `First` (swapped for
`false`). Since `If` on `Not x` goes where `If` on `x` with swapped successors goes, and `If` on
a constant where `First` with the matching order goes (`eff_not`, `eff_copy`, `eff_const`), the
new terminator refines the old one (`BInv.block`). `replay_inv`: a successful replay keeps
`ReplayInv` and `BInv` (the replayed terminators refine the input's).
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Rules (Rule BlockRule RNode RuleSet RwEvent)

/-- The block `fb` with the replayed terminator `st` (`stepVals` reads its kind, successors and
ID). -/
def stBlock (fb : Block) (st : BState) : Block :=
  { fb with kind := st.kind, controls := st.ctrls,
            succs := if st.swapped then swapS fb.succs else fb.succs }

theorem refines_poison {v : Val} (h : Sem.Refines v .poison) : v = .poison := by
  cases h; rfl

theorem refines_bool {v : Val} {b : Bool} (h : Sem.Refines v (.bool b)) :
    v = .poison ∨ v = .bool b := by
  cases h
  · exact .inl rfl
  · exact .inr rfl

theorem stepVals_if {b : Block} (hk : b.kind = .If) (v : Val) :
    stepVals b [v] = match v with
      | .bool true => succ b 0
      | .bool false => succ b 1
      | _ => .stuck s!"b{b.id}: If on poison or non-bool" := by
  simp only [stepVals, hk, ctlV, List.getElem?_cons_zero]
  rfl

theorem stepVals_first {b : Block} (hk : b.kind = .First) (cs : List Val) :
    stepVals b cs = succ b 0 := by
  simp only [stepVals, hk]

theorem succ_ok {b : Block} {k : Nat} {e : Edge} (h : b.succs[k]? = some e) :
    succ b k = .ok (.goto e) := by
  simp [succ, h, Res.ofOption]

theorem two_succs {s : Array Edge} (h : s.size = 2) : s[0]? = some s[0]! ∧ s[1]? = some s[1]! := by
  refine ⟨?_, ?_⟩ <;> rw [getElem!_pos s _ (by omega)] <;> simp [h]

theorem swapS_get (s : Array Edge) : (swapS s)[0]? = some s[1]! ∧ (swapS s)[1]? = some s[0]! := by
  simp [swapS]

/-- `If` on `Not w` goes where `If` on `w` with swapped successors goes. -/
theorem eff_not {S T : Block} (hS : S.kind = .If) (hT : T.kind = .If) (h2 : S.succs.size = 2)
    (hTs : T.succs = swapS S.succs) {v w : Val}
    (h : Sem.Refines v ((Cmp.not [w]).retype .bool)) :
    Res.Rel Next.Refines (stepVals S [v]) (stepVals T [w]) := by
  rw [stepVals_if hS, stepVals_if hT]
  obtain ⟨e0, e1⟩ := two_succs h2
  obtain ⟨s0, s1⟩ := swapS_get S.succs
  rw [← hTs] at s0 s1
  cases w with
  | bool b =>
    simp only [Cmp.not, bool1, Val.asBool, Val.retype] at h
    rcases refines_bool h with rfl | rfl
    · exact .stuck _ _
    · cases b
      · rw [succ_ok e0, succ_ok s1]; exact .ok (.goto _)
      · rw [succ_ok e1, succ_ok s0]; exact .ok (.goto _)
  | _ =>
    simp only [Cmp.not, bool1, Val.asBool, Val.retype] at h
    rw [refines_poison h]; exact .stuck _ _

/-- `If` on a copy of `w` (retyped at `bool`) goes where `If` on `w` goes. -/
theorem eff_copy {S T : Block} (hS : S.kind = .If) (hT : T.kind = .If)
    (hTs : T.succs = S.succs) (hid : T.id = S.id) {v w : Val}
    (h : Sem.Refines v (w.retype .bool)) :
    Res.Rel Next.Refines (stepVals S [v]) (stepVals T [w]) := by
  have hsucc : ∀ k, succ T k = succ S k := fun k => by unfold succ; rw [hTs, hid]
  rw [stepVals_if hS, stepVals_if hT]
  cases w with
  | bool b =>
    simp only [Val.retype] at h
    rcases refines_bool h with rfl | rfl
    · exact .stuck _ _
    · cases b <;> simp only [hsucc] <;> exact succ_refl S _
  | _ =>
    simp only [Val.retype] at h
    rw [refines_poison h]; exact .stuck _ _

/-- `If` on the constant `!sw` goes where `First` goes with the successors swapped iff `sw`. -/
theorem eff_const {S T : Block} (hS : S.kind = .If) (hT : T.kind = .First) (h2 : S.succs.size = 2)
    (sw : Bool) (hTs : T.succs = if sw then swapS S.succs else S.succs) {v : Val}
    (h : Sem.Refines v (.bool (!sw))) (cs : List Val) :
    Res.Rel Next.Refines (stepVals S [v]) (stepVals T cs) := by
  rw [stepVals_if hS, stepVals_first hT]
  obtain ⟨e0, e1⟩ := two_succs h2
  obtain ⟨s0, -⟩ := swapS_get S.succs
  rcases refines_bool h with rfl | rfl
  · exact .stuck _ _
  · cases sw
    · simp only [Bool.not_false, Bool.false_eq_true, ite_false] at hTs
      rw [← hTs] at e0
      rw [succ_ok e0]
      have e0' : S.succs[0]? = some T.succs[0]! := by rw [hTs]; exact two_succs h2 |>.1
      rw [succ_ok e0']; exact .ok (.goto _)
    · simp only [ite_true] at hTs
      rw [← hTs] at s0
      rw [succ_ok s0, succ_ok e1]; exact .ok (.goto _)

/-! ## The terminator invariant -/

theorem stBlock_init (fb : Block) :
    stBlock fb { kind := fb.kind, ctrls := fb.controls, swapped := false } = fb := by
  cases fb; rfl

theorem bstate_cons (f : Func) (B : BMap) (b b' : ID) (st : BState) :
    bstate f ((b', st) :: B) b = if b = b' then some st else bstate f B b := by
  unfold bstate
  simp only [List.lookup_cons]
  by_cases h : b = b'
  · subst h; simp
  · have : (b == b') = false := by simpa using h
    simp [this, h]

theorem swapS_size (s : Array Edge) : (swapS s).size = 2 := rfl

theorem swapS_swapS {s : Array Edge} (h : s.size = 2) : swapS (swapS s) = s := by
  apply Array.ext
  · simp [swapS, h]
  · intro i h1 h2
    simp only [swapS] at h1 ⊢
    have : i = 0 ∨ i = 1 := by simp at h1; omega
    rcases this with rfl | rfl
    · simp [getElem!_pos s 0 h2]
    · simp [getElem!_pos s 1 h2]

/-- The replayed terminators refine the input's: for every block of `f` whose controls are in
`C₀`, its replayed terminator `st` (swapped only with two successors) has its controls in `C`,
and as a function of its controls' denotations in `M` it refines the input's. -/
def BInv (tabs : Tables) (f : Func) (D₀ : ID → Option Value) (C₀ : ID → Prop) (M : Defs)
    (C : ID → Prop) (B : BMap) : Prop :=
  ∀ b fb st, f.block? b = some fb → (∀ c ∈ fb.controls, C₀ c) → bstate f B b = some st →
    (st.swapped = true → fb.succs.size = 2) ∧ (∀ c ∈ st.ctrls, C c) ∧
    ∀ n, ∃ m, ∀ ρ, Term.Typed D₀ tabs ρ →
      Res.Rel Next.Refines (stepVals fb (fb.controls.toList.map (den D₀ tabs ρ n)))
        (stepVals (stBlock fb st) (st.ctrls.toList.map (den M.get? tabs ρ m)))

theorem BInv.init (tabs : Tables) (f : Func) (C₀ : ID → Prop) :
    BInv tabs f f.value? C₀ f.valueTab C₀ [] := by
  intro b fb st hfb hc hst
  simp only [bstate, List.lookup_nil, hfb, Option.map_some, Option.some.injEq] at hst
  subst hst
  refine ⟨fun h => (by cases h), hc, fun n => ⟨n, fun ρ _ => ?_⟩⟩
  dsimp only
  rw [stBlock_init]
  exact stepVals_mono rfl rfl rfl (RefinesList.map _ _ (fun _ => Sem.Refines.refl _) _)

/-- A step `M → M'` that refines the denotations of `C ⊆ C'` keeps `BInv`. -/
theorem BInv.mono {tabs : Tables} {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop}
    {M M' : Defs} {C C' : ID → Prop} {B : BMap} (h : BInv tabs f D₀ C₀ M C B)
    (hsub : ∀ y, C y → C' y) (hty : ∀ ρ, Term.Typed D₀ tabs ρ → Term.Typed M.get? tabs ρ)
    {g : Nat → Nat} (hstep : ∀ ρ, Term.Typed M.get? tabs ρ → ∀ n y, C y →
      Sem.Refines (den M.get? tabs ρ n y) (den M'.get? tabs ρ (g n) y)) :
    BInv tabs f D₀ C₀ M' C' B := by
  intro b fb st hfb hc hst
  obtain ⟨h1, h2, h3⟩ := h b fb st hfb hc hst
  refine ⟨h1, fun c hc' => hsub c (h2 c hc'), fun n => ?_⟩
  obtain ⟨m, hm⟩ := h3 n
  refine ⟨g m, fun ρ hρ => stepVals_right (hm ρ hρ) ?_⟩
  refine refinesList_idx (by simp) fun j hj1 hj2 => ?_
  simp only [Array.getElem_toList]
  exact hstep ρ (hty ρ hρ) m _ (h2 _ (Array.getElem_mem _))

/-- Retarget the replayed terminator of `b` to `st'` when it refines `st`'s. -/
theorem BInv.retarget {tabs : Tables} {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop}
    {M : Defs} {C : ID → Prop} {B : BMap} (h : BInv tabs f D₀ C₀ M C B) {b : ID} {st st' : BState}
    (hst : bstate f B b = some st) (hty : ∀ ρ, Term.Typed D₀ tabs ρ → Term.Typed M.get? tabs ρ)
    (hnew : ∀ fb, f.block? b = some fb → (st.swapped = true → fb.succs.size = 2) →
      (∀ c ∈ st.ctrls, C c) →
      (st'.swapped = true → fb.succs.size = 2) ∧ (∀ c ∈ st'.ctrls, C c) ∧
      ∀ m, ∃ m', ∀ ρ, Term.Typed M.get? tabs ρ →
        Res.Rel Next.Refines (stepVals (stBlock fb st) (st.ctrls.toList.map (den M.get? tabs ρ m)))
          (stepVals (stBlock fb st') (st'.ctrls.toList.map (den M.get? tabs ρ m')))) :
    BInv tabs f D₀ C₀ M C ((b, st') :: B) := by
  intro b' fb st'' hfb hc hst'
  rw [bstate_cons] at hst'
  by_cases hb : b' = b
  · subst hb
    simp only [ite_true, Option.some.injEq] at hst'
    subst hst'
    obtain ⟨h1, h2, h3⟩ := h b' fb st hfb hc hst
    obtain ⟨n1, n2, n3⟩ := hnew fb hfb h1 h2
    refine ⟨n1, n2, fun n => ?_⟩
    obtain ⟨m, hm⟩ := h3 n
    obtain ⟨m', hm'⟩ := n3 m
    exact ⟨m', fun ρ hρ => Res.Rel.trans_next (hm ρ hρ) (hm' ρ (hty ρ hρ))⟩
  · simp only [hb, ite_false] at hst'
    exact h b' fb st'' hfb hc hst'

/-- A control-replacement event keeps `BInv`. -/
theorem BInv.control {tabs : Tables} {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop}
    {M : Defs} {C : ID → Prop} {B : BMap} (h : BInv tabs f D₀ C₀ M C B) (hC : DefClosed M C)
    (hty : ∀ ρ, Term.Typed D₀ tabs ρ → Term.Typed M.get? tabs ρ) {b : ID} {st : BState}
    (hst : bstate f B b = some st) {i : Nat} {c : ID} (hi : i < st.ctrls.size)
    (hr : copyReach tabs M M.size st.ctrls[i] c = true) :
    BInv tabs f D₀ C₀ M C ((b, { st with ctrls := st.ctrls.set i c }) :: B) := by
  refine h.retarget hst hty fun fb hfb h1 h2 => ⟨h1, fun a ha => ?_, fun m => ⟨m, fun ρ hρ => ?_⟩⟩
  · rcases Array.mem_or_eq_of_mem_set (w := hi) ha with ha | rfl
    · exact h2 a ha
    · exact copyReach_closed hC _ _ _ hr (h2 _ (Array.getElem_mem hi))
  · refine stepVals_mono rfl rfl rfl (refinesList_idx (by simp) fun j h1 h2 => ?_)
    simp only [Array.getElem_toList, Array.getElem_set]
    split
    · rename_i hij; subst hij
      exact copyReach_den hρ _ _ _ hr m
    · exact Sem.Refines.refl _

/-! ## Block-rule events -/

theorem ctrlRule_cases {br : BlockRule} {cr : Rule}
    (h : GoFV.Proof.Rules.BlockRule.ctrlRule br = some cr) :
    (br.newKind = .If ∧ ∃ x, cr.result =
      if br.swapSuccs then .build [GoFV.Proof.Rules.notNode x] else .copy (.var x)) ∨
    (br.newKind = .First ∧ cr.result = .build [GoFV.Proof.Rules.constNode (!br.swapSuccs)]) := by
  unfold GoFV.Proof.Rules.BlockRule.ctrlRule at h
  split at h
  · cases h; exact .inl ⟨‹br.newKind = .If›, _, rfl⟩
  · cases h; exact .inr ⟨‹br.newKind = .First›, rfl⟩
  · cases h

theorem blockOK_facts {tabs : Tables} {M : Defs} {br : BlockRule} {st st' : BState}
    {nc : Array ID} {defs : List Value} (h : blockOK tabs M br st nc = some (defs, st')) :
    ∃ cr c x, GoFV.Proof.Rules.BlockRule.ctrlRule br = some cr ∧ st.kind = .If ∧
      st.ctrls.toList = [c] ∧ M.get? c = some x ∧ ctrlDefs cr x nc = some defs ∧
      tabs.ty x.type = .bool ∧ nc.size = (if br.newKind = .If then 1 else 0) ∧
      ruleOK tabs M cr c defs = true ∧
      st' = { kind := br.newKind, ctrls := nc, swapped := st.swapped != br.swapSuccs } := by
  unfold blockOK at h
  split at h
  · rename_i cr c hcr hk hc
    split at h
    · rename_i x hx
      split at h
      · rename_i defs' hd
        by_cases hok : (isBool (tabs.ty x.type) &&
            nc.size == (if br.newKind == .If then 1 else 0) && ruleOK tabs M cr c defs') = true
        · simp only [hok, ite_true] at h
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq] at hok
          obtain ⟨⟨hb, hn⟩, hr⟩ := hok
          refine ⟨cr, c, x, hcr, hk, hc, hx, hd, ?_, ?_, hr, rfl⟩
          · revert hb; cases tabs.ty x.type <;> simp [isBool]
          · rw [hn]
        · simp only [hok] at h; cases h
      · cases h
    · cases h
  · cases h

theorem putAll_two (M : Defs) (u : Value) : (putAll M [u, u]).get? u.id = some u := by
  simp [putAll, get?_put]

theorem putAll_one (M : Defs) (u : Value) : (putAll M [u]).get? u.id = some u := by
  simp [putAll, get?_put]

theorem evalPure_not (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    evalPure .Not ty ai ax args = Cmp.not args := rfl

theorem evalPure_copy (ty : Ty) (ai : Int64) (ax : Option AuxRef) (w : Val) :
    evalPure .Copy ty ai ax [w] = w := rfl

theorem evalPure_constBool (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    evalPure .ConstBool ty ai ax args = .bool (ai != 0) := rfl

section BlockEv

variable {tabs : Tables} {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop} {M : Defs}
  {C : ID → Prop} {B : BMap} {b c : ID} {st : BState} {fb : Block}

theorem stBlock_if_size (h2 : fb.succs.size = 2) :
    (stBlock fb st).succs.size = 2 := by
  cases hs : st.swapped <;> simp [stBlock, hs, swapS_size, h2]

/-- The step of the control's denotation that the event's new definition `u` of `c` gives. -/
theorem den_new {M' : Defs} {u : Value} (hu : M'.get? c = some u) (ht : termOp u.op = true)
    {ρ : ID → Val} (m : Nat) :
    den M'.get? tabs ρ (m + 1) c = (GoFV.Proof.Rules.opVal tabs u.op (tabs.ty u.type) u.auxInt u.aux
      (u.args.toList.map (den M'.get? tabs ρ m))).retype (tabs.ty u.type) :=
  den_succ_term hu ht

/-- The fuel-raising step on the old terminator. -/
theorem stepVals_fuel (S : Block) (D : ID → Option Value) (ρ : ID → Val) (m : Nat) :
    Res.Rel Next.Refines (stepVals S [den D tabs ρ m c]) (stepVals S [den D tabs ρ (m + 1) c]) :=
  stepVals_mono rfl rfl rfl (.cons (den_fuel_mono D tabs ρ m (m + 1) c (by omega)) .nil)

end BlockEv

/-- **A block-rule event keeps `BInv`.** -/
theorem BInv.block {tabs : Tables} {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop}
    {M : Defs} {C : ID → Prop} {B : BMap} (h : BInv tabs f D₀ C₀ M C B)
    (hI : ReplayInv tabs D₀ C₀ M C) {cr : Rule} (hs : GoFV.Proof.Rules.Rule.SoundT cr)
    (hr : RetypeShapes) {c : ID} {defs : List Value} (F : RuleFacts tabs M cr c defs)
    {b : ID} {st : BState} (hst : bstate f B b = some st)
    (h2 : (f.block? b).map (·.succs.size) = some 2) {br : BlockRule}
    (hcr : GoFV.Proof.Rules.BlockRule.ctrlRule br = some cr) (hk : st.kind = .If)
    (hc : st.ctrls.toList = [c]) {x : Value} (hx : M.get? c = some x) {nc : Array ID}
    (hd : ctrlDefs cr x nc = some defs) (hb : tabs.ty x.type = .bool)
    (hn : nc.size = if br.newKind = .If then 1 else 0) :
    BInv tabs f D₀ C₀ (putAll M defs) (fun y => C y ∨ (C c ∧ y ∈ defIds defs))
      ((b, { kind := br.newKind, ctrls := nc, swapped := st.swapped != br.swapSuccs }) :: B) := by
  have h1 := h.mono (C' := fun y => C y ∨ (C c ∧ y ∈ defIds defs)) (fun y hy => .inl hy) hI.typed
    (fun ρ hρ n y hy => F.step hs hr hI.closed hρ n y hy)
  have hxid : x.id = c := by
    have := F.hxv; rw [hx] at this; cases this; exact F.hid
  have hcl := F.closed hI.closed
  refine h1.retarget hst (fun ρ hρ => F.typed (hI.typed ρ hρ)) fun fb hfb _ hctl => ?_
  have hfb2 : fb.succs.size = 2 := by rw [hfb] at h2; simpa using h2
  have hcC : (fun y => C y ∨ (C c ∧ y ∈ defIds defs)) c := by
    have : c ∈ st.ctrls := by rw [← Array.mem_toList_iff, hc]; exact List.mem_singleton_self _
    exact hctl c this
  have hS : (stBlock fb st).kind = .If := hk
  have hSs := stBlock_if_size (st := st) hfb2
  -- the new definition of `c` and its arguments
  have hnew : ∀ u, (putAll M defs).get? c = some u → ∀ a ∈ u.args,
      (fun y => C y ∨ (C c ∧ y ∈ defIds defs)) a := fun u hu a ha => by
    obtain ⟨m, hm, hargs⟩ := hcl c hcC
    rw [hu] at hm; cases hm; exact hargs a ha
  refine ⟨fun _ => hfb2, ?_, ?_⟩
  all_goals rcases ctrlRule_cases hcr with ⟨hK, x0, hres⟩ | ⟨hK, hres⟩
  · -- the new controls are arguments of `c`'s new definition
    rw [hK] at hn; simp only [ite_true] at hn
    have hnc := toList_of_size_one hn
    intro a ha
    rw [← Array.mem_toList_iff, hnc] at ha
    rw [List.mem_singleton] at ha; subst ha
    cases hsw : br.swapSuccs <;> rw [hsw] at hres <;> simp only [Bool.false_eq_true, ite_false,
      ite_true] at hres <;> unfold ctrlDefs at hd <;> rw [hres, hnc] at hd <;>
      simp only [Option.some.injEq] at hd <;> subst hd
    · exact hnew _ (by rw [← hxid]; exact putAll_one _ _) _ (by simp)
    · exact hnew _ (by rw [← hxid]; exact putAll_two _ _) _ (by simp)
  · rw [hK] at hn; simp at hn
    intro a ha
    subst hn; exact absurd ha (by simp)
  · rw [hK] at hn; simp only [ite_true] at hn
    have hnc := toList_of_size_one hn
    intro m
    refine ⟨m, fun ρ hρ => ?_⟩
    rw [hc, hnc]
    simp only [List.map_cons, List.map_nil]
    refine Res.Rel.trans_next (stepVals_fuel _ _ ρ m) ?_
    cases hsw : br.swapSuccs <;> rw [hsw] at hres <;> simp only [Bool.false_eq_true, ite_false,
      ite_true] at hres <;> unfold ctrlDefs at hd <;> rw [hres, hnc] at hd <;>
      simp only [Option.some.injEq] at hd <;> subst hd
    · -- copy
      rw [den_new (by rw [← hxid]; exact putAll_one _ _) termOp_copy]
      simp only [hb, List.map_cons, List.map_nil, evalPure_copy]
      refine eff_copy hS ?_ ?_ ?_ (Sem.Refines.refl _)
      · simp [stBlock, hK]
      · simp [stBlock, hsw]
      · rfl
    · -- `Not`
      rw [den_new (by rw [← hxid]; exact putAll_two _ _) (by decide : termOp .Not = true)]
      simp only [hb, List.map_cons, List.map_nil, evalPure_not]
      refine eff_not (T := stBlock fb _) hS (by simp [stBlock, hK, hk]) hSs ?_ (Sem.Refines.refl _)
      cases hss : st.swapped <;> simp [stBlock, hss, swapS_swapS hfb2]
  · rw [hK] at hn; simp at hn
    have hnc : nc.toList = [] := by subst hn; rfl
    intro m
    refine ⟨m, fun ρ hρ => ?_⟩
    rw [hc, hnc]
    simp only [List.map_cons, List.map_nil]
    refine Res.Rel.trans_next (stepVals_fuel _ _ ρ m) ?_
    unfold ctrlDefs at hd; rw [hres, hnc] at hd
    simp only [Option.some.injEq] at hd; subst hd
    rw [den_new (by rw [← hxid]; exact putAll_two _ _) (by decide : termOp .ConstBool = true)]
    simp only [hb, GoFV.Proof.Rules.constNode, evalPure_constBool]
    refine eff_const (T := stBlock fb _) hS (by simp [stBlock, hK, hk]) hSs br.swapSuccs ?_ ?_ _
    · cases hss : st.swapped <;> cases hsw : br.swapSuccs <;>
        simp [stBlock, hss, hsw, swapS_swapS hfb2]
    · cases hsw : br.swapSuccs <;> exact Sem.Refines.refl _

/-! ## The replay -/

/-- **Replay**: a successful replay of the log keeps `ReplayInv` and `BInv`. -/
theorem replay_inv {tabs : Tables} {s : RuleSet} (hs : s.AllSound) (hr : RetypeShapes)
    {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop} :
    ∀ (evs : List RwEvent) (M M' : Defs) (B B' : BMap) (C : ID → Prop),
      replay tabs (GoFV.Rules.Interp.Table.ofRuleSet s) f M B evs = some (M', B') →
      ReplayInv tabs D₀ C₀ M C → BInv tabs f D₀ C₀ M C B →
      ∃ C', ReplayInv tabs D₀ C₀ M' C' ∧ BInv tabs f D₀ C₀ M' C' B'
  | [], M, M', B, B', C, h, hI, hB => by
    simp only [replay, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨C, hI, hB⟩
  | .rule v i _ defs :: evs, M, M', B, B', C, h, hI, hB => by
    unfold replay at h
    split at h
    · cases h
    rename_i x hx
    split at h
    · cases h
    rename_i cr hcr
    split at h
    · rename_i hok
      obtain ⟨F⟩ := ruleFacts hok
      have hput : defs.foldl (fun M u => M.put u.id u) M = putAll M defs.toList := by
        simp [putAll, Array.foldl_toList]
      rw [hput] at h
      have hsd := ofRuleSet_sound hs hcr
      exact replay_inv hs hr evs _ M' B B' _ h (hI.rule hsd hr F)
        (hB.mono (fun y hy => .inl hy) hI.typed fun ρ hρ n y hy => F.step hsd hr hI.closed hρ n y hy)
    · cases h
  | .copyArg v i src :: evs, M, M', B, B', C, h, hI, hB => by
    unfold replay at h
    split at h
    · cases h
    rename_i x hx
    split at h
    · rename_i hi
      split at h
      · rename_i hrc
        exact replay_inv hs hr evs _ M' B B' C h (hI.copy hx hi hrc)
          (hB.mono (g := id) (fun _ h => h) hI.typed fun ρ hρ n y hy =>
            copyPut_den hx hi hrc hI.closed hρ n y hy)
      · cases h
    · cases h
  | .control b i c :: evs, M, M', B, B', C, h, hI, hB => by
    unfold replay at h
    split at h
    · cases h
    rename_i st hst
    split at h
    · rename_i hi
      split at h
      · rename_i hrc
        exact replay_inv hs hr evs M M' _ B' C h hI (hB.control hI.closed hI.typed hst hi hrc)
      · cases h
    · cases h
  | .phielim .. :: _, M, M', B, B', C, h, _, _ => by simp [replay] at h
  | .blockRule b i nc :: evs, M, M', B, B', C, h, hI, hB => by
    unfold replay at h
    split at h
    · cases h
    rename_i st hst
    split at h
    · cases h
    rename_i h2
    have h2' : (f.block? b).map (·.succs.size) = some 2 := by simpa using h2
    split at h
    · cases h
    rename_i br hbr
    split at h
    · cases h
    rename_i defs st' hok
    obtain ⟨cr, c, x, hcr, hk, hc, hx, hd, hb, hn, hrule, rfl⟩ := blockOK_facts hok
    obtain ⟨cr', hcr', hsd⟩ := ofRuleSet_blockSound hs hbr
    rw [hcr] at hcr'; cases hcr'
    obtain ⟨F⟩ := ruleFacts hrule
    have hput : defs.foldl (fun M u => M.put u.id u) M = putAll M defs := rfl
    rw [hput] at h
    exact replay_inv hs hr evs _ M' _ B' _ h (hI.rule hsd hr F)
      (hB.block hI hsd hr F hst h2' hcr hk hc hx hd hb hn)

end GoFV.Proof.Pass.Rewrite
