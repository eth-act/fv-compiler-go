import GoFV.Proof.Low.ValStep

/-!
# Replaying lowered terminators (issue #385)

`stepValsL` (the terminator of a lowered block on its control values) is monotone in the
controls (`stepValsL_mono`; `Arm64.taken` reads flags and registers only where they are
defined, `taken_mono`). `BInvL`: along the replay the replayed terminators (`BStateL`: kind,
controls, auxint, swapped successors), as functions of their controls' lowered denotations in
the replayed definitions, refine the input's. A block-rule event (`blockOKL`) keeps it by
`BlockRuleL.Sound`: the old block, when it takes a successor, decides it by `brVal` of the matched
control's pattern denotation; the new one takes the same edge (`BInvL.block`).
-/

namespace GoFV.Proof.Low.Val

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Opt.RewriteCheck GoFV.Opt.LowerCheck GoFV.Proof.Term
open GoFV.Proof.Low
open GoFV.Proof.Pass.Rewrite (Good good_of_flat good_mono evalE_good evalE_erase InI DefClosed
  DefClosed.arg refinesList_idx wf_of cons_of cond_of isOpPat inst_at swapS_size two_succs swapS_get
  succ_ok stepVals_if stepVals_first)
open GoFV.Proof.Rules (Path PEnv DV Oracle evalE toAuxIntD)

/-! ## Monotonicity of the arm64 conditions -/

/-- `a` defined means `b` defined with the same value. -/
def OptLE {α : Type} (a b : Option α) : Prop := ∀ t, a = some t → b = some t

theorem optLE_refl {α : Type} (a : Option α) : OptLE a a := fun _ h => h

theorem optLE_none {α : Type} (b : Option α) : OptLE none b := fun _ h => by cases h

theorem optLE_bind {α β : Type} {a a' : Option α} {f g : α → Option β} (h : OptLE a a')
    (hf : ∀ x, OptLE (f x) (g x)) : OptLE (a >>= f) (a' >>= g) := by
  intro t ht
  cases ha : a with
  | none => rw [ha] at ht; cases ht
  | some x =>
    rw [ha] at ht
    rw [h x ha]
    exact hf x t ht

theorem optLE_map {α β : Type} {a a' : Option α} (h : OptLE a a') (f : α → β) :
    OptLE (a.map f) (a'.map f) := by
  intro t ht
  cases ha : a with
  | none => rw [ha] at ht; cases ht
  | some x => rw [ha] at ht; rw [h x ha]; exact ht

theorem optLE_cases {α : Type} {a b : Option α} (h : OptLE a b) : a = none ∨ b = a := by
  cases a with
  | none => exact .inl rfl
  | some x => exact .inr (h x rfl)

theorem flagBit_mono {x y : Val} (h : Sem.Refines x y) : OptLE x.flagBit y.flagBit := by
  intro t ht
  cases h <;> simp_all [Val.flagBit]

theorem eval_mono (c : Cond) {n z f v n' z' f' v' : Option Bool} (hn : OptLE n n')
    (hz : OptLE z z') (hf : OptLE f f') (hv : OptLE v v') :
    OptLE (c.eval n z f v) (c.eval n' z' f' v') := by
  rcases optLE_cases hn with rfl | rfl <;> rcases optLE_cases hz with rfl | rfl <;>
    rcases optLE_cases hf with rfl | rfl <;> rcases optLE_cases hv with rfl | rfl <;>
    cases c <;> simp [OptLE, Cond.eval]

theorem reg_mono {x y : Val} (h : Sem.Refines x y) : OptLE (Arm64.reg x) (Arm64.reg y) := by
  intro t ht
  cases h <;> simp_all [Arm64.reg]

theorem taken_poison (k : BlockKind) (ai : Int64) : Arm64.taken k ai .poison = none := by
  cases k <;> rfl

theorem taken_mem (k : BlockKind) (ai : Int64) (m : Mem) : Arm64.taken k ai (.mem m) = none := by
  cases k <;> rfl

theorem taken_tuple (k : BlockKind) (ai : Int64) (l : List Val) :
    Arm64.taken k ai (.tuple l) = none := by
  cases k <;> rfl

theorem taken_blob (k : BlockKind) (ai : Int64) (l : List Byte) :
    Arm64.taken k ai (.blob l) = none := by
  cases k <;> rfl

theorem taken_agg4 (k : BlockKind) (ai : Int64) {n z f v n' z' f' v' : Val}
    (hn : Sem.Refines n n') (hz : Sem.Refines z z') (hf : Sem.Refines f f')
    (hv : Sem.Refines v v') :
    OptLE (Arm64.taken k ai (.agg [n, z, f, v])) (Arm64.taken k ai (.agg [n', z', f', v'])) := by
  have e := fun c => eval_mono c (flagBit_mono hn) (flagBit_mono hz) (flagBit_mono hf)
    (flagBit_mono hv)
  have nv := optLE_bind (flagBit_mono hn) fun nb => optLE_bind (flagBit_mono hz) fun zb =>
    optLE_refl (pure (nb || zb) : Option Bool)
  have gv := optLE_bind (flagBit_mono hn) fun nb => optLE_bind (flagBit_mono hz) fun zb =>
    optLE_refl (pure (!nb && !zb) : Option Bool)
  cases k
  all_goals first
    | exact optLE_none _
    | exact nv
    | exact gv
    | exact e .eq
    | exact e .ne
    | exact e .hs
    | exact e .lo
    | exact e .mi
    | exact e .pl
    | exact e .vs
    | exact e .vc
    | exact e .hi
    | exact e .ls
    | exact e .ge
    | exact e .lt
    | exact e .gt
    | exact e .le
    | exact e .al
    | exact e .nv

theorem taken_agg (k : BlockKind) (ai : Int64) {as bs : List Val} (hl : RefinesList as bs) :
    OptLE (Arm64.taken k ai (.agg as)) (Arm64.taken k ai (.agg bs)) := by
  rcases hl with _ | ⟨hn, hl⟩
  · rw [show Arm64.taken k ai (.agg []) = none by cases k <;> rfl]; exact optLE_none _
  rcases hl with _ | ⟨hz, hl⟩
  · rw [show Arm64.taken k ai (.agg [_]) = none by cases k <;> rfl]; exact optLE_none _
  rcases hl with _ | ⟨hf, hl⟩
  · rw [show Arm64.taken k ai (.agg [_, _]) = none by cases k <;> rfl]; exact optLE_none _
  rcases hl with _ | ⟨hv, hl⟩
  · rw [show Arm64.taken k ai (.agg [_, _, _]) = none by cases k <;> rfl]; exact optLE_none _
  rcases hl with _ | ⟨_, _⟩
  · exact taken_agg4 k ai hn hz hf hv
  · rw [show Arm64.taken k ai (.agg (_ :: _ :: _ :: _ :: _ :: _)) = none by cases k <;> rfl]
    exact optLE_none _

/-- **`Arm64.taken` is monotone** in the control. -/
theorem taken_mono (k : BlockKind) (ai : Int64) {c c' : Val} (hr : Sem.Refines c c') :
    OptLE (Arm64.taken k ai c) (Arm64.taken k ai c') := by
  cases hr with
  | poison => rw [taken_poison]; exact optLE_none _
  | int => exact optLE_refl _
  | bool => exact optLE_refl _
  | ptr => exact optLE_refl _
  | empty => exact optLE_refl _
  | mem _ => rw [taken_mem]; exact optLE_none _
  | tuple _ => rw [taken_tuple]; exact optLE_none _
  | blob _ => rw [taken_blob]; exact optLE_none _
  | agg hl => exact taken_agg k ai hl

/-- **`stepValsL` is monotone** in the controls, for blocks with the same kind, auxint, successors
and ID. -/
theorem stepValsL_mono {b b' : Block} (hk : b'.kind = b.kind) (ha : b'.auxInt = b.auxInt)
    (hs : b'.succs = b.succs) (hid : b'.id = b.id) {cs cs' : List Val} (h : RefinesList cs cs') :
    Res.Rel Next.Refines (stepValsL b cs) (stepValsL b' cs') := by
  have hsucc : ∀ k, Sem.succ b' k = Sem.succ b k := fun k => by unfold Sem.succ; rw [hs, hid]
  have hc := ctlV_mono hid h
  unfold stepValsL
  rw [hk, ha]
  split
  · split
    · refine Res.Rel.bind (hc 0) fun x y hxy => ?_
      cases hx : Arm64.reg x with
      | none => exact .stuck _ _
      | some t =>
        rw [reg_mono hxy t hx]
        simp only [hsucc]; exact succ_refl b _
    · refine Res.Rel.bind (hc 0) fun x y hxy => ?_
      cases hx : Arm64.taken b.kind b.auxInt x with
      | none => exact .stuck _ _
      | some t =>
        rw [taken_mono b.kind b.auxInt hxy t hx]
        cases t <;> simp only [hsucc] <;> exact succ_refl b _
  · exact stepVals_mono hk hs hid h

/-! ## Conditional blocks -/

theorem res_ok_bind {α β : Type} (a : α) (f : α → Res β) : (Res.ok a >>= f) = f a := rfl

theorem brVal_eq (k : BlockKind) (ai : Int64) (c : Val) : brVal k ai c =
    if k = .If then c.flagBit else if k = .ARM64JUMPTABLE then none
    else if k.isArm64 then Arm64.taken k ai c else none := by
  cases k <;> first | rfl | (cases c <;> rfl)

theorem brVal_mono {k : BlockKind} {ai : Int64} {w y : Val} (hr : Sem.Refines w y) {b : Bool}
    (h : brVal k ai w = some b) : brVal k ai y = some b := by
  rw [brVal_eq] at h ⊢
  split
  · rename_i hh; rw [ite_eq_left_of_eq_true _ _ (eq_true hh)] at h; exact flagBit_mono hr b h
  · rename_i hh; rw [ite_eq_right_of_eq_false _ _ (eq_false hh)] at h
    split
    · rename_i hj; rw [ite_eq_left_of_eq_true _ _ (eq_true hj)] at h; cases h
    · rename_i hj; rw [ite_eq_right_of_eq_false _ _ (eq_false hj)] at h
      split
      · rename_i ha; rw [ite_eq_left_of_eq_true _ _ (eq_true ha)] at h; exact taken_mono _ _ hr b h
      · rename_i ha; rw [ite_eq_right_of_eq_false _ _ (eq_false ha)] at h; cases h

/-- A conditional block gets stuck where `brVal` is undefined, else goes along its edge. -/
theorem stepL_cond {S : Block} (hk : condKind S.kind = true) (x : Val) :
    (brVal S.kind S.auxInt x = none → ∃ msg, stepValsL S [x] = .stuck msg) ∧
    (∀ b, brVal S.kind S.auxInt x = some b → stepValsL S [x] = Sem.succ S (if b then 0 else 1)) := by
  unfold condKind at hk
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
  rcases hk with hif | ⟨harm, hjt⟩
  · have hna : S.kind.isArm64 = false := by rw [hif]; rfl
    have hs : stepValsL S [x] = stepVals S [x] := by simp only [stepValsL, hna]; rfl
    rw [hs, stepVals_if hif, brVal_eq, ite_eq_left_of_eq_true _ _ (eq_true hif)]
    refine ⟨fun h => ?_, fun b h => ?_⟩
    · cases x <;> first | exact ⟨_, rfl⟩ | cases h
    · cases x <;> first | (cases h; cases b <;> rfl) | cases h
  · have hni : S.kind ≠ .If := fun h => by rw [h] at harm; cases harm
    rw [brVal_eq, ite_eq_right_of_eq_false _ _ (eq_false hni), ite_eq_right_of_eq_false _ _ (eq_false hjt), ite_eq_left_of_eq_true _ _ (eq_true harm)]
    refine ⟨fun h => ?_, fun b h => ?_⟩ <;> unfold stepValsL <;> rw [ite_eq_left_of_eq_true _ _ (eq_true harm)] <;> split
    · rename_i hh; exact absurd hh hjt
    · simp only [ctlV, List.getElem?_cons_zero, res_ok_bind, h]; exact ⟨_, rfl⟩
    · rename_i hh; exact absurd hh hjt
    · simp only [ctlV, List.getElem?_cons_zero, res_ok_bind, h]; cases b <;> rfl

/-- A conditional block either gets stuck or goes along the edge `brVal` of a refining control
decides. -/
theorem old_step {S : Block} (hk : condKind S.kind = true) {x X : Val} (hx : Sem.Refines x X) :
    (∃ msg, stepValsL S [x] = .stuck msg) ∨
      ∃ b, brVal S.kind S.auxInt X = some b ∧ stepValsL S [x] = Sem.succ S (if b then 0 else 1) := by
  cases hb : brVal S.kind S.auxInt x with
  | none => exact .inl ((stepL_cond hk x).1 hb)
  | some b => exact .inr ⟨b, brVal_mono hx hb, (stepL_cond hk x).2 b hb⟩

/-- A conditional block whose control decides `b` by `brVal` goes along that edge. -/
theorem new_step {T : Block} (hk : condKind T.kind = true) {y : Val} {b : Bool}
    (h : brVal T.kind T.auxInt y = some b) : stepValsL T [y] = Sem.succ T (if b then 0 else 1) :=
  (stepL_cond hk y).2 b h

/-! ## Replayed terminators -/

/-- The block `fb` with the replayed terminator `st` (`stepValsL` reads its kind, auxint,
successors and ID). -/
def stBlockL (fb : Block) (st : BStateL) : Block :=
  { fb with kind := st.kind, controls := st.ctrls, auxInt := st.auxInt,
            succs := if st.swapped then swapS fb.succs else fb.succs }

theorem stBlockL_init (fb : Block) :
    stBlockL fb { kind := fb.kind, ctrls := fb.controls, auxInt := fb.auxInt, swapped := false } =
      fb := by
  cases fb; rfl

theorem bstateL_cons (f : Func) (B : BMapL) (b b' : ID) (st : BStateL) :
    bstateL f ((b', st) :: B) b = if b = b' then some st else bstateL f B b := by
  unfold bstateL
  simp only [List.lookup_cons]
  by_cases h : b = b'
  · subst h; simp
  · have : (b == b') = false := by simpa using h
    simp [this, h]

/-- The replayed terminators refine the input's: for every block of `f` whose controls are in
`C₀`, its replayed terminator `st` (swapped only with two successors) has its controls in `C`,
and as a function of its controls' lowered denotations in `M` it refines the input's in `D₀`. -/
def BInvL (tabs : Tables) (f : Func) (D₀ : ID → Option Value) (C₀ : ID → Prop) (M : Defs)
    (C : ID → Prop) (B : BMapL) : Prop :=
  ∀ b fb st, f.block? b = some fb → (∀ c ∈ fb.controls, C₀ c) → bstateL f B b = some st →
    (st.swapped = true → fb.succs.size = 2) ∧ (∀ c ∈ st.ctrls, C c) ∧
    ∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ →
      Res.Rel Next.Refines (stepValsL fb (fb.controls.toList.map (denL true D₀ tabs ρ n)))
        (stepValsL (stBlockL fb st) (st.ctrls.toList.map (denL true M.get? tabs ρ m)))

theorem BInvL.init (tabs : Tables) (f : Func) (C₀ : ID → Prop) :
    BInvL tabs f f.value? C₀ f.valueTab C₀ [] := by
  intro b fb st hfb hc hst
  simp only [bstateL, List.lookup_nil, hfb, Option.map_some, Option.some.injEq] at hst
  subst hst
  refine ⟨fun h => (by cases h), hc, fun n => ⟨n, fun ρ _ => ?_⟩⟩
  dsimp only
  rw [stBlockL_init]
  exact stepValsL_mono rfl rfl rfl rfl (RefinesList.refl _)

/-- A step `M → M'` that refines the denotations of `C ⊆ C'` keeps `BInvL`. -/
theorem BInvL.mono {tabs : Tables} {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop}
    {M M' : Defs} {C C' : ID → Prop} {B : BMapL} (h : BInvL tabs f D₀ C₀ M C B)
    (hsub : ∀ y, C y → C' y) (hty : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ)
    {g : Nat → Nat} (hstep : ∀ ρ, TypedL true M.get? tabs ρ → ∀ n y, C y →
      Sem.Refines (denL true M.get? tabs ρ n y) (denL true M'.get? tabs ρ (g n) y)) :
    BInvL tabs f D₀ C₀ M' C' B := by
  intro b fb st hfb hc hst
  obtain ⟨h1, h2, h3⟩ := h b fb st hfb hc hst
  refine ⟨h1, fun c hc' => hsub c (h2 c hc'), fun n => ?_⟩
  obtain ⟨m, hm⟩ := h3 n
  refine ⟨g m, fun ρ hρ => Res.Rel.trans_next (hm ρ hρ) (stepValsL_mono rfl rfl rfl rfl ?_)⟩
  refine refinesList_idx (by simp) fun j hj1 hj2 => ?_
  simp only [Array.getElem_toList]
  exact hstep ρ (hty ρ hρ) m _ (h2 _ (Array.getElem_mem _))

/-- Retarget the replayed terminator of `b` to `st'` when it refines `st`'s. -/
theorem BInvL.retarget {tabs : Tables} {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop}
    {M : Defs} {C : ID → Prop} {B : BMapL} (h : BInvL tabs f D₀ C₀ M C B) {b : ID}
    {st st' : BStateL} (hst : bstateL f B b = some st)
    (hty : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ)
    (hnew : ∀ fb, f.block? b = some fb → (st.swapped = true → fb.succs.size = 2) →
      (∀ c ∈ st.ctrls, C c) →
      (st'.swapped = true → fb.succs.size = 2) ∧ (∀ c ∈ st'.ctrls, C c) ∧
      ∀ m, ∃ m', ∀ ρ, TypedL true M.get? tabs ρ →
        Res.Rel Next.Refines (stepValsL (stBlockL fb st) (st.ctrls.toList.map (denL true M.get? tabs ρ m)))
          (stepValsL (stBlockL fb st') (st'.ctrls.toList.map (denL true M.get? tabs ρ m')))) :
    BInvL tabs f D₀ C₀ M C ((b, st') :: B) := by
  intro b' fb st'' hfb hc hst'
  rw [bstateL_cons] at hst'
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

/-- A control-replacement event keeps `BInvL`. -/
theorem BInvL.control {tabs : Tables} {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop}
    {M : Defs} {C : ID → Prop} {B : BMapL} (h : BInvL tabs f D₀ C₀ M C B) (hC : DefClosed M C)
    (hty : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ) {b : ID} {st : BStateL}
    (hst : bstateL f B b = some st) {i : Nat} {c : ID} (hi : i < st.ctrls.size)
    (hr : copyReachL tabs M M.size st.ctrls[i] c = true) :
    BInvL tabs f D₀ C₀ M C ((b, { st with ctrls := st.ctrls.set i c }) :: B) := by
  refine h.retarget hst hty fun fb hfb h1 h2 => ⟨h1, fun a ha => ?_, fun m => ⟨m, fun ρ hρ => ?_⟩⟩
  · rcases Array.mem_or_eq_of_mem_set (w := hi) ha with ha | rfl
    · exact h2 a ha
    · exact copyReachL_closed hC _ _ _ hr (h2 _ (Array.getElem_mem hi))
  · refine stepValsL_mono rfl rfl rfl rfl (refinesList_idx (by simp) fun j h1 h2 => ?_)
    simp only [Array.getElem_toList, Array.getElem_set]
    split
    · rename_i hij; subst hij
      exact copyReachL_den hρ _ _ _ hr m
    · exact Sem.Refines.refl _

/-! ## Block-rule events -/

/-- The successors a replayed terminator with swap flag `sw` reads. -/
theorem sel_edge {s : Array Edge} (h2 : s.size = 2) (sw swS b : Bool) :
    ∃ e, (if sw then swapS s else s)[if b then 0 else 1]? = some e ∧
      (if (sw != swS) then swapS s else s)[if (b != swS) then 0 else 1]? = some e := by
  obtain ⟨e0, e1⟩ := two_succs h2
  obtain ⟨s0, s1⟩ := swapS_get s
  cases sw <;> cases swS <;> cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true,
    bne_self_eq_false, Bool.bne_true, Bool.bne_false, Bool.not_false, Bool.not_true] <;>
    first
    | exact ⟨_, e0, e0⟩ | exact ⟨_, e1, e1⟩ | exact ⟨_, s0, s0⟩ | exact ⟨_, s1, s1⟩
    | exact ⟨_, e0, s1⟩ | exact ⟨_, e1, s0⟩ | exact ⟨_, s0, e1⟩ | exact ⟨_, s1, e0⟩

/-- What `blockOKL` establishes about a block-rule event. -/
structure BlockFactsL (tabs : Tables) (M : Defs) (br : BlockRule) (st : BStateL) (nc : Array ID)
    (st' : BStateL) where
  pat : Pat
  sw : List Bool
  c : ID
  I : Inst
  hctl : br.controls = [pat]
  hsw : sw ∈ choices (GoFV.Opt.RewriteCheck.Pat.commutes pat)
  hc : st.ctrls.toList = [c]
  hkind : st.kind = br.kind
  hmatch : matchPatL tabs M (Pat.swapC pat sw).1 [] c = some I
  hcons : consOK (evalE (br.vars.map (·.ty)) (sigmaL tabs (envL tabs M I) (Pat.swapC pat sw).1)
      (oracleL (br.vars.map (·.ty)) tabs ((br.cond.map (negAtoms false)).getD []) [])
      (envL tabs M I) (Pat.denL tabs (envL tabs M I) [] (Pat.swapC pat sw).1))
    (sigmaL tabs (envL tabs M I) (Pat.swapC pat sw).1) (envL tabs M I) I [] (Pat.swapC pat sw).1 = true
  hwf : wfOK (envL tabs M I) [] (Pat.swapC pat sw).1 = true
  hsames : ∀ x, x ∈ GoFV.Opt.RewriteCheck.Pat.sames (Pat.swapC pat sw).1 →
    x ∉ GoFV.Opt.RewriteCheck.Pat.opNames (Pat.swapC pat sw).1
  hcond : ∀ cd, br.cond = some cd → evalE (br.vars.map (·.ty))
      (sigmaL tabs (envL tabs M I) (Pat.swapC pat sw).1)
      (oracleL (br.vars.map (·.ty)) tabs ((br.cond.map (negAtoms false)).getD []) [])
      (envL tabs M I) (Pat.denL tabs (envL tabs M I) [] (Pat.swapC pat sw).1) cd = .bool true
  hargs : GoFV.Proof.Rules.Pat.argsOK (envL tabs M I).ty [] (Pat.swapC pat sw).1 = true
  htop : Pat.topOKL ((envL tabs M I).ty []) (Pat.swapC pat sw).1 = true
  hargsL : Pat.argsOKL (envL tabs M I).ty [] (Pat.swapC pat sw).1 = true
  hleaves : leavesOK M I [] (Pat.swapC pat sw).1 = true
  hauxB : blockAuxOKB br.auxInt st.auxInt = true
  hctrls : (match br.newKind, br.newControls, nc.toList with
      | .First, [], [] => true
      | k, [(.var x, _)], [c'] => k != .First &&
          (DV.pos? (sigmaL tabs (envL tabs M I) (Pat.swapC pat sw).1 x)).map I.at == some c'
      | _, _, _ => false) = true
  ai' : Int64
  hai' : newAuxL (evalE (br.vars.map (·.ty)) (sigmaL tabs (envL tabs M I) (Pat.swapC pat sw).1)
      (oracleL (br.vars.map (·.ty)) tabs ((br.cond.map (negAtoms false)).getD []) [])
      (envL tabs M I) (Pat.denL tabs (envL tabs M I) [] (Pat.swapC pat sw).1)) br.newAuxInt = some ai'
  hst' : st' = { kind := br.newKind, ctrls := nc, auxInt := ai', swapped := st.swapped != br.swapSuccs }

theorem blockFactsL {tabs : Tables} {M : Defs} {br : BlockRule} {st st' : BStateL} {nc : Array ID}
    (h : blockOKL tabs M br st nc = some st') : Nonempty (BlockFactsL tabs M br st nc st') := by
  unfold blockOKL at h
  split at h
  · rename_i pat c hctl hc
    rw [Option.ite_none_right_eq_some] at h
    obtain ⟨hk, h⟩ := h
    · simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨⟨⟨hkind, -⟩, -⟩, -⟩ := hk
      obtain ⟨sw, hsw, h1⟩ := List.exists_of_findSome?_eq_some h
      unfold blockOK1 at h1
      split at h1
      · cases h1
      split at h1
      · cases h1
      rename_i I hm
      rw [Option.ite_none_right_eq_some] at h1
      obtain ⟨hok, h1⟩ := h1
      · simp only [Bool.and_eq_true] at hok
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsames, hcons⟩, hwf⟩, hcond⟩, hargs⟩, htop⟩, hargsL⟩, hleaves⟩, hauxB⟩, hctrls⟩ := hok
        simp only [List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
          decide_eq_false_iff_not] at hsames
        split at h1
        · rename_i ai' hai'
          cases h1
          refine ⟨⟨pat, sw, c, I, hctl, hsw, hc, hkind, hm, hcons, hwf, hsames, ?_, hargs, htop,
            hargsL, hleaves, hauxB, hctrls, ai', hai', rfl⟩⟩
          intro cd hcd
          split at hcond
          · rename_i cd' hcd'
            rw [hcd] at hcd'; cases hcd'
            split at hcond
            · rename_i heq; exact heq
            · cases hcond
          · rename_i hcd'; rw [hcd] at hcd'; cases hcd'
        · cases h1
  · cases h

theorem blockAuxOK_of {fl : GoFV.Rules.Field} {ai : Int64} (h : blockAuxOKB fl ai = true) :
    blockAuxOK fl ai := by
  unfold blockAuxOKB at h
  unfold blockAuxOK
  split at h
  · trivial
  · simpa using h
  · cases h

theorem newAuxL_eq {ev ev' : GoFV.Rules.Expr → DV} (hev : ∀ x, (ev x).erase = (ev' x).erase)
    (o : Option GoFV.Rules.Expr) : newAuxL ev o = newAuxL ev' o := by
  cases o with
  | none => rfl
  | some ae =>
    simp only [newAuxL]
    rcases DV.erase_eq_cases (hev ae) with h | ⟨v, v', p, h, h'⟩
    · rw [h]
    · rw [h, h']; rfl

theorem ctrls_var {k : BlockKind} {x : Nat} {pos : CtrlPos} {l : List ID}
    {g : Nat → Option ID}
    (h : (match k, [(NewControl.var x, pos)], l with
      | .First, [], [] => true
      | k, [(.var x, _)], [c'] => k != .First && g x == some c'
      | _, _, _ => false) = true) (hk : k ≠ .First) : ∃ c', l = [c'] ∧ g x = some c' := by
  rcases l with _ | ⟨c', _ | ⟨_, _⟩⟩
  · cases k <;> simp at h
  · refine ⟨c', rfl, ?_⟩
    cases k <;> first | exact absurd rfl hk | simpa using h
  · cases k <;> simp at h

theorem obl_var {k : BlockKind} {x : Nat} {pos : CtrlPos} {ai' : Int64}
    {σ : Nat → DV} {r : Option Bool}
    (h : (match k, [(NewControl.var x, pos)] with
          | .First, _ => some true
          | k, [(.var x, _)] => brVal k ai' ((σ x).valOr .poison)
          | _, _ => none) = r) (hk : k ≠ .First) : brVal k ai' ((σ x).valOr .poison) = r := by
  cases k <;> first | exact absurd rfl hk | exact h

/-- **A block-rule event** keeps `BInvL` (`BlockRuleL.Sound`). -/
theorem BInvL.block {tabs : Tables} {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop}
    {M : Defs} {C : ID → Prop} {B : BMapL} (h : BInvL tabs f D₀ C₀ M C B) (hC : DefClosed M C)
    (hty : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ) {b : ID} {st st' : BStateL}
    (hst : bstateL f B b = some st) (h2 : (f.block? b).map (·.succs.size) = some 2)
    {br : BlockRule} (hsd : BlockRuleL.Sound br) {nc : Array ID}
    (hok : blockOKL tabs M br st nc = some st') :
    BInvL tabs f D₀ C₀ M C ((b, st') :: B) := by
  obtain ⟨F⟩ := blockFactsL hok
  obtain ⟨hk, hnk, pat0, hctl0, -, -, -, hfirst, hvar, hall⟩ := hsd
  rw [F.hctl] at hctl0; cases hctl0
  obtain ⟨-, hsound⟩ := hall F.sw F.hsw
  -- names
  let pat' := (Pat.swapC F.pat F.sw).1
  let vtys := br.vars.map (·.ty)
  let or := oracleL vtys tabs ((br.cond.map (negAtoms false)).getD []) []
  have hcmem : F.c ∈ st.ctrls := by
    rw [← Array.mem_toList_iff, F.hc]; exact List.mem_singleton_self _
  have hm := matchPatL_ok F.hmatch
  obtain ⟨hmo, -, hnd, hhd⟩ := hm
  have hat : ∀ p w, (p, w) ∈ F.I → F.I.at p = w := fun p w h => inst_at h hnd
  have htopm : ([], F.c) ∈ F.I := by
    cases hI : F.I with
    | nil => rw [hI] at hhd; cases hhd
    | cons a I =>
      rw [hI] at hhd; simp only [List.head?_cons, Option.some.injEq] at hhd; subst hhd
      exact List.mem_cons_self
  have hσs : ∀ x, Good (InI F.I) (sigmaL tabs (envL tabs M F.I) pat' x) := fun x =>
    sigmaL_good (Q := fun _ => True) (S := GoFV.Proof.Pass.Rewrite.Pat.sz pat')
      (fun _ _ => trivial) (fun p w h _ => ⟨w, h⟩) (fun _ p w h _ _ => ⟨w, h.mem⟩) hmo trivial
      (Nat.le_refl _) x
  have hpos : ∀ {d : DV}, Good (InI F.I) d → ∀ {p : Path}, DV.pos? d = some p →
      (p, F.I.at p) ∈ F.I := by
    intro d hd p h
    cases d <;> simp only [DV.pos?, reduceCtorEq] at h
    rename_i w p'
    subst h
    obtain ⟨w', hw⟩ := hd.1 w p rfl
    rw [hat _ _ hw]; exact hw
  refine h.retarget hst hty fun fb hfb hsw1 hctls => ?_
  have hfb2 : fb.succs.size = 2 := by rw [hfb] at h2; simpa using h2
  have hIC : ∀ y ∈ F.I, C y.2 :=
    matchPatL_closed hC.arg F.hmatch (hctls _ hcmem)
  refine ⟨fun _ => hfb2, ?_, fun m => ?_⟩
  · -- the new controls are matched values
    intro a ha
    rw [F.hst'] at ha
    have hctrls := F.hctrls
    split at hctrls
    · rename_i hnc
      simp only at ha
      rw [← Array.mem_toList_iff, hnc] at ha; cases ha
    · rename_i k x pos c' _ hnc
      simp only at ha
      rw [← Array.mem_toList_iff, hnc, List.mem_singleton] at ha
      subst ha
      simp only [Bool.and_eq_true, beq_iff_eq, Option.map_eq_some_iff] at hctrls
      obtain ⟨-, p, hp, rfl⟩ := hctrls
      exact hIC _ (hpos (hσs x) hp)
    · cases hctrls
  · -- the new terminator takes the old one's edge
    refine ⟨m + GoFV.Proof.Pass.Rewrite.Pat.sz pat', fun ρ hρ => ?_⟩
    let e' := semEnvL tabs M F.I (denL true M.get? tabs ρ m)
    have hσ : ∀ x, (sigmaL tabs (envL tabs M F.I) pat' x).erase = (sigmaL tabs e' pat' x).erase :=
      sigmaL_erase (e := envL tabs M F.I) (e' := e') rfl rfl pat'
    have hev : ∀ x, (evalE vtys (sigmaL tabs (envL tabs M F.I) pat') or (envL tabs M F.I)
        (Pat.denL tabs (envL tabs M F.I) [] pat') x).erase =
        (evalE vtys (sigmaL tabs e' pat') or e' (Pat.denL tabs e' [] pat') x).erase :=
      evalE_erase (e := envL tabs M F.I) (e' := e') _ _ rfl rfl hσ _ _
    have hF : FieldsOKL tabs M F.I e' := by
      intro p w x hmm hx
      refine ⟨?_, ?_, ?_⟩ <;> simp [e', semEnvL, envL, hat _ _ hmm, hx]
    have hbt : Oracle.BoolTyped or := oracleL_boolTyped _ _ _ _
    have hwf := wf_of (e := envL tabs M F.I) (e' := e') rfl [] pat' F.hwf
    have hS : ∀ x, x ∈ GoFV.Opt.RewriteCheck.Pat.sames pat' →
        x ∉ GoFV.Opt.RewriteCheck.Pat.opNames pat' := F.hsames
    have hcons := cons_of (pat := pat') (I := F.I) (e := envL tabs M F.I) (e' := e')
      rfl rfl hev hσ (fun x w p' h hn => sigmaL_leaf h hn)
      (fun p p' h => by simp only [e', semEnvL, h]) hS [] pat' (fun _ h => h) F.hcons
    have hcond := cond_of hev F.hcond
    have htyped : GoFV.Proof.Rules.Pat.typed e' [] pat' :=
      typed_ofL (Q := fun _ => True) (fun _ _ => trivial) (fun p => rfl)
        (fun p w x hmm _ hx => by
          show (denL true _ tabs ρ m (F.I.at p)).hasTy _ = true
          rw [hat _ _ hmm]
          exact den_hasTyL hρ m hx)
        hnd pat' [] F.c hmo (.inl trivial) F.hleaves
    have hai' : newAuxL (evalE vtys (sigmaL tabs e' pat') or e' (Pat.denL tabs e' [] pat'))
        br.newAuxInt = some F.ai' := by
      rw [← newAuxL_eq hev]; exact F.hai'
    have hob := hsound tabs e' or st.auxInt F.ai' hbt hwf hcons hcond htyped F.hargs F.htop F.hargsL
      (blockAuxOK_of F.hauxB) hai'
    -- the old block
    have hlow : Sem.Refines (denL true M.get? tabs ρ m F.c) (Pat.denL tabs e' [] pat') :=
      den_le_patDenL (n := m) hF (fun p w hmm k hk => by
          show Sem.Refines _ (denL true _ tabs ρ m (F.I.at p))
          rw [hat _ _ hmm]; exact denL_fuel_mono _ _ _ _ _ _ _ hk)
        pat' [] F.c m hmo (Nat.le_succ _) (.inl (Nat.le_refl _))
    have hSk : (stBlockL fb st).kind = br.kind := F.hkind
    rw [F.hc]
    simp only [List.map_cons, List.map_nil]
    rcases old_step (hSk ▸ hk) hlow with ⟨msg, hm⟩ | ⟨bb, hbb, hstep⟩
    · rw [hm]; exact .stuck _ _
    rw [hstep]
    rw [hSk] at hbb
    have hob' := hob bb hbb
    obtain ⟨e, he1, he2⟩ := sel_edge hfb2 st.swapped br.swapSuccs bb
    have hT : ∀ (j : Nat), (stBlockL fb st').succs[j]? = (if (st.swapped != br.swapSuccs) then
        swapS fb.succs else fb.succs)[j]? := by
      intro j; rw [F.hst']; rfl
    rw [succ_ok (b := stBlockL fb st) he1]
    have hctrls := F.hctrls
    by_cases hnf : br.newKind = .First
    · -- `First`
      have hnc0 : br.newControls = [] := hfirst hnf
      rw [hnf] at hob'
      simp only [Option.some.injEq] at hob'
      have hsT : stepValsL (stBlockL fb st') ((st'.ctrls.toList).map
          (denL true M.get? tabs ρ (m + GoFV.Proof.Pass.Rewrite.Pat.sz pat'))) =
          Sem.succ (stBlockL fb st') 0 := by
        have hkT : (stBlockL fb st').kind = .First :=
          (congrArg (fun s => (stBlockL fb s).kind) F.hst').trans hnf
        have hna : (stBlockL fb st').kind.isArm64 = false := by rw [hkT]; rfl
        simp only [stepValsL, hna]
        exact stepVals_first hkT _
      rw [hsT, succ_ok (e := e) (by rw [hT]; rw [← hob'] at he2; simpa using he2)]
      exact .ok (.goto _)
    · obtain ⟨x, pos, hnc⟩ := hvar hnf
      rw [hnc] at hctrls hob'
      obtain ⟨c', hnc', hpc0⟩ := ctrls_var hctrls hnf
      have hob2 := obl_var hob' hnf
      simp only [Option.map_eq_some_iff] at hpc0
      obtain ⟨p, hp, hpc⟩ := hpc0
      -- the bound control
      obtain ⟨w0, hw0⟩ : ∃ w0, sigmaL tabs (envL tabs M F.I) pat' x = .val w0 (some p) := by
        revert hp; cases sigmaL tabs (envL tabs M F.I) pat' x <;> simp [DV.pos?]
      have hx := hσ x
      rw [hw0] at hx
      have hσ2 : Good (fun w p => Sem.Refines w
          (denL true M.get? tabs ρ (m + GoFV.Proof.Pass.Rewrite.Pat.sz pat') (F.I.at p)))
          (sigmaL tabs e' pat' x) :=
        sigmaL_good (Q := fun _ => True) (S := GoFV.Proof.Pass.Rewrite.Pat.sz pat')
          (fun _ _ => trivial)
          (fun p w hmm _ => by
            show Sem.Refines (denL true _ tabs ρ m (F.I.at p)) _
            exact denL_fuel_mono _ _ _ _ _ _ _ (by omega))
          (fun q p w hmm _ hsz => by
            rw [hat _ _ hmm.mem]
            exact patDen_le_denL (Q := fun _ => True) (fun _ _ => trivial) hF
              (fun _ _ _ _ _ h => h)
              (fun p w hmm => by
                show Sem.Refines (denL true _ tabs ρ m (F.I.at p)) _
                rw [hat _ _ hmm]; exact Sem.Refines.refl _)
              q p w _ hmm trivial (by omega))
          hmo trivial (Nat.le_refl _) x
      obtain ⟨wv, hwv, hwr⟩ : ∃ wv, sigmaL tabs e' pat' x = .val wv (some p) ∧
          Sem.Refines wv (denL true M.get? tabs ρ (m + GoFV.Proof.Pass.Rewrite.Pat.sz pat')
            (F.I.at p)) := by
        rcases DV.erase_eq_cases hx with h2 | ⟨v1, v2, p1, h1, h2⟩
        · exact ⟨w0, h2.symm, hσ2.1 w0 p h2.symm⟩
        · cases h1; exact ⟨v2, h2, hσ2.1 v2 p h2⟩
      rw [show sigmaL tabs e' (Pat.swapC F.pat F.sw).1 x = .val wv (some p) from hwv] at hob2
      simp only [DV.valOr] at hob2
      have hkT : (stBlockL fb st').kind = br.newKind :=
        congrArg (fun s => (stBlockL fb s).kind) F.hst'
      have haT : (stBlockL fb st').auxInt = F.ai' :=
        congrArg (fun s => (stBlockL fb s).auxInt) F.hst'
      have hcT : condKind (stBlockL fb st').kind = true := by
        rw [hkT]; simpa [hnf] using hnk
      have hctl' : st'.ctrls.toList = [F.I.at p] :=
        (congrArg (fun s : BStateL => s.ctrls.toList) F.hst').trans (by show nc.toList = _; rw [hnc', hpc])
      rw [hctl']
      simp only [List.map_cons, List.map_nil]
      rw [new_step hcT (by rw [hkT, haT]; exact brVal_mono hwr hob2)]
      rw [succ_ok (e := e) (by rw [hT]; exact he2)]
      exact .ok (.goto _)

end GoFV.Proof.Low.Val
