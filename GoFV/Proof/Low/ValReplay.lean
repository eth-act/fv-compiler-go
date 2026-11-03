import GoFV.Proof.Low.ValBlock

/-!
# Replaying the lowering log refines the denotations (issue #385)

The lowered counterpart of `GoFV/Proof/Pass/RewriteTermReplay.lean` and `replay_inv`
(`RewriteTermBlock.lean`) for `GoFV.Opt.LowerCheck.replayL`: starting from the input's
definitions `D₀` read in lowered mode, the values of a set `C₀` closed under arguments keep a
refining lowered denotation (`ReplayInvL`), and the atoms of `D₀` whose arguments are in `C₀`
keep their fields but the op (an atom rename, `renameOp`) while their arguments (rewritten only by
`copyArg` events, through compatible copies) keep refining denotations (`ReplayInvL.atoms`, the one
place that relates an atom's arguments). Value rule events use `RuleFactsL.step` and
`ArmRule.Sound1`, ellipsis events on terms `SetOpSound` (`setOp_den`), atom renames change no
denotation (`rename_den`); terminators keep `BInvL`.
-/

namespace GoFV.Proof.Low.Val

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Opt.RewriteCheck GoFV.Opt.LowerCheck GoFV.Proof.Term
open GoFV.Proof.Low
open GoFV.Proof.Pass.Rewrite (putAll get?_put defIds stepK DefClosed DefClosed.arg refinesList_idx
  copyPut copyPut_get set_getElem! foldl_rows foldl_brows ofRuleSet_values ofRuleSet_blocks)
open GoFV.Proof.Rules (ForallL)

/-! ## The rule table -/

theorem forallL_mem {α : Type} {P : α → Prop} : ∀ {l : List α}, ForallL P l → ∀ a ∈ l, P a
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, t⟩, a, .tail _ h => forallL_mem t a h

/-- Every value rule of the table of a sound lowering rule set is `ArmRule.Checked`. -/
theorem ofRuleSetL_checked {s : RuleSet} (hs : ArmRuleSet.AllSound s) {k i : Nat}
    {cr : GoFV.Rules.Interp.CRule}
    (h : ((GoFV.Rules.Interp.Table.ofRuleSet s).values[k]?).bind (·[i]?) = some cr) :
    ArmRule.Checked cr.rule := by
  cases hk : (GoFV.Rules.Interp.Table.ofRuleSet s).values[k]? with
  | none => rw [hk] at h; cases h
  | some row =>
    rw [hk] at h
    simp only [Option.bind_some] at h
    rw [ofRuleSet_values] at hk
    rcases foldl_rows s.values s.values (fun _ h => h) _ (fun k row h => by
        rw [Array.getElem?_replicate] at h
        split at h
        · cases h; exact .inl rfl
        · cases h) k row hk with rfl | ⟨p, hp, rfl⟩
    · simp at h
    · have hm := Array.mem_of_getElem? h
      simp only [Array.mem_map, List.mem_toArray] at hm
      obtain ⟨r, hr, rfl⟩ := hm
      exact forallL_mem (forallL_mem hs.1 p hp) r hr

/-- Every block rule of the table of a sound lowering rule set is `BlockRuleL.Sound`. -/
theorem ofRuleSetL_blockSound {s : RuleSet} (hs : ArmRuleSet.AllSound s) {k i : Nat}
    {br : BlockRule}
    (h : ((GoFV.Rules.Interp.Table.ofRuleSet s).blocks[k]?).bind (·[i]?) = some br) :
    BlockRuleL.Sound br := by
  cases hk : (GoFV.Rules.Interp.Table.ofRuleSet s).blocks[k]? with
  | none => rw [hk] at h; cases h
  | some row =>
    rw [hk] at h
    simp only [Option.bind_some] at h
    rw [ofRuleSet_blocks] at hk
    rcases foldl_brows s.blocks s.blocks (fun _ h => h) _ (fun k row h => by
        rw [Array.getElem?_replicate] at h
        split at h
        · cases h; exact .inl rfl
        · cases h) k row hk with rfl | ⟨p, hp, rfl⟩
    · simp at h
    · have hm := Array.mem_of_getElem? h
      simp only [List.mem_toArray] at hm
      exact forallL_mem (forallL_mem hs.2.1 p hp) br hm

/-! ## Ellipsis rules -/

theorem choices_ne : ∀ n, ∃ sw, sw ∈ choices n
  | 0 => ⟨[], by simp [choices]⟩
  | n + 1 => by
    obtain ⟨sw, hsw⟩ := choices_ne n
    exact ⟨false :: sw, by simp only [choices, List.mem_flatMap]; exact ⟨sw, hsw, by simp⟩⟩

theorem ellipsisOn_eq {o : Op} {p : Pat} (h : ellipsisOn o p = true) :
    ∃ c, p = .op o none .any .any .any .ellipsis [] c := by
  unfold ellipsisOn at h
  split at h
  · rename_i o' c
    simp only [beq_iff_eq] at h
    subst h
    exact ⟨c, rfl⟩
  · cases h

/-- A rule on an ellipsis pattern is no `ArmRule.Sound` rule (its pattern has no fixed arity). -/
theorem not_sound_of_ellipsis {r : Rule} {o : Op} (he : ellipsisOn o r.pat = true) :
    ¬ ArmRule.Sound r := by
  intro hs
  obtain ⟨sw, hsw⟩ := choices_ne (GoFV.Opt.RewriteCheck.Pat.commutes r.pat)
  have h := (hs sw hsw).1
  obtain ⟨c, hc⟩ := ellipsisOn_eq he
  simp only [Rule.swapC, hc] at h
  cases c <;> cases sw <;> simp [Pat.swapC, Pat.swapCs, GoFV.Proof.Rules.Pat.arityOk] at h

theorem termVL_gen {tabs : Tables} {v : Value} {o : Op} (hg : o.generic = true) (hv : v.op = o) :
    termVL tabs v = GoFV.Opt.RewriteCheck.termOp o := by
  unfold termVL; rw [hv]; simp only [hg, ite_true]

theorem termVL_arm {tabs : Tables} {v : Value} {o : Op} (hg : o.generic = false)
    (hm : (o == .ARM64MOVDaddr) = false) (hl : ldOp? o = none) (hv : v.op = o) :
    termVL tabs v = (GoFV.Opt.LowerTerm.armTerm o && !GoFV.Opt.LowerTerm.actOp o && !isRoot o) := by
  unfold termVL; rw [hv]; simp only [hg, hm, hl, Option.isSome_none, Bool.false_eq_true, ite_false]

theorem renameOp_src {o o' : Op} (h : renameOp o o' = true) (tabs : Tables) (v : Value)
    (hv : v.op = o) : termVL tabs v = false := by
  unfold renameOp at h
  split at h <;> first
    | (cases h; done)
    | (rw [termVL_gen (by decide) hv]; decide)
    | (rw [termVL_arm (by decide) (by decide) (by decide) hv]; decide)

theorem renameOp_dst {o o' : Op} (h : renameOp o o' = true) (tabs : Tables) (v : Value)
    (hv : v.op = o') : termVL tabs v = false := by
  unfold renameOp at h
  split at h <;> first
    | (cases h; done)
    | (rw [termVL_gen (by decide) hv]; decide)
    | (rw [termVL_arm (by decide) (by decide) (by decide) hv]; decide)

/-- A renamed atom is no `MOVDaddr`. -/
theorem renameOp_src_ne {o o' : Op} (h : renameOp o o' = true) : o ≠ .ARM64MOVDaddr := by
  unfold renameOp at h
  split at h <;> first | (cases h; done) | (intro h'; cases h')

/-- What `setOpDef` establishes. -/
theorem setOpDef_facts {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {x' : Value}
    (h : setOpDef tabs M r v = some x') : ∃ x o', M.get? v = some x ∧ r.result = .setOp o' ∧
      x' = { x with op := o' } ∧ ellipsisOn x.op r.pat = true ∧
      ((termVL tabs x = true ∧ termVL tabs x' = true ∧ topOKL x.op (shpL tabs x.type) = true) ∨
        (renameOp x.op o' = true ∧ termVL tabs x = false)) := by
  unfold setOpDef at h
  split at h
  · rename_i x o' hx hr
    dsimp only at h
    rw [Option.ite_none_right_eq_some] at h
    obtain ⟨hc, h⟩ := h
    · cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨⟨-, he⟩, -⟩, -⟩, hk⟩ := hc
      refine ⟨x, o', hx, hr, rfl, he, ?_⟩
      rcases hk with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, h2, h3⟩
      · exact .inr ⟨h1, h2⟩
  · cases h

theorem swapC_op (o : Op) (n : Option Nat) (ty ai ax : GoFV.Rules.Field) (ar : GoFV.Rules.Arity)
    (args : List Pat) (c : Bool) (sw : List Bool) : ∃ args' sw',
      Pat.swapC (.op o n ty ai ax ar args c) sw = (.op o n ty ai ax ar args' false, sw') := by
  simp only [Pat.swapC]
  split <;> (try split) <;> exact ⟨_, _, rfl⟩

/-- `Store`s are atoms. -/
theorem termVL_store (tabs : Tables) (v : Value) (h : v.op = .Store) : termVL tabs v = false := by
  rw [termVL_gen (by decide) h]; decide

/-- `LocalAddr`s are atoms. -/
theorem termVL_localAddr (tabs : Tables) (v : Value) (h : v.op = .LocalAddr) :
    termVL tabs v = false := by
  rw [termVL_gen (by decide) h]; decide

/-- The atoms `ArmRule.Mem` rules match. -/
theorem termVL_mem (tabs : Tables) (v : Value) {o : Op} (ho : o = .Store ∨ o = .LocalAddr)
    (h : v.op = o) : termVL tabs v = false := by
  rcases ho with rfl | rfl
  · exact termVL_store tabs v h
  · exact termVL_localAddr tabs v h

/-- What `atomDef` establishes for one new definition: a lowered store on the same arguments or a
lowered frame address on some of them. -/
theorem atomDef_one {tabs : Tables} {M : Defs} {v : ID} {defs : List Value} {u : Value}
    (h : atomDef tabs M v defs = some (u, none)) : ∃ x, M.get? v = some x ∧ termVL tabs x = false ∧
      termVL tabs u = false ∧ u.type = x.type ∧
      ((u.args = x.args ∧ memLower tabs x u = true) ∨
        ((∀ a ∈ u.args, a ∈ x.args) ∧ addrLower tabs x u = true)) := by
  unfold atomDef at h
  split at h
  · rename_i x _ u' hx
    rw [Option.ite_none_right_eq_some] at h
    obtain ⟨hc, h⟩ := h
    cases h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
      Array.all_eq_true, Array.contains_iff_mem] at hc
    obtain ⟨⟨⟨⟨⟨-, -⟩, ht⟩, ht'⟩, hty⟩, hk⟩ := hc
    refine ⟨x, hx, ht, ht', hty, ?_⟩
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, h2⟩
    · exact .inr ⟨fun a ha => by
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
        exact h1 i hi, h2⟩
  · rename_i x _ u' s hx
    rw [Option.ite_none_right_eq_some] at h
    obtain ⟨-, h⟩ := h
    cases h
  · cases h

/-- What `atomDef` establishes for two new definitions: a lowered frame address on a fresh term
on some of the atom's arguments. -/
theorem atomDef_two {tabs : Tables} {M : Defs} {v : ID} {defs : List Value} {u s : Value}
    (h : atomDef tabs M v defs = some (u, some s)) : ∃ x, M.get? v = some x ∧
      termVL tabs x = false ∧ termVL tabs u = false ∧ u.type = x.type ∧
      addrLower tabs x u = true ∧ u.args = #[s.id] ∧ s.id ≠ v ∧ M.get? s.id = none ∧
      termVL tabs s = true ∧ ∀ a ∈ s.args, a ∈ x.args := by
  unfold atomDef at h
  split at h
  · rename_i x _ u' hx
    rw [Option.ite_none_right_eq_some] at h
    obtain ⟨-, h⟩ := h
    cases h
  · rename_i x _ u' s' hx
    rw [Option.ite_none_right_eq_some] at h
    obtain ⟨hc, h⟩ := h
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, ne_eq,
      Option.isNone_iff_eq_none, Array.all_eq_true, Array.contains_iff_mem] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, ht⟩, ht'⟩, hty⟩, hal⟩, hargs⟩, hne⟩, hn⟩, hts⟩, hs⟩ := hc
    refine ⟨x, hx, ht, ht', hty, hal, hargs, hne, hn, hts, fun a ha => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
    exact hs i hi
  · cases h

section SetOp

variable {tabs : Tables} {M : Defs} {v : ID} {x : Value} {o' : Op}

/-- An ellipsis event on a term refines the denotations (`SetOpSound`), at the same fuel. -/
theorem setOp_den (hx : M.get? v = some x) (ht : termVL tabs x = true)
    (ht' : termVL tabs { x with op := o' } = true) (htop : topOKL x.op (shpL tabs x.type) = true)
    (hso : SetOpSound x.op o') {ρ : ID → Val} :
    ∀ n y, Sem.Refines (denL true M.get? tabs ρ n y)
      (denL true (M.put v { x with op := o' }).get? tabs ρ n y)
  | 0, _ => .poison _
  | n + 1, y => by
    have ih := fun a => setOp_den hx ht ht' htop hso (ρ := ρ) n a
    by_cases hyv : y = v
    · rw [hyv]
      have hnew : (M.put v { x with op := o' }).get? v = some { x with op := o' } := by
        rw [get?_put]; simp
      rw [denT_succ hx ht, denT_succ hnew ht']
      refine Sem.Refines.trans (retypeL_mono _ (opValL_mono_term ht _
        (GoFV.Proof.AtomSim.refinesList_map fun a _ => ih a))) ?_
      exact hso tabs _ _ _ _ htop
    · have hkeep : ∀ w, (M.put v { x with op := o' }).get? y = w ↔ M.get? y = w := by
        intro w; rw [get?_put]; simp [hyv]
      cases hm : M.get? y with
      | none =>
        have h' := (hkeep none).2 hm
        have h1 : ¬ IsTermL tabs M.get? y := fun ⟨u, hu, _⟩ => by rw [hm] at hu; cases hu
        have h2 : ¬ IsTermL tabs (M.put v { x with op := o' }).get? y := fun ⟨u, hu, _⟩ => by
          rw [h'] at hu; cases hu
        rw [denL_succ_atom h1, denL_succ_atom h2]; exact Sem.Refines.refl _
      | some m =>
        have h' := (hkeep (some m)).2 hm
        by_cases htm : termVL tabs m = true
        · rw [denT_succ hm htm, denT_succ h' htm]
          exact retypeL_mono _ (opValL_mono_term htm _
            (GoFV.Proof.AtomSim.refinesList_map fun a _ => setOp_den hx ht ht' htop hso n a))
        · have h1 : ¬ IsTermL tabs M.get? y := fun ⟨u, hu, hu'⟩ => by
            rw [hm] at hu; cases hu; exact htm hu'
          have h2 : ¬ IsTermL tabs (M.put v { x with op := o' }).get? y := fun ⟨u, hu, hu'⟩ => by
            rw [h'] at hu; cases hu; exact htm hu'
          rw [denL_succ_atom h1, denL_succ_atom h2]; exact Sem.Refines.refl _

/-- Replacing an atom by an atom (a rename, a lowered load or store) changes no denotation. -/
theorem rename_den (hx : M.get? v = some x) (ht : termVL tabs x = false) {x' : Value}
    (ht' : termVL tabs x' = false) {ρ : ID → Val} :
    ∀ n y, denL true (M.put v x').get? tabs ρ n y = denL true M.get? tabs ρ n y
  | 0, _ => rfl
  | n + 1, y => by
    by_cases hyv : y = v
    · subst hyv
      have hnew : (M.put y x').get? y = some x' := by
        rw [get?_put]; simp
      have h1 : ¬ IsTermL tabs M.get? y := fun ⟨u, hu, hu'⟩ => by
        rw [hx] at hu; cases hu; rw [ht] at hu'; cases hu'
      have h2 : ¬ IsTermL tabs (M.put y x').get? y := fun ⟨u, hu, hu'⟩ => by
        rw [hnew] at hu; cases hu; rw [ht'] at hu'; cases hu'
      rw [denL_succ_atom h1, denL_succ_atom h2]
    · have h' : (M.put v x').get? y = M.get? y := by rw [get?_put]; simp [hyv]
      simp only [denL, h']
      split
      · rename_i m _
        split
        · congr 2
          exact List.map_congr_left fun a _ => rename_den hx ht ht' n a
        · rfl
      · rfl

/-- `put` of a definition with the same type and term-ness keeps `TypedL`. -/
theorem put_typed {x' : Value} (hx : M.get? v = some x) (hty : x'.type = x.type)
    (htt : termVL tabs x' = termVL tabs x) {ρ : ID → Val} (hT : TypedL true M.get? tabs ρ) :
    TypedL true (M.put v x').get? tabs ρ := by
  intro a ha hsome
  by_cases hav : a = v
  · subst hav
    have hnew : (M.put a x').get? a = some x' := by rw [get?_put]; simp
    have hs : shapeL true (M.put a x').get? tabs a = shapeL true M.get? tabs a := by
      rw [shapeL_of hnew, shapeL_of hx, hty]
    rw [hs]
    refine hT a (fun ⟨u, hu, hu'⟩ => ha ⟨x', hnew, ?_⟩) (by rw [hx]; rfl)
    rw [hx] at hu; cases hu; rw [htt]; exact hu'
  · have h' : (M.put v x').get? a = M.get? a := by rw [get?_put]; simp [hav]
    have hs : shapeL true (M.put v x').get? tabs a = shapeL true M.get? tabs a := by
      simp only [shapeL, h']
    rw [hs]
    exact hT a (fun ⟨u, hu, hu'⟩ => ha ⟨u, by rw [h']; exact hu, hu'⟩) (h' ▸ hsome)

/-- The arguments of a definition of a closed set are in it. -/
theorem closed_args {C : ID → Prop} (hC : DefClosed M C) (hx : M.get? v = some x) (hv : C v) :
    ∀ a ∈ x.args, C a := by
  obtain ⟨m, hm, ha⟩ := hC v hv
  rw [hx] at hm; cases hm; exact ha

/-- `put` of a definition whose arguments are in a closed set (if its key is) keeps it closed. -/
theorem put_closed {x' : Value} {C : ID → Prop} (hcl : C v → ∀ a ∈ x'.args, C a)
    (hC : DefClosed M C) : DefClosed (M.put v x') C := by
  intro y hy
  obtain ⟨m, hm, ha⟩ := hC y hy
  by_cases hyv : y = v
  · subst hyv
    exact ⟨x', by rw [get?_put]; simp, hcl hy⟩
  · exact ⟨m, by rw [get?_put]; simp [hyv, hm], ha⟩

/-- `put` of a definition at a fresh key keeps the denotations of a closed set. -/
theorem denL_put_fresh {k : ID} {s : Value} (hk : M.get? k = none) {C : ID → Prop}
    (hC : DefClosed M C) {low : Bool} {ρ : ID → Val} :
    ∀ n y, C y → denL low (M.put k s).get? tabs ρ n y = denL low M.get? tabs ρ n y
  | 0, _, _ => rfl
  | n + 1, y, hy => by
    obtain ⟨m, hm, hargs⟩ := hC y hy
    have hyk : y ≠ k := fun h => by subst h; rw [hk] at hm; cases hm
    have h' : (M.put k s).get? y = M.get? y := by rw [get?_put]; simp [hyk]
    simp only [denL, h', hm]
    split
    · congr 2
      exact List.map_congr_left fun a ha =>
        denL_put_fresh hk hC n a (hargs a (Array.mem_toList_iff.1 ha))
    · rfl

/-- `put` of a term at a fresh key keeps `TypedL`. -/
theorem put_fresh_typed {k : ID} {s : Value} (hk : M.get? k = none) (hs : termVL tabs s = true)
    {ρ : ID → Val} (hT : TypedL true M.get? tabs ρ) : TypedL true (M.put k s).get? tabs ρ := by
  intro a ha hsome
  by_cases hak : a = k
  · subst hak; exact absurd ⟨s, by rw [get?_put]; simp, hs⟩ ha
  · have h' : (M.put k s).get? a = M.get? a := by rw [get?_put]; simp [hak]
    have hsh : shapeL true (M.put k s).get? tabs a = shapeL true M.get? tabs a := by
      simp only [shapeL, h']
    rw [hsh]
    exact hT a (fun ⟨u, hu, hu'⟩ => ha ⟨u, by rw [h']; exact hu, hu'⟩) (h' ▸ hsome)

end SetOp

/-! ## `copyArg` events -/

section CopyArg

variable {tabs : Tables} {M : Defs} {v : ID} {x : Value} {i : Nat} {src : ID}

theorem copyPut_isTermL (hx : M.get? v = some x) (hi : i < x.args.size) (y : ID) :
    IsTermL tabs (copyPut M v x i src hi).get? y ↔ IsTermL tabs M.get? y := by
  simp only [IsTermL, copyPut_get]
  split
  · subst y; rw [hx]
    constructor
    · rintro ⟨u, hu, ht⟩; cases hu; exact ⟨x, rfl, ht⟩
    · rintro ⟨u, hu, ht⟩; cases hu; exact ⟨_, rfl, ht⟩
  · exact Iff.rfl

theorem copyPut_typedL (hx : M.get? v = some x) (hi : i < x.args.size) {ρ : ID → Val}
    (hT : TypedL true M.get? tabs ρ) : TypedL true (copyPut M v x i src hi).get? tabs ρ :=
  put_typed (x' := { x with args := x.args.set i src hi }) hx rfl rfl hT

theorem copyPut_closedL (hx : M.get? v = some x) (hi : i < x.args.size)
    (hr : copyReachL tabs M M.size x.args[i] src = true) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (copyPut M v x i src hi) C := by
  intro y hy
  obtain ⟨m, hm, hargs⟩ := hC y hy
  rw [copyPut_get]
  split
  · subst y; rw [hx] at hm; cases hm
    refine ⟨_, rfl, fun a ha => ?_⟩
    rcases Array.mem_or_eq_of_mem_set (w := hi) ha with ha | rfl
    · exact hargs a ha
    · exact copyReachL_closed hC _ _ _ hr (hargs _ (Array.getElem_mem hi))
  · exact ⟨m, hm, hargs⟩

/-- A `copyArg` event refines the denotations of a closed set. -/
theorem copyPut_denL (hx : M.get? v = some x) (hi : i < x.args.size)
    (hr : copyReachL tabs M M.size x.args[i] src = true) {C : ID → Prop} (hC : DefClosed M C)
    {ρ : ID → Val} (hT : TypedL true M.get? tabs ρ) :
    ∀ n y, C y → Sem.Refines (denL true M.get? tabs ρ n y)
      (denL true (copyPut M v x i src hi).get? tabs ρ n y)
  | 0, _, _ => .poison _
  | n + 1, y, hy => by
    obtain ⟨m, hm, hargs⟩ := hC y hy
    by_cases ht : IsTermL tabs M.get? y
    · obtain ⟨m', hm', hop⟩ := ht
      rw [hm] at hm'; cases hm'
      by_cases hyv : y = v
      · rw [hyv] at hm ⊢
        rw [hx] at hm; cases hm
        have hnew : (copyPut M v x i src hi).get? v = some { x with args := x.args.set i src hi } := by
          rw [copyPut_get]; simp
        rw [denT_succ hx hop, denT_succ hnew hop]
        apply retypeL_mono; apply opValL_mono_term hop
        refine refinesList_idx (by simp) fun j h1 h2 => ?_
        simp only [Array.getElem_toList, Array.getElem_set]
        split
        · rename_i hij; subst hij
          exact (copyReachL_den hT _ _ _ hr n).trans
            (copyPut_denL hx hi hr hC hT n src (copyReachL_closed hC _ _ _ hr
              (hargs _ (Array.getElem_mem hi))))
        · exact copyPut_denL hx hi hr hC hT n _ (hargs _ (Array.getElem_mem _))
      · have hkeep : (copyPut M v x i src hi).get? y = some m := by
          rw [copyPut_get]; simp [hyv, hm]
        rw [denT_succ hm hop, denT_succ hkeep hop]
        exact retypeL_mono _ (opValL_mono_term hop _ (GoFV.Proof.AtomSim.refinesList_map fun a ha =>
          copyPut_denL hx hi hr hC hT n a (hargs a (Array.mem_toList_iff.1 ha))))
    · have ht' : ¬ IsTermL tabs (copyPut M v x i src hi).get? y := fun h =>
        ht ((copyPut_isTermL hx hi y).1 h)
      rw [denL_succ_atom ht, denL_succ_atom ht']; exact Sem.Refines.refl _

end CopyArg

/-! ## The replay invariant -/

/-- The arguments of `a'` (in `M`) are as many as those of `a` (in `D₀`), in `C`, and refine
them. -/
def ArgsRefL (tabs : Tables) (D₀ : ID → Option Value) (M : Defs) (C : ID → Prop) (a a' : Value) :
    Prop :=
  a'.args.size = a.args.size ∧
    ∀ i < a.args.size, C a'.args[i]! ∧ ∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ →
      Sem.Refines (denL true D₀ tabs ρ n a.args[i]!) (denL true M.get? tabs ρ m a'.args[i]!)

/-- What holds along the replay from the definitions `D₀` (lowered mode) and a closed set `C₀`:
the current definitions `M` with a set `C ⊇ C₀` closed under arguments; refining denotations of
`C₀`; the atoms of `D₀` with arguments in `C₀` stay atoms of the same type, with refining
arguments unless they read none (`argFree`, a lowered frame address). -/
structure ReplayInvL (tabs : Tables) (D₀ : ID → Option Value) (C₀ : ID → Prop) (M : Defs)
    (C : ID → Prop) : Prop where
  closed : DefClosed M C
  sub : ∀ y, C₀ y → C y
  typed : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ
  denRef : ∀ y, C₀ y → ∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ →
    Sem.Refines (denL true D₀ tabs ρ n y) (denL true M.get? tabs ρ m y)
  atoms : ∀ y a, D₀ y = some a → termVL tabs a = false → (∀ b ∈ a.args, C₀ b) →
    ∃ a', M.get? y = some a' ∧ termVL tabs a' = false ∧
      (argFree tabs a' = true ∨ ArgsRefL tabs D₀ M C a a')

theorem ReplayInvL.init {tabs : Tables} {M : Defs} {C₀ : ID → Prop} (hC : DefClosed M C₀) :
    ReplayInvL tabs M.get? C₀ M C₀ where
  closed := hC
  sub := fun _ h => h
  typed := fun _ h => h
  denRef := fun _ _ n => ⟨n, fun _ _ => Sem.Refines.refl _⟩
  atoms := fun y a hy ha hargs => ⟨a, hy, ha, .inr ⟨rfl, fun i hi =>
    ⟨hargs _ (by rw [getElem!_pos a.args i hi]; exact Array.getElem_mem hi),
      fun n => ⟨n, fun _ _ => Sem.Refines.refl _⟩⟩⟩⟩

section Inv

variable {tabs : Tables} {D₀ : ID → Option Value} {C₀ : ID → Prop} {M : Defs} {C : ID → Prop}

/-- Compose a refinement from `D₀` with one step `M → M'`. -/
theorem denL_compose {M' : Defs} {y y' : ID} {g : Nat → Nat}
    (h1 : ∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ →
      Sem.Refines (denL true D₀ tabs ρ n y) (denL true M.get? tabs ρ m y'))
    (hty : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ)
    (h2 : ∀ ρ, TypedL true M.get? tabs ρ → ∀ n,
      Sem.Refines (denL true M.get? tabs ρ n y') (denL true M'.get? tabs ρ (g n) y')) :
    ∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ →
      Sem.Refines (denL true D₀ tabs ρ n y) (denL true M'.get? tabs ρ m y') := by
  intro n
  obtain ⟨m, hm⟩ := h1 n
  exact ⟨g m, fun ρ hρ => (hm ρ hρ).trans (h2 ρ (hty ρ hρ) m)⟩

/-- `ArgsRefL` along a step `M → M'` refining the denotations of `C ⊆ C'`. -/
theorem ArgsRefL.step {M' : Defs} {C' : ID → Prop} {a a' : Value} {g : Nat → Nat}
    (h : ArgsRefL tabs D₀ M C a a') (hsub : ∀ y, C y → C' y)
    (hty : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ)
    (hstep : ∀ ρ, TypedL true M.get? tabs ρ → ∀ n y, C y →
      Sem.Refines (denL true M.get? tabs ρ n y) (denL true M'.get? tabs ρ (g n) y)) :
    ArgsRefL tabs D₀ M' C' a a' :=
  ⟨h.1, fun i hi => ⟨hsub _ (h.2 i hi).1,
    denL_compose (h.2 i hi).2 hty fun ρ hρ n => hstep ρ hρ n _ (h.2 i hi).1⟩⟩

theorem ReplayInvL.rule {r : Rule} {v : ID} {defs : List Value} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hs : ArmRule.Sound1 r) (F : RuleFactsL tabs M r v defs) :
    ReplayInvL tabs D₀ C₀ (putAll M defs) (fun y => C y ∨ (C v ∧ y ∈ defIds defs)) where
  closed := F.closed hI.closed
  sub := fun y h => .inl (hI.sub y h)
  typed := fun ρ h => F.typed (hI.typed ρ h)
  denRef := fun y hy => denL_compose (hI.denRef y hy) hI.typed
    fun ρ hρ n => F.step hs hI.closed hρ n y (hI.sub y hy)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
    exact ⟨a', F.keepAtom ha' hat, hat, hrest.imp id fun hr =>
      hr.step (fun _ h => .inl h) hI.typed fun ρ hρ n z hz => F.step hs hI.closed hρ n z hz⟩

theorem ReplayInvL.setOp {v : ID} {x : Value} {o' : Op} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (ht : termVL tabs x = true)
    (ht' : termVL tabs { x with op := o' } = true) (htop : topOKL x.op (shpL tabs x.type) = true)
    (hso : SetOpSound x.op o') :
    ReplayInvL tabs D₀ C₀ (M.put v { x with op := o' }) C where
  closed := put_closed (x' := { x with op := o' }) (fun hv a ha => closed_args hI.closed hx hv a ha)
    hI.closed
  sub := hI.sub
  typed := fun ρ h => put_typed (x' := { x with op := o' }) hx rfl (by rw [ht, ht']) (hI.typed ρ h)
  denRef := fun y hy => denL_compose (g := id) (hI.denRef y hy) hI.typed
    fun ρ _ n => setOp_den hx ht ht' htop hso n y
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
    have hyv : y ≠ v := fun h => by subst h; rw [hx] at ha'; cases ha'; rw [ht] at hat; cases hat
    exact ⟨a', by rw [get?_put]; simp [hyv, ha'], hat, hrest.imp id fun hr =>
      hr.step (g := id) (fun _ h => h) hI.typed fun ρ _ n z _ => setOp_den hx ht ht' htop hso n z⟩

/-- Replacing the atom `x` at `v` by an atom `x'` of the same type: a rename, a lowered store
(the same arguments) or a lowered frame address (`argFree`). -/
theorem ReplayInvL.atomPut {v : ID} {x x' : Value} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (ht : termVL tabs x = false) (ht' : termVL tabs x' = false)
    (hty : x'.type = x.type) (hcl : C v → ∀ a ∈ x'.args, C a)
    (hargs : argFree tabs x' = true ∨
      (x'.args = x.args ∧ (argFree tabs x = true → argFree tabs x' = true))) :
    ReplayInvL tabs D₀ C₀ (M.put v x') C where
  closed := put_closed hcl hI.closed
  sub := hI.sub
  typed := fun ρ h => put_typed hx hty (by rw [ht, ht']) (hI.typed ρ h)
  denRef := fun y hy => denL_compose (g := id) (hI.denRef y hy) hI.typed
    fun ρ _ n => by rw [rename_den hx ht ht']; exact Sem.Refines.refl _
  atoms := fun y a hy ha hargs' => by
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs'
    have hstep : ∀ ρ, TypedL true M.get? tabs ρ → ∀ n z, C z →
        Sem.Refines (denL true M.get? tabs ρ n z) (denL true (M.put v x').get? tabs ρ (id n) z) :=
      fun ρ _ n z _ => by rw [rename_den hx ht ht']; exact Sem.Refines.refl _
    by_cases hyv : y = v
    · subst hyv
      rw [hx] at ha'; cases ha'
      refine ⟨x', by rw [get?_put]; simp, ht', ?_⟩
      rcases hargs with hf | ⟨heq, hf⟩
      · exact .inl hf
      · rcases hrest with hr | hr
        · exact .inl (hf hr)
        · refine .inr ?_
          have hr' := hr.step (fun _ h => h) hI.typed hstep
          unfold ArgsRefL at hr' ⊢
          rw [heq]; exact hr'
    · exact ⟨a', by rw [get?_put]; simp [hyv, ha'], hat, hrest.imp id fun hr =>
        hr.step (fun _ h => h) hI.typed hstep⟩

/-- Putting a term at a fresh key; the key joins the closed set if `P` holds. -/
theorem ReplayInvL.fresh {s : Value} {P : Prop} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hk : M.get? s.id = none) (hs : termVL tabs s = true) (hcl : P → ∀ a ∈ s.args, C a) :
    ReplayInvL tabs D₀ C₀ (M.put s.id s) (fun y => C y ∨ (P ∧ y = s.id)) where
  closed := by
    intro y hy
    rcases hy with hy | ⟨hp, rfl⟩
    · obtain ⟨m, hm, ha⟩ := hI.closed y hy
      have hyk : y ≠ s.id := fun h => by subst h; rw [hk] at hm; cases hm
      exact ⟨m, by rw [get?_put]; simp [hyk, hm], fun a h => .inl (ha a h)⟩
    · exact ⟨s, by rw [get?_put]; simp, fun a h => .inl (hcl hp a h)⟩
  sub := fun y h => .inl (hI.sub y h)
  typed := fun ρ h => put_fresh_typed hk hs (hI.typed ρ h)
  denRef := fun y hy => denL_compose (g := id) (hI.denRef y hy) hI.typed
    fun ρ _ n => by rw [denL_put_fresh hk hI.closed _ y (hI.sub y hy)]; exact Sem.Refines.refl _
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
    have hyk : y ≠ s.id := fun h => by subst h; rw [hk] at ha'; cases ha'
    exact ⟨a', by rw [get?_put]; simp [hyk, ha'], hat, hrest.imp id fun hr =>
      hr.step (g := id) (fun _ h => .inl h) hI.typed fun ρ _ n z hz => by
        rw [denL_put_fresh hk hI.closed _ z hz]; exact Sem.Refines.refl _⟩

theorem ReplayInvL.copy {v : ID} {x : Value} {i : Nat} {src : ID} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (hi : i < x.args.size)
    (hr : copyReachL tabs M M.size x.args[i] src = true) :
    ReplayInvL tabs D₀ C₀ (copyPut M v x i src hi) C where
  closed := copyPut_closedL hx hi hr hI.closed
  sub := hI.sub
  typed := fun ρ h => copyPut_typedL hx hi (hI.typed ρ h)
  denRef := fun y hy => denL_compose (g := id) (hI.denRef y hy) hI.typed
    fun ρ hρ n => copyPut_denL hx hi hr hI.closed hρ n y (hI.sub y hy)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
    have hstep : ∀ ρ, TypedL true M.get? tabs ρ → ∀ n z, C z →
        Sem.Refines (denL true M.get? tabs ρ n z)
          (denL true (copyPut M v x i src hi).get? tabs ρ (id n) z) :=
      fun ρ hρ n z hz => copyPut_denL hx hi hr hI.closed hρ n z hz
    by_cases hyv : y = v
    · rw [hyv] at ha'; rw [hx] at ha'; cases ha'
      refine ⟨{ x with args := x.args.set i src hi }, by rw [copyPut_get]; simp [hyv], hat, ?_⟩
      rcases hrest with hf | ⟨hsz, hrest⟩
      · exact .inl hf
      refine .inr ⟨by simpa using hsz, fun j hj => ?_⟩
      have hj' : j < x.args.size := hsz ▸ hj
      simp only [set_getElem! hi hj']
      split
      · rename_i hij; subst hij
        have hold := (hrest i hj).1
        rw [getElem!_pos x.args i hi] at hold
        have hsrc := copyReachL_closed hI.closed _ _ _ hr hold
        refine ⟨hsrc, ?_⟩
        have h1 := (hrest i hj).2
        rw [getElem!_pos x.args i hi] at h1
        intro n
        obtain ⟨m, hm⟩ := h1 n
        exact ⟨m, fun ρ hρ => (hm ρ hρ).trans ((copyReachL_den (hI.typed ρ hρ) _ _ _ hr m).trans
          (hstep ρ (hI.typed ρ hρ) m src hsrc))⟩
      · exact ⟨(hrest j hj).1, denL_compose (g := id) (hrest j hj).2 hI.typed
          fun ρ hρ n => hstep ρ hρ n _ (hrest j hj).1⟩
    · exact ⟨a', by rw [copyPut_get]; simp [hyv, ha'], hat, hrest.imp id fun hr =>
        hr.step (fun _ h => h) hI.typed hstep⟩

end Inv

/-- What `ruleOKL` establishes: the matched value is a term and some commutation choice
validates. -/
theorem ruleOKL_facts {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}
    (h : ruleOKL tabs M r v defs = true) : ∃ sw ∈ choices (GoFV.Opt.RewriteCheck.Pat.commutes r.pat),
      Nonempty (RuleFactsL tabs M (Rule.swapC r sw) v defs) := by
  unfold ruleOKL at h
  split at h
  · cases h
  · rename_i x hx
    simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
    obtain ⟨⟨ht, hid⟩, sw, hsw, h1⟩ := h
    exact ⟨sw, hsw, ruleFactsL hx ht hid h1⟩

/-- **Replay**: a successful replay of the log keeps `ReplayInvL` and `BInvL`. -/
theorem replayL_inv {tabs : Tables} {s : RuleSet} (hs : ArmRuleSet.AllSound s)
    {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop} :
    ∀ (evs : List RwEvent) (M M' : Defs) (B B' : BMapL) (C : ID → Prop),
      replayL tabs (GoFV.Rules.Interp.Table.ofRuleSet s) f M B evs = some (M', B') →
      ReplayInvL tabs D₀ C₀ M C → BInvL tabs f D₀ C₀ M C B →
      ∃ C', ReplayInvL tabs D₀ C₀ M' C' ∧ BInvL tabs f D₀ C₀ M' C' B'
  | [], M, M', B, B', C, h, hI, hB => by
    simp only [replayL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨C, hI, hB⟩
  | .rule v i _ defs :: evs, M, M', B, B', C, h, hI, hB => by
    unfold replayL at h
    split at h
    · cases h
    rename_i x hx
    split at h
    · cases h
    rename_i cr hcr
    have hck := ofRuleSetL_checked hs hcr
    split at h
    · -- ellipsis rules
      rename_i o' hres
      split at h
      · rename_i x' hdef
        obtain ⟨x0, o2, hx0, hr2, rfl, he, hk⟩ := setOpDef_facts hdef
        rw [hx] at hx0; cases hx0
        rw [hres] at hr2; cases hr2
        rcases hk with ⟨ht, ht', htop⟩ | ⟨hren, ht⟩
        · have hso : SetOpSound x.op o' := by
            rcases hck with hsd | ⟨o, o3, he3, hr3, -, -, -, -, hso⟩ | ⟨o, o3, he3, hr3, -, -, hren⟩ |
                ⟨om, n, pty, pai, pax, par, pargs, pc, hpat, hom⟩
            · exact absurd hsd (not_sound_of_ellipsis he)
            · obtain ⟨c, hc⟩ := ellipsisOn_eq he
              obtain ⟨c', hc'⟩ := ellipsisOn_eq he3
              rw [hc] at hc'; cases hc'
              rw [hres] at hr3; cases hr3
              exact hso
            · obtain ⟨c, hc⟩ := ellipsisOn_eq he
              obtain ⟨c', hc'⟩ := ellipsisOn_eq he3
              rw [hc] at hc'; cases hc'
              rw [renameOp_src hren tabs x rfl] at ht; cases ht
            · obtain ⟨c, hc⟩ := ellipsisOn_eq he
              rw [hc] at hpat
              injection hpat with hxo
              rw [termVL_mem tabs x hom hxo] at ht; cases ht
          exact replayL_inv hs evs _ M' B B' C h (hI.setOp hx ht ht' htop hso)
            (hB.mono (g := id) (fun _ h => h) hI.typed fun ρ _ n y _ => setOp_den hx ht ht' htop hso n y)
        · have ht' := renameOp_dst hren tabs { x with op := o' } rfl
          have hfree : argFree tabs x = true → argFree tabs { x with op := o' } = true :=
            fun hf => absurd (argFree_cases hf).1 (renameOp_src_ne hren)
          exact replayL_inv hs evs _ M' B B' C h
            (hI.atomPut hx ht ht' rfl (fun hv a ha => closed_args hI.closed hx hv a ha)
              (.inr ⟨rfl, hfree⟩))
            (hB.mono (g := id) (fun _ h => h) hI.typed fun ρ _ n y _ => by
              rw [rename_den hx ht ht']; exact Sem.Refines.refl _)
      · cases h
    · -- value rules
      rename_i hnot
      split at h
      · rename_i hok
        obtain ⟨sw, hsw, ⟨F⟩⟩ := ruleOKL_facts hok
        have hsd : ArmRule.Sound1 (Rule.swapC cr.rule sw) := by
          rcases hck with hsd | ⟨o, o3, -, hr3, -⟩ | ⟨o, o3, -, hr3, -⟩ |
              ⟨om, n, pty, pai, pax, par, pargs, pc, hpat, hom⟩
          · exact hsd sw hsw
          · exact absurd hr3 (hnot o3)
          · exact absurd hr3 (hnot o3)
          · exfalso
            obtain ⟨args', sw', hs'⟩ := swapC_op om n pty pai pax par pargs pc sw
            have hp' : (Rule.swapC cr.rule sw).pat = .op om n pty pai pax par args' false := by
              simp only [Rule.swapC, hpat, hs']
            have hm := F.hmatch
            rw [F.hpat] at hp' hm
            injection hp' with ho
            obtain ⟨-, x', hx', hop, ht', -⟩ := hm
            rw [termVL_mem tabs x' hom (hop.trans ho)] at ht'; cases ht'
        have hput : defs.foldl (fun M u => M.put u.id u) M = putAll M defs.toList := by
          simp [putAll, Array.foldl_toList]
        rw [hput] at h
        exact replayL_inv hs evs _ M' B B' _ h (hI.rule hsd F)
          (hB.mono (fun y hy => .inl hy) hI.typed fun ρ hρ n y hy => F.step hsd hI.closed hρ n y hy)
      · -- a lowered store or frame address (`atomDef`)
        split at h
        · rename_i u hdef
          obtain ⟨x0, hx0, ht, ht', hty, hk⟩ := atomDef_one hdef
          have hcl : C v → ∀ a ∈ u.args, C a := fun hv a ha => by
            have hxa := closed_args hI.closed hx0 hv
            rcases hk with ⟨heq, -⟩ | ⟨hsub, -⟩
            · exact hxa a (heq ▸ ha)
            · exact hxa a (hsub a ha)
          have hfree : argFree tabs u = true ∨
              (u.args = x0.args ∧ (argFree tabs x0 = true → argFree tabs u = true)) := by
            rcases hk with ⟨heq, hm⟩ | ⟨-, hal⟩
            · exact .inr ⟨heq, fun hf =>
                absurd ((memLower_op hm).symm.trans (argFree_cases hf).1) (by decide)⟩
            · exact .inl (argFree_of_addrLower hal)
          exact replayL_inv hs evs _ M' B B' C h (hI.atomPut hx0 ht ht' hty hcl hfree)
            (hB.mono (g := id) (fun _ h => h) hI.typed fun ρ _ n y _ => by
              rw [rename_den hx0 ht ht']; exact Sem.Refines.refl _)
        · rename_i u s hdef
          obtain ⟨x0, hx0, ht, ht', hty, hal, hua, hsv, hsn, hst, hsa⟩ := atomDef_two hdef
          have hI1 := hI.fresh (P := C v) hsn hst fun hv a ha =>
            closed_args hI.closed hx0 hv a (hsa a ha)
          have hx1 : (M.put s.id s).get? v = some x0 := by
            rw [get?_put]; simp [show v ≠ s.id from fun h => hsv h.symm, hx0]
          have hcl : (C v ∨ (C v ∧ v = s.id)) → ∀ a ∈ u.args, (C a ∨ (C v ∧ a = s.id)) :=
            fun hv a ha => by
              rw [hua] at ha
              have : a = s.id := by simpa using ha
              exact .inr ⟨hv.elim id (·.1), this⟩
          have hI2 := hI1.atomPut hx1 ht ht' hty hcl (.inl (argFree_of_addrLower hal))
          have hB1 := hB.mono (M' := M.put s.id s) (C' := fun y => C y ∨ (C v ∧ y = s.id)) (g := id)
            (fun y h => .inl h)
            hI.typed fun ρ _ n y hy => by
              rw [denL_put_fresh hsn hI.closed _ y hy]; exact Sem.Refines.refl _
          exact replayL_inv hs evs _ M' B B' _ h hI2
            (hB1.mono (g := id) (fun _ h => h) hI1.typed fun ρ _ n y _ => by
              rw [rename_den hx1 ht ht']; exact Sem.Refines.refl _)
        · cases h
  | .copyArg v i src :: evs, M, M', B, B', C, h, hI, hB => by
    unfold replayL at h
    split at h
    · cases h
    rename_i x hx
    split at h
    · rename_i hi
      split at h
      · rename_i hrc
        exact replayL_inv hs evs _ M' B B' C h (hI.copy hx hi hrc)
          (hB.mono (g := id) (fun _ h => h) hI.typed fun ρ hρ n y hy =>
            copyPut_denL hx hi hrc hI.closed hρ n y hy)
      · exact replayL_inv hs evs M M' B B' C h hI hB
    · cases h
  | .control b i c :: evs, M, M', B, B', C, h, hI, hB => by
    unfold replayL at h
    split at h
    · cases h
    rename_i st hst
    split at h
    · rename_i hi
      split at h
      · rename_i hrc
        exact replayL_inv hs evs M M' _ B' C h hI (hB.control hI.closed hI.typed hst hi hrc)
      · cases h
    · cases h
  | .phielim .. :: _, M, M', B, B', C, h, _, _ => by simp [replayL] at h
  | .snap .. :: _, M, M', B, B', C, h, _, _ => by simp [replayL] at h
  | .blockRule b i nc :: evs, M, M', B, B', C, h, hI, hB => by
    unfold replayL at h
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
    rename_i st' hok
    exact replayL_inv hs evs M M' _ B' C h hI
      (hB.block hI.closed hI.typed hst h2' (ofRuleSetL_blockSound hs hbr) hok)

end GoFV.Proof.Low.Val
