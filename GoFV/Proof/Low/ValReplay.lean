import GoFV.Proof.Low.ValBlock
import GoFV.Proof.Low.AddrFold
import GoFV.Proof.Low.ValMul

/-!
# Replaying the lowering log refines the denotations (issue #385)

The lowered counterpart of `GoFV/Proof/Pass/RewriteTermReplay.lean` and `replay_inv`
(`RewriteTermBlock.lean`) for `GoFV.Opt.LowerCheck.replayL`: starting from the input's
definitions `D₀` read in lowered mode and a set `C₀` closed under arguments, the atoms of `D₀`
whose arguments are in `C₀` stay atoms (renamed, `renameOp`; lowered stores and frame addresses,
`atomDef`) whose arguments (rewritten by `copyArg` events, through compatible copies) keep related
denotations (`ReplayInvL.atoms`, the one place that relates an atom's arguments: `ArgRel` of
`stArg`, refinement, or for the address of an arm64 store lowering a `Store` the `AddrRef` at its
offset and aux, which an `ADDconst` offset folded into the store keeps, `ReplayInvL.fold`, and a
global symbol's or frame variable's address, `ReplayInvL.foldAddr`, the latter in every activation
whose frame addresses the valuation holds, `FrameVals`; a `Store` lowered to an indexed store
relates its address to the indexed store's base and index, `IdxRefL`, `ReplayInvL.idxFold`).
Value rule events use `RuleFactsL.step` and `ArmRule.Sound1`, ellipsis events on terms
`SetOpSoundT` (`setOp_den`), atom replacements change no denotation (`rename_den`); terminators
keep `BInvL`.
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

/-- Every block rule of the table of a sound lowering rule set is `BlockRuleL.Checked`. -/
theorem ofRuleSetL_blockSound {s : RuleSet} (hs : ArmRuleSet.AllSound s) {k i : Nat}
    {br : BlockRule}
    (h : ((GoFV.Rules.Interp.Table.ofRuleSet s).blocks[k]?).bind (·[i]?) = some br) :
    BlockRuleL.Checked br := by
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
    (hm : (o == .ARM64MOVDaddr) = false) (hl : ldOp? o = none)
    (hd : GoFV.Opt.LowerTerm.pureActOp o = false) (hv : v.op = o) :
    termVL tabs v = (GoFV.Opt.LowerTerm.armTerm o && !GoFV.Opt.LowerTerm.actOp o && !isRoot o) := by
  unfold termVL; rw [hv]; simp only [hg, hm, hl, hd, Option.isSome_none, Bool.false_eq_true, ite_false]

theorem renameOp_src {o o' : Op} (h : renameOp o o' = true) (tabs : Tables) (v : Value)
    (hv : v.op = o) : termVL tabs v = false := by
  unfold renameOp at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · unfold callRename at h
    split at h <;> first
      | (cases h; done)
      | (rw [termVL_gen (by decide) hv]; decide)
      | (rw [termVL_arm (by decide) (by decide) (by decide) (by decide) hv]; decide)
  · unfold atomicRen at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨rfl, -⟩
    · unfold Arm64.atomicOf at h
      split at h <;> first
        | (cases h; done)
        | (cases h; rw [termVL_gen (by decide) hv]; decide)
    · rw [termVL_gen (by decide) hv]; decide

theorem renameOp_dst {o o' : Op} (h : renameOp o o' = true) (tabs : Tables) (v : Value)
    (hv : v.op = o') : termVL tabs v = false := by
  unfold renameOp at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · unfold callRename at h
    split at h <;> first
      | (cases h; done)
      | (rw [termVL_gen (by decide) hv]; decide)
      | (rw [termVL_arm (by decide) (by decide) (by decide) (by decide) hv]; decide)
  · unfold atomicRen at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨-, rfl⟩
    · unfold Arm64.atomicOf at h
      split at h <;> first
        | (cases h; done)
        | (cases h; rw [termVL_arm (by decide) (by decide) (by decide) (by decide) hv]; decide)
    · rw [termVL_arm (by decide) (by decide) (by decide) (by decide) hv]; decide

/-- A renamed atom is no `MOVDaddr`. -/
theorem renameOp_src_ne {o o' : Op} (h : renameOp o o' = true) : o ≠ .ARM64MOVDaddr := by
  unfold renameOp at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · unfold callRename at h
    split at h <;> first | (cases h; done) | (intro h'; cases h')
  · intro h'
    have := (atomicRen_facts h).1
    rw [h'] at this; exact absurd this (by decide)

/-- A renamed atom is no indexed store. -/
theorem renameOp_idx {o o' : Op} (h : renameOp o o' = true) : idxStore o = none := by
  unfold renameOp at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · unfold callRename at h
    split at h <;> first | (cases h; done) | rfl
  · cases hi : idxStore o with
    | none => rfl
    | some p =>
      obtain ⟨p, s⟩ := p
      exact absurd (atomicRen_facts h).1 (by rw [(idxStore_facts hi).1]; decide)

/-- What `setOpDef` establishes. -/
theorem setOpDef_facts {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {x' : Value}
    (h : setOpDef tabs M r v = some x') : ∃ x o', M.get? v = some x ∧ r.result = .setOp o' ∧
      x' = { x with op := o' } ∧ ellipsisOn x.op r.pat = true ∧
      ((termVL tabs x = true ∧ termVL tabs x' = true ∧ topOKL x.op (shpL tabs x.type) = true ∧
          setArgsOK tabs M x = true) ∨
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
      rcases hk with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨h1, h2⟩
      · exact .inl ⟨h1, h2, h3, h4⟩
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

/-- `Zero`s are atoms. -/
theorem termVL_zero (tabs : Tables) (v : Value) (h : v.op = .Zero) : termVL tabs v = false := by
  rw [termVL_gen (by decide) h]; decide

/-- `Move`s are atoms. -/
theorem termVL_move (tabs : Tables) (v : Value) (h : v.op = .Move) : termVL tabs v = false := by
  rw [termVL_gen (by decide) h]; decide

/-- `LocalAddr`s are atoms. -/
theorem termVL_localAddr (tabs : Tables) (v : Value) (h : v.op = .LocalAddr) :
    termVL tabs v = false := by
  rw [termVL_gen (by decide) h]; decide

/-- The arm64 stores are atoms. -/
theorem termVL_st (tabs : Tables) (v : Value) {o : Op} (ho : (stSize o).isSome = true)
    (h : v.op = o) : termVL tabs v = false := by
  unfold stSize at ho
  split at ho <;> first
    | (cases ho; done)
    | (rw [termVL_arm (by decide) (by decide) (by decide) (by decide) h]; decide)

/-- The indexed arm64 stores are atoms. -/
theorem termVL_idx (tabs : Tables) (v : Value) {o : Op} (ho : (idxStore o).isSome = true)
    (h : v.op = o) : termVL tabs v = false := by
  unfold idxStore at ho
  split at ho <;> first
    | (cases ho; done)
    | (rw [termVL_arm (by decide) (by decide) (by decide) (by decide) h]; decide)

/-- The lowered bounds panics are atoms. -/
theorem termVL_pb (tabs : Tables) (v : Value) {o : Op} (ho : pbAtom o = true)
    (h : v.op = o) : termVL tabs v = false := by
  unfold pbAtom at ho
  split at ho <;> first
    | (cases ho; done)
    | (rw [termVL_arm (by decide) (by decide) (by decide) (by decide) h]; decide)

/-- The lowered bounds panics with constant operands are atoms. -/
theorem termVL_pbKeep (tabs : Tables) (v : Value) {o : Op} {ks : List Nat} (hk : pbKeep o = some ks)
    (h : v.op = o) : termVL tabs v = false := by
  unfold pbKeep at hk
  split at hk <;> first
    | (cases hk; done)
    | (rw [termVL_arm (by decide) (by decide) (by decide) (by decide) h]; decide)

/-- The atoms `ArmRule.Mem` rules match. -/
theorem termVL_mem (tabs : Tables) (v : Value) {o : Op}
    (ho : o = .Store ∨ o = .LocalAddr ∨ ((stSize o).isSome = true ∨ (idxStore o).isSome = true) ∨
      pbAtom o = true ∨ o = .Zero ∨ o = .Move)
    (h : v.op = o) : termVL tabs v = false := by
  rcases ho with rfl | rfl | (ho | ho) | ho | rfl | rfl
  · exact termVL_store tabs v h
  · exact termVL_localAddr tabs v h
  · exact termVL_st tabs v ho h
  · exact termVL_idx tabs v ho h
  · exact termVL_pb tabs v ho h
  · exact termVL_zero tabs v h
  · exact termVL_move tabs v h

theorem any_store {o : Option Value} (h : o.any (·.op == .Store) = true) :
    ∃ a, o = some a ∧ a.op = .Store := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, by simpa using h⟩

theorem any_store3 {o : Option Value}
    (h : o.any (fun a => a.op == .Store && a.args.size == 3) = true) :
    ∃ a, o = some a ∧ a.op = .Store ∧ a.args.size = 3 := by
  cases o with
  | none => cases h
  | some a =>
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨a, rfl, h⟩

/-- What `atomDef` establishes for one new definition: a lowered store on the same arguments at
offset 0 without aux, a lowered frame address on some of them, or an offset or a symbol's or frame
variable's address folded into an arm64 store of a `Store` of `f`, or that store indexed, or its
index scaled (a narrow store's value read back through a narrowing `Copy`, `stValPick`). -/
theorem atomDef_one {tabs : Tables} {f : Func} {M : Defs} {v : ID} {defs : List Value} {u : Value}
    (h : atomDef tabs f M v defs = some (u, none)) : ∃ x, M.get? v = some x ∧
      termVL tabs x = false ∧ termVL tabs u = false ∧ u.type = x.type ∧
      ((u.args = x.args ∧ memLower tabs x u = true ∧ u.auxInt = 0 ∧ u.aux = none) ∨
        (u.args = x.args ∧ bulkLower x u = true) ∨
        ((∀ a ∈ u.args, a ∈ x.args) ∧ addrLower tabs x u = true) ∨
        ((stFold tabs M x u = true ∨ stFoldAddr tabs f M x u = true ∨
            stIdxFold tabs M x u = true) ∧
          ∃ a, f.value? v = some a ∧ a.op = .Store) ∨
        (stIdxScale tabs M x u = true ∧
          ∃ a, f.value? v = some a ∧ a.op = .Store ∧ a.args.size = 3)) := by
  unfold atomDef at h
  split at h
  · rename_i x _ u' hx
    unfold atomDef1 at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨-, -⟩, ht⟩, ht'⟩, hty⟩, hk⟩ := hc
      simp only [Bool.not_eq_true'] at ht ht'
      refine ⟨x, hx, ht, ht', beq_iff_eq.1 hty, ?_⟩
      rcases hk with (((⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · exact .inl ⟨beq_iff_eq.1 h1, h2, beq_iff_eq.1 h3, beq_iff_eq.1 h4⟩
      · exact .inr (.inl ⟨beq_iff_eq.1 h1, h2⟩)
      · refine .inr (.inr (.inl ⟨fun a ha => ?_, h2⟩))
        simp only [Array.all_eq_true, Array.contains_iff_mem] at h1
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
        exact h1 i hi
      · exact .inr (.inr (.inr (.inl ⟨or_assoc.1 h1, any_store h2⟩)))
      · exact .inr (.inr (.inr (.inr ⟨h1, any_store3 h2⟩)))
    · cases h
  · rename_i x _ u' s hx
    rw [Option.ite_none_right_eq_some] at h
    obtain ⟨-, h⟩ := h
    cases h
  · cases h

/-- What `atomDef` establishes for two new definitions: a lowered frame address on a fresh term
on some of the atom's arguments. -/
theorem atomDef_two {tabs : Tables} {f : Func} {M : Defs} {v : ID} {defs : List Value}
    {u s : Value} (h : atomDef tabs f M v defs = some (u, some s)) : ∃ x, M.get? v = some x ∧
      termVL tabs x = false ∧ termVL tabs u = false ∧ u.type = x.type ∧
      addrLower tabs x u = true ∧ u.args = #[s.id] ∧ s.id ≠ v ∧ M.get? s.id = none ∧
      termVL tabs s = true ∧ ∀ a ∈ s.args, a ∈ x.args := by
  unfold atomDef at h
  split at h
  · rename_i x _ u' hx
    unfold atomDef1 at h
    split at h <;> cases h
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

/-- The arguments `setArgW64` asks for, denoted under `TypedL`, are 64-bit integers
(`setArgsOK`, `den_hasTyL`). -/
theorem setArgs_hasTy {ρ : ID → Val} (hT : TypedL true M.get? tabs ρ)
    (hs : setArgsOK tabs M x = true) (n : Nat) :
    ∀ i w, (x.args.toList.map (denL true M.get? tabs ρ n))[i]? = some w →
      setArgW64 x.op i = true → w.hasTy (.int .w64) = true := by
  intro i w hw hi
  simp only [List.getElem?_map, Array.getElem?_toList, Option.map_eq_some_iff] at hw
  obtain ⟨a, ha, rfl⟩ := hw
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 ha
  have ha' : x.args[i]! = a := by rw [getElem!_def, ha]
  unfold setArgsOK at hs
  rw [List.all_eq_true] at hs
  have h1 := hs i (List.mem_range.2 hlt)
  simp only [hi, Bool.not_true, Bool.false_or, ha'] at h1
  cases hy : M.get? a with
  | none => rw [hy] at h1; cases h1
  | some y =>
    rw [hy, Option.any_some, GoFV.Proof.Rules.isInt64Ty_iff] at h1
    have h := den_hasTyL hT n hy
    rwa [h1] at h

/-- An ellipsis event on a term refines the denotations (`SetOpSoundT`), at the same fuel. -/
theorem setOp_den (hx : M.get? v = some x) (ht : termVL tabs x = true)
    (ht' : termVL tabs { x with op := o' } = true) (htop : topOKL x.op (shpL tabs x.type) = true)
    (hs : setArgsOK tabs M x = true) (hso : SetOpSoundT x.op o') {ρ : ID → Val}
    (hT : TypedL true M.get? tabs ρ) :
    ∀ n y, Sem.Refines (denL true M.get? tabs ρ n y)
      (denL true (M.put v { x with op := o' }).get? tabs ρ n y)
  | 0, _ => .poison _
  | n + 1, y => by
    have ih := fun a => setOp_den hx ht ht' htop hs hso hT n a
    by_cases hyv : y = v
    · rw [hyv]
      have hnew : (M.put v { x with op := o' }).get? v = some { x with op := o' } := by
        rw [get?_put]; simp
      rw [denT_succ hx ht, denT_succ hnew ht']
      exact Sem.Refines.trans (hso tabs _ _ _ _ htop (setArgs_hasTy hT hs n))
        (retypeL_mono _ (opValL_mono_term ht' _
          (GoFV.Proof.AtomSim.refinesList_map fun a _ => ih a)))
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
            (GoFV.Proof.AtomSim.refinesList_map fun a _ => ih a))
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

/-- The copies `copyStepL` replaces an argument through: a compatible one, or a narrowing `Copy`
keeping the bits the op reads (`truncReachL`). -/
abbrev CopyOKL (tabs : Tables) (M : Defs) (x : Value) (i : Nat) (src : ID) (hi : i < x.args.size) :
    Prop :=
  copyReachL tabs M M.size x.args[i] src = true ∨
    truncReachL tabs M M.size x.op x.auxInt i x.args[i] src = true

theorem copyOKL_closed {hi : i < x.args.size} (hr : CopyOKL tabs M x i src hi) {C : ID → Prop}
    (hC : DefClosed M C) (ha : C x.args[i]) : C src := by
  rcases hr with hr | hr
  · exact copyReachL_closed hC _ _ _ hr ha
  · obtain ⟨k, -, htf⟩ := truncReachL_cases hr
    exact truncFrom_closed hC htf ha

theorem copyPut_closedL (hx : M.get? v = some x) (hi : i < x.args.size)
    (hr : CopyOKL tabs M x i src hi) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (copyPut M v x i src hi) C := by
  intro y hy
  obtain ⟨m, hm, hargs⟩ := hC y hy
  rw [copyPut_get]
  split
  · subst y; rw [hx] at hm; cases hm
    refine ⟨_, rfl, fun a ha => ?_⟩
    rcases Array.mem_or_eq_of_mem_set (w := hi) ha with ha | rfl
    · exact hargs a ha
    · exact copyOKL_closed hr hC (hargs _ (Array.getElem_mem hi))
  · exact ⟨m, hm, hargs⟩

/-- A `copyArg` event refines the denotations of a closed set: through a compatible copy the
argument is what it copies (`copyReachL_den`); through a narrowing `Copy` the op reads the bits
it keeps (`truncFrom_den`, `opValL_narrow_mono`). -/
theorem copyPut_denL (hx : M.get? v = some x) (hi : i < x.args.size)
    (hr : CopyOKL tabs M x i src hi) {C : ID → Prop} (hC : DefClosed M C)
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
        have hsC : C src := copyOKL_closed hr hC (hargs _ (Array.getElem_mem hi))
        rw [denT_succ hx hop, denT_succ hnew hop]
        apply retypeL_mono
        rcases hr with hrc | hrt
        · apply opValL_mono_term hop
          refine refinesList_idx (by simp) fun j h1 h2 => ?_
          simp only [Array.getElem_toList, Array.getElem_set]
          split
          · rename_i hij; subst hij
            exact (copyReachL_den hT _ _ _ hrc n).trans
              (copyPut_denL hx hi (.inl hrc) hC hT n src hsC)
          · exact copyPut_denL hx hi (.inl hrc) hC hT n _ (hargs _ (Array.getElem_mem _))
        · obtain ⟨k, hk, htf⟩ := truncReachL_cases hrt
          obtain ⟨w, hkw, hw64, hd⟩ := truncFrom_den hT htf
          refine opValL_narrow_mono hk _ _ (by simp) fun j h1 h2 => ?_
          simp only [List.getElem_map, Array.getElem_toList, Array.getElem_set]
          split
          · rename_i hij; subst hij
            exact .inr ⟨k, w, hk, hkw, hw64, (hd n).trans
              (retypeL_mono _ (copyPut_denL hx hi (.inr hrt) hC hT n src hsC))⟩
          · exact .inl (copyPut_denL hx hi (.inr hrt) hC hT n _ (hargs _ (Array.getElem_mem _)))
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

/-- The arguments of `a'` (in `M`) are as many as those of `a` (in `D₀`), in `C`, and related to
them (`ArgRel` of `stArg`: refinement, or the address of an arm64 store lowering a `Store`), the
valuation holding the frame addresses of activation 0 (`FrameVals`). -/
def ArgsRefL (tabs : Tables) (D₀ : ID → Option Value) (M : Defs) (C : ID → Prop) (a a' : Value) :
    Prop :=
  a'.args.size = a.args.size ∧
    ∀ i < a.args.size, C a'.args[i]! ∧ ∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ →
      FrameVals tabs 0 D₀ ρ → ArgRel tabs 0 (stArg a a' i) (denL true D₀ tabs ρ n a.args[i]!)
        (denL true M.get? tabs ρ m a'.args[i]!)

/-- The `Store` `a` of `D₀` (three arguments) lowered to the indexed store `a'` in `M` (four, an
`idxStore` op): the arguments of `a'` in `C`, its base and index giving at its scale (`idxAddr`)
the address `a`'s address is (`AddrRef` at offset 0 without aux), its value and memory refining
`a`'s, the valuation holding the frame addresses of activation 0 (`FrameVals`). -/
def IdxRefL (tabs : Tables) (D₀ : ID → Option Value) (M : Defs) (C : ID → Prop) (a a' : Value) :
    Prop :=
  a.args.size = 3 ∧ a'.args.size = 4 ∧ (idxStore a'.op).isSome = true ∧ (∀ i < 4, C a'.args[i]!) ∧
    (∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ → FrameVals tabs 0 D₀ ρ →
      AddrRef tabs 0 none 0 (denL true D₀ tabs ρ n a.args[0]!)
        (idxAddr (idxScale a'.op) (denL true M.get? tabs ρ m a'.args[0]!)
          (denL true M.get? tabs ρ m a'.args[1]!))) ∧
    ∀ i < 2, ∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ → FrameVals tabs 0 D₀ ρ →
      ArgRel tabs 0 none (denL true D₀ tabs ρ n a.args[i + 1]!)
        (denL true M.get? tabs ρ m a'.args[i + 2]!)

/-- How the arguments of an atom `a'` of `M` relate to those of the atom `a` of `D₀` it replays:
argument by argument (`ArgsRefL`), or as an indexed store (`IdxRefL`). -/
abbrev AtomRefL (tabs : Tables) (D₀ : ID → Option Value) (M : Defs) (C : ID → Prop)
    (a a' : Value) : Prop :=
  ArgsRefL tabs D₀ M C a a' ∨ IdxRefL tabs D₀ M C a a'

/-- What holds along the replay from the definitions `D₀` (lowered mode) and a closed set `C₀`:
the current definitions `M` with a set `C` closed under arguments; the atoms of `D₀` with
arguments in `C₀` stay atoms of the same type, with arguments in `C` related to theirs
(`AtomRefL`, the valuation holding `D₀`'s frame addresses of activation 0, `FrameVals`, which a
frame variable's load reads, `ReplayInvL.frameFold`) unless they read none (`argFree`, a lowered
frame address). -/
structure ReplayInvL (tabs : Tables) (D₀ : ID → Option Value) (C₀ : ID → Prop) (M : Defs)
    (C : ID → Prop) : Prop where
  closed : DefClosed M C
  typed : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ
  atoms : ∀ y a, D₀ y = some a → termVL tabs a = false → (∀ b ∈ a.args, C₀ b) →
    ∃ a', M.get? y = some a' ∧ termVL tabs a' = false ∧
      (argFree tabs a' = true ∨ AtomRefL tabs D₀ M C a a')

theorem ReplayInvL.init {tabs : Tables} {M : Defs} {C₀ : ID → Prop} (hC : DefClosed M C₀) :
    ReplayInvL tabs M.get? C₀ M C₀ where
  closed := hC
  typed := fun _ h => h
  atoms := fun y a hy ha hargs => ⟨a, hy, ha, .inr (.inl ⟨rfl, fun i hi =>
    ⟨hargs _ (by rw [getElem!_pos a.args i hi]; exact Array.getElem_mem hi),
      fun n => ⟨n, fun _ _ _ => by rw [stArg_self]; exact Sem.Refines.refl _⟩⟩⟩)⟩

section Inv

variable {tabs : Tables} {D₀ : ID → Option Value} {C₀ : ID → Prop} {M : Defs} {C : ID → Prop}

/-- Compose an argument relation from `D₀` with one step `M → M'`. -/
theorem argRel_compose {M' : Defs} {y y' : ID} {o : Option (Int64 × Option AuxRef)}
    {g : Nat → Nat}
    (h1 : ∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ → FrameVals tabs 0 D₀ ρ →
      ArgRel tabs 0 o (denL true D₀ tabs ρ n y) (denL true M.get? tabs ρ m y'))
    (hty : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ)
    (h2 : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n,
      Sem.Refines (denL true M.get? tabs ρ n y') (denL true M'.get? tabs ρ (g n) y')) :
    ∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ → FrameVals tabs 0 D₀ ρ →
      ArgRel tabs 0 o (denL true D₀ tabs ρ n y) (denL true M'.get? tabs ρ m y') := by
  intro n
  obtain ⟨m, hm⟩ := h1 n
  exact ⟨g m, fun ρ hρ hF => (hm ρ hρ hF).trans_right (h2 ρ (hty ρ hρ) hF m)⟩

/-- `ArgsRefL` along a step `M → M'` refining the denotations of `C ⊆ C'`. -/
theorem ArgsRefL.step {M' : Defs} {C' : ID → Prop} {a a' : Value} {g : Nat → Nat}
    (h : ArgsRefL tabs D₀ M C a a') (hsub : ∀ y, C y → C' y)
    (hty : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ)
    (hstep : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n y, C y →
      Sem.Refines (denL true M.get? tabs ρ n y) (denL true M'.get? tabs ρ (g n) y)) :
    ArgsRefL tabs D₀ M' C' a a' :=
  ⟨h.1, fun i hi => ⟨hsub _ (h.2 i hi).1,
    argRel_compose (h.2 i hi).2 hty fun ρ hρ hF n => hstep ρ hρ hF n _ (h.2 i hi).1⟩⟩

/-- `IdxRefL` along a step `M → M'` refining the denotations of `C ⊆ C'`. -/
theorem IdxRefL.step {M' : Defs} {C' : ID → Prop} {a a' : Value} {g : Nat → Nat}
    (h : IdxRefL tabs D₀ M C a a') (hsub : ∀ y, C y → C' y)
    (hty : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ)
    (hstep : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n y, C y →
      Sem.Refines (denL true M.get? tabs ρ n y) (denL true M'.get? tabs ρ (g n) y)) :
    IdxRefL tabs D₀ M' C' a a' := by
  obtain ⟨h3, h4, hix, hC, hA, hV⟩ := h
  refine ⟨h3, h4, hix, fun i hi => hsub _ (hC i hi), fun n => ?_, fun i hi =>
    argRel_compose (hV i hi) hty fun ρ hρ hF n => hstep ρ hρ hF n _ (hC _ (by omega))⟩
  obtain ⟨m, hm⟩ := hA n
  exact ⟨g m, fun ρ hρ hF => ArgRel.trans_right (o := some (0, none)) (hm ρ hρ hF)
    (idxAddr_mono _ (hstep ρ (hty ρ hρ) hF m _ (hC 0 (by omega)))
      (hstep ρ (hty ρ hρ) hF m _ (hC 1 (by omega))))⟩

/-- `AtomRefL` along a step `M → M'` refining the denotations of `C ⊆ C'`. -/
theorem AtomRefL.step {M' : Defs} {C' : ID → Prop} {a a' : Value} {g : Nat → Nat}
    (h : AtomRefL tabs D₀ M C a a') (hsub : ∀ y, C y → C' y)
    (hty : ∀ ρ, TypedL true D₀ tabs ρ → TypedL true M.get? tabs ρ)
    (hstep : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n y, C y →
      Sem.Refines (denL true M.get? tabs ρ n y) (denL true M'.get? tabs ρ (g n) y)) :
    AtomRefL tabs D₀ M' C' a a' :=
  Or.imp (fun h => h.step hsub hty hstep) (fun h => h.step hsub hty hstep) h

theorem ReplayInvL.rule {r : Rule} {v : ID} {defs : List Value} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hs : ArmRule.Sound1 r) (F : RuleFactsL tabs M r v defs) :
    ReplayInvL tabs D₀ C₀ (putAll M defs) (fun y => C y ∨ (C v ∧ y ∈ defIds defs)) where
  closed := F.closed hI.closed
  typed := fun ρ h => F.typed (hI.typed ρ h)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
    exact ⟨a', F.keepAtom ha' hat, hat, hrest.imp id fun hr =>
      hr.step (fun _ h => .inl h) hI.typed fun ρ hρ _ n z hz => F.step hs hI.closed hρ n z hz⟩

theorem ReplayInvL.setOp {v : ID} {x : Value} {o' : Op} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (ht : termVL tabs x = true)
    (ht' : termVL tabs { x with op := o' } = true) (htop : topOKL x.op (shpL tabs x.type) = true)
    (hs : setArgsOK tabs M x = true) (hso : SetOpSoundT x.op o') :
    ReplayInvL tabs D₀ C₀ (M.put v { x with op := o' }) C where
  closed := put_closed (x' := { x with op := o' }) (fun hv a ha => closed_args hI.closed hx hv a ha)
    hI.closed
  typed := fun ρ h => put_typed (x' := { x with op := o' }) hx rfl (by rw [ht, ht']) (hI.typed ρ h)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
    have hyv : y ≠ v := fun h => by subst h; rw [hx] at ha'; cases ha'; rw [ht] at hat; cases hat
    exact ⟨a', by rw [get?_put]; simp [hyv, ha'], hat, hrest.imp id fun hr =>
      hr.step (g := id) (fun _ h => h) hI.typed fun ρ hρ _ n z _ => setOp_den hx ht ht' htop hs hso hρ n z⟩

/-- Replacing the atom `x` at `v` by an atom `x'` of the same type: a rename, a lowered store
(the same arguments, related as before; `x` no indexed store) or a lowered frame address
(`argFree`). -/
theorem ReplayInvL.atomPut {v : ID} {x x' : Value} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (ht : termVL tabs x = false) (ht' : termVL tabs x' = false)
    (hty : x'.type = x.type) (hcl : C v → ∀ a ∈ x'.args, C a)
    (hargs : argFree tabs x' = true ∨
      (x'.args = x.args ∧ idxStore x.op = none ∧ (argFree tabs x = true → argFree tabs x' = true) ∧
        ∀ (a : Value) (i act : Nat) (s t : Val), ArgRel tabs act (stArg a x i) s t →
          ArgRel tabs act (stArg a x' i) s t)) :
    ReplayInvL tabs D₀ C₀ (M.put v x') C where
  closed := put_closed hcl hI.closed
  typed := fun ρ h => put_typed hx hty (by rw [ht, ht']) (hI.typed ρ h)
  atoms := fun y a hy ha hargs' => by
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs'
    have hstep : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n z, C z →
        Sem.Refines (denL true M.get? tabs ρ n z) (denL true (M.put v x').get? tabs ρ (id n) z) :=
      fun ρ _ _ n z _ => by rw [rename_den hx ht ht']; exact Sem.Refines.refl _
    by_cases hyv : y = v
    · subst hyv
      rw [hx] at ha'; cases ha'
      refine ⟨x', by rw [get?_put]; simp, ht', ?_⟩
      rcases hargs with hf | ⟨heq, hnx, hf, hrel⟩
      · exact .inl hf
      · rcases hrest with hr | hr | hr
        · exact .inl (hf hr)
        · refine .inr (.inl ?_)
          obtain ⟨hsz, hr'⟩ := hr.step (fun _ h => h) hI.typed hstep
          refine ⟨by rw [heq]; exact hsz, fun i hi => ?_⟩
          obtain ⟨hc, hd⟩ := hr' i hi
          refine ⟨by rw [heq]; exact hc, fun n => ?_⟩
          obtain ⟨m, hm⟩ := hd n
          exact ⟨m, fun ρ hρ hF => by rw [heq]; exact hrel a i 0 _ _ (hm ρ hρ hF)⟩
        · exfalso
          have := hr.2.2.1
          rw [hnx] at this; cases this
    · exact ⟨a', by rw [get?_put]; simp [hyv, ha'], hat, hrest.imp id fun hr =>
        hr.step (fun _ h => h) hI.typed hstep⟩

/-- What `stFold` says. -/
theorem stFold_cases {x u : Value} (h : stFold tabs M x u = true) :
    ∃ y, M.get? x.args[0]! = some y ∧ (stSize x.op).isSome = true ∧ u.op = x.op ∧
      u.type = x.type ∧ x.args.size = 3 ∧ offOK x.auxInt = true ∧ offOK u.auxInt = true ∧
      (y.op = .ARM64ADDconst ∨ y.op = .OffPtr) ∧ termVL tabs y = true ∧ y.args.size = 1 ∧
      wordShape (shpL tabs y.type) = true ∧ offOK y.auxInt = true ∧
      u.auxInt.toInt = x.auxInt.toInt + y.auxInt.toInt ∧
      u.args = #[y.args[0]!, x.args[1]!, x.args[2]!] ∧ x.aux = none ∧ u.aux = none := by
  unfold stFold at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  split at h9
  · rename_i y hy
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h9
    obtain ⟨⟨⟨⟨⟨⟨h10, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h9
    exact ⟨y, hy, h1, h2, h3, h6, h7, h8, h10, h11, h12, h13, h14, h15, h16, h4, h5⟩
  · cases h9

/-- `opValL` of the generic `OffPtr [k]` on one argument: `PtrOps.offPtr`. -/
theorem opValL_offPtr (tabs : Tables) (T : Ty) (k : Int64) (ax : Option AuxRef) (z : Val) :
    opValL tabs .OffPtr T k ax [z] = PtrOps.offPtr k [z] := by
  simp only [opValL, show Op.OffPtr.generic = true by decide, ite_true]
  rfl

/-- `OffPtr [k]` is `poison` or `ADDconst [k]` (`Arm64.addP`) at a word shape: both move a pointer
by `ptrRes`, and on an integer word `OffPtr`'s window check (`wordRes`) only adds `poison`. -/
theorem offPtr_cases {T : Ty} (hT : wordShape T = true) (k : Int64) (z : Val) :
    PtrOps.offPtr k [z] = .poison ∨ PtrOps.offPtr k [z] = Arm64.addP T z (BitVec.ofInt 64 k.toInt) := by
  have hres : ∀ a : BitVec 64, Arm64.res T a = .int .w64 a := fun a => by
    rcases wordShape_cases hT with rfl | ⟨e, rfl⟩ <;> rfl
  cases z with
  | ptr p => exact .inr rfl
  | int w x =>
    cases w with
    | w64 =>
      change PtrOps.wordRes x _ = .poison ∨ PtrOps.wordRes x _ = Arm64.addP T (.int .w64 x) _
      unfold PtrOps.wordRes
      split
      · right
        simp only [Arm64.addP, Arm64.reg, BitVec.setWidth_eq, hres]
      · exact .inl rfl
    | _ => exact .inl rfl
  | _ => exact .inl rfl

/-- A word shape is at least 64 bits wide. -/
theorem argWidth_of_wordShape {T : Ty} (h : wordShape T = true) : 64 ≤ argWidth T := by
  cases T with
  | int w => cases w <;> simp_all [wordShape, argWidth, Width.bits]
  | ptr e => simp [argWidth]
  | _ => simp [wordShape] at h

/-- **An address folded into an arm64 store** of a `Store` of `D₀`: the store's address
(argument 0, whose closure in `M` holds `b`) becomes `b`, with the offset and aux `haddr` relates
it at; value and memory stay. -/
theorem ReplayInvL.foldWith {v b : ID} {x u : Value} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (ht : termVL tabs x = false) (ht' : termVL tabs u = false)
    (hst : (stSize x.op).isSome = true) (hop : u.op = x.op) (hty : u.type = x.type)
    (hsz : x.args.size = 3) (hargs : u.args = #[b, x.args[1]!, x.args[2]!])
    (hbC : ∀ {C' : ID → Prop}, DefClosed M C' → C' x.args[0]! → C' b)
    (haddr : C b → ∀ s n, (∃ m, ∀ ρ, TypedL true D₀ tabs ρ → FrameVals tabs 0 D₀ ρ →
        ArgRel tabs 0 (some (x.auxInt, x.aux)) (denL true D₀ tabs ρ n s)
          (denL true M.get? tabs ρ m x.args[0]!)) →
      ∃ m, ∀ ρ, TypedL true D₀ tabs ρ → FrameVals tabs 0 D₀ ρ →
        ArgRel tabs 0 (some (u.auxInt, u.aux)) (denL true D₀ tabs ρ n s)
          (denL true M.get? tabs ρ m b))
    (hsrc : ∀ a, D₀ v = some a → a.op = .Store) :
    ReplayInvL tabs D₀ C₀ (M.put v u) C := by
  have hmem : ∀ i, i < x.args.size → x.args[i]! ∈ x.args := fun i h => by
    rw [getElem!_pos x.args i h]; exact Array.getElem_mem h
  have hcl : C v → ∀ a ∈ u.args, C a := fun hv a ha => by
    have hxa := closed_args hI.closed hx hv
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hbC hI.closed (hxa _ (hmem 0 (by omega)))
    · exact hxa _ (hmem 1 (by omega))
    · exact hxa _ (hmem 2 (by omega))
  have hstep : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n z, C z →
      Sem.Refines (denL true M.get? tabs ρ n z) (denL true (M.put v u).get? tabs ρ (id n) z) :=
    fun ρ _ _ n z _ => by rw [rename_den hx ht ht']; exact Sem.Refines.refl _
  refine
    { closed := put_closed hcl hI.closed
      typed := fun ρ h => put_typed hx hty (by rw [ht, ht']) (hI.typed ρ h)
      atoms := fun z a hz ha hargs' => ?_ }
  obtain ⟨a', ha', hat, hrest⟩ := hI.atoms z a hz ha hargs'
  by_cases hzv : z ≠ v
  · exact ⟨a', by rw [get?_put]; simp [hzv, ha'], hat, hrest.imp id fun hr =>
      hr.step (fun _ h => h) hI.typed hstep⟩
  obtain rfl : z = v := Classical.byContradiction hzv
  rw [hx] at ha'; cases ha'
  refine ⟨u, by rw [get?_put]; simp, ht', .inr (.inl ?_)⟩
  have hS := hsrc a hz
  rcases hrest with hf | ⟨hsza, hr⟩ | hix
  · exact absurd hst (by rw [(argFree_cases hf).1]; decide)
  rotate_left
  · obtain ⟨⟨p, s⟩, hp⟩ := Option.isSome_iff_exists.1 hix.2.2.1
    rw [(idxStore_facts hp).2.1] at hst; cases hst
  have hu3 : u.args.size = 3 := by rw [hargs]; rfl
  refine ⟨by omega, fun i hi => ?_⟩
  rcases i with _ | _ | _ | i
  · -- the address
    obtain ⟨hc0, hd0⟩ := hr 0 hi
    rw [stArg_zero hS hst] at hd0
    have hu0 : u.args[0]! = b := by rw [hargs]; rfl
    rw [hu0]
    have hbM : C b := hbC hI.closed hc0
    refine ⟨hbM, ?_⟩
    rw [stArg_zero hS (by rw [hop]; exact hst)]
    exact argRel_compose (g := id) (fun n => haddr hbM _ n (hd0 n)) hI.typed
      fun ρ hρ hF n => hstep ρ hρ hF n b hbM
  · -- the value
    have e : u.args[1]! = x.args[1]! := by rw [hargs]; rfl
    obtain ⟨hc, hd⟩ := (hr 1 hi)
    refine ⟨by rw [e]; exact hc, ?_⟩
    rw [e, stArg_succ]
    rw [stArg_succ] at hd
    exact argRel_compose (g := id) hd hI.typed fun ρ hρ hF n => hstep ρ hρ hF n _ hc
  · -- the memory
    have e : u.args[2]! = x.args[2]! := by rw [hargs]; rfl
    obtain ⟨hc, hd⟩ := (hr 2 hi)
    refine ⟨by rw [e]; exact hc, ?_⟩
    rw [e, stArg_succ]
    rw [stArg_succ] at hd
    exact argRel_compose (g := id) hd hI.typed fun ρ hρ hF n => hstep ρ hρ hF n _ hc
  · omega

/-- The one argument of a value with one argument. -/
theorem args_one {y : Value} (h : y.args.size = 1) : y.args = #[y.args[0]!] := by
  rcases hy' : y.args with ⟨l⟩
  rw [hy'] at h
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 (by simpa using h)
  rfl

/-- **An offset folded into an arm64 store** of a `Store` of `D₀` (`stFold`): the store's address
(argument 0, `ADDconst [k2] b` in `M`) becomes `b`, its offset `k1 + k2`, related by `AddrRef`
at the new offset (`addrRef_fold`); value and memory stay. -/
theorem ReplayInvL.fold {v : ID} {x u : Value} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (ht : termVL tabs x = false) (ht' : termVL tabs u = false)
    (hfold : stFold tabs M x u = true) (hsrc : ∀ a, D₀ v = some a → a.op = .Store) :
    ReplayInvL tabs D₀ C₀ (M.put v u) C := by
  obtain ⟨y, hy, hst, hop, hty, hsz, hk1, -, hyop, hyt, hysz, hyw, hk2, hk, hargs, hxa, hua⟩ :=
    stFold_cases hfold
  have hb := args_one hysz
  refine hI.foldWith hx ht ht' hst hop hty hsz hargs
    (fun hC h0 => closed_args hC hy h0 _ (by rw [hb]; simp)) (fun hbM s n ⟨m, hm⟩ => ?_) hsrc
  rw [hxa] at hm
  rw [hua]
  obtain ⟨w, hw, -⟩ := hI.closed _ hbM
  rcases m with _ | m
  · refine ⟨0, fun ρ hρ hF p hp => ?_⟩
    have := hm ρ hρ hF p hp
    simp [denL, addrAt, Arm64.addr, Arm64.reg] at this
  · refine ⟨m, fun ρ hρ hF => ?_⟩
    have h1 := hm ρ hρ hF
    rw [denT_succ hy hyt, hb, show (#[y.args[0]!] : Array ID).toList = [y.args[0]!] from rfl]
      at h1
    rcases hyop with hyop | hyop
    · rw [hyop] at h1
      simp only [List.map_cons, List.map_nil, opValL_addConst] at h1
      exact addrRef_fold (den_hasTyL (hI.typed ρ hρ) m hw) (argWidth_of_wordShape hyw)
        hk1 hk2 hk h1
    · rw [hyop] at h1
      simp only [List.map_cons, List.map_nil, opValL_offPtr] at h1
      rcases offPtr_cases hyw y.auxInt (denL true M.get? tabs ρ m y.args[0]!) with h0 | h0
      · rw [h0, retypeL_poison] at h1
        intro p hp
        have := h1 p hp
        simp [addrAt, Arm64.addr, Arm64.reg] at this
      · rw [h0] at h1
        exact addrRef_fold (den_hasTyL (hI.typed ρ hρ) m hw) (argWidth_of_wordShape hyw)
          hk1 hk2 hk h1

/-- What `stFoldAddr` says. -/
theorem stFoldAddr_cases {f : Func} {x u : Value} (h : stFoldAddr tabs f M x u = true) :
    (stSize x.op).isSome = true ∧ u.op = x.op ∧ u.type = x.type ∧ x.aux = none ∧
      x.args.size = 3 ∧ offOK x.auxInt = true ∧ offOK u.auxInt = true ∧
      ((∃ m, M.get? x.args[0]! = some m ∧ m.op = .ARM64MOVDaddr ∧ m.args.size = 1 ∧
          m.aux.isSome = true ∧ u.aux = m.aux ∧ u.auxInt.toInt = x.auxInt.toInt + m.auxInt.toInt ∧
          u.args = #[m.args[0]!, x.args[1]!, x.args[2]!] ∧ termVL tabs m = true ∧
          wordShape (shpL tabs m.type) = true) ∨
        (∃ a m, frameAddr tabs M x.args[0]! = some (a, m) ∧ m.args.size = 1 ∧
          m.aux.isSome = true ∧ u.aux = m.aux ∧ u.auxInt = x.auxInt ∧
          u.args = #[m.args[0]!, x.args[1]!, x.args[2]!] ∧
          ∃ l, f.value? a = some l ∧ l.op = .LocalAddr ∧ l.aux = m.aux)) := by
  unfold stFoldAddr at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩
  rcases h8 with h8 | h8
  · left
    split at h8
    · rename_i m hm
      simp only [Bool.and_eq_true, beq_iff_eq] at h8
      obtain ⟨⟨⟨⟨⟨⟨⟨h10, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩ := h8
      exact ⟨m, hm, h10, h11, h12, h13, h14, h15, h16, h17⟩
    · cases h8
  · right
    split at h8
    · rename_i a m hm
      simp only [Bool.and_eq_true, beq_iff_eq] at h8
      obtain ⟨⟨⟨⟨⟨h10, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := h8
      refine ⟨a, m, hm, h10, h11, h12, h13, h14, ?_⟩
      cases hl : f.value? a with
      | none => rw [hl] at h15; cases h15
      | some l =>
        rw [hl] at h15
        simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h15
        exact ⟨l, rfl, h15.1, h15.2⟩
    · cases h8

/-- No store address is the pointer word of a value moved from `poison`. -/
theorem addrRef_poison {act act' : Nat} {ax : Option AuxRef} {k k' : Int64} {x z : Val}
    (h : AddrRef tabs act none k x .poison) : AddrRef tabs act' ax k' x z := by
  intro p hp
  have := h p hp
  simp [addrAt, Arm64.addr, Arm64.reg] at this

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
  typed := fun ρ h => put_fresh_typed hk hs (hI.typed ρ h)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
    have hyk : y ≠ s.id := fun h => by subst h; rw [hk] at ha'; cases ha'
    exact ⟨a', by rw [get?_put]; simp [hyk, ha'], hat, hrest.imp id fun hr =>
      hr.step (g := id) (fun _ h => .inl h) hI.typed fun ρ _ _ n z hz => by
        rw [denL_put_fresh hk hI.closed _ z hz]; exact Sem.Refines.refl _⟩

theorem ReplayInvL.copy {v : ID} {x : Value} {i : Nat} {src : ID} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (hi : i < x.args.size)
    (hr : CopyOKL tabs M x i src hi) :
    ReplayInvL tabs D₀ C₀ (copyPut M v x i src hi) C where
  closed := copyPut_closedL hx hi hr hI.closed
  typed := fun ρ h => copyPut_typedL hx hi (hI.typed ρ h)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
    have hstep : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n z, C z →
        Sem.Refines (denL true M.get? tabs ρ n z)
          (denL true (copyPut M v x i src hi).get? tabs ρ (id n) z) :=
      fun ρ hρ _ n z hz => copyPut_denL hx hi hr hI.closed hρ n z hz
    by_cases hyv : y = v
    · rw [hyv] at ha'; rw [hx] at ha'; cases ha'
      -- an atom: its argument is replaced through a compatible copy only (a narrowing one is
      -- read by a term, `termVL_narrow`)
      have hrc : copyReachL tabs M M.size x.args[i] src = true := by
        rcases hr with hr | hr
        · exact hr
        · obtain ⟨k, hk, -⟩ := truncReachL_cases hr
          rw [termVL_narrow hk] at hat; cases hat
      have hnew : ∀ j < x.args.size, C x.args[j]! → C (x.args.set i src hi)[j]! ∧
          ∀ ρ, TypedL true D₀ tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ m,
            Sem.Refines (denL true M.get? tabs ρ m x.args[j]!)
              (denL true (copyPut M v x i src hi).get? tabs ρ m (x.args.set i src hi)[j]!) := by
        intro j hj hc
        simp only [set_getElem! hi hj]
        split
        · rename_i hij; subst hij
          rw [getElem!_pos x.args i hi] at hc ⊢
          have hsrc := copyReachL_closed hI.closed _ _ _ hrc hc
          exact ⟨hsrc, fun ρ hρ hF m => (copyReachL_den (hI.typed ρ hρ) _ _ _ hrc m).trans
            (hstep ρ (hI.typed ρ hρ) hF m src hsrc)⟩
        · exact ⟨hc, fun ρ hρ hF m => hstep ρ (hI.typed ρ hρ) hF m _ hc⟩
      refine ⟨{ x with args := x.args.set i src hi }, by rw [copyPut_get]; simp [hyv], hat, ?_⟩
      rcases hrest with hf | ⟨hsz, hrest⟩ | ⟨h3, h4, hix, hC, hA, hV⟩
      · exact .inl hf
      · refine .inr (.inl ⟨by simpa using hsz, fun j hj => ?_⟩)
        obtain ⟨hc, hd⟩ := hrest j hj
        obtain ⟨hc', hd'⟩ := hnew j (hsz ▸ hj) hc
        refine ⟨hc', fun n => ?_⟩
        obtain ⟨m, hm⟩ := hd n
        exact ⟨m, fun ρ hρ hF => (hm ρ hρ hF).trans_right (hd' ρ hρ hF m)⟩
      · have h4' : (x.args.set i src hi).size = 4 := by simpa using h4
        refine .inr (.inr ⟨h3, h4', hix, fun j hj => (hnew j (by omega) (hC j hj)).1,
          fun n => ?_, fun j hj n => ?_⟩)
        · obtain ⟨m, hm⟩ := hA n
          exact ⟨m, fun ρ hρ hF => ArgRel.trans_right (o := some (0, none)) (hm ρ hρ hF)
            (idxAddr_mono _ ((hnew 0 (by omega) (hC 0 (by omega))).2 ρ hρ hF m)
              ((hnew 1 (by omega) (hC 1 (by omega))).2 ρ hρ hF m))⟩
        · obtain ⟨m, hm⟩ := hV j hj n
          exact ⟨m, fun ρ hρ hF => (hm ρ hρ hF).trans_right
            ((hnew (j + 2) (by omega) (hC _ (by omega))).2 ρ hρ hF m)⟩
    · exact ⟨a', by rw [copyPut_get]; simp [hyv, ha'], hat, hrest.imp id fun hr =>
        hr.step (fun _ h => h) hI.typed hstep⟩

/-! ### A frame variable's address folded into a load or an `ADDconst` (`frameFold`) -/

/-- What `frameFold` says. -/
theorem frameFold_cases {f : Func} {v : ID} {defs : List Value} {u : Value}
    (h : frameFold tabs f M v defs = some u) :
    ∃ x a m, M.get? v = some x ∧ frameAddr tabs M x.args[0]! = some (a, m) ∧ u.type = x.type ∧
      u.auxInt = x.auxInt ∧ offOK x.auxInt = true ∧ termVL tabs x = true ∧
      termVL tabs u = true ∧ m.args.size = 1 ∧
      u.aux = m.aux ∧ (∃ l, f.value? a = some l ∧ l.op = .LocalAddr ∧ l.aux = m.aux) ∧
      (((ldOp? x.op).isSome = true ∧ u.op = x.op ∧ x.aux = none ∧ x.args.size = 2 ∧
          u.args = #[m.args[0]!, x.args[1]!]) ∨
        (x.op = .ARM64ADDconst ∧ u.op = .ARM64MOVDaddr ∧ x.args.size = 1 ∧
          wordShape (shpL tabs x.type) = true ∧ u.args = #[m.args[0]!])) := by
  unfold frameFold at h
  split at h
  · rename_i x _ u' hx
    split at h
    · cases h
    rename_i p hp
    have e : x.args[0]! = p := by simp [getElem!_def, hp]
    subst e
    split at h
    · rename_i a m hm
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h10⟩, h11⟩, h13⟩, h14⟩ := hc
        refine ⟨x, a, m, hx, hm, h3, h4, h5, h6, h7, h10, h11, ?_, ?_⟩
        · cases hl : f.value? a with
          | none => rw [hl] at h13; cases h13
          | some l =>
            rw [hl] at h13
            simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h13
            exact ⟨l, rfl, h13.1, h13.2⟩
        · rcases h14 with ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ | ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩
          · exact .inl ⟨a1, a2, a3, a4, a5⟩
          · exact .inr ⟨a1, a2, a3, a4, a5⟩
      · cases h
    · cases h
  · cases h

/-- The two arguments of a value with two arguments. -/
theorem args_two {y : Value} (h : y.args.size = 2) : y.args = #[y.args[0]!, y.args[1]!] := by
  rcases hy' : y.args with ⟨l⟩
  rw [hy'] at h
  match l, h with
  | [a, b], _ => rfl

/-- The integer loads are arm64 ops other than `MOVDaddr`. -/
theorem ldOp_arm {o : Op} {p : Nat × Bool} (h : ldOp? o = some p) :
    o.generic = false ∧ (o == .ARM64MOVDaddr) = false := by
  rcases ldOp?_mem h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- An address at a frame variable's aux: the variable's block in activation 0. -/
theorem symPtr_name {n : AuxRef} (hn : GoFV.Opt.LowerTerm.auxIsName tabs (some n) = true)
    (k : Int64) (y : Val) :
    symPtr tabs k (some n) y = some ⟨frameBlk tabs 0 n, BitVec.ofInt 64 k.toInt⟩ := by
  unfold GoFV.Opt.LowerTerm.auxIsName at hn
  simp only [Option.bind_some] at hn
  split at hn
  · rename_i hd
    simp only [symPtr, hd]
  · cases hn

/-- **The folded load**: an integer load at offset `k` (no aux) of a frame variable `n`'s address
register (`poison` or the address word in activation 0, `FrameVals`) is refined by the load of
`n` at `k` on any base, on a refined memory. -/
theorem ldVal_frameFold {n : AuxRef} (hn : GoFV.Opt.LowerTerm.auxIsName tabs (some n) = true)
    {k : Int64} (hk : offOK k = true) {w X X' : Val}
    (hw : w = .poison ∨ w = (framePtr tabs 0 n).word) (hX : Sem.Refines X X') (z : Val)
    (sz : Nat) (s : Bool) (T : Ty) :
    Sem.Refines (ldVal tabs sz s T k none [w, X]) (ldVal tabs sz s T k (some n) [z, X']) := by
  have hp : symPtr tabs k none w = none ∨ symPtr tabs k none w = symPtr tabs k (some n) z := by
    rcases hw with rfl | rfl
    · exact .inl rfl
    · right
      obtain ⟨b, -⟩ := offOK_toNat hk
      rw [symPtr_name hn]
      exact addr_framePtr tabs 0 n (by omega)
  rcases hp with hp | hp
  · have : ldVal tabs sz s T k none [w, X] = .poison := by
      cases X <;> simp only [ldVal, hp, Option.elim]
    rw [this]; exact .poison _
  · have : ldVal tabs sz s T k none [w, X] = ldVal tabs sz s T k (some n) [z, X] := by
      cases X <;> simp only [ldVal, hp]
    rw [this]
    exact ldVal_mono tabs sz s T k (some n) (.cons (Sem.Refines.refl z) (.cons hX .nil))

/-- **The folded offset**: `ADDconst [k]` (at a word shape) of a frame variable `n`'s address
register (`poison` or the address word in activation 0, `FrameVals`) is refined by `MOVDaddr [k]
{n}` on any base: the address word moved by `k` inside the frame block's window
(`Ptr.word_add`). -/
theorem addConst_frameFold {n : AuxRef} (hn : GoFV.Opt.LowerTerm.auxIsName tabs (some n) = true)
    {k : Int64} (hk : offOK k = true) {T : Ty} (hT : wordShape T = true) {w : Val}
    (hw : w = .poison ∨ w = (framePtr tabs 0 n).word) (z : Val) :
    Sem.Refines ((Arm64.addP T w (BitVec.ofInt 64 k.toInt)).retypeL T)
      ((movAddr tabs k (some n) [z]).retypeL T) := by
  rcases hw with rfl | rfl
  · simp only [Arm64.addP, Arm64.reg, retypeL_poison]; exact .poison _
  obtain ⟨b, -⟩ := offOK_toNat hk
  have hq : (⟨frameBlk tabs 0 n, BitVec.ofInt 64 k.toInt⟩ : Ptr) =
      (framePtr tabs 0 n).add (BitVec.ofInt 64 k.toInt) := by simp [framePtr, Ptr.add]
  have hw : ((framePtr tabs 0 n).add (BitVec.ofInt 64 k.toInt)).inWindow = true := by
    rw [← hq]; exact frame_inWindow tabs 0 n (by omega)
  simp only [movAddr, symPtr_name hn, Option.elim, hq, PtrOps.ptrRes, hw, ite_true]
  rcases Ptr.word_cases (framePtr tabs 0 n) with ⟨-, h⟩ | ⟨hc, a, ha, h⟩ | ⟨h', -⟩
  rotate_right
  · rw [show (framePtr tabs 0 n).inWindow = true from Ptr.inWindow_zero _] at h'; cases h'
  · rw [h]
    simp only [Arm64.addP, PtrOps.ptrRes, hw, ite_true]
    exact Sem.Refines.refl _
  · rw [h, Ptr.word_add hc ha hw]
    have hres : Arm64.res T (a + BitVec.ofInt 64 k.toInt) =
        .int .w64 (a + BitVec.ofInt 64 k.toInt) := by
      rcases wordShape_cases hT with rfl | ⟨e, rfl⟩ <;> rfl
    simp only [Arm64.addP, Arm64.reg, BitVec.setWidth_eq, hres]
    exact Sem.Refines.refl _

/-- A value a pointer word refines is `poison` or that word. -/
theorem refines_word {x : Val} {q : Ptr} (h : Sem.Refines x q.word) :
    x = .poison ∨ x = q.word := by
  rcases Ptr.word_cases q with ⟨-, hq⟩ | ⟨-, a, -, hq⟩ | ⟨-, hq⟩ <;> rw [hq] at h ⊢ <;> cases h <;>
    simp

/-- `ADDconst [0]` (at a word shape) of a frame variable `n`'s address register (`poison` or the
address word in activation 0) is `poison` or that word. -/
theorem addZero_frame {n : AuxRef} (hn : GoFV.Opt.LowerTerm.auxIsName tabs (some n) = true)
    {T : Ty} (hT : wordShape T = true) {w : Val}
    (hw : w = .poison ∨ w = (framePtr tabs 0 n).word) :
    (Arm64.addP T w (BitVec.ofInt 64 (0 : Int64).toInt)).retypeL T = .poison ∨
      (Arm64.addP T w (BitVec.ofInt 64 (0 : Int64).toInt)).retypeL T =
        (framePtr tabs 0 n).word := by
  have h1 := addConst_frameFold hn (k := 0) (by decide) hT hw .poison
  have hw0 : (framePtr tabs 0 n).inWindow = true := frame_inWindow tabs 0 n (k := 0) (by decide)
  have e : (⟨frameBlk tabs 0 n, BitVec.ofInt 64 (0 : Int64).toInt⟩ : Ptr) = framePtr tabs 0 n := by
    simp [framePtr]
  have h2 : (movAddr tabs 0 (some n) [.poison]).retypeL T = (framePtr tabs 0 n).word := by
    simp only [movAddr, symPtr_name hn, Option.elim, e, PtrOps.ptrRes, hw0, ite_true]
    exact word_retypeL (wordShape_cases hT) _
  rw [h2] at h1
  exact refines_word h1

/-- What `frameAddr` says: the atom `m` (a `MOVDaddr`) at `a`, which is `p` or the argument of
`ADDconst [0]` at `p` (a term at a word shape). -/
theorem frameAddr_cases {p a : ID} {m : Value} (h : frameAddr tabs M p = some (a, m)) :
    M.get? a = some m ∧ m.op = .ARM64MOVDaddr ∧ termVL tabs m = false ∧
      (a = p ∨ ∃ y, M.get? p = some y ∧ y.op = .ARM64ADDconst ∧ y.auxInt = 0 ∧
        termVL tabs y = true ∧ wordShape (shpL tabs y.type) = true ∧ y.args = #[a]) := by
  unfold frameAddr at h
  split at h
  · rename_i y hy
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      exact ⟨hy, hc.1, hc.2, .inl rfl⟩
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
        split at h
        · rename_i a' ha'
          split at h
          · rename_i m' hm'
            split at h
            · rename_i hc2
              cases h
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc2
              have e : y.args[0]! = a := by simp [getElem!_def, ha']
              exact ⟨hm', hc2.1, hc2.2, .inr ⟨y, hy, h1, h2, h3, h4, by rw [args_one h5, e]⟩⟩
            · cases h
          · cases h
        · cases h
      · cases h
  · cases h

/-- A closed set holding `p` holds the frame address atom `frameAddr` finds through it. -/
theorem frameAddr_closed {p a : ID} {m : Value} {C' : ID → Prop}
    (h : frameAddr tabs M p = some (a, m)) (hC : DefClosed M C') (hp : C' p) : C' a := by
  obtain ⟨-, -, -, hcase⟩ := frameAddr_cases h
  rcases hcase with rfl | ⟨y, hy, -, -, -, -, hya⟩
  · exact hp
  · exact closed_args hC hy hp a (by rw [hya]; simp)

/-- The address `frameAddr` finds through `p`, of a `LocalAddr {n}` of `f`, denotes `poison` or
`n`'s address word, where the valuation holds the frame addresses of activation 0 (`FrameVals`,
`addZero_frame`). -/
theorem frameAddr_den {f : Func} (hD : ∀ y, D₀ y = f.value? y) {p a : ID} {m l : Value}
    {n : AuxRef} (h : frameAddr tabs M p = some (a, m)) (hl : f.value? a = some l)
    (hlop : l.op = .LocalAddr) (hlax : l.aux = some n) (hmax : m.aux = some n) {ρ : ID → Val}
    (hF : FrameVals tabs 0 D₀ ρ) :
    ∀ k, denL true M.get? tabs ρ k p = .poison ∨
      denL true M.get? tabs ρ k p = (framePtr tabs 0 n).word := by
  obtain ⟨hm, hmop, hmt, hcase⟩ := frameAddr_cases h
  have ha0 : ¬ IsTermL tabs M.get? a := fun ⟨w, hw, hw'⟩ => by
    rw [hm] at hw; cases hw; rw [hmt] at hw'; cases hw'
  have hρ : ρ a = .poison ∨ ρ a = (framePtr tabs 0 n).word := by
    rcases hF a l n (by rw [hD]; exact hl) hlop hlax with h | ⟨h, -⟩
    · exact .inl h
    · exact .inr h
  have hA : ∀ k, denL true M.get? tabs ρ k a = .poison ∨
      denL true M.get? tabs ρ k a = (framePtr tabs 0 n).word := fun k => by
    rcases k with _ | k
    · exact .inl rfl
    · rw [denL_succ_atom ha0]; exact hρ
  rcases hcase with rfl | ⟨y, hy, hyop, hy0, hyt, hyw, hya⟩
  · exact hA
  intro k
  rcases k with _ | k
  · exact .inl rfl
  have hname : GoFV.Opt.LowerTerm.auxIsName tabs (some n) = true := by
    rw [← hmax]; exact (movDaddr_atom hmop hmt).1
  rw [denT_succ hy hyt, hyop, hy0, hya, show (#[a] : Array ID).toList = [a] from rfl]
  simp only [List.map_cons, List.map_nil, opValL_addConst]
  exact addZero_frame hname hyw (hA k)

/-- **A global symbol's or frame variable's address folded into an arm64 store** of a `Store` of
`D₀` (`stFoldAddr`): the store's address (argument 0, `MOVDaddr [k2] {n} b` in `M`, or for a
frame variable `ADDconst [0]` of it, `frameAddr`) becomes `b`, its offset `k1 + k2` and aux `n`,
related by `AddrRef` at the new offset and aux: the global's address (`addrRef_foldSym`), or the
frame variable's, which the source's `LocalAddr {n}` holds (`FrameVals`, `frameAddr_den`,
`addrRef_foldFrame`); value and memory stay. -/
theorem ReplayInvL.foldAddr {f : Func} (hD : ∀ y, D₀ y = f.value? y) {v : ID} {x u : Value}
    (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (ht : termVL tabs x = false) (ht' : termVL tabs u = false)
    (hfold : stFoldAddr tabs f M x u = true) (hsrc : ∀ a, D₀ v = some a → a.op = .Store) :
    ReplayInvL tabs D₀ C₀ (M.put v u) C := by
  obtain ⟨hst, hop, hty, hxa, hsz, hk1, hk0, hcase⟩ := stFoldAddr_cases hfold
  rcases hcase with ⟨m, hm, hmop, hmsz, hmax, hua, hk, hargs, hmt, hmw⟩ |
    ⟨a, m, hfa, hmsz, hmax, hua, hk, hargs, l, hl, hlop, hlax⟩
  · -- a global symbol's or frame variable's address term
    obtain ⟨nn, hnn⟩ : ∃ nn, m.aux = some nn := Option.isSome_iff_exists.1 hmax
    have hb := args_one hmsz
    refine hI.foldWith hx ht ht' hst hop hty hsz hargs
      (fun hC h0 => closed_args hC hm h0 _ (by rw [hb]; simp))
      (fun _ s n ⟨j, hj⟩ => ⟨j, fun ρ hρ hF => ?_⟩) hsrc
    have h1 := hj ρ hρ hF
    rw [hxa] at h1
    rw [hua, hnn]
    rcases j with _ | j
    · exact addrRef_poison h1
    · rw [denT_succ hm hmt, hmop, hb, hnn,
        show (#[m.args[0]!] : Array ID).toList = [m.args[0]!] from rfl] at h1
      simp only [List.map_cons, List.map_nil, opValL_movDaddr] at h1
      exact addrRef_foldSym hmw hk1 hk0 hk h1 _
  · -- a frame variable
    obtain ⟨hmA, hmop, hmt, -⟩ := frameAddr_cases hfa
    obtain ⟨nn, hnn⟩ : ∃ nn, m.aux = some nn := Option.isSome_iff_exists.1 hmax
    have hb := args_one hmsz
    refine hI.foldWith hx ht ht' hst hop hty hsz hargs
      (fun hC h0 => closed_args hC hmA (frameAddr_closed hfa hC h0) _ (by rw [hb]; simp))
      (fun _ s n ⟨j, hj⟩ => ⟨j, fun ρ hρ hF => ?_⟩) hsrc
    have h1 := hj ρ hρ hF
    rw [hxa] at h1
    rw [hua, hnn]
    have hname : GoFV.Opt.LowerTerm.auxIsName tabs (some nn) = true := by
      rw [← hnn]; exact (movDaddr_atom hmop hmt).1
    exact addrRef_foldFrame hname hk1 (by rw [hk]) (frameAddr_den hD hfa hl hlop
      (by rw [hlax, hnn]) hnn hF j) h1 _

/-- An integer load is a term. -/
theorem termVL_ld {x : Value} {p : Nat × Bool} (hl : ldOp? x.op = some p) :
    termVL tabs x = true := by
  obtain ⟨hg, hm⟩ := ldOp_arm hl
  simp only [termVL, hg, hm, hl, Bool.false_eq_true, ite_false, Option.isSome_some, ite_true]

/-- **Replacing the term `x` at `v` by the term `u`** refines every denotation, where the top
node does (`htop`) for argument values refining each other that have a property `P` every
denotation of `M` has (`hP`: e.g. an address argument's value is `poison` or a frame variable's
address word). -/
theorem termPut_den {v : ID} {x u : Value} {P : (ID → Val) → Prop} (hx : M.get? v = some x)
    (hxt : termVL tabs x = true) (hut : termVL tabs u = true) {ρ : ID → Val}
    (hP : ∀ k, P (denL true M.get? tabs ρ k))
    (htop : ∀ F G : ID → Val, (∀ a, Sem.Refines (F a) (G a)) → P F →
      Sem.Refines
        ((opValL tabs x.op (shpL tabs x.type) x.auxInt x.aux (x.args.toList.map F)).retypeL
          (shpL tabs x.type))
        ((opValL tabs u.op (shpL tabs u.type) u.auxInt u.aux (u.args.toList.map G)).retypeL
          (shpL tabs u.type))) :
    ∀ k y, Sem.Refines (denL true M.get? tabs ρ k y) (denL true (M.put v u).get? tabs ρ k y)
  | 0, _ => .poison _
  | k + 1, y => by
    have ih := fun a => termPut_den hx hxt hut hP htop k a
    by_cases hyv : y = v
    · subst hyv
      have hnew : (M.put y u).get? y = some u := by rw [get?_put]; simp
      rw [denT_succ hx hxt, denT_succ hnew hut]
      exact htop _ _ ih (hP k)
    · have h' : (M.put v u).get? y = M.get? y := by rw [get?_put]; simp [hyv]
      cases hmy : M.get? y with
      | none =>
        have h1 : ¬ IsTermL tabs M.get? y := fun ⟨w, hw, _⟩ => by rw [hmy] at hw; cases hw
        have h2 : ¬ IsTermL tabs (M.put v u).get? y := fun ⟨w, hw, _⟩ => by
          rw [h', hmy] at hw; cases hw
        rw [denL_succ_atom h1, denL_succ_atom h2]; exact Sem.Refines.refl _
      | some w =>
        have hw' : (M.put v u).get? y = some w := by rw [h', hmy]
        by_cases htw : termVL tabs w = true
        · rw [denT_succ hmy htw, denT_succ hw' htw]
          exact retypeL_mono _ (opValL_mono_term htw _
            (GoFV.Proof.AtomSim.refinesList_map fun a _ => ih a))
        · have h1 : ¬ IsTermL tabs M.get? y := fun ⟨w', hw, hw''⟩ => by
            rw [hmy] at hw; cases hw; exact htw hw''
          have h2 : ¬ IsTermL tabs (M.put v u).get? y := fun ⟨w', hw, hw''⟩ => by
            rw [hw'] at hw; cases hw; exact htw hw''
          rw [denL_succ_atom h1, denL_succ_atom h2]; exact Sem.Refines.refl _

/-- **A frame variable's address folded into an integer load or an `ADDconst`** (`frameFold`):
the term `x` at `v`, whose address argument is a lowered frame address (`frameAddr`: the atom
`MOVDaddr {n}` of a `LocalAddr {n}` of `f`, or `ADDconst [0]` of it), becomes the load of `n` or
`MOVDaddr {n}` at the same offset. Its denotation refines the old one where the valuation holds
the frame addresses of activation 0 (`FrameVals`; `frameAddr_den`, `ldVal_frameFold`,
`addConst_frameFold`, `termPut_den`): the step `M → M.put v u` refines every denotation, and `ReplayInvL`
carries over. -/
theorem ReplayInvL.frameFold {f : Func} (hD : ∀ y, D₀ y = f.value? y) {v : ID}
    {defs : List Value} {u : Value} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hld : frameFold tabs f M v defs = some u) :
    ReplayInvL tabs D₀ C₀ (M.put v u) C ∧
      ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n y, C y →
        Sem.Refines (denL true M.get? tabs ρ n y) (denL true (M.put v u).get? tabs ρ (id n) y) := by
  obtain ⟨x, a, m, hx, hfa, hty, hai, hk, hxt, hut, hmsz, hua, ⟨l, hlf, hlop, hlax⟩,
    hcase⟩ := frameFold_cases hld
  obtain ⟨hm, hmop, hmt, -⟩ := frameAddr_cases hfa
  obtain ⟨hname, -⟩ := movDaddr_atom hmop hmt
  obtain ⟨nn, hnn⟩ : ∃ nn, m.aux = some nn := by
    cases h : m.aux with
    | none => rw [h] at hname; cases hname
    | some nn => exact ⟨nn, rfl⟩
  rw [hnn] at hname
  have htop : ∀ F G : ID → Val, (∀ a, Sem.Refines (F a) (G a)) →
      (F x.args[0]! = .poison ∨ F x.args[0]! = (framePtr tabs 0 nn).word) →
      Sem.Refines
        ((opValL tabs x.op (shpL tabs x.type) x.auxInt x.aux (x.args.toList.map F)).retypeL
          (shpL tabs x.type))
        ((opValL tabs u.op (shpL tabs u.type) u.auxInt u.aux (u.args.toList.map G)).retypeL
          (shpL tabs u.type)) := by
    intro F G hFG hF
    rw [hty, hai, hua, hnn]
    rcases hcase with ⟨hl0, hop, hxa, hsz, huargs⟩ | ⟨hop, huop, hsz, hw, huargs⟩
    · obtain ⟨⟨sz, sg⟩, hl⟩ := Option.isSome_iff_exists.1 hl0
      obtain ⟨hg, hmd⟩ := ldOp_arm hl
      have hxl : x.args.toList = [x.args[0]!, x.args[1]!] := congrArg Array.toList (args_two hsz)
      have hul : u.args.toList = [m.args[0]!, x.args[1]!] := by rw [huargs]
      rw [hop, hxa, hxl, hul]
      simp only [List.map_cons, List.map_nil]
      rw [opValL_ld hg hmd hl, opValL_ld hg hmd hl]
      exact retypeL_mono _ (ldVal_frameFold hname hk hF (hFG _) _ _ _ _)
    · have hxl : x.args.toList = [x.args[0]!] := congrArg Array.toList (args_one hsz)
      have hul : u.args.toList = [m.args[0]!] := by rw [huargs]
      rw [hop, huop, hxl, hul]
      simp only [List.map_cons, List.map_nil, opValL_addConst, opValL_movDaddr]
      exact addConst_frameFold hname hk hw hF _
  have hstep : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n y, C y →
      Sem.Refines (denL true M.get? tabs ρ n y) (denL true (M.put v u).get? tabs ρ (id n) y) :=
    fun ρ _ hF n y _ => termPut_den hx hxt hut
      (P := fun F => F x.args[0]! = .poison ∨ F x.args[0]! = (framePtr tabs 0 nn).word)
      (frameAddr_den hD hfa hlf hlop (by rw [hlax, hnn]) hnn hF) htop n y
  have hcl : C v → ∀ z ∈ u.args, C z := fun hv z hz => by
    have hxa' := closed_args hI.closed hx hv
    have hsz0 : 0 < x.args.size := by
      rcases hcase with ⟨-, -, -, h, -⟩ | ⟨-, -, h, -, -⟩ <;> omega
    have h0 : C x.args[0]! :=
      hxa' _ (by rw [getElem!_pos x.args 0 hsz0]; exact Array.getElem_mem _)
    have hm0 : C m.args[0]! := closed_args hI.closed hm (frameAddr_closed hfa hI.closed h0) _
      (by rw [getElem!_pos m.args 0 (by omega)]; exact Array.getElem_mem _)
    rcases hcase with ⟨-, -, -, hsz, huargs⟩ | ⟨-, -, -, -, huargs⟩
    · rw [huargs] at hz
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hm0
      · exact hxa' _ (by rw [getElem!_pos x.args 1 (by omega)]; exact Array.getElem_mem _)
    · rw [huargs] at hz
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hz
      rw [hz]; exact hm0
  refine ⟨{ closed := put_closed hcl hI.closed
            typed := fun ρ h => put_typed hx hty (by rw [hxt, hut]) (hI.typed ρ h)
            atoms := fun y a hy ha hargs => ?_ }, hstep⟩
  obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
  have hyv : y ≠ v := fun h => by subst h; rw [hx] at ha'; cases ha'; rw [hxt] at hat; cases hat
  exact ⟨a', by rw [get?_put]; simp [hyv, ha'], hat, hrest.imp id fun hr =>
    hr.step (g := id) (fun _ h => h) hI.typed hstep⟩

/-! ### A load folding the offset of an `OffPtr` (`ldOffFold`) -/

/-- What `ldOffFold` says. -/
theorem ldOffFold_cases {v : ID} {defs : List Value} {u : Value}
    (h : ldOffFold tabs M v defs = some u) :
    ∃ x y bv, M.get? v = some x ∧ M.get? x.args[0]! = some y ∧ u.op = x.op ∧ u.type = x.type ∧
      (ldOp? x.op).isSome = true ∧ x.aux = none ∧ u.aux = none ∧ x.args.size = 2 ∧
      offOK x.auxInt = true ∧ y.op = .OffPtr ∧ termVL tabs y = true ∧ y.args.size = 1 ∧
      wordShape (shpL tabs y.type) = true ∧ offOK y.auxInt = true ∧
      u.auxInt.toInt = x.auxInt.toInt + y.auxInt.toInt ∧ u.args = #[y.args[0]!, x.args[1]!] ∧
      M.get? y.args[0]! = some bv := by
  unfold ldOffFold at h
  split at h
  · rename_i x _ u' hx
    split at h
    · cases h
    rename_i p hp
    have e : x.args[0]! = p := by simp [getElem!_def, hp]
    subst e
    split at h
    · rename_i y hy
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, -⟩, h11⟩, h12⟩, h13⟩, h14⟩,
          h15⟩, h16⟩, h17⟩, h18⟩ := hc
        obtain ⟨bv, hbv⟩ := Option.isSome_iff_exists.1 h18
        exact ⟨x, y, bv, hx, hy, h3, h4, h5, h6, h7, h8, h9, h11, h12, h13, h14, h15, h16, h17, hbv⟩
      · cases h
    · cases h
  · cases h

/-- **The folded load offset**: an integer load at offset `k1` (no aux) of `OffPtr [k2] z` (at a
word shape) is refined by the load at `k1 + k2` of any refinement of `z`, on a refined memory
(`offPtr_cases`, `addr_fold`). -/
theorem ldVal_offFold {T0 U : Ty} {z z' X X' : Val} (hz : z.hasTy T0 = true)
    (hU : wordShape U = true) {k1 k2 k : Int64} (h1 : offOK k1 = true) (h2 : offOK k2 = true)
    (hk : k.toInt = k1.toInt + k2.toInt) (hzz : Sem.Refines z z') (hX : Sem.Refines X X')
    (sz : Nat) (s : Bool) (T : Ty) :
    Sem.Refines (ldVal tabs sz s T k1 none [(PtrOps.offPtr k2 [z]).retypeL U, X])
      (ldVal tabs sz s T k none [z', X']) := by
  obtain ⟨b1, -⟩ := offOK_toNat h1
  obtain ⟨b2, -⟩ := offOK_toNat h2
  have hp : symPtr tabs k1 none ((PtrOps.offPtr k2 [z]).retypeL U) = none ∨
      symPtr tabs k1 none ((PtrOps.offPtr k2 [z]).retypeL U) = symPtr tabs k none z := by
    simp only [symPtr]
    rcases offPtr_cases hU k2 z with h0 | h0
    · left; rw [h0, retypeL_poison]; rfl
    · rw [h0]
      rcases addr_fold hz (argWidth_of_wordShape hU) b1 b2 with h | h
      · exact .inl h
      · right; rw [h, hk, BitVec.ofInt_add]
  rcases hp with hp | hp
  · have : ldVal tabs sz s T k1 none [(PtrOps.offPtr k2 [z]).retypeL U, X] = .poison := by
      cases X <;> simp only [ldVal, hp, Option.elim]
    rw [this]; exact .poison _
  · have : ldVal tabs sz s T k1 none [(PtrOps.offPtr k2 [z]).retypeL U, X] =
        ldVal tabs sz s T k none [z, X] := by
      cases X <;> simp only [ldVal, hp]
    rw [this]
    exact ldVal_mono tabs sz s T k none (.cons hzz (.cons hX .nil))

/-- **An `OffPtr` offset folded into an integer load** (`ldOffFold`): the load `x` at `v` of
`OffPtr [k2] b` becomes the load `u` of `b` at `k1 + k2`. Its denotation refines the old one
(`ldVal_offFold`, `termPut_den`): the step `M → M.put v u` refines every denotation, and
`ReplayInvL` carries over. -/
theorem ReplayInvL.ldOffFold {v : ID} {defs : List Value} {u : Value}
    (hI : ReplayInvL tabs D₀ C₀ M C) (hld : ldOffFold tabs M v defs = some u) :
    ReplayInvL tabs D₀ C₀ (M.put v u) C ∧
      ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n y, C y →
        Sem.Refines (denL true M.get? tabs ρ n y) (denL true (M.put v u).get? tabs ρ (id n) y) := by
  obtain ⟨x, y, bv, hx, hy, hop, hty, hl0, hxa, hua, hsz, hk1, hyop, hyt, hysz, hyw, hk2, hk,
    huargs, hbv⟩ := ldOffFold_cases hld
  obtain ⟨⟨sz, sg⟩, hl⟩ := Option.isSome_iff_exists.1 hl0
  obtain ⟨hg, hmd⟩ := ldOp_arm hl
  have hxt : termVL tabs x = true := termVL_ld hl
  have hut : termVL tabs u = true := termVL_ld (p := (sz, sg)) (by rw [hop]; exact hl)
  have hyl : y.args.toList = [y.args[0]!] := congrArg Array.toList (args_one hysz)
  have hxl : x.args.toList = [x.args[0]!, x.args[1]!] := congrArg Array.toList (args_two hsz)
  have hul : u.args.toList = [y.args[0]!, x.args[1]!] := by rw [huargs]
  let P : (ID → Val) → Prop := fun F => F x.args[0]! = .poison ∨
    ∃ w, w.hasTy (shpL tabs bv.type) = true ∧ Sem.Refines w (F y.args[0]!) ∧
      F x.args[0]! = (PtrOps.offPtr y.auxInt [w]).retypeL (shpL tabs y.type)
  have htop : ∀ F G : ID → Val, (∀ a, Sem.Refines (F a) (G a)) → P F →
      Sem.Refines
        ((opValL tabs x.op (shpL tabs x.type) x.auxInt x.aux (x.args.toList.map F)).retypeL
          (shpL tabs x.type))
        ((opValL tabs u.op (shpL tabs u.type) u.auxInt u.aux (u.args.toList.map G)).retypeL
          (shpL tabs u.type)) := by
    intro F G hFG hPF
    rw [hop, hty, hxa, hua, hxl, hul]
    simp only [List.map_cons, List.map_nil]
    rw [opValL_ld hg hmd hl, opValL_ld hg hmd hl]
    apply retypeL_mono
    rcases hPF with h0 | ⟨w, hw, hwb, h0⟩
    · rw [h0]
      have : ldVal tabs sz sg (shpL tabs x.type) x.auxInt none [.poison, F x.args[1]!] = .poison := by
        cases F x.args[1]! <;> rfl
      rw [this]; exact .poison _
    · rw [h0]
      exact ldVal_offFold hw hyw hk1 hk2 hk (hwb.trans (hFG _)) (hFG _) _ _ _
  have hP : ∀ ρ, TypedL true M.get? tabs ρ → ∀ k, P (denL true M.get? tabs ρ k) := fun ρ hT k => by
    rcases k with _ | k
    · exact .inl rfl
    · refine .inr ⟨denL true M.get? tabs ρ k y.args[0]!, den_hasTyL hT k hbv,
        denL_fuel_mono true M.get? tabs ρ k (k + 1) _ (by omega), ?_⟩
      rw [denT_succ hy hyt, hyop, hyl]
      simp only [List.map_cons, List.map_nil, opValL_offPtr]
  have hstep : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n y, C y →
      Sem.Refines (denL true M.get? tabs ρ n y) (denL true (M.put v u).get? tabs ρ (id n) y) :=
    fun ρ hT _ n z _ => termPut_den hx hxt hut (hP ρ hT) htop n z
  have hcl : C v → ∀ z ∈ u.args, C z := fun hv z hz => by
    have hxa' := closed_args hI.closed hx hv
    have h0 : C x.args[0]! :=
      hxa' _ (by rw [getElem!_pos x.args 0 (by omega)]; exact Array.getElem_mem _)
    rw [huargs] at hz
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact closed_args hI.closed hy h0 _
        (by rw [getElem!_pos y.args 0 (by omega)]; exact Array.getElem_mem _)
    · exact hxa' _ (by rw [getElem!_pos x.args 1 (by omega)]; exact Array.getElem_mem _)
  refine ⟨{ closed := put_closed hcl hI.closed
            typed := fun ρ h => put_typed hx hty (by rw [hxt, hut]) (hI.typed ρ h)
            atoms := fun y a hy ha hargs => ?_ }, hstep⟩
  obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
  have hyv : y ≠ v := fun h => by subst h; rw [hx] at ha'; cases ha'; rw [hxt] at hat; cases hat
  exact ⟨a', by rw [get?_put]; simp [hyv, ha'], hat, hrest.imp id fun hr =>
    hr.step (g := id) (fun _ h => h) hI.typed hstep⟩

/-! ### A `Store`'s arm64 store indexed (`stIdxFold`) -/

/-- What `stIdxFold` says. -/
theorem stIdxFold_cases {x u : Value} (h : stIdxFold tabs M x u = true) :
    ∃ y o s, M.get? x.args[0]! = some y ∧ idxStore u.op = some (o, s) ∧
      (stSize x.op).isSome = true ∧ u.type = x.type ∧ x.auxInt = 0 ∧ x.aux = none ∧
      x.args.size = 3 ∧ termVL tabs y = true ∧ y.args.size = 2 ∧
      wordShape (shpL tabs y.type) = true ∧
      (y.op = .ARM64ADD ∧ s = 1 ∨ y.op = .ARM64ADDshiftLL ∧ idxShift y.auxInt = some s) ∧
      u.args = #[y.args[0]!, y.args[1]!, x.args[1]!, x.args[2]!] := by
  unfold stIdxFold at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, h7⟩, h8⟩ := h
  split at h8
  · rename_i y o s hy ho
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h8
    obtain ⟨⟨⟨⟨⟨-, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h8
    exact ⟨y, o, s, hy, ho, h1, h2, h3, h4, h7, h10, h11, h12, h13, h14⟩
  · cases h8

/-- A 64-bit integer at a word shape keeps its value under `retypeL`. -/
theorem int64_retypeL {T : Ty} (hT : T = .int .w64 ∨ ∃ e, T = .ptr e) (x : BitVec 64) :
    (Val.int .w64 x).retypeL T = .int .w64 x := by
  unfold Val.retypeL
  rcases hT with rfl | ⟨e, rfl⟩ <;>
  · rw [Mono.widen_of_hasTy _ _ (by simp [Val.hasTy])]; rfl

/-- `ptrRes` at a word shape keeps its value under `retypeL`. -/
theorem ptrRes_retypeL {T : Ty} (hT : T = .int .w64 ∨ ∃ e, T = .ptr e) (q : Ptr) :
    (PtrOps.ptrRes q).retypeL T = PtrOps.ptrRes q := by
  unfold PtrOps.ptrRes
  split
  · exact word_retypeL hT q
  · exact retypeL_poison T

/-- `Arm64.res` at a word shape is the 64-bit integer. -/
theorem res_word {T : Ty} (hT : T = .int .w64 ∨ ∃ e, T = .ptr e) (x : BitVec 64) :
    Arm64.res T x = .int .w64 x := by
  rcases hT with rfl | ⟨e, rfl⟩ <;> rfl

/-- `addP` at a word shape, kept by `retypeL`, is `ADD` of the 64-bit integer. -/
theorem addP_retypeL {T : Ty} (hT : T = .int .w64 ∨ ∃ e, T = .ptr e) (a : Val) (z : BitVec 64) :
    (Arm64.addP T a z).retypeL T = Arm64.add .other [a, .int .w64 z] := by
  cases a with
  | ptr p =>
    simp only [Arm64.addP, Arm64.add, Arm64.reg, BitVec.setWidth_eq]
    exact ptrRes_retypeL hT _
  | _ =>
    simp only [Arm64.addP, Arm64.add, Arm64.op2, Arm64.reg, BitVec.setWidth_eq]
    first
    | (rw [res_word hT, int64_retypeL hT]; rfl)
    | exact retypeL_poison T

/-- `ADD a b` at a word shape, kept by `retypeL`, is the indexed address at the scale 1. -/
theorem add_retypeL {T : Ty} (hT : T = .int .w64 ∨ ∃ e, T = .ptr e) (a b : Val) :
    (Arm64.add T [a, b]).retypeL T = idxAddr 1 a b := by
  simp only [idxAddr, ite_true]
  cases a <;> cases b <;>
    simp only [Arm64.add, Arm64.op2, Arm64.reg] <;>
    first
    | exact retypeL_poison T
    | exact ptrRes_retypeL hT _
    | (rw [res_word hT, int64_retypeL hT]; rfl)
    | (split
       · rw [res_word hT, int64_retypeL hT]; rfl
       · exact retypeL_poison T)

/-- What `idxShift` says: a scale other than 1 that shifting left by the auxint multiplies by. -/
theorem idxShift_cases {k : Int64} {s : Nat} (h : idxShift k = some s) :
    s ≠ 1 ∧ ∀ y : BitVec 64, Arm64.shifted .ll k y = y * BitVec.ofNat 64 s := by
  unfold idxShift at h
  split at h
  · rename_i hk; cases h
    rw [beq_iff_eq] at hk; subst hk
    refine ⟨by decide, fun y => ?_⟩
    simp only [Arm64.shifted, Arm64.Shift.apply, Arm64.amt]
    rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl
  split at h
  · rename_i hk; cases h
    rw [beq_iff_eq] at hk; subst hk
    refine ⟨by decide, fun y => ?_⟩
    simp only [Arm64.shifted, Arm64.Shift.apply, Arm64.amt]
    rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl
  split at h
  · rename_i hk; cases h
    rw [beq_iff_eq] at hk; subst hk
    refine ⟨by decide, fun y => ?_⟩
    simp only [Arm64.shifted, Arm64.Shift.apply, Arm64.amt]
    rw [BitVec.shiftLeft_eq_mul_twoPow]; rfl
  · cases h

/-- `ADD a (b << k)` at a word shape, kept by `retypeL`, is the indexed address at the scale
`2^k` (`idxShift`). -/
theorem addSh_retypeL {T : Ty} (hT : T = .int .w64 ∨ ∃ e, T = .ptr e) {k : Int64} {s : Nat}
    (hk : idxShift k = some s) (a b : Val) :
    (Arm64.addSh T .ll k [a, b]).retypeL T = idxAddr s a b := by
  obtain ⟨hs, hsh⟩ := idxShift_cases hk
  simp only [idxAddr, hs, ite_false, Arm64.addSh]
  cases hb : Arm64.reg b with
  | some y => dsimp only; rw [addP_retypeL hT, hsh]
  | none => exact retypeL_poison T

/-- `opValL` of `ADD` on two arguments: `Arm64.add`. -/
theorem opValL_add (tabs : Tables) (T : Ty) (k : Int64) (ax : Option AuxRef) (a b : Val) :
    opValL tabs .ARM64ADD T k ax [a, b] = Arm64.add T [a, b] := by
  simp only [opValL, show Op.ARM64ADD.generic = false by decide,
    show (Op.ARM64ADD == .ARM64MOVDaddr) = false by decide,
    show ldOp? .ARM64ADD = none by decide, Bool.false_eq_true, ite_false]
  rfl

/-- `opValL` of `ADDshiftLL [k]` on two arguments: `Arm64.addSh`. -/
theorem opValL_addSh (tabs : Tables) (T : Ty) (k : Int64) (ax : Option AuxRef) (a b : Val) :
    opValL tabs .ARM64ADDshiftLL T k ax [a, b] = Arm64.addSh T .ll k [a, b] := by
  simp only [opValL, show Op.ARM64ADDshiftLL.generic = false by decide,
    show (Op.ARM64ADDshiftLL == .ARM64MOVDaddr) = false by decide,
    show ldOp? .ARM64ADDshiftLL = none by decide, Bool.false_eq_true, ite_false]
  rfl

/-- **A `Store`'s arm64 store indexed** (`stIdxFold`, `ARM64.rules:786-791`, `806-808`): the
store at offset 0 without aux of a `Store` of `D₀` whose address (argument 0) is `ADD p i` or
`ADDshiftLL [k] p i` (a term at a word shape) in `M` becomes the indexed store on `p i`, whose
indexed address (`idxAddr`) is that term's value (`add_retypeL`, `addSh_retypeL`); value and
memory stay (`IdxRefL`). -/
theorem ReplayInvL.idxFold {v : ID} {x u : Value} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (ht : termVL tabs x = false) (ht' : termVL tabs u = false)
    (hfold : stIdxFold tabs M x u = true) (hsrc : ∀ a, D₀ v = some a → a.op = .Store) :
    ReplayInvL tabs D₀ C₀ (M.put v u) C := by
  obtain ⟨y, o, s, hy, ho, hst, hty, hxk, hxa, hsz, hyt, hysz, hyw, hyop, hargs⟩ :=
    stIdxFold_cases hfold
  have hb := args_two hysz
  have hmem : ∀ i, i < x.args.size → x.args[i]! ∈ x.args := fun i h => by
    rw [getElem!_pos x.args i h]; exact Array.getElem_mem h
  have hymem : ∀ i, i < 2 → y.args[i]! ∈ y.args := fun i h => by
    rw [getElem!_pos y.args i (by omega)]; exact Array.getElem_mem (by omega)
  have e0 : u.args[0]! = y.args[0]! := by rw [hargs]; rfl
  have e1 : u.args[1]! = y.args[1]! := by rw [hargs]; rfl
  have e2 : u.args[2]! = x.args[1]! := by rw [hargs]; rfl
  have e3 : u.args[3]! = x.args[2]! := by rw [hargs]; rfl
  have hcl : C v → ∀ a ∈ u.args, C a := fun hv a ha => by
    have hxa := closed_args hI.closed hx hv
    have hya := closed_args hI.closed hy (hxa _ (hmem 0 (by omega)))
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hya _ (hymem 0 (by omega))
    · exact hya _ (hymem 1 (by omega))
    · exact hxa _ (hmem 1 (by omega))
    · exact hxa _ (hmem 2 (by omega))
  have hstep : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n z, C z →
      Sem.Refines (denL true M.get? tabs ρ n z) (denL true (M.put v u).get? tabs ρ (id n) z) :=
    fun ρ _ _ n z _ => by rw [rename_den hx ht ht']; exact Sem.Refines.refl _
  refine
    { closed := put_closed hcl hI.closed
      typed := fun ρ h => put_typed hx hty (by rw [ht, ht']) (hI.typed ρ h)
      atoms := fun z a hz ha hargs' => ?_ }
  obtain ⟨a', ha', hat, hrest⟩ := hI.atoms z a hz ha hargs'
  by_cases hzv : z ≠ v
  · exact ⟨a', by rw [get?_put]; simp [hzv, ha'], hat, hrest.imp id fun hr =>
      hr.step (fun _ h => h) hI.typed hstep⟩
  obtain rfl : z = v := Classical.byContradiction hzv
  rw [hx] at ha'; cases ha'
  refine ⟨u, by rw [get?_put]; simp, ht', .inr (.inr ?_)⟩
  have hS := hsrc a hz
  rcases hrest with hf | ⟨hsza, hr⟩ | hix
  · exact absurd hst (by rw [(argFree_cases hf).1]; decide)
  rotate_left
  · obtain ⟨⟨p, s'⟩, hp⟩ := Option.isSome_iff_exists.1 hix.2.2.1
    rw [(idxStore_facts hp).2.1] at hst; cases hst
  have hsc : idxScale u.op = s := by simp [idxScale, ho]
  obtain ⟨hc0, hd0⟩ := hr 0 (by omega)
  have hya := closed_args hI.closed hy hc0
  have hval : ∀ j < 2, ∀ n, ∃ m, ∀ ρ, TypedL true D₀ tabs ρ → FrameVals tabs 0 D₀ ρ →
      ArgRel tabs 0 none (denL true D₀ tabs ρ n a.args[j + 1]!)
        (denL true M.get? tabs ρ m x.args[j + 1]!) := fun j hj n => by
    obtain ⟨-, hd⟩ := hr (j + 1) (by omega)
    obtain ⟨m, hm⟩ := hd n
    exact ⟨m, fun ρ hρ hF => by have := hm ρ hρ hF; rwa [stArg_succ] at this⟩
  have hux : ∀ j < 2, u.args[j + 2]! = x.args[j + 1]! := fun j hj => by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · exact e2
    · exact e3
  refine ⟨by omega, by rw [hargs]; rfl, by rw [ho]; rfl, fun i hi => ?_, fun n => ?_,
    fun j hj n => ?_⟩
  · obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    · rw [e0]; exact hya _ (hymem 0 (by omega))
    · rw [e1]; exact hya _ (hymem 1 (by omega))
    · rw [e2]; exact (hr 1 (by omega)).1
    · rw [e3]; exact (hr 2 (by omega)).1
  · rw [stArg_zero hS hst, hxk, hxa] at hd0
    obtain ⟨m, hm⟩ := hd0 n
    rw [hsc, e0, e1]
    rcases m with _ | m
    · exact ⟨0, fun ρ hρ hF => addrRef_poison (hm ρ hρ hF)⟩
    refine ⟨m, fun ρ hρ hF => ?_⟩
    rw [rename_den hx ht ht', rename_den hx ht ht']
    have h1 := hm ρ hρ hF
    rw [denT_succ hy hyt, hb,
      show (#[y.args[0]!, y.args[1]!] : Array ID).toList = [y.args[0]!, y.args[1]!] from rfl] at h1
    simp only [List.map_cons, List.map_nil] at h1
    rcases hyop with ⟨hop, rfl⟩ | ⟨hop, hk⟩
    · rwa [hop, opValL_add, add_retypeL (wordShape_cases hyw)] at h1
    · rwa [hop, opValL_addSh, addSh_retypeL (wordShape_cases hyw) hk] at h1
  · obtain ⟨m, hm⟩ := hval j hj n
    exact ⟨m, fun ρ hρ hF => by rw [hux j hj, rename_den hx ht ht']; exact hm ρ hρ hF⟩

/-! ### An indexed store's index scaled (`stIdxScale`) -/

/-- What `stIdxScale` says. -/
theorem stIdxScale_cases {x u : Value} (h : stIdxScale tabs M x u = true) :
    ∃ y o s, idxStore x.op = some (o, 1) ∧ idxStore u.op = some (o, s) ∧
      M.get? x.args[1]! = some y ∧ u.type = x.type ∧ x.args.size = 4 ∧ termVL tabs y = true ∧
      y.op = .ARM64SLLconst ∧ y.args.size = 1 ∧ wordShape (shpL tabs y.type) = true ∧
      idxShift y.auxInt = some s ∧ u.args = #[x.args[0]!, y.args[0]!, x.args[2]!, x.args[3]!] := by
  unfold stIdxScale at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, h6⟩, h7⟩ := h
  split at h7
  · rename_i o o' s y hxo huo hy
    simp only [Bool.and_eq_true, beq_iff_eq] at h7
    obtain ⟨⟨⟨⟨⟨⟨rfl, hyt⟩, hyop⟩, hysz⟩, hyw⟩, hk⟩, hargs⟩ := h7
    exact ⟨y, o', s, hxo, huo, hy, h1, h6, hyt, hyop, hysz, hyw, hk, hargs⟩
  · cases h7

/-- `opValL` of `SLLconst [k]` on one argument: `Arm64.op1` of the left shift. -/
theorem opValL_sll (tabs : Tables) (T : Ty) (k : Int64) (ax : Option AuxRef) (a : Val) :
    opValL tabs .ARM64SLLconst T k ax [a] =
      Arm64.op1 T (Arm64.Shift.ll.apply · (Arm64.amt k)) [a] := by
  simp only [opValL, show Op.ARM64SLLconst.generic = false by decide,
    show (Op.ARM64SLLconst == .ARM64MOVDaddr) = false by decide,
    show ldOp? .ARM64SLLconst = none by decide, Bool.false_eq_true, ite_false]
  rfl

/-- The indexed address at the scale 1 on a `poison` index is `poison`. -/
theorem idxAddr_one_poison (a : Val) : idxAddr 1 a .poison = .poison := by
  simp only [idxAddr, ite_true]
  cases a <;> rfl

/-- The index `SLLconst [k] r` at a word shape, kept by `retypeL`, at the scale 1 is refined by
`r` at the scale `2^k` (`idxShift`). -/
theorem sll_idxAddr {T : Ty} (hT : T = .int .w64 ∨ ∃ e, T = .ptr e) {k : Int64} {s : Nat}
    (hk : idxShift k = some s) (tabs : Tables) (ax : Option AuxRef) (a r : Val) :
    Sem.Refines (idxAddr 1 a ((opValL tabs .ARM64SLLconst T k ax [r]).retypeL T))
      (idxAddr s a r) := by
  obtain ⟨hs, hsh⟩ := idxShift_cases hk
  rw [opValL_sll]
  cases hr : Arm64.reg r with
  | none =>
    simp only [Arm64.op1, hr, retypeL_poison, idxAddr_one_poison]
    exact .poison _
  | some y =>
    simp only [Arm64.op1, hr, idxAddr, hs, ↓reduceIte]
    rw [res_word hT, int64_retypeL hT]
    have h := hsh y
    simp only [Arm64.shifted] at h
    rw [h]
    exact Sem.Refines.refl _

/-- **An indexed store's index scaled** (`stIdxScale`, `ARM64.rules:809`, `810`): the indexed
store at the scale 1 of a `Store` of `D₀` (three arguments) whose index (argument 1) is
`SLLconst [k] r` (a term at a word shape) in `M` becomes the indexed store at the scale `2^k` on
`r`, whose indexed address refines the old one (`sll_idxAddr`); value and memory stay
(`IdxRefL`). -/
theorem ReplayInvL.scaleIdx {v : ID} {x u : Value} (hI : ReplayInvL tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (ht : termVL tabs x = false) (ht' : termVL tabs u = false)
    (hsc : stIdxScale tabs M x u = true)
    (hsrc : ∀ a, D₀ v = some a → a.op = .Store ∧ a.args.size = 3) :
    ReplayInvL tabs D₀ C₀ (M.put v u) C := by
  obtain ⟨y, o, s, hxo, huo, hy, hty, hsz, hyt, hyop, hysz, hyw, hk, hargs⟩ :=
    stIdxScale_cases hsc
  have hb := args_one hysz
  have hmem : ∀ i, i < x.args.size → x.args[i]! ∈ x.args := fun i h => by
    rw [getElem!_pos x.args i h]; exact Array.getElem_mem h
  have hy0 : y.args[0]! ∈ y.args := by
    rw [getElem!_pos y.args 0 (by omega)]; exact Array.getElem_mem (by omega)
  have e0 : u.args[0]! = x.args[0]! := by rw [hargs]; rfl
  have e1 : u.args[1]! = y.args[0]! := by rw [hargs]; rfl
  have hux : ∀ j < 2, u.args[j + 2]! = x.args[j + 2]! := fun j hj => by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · rw [hargs]; rfl
    · rw [hargs]; rfl
  have hcl : C v → ∀ a ∈ u.args, C a := fun hv a ha => by
    have hxa := closed_args hI.closed hx hv
    have hya := closed_args hI.closed hy (hxa _ (hmem 1 (by omega)))
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hxa _ (hmem 0 (by omega))
    · exact hya _ hy0
    · exact hxa _ (hmem 2 (by omega))
    · exact hxa _ (hmem 3 (by omega))
  have hstep : ∀ ρ, TypedL true M.get? tabs ρ → FrameVals tabs 0 D₀ ρ → ∀ n z, C z →
      Sem.Refines (denL true M.get? tabs ρ n z) (denL true (M.put v u).get? tabs ρ (id n) z) :=
    fun ρ _ _ n z _ => by rw [rename_den hx ht ht']; exact Sem.Refines.refl _
  refine
    { closed := put_closed hcl hI.closed
      typed := fun ρ h => put_typed hx hty (by rw [ht, ht']) (hI.typed ρ h)
      atoms := fun z a hz ha hargs' => ?_ }
  obtain ⟨a', ha', hat, hrest⟩ := hI.atoms z a hz ha hargs'
  by_cases hzv : z ≠ v
  · exact ⟨a', by rw [get?_put]; simp [hzv, ha'], hat, hrest.imp id fun hr =>
      hr.step (fun _ h => h) hI.typed hstep⟩
  obtain rfl : z = v := Classical.byContradiction hzv
  rw [hx] at ha'; cases ha'
  refine ⟨u, by rw [get?_put]; simp, ht', .inr (.inr ?_)⟩
  obtain ⟨-, hS3⟩ := hsrc a hz
  rcases hrest with hf | ⟨hsza, -⟩ | hix
  · exact absurd (argFree_cases hf).1 (idxStore_facts hxo).2.2.2.2.2.1
  · rw [hsz, hS3] at hsza; cases hsza
  obtain ⟨h3, -, -, hC, hA, hV⟩ := hix
  have hsc1 : idxScale x.op = 1 := by simp [idxScale, hxo]
  have hscs : idxScale u.op = s := by simp [idxScale, huo]
  have hyC := closed_args hI.closed hy (hC 1 (by omega))
  refine ⟨h3, by rw [hargs]; rfl, by rw [huo]; rfl, fun i hi => ?_, fun n => ?_,
    fun j hj n => ?_⟩
  · obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    · rw [e0]; exact hC 0 (by omega)
    · rw [e1]; exact hyC _ hy0
    · rw [hux 0 (by omega)]; exact hC 2 (by omega)
    · rw [hux 1 (by omega)]; exact hC 3 (by omega)
  · obtain ⟨m, hm⟩ := hA n
    rw [hsc1] at hm
    rw [hscs, e0, e1]
    rcases m with _ | m
    · refine ⟨0, fun ρ hρ hF => addrRef_poison (act := 0) (k := 0) ?_⟩
      have h1 := hm ρ hρ hF
      rwa [show denL true M.get? tabs ρ 0 x.args[1]! = .poison from rfl, idxAddr_one_poison] at h1
    refine ⟨m + 1, fun ρ hρ hF => ?_⟩
    rw [rename_den hx ht ht', rename_den hx ht ht']
    have h1 := hm ρ hρ hF
    rw [denT_succ hy hyt, hb, show (#[y.args[0]!] : Array ID).toList = [y.args[0]!] from rfl,
      hyop] at h1
    simp only [List.map_cons, List.map_nil] at h1
    exact ArgRel.trans_right (o := some (0, none)) h1
      ((sll_idxAddr (wordShape_cases hyw) hk tabs y.aux _ _).trans
        (idxAddr_mono _ (Sem.Refines.refl _)
          (denL_fuel_mono true M.get? tabs ρ m (m + 1) _ (by omega))))
  · obtain ⟨m, hm⟩ := hV j hj n
    exact ⟨m, fun ρ hρ hF => by rw [hux j hj, rename_den hx ht ht']; exact hm ρ hρ hF⟩

/-- **`copyStepL` keeps the replay invariants**: an argument replaced as `CopyOKL` allows
(`ReplayInvL.copy`, `copyPut_denL`), or no change. -/
theorem copyStepL_inv {f : Func} {B : BMapL} {v : ID} {i : Nat} {src : ID}
    (hI : ReplayInvL tabs D₀ C₀ M C) (hB : BInvL tabs f D₀ C₀ M C B) :
    ReplayInvL tabs D₀ C₀ (copyStepL tabs M v i src) C ∧
      BInvL tabs f D₀ C₀ (copyStepL tabs M v i src) C B := by
  unfold copyStepL
  split
  · rename_i x hx
    split
    · rename_i hi
      split
      · rename_i hr
        have hr' : CopyOKL tabs M x i src hi := by simpa only [Bool.or_eq_true] using hr
        exact ⟨hI.copy hx hi hr', hB.mono (g := id) (fun _ h => h) hI.typed
          fun ρ hρ _ n y hy => copyPut_denL hx hi hr' hI.closed hρ n y hy⟩
      · exact ⟨hI, hB⟩
    · exact ⟨hI, hB⟩
  · exact ⟨hI, hB⟩

/-- `copyFixL` keeps the replay invariants (`copyStepL_inv`). -/
theorem copyFixL_inv {f : Func} {B : BMapL} :
    ∀ (cs : List (ID × Nat × ID)) {M : Defs} {C : ID → Prop}, ReplayInvL tabs D₀ C₀ M C →
      BInvL tabs f D₀ C₀ M C B →
      ReplayInvL tabs D₀ C₀ (copyFixL tabs M cs) C ∧ BInvL tabs f D₀ C₀ (copyFixL tabs M cs) C B
  | [], _, _, hI, hB => ⟨hI, hB⟩
  | (_, _, _) :: cs, _, _, hI, hB =>
    let h := copyStepL_inv hI hB
    copyFixL_inv cs h.1 h.2

/-- **A strength-reduced multiplication** (`mulOKL`): `v` becomes a `Copy` of fresh terms the
event built; the step refines every denotation of `C` (`mul_step`), and `ReplayInvL` carries
over to `C` and, if `C` holds `v`, the event's definitions. -/
theorem ReplayInvL.mul {v : ID} {defs ds : List Value} (hI : ReplayInvL tabs D₀ C₀ M C)
    (h : mulOKL tabs M v defs = some ds) :
    ReplayInvL tabs D₀ C₀ (putAll M ds) (fun y => C y ∨ (C v ∧ y ∈ defIds ds)) := by
  obtain ⟨⟨x, hx, hxt⟩, hkeep, hids, hnew⟩ := mul_frame h
  have hnew' : ∀ y, C v → y ∈ defIds ds → ∃ m, (putAll M ds).get? y = some m ∧
      ∀ a ∈ m.args, C a ∨ (C v ∧ a ∈ defIds ds) := by
    intro y hv hy
    obtain ⟨u, hu, -, hargs⟩ := hnew y hy
    refine ⟨u, hu, fun a ha => ?_⟩
    rcases hargs a ha with ⟨x', hx', ha'⟩ | ha'
    · rw [hx] at hx'; cases hx'; exact .inl (closed_args hI.closed hx hv a ha')
    · exact .inr ⟨hv, ha'⟩
  refine { closed := ?_, typed := ?_, atoms := ?_ }
  · intro y hy
    rcases hy with hy | ⟨hv, hy⟩
    · by_cases hd : y ∈ defIds ds
      · obtain ⟨m, hm, -⟩ := hI.closed y hy
        rcases hids y hd with rfl | h
        · exact hnew' _ hy hd
        · rw [hm] at h; cases h
      · obtain ⟨m, hm, hargs⟩ := hI.closed y hy
        exact ⟨m, by rw [hkeep y hd, hm], fun a ha => .inl (hargs a ha)⟩
    · exact hnew' y hv hy
  · intro ρ hρ a ha hsome
    by_cases hd : a ∈ defIds ds
    · obtain ⟨u, hu, ht, -⟩ := hnew a hd
      exact absurd ⟨u, hu, ht⟩ ha
    · have he := hkeep a hd
      have hshape : shapeL true (putAll M ds).get? tabs a = shapeL true M.get? tabs a := by
        simp [shapeL, he]
      rw [hshape]
      exact hI.typed ρ hρ a (fun ⟨u, hu, ht⟩ => ha ⟨u, by rw [he]; exact hu, ht⟩) (he ▸ hsome)
  · intro y a hy ha hargs
    obtain ⟨a', ha', hat, hrest⟩ := hI.atoms y a hy ha hargs
    have hd : y ∉ defIds ds := fun hd => by
      rcases hids y hd with rfl | h
      · rw [hx] at ha'; cases ha'; rw [hxt] at hat; cases hat
      · rw [ha'] at h; cases h
    exact ⟨a', by rw [hkeep y hd, ha'], hat, hrest.imp id fun hr =>
      hr.step (g := fun n => n * ds.length) (fun _ h => .inl h) hI.typed
        fun ρ hρ _ n z hz => mul_step h hI.closed hρ n z hz⟩

end Inv

/-- What `ruleOKL` establishes: the matched value is a term and some commutation choice
validates the definitions it returns. -/
theorem ruleOKL_facts {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs ds : List Value}
    (h : ruleOKL tabs M r v defs = some ds) :
    ∃ sw ∈ choices (GoFV.Opt.RewriteCheck.Pat.commutes r.pat),
      Nonempty (RuleFactsL tabs M (Rule.swapC r sw) v ds) := by
  unfold ruleOKL at h
  split at h
  · cases h
  · rename_i x hx
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨sw, hsw, h1⟩ := List.exists_of_findSome?_eq_some h
      dsimp only at h1
      split at h1
      · rename_i h2
        cases h1
        exact ⟨sw, hsw, ruleFactsL hx hc.1 hc.2 h2⟩
      · cases h1
    · cases h

/-- **Replay**: a successful replay of the log keeps `ReplayInvL` and `BInvL` (from `D₀`, `f`'s
definitions). -/
theorem replayL_inv {tabs : Tables} {s : RuleSet} (hs : ArmRuleSet.AllSound s)
    {f : Func} {D₀ : ID → Option Value} {C₀ : ID → Prop} (hD : ∀ y, D₀ y = f.value? y) :
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
    · -- a constant folded into a lowered bounds panic (`pbFoldEv`): no change
      exact replayL_inv hs hD evs M M' B B' C h hI hB
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
        rcases hk with ⟨ht, ht', htop, hsa⟩ | ⟨hren, ht⟩
        · have hso : SetOpSoundT x.op o' := by
            rcases hck with hsd | ⟨o, o3, he3, hr3, -, -, -, -, hso⟩ | ⟨o, o3, he3, hr3, -, -, hren⟩ |
                ⟨om, n, pty, pai, pax, par, pargs, pc, hpat, hom⟩ | hm
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
            · simp [ArmRule.Mul, GoFV.Rules.Interp.mulResult, hres] at hm
          exact replayL_inv hs hD evs _ M' B B' C h
            (copyFixL_inv _ (hI.setOp hx ht ht' htop hsa hso)
              (hB.mono (g := id) (fun _ h => h) hI.typed fun ρ hρ _ n y _ =>
                setOp_den hx ht ht' htop hsa hso hρ n y)).1
            (copyFixL_inv _ (hI.setOp hx ht ht' htop hsa hso)
              (hB.mono (g := id) (fun _ h => h) hI.typed fun ρ hρ _ n y _ =>
                setOp_den hx ht ht' htop hsa hso hρ n y)).2
        · have ht' := renameOp_dst hren tabs { x with op := o' } rfl
          have hfree : argFree tabs x = true → argFree tabs { x with op := o' } = true :=
            fun hf => absurd (argFree_cases hf).1 (renameOp_src_ne hren)
          have hrel : ∀ (a : Value) (i act : Nat) (s t : Val), ArgRel tabs act (stArg a x i) s t →
              ArgRel tabs act (stArg a { x with op := o' } i) s t := fun a i act s t h => by
            rw [stArg_none (w := { x with op := o' }) (renameOp_stSize hren).2]
            rwa [stArg_none (renameOp_stSize hren).1] at h
          have hI2 := hI.atomPut hx ht ht' rfl (fun hv a ha => closed_args hI.closed hx hv a ha)
            (.inr ⟨rfl, renameOp_idx hren, hfree, hrel⟩)
          have hB2 := hB.mono (M' := M.put v { x with op := o' }) (g := id) (fun _ h => h)
            hI.typed fun ρ _ _ n y _ => by
              rw [rename_den hx ht ht']; exact Sem.Refines.refl _
          exact replayL_inv hs hD evs _ M' B B' C h (copyFixL_inv _ hI2 hB2).1
            (copyFixL_inv _ hI2 hB2).2
      · cases h
    · -- value rules
      rename_i hnot
      split at h
      · -- a strength-reduced multiplication (`mulOKL`)
        split at h
        · rename_i ds hok
          have hput : ds.foldl (fun M u => M.put u.id u) M = putAll M ds := by
            simp [putAll, Array.foldl_toList]
          rw [hput] at h
          exact replayL_inv hs hD evs _ M' B B' _ h (hI.mul hok)
            (hB.mono (M' := putAll M ds) (C' := fun y => C y ∨ (C v ∧ y ∈ defIds ds))
              (g := fun n => n * ds.length) (fun y hy => .inl hy) hI.typed
              fun ρ hρ _ n y hy => mul_step hok hI.closed hρ n y hy)
        · cases h
      rename_i hmul
      split at h
      · rename_i ds hok
        obtain ⟨sw, hsw, ⟨F⟩⟩ := ruleOKL_facts hok
        have hsd : ArmRule.Sound1 (Rule.swapC cr.rule sw) := by
          rcases hck with hsd | ⟨o, o3, -, hr3, -⟩ | ⟨o, o3, -, hr3, -⟩ |
              ⟨om, n, pty, pai, pax, par, pargs, pc, hpat, hom⟩ | hm
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
          · exact (hmul hm).elim
        have hput : ds.foldl (fun M u => M.put u.id u) M = putAll M ds := by
          simp [putAll, Array.foldl_toList]
        rw [hput] at h
        have hI2 := hI.rule hsd F
        have hB2 := hB.mono (M' := putAll M ds) (C' := fun y => C y ∨ (C v ∧ y ∈ defIds ds))
          (fun y hy => .inl hy) hI.typed fun ρ hρ _ n y hy => F.step hsd hI.closed hρ n y hy
        exact replayL_inv hs hD evs _ M' B B' _ h (copyFixL_inv _ hI2 hB2).1
          (copyFixL_inv _ hI2 hB2).2
      · -- a lowered store, a folded store offset or a frame address (`atomDef`)
        split at h
        · rename_i u hdef
          obtain ⟨x0, hx0, ht, ht', hty, hk⟩ := atomDef_one hdef
          have hB' := hB.mono (g := id) (fun _ h => h) hI.typed fun ρ _ _ n y _ => by
            rw [rename_den (x' := u) hx0 ht ht']; exact Sem.Refines.refl _
          rcases hk with ⟨heq, hm, h0, hax⟩ | ⟨heq, hz⟩ | ⟨hsub, hal⟩ |
              ⟨hfold | hfold | hfold, a, ha, hS⟩ | ⟨hsc, a, ha, hS, hS3⟩
          · have hrel : ∀ (a : Value) (i act : Nat) (s t : Val),
                ArgRel tabs act (stArg a x0 i) s t → ArgRel tabs act (stArg a u i) s t :=
              fun a i act s t h => by
                rw [stArg_none (by rw [memLower_op hm]; rfl)] at h
                unfold stArg; split
                · rw [h0, hax]; exact addrRef_zero h
                · exact h
            exact replayL_inv hs hD evs _ M' B B' C h
              (hI.atomPut hx0 ht ht' hty (fun hv a ha => closed_args hI.closed hx0 hv a (heq ▸ ha))
                (.inr ⟨heq, by rw [memLower_op hm]; rfl, fun hf =>
                  absurd ((memLower_op hm).symm.trans (argFree_cases hf).1) (by decide), hrel⟩)) hB'
          · -- a lowered `Zero` or `Move` on the same arguments
            have hx0op : x0.op = .Zero ∨ x0.op = .Move := by
              rcases (bulkLower_cases hz).1 with ⟨h, -⟩ | ⟨h, -⟩
              · exact .inl h
              · exact .inr h
            have hst : stSize u.op = none := by
              rcases bulkLower_op hz with h | h | h | h <;> rw [h] <;> rfl
            have hst0 : stSize x0.op = none := by rcases hx0op with h | h <;> rw [h] <;> rfl
            have hrel : ∀ (a : Value) (i act : Nat) (s t : Val),
                ArgRel tabs act (stArg a x0 i) s t → ArgRel tabs act (stArg a u i) s t :=
              fun a i act s t h => by
                rw [stArg_none hst0] at h
                rw [stArg_none hst]; exact h
            exact replayL_inv hs hD evs _ M' B B' C h
              (hI.atomPut hx0 ht ht' hty (fun hv a ha => closed_args hI.closed hx0 hv a (heq ▸ ha))
                (.inr ⟨heq, by rcases hx0op with h0 | h0 <;> rw [h0] <;> rfl, fun hf => by
                  rcases hx0op with h0 | h0 <;>
                    exact absurd (h0.symm.trans (argFree_cases hf).1) (by decide), hrel⟩)) hB'
          · exact replayL_inv hs hD evs _ M' B B' C h
              (hI.atomPut hx0 ht ht' hty (fun hv a ha => closed_args hI.closed hx0 hv a (hsub a ha))
                (.inl (argFree_of_addrLower hal))) hB'
          · exact replayL_inv hs hD evs _ M' B B' C h
              (hI.fold hx0 ht ht' hfold fun a' ha' => by
                rw [hD, ha] at ha'; cases ha'; exact hS) hB'
          · exact replayL_inv hs hD evs _ M' B B' C h
              (hI.foldAddr hD hx0 ht ht' hfold fun a' ha' => by
                rw [hD, ha] at ha'; cases ha'; exact hS) hB'
          · exact replayL_inv hs hD evs _ M' B B' C h
              (hI.idxFold hx0 ht ht' hfold fun a' ha' => by
                rw [hD, ha] at ha'; cases ha'; exact hS) hB'
          · exact replayL_inv hs hD evs _ M' B B' C h
              (hI.scaleIdx hx0 ht ht' hsc fun a' ha' => by
                rw [hD, ha] at ha'; cases ha'; exact ⟨hS, hS3⟩) hB'
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
            hI.typed fun ρ _ _ n y hy => by
              rw [denL_put_fresh hsn hI.closed _ y hy]; exact Sem.Refines.refl _
          exact replayL_inv hs hD evs _ M' B B' _ h hI2
            (hB1.mono (g := id) (fun _ h => h) hI1.typed fun ρ _ _ n y _ => by
              rw [rename_den hx1 ht ht']; exact Sem.Refines.refl _)
        · -- a frame variable's address folded into a load or an `ADDconst` (`frameFold`)
          split at h
          · rename_i u hld
            obtain ⟨hI', hstep⟩ := hI.frameFold hD hld
            exact replayL_inv hs hD evs _ M' B B' C h hI'
              (hB.mono (g := id) (fun _ h => h) hI.typed hstep)
          · -- an `OffPtr` offset folded into a load (`ldOffFold`)
            split at h
            · rename_i u hld
              obtain ⟨hI', hstep⟩ := hI.ldOffFold hld
              exact replayL_inv hs hD evs _ M' B B' C h hI'
                (hB.mono (g := id) (fun _ h => h) hI.typed hstep)
            · cases h
  | .copyArg v i src :: evs, M, M', B, B', C, h, hI, hB => by
    unfold replayL at h
    split at h
    · cases h
    rename_i x hx
    split at h
    · have hc := copyStepL_inv (v := v) (i := i) (src := src) hI hB
      exact replayL_inv hs hD evs _ M' B B' C h hc.1 hc.2
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
        exact replayL_inv hs hD evs M M' _ B' C h hI (hB.control hI.closed hI.typed hst hi hrc)
      · cases h
    · cases h
  | .phielim .. :: _, M, M', B, B', C, h, _, _ => by simp [replayL] at h
  | .snap .. :: _, M, M', B, B', C, h, _, _ => by simp [replayL] at h
  | .blockRule b i nc defs :: evs, M, M', B, B', C, h, hI, hB => by
    unfold replayL at h
    split at h
    · cases h
    rename_i st hst
    split at h
    · -- a jump table: two fresh terms
      rename_i hjt
      split at h
      · cases h
      rename_i st' us hok
      have hjt' : st.kind = .JumpTable := by simpa using hjt
      obtain ⟨c, ma, sb, -, -, -, -, rfl, hmt, hst', hmaa, hsba, hne, hfa, hfs⟩ :=
        jumpOKL_facts hok
      simp only [List.foldl_cons, List.foldl_nil] at h
      have hI1 := hI.fresh (P := True) hfs hst' (fun _ a ha => by rw [hsba] at ha; simp at ha)
      have hfa' : (M.put sb.id sb).get? ma.id = none := by
        rw [get?_put]; simp [Ne.symm hne, hfa]
      have hI2 := hI1.fresh (P := True) hfa' hmt (fun _ a ha => by
        rw [hmaa] at ha
        simp only [List.mem_toArray, List.mem_singleton] at ha
        exact .inr ⟨trivial, ha⟩)
      exact replayL_inv hs hD evs _ M' _ B' _ h hI2
        (hB.jump hI.typed (fun _ h => .inl (.inl h))
          (fun _ n y hy => (denL_put_fresh hfa' hI1.closed n y (.inl hy)).trans
            (denL_put_fresh hfs hI.closed n y hy)) hst hjt' hok
          (fun u hu => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · exact .inl (.inr ⟨trivial, rfl⟩)
            · exact .inr ⟨trivial, rfl⟩))
    rename_i hjt
    split at h
    · cases h
    rename_i h2
    have h2' : (f.block? b).map (·.succs.size) = some 2 := by simpa using h2
    split at h
    · cases h
    rename_i br hbr
    split at h
    · cases h
    rename_i st' us hok
    have hsd : BlockRuleL.Sound br := (ofRuleSetL_blockSound hs hbr).resolve_right fun hk => by
      rw [← blockOKL_kind hok] at hk; simp [hk] at hjt
    rcases blockOKL_us hI.closed hok with rfl | ⟨u, rfl, hk, ht, hcl⟩
    · exact replayL_inv hs hD evs M M' _ B' C h hI
        (hB.block hI.closed hI.typed (fun _ h => h) (fun _ _ _ _ => rfl) hst h2' hsd hok
          (fun _ hu => by cases hu))
    · simp only [List.foldl_cons, List.foldl_nil] at h
      exact replayL_inv hs hD evs _ M' _ B' _ h (hI.fresh (P := ∀ c ∈ st.ctrls, C c) hk ht hcl)
        (hB.block hI.closed hI.typed (fun _ h => .inl h)
          (fun _ n y hy => denL_put_fresh hk hI.closed n y hy) hst h2' hsd hok
          (fun u' hu => by
            rw [List.mem_singleton] at hu; subst hu
            exact ⟨by rw [get?_put]; simp, fun hp => .inr ⟨hp, rfl⟩⟩))

end GoFV.Proof.Low.Val
