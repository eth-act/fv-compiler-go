import GoFV.Proof.Pass.RewriteTermRule
import GoFV.Proof.Pass.RewriteTermNat

/-!
# One rule event refines the denotations (issue #113)

`rule_frame`: the puts of a validated rule event change only the IDs of its definitions (`v`
and fresh IDs, undefined before), each to a term node over matched values and the event's IDs.
`rule_step`: on a set `C` closed under arguments, every value's denotation after the event
refines the one before, with the fuel multiplied by `stepK r` (`Rule.Sound` at the matched
instance, `evalPure_natShape`, `Comm` swaps, leaf independence of the checks).
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Rules (Pat Rule RNode RArg Result)
open GoFV.Proof.Rules (DV PEnv Oracle Path Pat.den Pat.dens Pat.raw sigma evalE resDen nodeDen
  toAuxIntD)

/-! ## Result nodes -/

/-- The type shape of a result node. -/
def tySel (ev : GoFV.Rules.Expr → DV) (or : Oracle) (topTy : Ty) (n : RNode) : Ty :=
  match n.ty with
  | some te => match ev te with
    | .ty t => t
    | _ => or.ty te
  | none => topTy

/-- The auxint of a result node. -/
def aiSel (ev : GoFV.Rules.Expr → DV) (or : Oracle) (n : RNode) : Int64 :=
  match n.auxInt with
  | some ae => (toAuxIntD n.op.auxType (ev ae)).getD (or.auxInt ae)
  | none => 0

/-- The aux of a result node. -/
def axSel (or : Oracle) (n : RNode) : Option AuxRef :=
  match n.aux with
  | some xe => or.aux xe
  | none => none

/-- The value of a result argument. -/
def argVal (ev : GoFV.Rules.Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty)
    (nodes : List RNode) (f : Nat) : RArg → Val
  | .var x => (σ x).valOr (or.val (.var x))
  | .node j => nodeDen ev or σ topTy nodes f j

theorem nodeDen_succ (ev : GoFV.Rules.Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty)
    (nodes : List RNode) (f k : Nat) (n : RNode) (hk : nodes[k]? = some n) :
    nodeDen ev or σ topTy nodes (f + 1) k =
      (evalPure n.op (tySel ev or topTy n) (aiSel ev or n) (axSel or n)
        (n.args.map (argVal ev or σ topTy nodes f))).retype (tySel ev or topTy n) := by
  simp only [nodeDen, hk]
  rfl

theorem nodeOK_facts {tabs : Tables} {ev : GoFV.Rules.Expr → DV} {or : Oracle} {σ : Nat → DV}
    {I : Inst} {ids : List ID} {topTy : Ty} {n : RNode} {u : Value}
    (h : nodeOK tabs ev or σ I ids topTy n u = true) :
    u.op = n.op ∧ termOp n.op = true ∧ tabs.ty u.type = tySel ev or topTy n ∧
      u.auxInt = aiSel ev or n ∧ u.aux = axSel or n ∧ u.args.size = n.args.length ∧
      ∀ j (h1 : j < n.args.length) (h2 : j < u.args.size),
        argID σ I ids n.args[j] = some u.args[j] := by
  unfold nodeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hop, ht⟩, hty⟩, hai⟩, hax⟩, hsz⟩, hargs⟩ := h
  refine ⟨hop, ht, tyEq_sound hty, hai, hax, hsz, fun j h1 h2 => ?_⟩
  have := zip_all_get (f := fun x => match x with | (a, w) => argID σ I ids a == some w) hargs
    (by simp [hsz]) j h1 (by simpa using h2)
  simpa using this

theorem tySel_eq {ev ev' : GoFV.Rules.Expr → DV} (hev : ∀ x, (ev x).erase = (ev' x).erase)
    (or : Oracle) (topTy : Ty) (n : RNode) : tySel ev or topTy n = tySel ev' or topTy n := by
  unfold tySel
  split
  · rename_i te _
    rcases DV.erase_eq_cases (hev te) with h | ⟨v, v', p, h, h'⟩
    · rw [h]
    · rw [h, h']
  · rfl

theorem aiSel_eq {ev ev' : GoFV.Rules.Expr → DV} (hev : ∀ x, (ev x).erase = (ev' x).erase)
    (or : Oracle) (n : RNode) : aiSel ev or n = aiSel ev' or n := by
  unfold aiSel
  split
  · rename_i ae _
    rcases DV.erase_eq_cases (hev ae) with h | ⟨v, v', p, h, h'⟩
    · rw [h]
    · rw [h, h']; rfl
  · rfl

theorem good_mono {P Q : Val → Path → Prop} (h : ∀ w p, P w p → Q w p) {d : DV} (hd : Good P d) :
    Good Q d := ⟨fun w p hw => h w p (hd.1 w p hw), hd.2⟩

/-! ## The frame of a rule event -/

/-- The IDs a rule event defines. -/
def defIds (defs : List Value) : List ID := defs.map (·.id)

/-- The number of nodes a result builds. -/
def resLen : Result → Nat
  | .build ns => ns.length
  | _ => 0

/-- The fuel factor of a rule step. -/
def stepK (r : Rule) : Nat := Pat.sz r.pat + resLen r.result + 1

section Step

variable {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}

theorem CopyRes.ids {F : RuleFacts tabs M r v defs} (R : CopyRes tabs M r v defs F) :
    defIds defs = [v] := by
  rw [show defIds defs = defIds [R.u] from congrArg _ R.hdefs]; simp [defIds, R.hid]

theorem CopyRes.put {F : RuleFacts tabs M r v defs} (R : CopyRes tabs M r v defs F) :
    putAll M defs = M.put v R.u := by
  rw [show putAll M defs = putAll M [R.u] from congrArg _ R.hdefs]; simp [putAll, R.hid]

theorem BuildRes.usids {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F) :
    R.us.map (·.id) = v :: (R.us.map (·.id)).drop 1 := by
  have h := R.hhead
  cases hu : R.us.map (·.id) with
  | nil => rw [hu] at h; cases h
  | cons a l => rw [hu] at h; simp only [List.head?_cons, Option.some.injEq] at h; subst h; rfl

theorem BuildRes.ids {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F) :
    defIds defs = v :: R.us.map (·.id) := by
  rw [show defIds defs = defIds (R.u0 :: R.us) from congrArg _ R.hdefs]; simp [defIds, R.hid0]

theorem BuildRes.put {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F) :
    putAll M defs = putAll (M.put v R.u0) R.us := by
  rw [show putAll M defs = putAll M (R.u0 :: R.us) from congrArg _ R.hdefs]
  simp [putAll, R.hid0]

theorem BuildRes.nodup {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F) :
    (R.us.map (·.id)).Nodup := by
  rw [R.usids]; exact List.nodup_cons.2 ⟨R.hnv, R.hnodup⟩

theorem BuildRes.len {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F) :
    0 < R.nodes.length := by
  have := R.usids; rw [← R.hlen]
  cases hu : R.us with
  | nil => rw [hu] at this; cases this
  | cons _ _ => simp

theorem BuildRes.get {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F) (k : Nat)
    (hk : k < R.us.length) : (putAll M defs).get? R.us[k].id = some R.us[k] := by
  rw [R.put]; exact get?_putAll_mem _ _ _ R.nodup (List.getElem_mem hk)

theorem BuildRes.id0 {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F)
    (h0 : 0 < R.us.length) : R.us[0].id = v := by
  obtain ⟨u, l, hu⟩ : ∃ u l, R.us = u :: l := by
    cases h : R.us with
    | nil => simp [h] at h0
    | cons u l => exact ⟨u, l, rfl⟩
  have h1 := R.hhead
  simp only [hu, List.map_cons, List.head?_cons, Option.some.injEq] at h1
  simp only [hu, List.getElem_cons_zero, h1]

theorem RuleFacts.frame (F : RuleFacts tabs M r v defs) :
    (∀ y, y ∉ defIds defs → (putAll M defs).get? y = M.get? y) ∧
    v ∈ defIds defs ∧
    (∀ y ∈ defIds defs, y = v ∨ M.get? y = none) ∧
    (∀ y ∈ defIds defs, ∃ u, (putAll M defs).get? y = some u ∧ termOp u.op = true ∧
      ∀ a ∈ u.args, (∃ p, (p, a) ∈ F.I) ∨ a ∈ defIds defs) := by
  refine ⟨fun y hy => get?_putAll_not defs M y hy, ?_⟩
  rcases F.result with hR | hR
  · obtain ⟨R⟩ := hR
    rw [R.ids, R.put]
    refine ⟨List.mem_singleton_self _, fun y hy => .inl (List.mem_singleton.1 hy), fun y hy => ?_⟩
    rw [List.mem_singleton.1 hy]
    refine ⟨R.u, by rw [get?_put]; simp, by rw [R.hop]; exact termOp_copy, fun a ha => ?_⟩
    rw [R.hargs] at ha
    simp only [List.mem_toArray, List.mem_singleton] at ha
    subst ha
    exact .inl ⟨R.p, F.pos_mem (F.stEv_good R.ce) R.hpos⟩
  · obtain ⟨R⟩ := hR
    rw [R.ids]
    refine ⟨List.mem_cons_self, fun y hy => ?_, fun y hy => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact .inl rfl
      · rw [R.usids] at hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact .inl rfl
        · exact .inr (R.hfresh y hy)
    · have hy' : y ∈ R.us.map (·.id) := by
        rcases List.mem_cons.1 hy with rfl | hy
        · rw [R.usids]; exact List.mem_cons_self
        · exact hy
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy'
      simp only [List.length_map] at hk
      simp only [List.getElem_map]
      refine ⟨R.us[k], R.get k hk, ?_⟩
      obtain ⟨hop, ht, -, -, -, hsz, hargs⟩ := nodeOK_facts (R.hnode k (R.hlen ▸ hk) hk)
      refine ⟨hop ▸ ht, fun a ha => ?_⟩
      obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem ha
      have harg := hargs j (hsz ▸ hj) hj
      cases hn : (R.nodes[k]'(R.hlen ▸ hk)).args[j]'(hsz ▸ hj) with
      | var x =>
        rw [hn] at harg
        simp only [argID, Option.map_eq_some_iff] at harg
        obtain ⟨p, hp, hpa⟩ := harg
        rw [← hpa]
        exact .inl ⟨p, F.pos_mem (F.stσ_good x) hp⟩
      | node j' =>
        rw [hn] at harg
        simp only [argID] at harg
        exact .inr (List.mem_cons_of_mem _ (List.mem_of_getElem? harg))

end Step

end GoFV.Proof.Pass.Rewrite
