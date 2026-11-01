import GoFV.Proof.Pass.RewriteTermRule
import GoFV.Proof.Pass.RewriteTermNat
import GoFV.Proof.Pass.RewriteTermNonNeg

/-!
# One rule event refines the denotations (issue #113)

`rule_frame`: the puts of a validated rule event change only the IDs of its definitions (`v`
and fresh IDs, undefined before), each to a term node over matched values and the event's IDs.
`rule_step`: on a set `C` closed under arguments, every value's denotation after the event
refines the one before, with the fuel multiplied by `stepK r` (`Rule.SoundT` at the matched
instance, `evalPure_natShape`, `Comm` swaps, leaf independence of the checks).
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Rules (Pat Rule RNode RArg Result)
open GoFV.Proof.Rules (DV PEnv Oracle Path Pat.denT Pat.densT Pat.rawT sigmaT evalE resDenT
  nodeDenT toAuxIntD)

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
def argVal (tabs : Tables) (ev : GoFV.Rules.Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty)
    (nodes : List RNode) (f : Nat) : RArg → Val
  | .var x => (σ x).valOr (or.val (.var x))
  | .node j => nodeDenT tabs ev or σ topTy nodes f j

theorem nodeDen_succ (tabs : Tables) (ev : GoFV.Rules.Expr → DV) (or : Oracle) (σ : Nat → DV)
    (topTy : Ty) (nodes : List RNode) (f k : Nat) (n : RNode) (hk : nodes[k]? = some n) :
    nodeDenT tabs ev or σ topTy nodes (f + 1) k =
      (GoFV.Proof.Rules.opVal tabs n.op (tySel ev or topTy n) (aiSel ev or n) (axSel or n)
        (n.args.map (argVal tabs ev or σ topTy nodes f))).retype (tySel ev or topTy n) := by
  simp only [nodeDenT, hk]
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
def stepK (r : Rule) : Nat := Pat.sz r.pat + resLen r.result + 2

section Step

variable {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}

theorem CopyRes.ids {F : RuleFacts tabs M r v defs} (R : CopyRes tabs M r v defs F) :
    defIds defs = [v] := by
  rw [show defIds defs = defIds [R.u] from congrArg _ R.hdefs]; simp [defIds, R.hid]

theorem CopyRes.put {F : RuleFacts tabs M r v defs} (R : CopyRes tabs M r v defs F) :
    putAll M defs = M.put v R.u := by
  rw [show putAll M defs = putAll M [R.u] from congrArg _ R.hdefs]; simp [putAll, R.hid]

theorem BuildRes.usids {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F) :
    R.us.map (·.id) = R.top :: (R.us.map (·.id)).drop 1 := by
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

theorem BuildRes.top_nmem {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F) :
    R.top ∉ (R.us.map (·.id)).drop 1 := by
  rcases R.htop with h | h
  · rw [h]; exact R.hnv
  · exact h.2.2.1

theorem BuildRes.nodup {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F) :
    (R.us.map (·.id)).Nodup := by
  rw [R.usids]; exact List.nodup_cons.2 ⟨R.top_nmem, R.hnodup⟩

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
    (h0 : 0 < R.us.length) : R.us[0].id = R.top := by
  obtain ⟨u, l, hu⟩ : ∃ u l, R.us = u :: l := by
    cases h : R.us with
    | nil => simp [h] at h0
    | cons u l => exact ⟨u, l, rfl⟩
  have h1 := R.hhead
  simp only [hu, List.map_cons, List.head?_cons, Option.some.injEq] at h1
  simp only [hu, List.getElem_cons_zero, h1]

/-- An `@b` build leaves `v` its `Copy` of the fresh top. -/
theorem BuildRes.getV {F : RuleFacts tabs M r v defs} (R : BuildRes tabs M r v defs F)
    (hb : BlockTop tabs M v R.u0 R.us R.top) : (putAll M defs).get? v = some R.u0 := by
  have hv : v ∉ R.us.map (·.id) := by
    rw [R.usids]
    simp only [List.mem_cons, not_or]
    exact ⟨fun h => hb.1 h.symm, R.hnv⟩
  rw [R.put, get?_putAll_not _ _ _ hv, get?_put]; simp

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
        · rcases R.htop with h | h
          · exact .inl h
          · exact .inr h.2.1
        · exact .inr (R.hfresh y hy)
    · have hy' : y ∈ R.us.map (·.id) ∨ (y = v ∧ BlockTop tabs M v R.u0 R.us R.top) := by
        rcases List.mem_cons.1 hy with rfl | hy
        · rcases R.htop with h | h
          · left; rw [R.usids, h]; exact List.mem_cons_self
          · exact .inr ⟨rfl, h⟩
        · exact .inl hy
      rcases hy' with hy' | ⟨rfl, hb⟩
      rotate_left
      · refine ⟨R.u0, R.getV hb, by rw [hb.2.2.2.1]; exact termOp_copy, fun a ha => ?_⟩
        rw [hb.2.2.2.2.1] at ha
        simp only [List.mem_toArray, List.mem_singleton] at ha
        subst ha
        exact .inr (List.mem_cons_of_mem _ (by rw [R.usids]; exact List.mem_cons_self))
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

/-! ## The denotations -/

/-- The semantic instance: the leaves are `L` of the matched values. -/
def semEnv (tabs : Tables) (M : Defs) (I : Inst) (L : ID → Val) : PEnv :=
  { env tabs M I with leaf := fun p => L (I.at p) }

/-- `C` is defined and contains the arguments of its values. -/
def DefClosed (M : Defs) (C : ID → Prop) : Prop :=
  ∀ y, C y → ∃ m, M.get? y = some m ∧ ∀ a ∈ m.args, C a

theorem DefClosed.arg {M : Defs} {C : ID → Prop} (h : DefClosed M C) : ArgClosed M C := by
  intro w x hw hx a ha
  obtain ⟨m, hm, hargs⟩ := h w hw
  rw [hx] at hm; cases hm; exact hargs a ha

theorem refinesList_idx {α β : Type} {F : α → Val} {G : β → Val} :
    ∀ {l : List α} {m : List β}, l.length = m.length →
      (∀ j (h1 : j < l.length) (h2 : j < m.length), Sem.Refines (F l[j]) (G m[j])) →
      RefinesList (l.map F) (m.map G)
  | [], [], _, _ => .nil
  | a :: l, b :: m, hl, h => .cons (h 0 (by simp) (by simp))
      (refinesList_idx (by simpa using hl) fun j h1 h2 => h (j + 1) (by simpa using h1) (by simpa using h2))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

section Den

variable {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}

theorem RuleFacts.not_def (F : RuleFacts tabs M r v defs) {w : ID} {x : Value}
    (hw : M.get? w = some x) (hne : w ≠ v) : w ∉ defIds defs := fun h =>
  match F.frame.2.2.1 w h with
  | .inl h => hne h
  | .inr h => by rw [hw] at h; cases h

theorem RuleFacts.keep (F : RuleFacts tabs M r v defs) {w : ID} {x : Value}
    (hw : M.get? w = some x) (hne : w ≠ v) : (putAll M defs).get? w = some x := by
  rw [F.frame.1 w (F.not_def hw hne), hw]

theorem RuleFacts.keepAtom (F : RuleFacts tabs M r v defs) {w : ID} {x : Value}
    (hw : M.get? w = some x) (ha : termOp x.op = false) : (putAll M defs).get? w = some x := by
  refine F.keep hw fun h => ?_
  subst h; rw [F.hxv] at hw; cases hw; rw [F.hterm] at ha; cases ha

theorem RuleFacts.fields (F : RuleFacts tabs M r v defs) (L : ID → Val) :
    FieldsOK M F.I tabs (semEnv tabs M F.I L) := by
  intro p w x hm hx
  refine ⟨?_, ?_, ?_⟩ <;> simp [semEnv, env, F.at_eq hm, hx]

theorem RuleFacts.typed (F : RuleFacts tabs M r v defs) {ρ : ID → Val}
    (hT : Term.Typed M.get? tabs ρ) : Term.Typed (putAll M defs).get? tabs ρ := by
  intro a ha hsome
  by_cases hd : a ∈ defIds defs
  · obtain ⟨u, hu, ht, -⟩ := F.frame.2.2.2 a hd
    exact absurd ⟨u, hu, ht⟩ ha
  · have he := F.frame.1 a hd
    have hshape : shape (putAll M defs).get? tabs a = shape M.get? tabs a := by simp [shape, he]
    rw [hshape]
    exact hT a (fun ⟨u, hu, ht⟩ => ha ⟨u, by rw [he]; exact hu, ht⟩) (he ▸ hsome)

theorem RuleFacts.closed (F : RuleFacts tabs M r v defs) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (putAll M defs) (fun y => C y ∨ (C v ∧ y ∈ defIds defs)) := by
  have hfr := F.frame
  have hnew : ∀ y, C v → y ∈ defIds defs → ∃ m, (putAll M defs).get? y = some m ∧
      ∀ a ∈ m.args, C a ∨ (C v ∧ a ∈ defIds defs) := by
    intro y hv hy
    obtain ⟨u, hu, -, hargs⟩ := hfr.2.2.2 y hy
    refine ⟨u, hu, fun a ha => ?_⟩
    rcases hargs a ha with ⟨p, hp⟩ | ha'
    · exact .inl (F.hreach C hC.arg hv (p, a) hp)
    · exact .inr ⟨hv, ha'⟩
  intro y hy
  rcases hy with hy | ⟨hv, hy⟩
  · by_cases hd : y ∈ defIds defs
    · obtain ⟨m, hm, -⟩ := hC y hy
      rcases hfr.2.2.1 y hd with rfl | h
      · exact hnew _ hy hd
      · rw [hm] at h; cases h
    · obtain ⟨m, hm, hargs⟩ := hC y hy
      exact ⟨m, by rw [hfr.1 y hd, hm], fun a ha => .inl (hargs a ha)⟩
  · exact hnew y hv hy

theorem RuleFacts.top_ty (F : RuleFacts tabs M r v defs) (L : ID → Val) :
    (semEnv tabs M F.I L).ty [] = tabs.ty F.xv.type := by
  simp only [semEnv, env, F.at_top, F.hxv, Option.map_some, Option.getD_some]

/-- The validator's `frameNodeOK` gives `Rule.SoundT`'s frame premise (`FrameOK`) on the semantic
instance (same aux fields as the static one). -/
theorem RuleFacts.frameT (F : RuleFacts tabs M r v defs) (L : ID → Val)
    {ev' : GoFV.Rules.Expr → DV} (hev : ∀ x, (stEv tabs M r defs F.I x).erase = (ev' x).erase) :
    GoFV.Proof.Rules.FrameOK tabs (semEnv tabs M F.I L) ev' (stOr tabs r defs) r := by
  have hcf := F.hcf
  simp only [condFrameOK, Bool.and_eq_true] at hcf
  refine ⟨fun n hn => ?_, fun x hx => ?_, fun xy hxy => ?_, fun x hx => ?_, fun pq hpq => ?_⟩
  rotate_left
  · have h := List.all_eq_true.1 hcf.1.1.1 x hx
    simp only [strOf] at h
    cases hp : GoFV.Proof.Rules.Pat.auxPos x [] r.pat with
    | none => simp [hp] at h
    | some p =>
      simp only [hp, Option.bind_some] at h
      cases hs : GoFV.Proof.Rules.strAux? tabs ((env tabs M F.I).aux p) with
      | none => simp [hs] at h
      | some sd =>
        obtain ⟨s, d⟩ := sd
        simp only [hs, beq_iff_eq] at h
        exact ⟨p, s, d, rfl, hs, h⟩
  · have h := List.all_eq_true.1 hcf.1.1.2 xy hxy
    revert h
    split
    · rename_i p q hp hq
      intro h
      exact ⟨p, q, hp, hq, by simp only [semEnv, beq_iff_eq.1 h]⟩
    · intro h; cases h
  · have h := List.all_eq_true.1 hcf.1.2 x hx
    revert h
    split
    · rename_i f n hd
      intro h
      refine ⟨f, ?_⟩
      rcases DV.erase_eq_cases (hev (.var x)) with h' | ⟨v, v', p, h', -⟩
      · rw [← h', hd, beq_iff_eq.1 h]
      · rw [hd] at h'; cases h'
    · intro h; cases h
  · obtain ⟨p, q⟩ := pq
    have h := List.all_eq_true.1 hcf.2 (p, q) hpq
    simp only [semEnv, beq_iff_eq.1 h]
  rcases F.result with hR | hR
  · obtain ⟨R⟩ := hR
    rw [R.hres] at hn; simp [GoFV.Rules.Result.nodes] at hn
  · obtain ⟨R⟩ := hR
    rw [R.hres] at hn
    simp only [GoFV.Rules.Result.nodes] at hn
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hn
    have hk' : k < R.us.length := R.hlen ▸ hk
    have hmem : (R.nodes[k], R.us[k]) ∈ stNodes r defs := by
      simp only [stNodes, R.hres, R.hdefs]
      rw [List.mem_iff_getElem]
      exact ⟨k, by simp only [List.length_zip]; omega, by simp⟩
    have hf := F.hframe _ hmem
    obtain ⟨-, -, -, hai, hax, -, -⟩ := nodeOK_facts (R.hnode k hk hk')
    simp only [frameNodeOK, Bool.and_eq_true] at hf
    obtain ⟨⟨⟨hf1, hf2⟩, hf3⟩, hf4⟩ := hf
    refine ⟨fun xe x hxe hx => ?_, fun ae x hae hx => ?_, fun xe x hxe hx => ?_,
      fun ae b hae hb => ?_⟩
    · rw [hxe] at hf1
      simp only [Option.bind_some, hx, strOf] at hf1
      cases hp : GoFV.Proof.Rules.Pat.auxPos x [] r.pat with
      | none => simp [hp] at hf1
      | some p =>
        simp only [hp, Option.bind_some] at hf1
        cases hs : GoFV.Proof.Rules.strAux? tabs ((env tabs M F.I).aux p) with
        | none => simp [hs] at hf1
        | some sd =>
          obtain ⟨s, d⟩ := sd
          simp only [hs, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hf1
          refine ⟨p, s, d, rfl, hs, hf1.1, ?_⟩
          rw [← hf1.2, hax, axSel, hxe]
    · rw [hae] at hf2
      simp only [Option.bind_some, hx, strOf] at hf2
      cases hp : GoFV.Proof.Rules.Pat.auxPos x [] r.pat with
      | none => simp [hp] at hf2
      | some p =>
        simp only [hp, Option.bind_some] at hf2
        cases hs : GoFV.Proof.Rules.strAux? tabs ((env tabs M F.I).aux p) with
        | none => simp [hs] at hf2
        | some sd =>
          obtain ⟨s, d⟩ := sd
          simp only [hs, beq_iff_eq] at hf2
          refine ⟨p, s, d, rfl, hs, ?_⟩
          rw [← hf2, hai, aiSel_eq hev, aiSel, hae]
    · rw [hxe] at hf3
      simp only [Option.bind_some, hx] at hf3
      cases hp : GoFV.Proof.Rules.Pat.auxPos x [] r.pat with
      | none => simp [hp] at hf3
      | some p =>
        simp only [hp, beq_iff_eq] at hf3
        refine ⟨p, rfl, ?_⟩
        show _ = (env tabs M F.I).aux p
        rw [← hf3, hax, axSel, hxe]
    · rw [hae] at hf4
      simp only [Option.bind_some, hb] at hf4
      revert hf4
      cases hd : stEv tabs M r defs F.I b with
      | int i =>
        intro h
        refine ⟨i, ?_, of_decide_eq_true h⟩
        rcases DV.erase_eq_cases (hev b) with h' | ⟨v, v', p, h', -⟩
        · rw [← h', hd]
        · rw [hd] at h'; cases h'
      | _ => intro h; cases h

/-- The validator's `nonNegOKD` gives `Rule.SoundT`'s premise `Pat.nonNegOK` on the semantic
instance (`nonNegD_den`). -/
theorem nonNegOK_of {tabs : Tables} {D : ID → Option Value} {M : Defs} {I : Inst} {pat : Pat}
    {cond : Option GoFV.Rules.Expr} {ρ : ID → Val} {B : Nat}
    (hT : Term.Typed D tabs ρ) (h : nonNegOKD tabs D I pat cond = true) :
    GoFV.Proof.Rules.Pat.nonNegOK (semEnv tabs M I (den D tabs ρ B)) pat cond = true := by
  cases cond with
  | none => rfl
  | some c =>
    simp only [nonNegOKD, GoFV.Proof.Rules.Pat.nonNegOK, List.all_eq_true] at h ⊢
    intro x hx
    have hx' := h x hx
    revert hx'
    cases GoFV.Proof.Rules.Pat.leafPos x [] pat with
    | none => intro _; rfl
    | some p => exact nonNegD_den tabs D ρ hT _ B _

/-- **The matched value**: its denotation before the event is refined by the one after. -/
theorem RuleFacts.top (hs : GoFV.Proof.Rules.Rule.SoundT r)
    (F : RuleFacts tabs M r v defs) {C : ID → Prop} (hC : ArgClosed M C) (hv : C v)
    {ρ : ID → Val} (hT : Term.Typed (putAll M defs).get? tabs ρ) {n B : Nat}
    (hIH : ∀ y, C y → Sem.Refines (den M.get? tabs ρ n y) (den (putAll M defs).get? tabs ρ B y)) :
    Sem.Refines (den M.get? tabs ρ (n + 1) v) (den (putAll M defs).get? tabs ρ (B + stepK r) v) := by
  have hIC : ∀ p w, (p, w) ∈ F.I → C w := fun p w h => F.hreach C hC hv (p, w) h
  have hσ : ∀ x, (stσ tabs M r F.I x).erase =
      (sigmaT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) r.pat x).erase :=
    sigma_erase (e := env tabs M F.I)
      (e' := semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) rfl rfl r.pat
  have hev : ∀ x, (stEv tabs M r defs F.I x).erase =
      (evalE (stVtys r) (sigmaT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) r.pat)
        (stOr tabs r defs) (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B))
        (Pat.denT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) [] r.pat) x).erase :=
    evalE_erase (e := env tabs M F.I)
      (e' := semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) _ _ rfl rfl hσ _ _
  have hF := F.fields (den (putAll M defs).get? tabs ρ B)
  have hTop := F.top_ty (den (putAll M defs).get? tabs ρ B)
  have hdefw : ∀ p w x, (p, w) ∈ F.I → p ≠ [] → M.get? w = some x →
      (putAll M defs).get? w = some x := fun p w x hm hp hx => F.keep hx (F.ne_v hm hp)
  -- the hypotheses of `Rule.SoundT`
  have hbt : GoFV.Proof.Rules.Oracle.BoolTyped (stOr tabs r defs) := by
    intro x hx; exact ⟨true, by simp [stOr, oracle, hx]⟩
  have hwf := wf_of (e := env tabs M F.I) (e' := semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) rfl [] r.pat F.hwf
  have hcons := cons_of (pat := r.pat) (I := F.I) (e := env tabs M F.I) (e' := semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B))
    rfl rfl hev hσ (fun x w p' h hn => sigma_leaf h hn)
    (fun p p' h => by simp only [semEnv, h]) F.hS [] r.pat (fun _ h => h) F.hcons
  have hcond := cond_of hev F.hcond
  have htyped : GoFV.Proof.Rules.Pat.typed (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B))
      [] r.pat :=
    typed_of (fun p => rfl) (fun p w x hm hp hx => by
        show (den _ tabs ρ B (F.I.at p)).hasTy _ = true
        rw [F.at_eq hm]
        exact den_hasTy hT B (hdefw p w x hm hp hx))
      F.hnodup r.pat [] v F.hmatch (.inr (by rw [F.hpat]; rfl)) F.hleaves
  have hargs : GoFV.Proof.Rules.Pat.argsOK
      (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)).ty [] r.pat = true := F.hargs
  -- lower bound, before the top's `retype`
  have hlow0 : Sem.Refines (den M.get? tabs ρ (n + 1) v)
      ((Pat.rawT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) r.pat).retype
        ((semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)).ty [])) := by
    have h1 := den_le_patDen (n := n) hF (fun p w hm k hk => by
        show Sem.Refines _ (den _ tabs ρ B (F.I.at p))
        rw [F.at_eq hm]
        exact Sem.Refines.trans (den_fuel_mono _ _ _ k n w hk) (hIH w (hIC p w hm)))
      r.pat [] v (n + 1) F.hmatch (Nat.le_refl _) (.inr (by rw [F.hpat]; rfl))
    rw [F.hpat] at h1 ⊢
    simp only [Pat.denT, Pat.rawT] at h1 ⊢
    exact h1
  have hraw0 : (Pat.rawT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) r.pat).hasTy
      ((semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)).ty []) = true ∨
      (Pat.rawT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) r.pat).retype
        ((semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)).ty []) = .poison := by
    have hn : (topAll F.o (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) ||
        makeTop F.o ((semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)).ty [])) = true :=
      F.hnat
    have ht := htyped
    have ha := hargs
    rw [F.hpat] at ht ha ⊢
    rcases Bool.or_eq_true_iff.1 hn with hn | hn
    · exact .inl (raw_topAll hn ht ha)
    · exact raw_makeTop hn ht ha
  -- a `makeTop` whose raw value retypes to `poison`: the matched value is `poison`
  by_cases hpois : (Pat.rawT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B))
      r.pat).retype ((semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)).ty []) = .poison
  · rw [hpois] at hlow0
    generalize den M.get? tabs ρ (n + 1) v = a at hlow0 ⊢
    cases hlow0
    exact .poison _
  have hraw := hraw0.resolve_right hpois
  have hframe := F.frameT (den (putAll M defs).get? tabs ρ B) hev
  have hsound := hs.2 tabs _ _ hbt hframe hwf hcons hcond hraw htyped hargs (nonNegOK_of hT F.hnn)
  have hlow : Sem.Refines (den M.get? tabs ρ (n + 1) v)
      (Pat.rawT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) r.pat) := by
    rwa [GoFV.Proof.retype_of_hasTy hraw] at hlow0
  -- values bound on the semantic side
  have hleafU : ∀ p w, (p, w) ∈ F.I → Sem.Refines
      ((semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)).leaf p)
      (den (putAll M defs).get? tabs ρ B w) := fun p w hm => by
    show Sem.Refines (den _ tabs ρ B (F.I.at p)) _
    rw [F.at_eq hm]; exact Sem.Refines.refl _
  obtain ⟨S, hS⟩ : ∃ S, S = Pat.sz r.pat := ⟨_, rfl⟩
  have hσ2 : ∀ x, Good (fun w p => p ≠ [] ∧
      Sem.Refines w (den (putAll M defs).get? tabs ρ (B + S) (F.I.at p)))
      (sigmaT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) r.pat x) := by
    intro x
    have hm := F.hmatch
    have hS' : Pat.sz r.pat ≤ S := by omega
    rw [F.hpat] at hm hS' ⊢
    exact sigma_good (P := fun w p => p ≠ [] ∧
        Sem.Refines w (den (putAll M defs).get? tabs ρ (B + S) (F.I.at p))) (S := S)
      (fun p w hm' hp => ⟨hp, by
        show Sem.Refines (den _ tabs ρ B (F.I.at p)) _
        exact den_fuel_mono _ _ _ _ _ _ (by omega)⟩)
      (fun q p w hm' hp hsz => ⟨hp, by
        rw [F.at_eq hm'.mem]
        exact patDen_le_den hF hdefw hleafU q p w _ hm' hp (by omega)⟩) hm hS' x
  have hev2 : ∀ x, Good (fun w p => p ≠ [] →
      Sem.Refines w (den (putAll M defs).get? tabs ρ (B + S) (F.I.at p)))
      (evalE (stVtys r) (sigmaT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) r.pat)
        (stOr tabs r defs) (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B))
        (Pat.denT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) [] r.pat) x) :=
    evalE_good _ _ _ (fun x => good_mono (fun w p h _ => h.2) (hσ2 x)) (fun h => absurd rfl h)
      (fun x => good_of_flat (oracle_flat _ _ _ x))
  rcases F.result with hR | hR
  · -- copy
    obtain ⟨R⟩ := hR
    have hpos := R.hpos
    obtain ⟨w0, hst⟩ : ∃ w0, stEv tabs M r defs F.I R.ce = .val w0 (some R.p) := by
      revert hpos; cases stEv tabs M r defs F.I R.ce <;> simp [DV.pos?]
    have h' := hev R.ce
    rw [hst] at h'
    have hp : R.p ≠ [] := fun h => R.hne (by rw [h, F.at_top])
    have hcases : ∀ d : DV, (DV.val w0 (some R.p)).erase = d.erase →
        Good (fun w p => p ≠ [] →
          Sem.Refines w (den (putAll M defs).get? tabs ρ (B + S) (F.I.at p))) d →
        Sem.Refines (d.valOr ((stOr tabs r defs).val R.ce))
          (den (putAll M defs).get? tabs ρ (B + S) (F.I.at R.p)) := by
      intro d hd hg
      rcases DV.erase_eq_cases hd with rfl | ⟨v1, v2, p1, h1, rfl⟩
      · exact hg.1 w0 R.p rfl hp
      · cases h1; exact hg.1 v2 R.p rfl hp
    have hup := hcases _ h' (hev2 R.ce)
    rw [R.hres] at hsound
    obtain ⟨y, hy, hyt⟩ : ∃ y, M.get? (F.I.at R.p) = some y ∧ y.type = R.u.type := by
      have := R.hty
      cases h : M.get? (F.I.at R.p) with
      | none => rw [h] at this; cases this
      | some y => rw [h] at this; exact ⟨y, rfl, by simpa using this⟩
    have hkeep := F.keep hy R.hne
    have hdv : (putAll M defs).get? v = some R.u := by rw [R.put, get?_put]; simp
    have hK : B + stepK r = (B + S + 1) + 1 := by simp [stepK, resLen, R.hres, hS]; omega
    rw [hK, den_succ_term hdv (by rw [R.hop]; exact termOp_copy), R.hargs, R.hop]
    show Sem.Refines _ ((den _ tabs ρ (B + S + 1) (F.I.at R.p)).retype (tabs.ty R.u.type))
    rw [← hyt, ← shape_of (tabs := tabs) hkeep, den_retype hT _ _ (by rw [hkeep]; rfl)]
    exact hlow.trans (hsound.trans (hup.trans (den_fuel_mono _ _ _ _ _ _ (by omega))))
  · -- build
    obtain ⟨R⟩ := hR
    rw [R.hres] at hsound
    have hTy : (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)).ty [] =
        tabs.ty F.xv.type := hTop
    have key : ∀ f k (hk : k < R.nodes.length),
        Sem.Refines (nodeDenT tabs (evalE (stVtys r)
            (sigmaT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) r.pat)
            (stOr tabs r defs) (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B))
            (Pat.denT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) [] r.pat))
          (stOr tabs r defs) (sigmaT tabs (semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)) r.pat)
          ((semEnv tabs M F.I (den (putAll M defs).get? tabs ρ B)).ty []) R.nodes f k)
        (den (putAll M defs).get? tabs ρ (B + S + f) (R.us[k]'(R.hlen ▸ hk)).id) := by
      intro f
      induction f with
      | zero => intro k hk; exact .poison _
      | succ f ih =>
        intro k hk
        have hk' : k < R.us.length := R.hlen ▸ hk
        obtain ⟨hop, ht, hty, hai, hax, hsz, hargs⟩ := nodeOK_facts (R.hnode k hk hk')
        rw [nodeDen_succ _ _ _ _ _ _ f k R.nodes[k] (List.getElem?_eq_getElem hk)]
        rw [show B + S + (f + 1) = (B + S + f) + 1 by omega,
          den_succ_term (R.get k hk') (hop ▸ ht)]
        rw [← hTy] at hty
        rw [← tySel_eq hev, ← aiSel_eq hev, ← hty, ← hai, ← hax, hop]
        apply retype_mono
        apply GoFV.Proof.Rules.opVal_mono
        refine refinesList_idx (by simp [hsz]) fun j h1 h2 => ?_
        have harg := hargs j h1 (by simpa using h2)
        simp only [Array.getElem_toList]
        cases hn : R.nodes[k].args[j] with
        | var x =>
          rw [hn] at harg
          simp only [argID, Option.map_eq_some_iff] at harg
          obtain ⟨p, hp, hpa⟩ := harg
          simp only [argVal]
          obtain ⟨w0, hw0⟩ : ∃ w0, stσ tabs M r F.I x = .val w0 (some p) := by
            revert hp; cases stσ tabs M r F.I x <;> simp [DV.pos?]
          have hx := hσ x
          rw [hw0] at hx
          rcases DV.erase_eq_cases hx with h2 | ⟨v1, v2, p1, h1, h2⟩
          · rw [← h2]
            have := (hσ2 x).1 w0 p h2.symm
            rw [← hpa]
            exact this.2.trans (den_fuel_mono _ _ _ _ _ _ (by omega))
          · cases h1
            rw [h2]
            have := (hσ2 x).1 v2 p h2
            rw [← hpa]
            exact this.2.trans (den_fuel_mono _ _ _ _ _ _ (by omega))
        | node j' =>
          rw [hn] at harg
          simp only [argID] at harg
          simp only [argVal]
          obtain ⟨hj', hj'e⟩ := List.getElem?_eq_some_iff.1 harg
          simp only [List.length_map] at hj'
          rw [← hj'e]
          simp only [List.getElem_map]
          exact ih j' (R.hlen ▸ hj')
    have h0 := key R.nodes.length 0 R.len
    have hid := R.id0 (R.hlen ▸ R.len)
    simp only [hid] at h0
    rcases R.htop with htv | hb
    · rw [htv] at h0
      refine hlow.trans (hsound.trans (h0.trans (den_fuel_mono _ _ _ _ _ _ ?_)))
      simp [stepK, resLen, R.hres, hS]; omega
    · -- `@b`: `v` is a compatible copy of the fresh top
      have hdv := R.getV hb
      obtain ⟨-, -, -, hop, hargs, u, hu, hc⟩ := hb
      rw [List.head?_eq_getElem?] at hu
      obtain ⟨hl0, hu0⟩ := List.getElem?_eq_some_iff.1 hu
      have hut : (putAll M defs).get? R.u0.args[0]! = some u := by
        have := R.get 0 hl0
        rw [R.id0 hl0, hu0] at this
        rw [hargs]; exact this
      have hK : B + stepK r = (B + S + R.nodes.length + 1) + 1 := by
        simp [stepK, resLen, R.hres, hS]; omega
      rw [hK, den_copy hT hdv hop (by rw [hargs]; rfl) hut hc]
      have harg0 : R.u0.args[0]! = R.top := by rw [hargs]; rfl
      rw [harg0]
      exact hlow.trans (hsound.trans (h0.trans (den_fuel_mono _ _ _ _ _ _ (by omega))))

/-- **One rule event**: on a set closed under arguments, the denotations after the event refine
those before, with the fuel multiplied by `stepK r`. -/
theorem RuleFacts.step (hs : GoFV.Proof.Rules.Rule.SoundT r)
    (F : RuleFacts tabs M r v defs) {C : ID → Prop} (hC : DefClosed M C) {ρ : ID → Val}
    (hT : Term.Typed M.get? tabs ρ) :
    ∀ n y, C y → Sem.Refines (den M.get? tabs ρ n y) (den (putAll M defs).get? tabs ρ (n * stepK r) y) := by
  have hT' := F.typed hT
  intro n
  induction n with
  | zero => intro y _; exact .poison _
  | succ n ih =>
    intro y hy
    by_cases hyv : y = v
    · subst hyv
      rw [Nat.succ_mul]
      exact F.top hs hC.arg hy hT' ih
    · obtain ⟨m, hm, hargs⟩ := hC y hy
      have hkeep := F.keep hm hyv
      have hK : (n + 1) * stepK r = (n * stepK r + (stepK r - 1)) + 1 := by
        rw [Nat.succ_mul]; simp only [stepK]; omega
      rw [hK]
      by_cases ht : termOp m.op = true
      · rw [den_succ_term hm ht, den_succ_term hkeep ht]
        exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_map fun a ha =>
          (ih a (hargs a (Array.mem_toList_iff.1 ha))).trans
            (den_fuel_mono _ _ _ _ _ _ (by omega))))
      · have h1 : ¬ IsTerm M.get? y := fun ⟨u, hu, hu'⟩ => by
          rw [hm] at hu; cases hu; exact ht hu'
        have h2 : ¬ IsTerm (putAll M defs).get? y := fun ⟨u, hu, hu'⟩ => by
          rw [hkeep] at hu; cases hu; exact ht hu'
        rw [den_succ_atom h1, den_succ_atom h2]; exact Sem.Refines.refl _

end Den


end GoFV.Proof.Pass.Rewrite
