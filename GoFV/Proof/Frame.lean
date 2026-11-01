import GoFV.Proof.Block
import GoFV.Proof.Sched

/-!
# Frames: what one block entry changes

* `evalValue_regs`: a value's evaluation reads the registers of its arguments only (the other
  frame fields are the activation's inputs, which no step changes).
* `evalAll_spec`: evaluating a dependency order writes exactly its values, each to its
  evaluation in the final frame.
* `enterBlock_spec`: entering a block sets its `Phi`s from the incoming edge's arguments in
  the old frame, then runs its schedule; nothing outside the block's values changes.
* `schedNodes_*`, `sched_of_block`: the schedule of a block of a well-formed function is a
  dependency order of its non-`Phi` values with their own arguments.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

instance : LawfulMonad Res := LawfulMonad.mk'
  (id_map := by intro α x; cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := by intro α β γ x f g; cases x <;> rfl)

theorem mapM_loop_congr {α β : Type} {m : Type → Type} [Monad m] {f g : α → m β} :
    ∀ (l : List α) (acc : List β), (∀ a ∈ l, f a = g a) →
      List.mapM.loop f l acc = List.mapM.loop g l acc
  | [], _, _ => rfl
  | a :: l, acc, h => by
    simp only [List.mapM.loop, h a List.mem_cons_self]
    congr 1; funext b
    exact mapM_loop_congr l _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem mapM_congr' {α β : Type} {m : Type → Type} [Monad m] {f g : α → m β}
    (l : List α) (h : ∀ a ∈ l, f a = g a) : l.mapM f = l.mapM g :=
  mapM_loop_congr l [] h

theorem argVal_regs (ctx : Ctx) (fr : Frame) (r : Array (Option Val)) :
    argVal ctx { fr with regs := r } = argVal ctx fr := rfl

/-- A value's evaluation reads the registers of its arguments only. -/
theorem evalValue_regs {env : Env} {ctx : Ctx} {fr : Frame} {r r' : Array (Option Val)}
    {v : Value} (h : ∀ a ∈ v.args, r[a]? = r'[a]?) :
    evalValue env ctx { fr with regs := r } v = evalValue env ctx { fr with regs := r' } v := by
  unfold evalValue
  simp only [argVal_regs]
  congr 1
  exact mapM_congr' _ fun a ha => by rw [h a (Array.mem_toList_iff.1 ha)]

/-- Two frames of one activation (same inputs) whose registers agree on `v`'s arguments
evaluate `v` alike. -/
theorem evalValue_congr {env : Env} {ctx : Ctx} {fr g : Frame} {v : Value}
    (hg : g = { fr with regs := g.regs }) (h : ∀ a ∈ v.args, fr.regs[a]? = g.regs[a]?) :
    evalValue env ctx fr v = evalValue env ctx g v := by
  rw [hg]
  exact evalValue_regs (fr := fr) (r := fr.regs) (r' := g.regs) h

theorem lt_of_value? {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    x < f.valueTab.size := by
  unfold Func.value? at h
  rcases Nat.lt_or_ge x f.valueTab.size with hx | hx
  · exact hx
  · rw [Array.getElem?_eq_none hx] at h; cases h

theorem lt_of_block? {f : Func} {x : ID} {b : Block} (h : f.block? x = some b) :
    x < f.blockTab.size := by
  unfold Func.block? at h
  rcases Nat.lt_or_ge x f.blockTab.size with hx | hx
  · exact hx
  · rw [Array.getElem?_eq_none hx] at h; cases h

/-- The arguments of value `x` of `f` (none if `x` is not a value). -/
def argsF (f : Func) (x : ID) : List ID := ((f.value? x).map (·.args.toList)).getD []

theorem argsF_of {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    argsF f x = v.args.toList := by simp [argsF, h]

/-! ## `evalAll` -/

/-- Evaluating a dependency order `o` writes exactly the values of `o`, each to its evaluation
in the final frame. -/
theorem evalAll_spec {env : Env} {ctx : Ctx} :
    ∀ {o : List ID} {fr fr' : Frame}, o.Nodup → TopoRem (argsF ctx.f) o →
      fr.regs.size = ctx.f.valueTab.size → evalAll env ctx fr o = .ok fr' →
      fr' = { fr with regs := fr'.regs } ∧ fr'.regs.size = fr.regs.size ∧
      (∀ z, z ∉ o → fr'.regs[z]? = fr.regs[z]?) ∧
      (∀ x ∈ o, ∃ v y, ctx.f.value? x = some v ∧ fr'.regs[x]? = some (some y) ∧
        evalValue env ctx fr' v = .ok y)
  | [], fr, fr', _, _, _, h => by
    cases h
    exact ⟨rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: s, fr, fr', hn, ht, hs, h => by
    rw [evalAll_cons] at h
    unfold stepV at h
    cases hv : ctx.f.value? x with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h
      simp only at h
      cases he : evalValue env ctx fr v with
      | panic e m => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h
      | ok y =>
        rw [he] at h
        simp only at h
        have hxlt : x < fr.regs.size := hs ▸ lt_of_value? hv
        have hxs : x ∉ s := (List.nodup_cons.1 hn).1
        obtain ⟨h1, h2, h3, h4⟩ :=
          evalAll_spec (List.nodup_cons.1 hn).2 ht.2 (by simp [Frame.set, hs]) h
        have h1' : fr' = { fr with regs := fr'.regs } := h1
        refine ⟨h1', by rw [h2]; simp [Frame.set], fun z hz => ?_, fun x' hx' => ?_⟩
        · have hzs : z ∉ s := fun hm => hz (List.mem_cons_of_mem _ hm)
          have hzx : x ≠ z := fun he => hz (he ▸ List.mem_cons_self)
          rw [h3 z hzs, Frame.set_regs_ne hzx]
        · rcases List.mem_cons.1 hx' with rfl | hx'
          · refine ⟨v, y, hv, by rw [h3 _ hxs]; exact Frame.set_regs_self hxlt, ?_⟩
            rw [← he]
            refine (evalValue_congr (g := fr') h1' fun a ha => ?_).symm
            have has : a ∉ x' :: s := ht.1 a (by rw [argsF_of hv]; exact Array.mem_toList_iff.2 ha)
            have hax : x' ≠ a := fun he => has (he ▸ List.mem_cons_self)
            rw [h3 a (fun hm => has (List.mem_cons_of_mem _ hm)), Frame.set_regs_ne hax]
          · exact h4 x' hx'

/-! ## `enterBlock` -/

/-- The function `enterBlock` maps over the block's values to collect its `Phi`s. -/
def phiStep (ctx : Ctx) (fr : Frame) (i : Nat) (id : ID) : Res (Option (ID × Val)) :=
  match ctx.f.value? id with
  | some v =>
    if v.op == .Phi then
      match v.args[i]? with
      | some a =>
        match (fr.regs[a]?).join with
        | some x => .ok (some (id, x.retype (ctx.tys[id]?.getD .other)))
        | none => .stuck s!"phi v{id}: argument v{a} has no value"
      | none => .stuck s!"phi v{id}: no argument {i}"
    else .ok none
  | none => .stuck s!"v{id} is not in the function"

/-- The registers after setting the collected `Phi`s. -/
def setPhis (ps : List (ID × Val)) (r : Array (Option Val)) : Array (Option Val) :=
  ps.foldl (fun r (id, x) => r.set! id (some x)) r

theorem enterBlock_eq (env : Env) (ctx : Ctx) (fr : Frame) (b : Block) (i : Nat) :
    enterBlock env ctx fr b i =
      (b.values.toList.filterMapM (phiStep ctx fr i)).bind fun ps =>
        (Res.ofOption s!"b{b.id}: cyclic values" (ctx.sched[b.id]?).join).bind fun o =>
          evalAll env ctx { fr with regs := setPhis ps fr.regs } o.toList := rfl

theorem phiStep_some {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID} {p : ID × Val}
    (h : phiStep ctx fr i z = .ok (some p)) :
    p.1 = z ∧ ∃ v a y, ctx.f.value? z = some v ∧ v.op = .Phi ∧ v.args[i]? = some a ∧
      fr.regs[a]? = some (some y) ∧ p.2 = y.retype (ctx.tys[z]?.getD .other) := by
  unfold phiStep at h
  split at h
  · rename_i v hv
    split at h
    · rename_i hphi
      split at h
      · rename_i a ha
        split at h
        · rename_i y hy
          cases h
          refine ⟨rfl, v, a, y, hv, by simpa using hphi, ha, ?_, rfl⟩
          cases hr : fr.regs[a]? with
          | none => rw [hr] at hy; cases hy
          | some o => rw [hr] at hy; simp at hy; rw [hy]
        · cases h
      · cases h
    · cases h
  · cases h

theorem phiStep_none {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID}
    (h : phiStep ctx fr i z = .ok none) : ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi := by
  unfold phiStep at h
  split at h
  · rename_i v hv
    split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · rename_i hphi; exact ⟨v, hv, by simpa using hphi⟩
  · cases h

theorem filterMapM_phi {ctx : Ctx} {fr : Frame} {i : Nat} :
    ∀ {l : List ID} {ps : List (ID × Val)}, l.filterMapM (phiStep ctx fr i) = .ok ps →
      (ps.map Prod.fst).Sublist l ∧ (∀ p ∈ ps, phiStep ctx fr i p.1 = .ok (some p)) ∧
      ∀ z ∈ l, (∃ p ∈ ps, p.1 = z) ∨ phiStep ctx fr i z = .ok none
  | [], ps, h => by
    rw [List.filterMapM_nil] at h; cases h
    exact ⟨List.Sublist.slnil, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | z :: l, ps, h => by
    rw [List.filterMapM_cons] at h
    cases hz : phiStep ctx fr i z with
    | panic e m => rw [hz] at h; cases h
    | stuck msg => rw [hz] at h; cases h
    | ok o =>
      rw [hz] at h
      cases o with
      | none =>
        obtain ⟨h1, h2, h3⟩ := filterMapM_phi h
        refine ⟨h1.cons z, h2, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact .inr hz
        · exact h3 y hy
      | some p =>
        change (List.filterMapM (phiStep ctx fr i) l).bind (fun r => .ok (p :: r)) = .ok ps at h
        cases hl : List.filterMapM (phiStep ctx fr i) l with
        | panic e m => rw [hl] at h; cases h
        | stuck msg => rw [hl] at h; cases h
        | ok ps' =>
          rw [hl] at h; cases h
          obtain ⟨h1, h2, h3⟩ := filterMapM_phi hl
          have hp1 := (phiStep_some hz).1
          refine ⟨by rw [List.map_cons, hp1]; exact h1.cons_cons z, fun q hq => ?_, fun y hy => ?_⟩
          · rcases List.mem_cons.1 hq with rfl | hq
            · rw [hp1]; exact hz
            · exact h2 q hq
          · rcases List.mem_cons.1 hy with rfl | hy
            · exact .inl ⟨p, List.mem_cons_self, hp1⟩
            · rcases h3 y hy with ⟨q, hq, hqy⟩ | hn
              · exact .inl ⟨q, List.mem_cons_of_mem _ hq, hqy⟩
              · exact .inr hn

theorem setPhis_size : ∀ (ps : List (ID × Val)) (r : Array (Option Val)),
    (setPhis ps r).size = r.size
  | [], _ => rfl
  | (id, x) :: ps, r => by
    unfold setPhis; rw [List.foldl_cons]
    exact (setPhis_size ps _).trans (by simp)

theorem setPhis_not_mem : ∀ (ps : List (ID × Val)) (r : Array (Option Val)) (z : ID),
    z ∉ ps.map Prod.fst → (setPhis ps r)[z]? = r[z]?
  | [], _, _, _ => rfl
  | (id, x) :: ps, r, z, hz => by
    unfold setPhis; rw [List.foldl_cons]
    simp only [List.map_cons, List.mem_cons, not_or] at hz
    refine (setPhis_not_mem ps _ z hz.2).trans ?_
    dsimp only
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hz.1)]

theorem setPhis_mem : ∀ (ps : List (ID × Val)) (r : Array (Option Val)) (z : ID) (x : Val),
    (ps.map Prod.fst).Nodup → (z, x) ∈ ps → z < r.size → (setPhis ps r)[z]? = some (some x)
  | [], _, _, _, _, h, _ => absurd h List.not_mem_nil
  | (id, y) :: ps, r, z, x, hn, hm, hz => by
    unfold setPhis; rw [List.foldl_cons]
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hm with he | hm
    · obtain ⟨h1, h2⟩ := Prod.mk.inj he
      subst h1; subst h2
      refine (setPhis_not_mem ps _ _ hn.1).trans ?_
      dsimp only
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self]; simp [hz]
    · exact setPhis_mem ps _ z x hn.2 hm (by simpa using hz)

/-- What setting the collected `Phi`s does. -/
theorem phis_spec {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat} {ps : List (ID × Val)}
    (hnd : b.values.toList.Nodup) (hps : b.values.toList.filterMapM (phiStep ctx fr i) = .ok ps) :
    (setPhis ps fr.regs).size = fr.regs.size ∧
      (∀ z ∈ b.values, (ctx.f.value? z).isSome) ∧
      (∀ z, (z ∉ b.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi) →
        (setPhis ps fr.regs)[z]? = fr.regs[z]?) ∧
      (∀ z ∈ b.values, ∀ v, ctx.f.value? z = some v → v.op = .Phi → z < fr.regs.size →
        ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
          (setPhis ps fr.regs)[z]? = some (some (y.retype (ctx.tys[z]?.getD .other)))) := by
  obtain ⟨hsub, hsome, hall⟩ := filterMapM_phi hps
  have hnd' : (ps.map Prod.fst).Nodup := hsub.nodup hnd
  refine ⟨setPhis_size ps fr.regs, fun z hz => ?_, fun z hz => ?_, fun z hz v hv hphi hlt => ?_⟩
  · rcases hall z (Array.mem_toList_iff.2 hz) with ⟨p, hp, rfl⟩ | hn
    · obtain ⟨-, v, -, -, hv, -⟩ := phiStep_some (hsome p hp); simp [hv]
    · obtain ⟨v, hv, -⟩ := phiStep_none hn; simp [hv]
  · refine setPhis_not_mem ps fr.regs z fun hm => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    obtain ⟨-, v, a, y, hv, hphi, -⟩ := phiStep_some (hsome p hp)
    rcases hz with hz | ⟨v', hv', hne⟩
    · exact hz (Array.mem_toList_iff.1 (hsub.subset (List.mem_map.2 ⟨p, hp, rfl⟩)))
    · rw [hv] at hv'; cases hv'; exact hne hphi
  · rcases hall z (Array.mem_toList_iff.2 hz) with ⟨p, hp, rfl⟩ | hn
    · obtain ⟨_, v', a, y, hv', -, ha, hy, hp2⟩ := phiStep_some (hsome p hp)
      rw [hv] at hv'; cases hv'
      refine ⟨a, y, ha, hy, ?_⟩
      rw [← hp2]
      exact setPhis_mem ps fr.regs p.1 p.2 hnd' hp hlt
    · obtain ⟨v', hv', hne⟩ := phiStep_none hn
      rw [hv] at hv'; cases hv'; exact absurd hphi hne

/-- The `Phi` collection succeeds when every value's step does. -/
theorem filterMapM_phi_ok {ctx : Ctx} {fr : Frame} {i : Nat} :
    ∀ {l : List ID}, (∀ z ∈ l, ∃ o, phiStep ctx fr i z = .ok o) →
      ∃ ps, l.filterMapM (phiStep ctx fr i) = .ok ps
  | [], _ => ⟨[], rfl⟩
  | z :: l, h => by
    obtain ⟨o, ho⟩ := h z List.mem_cons_self
    obtain ⟨ps, hps⟩ := filterMapM_phi_ok (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.filterMapM_cons, ho]
    cases o with
    | none => exact ⟨ps, hps⟩
    | some p =>
      refine ⟨p :: ps, ?_⟩
      change (List.filterMapM (phiStep ctx fr i) l).bind (fun r => .ok (p :: r)) = _
      rw [hps]; rfl

/-- **Entering a block.** The `Phi`s take the incoming edge's argument from the old frame;
values outside the block and the block's non-`Phi`s keep their registers until the schedule
runs. -/
theorem enterBlock_spec {env : Env} {ctx : Ctx} {fr fr' : Frame} {b : Block} {i : Nat}
    (hnd : b.values.toList.Nodup) (h : enterBlock env ctx fr b i = .ok fr') :
    ∃ frP o, (ctx.sched[b.id]?).join = some o ∧ evalAll env ctx frP o.toList = .ok fr' ∧
      frP = { fr with regs := frP.regs } ∧ frP.regs.size = fr.regs.size ∧
      (∀ z ∈ b.values, (ctx.f.value? z).isSome) ∧
      (∀ z, (z ∉ b.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi) →
        frP.regs[z]? = fr.regs[z]?) ∧
      (∀ z ∈ b.values, ∀ v, ctx.f.value? z = some v → v.op = .Phi → z < fr.regs.size →
        ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
          frP.regs[z]? = some (some (y.retype (ctx.tys[z]?.getD .other)))) := by
  rw [enterBlock_eq] at h
  cases hps : b.values.toList.filterMapM (phiStep ctx fr i) with
  | panic e m => rw [hps] at h; cases h
  | stuck msg => rw [hps] at h; cases h
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _ at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      change evalAll env ctx _ o.toList = .ok fr' at h
      obtain ⟨h1, h2, h3, h4⟩ := phis_spec hnd hps
      exact ⟨_, o, rfl, h, rfl, h1, h2, h3, h4⟩

theorem phiStep_not_panic {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID} {e : Panic} {m : Mem} :
    phiStep ctx fr i z ≠ .panic e m := by
  unfold phiStep
  split
  · split
    · split
      · split <;> nofun
      · nofun
    · nofun
  · nofun

theorem filterMapM_phi_not_panic {ctx : Ctx} {fr : Frame} {i : Nat} {e : Panic} {m : Mem} :
    ∀ {l : List ID}, l.filterMapM (phiStep ctx fr i) ≠ .panic e m
  | [] => nofun
  | z :: l => by
    rw [List.filterMapM_cons]
    cases hz : phiStep ctx fr i z with
    | panic e' m' => exact absurd hz phiStep_not_panic
    | stuck msg => nofun
    | ok o =>
      cases o with
      | none => exact filterMapM_phi_not_panic
      | some p =>
        change (List.filterMapM (phiStep ctx fr i) l).bind (fun r => .ok (p :: r)) ≠ _
        cases hl : List.filterMapM (phiStep ctx fr i) l with
        | panic e' m' => exact absurd hl filterMapM_phi_not_panic
        | stuck msg => nofun
        | ok ps => nofun

/-- Where a block entry panics: in its schedule, after the `Phi`s. -/
theorem enterBlock_panic {env : Env} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {e : Panic} {m : Mem} (h : enterBlock env ctx fr b i = .panic e m) :
    ∃ ps o, b.values.toList.filterMapM (phiStep ctx fr i) = .ok ps ∧
      (ctx.sched[b.id]?).join = some o ∧
      evalAll env ctx { fr with regs := setPhis ps fr.regs } o.toList = .panic e m := by
  rw [enterBlock_eq] at h
  cases hps : b.values.toList.filterMapM (phiStep ctx fr i) with
  | panic e' m' => exact absurd hps filterMapM_phi_not_panic
  | stuck msg => rw [hps] at h; cases h
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _ at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      exact ⟨ps, o, rfl, rfl, h⟩

/-! ## The schedule of a well-formed block -/

theorem sched_of_block {tabs : Tables} {f : Func} {bid : ID} {b : Block} (hb : f.block? bid = some b) :
    ((Ctx.make tabs f).sched[bid]?).join = schedule f b := by
  unfold Func.block? at hb
  simp only [Ctx.make, Array.getElem?_map]
  cases h : f.blockTab[bid]? with
  | none => rw [h] at hb; cases hb
  | some o => rw [h] at hb; simp at hb; subst hb; simp

/-- Listed values of `b` are values with their own ID. -/
def ValuesOwn (f : Func) (b : Block) : Prop :=
  ∀ id ∈ b.values, ∃ v, f.value? id = some v ∧ v.id = id

theorem mem_schedNodes {f : Func} {b : Block} {n : SNode} :
    n ∈ (schedNodes f b).toList ↔ ∃ id ∈ b.values, ∃ v, f.value? id = some v ∧ v.op ≠ .Phi ∧
      n = ⟨v.id, v.args, prio v.op⟩ := by
  unfold schedNodes
  simp only [Array.toList_filterMap, List.mem_filterMap, Array.mem_toList_iff]
  constructor
  · rintro ⟨id, hid, h⟩
    split at h
    · rename_i v hv
      split at h
      · cases h
      · rename_i hp; cases h; exact ⟨id, hid, v, hv, by simpa using hp, rfl⟩
    · cases h
  · rintro ⟨id, hid, v, hv, hp, rfl⟩
    exact ⟨id, hid, by rw [hv]; simp [hp]⟩

theorem filterMap_sublist_self {α : Type} {g : α → Option α} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y, g x = some y → y = x) → (l.filterMap g).Sublist l
  | [], _ => List.Sublist.slnil
  | x :: l, h => by
    rw [List.filterMap_cons]
    have ih := filterMap_sublist_self (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    cases hx : g x with
    | none => exact ih.cons x
    | some y => rw [h x List.mem_cons_self y hx]; exact ih.cons_cons x

theorem schedNodes_sublist {f : Func} {b : Block} (hown : ValuesOwn f b) :
    ((schedNodes f b).toList.map (·.id)).Sublist b.values.toList := by
  unfold schedNodes
  rw [Array.toList_filterMap, List.map_filterMap]
  refine filterMap_sublist_self fun id hid y hy => ?_
  obtain ⟨v, hv, hvid⟩ := hown id (Array.mem_toList_iff.1 hid)
  simp only [hv] at hy
  split at hy <;> simp at hy
  rw [← hy, hvid]

theorem schedNodes_ids {f : Func} {b : Block} (hown : ValuesOwn f b)
    (hnd : b.values.toList.Nodup) : ((schedNodes f b).toList.map (·.id)).Nodup :=
  (schedNodes_sublist hown).nodup hnd

/-- The nodes of the schedule are the block's non-`Phi` values. -/
theorem nodeIn_schedNodes {f : Func} {b : Block} (hown : ValuesOwn f b) {x : ID} :
    NodeIn (schedNodes f b).toList x ↔ x ∈ b.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨id, hid, v, hv, hp, rfl⟩ := mem_schedNodes.1 hn
    obtain ⟨v', hv', hvid⟩ := hown id hid
    rw [hv] at hv'; cases hv'
    exact ⟨by rw [hvid]; exact hid, v, by rw [hvid]; exact hv, hp⟩
  · rintro ⟨hx, v, hv, hp⟩
    obtain ⟨v', hv', hvid⟩ := hown x hx
    rw [hv] at hv'; cases hv'
    exact ⟨_, mem_schedNodes.2 ⟨x, hx, v, hv, hp, rfl⟩, hvid⟩

/-- A node's arguments are its value's arguments. -/
theorem argsOf_schedNodes {f : Func} {b : Block} (hown : ValuesOwn f b)
    (hnd : b.values.toList.Nodup) {x : ID} {v : Value} (hx : x ∈ b.values)
    (hv : f.value? x = some v) (hp : v.op ≠ .Phi) :
    argsOf (schedNodes f b).toList x = v.args.toList := by
  obtain ⟨v', hv', hvid⟩ := hown x hx
  rw [hv] at hv'; cases hv'
  have hm : (⟨v.id, v.args, prio v.op⟩ : SNode) ∈ (schedNodes f b).toList :=
    mem_schedNodes.2 ⟨x, hx, v, hv, hp, rfl⟩
  have := argsOf_of_mem (schedNodes_ids hown hnd) hm
  rw [hvid] at this; exact this

theorem topoRem_congr {D D' : ID → List ID} :
    ∀ {o : List ID}, (∀ x ∈ o, D x = D' x) → TopoRem D o → TopoRem D' o
  | [], _, _ => trivial
  | x :: s, h, ⟨h1, h2⟩ =>
    ⟨by rw [← h x List.mem_cons_self]; exact h1,
      topoRem_congr (fun y hy => h y (List.mem_cons_of_mem _ hy)) h2⟩

/-- **The schedule of a block.** A computed schedule lists the block's non-`Phi` values once
each, after their arguments in the block. -/
theorem schedule_topo {f : Func} {b : Block} {o : Array ID} (hown : ValuesOwn f b)
    (hnd : b.values.toList.Nodup) (h : schedule f b = some o) :
    o.toList.Nodup ∧ TopoRem (argsF f) o.toList ∧
      ∀ x, x ∈ o.toList ↔ x ∈ b.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi := by
  have hs := (schedule_spec h).topo
  have hmem : ∀ x, x ∈ o.toList ↔ x ∈ b.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi :=
    fun x => (hs.mem x).trans (nodeIn_schedNodes hown)
  refine ⟨hs.nodup, topoRem_congr (fun x hx => ?_) hs.topoRem, hmem⟩
  obtain ⟨hxb, v, hv, hp⟩ := (hmem x).1 hx
  rw [argsOf_schedNodes hown hnd hxb hv hp, argsF_of hv]

end GoFV.Proof
