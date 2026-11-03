import GoFV.Proof.EvalL

/-!
# Lowered block entries: `evalAllL` and `enterBlockL`

`GoFV.Proof.Frame` for `runL`'s runner (any mode `md`): evaluating a dependency order
(`evalAllL_spec`), the `Phi`s of a block entry, taken at their shapes by `LMode.retype`
(`phiStepL`, `phisL_spec`, `enterBlockL_spec`), and where an entry panics (`enterBlockL_panic`).
`Ctx.makeL` has `Ctx.make`'s schedules (`sched_makeL`, `sched_of_blockL`).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- Evaluating a dependency order `o` writes exactly the values of `o`, each to its evaluation
in the final frame. -/
theorem evalAllL_spec {md : LMode} {env : Env} {ctx : Ctx} :
    ∀ {o : List ID} {fr fr' : Frame}, o.Nodup → TopoRem (argsF ctx.f) o →
      fr.regs.size = ctx.f.valueTab.size → evalAllL md env ctx fr o = .ok fr' →
      fr' = { fr with regs := fr'.regs } ∧ fr'.regs.size = fr.regs.size ∧
      (∀ z, z ∉ o → fr'.regs[z]? = fr.regs[z]?) ∧
      (∀ x ∈ o, ∃ v y, ctx.f.value? x = some v ∧ fr'.regs[x]? = some (some y) ∧
        evalValueL md env ctx fr' v = .ok y)
  | [], fr, fr', _, _, _, h => by
    cases h
    exact ⟨rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: s, fr, fr', hn, ht, hs, h => by
    rw [evalAllL_cons] at h
    unfold stepVL at h
    cases hv : ctx.f.value? x with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h
      simp only at h
      cases he : evalValueL md env ctx fr v with
      | panic e m => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h
      | ok y =>
        rw [he] at h
        simp only at h
        have hxlt : x < fr.regs.size := hs ▸ lt_of_value? hv
        have hxs : x ∉ s := (List.nodup_cons.1 hn).1
        obtain ⟨h1, h2, h3, h4⟩ :=
          evalAllL_spec (List.nodup_cons.1 hn).2 ht.2 (by simp [Frame.set, hs]) h
        have h1' : fr' = { fr with regs := fr'.regs } := h1
        refine ⟨h1', by rw [h2]; simp [Frame.set], fun z hz => ?_, fun x' hx' => ?_⟩
        · have hzs : z ∉ s := fun hm => hz (List.mem_cons_of_mem _ hm)
          have hzx : x ≠ z := fun he => hz (he ▸ List.mem_cons_self)
          rw [h3 z hzs, Frame.set_regs_ne hzx]
        · rcases List.mem_cons.1 hx' with rfl | hx'
          · refine ⟨v, y, hv, by rw [h3 _ hxs]; exact Frame.set_regs_self hxlt, ?_⟩
            rw [← he]
            refine (evalValueL_congr (g := fr') h1' fun a ha => ?_).symm
            have has : a ∉ x' :: s := ht.1 a (by rw [argsF_of hv]; exact Array.mem_toList_iff.2 ha)
            have hax : x' ≠ a := fun he => has (he ▸ List.mem_cons_self)
            rw [h3 a (fun hm => has (List.mem_cons_of_mem _ hm)), Frame.set_regs_ne hax]
          · exact h4 x' hx'

/-! ## `enterBlockL` -/

/-- The function `enterBlockL` maps over the block's values to collect its `Phi`s. -/
def phiStepL (md : LMode) (ctx : Ctx) (fr : Frame) (i : Nat) (id : ID) :
    Res (Option (ID × Val)) :=
  match ctx.f.value? id with
  | some v =>
    if v.op == .Phi then
      match v.args[i]? with
      | some a =>
        match (fr.regs[a]?).join with
        | some x => .ok (some (id, md.retype (ctx.tys[id]?.getD .other) x))
        | none => .stuck s!"phi v{id}: argument v{a} has no value"
      | none => .stuck s!"phi v{id}: no argument {i}"
    else .ok none
  | none => .stuck s!"v{id} is not in the function"

theorem enterBlockL_eq (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) (b : Block) (i : Nat) :
    enterBlockL md env ctx fr b i =
      (b.values.toList.filterMapM (phiStepL md ctx fr i)).bind fun ps =>
        (Res.ofOption s!"b{b.id}: cyclic values" (ctx.sched[b.id]?).join).bind fun o =>
          evalAllL md env ctx { fr with regs := setPhis ps fr.regs } o.toList := rfl

theorem phiStepL_some {md : LMode} {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID} {p : ID × Val}
    (h : phiStepL md ctx fr i z = .ok (some p)) :
    p.1 = z ∧ ∃ v a y, ctx.f.value? z = some v ∧ v.op = .Phi ∧ v.args[i]? = some a ∧
      fr.regs[a]? = some (some y) ∧ p.2 = md.retype (ctx.tys[z]?.getD .other) y := by
  unfold phiStepL at h
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

theorem phiStepL_none {md : LMode} {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID}
    (h : phiStepL md ctx fr i z = .ok none) : ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi := by
  unfold phiStepL at h
  split at h
  · rename_i v hv
    split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · rename_i hphi; exact ⟨v, hv, by simpa using hphi⟩
  · cases h

theorem filterMapM_phiL {md : LMode} {ctx : Ctx} {fr : Frame} {i : Nat} :
    ∀ {l : List ID} {ps : List (ID × Val)}, l.filterMapM (phiStepL md ctx fr i) = .ok ps →
      (ps.map Prod.fst).Sublist l ∧ (∀ p ∈ ps, phiStepL md ctx fr i p.1 = .ok (some p)) ∧
      ∀ z ∈ l, (∃ p ∈ ps, p.1 = z) ∨ phiStepL md ctx fr i z = .ok none
  | [], ps, h => by
    rw [List.filterMapM_nil] at h; cases h
    exact ⟨List.Sublist.slnil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩
  | z :: l, ps, h => by
    rw [List.filterMapM_cons] at h
    cases hz : phiStepL md ctx fr i z with
    | panic e m => rw [hz] at h; cases h
    | stuck msg => rw [hz] at h; cases h
    | ok o =>
      rw [hz] at h
      cases o with
      | none =>
        obtain ⟨h1, h2, h3⟩ := filterMapM_phiL h
        refine ⟨h1.cons z, h2, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact .inr hz
        · exact h3 y hy
      | some p =>
        change (List.filterMapM (phiStepL md ctx fr i) l).bind (fun r => .ok (p :: r)) = .ok ps at h
        cases hl : List.filterMapM (phiStepL md ctx fr i) l with
        | panic e m => rw [hl] at h; cases h
        | stuck msg => rw [hl] at h; cases h
        | ok ps' =>
          rw [hl] at h; cases h
          obtain ⟨h1, h2, h3⟩ := filterMapM_phiL hl
          have hp1 := (phiStepL_some hz).1
          refine ⟨by rw [List.map_cons, hp1]; exact h1.cons_cons z, fun q hq => ?_, fun y hy => ?_⟩
          · rcases List.mem_cons.1 hq with rfl | hq
            · rw [hp1]; exact hz
            · exact h2 q hq
          · rcases List.mem_cons.1 hy with rfl | hy
            · exact .inl ⟨p, List.mem_cons_self, hp1⟩
            · rcases h3 y hy with ⟨q, hq, hqy⟩ | hn
              · exact .inl ⟨q, List.mem_cons_of_mem _ hq, hqy⟩
              · exact .inr hn

/-- What setting the collected `Phi`s does. -/
theorem phisL_spec {md : LMode} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {ps : List (ID × Val)} (hnd : b.values.toList.Nodup)
    (hps : b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps) :
    (setPhis ps fr.regs).size = fr.regs.size ∧
      (∀ z ∈ b.values, (ctx.f.value? z).isSome) ∧
      (∀ z, (z ∉ b.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi) →
        (setPhis ps fr.regs)[z]? = fr.regs[z]?) ∧
      (∀ z ∈ b.values, ∀ v, ctx.f.value? z = some v → v.op = .Phi → z < fr.regs.size →
        ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
          (setPhis ps fr.regs)[z]? = some (some (md.retype (ctx.tys[z]?.getD .other) y))) := by
  obtain ⟨hsub, hsome, hall⟩ := filterMapM_phiL hps
  have hnd' : (ps.map Prod.fst).Nodup := hsub.nodup hnd
  refine ⟨setPhis_size ps fr.regs, fun z hz => ?_, fun z hz => ?_, fun z hz v hv hphi hlt => ?_⟩
  · rcases hall z (Array.mem_toList_iff.2 hz) with ⟨p, hp, rfl⟩ | hn
    · obtain ⟨-, v, -, -, hv, -⟩ := phiStepL_some (hsome p hp); simp [hv]
    · obtain ⟨v, hv, -⟩ := phiStepL_none hn; simp [hv]
  · refine setPhis_not_mem ps fr.regs z fun hm => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    obtain ⟨-, v, a, y, hv, hphi, -⟩ := phiStepL_some (hsome p hp)
    rcases hz with hz | ⟨v', hv', hne⟩
    · exact hz (Array.mem_toList_iff.1 (hsub.subset (List.mem_map.2 ⟨p, hp, rfl⟩)))
    · rw [hv] at hv'; cases hv'; exact hne hphi
  · rcases hall z (Array.mem_toList_iff.2 hz) with ⟨p, hp, rfl⟩ | hn
    · obtain ⟨_, v', a, y, hv', -, ha, hy, hp2⟩ := phiStepL_some (hsome p hp)
      rw [hv] at hv'; cases hv'
      refine ⟨a, y, ha, hy, ?_⟩
      rw [← hp2]
      exact setPhis_mem ps fr.regs p.1 p.2 hnd' hp hlt
    · obtain ⟨v', hv', hne⟩ := phiStepL_none hn
      rw [hv] at hv'; cases hv'; exact absurd hphi hne

/-- The `Phi` collection succeeds when every value's step does. -/
theorem filterMapM_phiL_ok {md : LMode} {ctx : Ctx} {fr : Frame} {i : Nat} :
    ∀ {l : List ID}, (∀ z ∈ l, ∃ o, phiStepL md ctx fr i z = .ok o) →
      ∃ ps, l.filterMapM (phiStepL md ctx fr i) = .ok ps
  | [], _ => ⟨[], rfl⟩
  | z :: l, h => by
    obtain ⟨o, ho⟩ := h z List.mem_cons_self
    obtain ⟨ps, hps⟩ := filterMapM_phiL_ok (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.filterMapM_cons, ho]
    cases o with
    | none => exact ⟨ps, hps⟩
    | some p =>
      refine ⟨p :: ps, ?_⟩
      change (List.filterMapM (phiStepL md ctx fr i) l).bind (fun r => .ok (p :: r)) = _
      rw [hps]; rfl

/-- **Entering a lowered block.** The `Phi`s take the incoming edge's argument from the old
frame, at their shapes; values outside the block and the block's non-`Phi`s keep their registers
until the schedule runs. -/
theorem enterBlockL_spec {md : LMode} {env : Env} {ctx : Ctx} {fr fr' : Frame} {b : Block}
    {i : Nat} (hnd : b.values.toList.Nodup) (h : enterBlockL md env ctx fr b i = .ok fr') :
    ∃ frP o, (ctx.sched[b.id]?).join = some o ∧ evalAllL md env ctx frP o.toList = .ok fr' ∧
      frP = { fr with regs := frP.regs } ∧ frP.regs.size = fr.regs.size ∧
      (∀ z ∈ b.values, (ctx.f.value? z).isSome) ∧
      (∀ z, (z ∉ b.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi) →
        frP.regs[z]? = fr.regs[z]?) ∧
      (∀ z ∈ b.values, ∀ v, ctx.f.value? z = some v → v.op = .Phi → z < fr.regs.size →
        ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
          frP.regs[z]? = some (some (md.retype (ctx.tys[z]?.getD .other) y))) := by
  rw [enterBlockL_eq] at h
  cases hps : b.values.toList.filterMapM (phiStepL md ctx fr i) with
  | panic e m => rw [hps] at h; cases h
  | stuck msg => rw [hps] at h; cases h
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _ at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      change evalAllL md env ctx _ o.toList = .ok fr' at h
      obtain ⟨h1, h2, h3, h4⟩ := phisL_spec hnd hps
      exact ⟨_, o, rfl, h, rfl, h1, h2, h3, h4⟩

theorem phiStepL_not_panic {md : LMode} {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID} {e : Panic}
    {m : Mem} : phiStepL md ctx fr i z ≠ .panic e m := by
  unfold phiStepL
  split
  · split
    · split
      · split <;> nofun
      · nofun
    · nofun
  · nofun

theorem filterMapM_phiL_not_panic {md : LMode} {ctx : Ctx} {fr : Frame} {i : Nat} {e : Panic}
    {m : Mem} : ∀ {l : List ID}, l.filterMapM (phiStepL md ctx fr i) ≠ .panic e m
  | [] => nofun
  | z :: l => by
    rw [List.filterMapM_cons]
    cases hz : phiStepL md ctx fr i z with
    | panic e' m' => exact absurd hz phiStepL_not_panic
    | stuck msg => nofun
    | ok o =>
      cases o with
      | none => exact filterMapM_phiL_not_panic
      | some p =>
        change (List.filterMapM (phiStepL md ctx fr i) l).bind (fun r => .ok (p :: r)) ≠ _
        cases hl : List.filterMapM (phiStepL md ctx fr i) l with
        | panic e' m' => exact absurd hl filterMapM_phiL_not_panic
        | stuck msg => nofun
        | ok ps => nofun

/-- Where a lowered block entry panics: in its schedule, after the `Phi`s. -/
theorem enterBlockL_panic {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {e : Panic} {m : Mem} (h : enterBlockL md env ctx fr b i = .panic e m) :
    ∃ ps o, b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps ∧
      (ctx.sched[b.id]?).join = some o ∧
      evalAllL md env ctx { fr with regs := setPhis ps fr.regs } o.toList = .panic e m := by
  rw [enterBlockL_eq] at h
  cases hps : b.values.toList.filterMapM (phiStepL md ctx fr i) with
  | panic e' m' => exact absurd hps filterMapM_phiL_not_panic
  | stuck msg => rw [hps] at h; cases h
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _ at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      exact ⟨ps, o, rfl, rfl, h⟩

/-! ## `Ctx.makeL` -/

theorem makeL_f (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).f = f := by
  unfold Ctx.makeL; split <;> rfl

theorem sched_makeL (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).sched = (Ctx.make tabs f).sched := by
  unfold Ctx.makeL; split <;> rfl

theorem sched_of_blockL {tabs : Tables} {f : Func} {bid : ID} {b : Block}
    (hb : f.block? bid = some b) : ((Ctx.makeL tabs f).sched[bid]?).join = schedule f b := by
  rw [sched_makeL]; exact sched_of_block hb

theorem params_makeL (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).params = (Ctx.make tabs f).params := by
  unfold Ctx.makeL; split <;> rfl

theorem outs_makeL (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).outs = (Ctx.make tabs f).outs := by
  unfold Ctx.makeL; split <;> rfl

theorem act_makeL (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).act = (Ctx.make tabs f).act := by
  unfold Ctx.makeL; split <;> rfl

theorem tabs_makeL (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).tabs = tabs := by
  unfold Ctx.makeL; split <;> rfl

/-- The shape of a value in `runL`'s context. -/
theorem tys_makeL (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).tys =
      f.valueTab.map (valueTy (if f.lowered then typeShapesL tabs else typeShapes tabs)) := by
  unfold Ctx.makeL; split <;> simp_all [Ctx.make]

end GoFV.Proof
