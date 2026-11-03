import GoFV.Proof.Low.DenL
import GoFV.Proof.SimL
import GoFV.Proof.EvalL
import GoFV.Proof.AtomSim

/-!
# Frames of `runL` for the lowered atom simulation (issue #385)

Phase 1's frame facts (`GoFV.Proof.Frame`, `GoFV.Proof.Avail`, `GoFV.Proof.AtomSimOK`) for the
lowered runner in mode `md` (`Sem.evalValueL`, `Sem.enterBlockL`): registers fixed by the mode's
shaping (`RegsTyped`), a value evaluated from its arguments' registers (`evalValueL_of_regs`), a
dependency order evaluated (`evalAllL_spec`), the `Phi`s of a block entry (`phiStepL`,
`phisL_spec`), where a block entry panics (`enterBlockL_panic`, `evalAllL_panic_split`), and the
contexts `Ctx.makeL` of two functions with the same own aux (`ctxL_eq`, `entryFrameL_eq`).
`rty_le`: shaping a refinement in Phase 1's mode is refined by shaping in lowered mode.
-/

namespace GoFV.Proof.Low.Sim

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Proof.Low GoFV.Proof.Term GoFV.Proof.AtomSim

/-! ## Shaping -/

/-- Shaping a refinement in mode `lS` is refined by shaping in mode `lT` when `lS` implies `lT`
(`retype_le_retypeL`). -/
theorem rty_le {lS lT : Bool} (hl : lS = true → lT = true) (t : Ty) {v v' : Val}
    (h : Sem.Refines v v') : Sem.Refines (rty lS t v) (rty lT t v') := by
  cases lS <;> cases lT
  · exact rty_mono false t h
  · unfold rty
    simp only [Bool.false_eq_true, ite_false, ite_true]
    exact (retype_mono t h).trans (retype_le_retypeL t v')
  · exact absurd (hl rfl) (by decide)
  · exact rty_mono true t h

/-- Every register is fixed by the mode's shaping at its value's shape. -/
def RegsTyped (md : LMode) (ctx : Ctx) (fr : Frame) : Prop :=
  ∀ (x : ID) (y : Val), fr.regs[x]? = some (some y) → md.retype (ctx.tys[x]?.getD .other) y = y

theorem regsTyped_replicate (md : LMode) (ctx : Ctx) (n : Nat) (fr : Frame)
    (h : fr.regs = Array.replicate n none) : RegsTyped md ctx fr := fun x y hx => by
  rw [h, Array.getElem?_replicate] at hx
  split at hx <;> cases hx

theorem regsTyped_set {md : LMode} {ctx : Ctx} {T : Frame} {x : ID} {y : Val}
    (ht : RegsTyped md ctx T) (hy : md.retype (ctx.tys[x]?.getD .other) y = y) :
    RegsTyped md ctx (T.set x y) := by
  intro z y' hz
  by_cases hxz : x = z
  · subst hxz
    by_cases hlt : x < T.regs.size
    · rw [Frame.set_regs_self hlt] at hz; cases hz; exact hy
    · have : (T.set x y).regs = T.regs := by
        simp [Frame.set, Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
      rw [this] at hz; exact ht x y' hz
  · rw [Frame.set_regs_ne hxz] at hz; exact ht z y' hz

/-! ## Values -/

/-- A value whose arguments have registers: its op on their registers, shaped. -/
theorem evalValueL_of_regs {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (h : ∀ a ∈ v.args, Reg fr a) :
    evalValueL md env ctx fr v = (evalOpL md.faulting env ctx fr v (v.args.toList.map (rv fr))
      (ctx.tys[v.id]?.getD .other)).bind
        (fun r => .ok (md.retype (ctx.tys[v.id]?.getD .other) r)) := by
  unfold evalValueL
  rw [mapM_regs fun a ha => h a (Array.mem_toList_iff.1 ha)]
  rfl

/-- A value's result is fixed by the mode's shaping at its own shape. -/
theorem evalValueL_typed {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValueL md env ctx fr v = .ok y) : md.retype (ctx.tys[v.id]?.getD .other) y = y := by
  unfold evalValueL at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e m => rw [hm] at h; cases h
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    cases ho : evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [ho] at h; cases h; exact rty_idem md.low _ r
    | panic e m => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h

theorem regsL_of_ok {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValueL md env ctx fr v = .ok y) : ∀ a ∈ v.args, Reg fr a :=
  evalValueL_args_def fun msg hm => by rw [h] at hm; cases hm

theorem regsL_of_panic {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {e : Panic}
    {m : Mem} (h : evalValueL md env ctx fr v = .panic e m) : ∀ a ∈ v.args, Reg fr a :=
  evalValueL_args_def fun msg hm => by rw [h] at hm; cases hm

/-! ## `evalAllL` -/

/-- Evaluating a dependency order `o` writes exactly the values of `o`, each to its evaluation
in the final frame (`evalAll_spec`). -/
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

/-- Evaluating values with their own IDs keeps the registers typed. -/
theorem regsTyped_evalAllL {md : LMode} {env : Env} {ctx : Ctx} {o : List ID} {fr fr' : Frame}
    (ht : RegsTyped md ctx fr) (hown : ∀ x ∈ o, ∀ v, ctx.f.value? x = some v → v.id = x)
    (e3 : ∀ z, z ∉ o → fr'.regs[z]? = fr.regs[z]?)
    (e4 : ∀ x ∈ o, ∃ v y, ctx.f.value? x = some v ∧ fr'.regs[x]? = some (some y) ∧
      evalValueL md env ctx fr' v = .ok y) : RegsTyped md ctx fr' := by
  intro z y hz
  by_cases hzo : z ∈ o
  · obtain ⟨v, y', hv, hy', hev'⟩ := e4 z hzo
    rw [hz] at hy'; cases hy'
    have := evalValueL_typed hev'
    rwa [hown z hzo v hv] at this
  · rw [e3 z hzo] at hz
    exact ht z y hz

/-- Where a source `evalAllL` panics: after an evaluated prefix, at one value. -/
theorem evalAllL_panic_split {md : LMode} {env : Env} {ctx : Ctx} {e : Panic} {m : Mem} :
    ∀ {o : List ID} {g : Frame}, evalAllL md env ctx g o = .panic e m →
      ∃ pre r post g', o = pre ++ r :: post ∧ evalAllL md env ctx g pre = .ok g' ∧
        stepVL md env ctx g' r = .panic e m
  | [], _, h => nomatch h
  | x :: s, g, h => by
    rw [evalAllL_cons] at h
    cases hx : stepVL md env ctx g x with
    | ok y =>
      rw [hx] at h
      obtain ⟨pre, r, post, g', ho, h1, h2⟩ := evalAllL_panic_split h
      refine ⟨x :: pre, r, post, g', by rw [ho]; rfl, ?_, h2⟩
      rw [evalAllL_cons, hx]; exact h1
    | panic e' m' =>
      rw [hx] at h; cases h
      exact ⟨[], x, s, g, rfl, rfl, hx⟩
    | stuck msg => rw [hx] at h; cases h

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

/-- What setting the collected `Phi`s does (`phis_spec`). -/
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

/-- A block entry without panic: the `Phi`s, the schedule, its evaluation. -/
theorem enterBlockL_ok_split {md : LMode} {env : Env} {ctx : Ctx} {fr fr' : Frame} {b : Block}
    {i : Nat} (h : enterBlockL md env ctx fr b i = .ok fr') :
    ∃ ps o, b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps ∧
      (ctx.sched[b.id]?).join = some o ∧
      evalAllL md env ctx { fr with regs := setPhis ps fr.regs } o.toList = .ok fr' := by
  rw [enterBlockL_eq] at h
  cases hps : b.values.toList.filterMapM (phiStepL md ctx fr i) with
  | panic e' m' => rw [hps] at h; cases h
  | stuck msg => rw [hps] at h; cases h
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _ at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      exact ⟨ps, o, rfl, rfl, h⟩

/-- Where a block entry panics: in its schedule, after the `Phi`s. -/
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

theorem enterBlockL_of {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {ps : List (ID × Val)} {o : Array ID} {r : Res Frame}
    (hps : b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps)
    (ho : (ctx.sched[b.id]?).join = some o)
    (hev : evalAllL md env ctx { fr with regs := setPhis ps fr.regs } o.toList = r) :
    enterBlockL md env ctx fr b i = r := by
  rw [enterBlockL_eq, hps]
  change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _
  rw [ho]; exact hev

/-- Setting the `Phi`s keeps the registers typed. -/
theorem regsTyped_phis {md : LMode} {ctx : Ctx} {blk : Block} {fr frP : Frame} {i : Nat}
    (ht : RegsTyped md ctx fr) (hPs : frP.regs.size = fr.regs.size)
    (hkeep : ∀ z, (z ∉ blk.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi) →
      frP.regs[z]? = fr.regs[z]?)
    (hphi : ∀ z ∈ blk.values, ∀ v, ctx.f.value? z = some v → v.op = .Phi → z < fr.regs.size →
      ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
        frP.regs[z]? = some (some (md.retype (ctx.tys[z]?.getD .other) y)))
    (hall : ∀ z ∈ blk.values, (ctx.f.value? z).isSome) : RegsTyped md ctx frP := by
  intro z y hz
  by_cases hph : z ∈ blk.values ∧ ∃ v, ctx.f.value? z = some v ∧ v.op = .Phi
  · obtain ⟨hzb, v, hv, hp⟩ := hph
    have hlt : z < fr.regs.size := by
      rw [← hPs]
      rcases Nat.lt_or_ge z frP.regs.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hz; cases hz
    obtain ⟨a, y0, -, -, hy⟩ := hphi z hzb v hv hp hlt
    rw [hz] at hy; cases hy
    exact rty_idem md.low _ _
  · have hk : z ∉ blk.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi := by
      by_cases hzb : z ∈ blk.values
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hall z hzb)
        exact .inr ⟨v, hv, fun hp => hph ⟨hzb, v, hv, hp⟩⟩
      · exact .inl hzb
    rw [hkeep z hk] at hz
    exact ht z y hz

/-! ## Contexts -/

theorem makeL_f (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).f = f := by
  unfold Ctx.makeL; split <;> rfl

theorem makeL_sched (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).sched = (Ctx.make tabs f).sched := by
  unfold Ctx.makeL; split <;> rfl

theorem typeShapesL_getD (tabs : Tables) (t : TypeRef) :
    (typeShapesL tabs)[t]?.getD .other = shpL tabs t := by
  unfold typeShapesL shpL
  rw [Array.getElem?_map]
  by_cases ht : t < tabs.types.size
  · simp [ht]
  · have hr : ((List.range tabs.types.size).toArray)[t]? = none := by simp [ht]
    have hn : tabs.type? t = none := by
      unfold Tables.type?
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt ht)]; rfl
    rw [hr]
    show Ty.other = tyOfL tabs 32 t
    simp [tyOfL, hn]

/-- The shape `Ctx.makeL` gives a value: its type's shape in `f`'s mode. -/
theorem tysL_of_value {tabs : Tables} {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    (Ctx.makeL tabs f).tys[x]? = some (shp f.lowered tabs v.type) := by
  unfold Ctx.makeL
  cases hl : f.lowered
  · simp only [Bool.false_eq_true, ite_false]
    rw [tys_of_value h]; simp [shp]
  · simp only [ite_true]
    unfold Func.value? at h
    simp only [Array.getElem?_map]
    cases hx : f.valueTab[x]? with
    | none => rw [hx] at h; cases h
    | some o =>
      rw [hx] at h; simp at h; subst h
      simp only [Option.map_some, valueTy, typeShapesL_getD, shp, ite_true]

/-- A context's shape of a value is `shapeL` of its function's value table. -/
theorem tysL_shape (tabs : Tables) (f : Func) (a : ID) :
    (Ctx.makeL tabs f).tys[a]?.getD .other = shapeL f.lowered f.value? tabs a := by
  cases hv : f.value? a with
  | some v => rw [tysL_of_value hv]; simp [shapeL, hv]
  | none =>
    simp only [shapeL, hv, Option.map_none, Option.getD_none]
    have hnone : (Ctx.makeL tabs f).tys[a]? = none ∨ (Ctx.makeL tabs f).tys[a]? = some .other := by
      unfold Func.value? at hv
      unfold Ctx.makeL
      split
      · simp only [Array.getElem?_map]
        cases h : f.valueTab[a]? with
        | none => left; rfl
        | some o =>
          rw [h] at hv
          cases o with
          | none => right; rfl
          | some v => cases hv
      · simp only [Ctx.make, Array.getElem?_map]
        cases h : f.valueTab[a]? with
        | none => left; rfl
        | some o =>
          rw [h] at hv
          cases o with
          | none => right; rfl
          | some v => cases hv
    rcases hnone with h | h <;> rw [h] <;> rfl

theorem schedL_of_block {tabs : Tables} {h : Func} {b : ID} {hb : Block}
    (hbb : h.block? b = some hb) (hid : hb.id = b) :
    ((Ctx.makeL tabs h).sched[hb.id]?).join = schedule h hb := by
  rw [makeL_sched, hid]; exact sched_of_block hbb

theorem ctxL_eq {tabs : Tables} {f g : Func} (h : f.ownAux = g.ownAux) :
    Ctx.makeL tabs g =
      { (Ctx.makeL tabs f) with f := g, sched := (Ctx.makeL tabs g).sched, tys := (Ctx.makeL tabs g).tys } := by
  unfold Ctx.makeL
  cases f.lowered <;> cases g.lowered <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Ctx.make, abiParams, h]

theorem entryFrameL_eq {env : Env} {tabs : Tables} {f g : Func} (h : f.ownAux = g.ownAux)
    (args : List Val) (mem : Mem) :
    entryFrame env (Ctx.makeL tabs g) args mem =
      { entryFrame env (Ctx.makeL tabs f) args mem with
        regs := Array.replicate g.valueTab.size none } := by
  rw [ctxL_eq (tabs := tabs) h]
  rfl

end GoFV.Proof.Low.Sim
