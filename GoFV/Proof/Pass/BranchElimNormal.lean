import GoFV.Proof.Pass.BranchElimSetup

variable [GoFV.SSA.Sem.Addrs]

/-!
# branchelim: a block outside the diamond

`normal_step`: a block of `f` other than `dom`, `post` and the arms is unchanged in `g`; from
frames that agree outside the arm values, both functions take the same step, to frames that
again agree outside the arm values (no such block reads an arm value, `usesOK`).
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof

variable {f g : Func} {s : Site}

namespace Setup

variable (S : Setup f g s)
include S

theorem normal_step {tabs : Tables} {env : Env} {frS frT : Frame} {b : ID} {i : Nat}
    (hb : b ∈ f.blocks) (hbd : b ≠ s.dom) (hbp : b ≠ s.post) (ha0 : s.arm0 ≠ some b)
    (ha1 : s.arm1 ≠ some b)
    (hfr : frT = { frS with regs := frT.regs }) (hsz : frT.regs.size = frS.regs.size)
    (hag : ∀ a, s.armVal f a = false → frT.regs[a]? = frS.regs[a]?) :
    (∀ G e, blockStep env (Ctx.make tabs f) frS b i = .goto G e →
      ∃ GT, blockStep env (Ctx.make tabs g) frT b i = .goto GT e ∧
        GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
        ∀ a, s.armVal f a = false → GT.regs[a]? = G.regs[a]?) ∧
    (∀ rs m, blockStep env (Ctx.make tabs f) frS b i = .ret rs m →
      blockStep env (Ctx.make tabs g) frT b i = .ret rs m) ∧
    (∀ e m, blockStep env (Ctx.make tabs f) frS b i = .panic e m →
      blockStep env (Ctx.make tabs g) frT b i = .panic e m) := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hreg : s.regionBlock b = false := by
    unfold Site.regionBlock
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact ⟨⟨⟨hbd, hbp⟩, ha0⟩, ha1⟩
  obtain ⟨fb, gb, hfb, hgb, hba⟩ := block_spec S.rel hwf hb hreg
  have hown := valuesOwn hwf hb hfb
  have hnd := hwf.valuesNodup b fb ⟨hb, hfb⟩
  have hnotpost : ∀ x ∈ fb.values, s.postVal f x = false := fun x hx =>
    Bool.eq_false_iff.2 fun hp => hbp (S.postVal_block hb hfb hx hp)
  have hnotarm : ∀ x ∈ fb.values, s.armVal f x = false := fun x hx =>
    Bool.eq_false_iff.2 fun ha => (S.armVal_block hb hfb hx ha).elim (fun h => ha0 h) (fun h => ha1 h)
  have hid : ∀ x ∈ fb.values, ∀ fv, f.value? x = some fv → fv.id = x := fun x hx fv hfv => by
    obtain ⟨v, hv, hvid⟩ := hown x hx
    rw [hfv] at hv; cases hv; exact hvid
  have hca : CtxAgree (Ctx.make tabs f) (Ctx.make tabs g) fb.values.toList :=
    S.ctxAgree (fun x hx _ _ hp => absurd hp (by rw [hnotpost x (Array.mem_toList_iff.1 hx)]; simp))
      (fun x hx => hid x (Array.mem_toList_iff.1 hx))
  -- arguments read in the block are no arm values
  obtain ⟨huse, hctl⟩ := uses_spec S.rel hb hfb
  have hargs : ∀ x ∈ fb.values, ∀ v, f.value? x = some v → ∀ a ∈ v.args, s.armVal f a = false := by
    intro x hx v hv a ha
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha
    have hu := huse x hx v hv k a hk
    unfold Site.useOK at hu
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
      Option.some.injEq] at hu
    unfold Site.armVal
    obtain ⟨h0, h1⟩ := hu
    rcases h0 with (h0 | h0) | h0
    · rcases h1 with (h1 | h1) | h1
      · rw [h0, h1]; rfl
      · exact absurd h1 ha1
      · exact absurd h1.1.1 hbp
    · exact absurd h0 ha0
    · exact absurd h0.1.1 hbp
  have hsched : schedule g gb = schedule f fb := by
    unfold schedule
    rw [show schedNodes g gb = schedNodes f fb from
      schedNodes_semEq hba.values fun x hx => hca.value x (Array.mem_toList_iff.2 hx)]
  have hE := enterBlock_agree (env := env) (i := i) (X := fun a => s.armVal f a = true) hba hca
    (fun z hz v hv => hid z hz v hv)
    (fun z hz v hv _ a ha => by
      rw [hargs z hz v hv a (Array.mem_of_getElem? ha)]; simp)
    (by
      change ((Ctx.make tabs g).sched[fb.id]?).join = ((Ctx.make tabs f).sched[fb.id]?).join
      obtain ⟨b', hb', hbid⟩ := hwf.blockId b hb
      rw [hfb] at hb'; cases hb'
      rw [hbid, sched_of_block hgb, sched_of_block hfb, hsched])
    (fun o ho => by
      obtain ⟨b', hb', hbid⟩ := hwf.blockId b hb
      rw [hfb] at hb'; cases hb'
      rw [hbid, sched_of_block hfb] at ho
      obtain ⟨-, -, omem⟩ := schedule_topo hown hnd ho
      have hsub : ∀ x ∈ o.toList, x ∈ fb.values.toList := fun x hx =>
        Array.mem_toList_iff.2 ((omem x).1 hx).1
      refine ⟨hca.mono hsub, fun x hx => ⟨?_, fun v hv a ha => ?_⟩⟩
      · show ¬ s.armVal f x = true
        rw [hnotarm x ((omem x).1 hx).1]; simp
      · show ¬ s.armVal f a = true
        rw [hargs x ((omem x).1 hx).1 v hv a ha]; simp)
    hfr hsz (fun a ha => hag a (by simpa using ha))
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl, hfb, hgb]
  cases hen : enterBlock env (Ctx.make tabs f) frS fb i with
  | stuck msg => exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  | panic e' m' =>
    rw [hE.2 _ _ hen]
    exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => h⟩
  | ok G1 =>
    obtain ⟨GT1, hT1, hfr1, hsz1, hag1⟩ := hE.1 G1 hen
    rw [hT1]
    have hst : stepTerm GT1 gb = stepTerm G1 fb := stepTerm_agree hba fun c hc => hag1 c (by
      rw [hctl c hc]; simp)
    simp only
    rw [hst]
    cases hs : stepTerm G1 fb with
    | ok n =>
      cases n with
      | goto e =>
        refine ⟨fun G e' h => ?_, fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
        cases h
        exact ⟨GT1, rfl, hfr1, hsz1, fun a ha => hag1 a (by simpa using ha)⟩
      | ret rs m => exact ⟨fun _ _ h => (nomatch h), fun _ _ h => h, fun _ _ h => (nomatch h)⟩
    | panic e m => exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => h⟩
    | stuck msg => exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

end Setup

end GoFV.Proof.BranchElim
