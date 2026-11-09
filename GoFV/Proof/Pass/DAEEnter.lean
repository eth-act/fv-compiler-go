import GoFV.Proof.Pass.DAEFinish
import GoFV.Proof.Pass.DSESim

variable [GoFV.SSA.Sem.Addrs]

/-!
# dead auto elim: `Phi`s and terminators

`phis_rel`: on related registers, the target collects its `Phi`s wherever the source does, each
related (`VR.retype`), and setting them keeps the registers related (`setPhis_rel`); the source's
`Phi`s keep its register property (`phis_pr`: a `Phi` is untainted and reads an untainted
argument). `stepTerm_rel`: the terminators of two blocks with the same kind, successors and
controls on related control registers: the same edge, or related results and memories.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.DAE

variable {U : Blk → Prop}

/-- Registers related wherever the source has one. -/
def RegsRel (U : Blk → Prop) (r r' : Array (Option Val)) : Prop :=
  ∀ (z : ID) (y : Val), r[z]? = some (some y) → ∃ y', r'[z]? = some (some y') ∧ VR U y y'

/-- Collected `Phi`s, related. -/
inductive PRel (U : Blk → Prop) : List (ID × Val) → List (ID × Val) → Prop where
  | nil : PRel U [] []
  | cons {z : ID} {x x' : Val} {ps ps' : List (ID × Val)} : VR U x x' → PRel U ps ps' →
      PRel U ((z, x) :: ps) ((z, x') :: ps')

theorem RegsRel.set {r r' : Array (Option Val)} (h : RegsRel U r r') (hs : r'.size = r.size)
    (z : ID) {x x' : Val} (hx : VR U x x') : RegsRel U (r.set! z (some x)) (r'.set! z (some x')) := by
  intro z' y hy
  simp only [Array.set!_eq_setIfInBounds] at hy ⊢
  by_cases hz : z = z'
  · subst hz
    by_cases hlt : z < r.size
    · rw [Array.getElem?_setIfInBounds_self_of_lt hlt] at hy
      cases hy
      exact ⟨x', by rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hs]; exact hlt)], hx⟩
    · simp [hlt] at hy
  · rw [Array.getElem?_setIfInBounds_ne hz] at hy
    rw [Array.getElem?_setIfInBounds_ne hz]
    exact h z' y hy

theorem setPhis_rel : {ps ps' : List (ID × Val)} → PRel U ps ps' → ∀ {r r' : Array (Option Val)},
    RegsRel U r r' → r'.size = r.size → RegsRel U (setPhis ps r) (setPhis ps' r')
  | _, _, .nil, _, _, h, _ => h
  | _, _, .cons (z := z) hx t, r, r', h, hs => by
    unfold setPhis
    rw [List.foldl_cons, List.foldl_cons]
    exact setPhis_rel t (h.set hs z hx) (by simp [hs])

variable {T : ID → Option AuxRef} {E : List AuxRef}

/-- One `Phi` step in source and target. -/
theorem phiStep_rel {tabs : Tables} {f g : Func} (R : ARelD tabs f g T E) {frS frT : Frame}
    (hag : RegsRel (UE E) frS.regs frT.regs) (i : Nat) {z : ID} {o : Option (ID × Val)}
    (h : phiStep (Ctx.make tabs f) frS i z = .ok o) :
    ∃ o', phiStep (Ctx.make tabs g) frT i z = .ok o' ∧
      ((o = none ∧ o' = none) ∨ ∃ x x', o = some (z, x) ∧ o' = some (z, x') ∧ VR (UE E) x x') := by
  unfold phiStep at h ⊢
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl] at h ⊢
  cases hfv : f.value? z with
  | none => rw [hfv] at h; cases h
  | some fv =>
    rw [hfv] at h
    obtain ⟨gv, hgv, hk⟩ := R.value z fv hfv
    rw [hgv]
    dsimp only at h ⊢
    have hsg : DSE.sameV fv gv = true ∨ (elimV fv gv = true ∧ fv.op ≠ .Phi ∧ gv.op ≠ .Phi) := by
      rcases hk with ⟨hs, -⟩ | ⟨he, -⟩
      · exact .inl hs
      · obtain ⟨hop, hgc, -⟩ := elimV_spec he
        refine .inr ⟨he, ?_, by rw [hgc]; nofun⟩
        rcases hop with h' | h' | h' | h' <;> rw [h'] <;> nofun
    rcases hsg with hs | ⟨-, hf, hg⟩
    · obtain ⟨-, hop, -, -, hty, -, hargs⟩ := DSE.sameV_spec hs
      rw [hop, hargs, tys_of_value hgv, hty]
      rw [tys_of_value hfv] at h
      by_cases hph : fv.op = .Phi
      · simp only [hph, beq_self_eq_true, ↓reduceIte] at h ⊢
        cases ha : fv.args[i]? with
        | none => rw [ha] at h; cases h
        | some a =>
          rw [ha] at h
          simp only at h ⊢
          cases hx : frS.regs[a]? with
          | none => rw [hx] at h; cases h
          | some ox =>
            cases ox with
            | none => rw [hx] at h; cases h
            | some x =>
              rw [hx] at h
              simp only [Option.join] at h
              cases h
              obtain ⟨x', hx', hv⟩ := hag a x hx
              rw [hx']
              exact ⟨_, rfl, .inr ⟨_, _, rfl, rfl, hv.retype _⟩⟩
      · have h1 : (fv.op == .Phi) = false := by simpa using hph
        simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases h
        exact ⟨none, rfl, .inl ⟨rfl, rfl⟩⟩
    · have h1 : (fv.op == .Phi) = false := by simpa using hf
      have h2 : (gv.op == .Phi) = false := by simpa using hg
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases h
      exact ⟨none, rfl, .inl ⟨rfl, rfl⟩⟩

/-- **The target collects related `Phi`s.** -/
theorem phis_rel {tabs : Tables} {f g : Func} (R : ARelD tabs f g T E) {frS frT : Frame}
    (hag : RegsRel (UE E) frS.regs frT.regs) (i : Nat) :
    ∀ {l : List ID} {ps : List (ID × Val)},
      l.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps →
      ∃ ps', l.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok ps' ∧ PRel (UE E) ps ps'
  | [], ps, h => by
    simp only [List.filterMapM_nil] at h
    cases h; exact ⟨[], rfl, .nil⟩
  | z :: l, ps, h => by
    rw [List.filterMapM_cons] at h ⊢
    cases hz : phiStep (Ctx.make tabs f) frS i z with
    | panic e m => rw [hz] at h; cases h
    | stuck msg => rw [hz] at h; cases h
    | ok o =>
      rw [hz] at h
      obtain ⟨o', ho', hrel⟩ := phiStep_rel R hag i hz
      rw [ho']
      cases hl : l.filterMapM (phiStep (Ctx.make tabs f) frS i) with
      | panic e m =>
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩ <;>
          simp only [bind, Res.bind, hl] at h <;> cases h
      | stuck msg =>
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩ <;>
          simp only [bind, Res.bind, hl] at h <;> cases h
      | ok rest =>
        obtain ⟨rest', hl', hr⟩ := phis_rel R hag i hl
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩
        · simp only [bind, Res.bind, hl] at h
          cases h
          exact ⟨rest', by simp only [bind, Res.bind, hl'], hr⟩
        · simp only [bind, Res.bind, hl, pure] at h
          cases h
          exact ⟨_, by simp only [bind, Res.bind, hl', pure], .cons hv hr⟩

/-- **The source's `Phi`s keep its register property.** -/
theorem phis_pr {tabs : Tables} {f g : Func} (R : ARelD tabs f g T E)
    {ce : CheckEnv} (hwf : WF ce f) {bid : ID} {fb : Block} (hb : BlockIn f bid fb)
    {fr : Frame} (hpr : RegsP (SPr tabs f T E) fr) {i : Nat} {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps) :
    RegsP (SPr tabs f T E) { fr with regs := setPhis ps fr.regs } := by
  have hnd := hwf.valuesNodup bid fb hb
  obtain ⟨hsz, hsome, hkeep, hphi⟩ := phis_spec hnd hps
  intro z y hz
  change (setPhis ps fr.regs)[z]? = some (some y) at hz
  by_cases hin : z ∈ fb.values
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hsome z hin)
    have hv' : f.value? z = some v := hv
    by_cases hph : v.op = .Phi
    · have hlt : z < fr.regs.size := by
        rw [← hsz]
        rcases Nat.lt_or_ge z (setPhis ps fr.regs).size with h | h
        · exact h
        · rw [Array.getElem?_eq_none h] at hz; cases hz
      obtain ⟨a, x, ha, hx, hset⟩ := hphi z hin v hv' hph hlt
      rw [hset] at hz
      cases hz
      have hxpr := hpr a x hx
      refine ⟨⟨fun n hn _ => ?_, fun _ => ?_⟩, retype_idem _ _⟩
      · -- a `Phi` has no tag
        have htag := R.tag z v hv'
        unfold tagStep at htag
        rw [hn] at htag
        split at htag
        · cases htag
        · rw [hph] at htag
          simp [propOp] at htag
      · refine retype_avoids (tempU_UE E) _ (hxpr.1.untainted fun hta => ?_)
        obtain ⟨k, hk⟩ := Array.getElem?_of_mem (Array.mem_of_getElem? ha)
        rcases uses_spec hv' (R.uses z (DSE.lt_of_value? hv')) hk hta with
          ⟨-, hp, -⟩ | ⟨gv, hgv, he, -⟩
        · rw [hph] at hp; cases hp
        · obtain ⟨hop, -⟩ := elimV_spec he
          rcases hop with h' | h' | h' | h' <;> rw [h'] at hph <;> cases hph
    · rw [hkeep z (.inr ⟨v, hv', hph⟩)] at hz
      exact hpr z y hz
  · rw [hkeep z (.inl hin)] at hz
    exact hpr z y hz

/-! ## Terminators -/

theorem control_rel {G GT : Frame} {b b' : Block} (hc : b'.controls = b.controls)
    (hreg : RegsRel U G.regs GT.regs) {k : Nat} {y : Val} (h : Sem.control G b k = .ok y) :
    ∃ y', Sem.control GT b' k = .ok y' ∧ VR U y y' := by
  unfold Sem.control at h ⊢
  rw [hc]
  cases hk : b.controls[k]? with
  | none => rw [hk] at h; cases h
  | some c =>
    rw [hk] at h
    simp only [Res.ofOption] at h ⊢
    cases hy : G.regs[c]? with
    | none => rw [hy] at h; cases h
    | some o =>
      cases o with
      | none => rw [hy] at h; cases h
      | some y0 =>
        rw [hy] at h
        simp only [Option.join] at h
        cases h
        obtain ⟨y', hy', hv⟩ := hreg c _ hy
        rw [hy']
        exact ⟨y', rfl, hv⟩

theorem VRL.any_eq (p : Val → Bool) (hp : ∀ a b, VR U a b → p b = p a) :
    {as bs : List Val} → VRL U as bs → bs.any p = as.any p
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp only [List.any_cons, hp _ _ h, VRL.any_eq p hp t]

theorem succ_not_ret {b : Block} {k : Nat} {rs : List Val} {m : Mem} :
    Sem.succ b k ≠ .ok (.ret rs m) := by
  unfold Sem.succ; cases b.succs[k]? <;> simp [Res.ofOption]

theorem control_not_panic {fr : Frame} {b : Block} {k : Nat} {e : Panic} {m : Mem} :
    Sem.control fr b k ≠ .panic e m := by
  unfold Sem.control; split
  · simp only [Res.ofOption]; split <;> nofun
  · nofun

/-- **The terminators on related controls.** -/
theorem stepTerm_rel {G GT : Frame} {b b' : Block} (hk : b'.kind = b.kind) (hs : b'.succs = b.succs)
    (hid : b'.id = b.id) (hc : b'.controls = b.controls) (hreg : RegsRel U G.regs GT.regs) :
    (∀ e, stepTerm G b = .ok (.goto e) → stepTerm GT b' = .ok (.goto e)) ∧
    (∀ rs m, stepTerm G b = .ok (.ret rs m) →
      ∃ rs' m', stepTerm GT b' = .ok (.ret rs' m') ∧ VRL U rs rs' ∧ Mem.EqOff U m m') := by
  have hsucc : ∀ k, Sem.succ b' k = Sem.succ b k := fun k => by unfold Sem.succ; rw [hs, hid]
  have hct : ∀ k y, Sem.control G b k = .ok y → ∃ y', Sem.control GT b' k = .ok y' ∧ VR U y y' :=
    fun k y h => control_rel hc hreg h
  -- the same step when the source's first control is neither a memory nor a tuple
  have same : ∀ n, stepTerm G b = .ok n → b.kind ≠ .Ret → stepTerm GT b' = .ok n := by
    intro n h hR
    unfold stepTerm at h ⊢
    rw [hk]
    simp only [hsucc, hid]
    cases hkb : b.kind <;> simp only [hkb] at h ⊢
    all_goals first
      | exact h
      | exact absurd hkb hR
      | (cases hc0 : Sem.control G b 0 with
          | ok y =>
            obtain ⟨y', hy', hv⟩ := hct 0 y hc0
            rw [hc0] at h
            rw [hy']
            cases y with
            | bool c => rw [hv.eq nofun nofun]; exact h
            | int w x => rw [hv.eq nofun nofun]; exact h
            | _ => simp [bind, Res.bind] at h
          | panic _ _ => exact absurd hc0 control_not_panic
          | stuck _ => rw [hc0] at h; cases h)
      | cases h
  refine ⟨fun e h => ?_, fun rs m h => ?_⟩
  · by_cases hR : b.kind = .Ret
    · unfold stepTerm at h
      rw [hR] at h
      cases hc0 : Sem.control G b 0 with
      | ok y =>
        rw [hc0] at h
        simp only [bind, Res.bind] at h
        split at h
        · split at h
          · split at h <;> cases h
          · cases h
        · cases h
      | panic _ _ => exact absurd hc0 control_not_panic
      | stuck _ => rw [hc0] at h; cases h
    · exact same _ h hR
  · by_cases hR : b.kind = .Ret
    · unfold stepTerm at h ⊢
      rw [hR] at h
      rw [hk, hR]
      cases hc0 : Sem.control G b 0 with
      | ok y =>
        obtain ⟨y', hy', hv⟩ := hct 0 y hc0
        rw [hc0] at h
        rw [hy']
        simp only [bind, Res.bind] at h ⊢
        cases y with
        | tuple vs =>
          obtain ⟨ws, rfl, hws⟩ := hv.tuple_inv
          simp only at h ⊢
          rcases hws.getLast? with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
          · rw [h1] at h; cases h
          · rw [h1] at h
            rw [h2]
            cases a with
            | mem M =>
              obtain ⟨M', rfl, hM⟩ := ha.mem_inv
              simp only at h ⊢
              rw [VRL.any_eq _ (fun a b h => by cases h <;> rfl) hws.dropLast]
              split at h
              · cases h
              · cases h
                rename_i hp
                simp only [hp, Bool.false_eq_true, ↓reduceIte]
                exact ⟨_, _, rfl, hws.dropLast, hM⟩
            | _ => simp at h
        | _ => simp at h
      | panic _ _ => exact absurd hc0 control_not_panic
      | stuck _ => rw [hc0] at h; cases h
    · exact ⟨rs, m, same _ h hR, VRL.refl rs, EqOff.refl U m⟩

end GoFV.Proof.DAE
