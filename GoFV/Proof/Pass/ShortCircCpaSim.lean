import GoFV.Proof.Pass.ShortCircCpaMid
import GoFV.Proof.Pass.PhiOptForm
import GoFV.Proof.Merge

variable [GoFV.SSA.Sem.Addrs]

/-!
# short circuit, step 1: replacing the `If` controls in `Phi`s by constants

`g` and `mid f g` (the result with `f`'s arguments) differ only in `Phi` arguments that `Just`
justifies, so their runs are equal (`runLoop_eq`): in equal frames, a `Phi` entered along edge
`k` from an `If` on `c` reads the constant `c` holds there. The invariant (`Inv`): along the
incoming edge, the control of an `If` predecessor holds the edge's boolean (`EdgeFact`, from the
predecessor's terminator), and after the entry block every constant of the entry holds its value
(`ConstsSet`, from the entry's schedule; no other block writes it).
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

variable {tabs : Tables} {f g : Func}

/-- The constants of `g`'s entry hold their values. -/
def ConstsSet (tabs : Tables) (g : Func) (fr : Frame) : Prop :=
  ∀ c d, ConstOK tabs g c d → fr.regs[c]? = some (some (.bool d))

/-- Entered along edge `i` of `y`: an `If` predecessor's control holds the edge's boolean. -/
def EdgeFact (g : Func) (fr : Frame) (y : ID) (i : Nat) : Prop :=
  ∀ Y e P c0, g.block? y = some Y → Y.preds[i]? = some e → g.block? e.b = some P →
    P.kind = .If → P.controls[0]? = some c0 → fr.regs[c0]? = some (some (.bool (e.i == 0)))

/-- The invariant at a block entry. -/
def Inv (tabs : Tables) (g : Func) (fr : Frame) (y : ID) (i : Nat) : Prop :=
  y ∈ g.blocks ∧ fr.regs.size = g.valueTab.size ∧ EdgeFact g fr y i ∧
    (y ≠ g.entry → ConstsSet tabs g fr)

/-- An `If` that continues along `e`: `e` is successor `k`, and the control holds `k = 0`. -/
theorem stepTerm_if_goto {G : Frame} {B : Block} {c : ID} (hk : B.kind = .If)
    (hc : B.controls[0]? = some c) {e : Edge} (h : stepTerm G B = .ok (.goto e)) :
    ∃ k, B.succs[k]? = some e ∧ G.regs[c]? = some (some (.bool (k == 0))) := by
  unfold stepTerm at h
  rw [hk] at h
  cases hctl : Sem.control G B 0 with
  | ok v =>
    rw [hctl] at h
    simp only [bind, Res.bind] at h
    have hv : G.regs[c]? = some (some v) := by
      unfold Sem.control at hctl
      simp only [hc] at hctl
      cases hr : G.regs[c]? with
      | none => simp [hr, Res.ofOption] at hctl
      | some o =>
        cases o with
        | none => simp [hr, Res.ofOption] at hctl
        | some v' => simp [hr, Res.ofOption] at hctl; rw [hctl]
    split at h
    · obtain ⟨e', he, he'⟩ := Dead.succ_ok h
      cases he'
      exact ⟨0, he, by rw [hv]; rfl⟩
    · obtain ⟨e', he, he'⟩ := Dead.succ_ok h
      cases he'
      exact ⟨1, he, by rw [hv]; rfl⟩
    · cases h
  | panic e m => rw [hctl] at h; cases h
  | stuck msg => rw [hctl] at h; cases h

theorem filterMapM_loop_congr {α β : Type} {F G : α → Res (Option β)} :
    ∀ (l : List α) (acc : List β), (∀ a ∈ l, F a = G a) →
      List.filterMapM.loop F l acc = List.filterMapM.loop G l acc
  | [], _, _ => rfl
  | a :: l, acc, h => by
    simp only [List.filterMapM.loop, h a List.mem_cons_self]
    congr 1; funext b
    cases b <;> exact filterMapM_loop_congr l _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

namespace CRel

variable (C : CRel tabs f g)
include C

/-- `mid f g` has `g`'s values up to the arguments of `Phi`s. -/
theorem mid_rel (x : ID) :
    ((mid f g).value? x = none ↔ g.value? x = none) ∧
      ∀ v, g.value? x = some v → ∃ mv, (mid f g).value? x = some mv ∧ mv.op = v.op ∧
        mv.id = v.id ∧ mv.type = v.type ∧ (v.op ≠ .Phi → mv = v) := by
  refine ⟨?_, fun v hv => ?_⟩
  · rw [mid_value]
    cases g.value? x <;> cases f.value? x <;> simp
  · cases hfv : f.value? x with
    | none => exact ⟨v, by rw [C.mid_of_none hfv, hv], rfl, rfl, rfl, fun _ => rfl⟩
    | some fv =>
      obtain ⟨gv, hgv, hm, heq⟩ := C.mid_of_f hfv
      rw [hv] at hgv; cases hgv
      obtain ⟨h1, h2, -, -, -, h6, -⟩ := value_fields heq
      refine ⟨_, hm, h2.symm, h1.symm, h6.symm, fun hph => ?_⟩
      obtain ⟨gv', hgv', -, hsz, hargs⟩ := C.value x fv hfv
      rw [hv] at hgv'; cases hgv'
      have ha : v.args = fv.args := args_eq_of hsz fun k a hk => by
        obtain ⟨ga, hga, hor⟩ := hargs k a hk
        rcases hor with rfl | ⟨hp, -⟩
        · exact hga
        · exact absurd (h2 ▸ hp) hph
      rw [← value_eta heq, ← ha]

theorem tys_eq : (Ctx.make tabs g).tys = (Ctx.make tabs (mid f g)).tys := by
  simp only [Ctx.make, mid]
  apply Array.ext (by simp)
  intro x h1 h2
  simp only [Array.getElem_map, Array.getElem_mapIdx]
  split
  · rename_i gv fv hgv _; rw [hgv]; rfl
  · rfl

theorem schedNodes_eq (B : Block) : schedNodes (mid f g) B = schedNodes g B := by
  unfold schedNodes
  congr 1
  funext id
  obtain ⟨h0, hs⟩ := C.mid_rel id
  cases hg : g.value? id with
  | none => rw [h0.2 hg]
  | some v =>
    obtain ⟨mv, hm, hop, hid, -, hne⟩ := hs v hg
    rw [hm]
    by_cases hph : v.op = .Phi
    · simp [hop, hph]
    · rw [hne hph]

theorem sched_eq : (Ctx.make tabs g).sched = (Ctx.make tabs (mid f g)).sched := by
  simp only [Ctx.make, mid]
  congr 1
  funext o
  cases o with
  | none => rfl
  | some B =>
    simp only [Option.bind_some]
    unfold schedule
    rw [show schedNodes { g with valueTab := _ } B = schedNodes g B from C.schedNodes_eq B]

theorem evalValue_eq (env : Env) (fr : Frame) (v : Value) :
    evalValue env (Ctx.make tabs g) fr v = evalValue env (Ctx.make tabs (mid f g)) fr v := by
  have ht := C.tys_eq
  generalize hG : Ctx.make tabs g = cG at ht
  generalize hM : Ctx.make tabs (mid f g) = cM at ht
  have h1 : cG.tabs = cM.tabs := by rw [← hG, ← hM]; rfl
  have h4 : cG.params = cM.params := by rw [← hG, ← hM]; rfl
  have h8 : cG.act = cM.act := by rw [← hG, ← hM]; rfl
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := cG
  obtain ⟨_, _, _, _, _, _, _, _, _⟩ := cM
  dsimp only at h1 ht h4 h8
  subst h1 ht h4 h8
  rfl

theorem evalAll_eq (env : Env) :
    ∀ (o : List ID) (fr : Frame), (∀ x ∈ o, (mid f g).value? x = g.value? x) →
      evalAll env (Ctx.make tabs g) fr o = evalAll env (Ctx.make tabs (mid f g)) fr o
  | [], _, _ => rfl
  | x :: o, fr, h => by
    rw [evalAll_cons, evalAll_cons]
    unfold stepV
    rw [show (Ctx.make tabs (mid f g)).f.value? x = (Ctx.make tabs g).f.value? x from
      h x List.mem_cons_self]
    cases (Ctx.make tabs g).f.value? x with
    | none => rfl
    | some v =>
      simp only
      rw [C.evalValue_eq env fr v]
      cases evalValue env (Ctx.make tabs (mid f g)) fr v with
      | ok y => exact evalAll_eq env o _ fun z hz => h z (List.mem_cons_of_mem _ hz)
      | panic e m => rfl
      | stuck msg => rfl

variable {ce : CheckEnv}

/-- A value listed in block `y` of `g`: a value of `f` listed in `y`, or a new constant. -/
theorem listed_g (hwf : WF ce f) {y : ID} {Y : Block} (hY : BlockIn g y Y) {z : ID}
    (hz : z ∈ Y.values) :
    ∃ b, f.block? y = some b ∧ ((∃ fv, f.value? z = some fv ∧ fv.block = y ∧ z ∈ b.values ∧
      BlockIn f y b) ∨ (y = f.entry ∧ ∃ w, g.value? z = some w ∧ w.op = .ConstBool)) := by
  obtain ⟨fE, news, E⟩ := C.ext_g
  obtain ⟨b, hb, -, hl⟩ := E.listing hwf hY hz
  refine ⟨b, hb, ?_⟩
  rcases hl with ⟨hbf, hx⟩ | ⟨rfl, hn⟩
  · obtain ⟨fv, hfv, -, hblk⟩ := hwf.valueId y b hbf z hx
    exact .inl ⟨fv, hfv, hblk, hx, hbf⟩
  · obtain ⟨-, w, hw, hop, -⟩ := E.newv z hn
    exact .inr ⟨rfl, w, hw, hop⟩

/-- **The `Phi`s read equal values.** -/
theorem phiStep_eq (hwf : WF ce f) {fr : Frame} {y : ID} {Y : Block} {i : Nat}
    (hY : BlockIn g y Y) (hI : Inv tabs g fr y i) {z : ID} (hz : z ∈ Y.values) :
    phiStep (Ctx.make tabs g) fr i z = phiStep (Ctx.make tabs (mid f g)) fr i z := by
  obtain ⟨fE, news, E⟩ := C.ext_g
  have hwg := E.wf hwf
  obtain ⟨h0, hs⟩ := C.mid_rel z
  unfold phiStep
  change (match g.value? z with | some v => _ | none => _) =
    (match (mid f g).value? z with | some v => _ | none => _)
  cases hg : g.value? z with
  | none => rw [h0.2 hg]
  | some v =>
    obtain ⟨mv, hm, hop, -, -, hne⟩ := hs v hg
    rw [hm]
    by_cases hph : v.op = .Phi
    · simp only [hop, hph, beq_self_eq_true, ite_true]
      obtain ⟨b, hb, hl⟩ := C.listed_g hwf hY hz
      rcases hl with ⟨fv, hfv, hfb, hzb, hbf⟩ | ⟨-, w, hw, hwop⟩
      · obtain ⟨gv, hgv, hmid, heq⟩ := C.mid_of_f hfv
        rw [hg] at hgv; cases hgv
        rw [hm] at hmid; cases hmid
        obtain ⟨gv', hgv', -, hsz, hargs⟩ := C.value z fv hfv
        rw [hg] at hgv'; cases hgv'
        show (match v.args[i]? with | some a => _ | none => _) =
          (match fv.args[i]? with | some a => _ | none => _)
        cases hfa : fv.args[i]? with
        | none =>
          have : v.args[i]? = none := by
            rw [Array.getElem?_eq_none_iff] at hfa ⊢; omega
          rw [this]
        | some fa =>
          obtain ⟨ga, hga, hor⟩ := hargs i fa hfa
          rw [hga]
          rcases hor with rfl | ⟨-, Y', e, P, hY', he, hP, hPk, hPc, hc⟩
          · rw [C.tys_eq]
          · rw [hfb, hb] at hY'; cases hY'
            obtain ⟨-, hfr, hedge, hcs⟩ := hI
            have hgb : g.block? y = some (adj f news y b) := by rw [E.block, hb]; rfl
            rw [hY.2] at hgb; cases hgb
            have he' : (adj f news y b).preds[i]? = some e := by rw [adj_fields.2.2.1]; exact he
            have hgP : g.block? e.b = some (adj f news e.b P) := by rw [E.block, hP]; rfl
            have hfa' := hedge _ e _ fa hY.2 he' hgP (by rw [adj_fields.2.2.2.1]; exact hPk)
              (by rw [adj_fields.2.2.2.2]; exact hPc)
            have hne : y ≠ g.entry := fun hy => by
              have := hwg.entryPreds (adj f news y b) (by rw [← hy]; exact hY.2)
              rw [adj_fields.2.2.1] at this
              have hl := (Array.getElem?_eq_some_iff.1 he).1
              omega
            have hga' := hcs hne ga _ hc
            simp only [hfa', hga', Option.join_some, C.tys_eq]
      · rw [hg] at hw; cases hw
        rw [hwop] at hph; cases hph
    · rw [hne hph]
      have : (v.op == .Phi) = false := by simpa using hph
      simp only [this, Bool.false_eq_true, ite_false]

/-- **A block entry is the same in `g` and `mid f g`.** -/
theorem enter_eq (hwf : WF ce f) (env : Env) {fr : Frame} {y : ID} {Y : Block} {i : Nat}
    (hY : BlockIn g y Y) (hI : Inv tabs g fr y i) :
    enterBlock env (Ctx.make tabs g) fr Y i = enterBlock env (Ctx.make tabs (mid f g)) fr Y i := by
  obtain ⟨fE, news, E⟩ := C.ext_g
  have hwg := E.wf hwf
  rw [enterBlock_eq, enterBlock_eq]
  have hphis : List.filterMapM (phiStep (Ctx.make tabs g) fr i) Y.values.toList =
      List.filterMapM (phiStep (Ctx.make tabs (mid f g)) fr i) Y.values.toList :=
    by unfold List.filterMapM; exact filterMapM_loop_congr _ _ fun z hz =>
      C.phiStep_eq hwf hY hI (Array.mem_toList_iff.1 hz)
  rw [hphis, ← C.sched_eq]
  cases List.filterMapM (phiStep (Ctx.make tabs (mid f g)) fr i) Y.values.toList with
  | panic e m => rfl
  | stuck msg => rfl
  | ok ps =>
    show (Res.ofOption _ _).bind _ = (Res.ofOption _ _).bind _
    obtain ⟨Y', hY', hid⟩ := hwg.blockId y hY.1
    rw [hY.2] at hY'; cases hY'
    rw [hid, sched_of_block hY.2]
    cases hs : schedule g Y with
    | none => rfl
    | some o =>
      show evalAll env _ _ o.toList = evalAll env _ _ o.toList
      have ht := schedule_topo (valuesOwn hwg hY.1 hY.2) (hwg.valuesNodup y Y hY) hs
      refine C.evalAll_eq env o.toList _ fun x hx => ?_
      obtain ⟨-, v, hv, hph⟩ := (ht.2.2 x).1 hx
      obtain ⟨-, hrel⟩ := C.mid_rel x
      obtain ⟨mv, hm, -, -, -, hne⟩ := hrel v hv
      rw [hm, hv, hne hph]

/-- **The invariant at the next block.** -/
theorem inv_next (hwf : WF ce f) (env : Env) {fr fr' : Frame} {y : ID} {Y : Block} {i : Nat}
    (hY : BlockIn g y Y) (hI : Inv tabs g fr y i)
    (he : enterBlock env (Ctx.make tabs g) fr Y i = .ok fr') {e : Edge}
    (hst : stepTerm fr' Y = .ok (.goto e)) : Inv tabs g fr' e.b e.i := by
  obtain ⟨fE, news, E⟩ := C.ext_g
  have hwg := E.wf hwf
  obtain ⟨hym, hsz, -, hcs⟩ := hI
  obtain ⟨Y', hY', hid⟩ := hwg.blockId y hY.1
  rw [hY.2] at hY'; cases hY'
  have hnd := hwg.valuesNodup y Y hY
  obtain ⟨frP, o, ho, hev, hfrP, hszP, -, hkeep, -⟩ := enterBlock_spec hnd he
  rw [hid, sched_of_block hY.2] at ho
  have ht := schedule_topo (valuesOwn hwg hY.1 hY.2) hnd ho
  obtain ⟨-, hsz', hout, hin⟩ := evalAll_spec ht.1 (by exact ht.2.1) (by rw [hszP, hsz]; rfl) hev
  have hem : e ∈ Y.succs := stepTerm_goto_mem hst
  obtain ⟨k0, hk0⟩ := Array.mem_iff_getElem?.1 hem
  refine ⟨(hwg.succLink y Y hY k0 e hk0).1, by rw [hsz', hszP, hsz], ?_, fun _ => ?_⟩
  · intro Y2 e2 P c0 hY2 he2 hP hPk hPc
    have hPY : e2 = ⟨y, k0⟩ ∧ P = Y := by
      obtain ⟨-, C2, hC2, hpred⟩ := hwg.succLink y Y hY k0 e hk0
      rw [hY2] at hC2; cases hC2
      rw [he2] at hpred; cases hpred
      rw [hY.2] at hP; cases hP
      exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := hPY
    obtain ⟨k, hk, hc⟩ := stepTerm_if_goto hPk hPc hst
    obtain ⟨-, C2, hC2, hpred⟩ := hwg.succLink y P hY k e hk
    rw [hY2] at hC2; cases hC2
    rw [he2] at hpred; cases hpred
    exact hc
  · intro c d hc
    obtain ⟨hcE, w, hw, hop, hargs, hwid, hwb, hd, hty⟩ := hc
    by_cases hye : y = g.entry
    · -- the entry's schedule evaluates the constant
      subst hye
      rw [valsOf_eq hY.2] at hcE
      obtain ⟨v, r, hv, hr, hev'⟩ := hin c ((ht.2.2 c).2 ⟨hcE, w, hw, by rw [hop]; decide⟩)
      have hv' : g.value? c = some v := hv
      rw [hw] at hv'; cases hv'
      rw [PhiOpt.evalValue_nil hargs (by unfold PhiOpt.formOp; simp [hop])] at hev'
      cases hev'
      rw [hr, hop, hwid, tys_of_value hw, hty, ← hd]
      rfl
    · -- another block does not write it
      have hcY : c ∉ Y.values := fun hm => hye (by
        have hEb := hwg.entry
        obtain ⟨gE, hgE⟩ : ∃ gE, g.block? g.entry = some gE := by
          obtain ⟨gE, h, -⟩ := hwg.blockId g.entry hEb; exact ⟨gE, h⟩
        rw [valsOf_eq hgE] at hcE
        exact hwg.valueOnce y Y g.entry gE hY ⟨hEb, hgE⟩ c hm hcE)
      have hco : c ∉ o.toList := fun hm => hcY ((ht.2.2 c).1 hm).1
      rw [hout c hco, hkeep c (.inl hcY)]
      exact hcs hye c d ⟨hcE, w, hw, hop, hargs, hwid, hwb, hd, hty⟩

/-- **`g` and `mid f g` run alike.** -/
theorem runLoop_eq (hwf : WF ce f) (env : Env) :
    ∀ (fuel : Nat) (fr : Frame) (y : ID) (i : Nat), Inv tabs g fr y i →
      runLoop env (Ctx.make tabs g) fuel fr y i = runLoop env (Ctx.make tabs (mid f g)) fuel fr y i
  | 0, _, _, _, _ => rfl
  | n + 1, fr, y, i, hI => by
    rw [runLoop_succ, runLoop_succ]
    change (match g.block? y with | none => _ | some b => _) =
      (match g.block? y with | none => _ | some b => _)
    cases hY : g.block? y with
    | none => rfl
    | some Y =>
      simp only
      have hYin : BlockIn g y Y := ⟨hI.1, hY⟩
      rw [← C.enter_eq hwf env hYin hI]
      cases he : enterBlock env (Ctx.make tabs g) fr Y i with
      | panic e m => rfl
      | stuck msg => rfl
      | ok fr' =>
        simp only
        cases hst : stepTerm fr' Y with
        | ok nx =>
          cases nx with
          | goto e => exact runLoop_eq hwf env n fr' e.b e.i (C.inv_next hwf env hYin hI he hst)
          | ret rs m => rfl
        | panic e m => rfl
        | stuck msg => rfl

/-- **`g` refines `mid f g`** (they run alike). -/
theorem refines_mid (hwf : WF ce f) : Refines tabs g tabs (mid f g) := by
  obtain ⟨fE, news, E⟩ := C.ext_g
  have hwg := E.wf hwf
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  have hrun : run env tabs g args mem fuel = run env tabs (mid f g) args mem fuel := by
    unfold run runCtx
    have hent : entryFrame env (Ctx.make tabs (mid f g)) args mem =
        entryFrame env (Ctx.make tabs g) args mem := by
      unfold entryFrame
      simp only [Ctx.make, mid, Array.size_mapIdx]
      rfl
    have hp : (Ctx.make tabs (mid f g)).params = (Ctx.make tabs g).params := rfl
    have ho : (Ctx.make tabs (mid f g)).outs = (Ctx.make tabs g).outs := rfl
    have ha : (Ctx.make tabs (mid f g)).act = (Ctx.make tabs g).act := rfl
    have he : (Ctx.make tabs (mid f g)).f.entry = (Ctx.make tabs g).f.entry := rfl
    rw [hp, ho, ha, he, hent]
    split
    · rfl
    · congr 1
      refine C.runLoop_eq hwf env fuel _ _ _ ⟨hwg.entry, ?_, ?_, fun h => absurd rfl h⟩
      · simp [entryFrame, Ctx.make]
      · intro Y e P c0 hY he
        have := hwg.entryPreds Y hY
        have hl := (Array.getElem?_eq_some_iff.1 he).1
        omega
  rw [hrun]
  exact OutcomeRefines.refl hd

end CRel

end GoFV.Proof.ShortCirc
