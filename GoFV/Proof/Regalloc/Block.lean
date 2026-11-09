import GoFV.Proof.Regalloc.Steps
import GoFV.Proof.Low.SimBase
import GoFV.Proof.Pass.DeadRelL
import GoFV.Proof.Pass.TrimLoc

variable [GoFV.SSA.Sem.Addrs]

/-!
# Regalloc checker soundness, stage 4: blocks (`docs/plans/regalloc-check.md` §5)

* `walk_sim`: the checker's walk over a target block's values (`walk`) relates `runSched`'s
  evaluation of the block's schedule (`evalAllL`) to `runLoc`'s of the target values
  (`enterListLoc`): both panic alike, or both continue with `Match` of the walk's facts; frame
  constants the target does not issue run in the source alone (`kAll_sim`);
* `phiEdge_sim`: the source's `Phi`s along an edge the checker accepted (`phiEdge`) keep `Match`
  with the edge's facts; `sub_sound`: facts the certificate claims follow;
* `term_sim`: a terminator `termOK` accepts continues alike.
-/

namespace GoFV.Proof.RA

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RegallocCheck GoFV.Proof.Low.Sim

variable {tabs : Tables} {f g : Func}

/-! ## Related results -/

/-- A source result and a target result: the target does what the source does when the source
continues (related by `P`) or panics. -/
def SimRes {α β : Type} (P : α → β → Prop) : Res α → Res β → Prop
  | .ok x, t => ∃ y, t = .ok y ∧ P x y
  | .panic e m, t => t = .panic e m
  | .stuck _, _ => True

theorem SimRes.bind {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop} {r : Res α}
    {t : Res β} {k : α → Res γ} {k' : β → Res δ} (h : SimRes P r t)
    (hk : ∀ x y, P x y → SimRes Q (k x) (k' y)) : SimRes Q (Res.bind r k) (Res.bind t k') := by
  cases r with
  | ok x => obtain ⟨y, rfl, hP⟩ := h; exact hk x y hP
  | panic e m => cases h; exact rfl
  | stuck msg => trivial

theorem exc_bind_ok {ε α β : Type} {x : Except ε α} {k : α → Except ε β} {y : β}
    (h : (x >>= k) = .ok y) : ∃ a, x = .ok a ∧ k a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem res_bind_ok {α β : Type} {x : Res α} {k : α → Res β} {y : β}
    (h : (x >>= k) = .ok y) : ∃ a, x = .ok a ∧ k a = .ok y := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | panic e m => cases h
  | stuck msg => cases h

theorem evalAllL_append' (md : LMode) (env : Env) (ctx : Ctx) (l1 l2 : List ID) (fr : Frame) :
    evalAllL md env ctx fr (l1 ++ l2) =
      (evalAllL md env ctx fr l1).bind fun fr' => evalAllL md env ctx fr' l2 := by
  rw [evalAllL_append]
  cases evalAllL md env ctx fr l1 <;> rfl

theorem enterListLoc_cons' {env : Env} {lc : LocCtx} {s : LocState} {d : ID} {ds : List ID}
    {w : Value} (hw : lc.ctx.f.value? d = some w) :
    enterListLoc env lc s (d :: ds) =
      (stepLoc env lc s w).bind fun s' => enterListLoc env lc s' ds := by
  simp only [enterListLoc, hw]
  cases stepLoc env lc s w <;> rfl

/-! ## Source frame constants -/

theorem redefine_K {cx : Cx} {S : Facts} {u : ID} (hk : cx.isK u = true) : cx.redefine S u = S := by
  unfold Cx.redefine; rw [if_pos hk]

/-- `Match` after source value `d` took `y`, given the facts. -/
theorem upd_match {env : Env} {frA : Frame} {S T : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {d : ID} {u : Value} {y : Val}
    (hu : f.value? d = some u) (hud : u.id = d)
    (hev : evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u = .ok y)
    (hT : ∀ F ∈ T, FactOK (Cx.make tabs f g) env frA (upd fr d y) s F) :
    Match (Cx.make tabs f g) env frA T (upd fr d y) s := by
  have hlt : d < fr.regs.size := by rw [h.fsize]; exact value?_lt hu
  have hys : (Cx.make tabs f g).md.retype ((Cx.make tabs f g).fty d) y = y := by
    have := evalValueL_shaped hev
    rw [hud] at this; exact this
  refine { facts := hT, fr_eq := upd_fr_eq h.fr_eq d y, s_fr := h.s_fr, shaped := ?_,
           kinv := ?_, regs := h.regs, fsize := by rw [upd_size]; exact h.fsize }
  · intro id x hx
    by_cases hid : id = d
    · subst hid
      rw [upd_self' hlt] at hx
      cases hx
      exact hys
    · rw [upd_ne hid] at hx; exact h.shaped id x hx
  · intro id x hk hx
    by_cases hid : id = d
    · subst hid
      rw [upd_self' hlt] at hx
      cases hx
      exact eval_kval h hk hu hev
    · rw [upd_ne hid] at hx; exact h.kinv id x hk hx

/-- A source frame constant keeps `Match`. -/
theorem kRun_match {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {d : ID} {u : Value} {y : Val}
    (hk : (Cx.make tabs f g).isK d = true) (hu : f.value? d = some u)
    (hev : evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u = .ok y) :
    Match (Cx.make tabs f g) env frA S (upd fr d y) s := by
  obtain ⟨v, hv, hid, -⟩ := isK_spec hk
  rw [show (Cx.make tabs f g).f = f from rfl, hu] at hv
  cases hv
  exact upd_match h hu hid hev fun F hF =>
    factOK_keep h hu hid hev (by rw [redefine_K hk]; exact hF) (fun _ => rfl)

/-- A frame constant's op never panics. -/
theorem evalValueL_K_ne_panic {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {e : Panic} {m : Mem} (hk : kOp v.op = true) : evalValueL md env ctx fr v ≠ .panic e m := by
  intro h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | ok L =>
    rw [evalValueL_eq (mapM_ofOption_forall₂ hm), evalOpL_kop_eq hk] at h
    cases h
  | panic e' m' => exact mapM_ofOption_ne_panic hm
  | stuck msg =>
    unfold evalValueL at h
    change Res.bind _ _ = _ at h
    rw [hm] at h; cases h

theorem sc_value {x : ID} : (Cx.make tabs f g).sc.f.value? x = f.value? x := by rw [sc_f]

/-- The source frame constants the target does not issue run in the source alone. -/
theorem kAll_sim {env : Env} {frA : Frame} {S : Facts} {s : LocState} :
    ∀ (os : List ID) (fr : Frame), (∀ x ∈ os, (Cx.make tabs f g).isK x = true) →
      Match (Cx.make tabs f g) env frA S fr s →
      SimRes (fun fr' s' => Match (Cx.make tabs f g) env frA S fr' s')
        (evalAllL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr os) (.ok s)
  | [], _, _, h => ⟨s, rfl, h⟩
  | x :: os, fr, hk, h => by
    have hkx := hk x List.mem_cons_self
    obtain ⟨v, hv, -, hkv⟩ := isK_spec hkx
    have hv' : f.value? x = some v := hv
    simp only [evalAllL, sc_value, hv']
    cases hev : evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr v with
    | ok y =>
      exact kAll_sim os (upd fr x y) (fun z hz => hk z (List.mem_cons_of_mem _ hz))
        (kRun_match h hkx hv' hev)
    | panic e m => exact absurd hev (evalValueL_K_ne_panic (isKVal_spec hkv).1)
    | stuck msg => trivial

/-! ## One target value -/

/-- A kept value: the source evaluates it, the target runs it; `Match` with `keptFacts`. -/
theorem kept_sim {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    (hown : f.ownAux = g.ownAux)
    {d : ID} {u w : Value} (hu : f.value? d = some u) (hw : g.value? d = some w)
    (hud : u.id = d) (hwd : w.id = d) (hsame : sameOp u w = true) (hphi : w.op ≠ .Phi)
    (hnd : writesNodup ((Cx.make tabs f g).lc.home d) ((Cx.make tabs f g).gty d) = true)
    (hchk : keptChecks (Cx.make tabs f g) S w u = .ok ()) :
    SimRes (fun fr' s' => Match (Cx.make tabs f g) env frA (keptFacts (Cx.make tabs f g) S w u) fr' s')
      (match evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u with
        | .ok y => .ok (upd fr d y) | .panic e m => .panic e m | .stuck msg => .stuck msg)
      (stepLoc env (Cx.make tabs f g).lc s w) := by
  cases hev : evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u with
  | stuck msg => trivial
  | ok y =>
    obtain ⟨argv, hargv⟩ := evalValueL_regsAre (fun msg h' => by rw [hev] at h'; cases h')
    have hev' := hev
    rw [evalValueL_eq hargv, hud] at hev'
    rw [kept_step h hlow hown hu hw hud hwd hsame hphi hchk hargv]
    cases hr : evalOpL true env (Cx.make tabs f g).sc fr u argv ((Cx.make tabs f g).fty d) with
    | ok r0 =>
      rw [show (Cx.make tabs f g).md.faulting = true from rfl] at hev'
      change (evalOpL true env (Cx.make tabs f g).sc fr u argv ((Cx.make tabs f g).fty d)).bind _ = _ at hev'
      rw [hr] at hev'
      cases hev'
      exact ⟨_, rfl, kept_match h hlow hu hw hud hwd hsame hnd hargv hr⟩
    | panic e m =>
      change (evalOpL true env (Cx.make tabs f g).sc fr u argv ((Cx.make tabs f g).fty d)).bind _ = _ at hev'
      rw [hr] at hev'; cases hev'
    | stuck msg =>
      change (evalOpL true env (Cx.make tabs f g).sc fr u argv ((Cx.make tabs f g).fty d)).bind _ = _ at hev'
      rw [hr] at hev'; cases hev'
  | panic e m =>
    obtain ⟨argv, hargv⟩ := evalValueL_regsAre (fun msg h' => by rw [hev] at h'; cases h')
    have hev' := hev
    rw [evalValueL_eq hargv, hud] at hev'
    rw [kept_step h hlow hown hu hw hud hwd hsame hphi hchk hargv]
    change (evalOpL true env (Cx.make tabs f g).sc fr u argv ((Cx.make tabs f g).fty d)).bind _ = _ at hev'
    show _ = _
    cases hr : evalOpL true env (Cx.make tabs f g).sc fr u argv ((Cx.make tabs f g).fty d) with
    | ok r0 => rw [hr] at hev'; cases hev'
    | panic e' m' => rw [hr] at hev'; cases hev'; rfl
    | stuck msg => rw [hr] at hev'; cases hev'

/-- A kept `KeepAlive` that became `Copy`/`VarLive`. -/
theorem keepAlive_sim' {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    {d : ID} {u w : Value} (hu : f.value? d = some u) (hw : g.value? d = some w)
    (hud : u.id = d) (hwd : w.id = d) (hka : isKeepAliveCopy u w = true)
    (hnd : writesNodup ((Cx.make tabs f g).lc.home d) ((Cx.make tabs f g).gty d) = true)
    (hchk : keepAliveChecks (Cx.make tabs f g) S w u = .ok ()) :
    SimRes (fun fr' s' => Match (Cx.make tabs f g) env frA
        (writeFacts (Cx.make tabs f g)
          ((Cx.make tabs f g).redefine (clobberFacts (Cx.make tabs f g) S w) u.id) w u.id) fr' s')
      (match evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u with
        | .ok y => .ok (upd fr d y) | .panic e m => .panic e m | .stuck msg => .stuck msg)
      (stepLoc env (Cx.make tabs f g).lc s w) := by
  have := keepAlive_sim h hlow hu hw hud hwd hka hnd hchk
  revert this
  cases evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u with
  | ok y => intro ⟨s', hs', hm⟩; exact ⟨s', hs', hm⟩
  | panic e m => intro hp; exact hp
  | stuck msg => intro _; trivial

theorem stepLoc_phi {env : Env} {lc : LocCtx} {s : LocState} {w : Value} (hphi : w.op = .Phi)
    (hh : w.args.all (lc.home · == lc.home w.id) = true) : stepLoc env lc s w = .ok s := by
  unfold stepLoc
  rw [if_pos (by rw [hphi]; rfl), if_pos hh]

/-- What `stepValue` accepted. -/
theorem stepValue_spec {cx : Cx} {cert : Cert} {S S1 : Facts} {d : ID} {os os1 : List ID}
    (h : stepValue cx cert S d os = .ok (S1, os1)) :
    ∃ w, cx.g.value? d = some w ∧ w.id = d ∧
      ((w.op = .Phi ∧ w.args.all (cx.lc.home · == cx.lc.home d) = true ∧ S1 = S ∧ os1 = os) ∨
       (w.op ≠ .Phi ∧ writesNodup (cx.lc.home d) (cx.gty d) = true ∧
        ((∃ u, cx.f.value? d = some u ∧ u.id = d ∧ d ∈ os ∧
            (∀ x ∈ os.takeWhile (· != d), cx.isK x = true) ∧
            os1 = (os.dropWhile (· != d)).drop 1 ∧
            ((sameOp u w = true ∧ keptStep cx S w u = .ok S1) ∨
             (sameOp u w = false ∧ isKeepAliveCopy u w = true ∧ keepAliveStep cx S w u = .ok S1))) ∨
         (os1 = os ∧ newStep cx cert S w = .ok S1)))) := by
  unfold stepValue at h
  cases hw : cx.g.value? d with
  | none => rw [hw] at h; cases h
  | some w =>
  rw [hw] at h
  dsimp only at h
  refine ⟨w, rfl, ?_⟩
  by_cases hid : (w.id != d) = true
  · rw [if_pos hid] at h; cases h
  rw [if_neg hid] at h
  refine ⟨by simpa using hid, ?_⟩
  by_cases hphi : (w.op == .Phi) = true
  · rw [if_pos hphi] at h
    by_cases hh : (w.args.all fun x => cx.lc.home x == cx.lc.home d) = true
    · rw [if_pos hh] at h; cases h
      exact .inl ⟨by simpa using hphi, hh, rfl, rfl⟩
    · rw [if_neg hh] at h; cases h
  rw [if_neg hphi] at h
  by_cases hnd : (!writesNodup (cx.lc.home d) (cx.gty d)) = true
  · rw [if_pos hnd] at h; cases h
  rw [if_neg hnd] at h
  refine .inr ⟨by simpa using hphi, by simpa using hnd, ?_⟩
  cases hu : cx.f.value? d with
  | none =>
    rw [hu] at h
    dsimp only at h
    obtain ⟨S2, hS2, h⟩ := exc_bind_ok h
    cases h
    exact .inr ⟨rfl, hS2⟩
  | some u =>
  rw [hu] at h
  dsimp only at h
  by_cases hin : os.contains d = true
  · rw [if_pos hin] at h
    by_cases hud : (u.id != d) = true
    · rw [if_pos hud] at h; cases h
    rw [if_neg hud] at h
    by_cases hso : (!sameOp u w && !isKeepAliveCopy u w) = true
    · rw [if_pos hso] at h; cases h
    rw [if_neg hso] at h
    by_cases hpre : (!(List.takeWhile (fun x => x != d) os).all cx.isK) = true
    · rw [if_pos hpre] at h; cases h
    rw [if_neg hpre] at h
    have hpre' : ∀ x ∈ os.takeWhile (· != d), cx.isK x = true := by
      simpa [List.all_eq_true] using hpre
    refine .inl ⟨u, rfl, by simpa using hud, by simpa using hin, hpre', ?_⟩
    by_cases hs : sameOp u w = true
    · rw [if_pos hs] at h
      obtain ⟨S2, hS2, h⟩ := exc_bind_ok h
      cases h
      exact ⟨rfl, .inl ⟨hs, hS2⟩⟩
    · rw [if_neg hs] at h
      obtain ⟨S2, hS2, h⟩ := exc_bind_ok h
      cases h
      have hs' : sameOp u w = false := by simpa using hs
      have hka : isKeepAliveCopy u w = true := by
        simp only [hs', Bool.not_false, Bool.true_and] at hso
        simpa using hso
      exact ⟨rfl, .inr ⟨hs', hka, hS2⟩⟩
  · rw [if_neg hin] at h
    obtain ⟨S2, hS2, h⟩ := exc_bind_ok h
    cases h
    exact .inr ⟨rfl, hS2⟩

theorem dropWhile_ne_of_mem {d : ID} : ∀ {os : List ID}, d ∈ os →
    os.dropWhile (· != d) = d :: (os.dropWhile (· != d)).drop 1
  | x :: os, h => by
    by_cases hx : x = d
    · subst hx; simp [List.dropWhile_cons]
    · have : d ∈ os := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      simp only [List.dropWhile_cons, bne_iff_ne, ne_eq, hx, not_false_eq_true, ite_true]
      exact dropWhile_ne_of_mem this

theorem split_at {d : ID} {os : List ID} (h : d ∈ os) :
    os = os.takeWhile (· != d) ++ [d] ++ (os.dropWhile (· != d)).drop 1 := by
  conv => lhs; rw [← List.takeWhile_append_dropWhile (p := (· != d)) (l := os)]
  rw [dropWhile_ne_of_mem h]
  simp

/-- `evalAllL` of one source value. -/
theorem evalAllL_one {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {d : ID} {u : Value}
    (hu : ctx.f.value? d = some u) :
    evalAllL md env ctx fr [d] =
      match evalValueL md env ctx fr u with
      | .ok y => .ok (upd fr d y) | .panic e m => .panic e m | .stuck msg => .stuck msg := by
  simp only [evalAllL, hu]
  cases evalValueL md env ctx fr u <;> rfl

/-- **One target value** (`stepValue`): the source runs a prefix `c` of its schedule (skipped
frame constants and the kept value), the target the value. -/
theorem stepValue_sim {env : Env} {frA : Frame} {cert : Cert} {S S1 : Facts} {fr : Frame}
    {s : LocState} (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    (hown : f.ownAux = g.ownAux) {d : ID} {os os1 : List ID}
    (hsv : stepValue (Cx.make tabs f g) cert S d os = .ok (S1, os1)) :
    ∃ w c, g.value? d = some w ∧ os = c ++ os1 ∧
      SimRes (fun fr' s' => Match (Cx.make tabs f g) env frA S1 fr' s')
        (evalAllL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr c)
        (stepLoc env (Cx.make tabs f g).lc s w) := by
  obtain ⟨w, hw, hwd, hc⟩ := stepValue_spec hsv
  have hw' : g.value? d = some w := hw
  rcases hc with ⟨hphi, hh, rfl, rfl⟩ | ⟨hphi, hnd, hk | ⟨rfl, hnew⟩⟩
  · refine ⟨w, [], hw', rfl, s, ?_, h⟩
    exact stepLoc_phi hphi (by rw [hwd]; exact hh)
  · obtain ⟨u, hu, hud, hin, hpre, rfl, hstep⟩ := hk
    have hu' : f.value? d = some u := hu
    refine ⟨w, os.takeWhile (· != d) ++ [d], hw', split_at hin, ?_⟩
    rw [evalAllL_append']
    have hK := kAll_sim (S := S) (s := s) (env := env) (frA := frA) _ fr hpre h
    have hb := SimRes.bind (Q := fun fr' s' => Match (Cx.make tabs f g) env frA S1 fr' s')
      (k := fun fr' => evalAllL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr' [d])
      (k' := fun s' => stepLoc env (Cx.make tabs f g).lc s' w) hK ?_
    · rwa [Res.bind_ok] at hb
    · intro fr' s' h'
      rw [evalAllL_one (by rw [sc_value]; exact hu')]
      rcases hstep with ⟨hso, hks⟩ | ⟨-, hka, hks⟩
      · unfold keptStep at hks
        simp only [bind, Except.bind, pure, Except.pure] at hks
        split at hks
        · cases hks
        · rename_i hchk
          cases hks
          exact kept_sim h' hlow hown hu' hw' hud hwd hso hphi hnd hchk
      · unfold keepAliveStep at hks
        simp only [bind, Except.bind, pure, Except.pure] at hks
        split at hks
        · cases hks
        · rename_i hchk
          cases hks
          exact keepAlive_sim' h' hlow hu' hw' hud hwd hka hnd hchk
  · refine ⟨w, [], hw', rfl, ?_⟩
    change ∃ s', stepLoc env (Cx.make tabs f g).lc s w = Res.ok s' ∧
      Match (Cx.make tabs f g) env frA S1 fr s'
    unfold newStep at hnew
    split at hnew
    · rename_i hmv
      have hmv' : w.op = .Copy ∨ w.op = .LoadReg ∨ w.op = .StoreReg := by
        simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using hmv
      exact move_sim h hlow hmv' (by rw [hwd]; exact hnd) hnew
    · dsimp only at hnew
      split at hnew
      · cases hnew
      · rename_i u hu
        split at hnew
        · cases hnew
        · rename_i hur
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hur
          unfold rematStep at hnew
          simp only [bind, Except.bind, pure, Except.pure] at hnew
          split at hnew
          · cases hnew
          · rename_i hchk
            cases hnew
            have hwg : g.value? w.id = some w := by rw [hwd]; exact hw'
            have hug : f.value? u.id = some u := by rw [hur]; exact hu
            exact remat_sim h hlow hwg hug (by rw [hwd]; exact hnd) hchk

/-! ## The walk -/

theorem walk_cons {cx : Cx} {cert : Cert} {S : Facts} {d : ID} {ds os : List ID}
    {r : Facts × List ID} (h : walk cx cert S (d :: ds) os = .ok r) :
    ∃ S1 os1, stepValue cx cert S d os = .ok (S1, os1) ∧ walk cx cert S1 ds os1 = .ok r := by
  simp only [walk, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    exact ⟨p.1, p.2, hp, h⟩

/-- **The walk**: the source's schedule and the target's values of a block. -/
theorem walk_sim {env : Env} {frA : Frame} {cert : Cert} (hlow : f.lowered = g.lowered)
    (hown : f.ownAux = g.ownAux) :
    ∀ (ds : List ID) (S : Facts) (os : List ID) (S' : Facts) (rest : List ID) (fr : Frame)
      (s : LocState),
      walk (Cx.make tabs f g) cert S ds os = .ok (S', rest) →
      (∀ x ∈ rest, (Cx.make tabs f g).isK x = true) →
      Match (Cx.make tabs f g) env frA S fr s →
      SimRes (fun fr' s' => Match (Cx.make tabs f g) env frA S' fr' s')
        (evalAllL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr os)
        (enterListLoc env (Cx.make tabs f g).lc s ds)
  | [], S, os, S', rest, fr, s, hw, hrest, h => by
    simp only [walk, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact kAll_sim os fr hrest h
  | d :: ds, S, os, S', rest, fr, s, hw, hrest, h => by
    obtain ⟨S1, os1, hsv, hw1⟩ := walk_cons hw
    obtain ⟨w, c, hwv, rfl, hsim⟩ := stepValue_sim h hlow hown hsv
    rw [evalAllL_append']
    have hlv : (Cx.make tabs f g).lc.ctx.f.value? d = some w := by rw [lc_f]; exact hwv
    rw [enterListLoc_cons' hlv]
    exact SimRes.bind hsim fun fr' s' h' => walk_sim hlow hown ds S1 os1 S' rest fr' s' hw1 hrest h'

/-! ## Phis -/

theorem setPhis_mem' : ∀ (ps : List (ID × Val)) (r : Array (Option Val)) (z : ID) (x : Val),
    (z, x) ∈ ps → (∀ q ∈ ps, q.1 = z → q.2 = x) → z < r.size →
    (setPhis ps r)[z]? = some (some x)
  | [], _, _, _, h, _, _ => absurd h List.not_mem_nil
  | (id, y) :: ps, r, z, x, hm, hq, hlt => by
    unfold setPhis
    rw [List.foldl_cons]
    by_cases hin : z ∈ ps.map Prod.fst
    · obtain ⟨⟨z', x'⟩, hp, rfl⟩ := List.mem_map.1 hin
      have hx' : x' = x := hq _ (List.mem_cons_of_mem _ hp) rfl
      subst hx'
      exact setPhis_mem' ps _ _ _ hp (fun q hq' => hq q (List.mem_cons_of_mem _ hq'))
        (by simpa [Array.set!] using hlt)
    · simp only [List.mem_cons, Prod.mk.injEq] at hm
      have hzid : id = z ∧ y = x := by
        rcases hm with h | h
        · exact ⟨h.1.symm, h.2.symm⟩
        · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩) hin
      obtain ⟨rfl, rfl⟩ := hzid
      refine (setPhis_not_mem ps _ id hin).trans ?_
      simp [Array.set!, Array.getElem?_setIfInBounds, hlt]

/-- The source's `Phi`s along edge `i` of block `b`: the registers of the block's other values
unchanged, each `Phi`'s its `i`th argument's at its shape. -/
theorem phis_spec {md : LMode} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {ps : List (ID × Val)} (hps : b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps) :
    (setPhis ps fr.regs).size = fr.regs.size ∧
      (∀ z ∈ b.values, (ctx.f.value? z).isSome) ∧
      (∀ z, (z ∉ b.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi) →
        (setPhis ps fr.regs)[z]? = fr.regs[z]?) ∧
      (∀ z ∈ b.values, ∀ v, ctx.f.value? z = some v → v.op = .Phi → z < fr.regs.size →
        ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
          (setPhis ps fr.regs)[z]? = some (some (md.retype (ctx.tys[z]?.getD .other) y))) := by
  obtain ⟨hsub, hsome, hall⟩ := filterMapM_phiL hps
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
  · rcases hall z (Array.mem_toList_iff.2 hz) with ⟨p, hp, hpz⟩ | hn
    · obtain ⟨_, v', a, y, hv', -, ha, hy, hp2⟩ := phiStepL_some (hsome p hp)
      rw [hpz, hv] at hv'; cases hv'
      refine ⟨a, y, ha, hy, ?_⟩
      apply setPhis_mem' ps fr.regs z _ (by rw [← hpz, ← hp2]; exact hp) _ hlt
      intro q hq hqz
      obtain ⟨_, v'', a', y', hv'', -, ha', hy', hq2⟩ := phiStepL_some (hsome q hq)
      rw [hqz, hv] at hv''; cases hv''
      rw [ha] at ha'; cases ha'
      rw [hy] at hy'; cases hy'
      rw [hq2, hqz]
    · obtain ⟨v', hv', hne⟩ := phiStepL_none hn
      rw [hv] at hv'; cases hv'; exact absurd hphi hne

theorem isK_not_phi {cx : Cx} {z : ID} (hk : cx.isK z = true) {v : Value}
    (hv : cx.f.value? z = some v) : v.op ≠ .Phi := by
  obtain ⟨v', hv', -, hkv⟩ := isK_spec hk
  rw [hv] at hv'; cases hv'
  intro hp
  have := (isKVal_spec hkv).1
  rw [hp] at this; cases this

/-- `Match` after the source's `Phi`s, given the facts. -/
theorem phis_match {env : Env} {frA : Frame} {S T : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {b : Block} {i : Nat} {ps : List (ID × Val)}
    (hps : b.values.toList.filterMapM
      (phiStepL (Cx.make tabs f g).md (Cx.make tabs f g).sc fr i) = .ok ps)
    (hT : ∀ F ∈ T, FactOK (Cx.make tabs f g) env frA { fr with regs := setPhis ps fr.regs } s F) :
    Match (Cx.make tabs f g) env frA T { fr with regs := setPhis ps fr.regs } s := by
  obtain ⟨hsz, hsome, hother, hphis⟩ := phis_spec hps
  have hkeep : ∀ z, (∀ v, f.value? z = some v → v.op ≠ .Phi) →
      (setPhis ps fr.regs)[z]? = fr.regs[z]? := by
    intro z hz
    apply hother
    by_cases hb : z ∈ b.values
    · have := hsome z hb
      rw [sc_value] at this
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 this
      exact .inr ⟨v, by rw [sc_value]; exact hv, hz v hv⟩
    · exact .inl hb
  refine { facts := hT, fr_eq := ?_, s_fr := h.s_fr, shaped := ?_, kinv := ?_, regs := h.regs,
           fsize := by rw [hsz]; exact h.fsize }
  · conv => lhs; rw [h.fr_eq]
  · intro id x hx
    by_cases hp : ∃ v, f.value? id = some v ∧ v.op = .Phi ∧ id ∈ b.values
    · obtain ⟨v, hv, hphi, hb⟩ := hp
      have hlt : id < fr.regs.size := by
        rw [← hsz]
        exact (Array.getElem?_eq_some_iff.1 (Option.join_eq_some_iff.1 hx)).1
      obtain ⟨a, y, -, -, hset⟩ := hphis id hb v (by rw [sc_value]; exact hv) hphi hlt
      simp only at hx
      rw [hset] at hx
      cases hx
      exact LMode.retype_idem _ _ _
    · have : (setPhis ps fr.regs)[id]? = fr.regs[id]? := by
        apply hother
        by_cases hb : id ∈ b.values
        · have := hsome id hb
          rw [sc_value] at this
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 this
          exact .inr ⟨v, by rw [sc_value]; exact hv, fun hphi => hp ⟨v, hv, hphi, hb⟩⟩
        · exact .inl hb
      simp only at hx
      rw [this] at hx
      exact h.shaped id x hx
  · intro id x hk hx
    simp only at hx
    rw [hkeep id fun v hv => isK_not_phi hk hv] at hx
    exact h.kinv id x hk hx

/-- Exact facts imply weak ones: the certificate's facts hold where the edge's do. -/
theorem sub_sound {cx : Cx} {env : Env} {frA : Frame} {S T : Facts} {fr : Frame} {s : LocState}
    (h : Match cx env frA S fr s) (hsub : sub T S = true) : Match cx env frA T fr s := by
  refine { h with facts := fun F hF => ?_ }
  unfold sub at hsub
  have := List.all_eq_true.1 hsub F hF
  obtain ⟨l, o⟩ := F
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at this
  rcases this with hS | ⟨⟨hw, hc⟩, hS⟩
  · exact h.facts _ hS
  · have hF' := h.facts _ hS
    by_cases hl : l = .avail
    · subst hl; exact hF'
    · rw [factOK_loc hl] at hF' ⊢
      intro x hx
      have := hF' x hx
      simp only [Bool.false_eq_true, ite_false] at this
      simp only [hw, ite_true]
      have hc' : o.comp = none := by simpa using hc
      rw [this, hc']
      simp only [comp]
      unfold Cx.origTy
      rw [hc']
      exact srcVal_shaped h hx

/-- A fact `phiFacts` gives about phi `F.2.id` (entered along edge `i`, from the facts `S`). -/
def PhiFact (cx : Cx) (S : Facts) (i : Nat) (F : Fact) : Prop :=
  ∃ p a l, cx.f.value? F.2.id = some p ∧ p.op = .Phi ∧ p.args[i]? = some a ∧
    readLoc (cx.lc.home F.2.id) (cx.fty F.2.id) = some (.loc l) ∧ F.1 = l ∧ F.2.comp = none ∧
    ((S.holdsExact l (cx.canon a) = true ∧
        F.2.weak = !shapeEq (cx.fty F.2.id) (cx.fty (cx.canon a))) ∨
     (S.holds l (cx.canon a) = true ∧ F.2.weak = true ∧
        composes cx.f.lowered (cx.fty F.2.id) (cx.fty (cx.canon a)) = true))

theorem phiFacts_mem {cx : Cx} {S : Facts} {i : Nat} {pb : Option ID} :
    ∀ {ids : List ID} {N : Facts}, phiFacts cx S i pb ids = .ok N →
      ∀ F ∈ N, F.2.id ∈ ids ∧ PhiFact cx S i F
  | [], N, h => by
    simp only [phiFacts, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | id :: ids, N, h => by
    rw [phiFacts.eq_2] at h
    obtain ⟨rest, hrest, h⟩ := exc_bind_ok h
    have ih : ∀ F ∈ rest, F.2.id ∈ id :: ids ∧ PhiFact cx S i F := fun F hF =>
      ⟨List.mem_cons_of_mem _ (phiFacts_mem hrest F hF).1, (phiFacts_mem hrest F hF).2⟩
    cases hp : cx.f.value? id with
    | none => rw [hp] at h; cases h; exact ih
    | some p =>
    rw [hp] at h
    dsimp only at h
    by_cases hphi : (p.op != Op.Phi) = true
    · rw [if_pos hphi] at h; cases h; exact ih
    rw [if_neg hphi] at h
    have hphi' : p.op = .Phi := by simpa using hphi
    cases ha : p.args[i]? with
    | none => rw [ha] at h; cases h
    | some a =>
    rw [ha] at h
    dsimp only at h
    cases hl : readLoc (cx.lc.home id) (cx.fty id) with
    | none => rw [hl] at h; cases h
    | some r =>
    cases r with
    | zero => rw [hl] at h; cases h
    | tuple ls => rw [hl] at h; cases h
    | poison => rw [hl] at h; cases h
    | loc l =>
    rw [hl] at h
    dsimp only at h
    by_cases hex : S.holdsExact l (cx.canon a) = true
    · rw [if_pos hex] at h; cases h
      intro F hF
      rcases List.mem_cons.1 hF with rfl | hF
      · exact ⟨List.mem_cons_self, p, a, l, hp, hphi', ha, hl, rfl, rfl, .inl ⟨hex, rfl⟩⟩
      · exact ih F hF
    rw [if_neg hex] at h
    by_cases hho : S.holds l (cx.canon a) = true
    · rw [if_pos hho] at h
      by_cases hco : (!composes cx.f.lowered (cx.fty id) (cx.fty (cx.canon a))) = true
      · rw [if_pos hco] at h; cases h
      rw [if_neg hco] at h
      cases h
      intro F hF
      rcases List.mem_cons.1 hF with rfl | hF
      · exact ⟨List.mem_cons_self, p, a, l, hp, hphi', ha, hl, rfl, rfl,
          .inr ⟨hho, rfl, by simpa using hco⟩⟩
      · exact ih F hF
    · rw [if_neg hho] at h; cases h

/-- **The source's `Phi`s along an edge `phiEdge` accepted**: `Match` with the edge's facts. -/
theorem phiEdge_sim {env : Env} {frA : Frame} {S E : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {bid : ID} {i : Nat}
    (he : phiEdge (Cx.make tabs f g) S bid i = .ok E) {b : Block} (hb : f.block? bid = some b)
    {ps : List (ID × Val)}
    (hps : b.values.toList.filterMapM
      (phiStepL (Cx.make tabs f g).md (Cx.make tabs f g).sc fr i) = .ok ps) :
    Match (Cx.make tabs f g) env frA E { fr with regs := setPhis ps fr.regs } s := by
  unfold phiEdge at he
  rw [show (Cx.make tabs f g).f.block? bid = some b from hb] at he
  dsimp only at he
  obtain ⟨N, hN, he⟩ := exc_bind_ok he
  cases he
  obtain ⟨hsz, hsome, hother, hphis⟩ := phis_spec hps
  -- the registers of values other than the block's phis are unchanged
  have hkeep : ∀ z, z ∉ b.values.toList.filter (Cx.make tabs f g).isPhi →
      (setPhis ps fr.regs)[z]? = fr.regs[z]? := by
    intro z hz
    apply hother
    by_cases hzb : z ∈ b.values
    · have := hsome z hzb
      rw [sc_value] at this
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 this
      refine .inr ⟨v, by rw [sc_value]; exact hv, fun hphi => hz ?_⟩
      rw [List.mem_filter]
      refine ⟨Array.mem_toList_iff.2 hzb, ?_⟩
      unfold Cx.isPhi
      rw [show (Cx.make tabs f g).f = f from rfl, hv]
      simp [hphi]
    · exact .inl hzb
  apply phis_match h hps
  intro F hF
  rcases List.mem_append.1 hF with hF | hF
  · obtain ⟨hid, p, a, l, hp, hphi, ha, hl, hF1, hcomp, hcase⟩ := phiFacts_mem hN F hF
    obtain ⟨l', o⟩ := F
    simp only at hF1 hcomp hid hp hl hcase ⊢
    subst l'
    rw [factOK_loc (readLoc_loc_ne hl)]
    intro x hx
    have hnk : (Cx.make tabs f g).isK o.id = false := by
      cases hk : (Cx.make tabs f g).isK o.id
      · rfl
      · exact absurd hphi (isK_not_phi hk hp)
    unfold srcVal at hx
    rw [if_neg (by simp [hnk])] at hx
    have hlt : o.id < fr.regs.size := by
      rw [← hsz]
      exact (Array.getElem?_eq_some_iff.1 (Option.join_eq_some_iff.1 hx)).1
    obtain ⟨a', y, ha', hy, hset⟩ :=
      hphis o.id (Array.mem_toList_iff.1 hid) p (by rw [sc_value]; exact hp) hphi hlt
    rw [ha] at ha'; cases ha'
    simp only at hx
    rw [hset] at hx
    cases hx
    have hsy : srcVal (Cx.make tabs f g) env frA fr a = some y :=
      srcVal_of_reg h (by rw [hy]; rfl)
    have hfa := (srcVal_canon hsy).2
    have hya := srcVal_shaped h hsy
    simp only [comp, Cx.origTy, hcomp]
    rcases hcase with ⟨hex, hw⟩ | ⟨hho, hw, hco⟩
    · have hex' := holdsExact_iff.1 hex
      have hat : s.at l = y := by
        have := (factOK_loc (readLoc_loc_ne hl)).1 (h.facts _ hex') y (srcVal_canon hsy).1
        simpa [comp] using this
      rw [hw, hat]
      cases hsh : shapeEq ((Cx.make tabs f g).fty o.id) ((Cx.make tabs f g).fty ((Cx.make tabs f g).canon a))
      · rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        show y = (Cx.make tabs f g).md.retype ((Cx.make tabs f g).fty o.id) y
        rw [retype_shapeEq _ hsh, hfa, hya]
    · rw [hw]
      simp only [ite_true]
      show (Cx.make tabs f g).md.retype ((Cx.make tabs f g).fty o.id) (s.at l) =
        (Cx.make tabs f g).md.retype ((Cx.make tabs f g).fty o.id) y
      have hr := holds_read h (readLoc_loc_ne hl) hho hsy
      rw [← hfa] at hr
      rw [← hr, retype_composes (md := (Cx.make tabs f g).md) hco]
  · rw [List.mem_filter] at hF
    obtain ⟨hFS, hc⟩ := hF
    obtain ⟨l, o⟩ := F
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hnid : o.id ∉ b.values.toList.filter (Cx.make tabs f g).isPhi := fun hm =>
      absurd (List.contains_iff_mem.2 hm) (by rw [hc1]; decide)
    have hfac := h.facts _ hFS
    by_cases hl : l = .avail
    · subst hl
      have hany : ∀ z ∈ b.values.toList.filter (Cx.make tabs f g).isPhi,
          (Cx.make tabs f g).reads o.id z = false := by
        intro z hz
        cases hr : (Cx.make tabs f g).reads o.id z
        · rfl
        · exfalso
          have : (b.values.toList.filter (Cx.make tabs f g).isPhi).any
              ((Cx.make tabs f g).reads o.id ·) = true := List.any_eq_true.2 ⟨z, hz, hr⟩
          simp [this] at hc2
      obtain ⟨v, y, hv, hvid, hreg, hev⟩ := factOK_avail.1 hfac
      refine factOK_avail.2 ⟨v, y, hv, hvid, ?_, ?_⟩
      · show ((setPhis ps fr.regs)[o.id]?).join = some y
        rw [hkeep o.id hnid]; exact hreg
      · rw [← hev]
        refine (evalValueL_congr rfl fun a ha => (hkeep a fun hm => ?_).symm).symm
        have := hany a hm
        unfold Cx.reads at this
        rw [hv] at this
        simp [ha] at this
    · rw [factOK_loc hl] at hfac ⊢
      intro x hx
      apply hfac x
      unfold srcVal at hx ⊢
      split
      · rename_i hk; rw [if_pos hk] at hx; exact hx
      · rename_i hk; rw [if_neg hk] at hx
        simp only at hx
        rw [hkeep o.id hnid] at hx; exact hx

/-! ## Terminators -/

theorem termOK_spec {cx : Cx} {S : Facts} {b b' : Block} (h : termOK cx S b b' = .ok ()) :
    b'.kind = b.kind ∧ b'.auxInt = b.auxInt ∧ b'.succs = b.succs ∧
      b'.controls.size = b.controls.size ∧
      ctrlOK cx S b.id b.kind 0 b.controls.toList b'.controls.toList = .ok () := by
  unfold termOK at h
  by_cases hc : (b.kind == b'.kind && b.auxInt == b'.auxInt && b.aux == b'.aux &&
      b.succs == b'.succs && b.controls.size == b'.controls.size) = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind, pure,
      Except.pure] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨hk, ha⟩, -⟩, hs⟩, hsz⟩ := hc
    exact ⟨hk.symm, ha.symm, hs.symm, hsz.symm, h⟩
  · simp only [Bool.not_eq_true] at hc
    simp [hc, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- What `ctrlOK` asks of one control `c` (target `c'`, index `j`). -/
def CtrlOne (cx : Cx) (S : Facts) (k : BlockKind) (j : Nat) (c c' : ID) (u w : Value) : Prop :=
  (w.op = .MakeResult → readsControl k j = true →
    c' = c ∧ sameOp u w = true ∧ ((Loc.avail, (⟨c, none, false⟩ : Orig)) ∈ S) ∧
      argsOKL cx S w.args.toList u.args.toList none = .ok ()) ∧
  (w.op = .MakeResult → readsControl k j = false → ∀ a ∈ w.args, readable cx a = true) ∧
  (w.op ≠ .MakeResult → readsControl k j = true → argOK cx S c' c none = .ok ()) ∧
  (w.op ≠ .MakeResult → readsControl k j = false → readable cx c' = true)

theorem ctrlOK_cons {cx : Cx} {S : Facts} {bid : ID} {k : BlockKind} {j : Nat} {c c' : ID}
    {cs cs' : List ID} (h : ctrlOK cx S bid k j (c :: cs) (c' :: cs') = .ok ()) :
    ∃ u w, cx.f.value? c = some u ∧ cx.g.value? c' = some w ∧ CtrlOne cx S k j c c' u w ∧
      ctrlOK cx S bid k (j + 1) cs cs' = .ok () := by
  rw [ctrlOK.eq_1] at h
  cases hu : cx.f.value? c with
  | none => rw [hu] at h; cases h
  | some u =>
  cases hw : cx.g.value? c' with
  | none => rw [hu, hw] at h; cases h
  | some w =>
  rw [hu, hw] at h
  dsimp only at h
  refine ⟨u, w, rfl, rfl, ?_⟩
  by_cases hm : (w.op == .MakeResult) = true
  · have hm' : w.op = .MakeResult := by simpa using hm
    rw [if_pos hm] at h
    by_cases hrd : readsControl k j = true
    · rw [if_pos hrd] at h
      by_cases h1 : (c' != c || !sameOp u w) = true
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      by_cases h2 : (!List.contains S (Loc.avail, { id := c, comp := none, weak := false })) = true
      · rw [if_pos h2] at h; cases h
      rw [if_neg h2] at h
      obtain ⟨r, hr, h⟩ := exc_bind_ok h
      cases r
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', not_or,
        Decidable.not_not, Bool.not_eq_false] at h1
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.contains_iff_mem] at h2
      refine ⟨⟨fun _ _ => ⟨h1.1, h1.2, h2, hr⟩, fun _ hf => absurd hrd (by rw [hf]; decide),
        fun hn => absurd hm' hn, fun hn => absurd hm' hn⟩, h⟩
    · rw [if_neg hrd] at h
      by_cases h1 : (!w.args.all (readable cx)) = true
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      simp only [Bool.not_eq_true', Bool.not_eq_false, Array.all_eq_true_iff_forall_mem] at h1
      refine ⟨⟨fun _ ht => absurd ht hrd, fun _ _ => h1, fun hn => absurd hm' hn,
        fun hn => absurd hm' hn⟩, h⟩
  · have hm' : w.op ≠ .MakeResult := by simpa using hm
    rw [if_neg hm] at h
    by_cases hrd : readsControl k j = true
    · rw [if_pos hrd] at h
      obtain ⟨r, hr, h⟩ := exc_bind_ok h
      cases r
      refine ⟨⟨fun hn => absurd hn hm', fun hn => absurd hn hm', fun _ _ => hr,
        fun _ hf => absurd hrd (by rw [hf]; decide)⟩, h⟩
    · rw [if_neg hrd] at h
      by_cases h1 : (!readable cx c') = true
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      refine ⟨⟨fun hn => absurd hn hm', fun hn => absurd hn hm', fun _ ht => absurd ht hrd,
        fun _ _ => by simpa using h1⟩, h⟩

theorem argOK_readable {cx : Cx} {S : Facts} {a' a : ID} {sel : Option Nat} {s : LocState}
    (h : argOK cx S a' a sel = .ok ()) : ∃ x, s.read cx.lc a' = .ok x := by
  unfold argOK at h
  cases hr : readLoc (cx.lc.home a') (cx.gty a') with
  | none => rw [hr] at h; cases h
  | some r =>
    obtain ⟨x, hx⟩ := raw_ok (s := s) hr
    exact ⟨_, read_eq hx⟩

theorem readable_read {cx : Cx} {a' : ID} {s : LocState} (h : readable cx a' = true) :
    ∃ x, s.read cx.lc a' = .ok x := by
  unfold readable at h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨x, hx⟩ := raw_ok (s := s) hr
  exact ⟨_, read_eq hx⟩

theorem argsOKL_readable {cx : Cx} {S : Facts} {s : LocState} :
    ∀ {as' as : List ID} {sel : Option Nat}, argsOKL cx S as' as sel = .ok () →
      as'.length = as.length → ∀ a' ∈ as', ∃ x, s.read cx.lc a' = .ok x
  | [], _, _, _, _, _, h => absurd h List.not_mem_nil
  | a' :: as', a :: as, sel, hok, hlen, b, hb => by
    simp only [argsOKL, bind, Except.bind] at hok
    split at hok
    · cases hok
    · rename_i r hr
      rcases List.mem_cons.1 hb with rfl | hb
      · exact argOK_readable hr
      · exact argsOKL_readable hok (by simpa using hlen) b hb
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen

theorem mapM_ok_of {F : ID → Res Val} :
    ∀ {l : List ID}, (∀ a ∈ l, ∃ x, F a = .ok x) → ∃ xs, l.mapM F = .ok xs
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨x, hx⟩ := h a List.mem_cons_self
    obtain ⟨xs, hxs⟩ := mapM_ok_of (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨x :: xs, ?_⟩
    rw [List.mapM_cons, hx, hxs]; rfl

/-- The staged controls of `stepTermLoc`. -/
def stageFold (val : ID → Val) (l : List ID) (r : Array (Option Val)) : Array (Option Val) :=
  l.foldl (fun r c => if c < r.size then r.set! c (some (val c)) else r) r

theorem stageFold_cons (val : ID → Val) (c : ID) (l : List ID) (r : Array (Option Val)) :
    stageFold val (c :: l) r =
      stageFold val l (if c < r.size then r.set! c (some (val c)) else r) := rfl

theorem stageFold_size (val : ID → Val) :
    ∀ (l : List ID) (r : Array (Option Val)), (stageFold val l r).size = r.size
  | [], _ => rfl
  | c :: l, r => by
    rw [stageFold_cons, stageFold_size val l]
    split <;> simp [Array.set!]

theorem stageFold_not_mem (val : ID → Val) :
    ∀ (l : List ID) (r : Array (Option Val)) (z : ID), z ∉ l → (stageFold val l r)[z]? = r[z]?
  | [], _, _, _ => rfl
  | c :: l, r, z, hz => by
    rw [stageFold_cons, stageFold_not_mem val l _ z (fun h => hz (List.mem_cons_of_mem _ h))]
    have hne : c ≠ z := fun h => hz (h ▸ List.mem_cons_self)
    split
    · simp [Array.set!, Array.getElem?_setIfInBounds, hne]
    · rfl

theorem stageFold_mem (val : ID → Val) :
    ∀ (l : List ID) (r : Array (Option Val)) (z : ID), z ∈ l → z < r.size →
      (stageFold val l r)[z]? = some (some (val z))
  | [], _, _, h, _ => absurd h List.not_mem_nil
  | c :: l, r, z, hz, hlt => by
    rw [stageFold_cons]
    by_cases hl : z ∈ l
    · exact stageFold_mem val l _ z hl (by split <;> simp_all [Array.set!])
    · have hc : z = c := by
        rcases List.mem_cons.1 hz with h | h
        · exact h
        · exact absurd h hl
      subst hc
      rw [stageFold_not_mem val l _ z hl, if_pos hlt]
      simp [Array.set!, Array.getElem?_setIfInBounds, hlt]

theorem forIn_stage {lc : LocCtx} {s : LocState} {val : ID → Val} :
    ∀ (l : List ID) (regs : Array (Option Val)), (∀ c ∈ l, s.control lc c = .ok (val c)) →
      forIn l regs (TrimLoc.stageBody lc s) = .ok (stageFold val l regs)
  | [], _, _ => rfl
  | c :: cs, regs, h => by
    rw [List.forIn_cons]
    unfold TrimLoc.stageBody
    rw [h c List.mem_cons_self]
    exact forIn_stage cs _ fun c' hc' => h c' (List.mem_cons_of_mem _ hc')

theorem succ_rel {b b' : Block} (hs : b'.succs = b.succs) {j : Nat} {n : Next}
    (h : succ b j = .ok n) : succ b' j = .ok n := by
  obtain ⟨e, he, rfl⟩ := Dead.succ_ok h
  unfold succ; rw [hs, he]; rfl

/-- A generic terminator of the same kind and successors whose control value (when read) is the
same continues alike. -/
theorem stepTerm_ctl {fr fr' : Frame} {b b' : Block} (hk : b'.kind = b.kind)
    (hs : b'.succs = b.succs)
    (hc : (b.kind = .If ∨ b.kind = .JumpTable ∨ b.kind = .Ret) → ∀ x,
      Sem.control fr b 0 = .ok x → Sem.control fr' b' 0 = .ok x)
    {n : Next} (h : stepTerm fr b = .ok n) : stepTerm fr' b' = .ok n := by
  unfold stepTerm at h ⊢
  rw [hk]
  cases hb : b.kind <;> simp only [hb] at h ⊢
  case Plain => exact succ_rel hs h
  case First => exact succ_rel hs h
  case Defer => exact succ_rel hs h
  case If =>
    obtain ⟨x, hx, h'⟩ := res_bind_ok h
    rw [hc (.inl hb) x hx]
    simp only [bind, Res.bind] at h' ⊢
    split at h'
    · exact succ_rel hs h'
    · exact succ_rel hs h'
    · cases h'
  case JumpTable =>
    obtain ⟨x, hx, h'⟩ := res_bind_ok h
    rw [hc (.inr (.inl hb)) x hx]
    simp only [bind, Res.bind] at h' ⊢
    split at h'
    · exact succ_rel hs h'
    · cases h'
  case Ret =>
    obtain ⟨x, hx, h'⟩ := res_bind_ok h
    rw [hc (.inr (.inr hb)) x hx]
    simp only [bind, Res.bind] at h' ⊢
    split at h'
    · split at h'
      · split at h'
        · cases h'
        · rename_i hp
          rw [if_neg hp]
          exact h'
      · cases h'
    · cases h'
  all_goals cases h

/-- A terminator of the same kind, `auxInt` and successors whose control value (when read) is the
same continues alike. -/
theorem stepTermL_ctl {fr fr' : Frame} {b b' : Block} (hk : b'.kind = b.kind)
    (ha : b'.auxInt = b.auxInt) (hs : b'.succs = b.succs)
    (hc : readsControl b.kind 0 = true → ∀ x, Sem.control fr b 0 = .ok x →
      Sem.control fr' b' 0 = .ok x)
    {n : Next} (h : stepTermL fr b = .ok n) : stepTermL fr' b' = .ok n := by
  by_cases har : b.kind.isArm64 = true
  · obtain ⟨v, j, hcv, hsj, hT⟩ := Dead.stepTermL_arm har h
    have hrc : readsControl b.kind 0 = true := by simp [readsControl, har]
    rw [hT fr' b' hk ha (hc hrc v hcv)]
    exact succ_rel hs hsj
  · have har' : b'.kind.isArm64 = false := by rw [hk]; exact Bool.eq_false_iff.2 har
    rw [stepTermL_generic fr (Bool.eq_false_iff.2 har)] at h
    rw [stepTermL_generic fr' har']
    refine stepTerm_ctl hk hs (fun hkd => hc ?_) h
    rcases hkd with hkd | hkd | hkd <;> simp [readsControl, hkd]

theorem control_ok_of {s : LocState} {c' : ID} {w : Value}
    (hw : g.value? c' = some w) (hone : w.op = .MakeResult →
      ∃ xs, w.args.toList.mapM (s.read (Cx.make tabs f g).lc) = .ok xs)
    (hnot : w.op ≠ .MakeResult → ∃ x, s.read (Cx.make tabs f g).lc c' = .ok x) :
    ∃ x, s.control (Cx.make tabs f g).lc c' = .ok x := by
  unfold LocState.control
  rw [lc_f, hw]
  dsimp only
  by_cases hm : w.op = .MakeResult
  · rw [if_pos (by simp [hm])]
    obtain ⟨xs, hxs⟩ := hone hm
    show ∃ x, Res.bind _ _ = _
    rw [hxs]
    exact ⟨_, rfl⟩
  · rw [if_neg (by simp [hm])]
    exact hnot hm

theorem ctrlOK_readable {S : Facts} {bid : ID} {k : BlockKind} {s : LocState} :
    ∀ {j : Nat} {cs cs' : List ID}, ctrlOK (Cx.make tabs f g) S bid k j cs cs' = .ok () →
      cs'.length ≤ cs.length → ∀ c' ∈ cs', ∃ x, s.control (Cx.make tabs f g).lc c' = .ok x
  | _, _, [], _, _, _, h => absurd h List.not_mem_nil
  | _, [], _ :: _, _, hlen, _, _ => by simp at hlen
  | j, c :: cs, c0 :: cs', hok, hlen, c', hc' => by
    obtain ⟨u, w, hu, hw, ⟨h1, h2, h3, h4⟩, hrest⟩ := ctrlOK_cons hok
    rcases List.mem_cons.1 hc' with rfl | hc'
    · refine control_ok_of hw (fun hm => ?_) (fun hm => ?_)
      · cases hrd : readsControl k j
        · exact mapM_ok_of fun a ha => readable_read (h2 hm hrd a (Array.mem_toList_iff.1 ha))
        · obtain ⟨-, hso, -, hargs⟩ := h1 hm hrd
          have hl : w.args.toList.length = u.args.toList.length := by
            simp only [Array.length_toList]; exact ((sameOp_spec hso).2.2.2.2).symm
          exact mapM_ok_of fun a ha => argsOKL_readable hargs hl a ha
      · cases hrd : readsControl k j
        · exact readable_read (h4 hm hrd)
        · exact argOK_readable (h3 hm hrd)
    · exact ctrlOK_readable hrest (by simpa using hlen) c' hc'

/-- The control `stepTermL` reads: the target's reads the source's value. -/
theorem ctrl_head_val {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    {k : BlockKind} {j : Nat} {c c' : ID} {u w : Value} (hu : f.value? c = some u)
    (hw : g.value? c' = some w) (hone : CtrlOne (Cx.make tabs f g) S k j c c' u w)
    (hrd : readsControl k j = true) {x : Val} (hx : (fr.regs[c]?).join = some x) :
    s.control (Cx.make tabs f g).lc c' = .ok x := by
  obtain ⟨h1, -, h3, -⟩ := hone
  unfold LocState.control
  rw [lc_f, hw]
  dsimp only
  by_cases hm : w.op = .MakeResult
  · rw [if_pos (by simp [hm])]
    obtain ⟨hcc, hso, hav, hargs⟩ := h1 hm hrd
    subst c'
    obtain ⟨hop, -, -, hty, hsz⟩ := sameOp_spec hso
    obtain ⟨v, y, hv, hvid, hreg, hev⟩ := factOK_avail.1 (h.facts _ hav)
    have hv' : f.value? c = some v := hv
    rw [hu] at hv'; cases hv'
    rw [hx] at hreg; cases hreg
    obtain ⟨argv, hargv⟩ := evalValueL_regsAre (fun msg h' => by rw [hev] at h'; cases h')
    rw [evalValueL_eq hargv, evalOpL_makeResult (by rw [hop, hm])] at hev
    simp only [Res.bind_ok] at hev
    cases hev
    obtain ⟨argv', hargv', hrel⟩ := argsOKL_read h hlow hargs
      (by simp only [Array.length_toList]; exact hsz.symm) (regsAre_srcVal h hargv)
    have he := ArgsRel.eq_of_none hrel
    subst he
    show Res.bind _ _ = _
    rw [hargv']
    have hmd : LMode.loc g = (Cx.make tabs f g).md := by
      have := loc_md (tabs := tabs) hlow; rwa [lc_f] at this
    have hvid' : u.id = c := hvid
    show Res.ok ((LMode.loc g).retype ((Cx.make tabs f g).gty c) (Val.tuple argv')) =
      Res.ok ((Cx.make tabs f g).md.retype ((Cx.make tabs f g).fty u.id) (Val.tuple argv'))
    rw [hmd, hvid', gty_eq_fty hlow hu hw hty]
  · rw [if_neg (by simp [hm])]
    obtain ⟨x', hx', hrel⟩ := argOK_read h hlow (h3 hm hrd) (srcVal_of_reg h hx)
    rw [hx', hrel]

theorem list_cons_of_getElem? {l : List ID} {c : ID} (h : l[0]? = some c) : ∃ cs, l = c :: cs := by
  cases l with
  | nil => simp at h
  | cons x xs => simp at h; exact ⟨xs, by rw [h]⟩

/-- **A terminator `termOK` accepted** continues alike, with the target's controls staged. -/
theorem term_sim {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    (hsz : s.fr.regs.size = g.valueTab.size) {b b' : Block}
    (ht : termOK (Cx.make tabs f g) S b b' = .ok ()) {n : Next} (hn : stepTermL fr b = .ok n) :
    ∃ s', stepTermLoc (Cx.make tabs f g).lc s b' = .ok (n, s') ∧
      Match (Cx.make tabs f g) env frA S fr s' ∧ s'.fr.regs.size = g.valueTab.size := by
  obtain ⟨hk, ha, hs, hcs, hctl⟩ := termOK_spec ht
  have hread : ∀ c' ∈ b'.controls.toList, ∃ x, s.control (Cx.make tabs f g).lc c' = .ok x :=
    ctrlOK_readable hctl (by simp [hcs])
  let val : ID → Val := fun c => match s.control (Cx.make tabs f g).lc c with
    | .ok x => x
    | _ => .poison
  have hval : ∀ c ∈ b'.controls.toList, s.control (Cx.make tabs f g).lc c = .ok (val c) := by
    intro c hc
    obtain ⟨x, hx⟩ := hread c hc
    simp only [val, hx]
  let R := stageFold val b'.controls.toList s.fr.regs
  have hT : stepTermL (TrimLoc.stageLoc s R).fr b' = .ok n := by
    refine stepTermL_ctl hk ha hs ?_ hn
    intro hrc x hcx
    unfold Sem.control at hcx ⊢
    cases hc0 : b.controls[0]? with
    | none => rw [hc0] at hcx; cases hcx
    | some c =>
      rw [hc0] at hcx
      dsimp only at hcx
      obtain ⟨cs, hl⟩ := list_cons_of_getElem? (by rw [Array.getElem?_toList]; exact hc0)
      have hpos : 0 < b'.controls.toList.length := by
        rw [Array.length_toList, hcs, ← Array.length_toList, hl]; simp
      obtain ⟨c', cs', hl'⟩ : ∃ c' cs', b'.controls.toList = c' :: cs' := by
        cases hh : b'.controls.toList with
        | nil => rw [hh] at hpos; simp at hpos
        | cons c' cs' => exact ⟨c', cs', rfl⟩
      have hc0' : b'.controls[0]? = some c' := by rw [← Array.getElem?_toList, hl']; rfl
      rw [hc0']
      dsimp only
      rw [hl, hl'] at hctl
      obtain ⟨u, w, hu, hw, hone, -⟩ := ctrlOK_cons hctl
      have hx : (fr.regs[c]?).join = some x := by
        cases hj : (fr.regs[c]?).join with
        | none => rw [hj] at hcx; cases hcx
        | some y => rw [hj] at hcx; cases hcx; rfl
      have hcv := ctrl_head_val h hlow hu hw hone hrc hx
      have hlt : c' < s.fr.regs.size := by rw [hsz]; exact value?_lt hw
      have hreg := stageFold_mem val b'.controls.toList s.fr.regs c'
        (by rw [hl']; exact List.mem_cons_self) hlt
      show Res.ofOption _ (R[c']?).join = .ok x
      rw [show R[c']? = _ from hreg]
      simp only [val, hcv]
      rfl
  refine ⟨TrimLoc.stageLoc s R, ?_, ?_, ?_⟩
  · rw [TrimLoc.stepTermLoc_eq, forIn_stage _ _ hval]
    show Res.bind (stepTermL (TrimLoc.stageLoc s R).fr b') _ = _
    rw [hT]
    rfl
  · exact { facts := h.facts, fr_eq := h.fr_eq,
            s_fr := by
              show { s.fr with regs := R } = { frA with regs := R }
              rw [h.s_fr],
            shaped := h.shaped, kinv := h.kinv, regs := h.regs, fsize := h.fsize }
  · show R.size = _
    rw [stageFold_size]; exact hsz
