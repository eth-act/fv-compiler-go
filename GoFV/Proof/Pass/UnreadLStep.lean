import GoFV.Proof.Pass.UnreadLOps
import GoFV.Proof.RetypeL

/-!
# elim unread autos on `runL`: one value in source and target

`tgt_rel`: a value of `f` the source evaluates in frame `S` (registers avoiding the eliminated
variables `UE E` and typed), against `g`'s value with the same ID in the target frame `T`
(registers related by `VR`):

* a kept value whose arguments are all of a shape without memories or tuples reads equal
  registers, so evaluates alike (its evaluation reads of `g` only the sign extension of its first
  argument, which an eliminated write does not have, `sxOf_eq`);
* a kept value of `DAE.memOps` reads equal registers but its last one, related: dead auto elim's
  `memOp_rel`; one of `armMemOps` reads a memory last: `armMemOp_rel`;
* an eliminated write (a symbol store or `VarDef` of a variable of `E`, a frame temporary of
  `UE E`) is `Copy mem` in the target: the source writes only into `UE E` (`EqOff.write_left`,
  `EqOff.poison_left`).

`src_av`: a value the source evaluates avoids `UE E` (`evalValueL_av`; an eliminated write writes
avoiding bytes). `src_panic_av`: a panicking one panics avoiding `UE E`.
-/

namespace GoFV.Proof.UnreadL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.DAE GoFV.Opt

variable {U : Blk → Prop}

/-! ## Evaluation pieces -/

theorem evalValueL_of_argVals {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {vs : List Val} (h : CSE.argVals fr v.args = some vs) :
    evalValueL md env ctx fr v =
      (evalOpL md.faulting env ctx fr v vs (ctx.tys[v.id]?.getD .other)).bind
        fun r => .ok (md.retype (ctx.tys[v.id]?.getD .other) r) := by
  unfold evalValueL
  rw [CSE.mapM_res_ofOption h]
  rfl

theorem argVals_of_evalL {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (h : ∀ msg, evalValueL md env ctx fr v ≠ .stuck msg) : ∃ vs, CSE.argVals fr v.args = some vs :=
  CSE.argVals_some (evalValueL_args_def h)

theorem evalOpL_frame' (faulting : Bool) (env : Env) (ctx : Ctx) (fr : Frame)
    (r : Array (Option Val)) (v : Value) (argv : List Val) (ty : Ty) :
    evalOpL faulting env ctx { fr with regs := r } v argv ty = evalOpL faulting env ctx fr v argv ty :=
  rfl

theorem evalValueL_copy {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {w : ID}
    {y : Val} (hop : v.op = .Copy) (ha : v.args = #[w]) (hw : fr.regs[w]? = some (some y)) :
    evalValueL md env ctx fr v = .ok (md.retype (ctx.tys[v.id]?.getD .other) y) := by
  have hvs : CSE.argVals fr v.args = some [y] := by
    rw [ha]; simp [CSE.argVals, hw]
  rw [evalValueL_of_argVals hvs]
  have hg : v.op.generic = true := by rw [hop]; rfl
  rw [evalOpL_generic _ _ _ _ _ _ hg, evalOp_copy hop]
  rfl

/-- A typed register of a shape without memories or tuples is neither. -/
theorem typedL_plain {md : LMode} {t : Ty} {z : Val} (h : md.retype t z = z)
    (ht : DAE.memTy t = false) : (∀ m, z ≠ .mem m) ∧ (∀ vs, z ≠ .tuple vs) := by
  constructor
  · rintro m rfl
    unfold LMode.retype at h
    split at h <;> cases t <;> simp_all [DAE.memTy, Val.retypeL, Val.widen, Val.retype]
  · rintro vs rfl
    unfold LMode.retype at h
    split at h <;> cases t <;> simp_all [DAE.memTy, Val.retypeL, Val.widen, Val.retype]

/-- A typed register of the memory shape is a memory or `poison`. -/
theorem typedL_mem {md : LMode} {z : Val} (h : md.retype .mem z = z) :
    (∃ M, z = .mem M) ∨ z = .poison := by
  unfold LMode.retype at h
  split at h
  all_goals
    cases z with
    | mem M => exact .inl ⟨M, rfl⟩
    | poison => exact .inr rfl
    | _ => simp [Val.retypeL, Val.widen, Val.retype] at h

/-! ## The context of `g` -/

section Ctx

variable {tabs : Tables} {f g : Func} {E : List AuxRef}

theorem ctxL_facts (R : URel tabs f g E) :
    (Ctx.makeL tabs g).tabs = (Ctx.makeL tabs f).tabs ∧
      (Ctx.makeL tabs g).params = (Ctx.makeL tabs f).params ∧
      (Ctx.makeL tabs g).act = (Ctx.makeL tabs f).act := by
  refine ⟨by simp only [tabs_makeL], ?_, by simp only [act_makeL]; rfl⟩
  simp only [params_makeL, Ctx.make, abiParams, R.ownAux]

theorem act_makeL0 (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).act = 0 := by
  rw [act_makeL]; rfl

/-- The shape of a value of `g`, by its ID, is that of `f`'s. -/
theorem tysL_eq (R : URel tabs f g E) (x : ID) :
    (Ctx.makeL tabs g).tys[x]?.getD .other = (Ctx.makeL tabs f).tys[x]?.getD .other := by
  cases hf : f.value? x with
  | none =>
    have hg := R.none x hf
    have e : ∀ h : Func, h.value? x = none → (Ctx.makeL tabs h).tys[x]?.getD .other = .other := by
      intro h hh
      rw [tys_makeL]
      unfold Func.value? at hh
      simp only [Array.getElem?_map]
      cases hx : h.valueTab[x]? with
      | none => rfl
      | some o =>
        rw [hx] at hh
        simp only [Option.join_some] at hh
        subst hh; rfl
    rw [e g hg, e f hf]
  | some fv =>
    obtain ⟨gv, hgv, hk⟩ := R.value x fv hf
    have hty : gv.type = fv.type := by
      rcases hk with ⟨hs, -⟩ | ⟨he, -⟩
      · exact (DSE.sameV_spec hs).2.2.2.2.1
      · exact (elimV_spec he).2.2.2.2.2.1
    rw [tysL_of_value hgv, tysL_of_value hf, hty, R.low]

/-- An eliminated write and its `Copy` both hold no sign-extended register. -/
theorem signExt_elim {val? val?' : ID → Option Value} {fv gv : Value} (he : elimV fv gv = true) :
    Arm64.signExtendsIn val?' gv = Arm64.signExtendsIn val? fv := by
  obtain ⟨hop, hc, -⟩ := elimV_spec he
  unfold Arm64.signExtendsIn
  rw [hc]
  simp only [elimOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl

/-- Whether a value is an `LDPSW` is the same in `g` and `f`. -/
theorem ldpsw_eq (R : URel tabs f g E) (a : ID) :
    (g.value? a).map (·.op == .ARM64LDPSW) = (f.value? a).map (·.op == .ARM64LDPSW) := by
  cases hf : f.value? a with
  | none => rw [R.none a hf]
  | some fv =>
    obtain ⟨gv, hgv, hk⟩ := R.value a fv hf
    rw [hgv]
    simp only [Option.map_some, Option.some.injEq]
    rcases hk with ⟨hs, -⟩ | ⟨he, -⟩
    · rw [(DSE.sameV_spec hs).2.1]
    · obtain ⟨hop, hc, -⟩ := elimV_spec he
      rw [hc]
      simp only [elimOps, List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl

/-- The sign extensions the evaluation reads of `g` are `f`'s. -/
theorem sxOf_eq (R : URel tabs f g E) (v : Value) : sxOf g v = sxOf f v := by
  unfold sxOf
  cases ha : v.args[0]? with
  | none => rfl
  | some a =>
    simp only [Option.bind_some]
    cases hf : f.value? a with
    | none => rw [R.none a hf]; rfl
    | some fv =>
      obtain ⟨gv, hgv, hk⟩ := R.value a fv hf
      rw [hgv]
      simp only [Option.map_some, Option.some.injEq]
      rcases hk with ⟨hs, -⟩ | ⟨he, -⟩
      · obtain ⟨-, hop, -, -, -, -, hargs⟩ := DSE.sameV_spec hs
        refine Arm64.signExtendsIn_congr hop fun _ => ?_
        rw [hargs]
        cases fv.args[0]? with
        | none => rfl
        | some c => exact ldpsw_eq R c
      · exact signExt_elim he

end Ctx

/-! ## Related results -/

theorem resRel_lift {md : LMode} {t : Ty} {r r' : Res Val} (h : ResRel U r r') :
    ResRel U (r.bind fun r => .ok (md.retype t r)) (r'.bind fun r => .ok (md.retype t r)) := by
  refine ⟨fun y hy => ?_, fun e m hp => ?_⟩
  · cases r with
    | ok r =>
      obtain ⟨y', h1, h2⟩ := h.1 r rfl
      cases hy; rw [h1]; exact ⟨_, rfl, VR.mdRetype h2 md t⟩
    | panic _ _ => cases hy
    | stuck _ => cases hy
  · cases r with
    | ok r => cases hp
    | panic e' m' =>
      cases hp
      obtain ⟨m'', h1, h2⟩ := h.2 _ _ rfl
      rw [h1]; exact ⟨m'', rfl, h2⟩
    | stuck _ => cases hp

/-! ## Eliminated writes -/

theorem storePair_eqOff {n : Nat} {p q : Ptr} {a b : Val} {M M1 : Mem}
    (hw : Arm64.storePair n p q a b M = some M1) (hp : U p.blk) (hq : U q.blk) :
    ∀ M', Mem.EqOff U M M' → Mem.EqOff U M1 M' := by
  unfold Arm64.storePair at hw
  obtain ⟨M2, h1, h2⟩ := Option.bind_eq_some_iff.1 hw
  intro M' hM
  exact EqOff.write_left (EqOff.write_left hM h1 hp) h2 hq

/-- An eliminated symbol store writes into `U`: the source's memory after it is equal outside
`U` to the target's, and it avoids `U` when its arguments do. -/
theorem elimStore {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {ty : Ty}
    (hop : v.op ∈ armA) (hstore : v.op ∈ elimOps) (hsym : ∀ (k : Int64) a p, symAddr ctx { v with auxInt := k } a = some p → U p.blk)
    {L : List Val} {w : Val} {r : Val}
    (h : evalOpL false env ctx fr v (L ++ [w]) ty = .ok r) :
    ∃ M M1, w = .mem M ∧ r = .mem M1 ∧ (∀ M', Mem.EqOff U M M' → Mem.EqOff U M1 M') ∧
      ((∀ z ∈ L ++ [w], Val.Avoids U z) → M1.Avoids U) := by
  rw [evalOpL_armA hop] at h
  unfold arm64Op at h
  simp only [nilFaults, Bool.not_false, ite_true] at h
  generalize hop' : v.op = op at h hop hstore
  split at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | exact absurd hstore (by decide)
    | (simp only [snoc3, snoc4] at *
       rcases ‹L = _ ∧ _› with ⟨rfl, rfl⟩
       cases hw : Arm64.storeN _ _ _ _ with
       | none => rw [hw] at h; cases h
       | some M1 =>
         rw [hw] at h; cases h
         exact ⟨_, M1, rfl, rfl, fun M' hM => EqOff.write_left hM hw (hsym _ _ _ ‹_›),
           fun hav => memAvoids_write (hav (.mem _) (by simp)) hw
             (fun _ => storeBytes_av _ (hav _ (by simp)))⟩)
    | (simp only [snoc3, snoc4] at *
       rcases ‹L = _ ∧ _› with ⟨rfl, rfl⟩
       cases hw : Arm64.storePair _ _ _ _ _ _ with
       | none => rw [hw] at h; cases h
       | some M1 =>
         rw [hw] at h; cases h
         obtain ⟨h1, h2⟩ := pairAddr_eq_some ‹pairAddr _ _ _ _ = some (_, _)›
         exact ⟨_, M1, rfl, rfl, storePair_eqOff hw (hsym _ _ _ h1) (hsym _ _ _ h2),
           fun hav => storePair_av (hav (.mem _) (by simp)) hw (storeBytes_av _ (hav _ (by simp)))
             (storeBytes_av _ (hav _ (by simp)))⟩)
    | (exfalso; simp only [armA, List.mem_cons, List.not_mem_nil, or_false] at hop; simp_all; done)

/-! ## The eliminated variables' symbols -/

theorem symAddr_elim {tabs : Tables} {f : Func} {E : List AuxRef} {v : Value} {n : AuxRef}
    (hn : v.aux = some n) (hnE : n ∈ E) (htemp : tabs.forgeable n = false) :
    ∀ a p, symAddr (Ctx.makeL tabs f) v a = some p → UE E p.blk := by
  intro a p hp
  unfold symAddr at hp
  rw [hn] at hp
  simp only [tabs_makeL] at hp
  split at hp
  · rename_i heq
    unfold Tables.forgeable at htemp
    rw [heq] at htemp; cases htemp
  · cases hp; exact ⟨n, hnE, by rw [act_makeL0, frameBlk_temp htemp]⟩
  · cases hp

theorem elimOps_store {op : Op} (h : op ∈ elimOps) (hv : op ≠ .VarDef) : op ∈ armA := by
  simp only [elimOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact absurd rfl hv
  all_goals decide

theorem elimOps_noPanic {op : Op} (h : op ∈ elimOps) : ¬ PanickingL false op := by
  simp only [elimOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rintro (hc | hn | ⟨hf, -⟩)
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> cases hc
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> cases hn
  · cases hf

theorem memOps_generic {op : Op} (h : op ∈ DAE.memOps) : op.generic = true := by
  have key : DAE.memOps.all Op.generic = true := by decide
  exact List.all_eq_true.1 key op h

/-! ## One value -/

/-- The source's register property: it avoids the eliminated variables and has its shape. -/
def SPrL (tabs : Tables) (f : Func) (E : List AuxRef) (x : ID) (y : Val) : Prop :=
  Val.Avoids (UE E) y ∧
    LMode.retype ⟨f.lowered, false⟩ ((Ctx.makeL tabs f).tys[x]?.getD .other) y = y

theorem shape_arg {tabs : Tables} {f : Func} {a : ID} {av : Value} (h : f.value? a = some av) :
    (Ctx.makeL tabs f).tys[a]?.getD .other = shapeOf tabs f av.type := by
  rw [tysL_of_value h]; rfl

/-- **One value in source and target.** -/
theorem tgt_rel {env : Env} (hfs : env.FrameSafe) {tabs : Tables} {f g : Func} {E : List AuxRef}
    (R : URel tabs f g E) {S Tf : Frame} (hT : Tf = { S with regs := Tf.regs })
    (hpr : ∀ a y, S.regs[a]? = some (some y) → SPrL tabs f E a y)
    {x : ID} {fv gv : Value} (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (hid : fv.id = x) (hph : fv.op ≠ .Phi)
    (hargs : ∀ a ∈ gv.args, ∃ vS vT, S.regs[a]? = some (some vS) ∧ Tf.regs[a]? = some (some vT) ∧
      VR (UE E) vS vT) :
    ResRel (UE E) (evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) S fv)
      (evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) Tf gv) := by
  have hU := tempU_UE E
  obtain ⟨htabs, hpar, hact⟩ := ctxL_facts R
  obtain ⟨gv', hgv', hk⟩ := R.value x fv hfv
  rw [hgv] at hgv'; cases hgv'
  rcases hk with ⟨hs, hok⟩ | ⟨he, n, hn, hnE⟩
  · -- a kept value
    obtain ⟨hgid, hgop, hgax, hgai, hgty, -, hgargs⟩ := DSE.sameV_spec hs
    obtain ⟨hnoE, hcases⟩ := keptOK_spec hok
    rw [hgargs] at hargs
    by_cases hst : ∃ msg, evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) S fv = .stuck msg
    · obtain ⟨msg, hm⟩ := hst; rw [hm]; exact resRel_stuck _ _
    obtain ⟨vs, hvs⟩ := argVals_of_evalL (fun msg h' => hst ⟨msg, h'⟩)
    obtain ⟨vsT, hvsT, hrel⟩ := argVals_rel' hargs hvs
    rw [← hgargs] at hvsT
    rw [evalValueL_of_argVals hvs, evalValueL_of_argVals hvsT, hgid, tysL_eq R fv.id]
    have hsx : sxOf (Ctx.makeL tabs g).f gv = sxOf (Ctx.makeL tabs f).f fv := by
      rw [makeL_f, makeL_f, ← sxOf_eq R fv]
      unfold sxOf; rw [hgargs]
    rw [hT, evalOpL_frame', evalOpL_congr hgop hgax hgai hgid htabs hpar hact hsx]
    simp only
    apply resRel_lift
    have hplain : ∀ a ∈ fv.args, plainArg tabs f a = true → ∀ z,
        S.regs[a]? = some (some z) → (∀ m, z ≠ .mem m) ∧ (∀ vs, z ≠ .tuple vs) := by
      intro a _ hp z hz
      refine typedL_plain (hpr a z hz).2 ?_
      unfold plainArg at hp
      cases hav : f.value? a with
      | none =>
        have e : (Ctx.makeL tabs f).tys[a]?.getD .other = .other := by
          rw [tys_makeL]
          unfold Func.value? at hav
          simp only [Array.getElem?_map]
          cases hx : f.valueTab[a]? with
          | none => rfl
          | some o =>
            rw [hx] at hav
            simp only [Option.join_some] at hav
            subst hav; rfl
        rw [e]; rfl
      | some av =>
        rw [hav] at hp
        rw [shape_arg hav]
        simpa using hp
    rcases hcases with hP | hall | ⟨hpop, hmem | ⟨harm, hml⟩⟩
    · exact absurd hP hph
    · have : vsT = vs := hrel.eq_of fun z hz => by
        obtain ⟨a, ha, hza⟩ := argVals_mem hvs hz
        exact hplain a ha (hall a ha) z hza
      subst this
      exact resRel_refl _
    · cases hb : fv.args.back? with
      | none =>
        have h0 : fv.args = #[] := by rw [Array.back?_eq_none_iff] at hb; exact hb
        rw [h0] at hvs
        simp [CSE.argVals] at hvs; subst hvs
        cases hrel
        exact resRel_refl _
      | some m =>
        obtain ⟨L, w, rfl, -, hL⟩ := argVals_snoc hvs hb
        obtain ⟨L', w', rfl, hLL, hww⟩ := VRL.snoc_inv hrel
        have : L' = L := hLL.eq_of fun z hz => by
          obtain ⟨a, ha, hza⟩ := hL z hz
          exact hplain a (DSE.mem_of_mem_pop ha) (hpop a ha) z hza
        subst this
        rw [evalOpL_generic _ _ _ _ _ _ (memOps_generic hmem),
          evalOpL_generic _ _ _ _ _ _ (memOps_generic hmem)]
        refine memOp_rel hfs hU hmem hww fun _ z hz => ?_
        obtain ⟨a, -, hza⟩ := argVals_mem hvs hz
        exact (hpr a z hza).1
    · obtain ⟨m, mv, hb, hmv, hshape⟩ := memLast_spec hml
      obtain ⟨L, w, rfl, hwm, hL⟩ := argVals_snoc hvs hb
      obtain ⟨L', w', rfl, hLL, hww⟩ := VRL.snoc_inv hrel
      have : L' = L := hLL.eq_of fun z hz => by
        obtain ⟨a, ha, hza⟩ := hL z hz
        exact hplain a (DSE.mem_of_mem_pop ha) (hpop a ha) z hza
      subst this
      have hwt := (hpr m w hwm).2
      rw [shape_arg hmv, hshape] at hwt
      rcases typedL_mem hwt with ⟨M, rfl⟩ | rfl
      · obtain ⟨M', rfl, hM⟩ := VR.mem_inv hww
        exact armMemOp_rel hfs hU (symOK_of (act_makeL0 tabs f) hnoE) harm
          (fun z hz => by
            obtain ⟨a, -, hza⟩ := hL z hz
            exact (hpr a z hza).1)
          hM (hpr m _ hwm).1
      · rw [hww.eq (fun _ => nofun) (fun _ => nofun)]
        exact resRel_refl _
  · -- an eliminated write
    obtain ⟨hop, hgc, -, -, hgid, hgty, -, m, hback, hgargs⟩ := elimV_spec he
    obtain ⟨vSm, vTm, hSm, hTm, hVm⟩ := hargs m (by rw [hgargs]; simp)
    rw [evalValueL_copy hgc hgargs hTm, hgid, tysL_eq R fv.id]
    refine ⟨fun y hy => ?_, fun e mm hp => absurd (evalValueL_panic_op hp) (elimOps_noPanic hop)⟩
    obtain ⟨vs, hvs⟩ := argVals_of_evalL (v := fv) (fun msg h' => by rw [h'] at hy; cases hy)
    rw [evalValueL_of_argVals hvs] at hy
    obtain ⟨r, hr, rfl⟩ := CSE.bind_ok hy
    obtain ⟨L, w, rfl, hwm, -⟩ := argVals_snoc hvs hback
    rw [hSm] at hwm; cases hwm
    refine ⟨_, rfl, VR.mdRetype ?_ _ _⟩
    by_cases hvd : fv.op = .VarDef
    · rw [evalOpL_generic _ _ _ _ _ _ (by rw [hvd]; rfl)] at hr
      rw [evalOp_memRoot (by simp [hvd])] at hr
      obtain ⟨M, n0, hL, hax, rfl, -⟩ := DSE.varDef_shape hvd hr
      rw [hax] at hn; cases hn
      obtain ⟨rfl, rfl⟩ := snoc_inj (L' := []) hL
      obtain ⟨M', rfl, hM⟩ := VR.mem_inv hVm
      refine .mem (EqOff.poison_left hM ⟨n, hnE, ?_⟩)
      rw [tabs_makeL, act_makeL0, frameBlk_temp (R.temp n hnE)]
    · obtain ⟨M, M1, rfl, rfl, hM1, -⟩ := elimStore (elimOps_store hop hvd) hop
        (fun k => symAddr_elim (v := { fv with auxInt := k }) hn hnE (R.temp n hnE)) hr
      obtain ⟨M', rfl, hM⟩ := VR.mem_inv hVm
      exact .mem (hM1 M' hM)

/-- **A value the source evaluates avoids the eliminated variables.** -/
theorem src_av {env : Env} (hfs : env.FrameSafe) {tabs : Tables} {f g : Func} {E : List AuxRef}
    (R : URel tabs f g E) {S : Frame} (hfok : FrameOK (UE E) S)
    (hpr : ∀ a y, S.regs[a]? = some (some y) → SPrL tabs f E a y)
    {x : ID} {fv : Value} (hfv : f.value? x = some fv) (hid : fv.id = x) {y : Val}
    (h : evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) S fv = .ok y) : SPrL tabs f E x y := by
  have hU := tempU_UE E
  refine ⟨?_, by have := evalValueL_typed h; rwa [hid] at this⟩
  obtain ⟨gv, -, hk⟩ := R.value x fv hfv
  rcases hk with ⟨-, hok⟩ | ⟨he, n, hn, hnE⟩
  · have hnoE := (keptOK_spec hok).1
    refine evalValueL_av hfs hU rfl hfok (symOK_of (act_makeL0 tabs f) hnoE)
      (fun n' _ hax hu => frameBlk_notUE (hnoE n' hax) (by rwa [act_makeL0] at hu))
      (fun a _ z hz => (hpr a z hz).1) h
  · obtain ⟨hop, -⟩ := elimV_spec he
    obtain ⟨vs, hvs⟩ := argVals_of_evalL (v := fv) (fun msg h' => by rw [h'] at h; cases h)
    rw [evalValueL_of_argVals hvs] at h
    obtain ⟨r, hr, rfl⟩ := CSE.bind_ok h
    have hav : ∀ z ∈ vs, Val.Avoids (UE E) z := fun z hz => by
      obtain ⟨a, -, hza⟩ := argVals_mem hvs hz
      exact (hpr a z hza).1
    refine mdRetype_av hU _ _ ?_
    obtain ⟨m, hback, -⟩ := (elimV_spec he).2.2.2.2.2.2.2
    obtain ⟨L, w, rfl, -, -⟩ := argVals_snoc hvs hback
    by_cases hvd : fv.op = .VarDef
    · rw [evalOpL_generic _ _ _ _ _ _ (by rw [hvd]; rfl), evalOp_memRoot (by simp [hvd])] at hr
      obtain ⟨M, n0, hL, -, rfl, -⟩ := DSE.varDef_shape hvd hr
      exact memAvoids_poison (hav (.mem M) (by rw [hL]; simp)) _
    · obtain ⟨M, M1, rfl, rfl, -, hA⟩ := elimStore (elimOps_store hop hvd) hop
        (fun k => symAddr_elim (v := { fv with auxInt := k }) hn hnE (R.temp n hnE)) hr
      exact hA hav

/-- **A value the source evaluates panics avoiding the eliminated variables.** -/
theorem src_panic {env : Env} (hfs : env.FrameSafe) {tabs : Tables} {f : Func} {E : List AuxRef}
    {S : Frame} (hpr : ∀ a y, S.regs[a]? = some (some y) → SPrL tabs f E a y) {fv : Value}
    {e : Panic} {m : Mem}
    (h : evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) S fv = .panic e m) :
    e.Avoids (UE E) ∧ m.Avoids (UE E) :=
  evalValueL_panic_av hfs (tempU_UE E) rfl (fun a _ z hz => (hpr a z hz).1) h

end GoFV.Proof.UnreadL
