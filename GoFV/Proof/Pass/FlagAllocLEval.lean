import GoFV.Proof.Pass.FlagAllocLCheck
import GoFV.Proof.Pass.MoveLOps
import GoFV.Proof.Pass.DeadRelL
import GoFV.Proof.DomRel
import GoFV.Proof.CheckFacts

/-!
# What `flagAllocB` gives, and evaluating clones (issue #385)

The checks of `GoFV.Proof.Pass.FlagAllocLCheck` as propositions (`args2_spec`, `keptB_spec`,
`keptOK_spec`, `cloneOK_spec`, …); a clone op evaluates to `cloneVal` of its op, shape, aux,
auxint and arguments (`evalOpL_clone`), so a clone and its original with equal arguments and
shapes evaluate alike (`evalValueL_clone`) and a clone op never panics; the contexts of
`runSched` (`Ctx.makeSched`).
-/

namespace GoFV.Proof.FlagAllocL

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof GoFV.Proof.MoveL

/-! ## The checks -/

theorem args2_spec {p : ID → ID → Bool} :
    ∀ {l l' : List ID}, args2 p l l' = true →
      l.length = l'.length ∧ ∀ (k : Nat) (b : ID), l'[k]? = some b → ∃ a, l[k]? = some a ∧ p a b = true
  | [], [], _ => ⟨rfl, fun _ _ h => by simp at h⟩
  | a :: l, b :: l', h => by
    simp only [args2, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := args2_spec h.2
    refine ⟨by simp [h1], fun k c hc => ?_⟩
    cases k with
    | zero => simp at hc; subst hc; exact ⟨a, rfl, h.1⟩
    | succ k => exact h2 k c (by simpa using hc)
  | [], _ :: _, h => by simp [args2] at h
  | _ :: _, [], h => by simp [args2] at h

theorem listedIn_spec {f : Func} {b x : ID} (h : listedIn f b x = true) :
    ∃ blk, f.block? b = some blk ∧ x ∈ blk.values := by
  unfold listedIn at h
  cases hb : f.block? b with
  | none => rw [hb] at h; cases h
  | some blk => rw [hb] at h; exact ⟨blk, rfl, by simpa using h⟩

theorem listedIn_of {f : Func} {b x : ID} {blk : Block} (hb : f.block? b = some blk)
    (hx : x ∈ blk.values) : listedIn f b x = true := by
  unfold listedIn; rw [hb]; simpa using hx

/-- `g`'s block `b` is well formed (`ownB`). -/
structure GOwn (g : Func) (b : ID) (gb : Block) : Prop where
  id : gb.id = b
  nd : gb.values.toList.Nodup
  valueId : ∀ x ∈ gb.values, ∃ v, g.value? x = some v ∧ v.id = x ∧ v.block = b

theorem ownB_spec {g : Func} {b : ID} {gb : Block} (h : ownB g b gb = true) : GOwn g b gb := by
  unfold ownB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun x hx => ?_⟩
  have := (Array.all_eq_true_iff_forall_mem.1 h3) x hx
  split at this
  · rename_i v hv
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨v, hv, this.1, this.2⟩
  · cases this

theorem keptB_spec {f g : Func} {x : ID} (h : keptB f g x = true) :
    ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧ fv.block = gv.block ∧
      listedIn f fv.block x = true ∧ listedIn g gv.block x = true := by
  unfold keptB at h
  split at h
  · rename_i fv gv hf hg
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨fv, gv, hf, hg, h.1.1, h.1.2, h.2⟩
  · cases h

/-- A value of `g`'s block not in `f`'s is not kept. -/
theorem not_kept_g {f g : Func} {b : ID} {fb gb : Block} (hO : GOwn g b gb)
    (hfb : f.block? b = some fb) {x : ID}
    (hxg : x ∈ gb.values) (hxf : x ∉ fb.values) : keptB f g x = false := by
  cases hk : keptB f g x with
  | false => rfl
  | true =>
    obtain ⟨fv, gv, -, hgv, hbl, hlf, -⟩ := keptB_spec hk
    obtain ⟨gv', hgv', -, hgvb⟩ := hO.valueId x hxg
    rw [hgv] at hgv'; cases hgv'
    rw [hbl, hgvb] at hlf
    obtain ⟨blk, hblk, hx⟩ := listedIn_spec hlf
    rw [hfb] at hblk; cases hblk
    exact absurd hx hxf

/-- A value of `f`'s block not in `g`'s is not kept. -/
theorem not_kept_f {ce : CheckEnv} {f g : Func} (hwf : WF ce f) {b : ID} {fb gb : Block}
    (hb : b ∈ f.blocks) (hfb : f.block? b = some fb) (hgb : g.block? b = some gb) {x : ID}
    (hxf : x ∈ fb.values) (hxg : x ∉ gb.values) : keptB f g x = false := by
  cases hk : keptB f g x with
  | false => rfl
  | true =>
    obtain ⟨fv, gv, hfv, -, hbl, -, hlg⟩ := keptB_spec hk
    obtain ⟨fv', hfv', -, hfvb⟩ := hwf.valueId b fb ⟨hb, hfb⟩ x hxf
    rw [hfv] at hfv'; cases hfv'
    rw [← hbl, hfvb] at hlg
    obtain ⟨blk, hblk, hx⟩ := listedIn_spec hlg
    rw [hgb] at hblk; cases hblk
    exact absurd hx hxg

theorem argRel_spec {f g : Func} {C : List (ID × ID)} {ga fa : ID}
    (h : argRel f g C ga fa = true) : (ga = fa ∧ keptB f g ga = true) ∨ (ga, fa) ∈ C := by
  unfold argRel at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  exact h

theorem keptOK_spec {f g : Func} {C : List (ID × ID)} {x : ID} (h : keptOK f g C x = true) :
    ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧ gv.op = fv.op ∧ gv.type = fv.type ∧
      gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧ sxOf g gv = sxOf f fv ∧
      args2 (argRel f g C) gv.args.toList fv.args.toList = true := by
  unfold keptOK at h
  split at h
  · rename_i fv gv hf hg
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact ⟨fv, gv, hf, hg, h1, h2, h3, h4, h5, h6⟩
  · cases h

theorem cloneOK_spec {dc : Cert} {f g : Func} {b : ID} {P : List ID} {C : List (ID × ID)}
    {x o : ID} (h : cloneOK dc f g b P C x o = true) :
    ∃ ov gv, f.value? o = some ov ∧ g.value? x = some gv ∧ cloneOp gv.op = true ∧
      gv.op = ov.op ∧ gv.type = ov.type ∧ gv.aux = ov.aux ∧ gv.auxInt = ov.auxInt ∧
      args2 (argRel f g C) gv.args.toList ov.args.toList = true ∧
      (o ∈ P ∨ (ov.block ≠ b ∧ dc.anc ov.block b = true ∧ ov.block ∈ f.blocks ∧
        listedIn f ov.block o = true)) := by
  unfold cloneOK at h
  split at h
  · rename_i ov gv hf hg
    simp only [availB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      List.contains_iff_mem, Array.contains_iff_mem] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    refine ⟨ov, gv, hf, hg, h1, h2, h3, h4, h5, h6, ?_⟩
    rcases h7 with h7 | ⟨⟨⟨h7, h8⟩, h9⟩, h10⟩
    · exact .inl h7
    · exact .inr ⟨h7, h8, h9, h10⟩
  · cases h

theorem topoOK_spec {f : Func} {L : List ID} {z : ID} (h : topoOK f L z = true) :
    ∃ v, f.value? z = some v ∧ ∀ a ∈ v.args, a ∉ L := by
  unfold topoOK at h
  split at h
  · rename_i v hv
    refine ⟨v, hv, fun a ha => ?_⟩
    have := (Array.all_eq_true_iff_forall_mem.1 h) a ha
    simpa using this
  · cases h

theorem remOK_spec {f : Func} {z : ID} (h : remOK f z = true) :
    ∃ v, f.value? z = some v ∧ cloneOp v.op = true := by
  unfold remOK at h
  cases hv : f.value? z with
  | none => rw [hv] at h; cases h
  | some v => rw [hv] at h; exact ⟨v, rfl, h⟩

theorem ctrlsOK_spec {f g : Func} {fb gb : Block} {C : List (ID × ID)}
    (h : ctrlsOK f g fb gb C = true) :
    args2 (argRel f g C) gb.controls.toList fb.controls.toList = true ∧
      (gb.controls = fb.controls ∨ fb.kind.isArm64 = true) := by
  unfold ctrlsOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h

theorem phisOK_spec {f g : Func} {fb gb : Block} (h : phisOK f g fb gb = true) :
    fb.values.filter (isPhiIn f) = gb.values.filter (isPhiIn g) ∧
      ∀ x ∈ fb.values.filter (isPhiIn f), ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧
        gv.op = fv.op ∧ gv.type = fv.type ∧ gv.args = fv.args ∧ ∀ a ∈ fv.args, keptB f g a = true := by
  unfold phisOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun x hx => ?_⟩
  have := (Array.all_eq_true_iff_forall_mem.1 h.2) x hx
  split at this
  · rename_i fv gv hf hg
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩, -⟩, h7⟩ := this
    exact ⟨fv, gv, hf, hg, h1, h2, h5, fun a ha => (Array.all_eq_true_iff_forall_mem.1 h7) a ha⟩
  · cases this

/-- What `blockB` checks of block `b`. -/
theorem blockB_spec {tabs : Tables} {dc : Cert} {f g : Func} {cert : Array (Option ID)} {b : ID}
    (h : blockB (Ctx.makeL tabs f).tys (Ctx.makeL tabs g).tys dc f g cert b = true) :
    ∃ fb gb, f.block? b = some fb ∧ g.block? b = some gb ∧ GOwn g b gb ∧ gb.kind = fb.kind ∧
      gb.auxInt = fb.auxInt ∧ gb.succs = fb.succs ∧ gb.preds = fb.preds ∧ phisOK f g fb gb = true ∧
      schedOrder g (Ctx.makeL tabs g).tys gb = some (gb.values.filter (!isPhiIn g ·)) ∧
      (schedOrder f (Ctx.makeL tabs f).tys fb = none ∨
        schedOrder f (Ctx.makeL tabs f).tys fb = some (fb.values.filter (!isPhiIn f ·))) ∧
      walkB dc f g cert b fb gb (fb.values.filter (!isPhiIn f ·)).toList
        (gb.values.filter (!isPhiIn g ·)).toList [] [] = true := by
  unfold blockB at h
  split at h
  · rename_i fb gb hf hg
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, ⟨⟨h7, h8⟩, h9⟩⟩ := h
    exact ⟨fb, gb, hf, hg, ownB_spec h0, h1, h2, h3, h4, h5, h7, h8, h9⟩
  · cases h

/-- What `flagAllocWith` checks. -/
theorem flagAllocWith_spec {tabs : Tables} {cert : Array (Option ID)} {f g : Func}
    (h : flagAllocWith tabs cert f g = true) :
    g.entry = f.entry ∧ g.blocks = f.blocks ∧ g.ownAux = f.ownAux ∧ g.lowered = f.lowered ∧
      ∀ b ∈ f.blocks,
        blockB (Ctx.makeL tabs f).tys (Ctx.makeL tabs g).tys (make f) f g cert b = true := by
  unfold flagAllocWith at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun b hb => (Array.all_eq_true_iff_forall_mem.1 h5) b hb⟩

/-! ## Clone ops -/

/-- The result of a clone op: Phase 1's `evalPure` for `Select0`/`Select1`, else
`Arm64.evalPure`. -/
def cloneVal (op : Op) (ty : Ty) (ai : Int64) (aux : Option AuxRef) (argv : List Val) : Val :=
  if op.generic then evalPure op ty ai aux argv else Arm64.evalPure op ty ai aux argv

/-- **A clone op evaluates** to `cloneVal`. -/
theorem evalOpL_clone {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (h : cloneOp v.op = true) :
    evalOpL faulting env ctx fr v argv ty = .ok (cloneVal v.op ty v.auxInt v.aux argv) := by
  unfold cloneOp at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with (hop | hop) | ⟨⟨hg, ha⟩, hr⟩
  all_goals first
    | (have hg : v.op.generic = true := by rw [hop]; rfl
       rw [evalOpL_generic _ _ _ _ _ _ hg]
       have hr : isRoot v.op = false := by rw [hop]; rfl
       rw [CSE.evalOp_tail hr (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
         (by rw [hop]; nofun) (by rw [hop]; nofun)]
       have hf : frameVal ctx v = none := by unfold frameVal; rw [hop]
       rw [hf]
       unfold cloneVal
       rw [hg]
       rfl)
    | (rw [evalOpL_pure hg ha, hr]
       unfold cloneVal
       rw [hg]
       rfl)

theorem mapM_args_ok_or_stuck {fr : Frame} {v : Value} :
    (∃ argv, v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) = .ok argv) ∨
    (∃ msg, v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) = .stuck msg) := by
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | ok argv => exact .inl ⟨argv, rfl⟩
  | stuck msg => exact .inr ⟨msg, rfl⟩
  | panic e m => exact absurd hm mapM_ofOption_ne_panic

/-- A clone op never panics. -/
theorem evalValueL_clone_not_panic {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (hc : cloneOp v.op = true) {e : Panic} {m : Mem} : evalValueL md env ctx fr v ≠ .panic e m := by
  unfold evalValueL
  rcases mapM_args_ok_or_stuck (fr := fr) (v := v) with ⟨argv, hm⟩ | ⟨msg, hm⟩
  · rw [hm]
    simp only [bind, Res.bind]
    rw [evalOpL_clone hc]
    nofun
  · rw [hm]
    nofun

/-- **A clone evaluates as its original**: same op (a clone op), aux, auxint and shape, and
arguments with equal registers. -/
theorem evalValueL_clone {md : LMode} {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame}
    {v v' : Value} (hc : cloneOp v'.op = true) (hop : v'.op = v.op) (haux : v'.aux = v.aux)
    (hai : v'.auxInt = v.auxInt) (hsz : v'.args.size = v.args.size)
    (hargs : ∀ (k : Nat) (a : ID), v.args[k]? = some a →
      ∃ a' y, v'.args[k]? = some a' ∧ fr.regs[a]? = some (some y) ∧ fr'.regs[a']? = some (some y))
    (hty : ctx'.tys[v'.id]? = ctx.tys[v.id]?) :
    evalValueL md env ctx' fr' v' = evalValueL md env ctx fr v := by
  have hc' : cloneOp v.op = true := hop ▸ hc
  unfold evalValueL
  rw [mapM_ofOption_eq (l := v'.args.toList) (l' := v.args.toList)
    (m := fun a => s!"v{v'.id}: argument v{a} has no value")
    (m' := fun a => s!"v{v.id}: argument v{a} has no value")
    (r := fun a => (fr'.regs[a]?).join) (r' := fun a => (fr.regs[a]?).join) (by simp [hsz])
    (fun k a' ha' => by
      have hk : k < v.args.size := by
        have := (List.getElem?_eq_some_iff.1 ha').1; simp at this; omega
      obtain ⟨a'', y, h1, h2, h3⟩ := hargs k v.args[k] (by simp [hk])
      rw [Array.getElem?_toList] at ha'
      rw [ha'] at h1; cases h1
      exact ⟨v.args[k], y, by simp [hk], by simp [h3], by simp [h2]⟩)]
  simp only [bind, Res.bind]
  congr 1
  funext argv
  rw [hty, evalOpL_clone hc, evalOpL_clone hc', hop, haux, hai]

/-! ## `runSched`'s contexts -/

theorem makeSched_f (tabs : Tables) (f : Func) : (Ctx.makeSched tabs f).f = f := makeL_f tabs f

theorem makeSched_tabs (tabs : Tables) (f : Func) : (Ctx.makeSched tabs f).tabs = tabs :=
  tabs_makeL tabs f

theorem makeSched_tys (tabs : Tables) (f : Func) :
    (Ctx.makeSched tabs f).tys = (Ctx.makeL tabs f).tys := rfl

theorem makeSched_params (tabs : Tables) (f : Func) :
    (Ctx.makeSched tabs f).params = (Ctx.makeL tabs f).params := rfl

theorem makeSched_act (tabs : Tables) (f : Func) :
    (Ctx.makeSched tabs f).act = (Ctx.makeL tabs f).act := rfl

/-- `runSched`'s schedule of a block: its `schedOrder`. -/
theorem sched_makeSched {tabs : Tables} {f : Func} {b : ID} {blk : Block}
    (hb : f.block? b = some blk) :
    ((Ctx.makeSched tabs f).sched[b]?).join = schedOrder f (Ctx.makeL tabs f).tys blk := by
  unfold Ctx.makeSched Func.block? at *
  simp only [Array.getElem?_map]
  cases h : f.blockTab[b]? with
  | none => rw [h] at hb; cases hb
  | some o => rw [h] at hb; cases o with
    | none => cases hb
    | some blk' => cases hb; rfl

/-- Values of `f` and `g` of the same type have the same shape (lowered alike). -/
theorem tys_eq {tabs : Tables} {f g : Func} (hlow : g.lowered = f.lowered) {x y : ID}
    {gv fv : Value} (hg : g.value? x = some gv) (hf : f.value? y = some fv) (ht : gv.type = fv.type) :
    (Ctx.makeSched tabs g).tys[x]? = (Ctx.makeSched tabs f).tys[y]? := by
  rw [makeSched_tys, makeSched_tys, Dead.tys_of_valueL hg, Dead.tys_of_valueL hf, hlow, ht]

theorem params_eq {tabs : Tables} {f g : Func} (hown : g.ownAux = f.ownAux) :
    (Ctx.makeSched tabs g).params = (Ctx.makeSched tabs f).params := by
  rw [makeSched_params, makeSched_params, params_makeL, params_makeL]
  simp only [Ctx.make, abiParams, hown]

theorem act_eq {tabs : Tables} {f g : Func} :
    (Ctx.makeSched tabs g).act = (Ctx.makeSched tabs f).act := by
  rw [makeSched_act, makeSched_act, act_makeL, act_makeL]; rfl

end GoFV.Proof.FlagAllocL
