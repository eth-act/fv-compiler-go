import GoFV.Proof.Pass.NilLateLRel
import GoFV.Proof.Speculate

variable [GoFV.SSA.Sem.Addrs]

/-!
# `late nilcheck` under `runSched`: a block's values

The source (`f`, its order `o`) and the target (`g`, `o` without the removed values) evaluate a
block's non-`Phi` values from frames that agree but on the removed values (`Agree`):

* `seg_panic`: after a removed check of `p` panicked (`p` nil), the target runs the values after
  it (removed checks absent, `safeOpB` values `.ok` or the same panic) to the value that faults
  on `p` (`faultsOnB`), which panics with the same `nilDeref` and memory;
* `block_sim`: the target's evaluation is the source's (`ResRel`): the same panic, or frames
  that agree; a removed check that does not panic only sets its own register.
-/

namespace GoFV.Proof.NilLateL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Opt.NilLate

/-! ## Frames -/

/-- The target frame is the source frame but on the removed values. -/
def Agree (rm : ID → Bool) (FS FT : Frame) : Prop :=
  FT = { FS with regs := FT.regs } ∧ FT.regs.size = FS.regs.size ∧
    ∀ z, rm z = false → FT.regs[z]? = FS.regs[z]?

theorem Agree.set_both {rm : ID → Bool} {FS FT : Frame} (h : Agree rm FS FT) (x : ID) (y : Val) :
    Agree rm (FS.set x y) (FT.set x y) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, by simp [Frame.set, h2], fun z hz => ?_⟩
  · rw [h1]; rfl
  · by_cases hzx : x = z
    · subst hzx
      by_cases hlt : x < FS.regs.size
      · rw [Frame.set_regs_self hlt, Frame.set_regs_self (by rw [h2]; exact hlt)]
      · simp [Frame.set, Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt, h2]
    · rw [Frame.set_regs_ne hzx, Frame.set_regs_ne hzx]; exact h3 z hz

theorem Agree.set_rm {rm : ID → Bool} {FS FT : Frame} (h : Agree rm FS FT) {x : ID}
    (hx : rm x = true) (y : Val) : Agree rm (FS.set x y) FT := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [h1]; rfl, by simp [Frame.set, h2], fun z hz => ?_⟩
  have hzx : x ≠ z := fun e => by subst e; rw [hx] at hz; cases hz
  rw [Frame.set_regs_ne hzx]; exact h3 z hz

theorem set_size (fr : Frame) (x : ID) (y : Val) : (fr.set x y).regs.size = fr.regs.size := by
  simp [Frame.set]

/-- Setting a register keeps the others' values. -/
theorem set_some {fr : Frame} {x a : ID} {y : Val} (hx : x < fr.regs.size)
    (h : a = x ∨ ∃ z, fr.regs[a]? = some (some z)) : ∃ z, (fr.set x y).regs[a]? = some (some z) := by
  by_cases hax : x = a
  · subst hax; exact ⟨y, Frame.set_regs_self hx⟩
  · rcases h with h | ⟨z, hz⟩
    · exact absurd h.symm hax
    · exact ⟨z, by rw [Frame.set_regs_ne hax, hz]⟩

/-! ## Arguments -/

private theorem mapM_vals {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L →
      l.map r = L.map some
  | [], L, h => by cases h; rfl
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : r a with
    | none => rw [ha] at h; cases h
    | some z =>
      rw [ha] at h
      change Res.bind (List.mapM (fun a => Res.ofOption (m a) (r a)) l) _ = _ at h
      cases hl : l.mapM (fun a => Res.ofOption (m a) (r a)) with
      | ok L' =>
        rw [hl] at h
        cases h
        simp only [List.map_cons, ha, mapM_vals hl]
      | panic e m' => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h

private theorem vals_get {l : List ID} {L : List Val} {r : ID → Option Val}
    (h : l.map r = L.map some) {k : Nat} {a : ID} {y : Val} (hl : l[k]? = some a)
    (hr : r a = some y) : L[k]? = some y := by
  have := congrArg (·[k]?) h
  simp only [List.getElem?_map, hl, Option.map_some, hr] at this
  cases hL : L[k]? with
  | none => rw [hL] at this; cases this
  | some z => rw [hL] at this; simp only [Option.map_some, Option.some.injEq] at this; rw [this]

private theorem vals_last {l : List ID} {L : List Val} {r : ID → Option Val}
    (h : l.map r = L.map some) {a : ID} {y : Val} (hl : l.getLast? = some a)
    (hr : r a = some y) : L.getLast? = some y := by
  have := congrArg List.getLast? h
  simp only [List.getLast?_map, hl, Option.map_some, hr] at this
  cases hL : L.getLast? with
  | none => rw [hL] at this; cases this
  | some z => rw [hL] at this; simp only [Option.map_some, Option.some.injEq] at this; rw [this]

/-- `evalValueL` once the arguments are read. -/
theorem evalValueL_bind {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val}
    (h : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) = .ok argv) :
    evalValueL md env ctx fr v =
      Res.bind (evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other))
        (fun r => .ok (md.retype (ctx.tys[v.id]?.getD .other) r)) := by
  unfold evalValueL; rw [h]; rfl

/-- The arguments of `v` all have registers: they are read. -/
theorem args_read {fr : Frame} {v : Value} (h : ∀ a ∈ v.args, ∃ y, fr.regs[a]? = some (some y)) :
    ∃ argv, v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) = .ok argv ∧
      v.args.toList.map (fun a => (fr.regs[a]?).join) = argv.map some := by
  obtain ⟨L, hL⟩ := mapM_ofOption_ok (m := fun a => s!"v{v.id}: argument v{a} has no value")
    (r := fun a => (fr.regs[a]?).join) (l := v.args.toList) (fun a ha => by
      obtain ⟨y, hy⟩ := h a (Array.mem_toList_iff.1 ha)
      exact ⟨y, by rw [hy]; rfl⟩)
  exact ⟨L, hL, mapM_vals hL⟩

theorem arg_val {fr : Frame} {v : Value} {argv : List Val}
    (h : v.args.toList.map (fun a => (fr.regs[a]?).join) = argv.map some) {k : Nat} {a : ID}
    {y : Val} (hk : v.args[k]? = some a) (hy : fr.regs[a]? = some (some y)) : argv[k]? = some y :=
  vals_get h (by rw [Array.getElem?_toList]; exact hk) (by rw [hy]; rfl)

theorem last_val {fr : Frame} {v : Value} {argv : List Val}
    (h : v.args.toList.map (fun a => (fr.regs[a]?).join) = argv.map some) {a : ID}
    {y : Val} (hk : v.args.back? = some a) (hy : fr.regs[a]? = some (some y)) :
    argv.getLast? = some y :=
  vals_last h (by rw [Array.getLast?_toList]; exact hk) (by rw [hy]; rfl)

/-! ## The two contexts -/

theorem eV_op {a b : Value} (h : eraseV a = eraseV b) : a.op = b.op := by
  have := congrArg Value.op h; exact this
theorem eV_args {a b : Value} (h : eraseV a = eraseV b) : a.args = b.args := by
  have := congrArg Value.args h; exact this
theorem eV_aux {a b : Value} (h : eraseV a = eraseV b) : a.aux = b.aux := by
  have := congrArg Value.aux h; exact this
theorem eV_auxInt {a b : Value} (h : eraseV a = eraseV b) : a.auxInt = b.auxInt := by
  have := congrArg Value.auxInt h; exact this
theorem eV_id {a b : Value} (h : eraseV a = eraseV b) : a.id = b.id := by
  have := congrArg Value.id h; exact this
theorem eV_type {a b : Value} (h : eraseV a = eraseV b) : a.type = b.type := by
  have := congrArg Value.type h; exact this

theorem nlSched_f (tabs : Tables) (f : Func) : (Ctx.makeSched tabs f).f = f := makeL_f tabs f

theorem nlSched_tabs (tabs : Tables) (f : Func) : (Ctx.makeSched tabs f).tabs = tabs :=
  tabs_makeL tabs f

variable {tabs : Tables} {f g : Func} {rm : ID → Bool}

theorem NLRel.val (R : NLRel tabs f g rm) {x : ID} (hx : rm x = false) {w : Value}
    (hw : f.value? x = some w) : ∃ w', g.value? x = some w' ∧ eraseV w' = eraseV w := by
  have h := R.value x
  rw [hx, hw] at h
  simp only [Bool.false_eq_true, ite_false, Option.map_some] at h
  cases hg : g.value? x with
  | none => rw [hg] at h; cases h
  | some w' => rw [hg] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨w', rfl, h⟩

theorem NLRel.val_rm (R : NLRel tabs f g rm) {x : ID} (hx : rm x = true) : g.value? x = none := by
  have h := R.value x
  rw [hx] at h
  simp only [ite_true, Option.map_eq_none_iff] at h
  exact h

theorem NLRel.val_none (R : NLRel tabs f g rm) {x : ID} (hw : f.value? x = none) :
    g.value? x = none := by
  have h := R.value x
  rw [hw] at h
  simp only [Option.map_none, ite_self, Option.map_eq_none_iff] at h
  exact h

theorem NLRel.params (R : NLRel tabs f g rm) :
    (Ctx.makeSched tabs g).params = (Ctx.makeSched tabs f).params := by
  show (Ctx.makeL tabs g).params = (Ctx.makeL tabs f).params
  rw [params_makeL, params_makeL]
  simp only [Ctx.make, abiParams, R.ownAux]

theorem NLRel.act (_R : NLRel tabs f g rm) :
    (Ctx.makeSched tabs g).act = (Ctx.makeSched tabs f).act := by
  show (Ctx.makeL tabs g).act = (Ctx.makeL tabs f).act
  rw [act_makeL, act_makeL]; rfl

private theorem valueTy_erase {S : Array Ty} {o o' : Option Value}
    (h : o.map eraseV = o'.map eraseV) : valueTy S o = valueTy S o' := by
  cases o with
  | none => cases o' with
    | none => rfl
    | some _ => cases h
  | some v => cases o' with
    | none => cases h
    | some v' =>
      simp only [Option.map_some, Option.some.injEq] at h
      have : v.type = v'.type := eV_type h
      simp only [valueTy, this]

private theorem tys_get {S : Array Ty} (f : Func) (x : ID) :
    (f.valueTab.map (valueTy S))[x]? =
      if x < f.valueTab.size then some (valueTy S (f.value? x)) else none := by
  rw [Array.getElem?_map]
  by_cases hx : x < f.valueTab.size
  · simp only [hx, ite_true, Func.value?, Array.getElem?_eq_getElem hx, Option.map_some,
      Option.join_some]
  · simp only [hx, ite_false, Array.getElem?_eq_none (Nat.le_of_not_lt hx), Option.map_none]

theorem NLRel.tys (R : NLRel tabs f g rm) {x : ID} (hx : rm x = false) :
    (Ctx.makeSched tabs g).tys[x]? = (Ctx.makeSched tabs f).tys[x]? := by
  have hv : (g.value? x).map eraseV = (f.value? x).map eraseV := by
    rw [R.value x, hx]; rfl
  show (Ctx.makeL tabs g).tys[x]? = (Ctx.makeL tabs f).tys[x]?
  unfold Ctx.makeL
  rw [R.lowered]
  split
  · simp only [tys_get, R.vsize, valueTy_erase hv]
  · simp only [Ctx.make, tys_get, R.vsize, valueTy_erase hv]

/-- What `MOVDreg`/`MOVDnop` read of the function agrees on kept values. -/
theorem NLRel.sx (R : NLRel tabs f g rm) {x : ID} (hx : rm x = false) {w w' : Value}
    (hw : f.value? x = some w) (he : eraseV w' = eraseV w) : sxOf g w' = sxOf f w := by
  have hargs : w'.args = w.args := eV_args he
  unfold sxOf
  rw [hargs]
  cases ha : w.args[0]? with
  | none => rfl
  | some a =>
    have hra : rm a = false := R.usedV x w hx hw a (Array.mem_of_getElem? ha)
    simp only [Option.bind_some]
    cases hfa : f.value? a with
    | none => rw [R.val_none hfa]; rfl
    | some u =>
      obtain ⟨u', hgu, heu⟩ := R.val hra hfa
      rw [hgu]
      simp only [Option.map_some, Option.some.injEq]
      have huop : u'.op = u.op := eV_op heu
      have huargs : u'.args = u.args := eV_args heu
      refine Arm64.signExtendsIn_congr huop ?_
      intro _
      rw [huargs]
      cases hc : u.args[0]? with
      | none => rfl
      | some c =>
        have hrc : rm c = false := R.usedV a u hra hfa c (Array.mem_of_getElem? hc)
        simp only [Option.bind_some]
        cases hfc : f.value? c with
        | none => rw [R.val_none hfc]
        | some t =>
          obtain ⟨t', hgt, het⟩ := R.val hrc hfc
          rw [hgt]
          simp only [Option.map_some, eV_op het]

/-- **A kept value evaluates alike** in the target and source contexts from agreeing frames. -/
theorem NLRel.eval (R : NLRel tabs f g rm) {md : LMode} {env : Env} {FS FT : Frame}
    (hA : Agree rm FS FT) {x : ID} (hx : rm x = false) {w w' : Value} (hw : f.value? x = some w)
    (hid : w.id = x) (he : eraseV w' = eraseV w)
    (hset : ∀ a ∈ w.args, ∃ y, FS.regs[a]? = some (some y)) :
    evalValueL md env (Ctx.makeSched tabs g) FT w' = evalValueL md env (Ctx.makeSched tabs f) FS w := by
  have hargs : w'.args = w.args := eV_args he
  refine evalValueL_eq_of_args (eV_op he) (eV_aux he) (eV_auxInt he) (eV_id he) (by rw [hargs])
    (fun k a hk => ?_) hA.1 (by rw [hid]; exact R.tys hx) (by rw [nlSched_tabs, nlSched_tabs])
    R.params R.act (by rw [nlSched_f, nlSched_f]; exact R.sx hx hw he)
  have ha : a ∈ w.args := Array.mem_of_getElem? hk
  obtain ⟨y, hy⟩ := hset a ha
  refine ⟨a, y, by rw [hargs]; exact hk, hy, ?_⟩
  rw [hA.2.2 a (R.usedV x w hx hw a ha), hy]

/-! ## After a removed check panicked -/

/-- **The target reaches the fault**: after a removed check of `p` (on memory `mm`) panicked, `p`'s
base being nil, the target's values up to the one that faults on `p` panic with the same
`nilDeref` and memory. -/
theorem seg_panic (R : NLRel tabs f g rm) {env : Env} {blk : Array ID} {p mm : ID} {pv : Val}
    {b : Ptr} {m : Mem} (hpv : Arm64.addr pv 0 = some b) (hb : b.isNil = true) :
    ∀ (xs avail : List ID) (G : Frame), segB f rm blk p mm avail xs = true →
      G.regs.size = f.valueTab.size →
      G.regs[p]? = some (some pv) → G.regs[mm]? = some (some (.mem m)) →
      (∀ a ∈ avail, rm a = false → ∃ y, G.regs[a]? = some (some y)) →
      (∀ x ∈ xs, rm x = false → ∀ w, f.value? x = some w → ∀ a ∈ w.args,
        blk.contains a = false → ∃ y, G.regs[a]? = some (some y)) →
      evalAllL ⟨f.lowered, true⟩ env (Ctx.makeSched tabs g) G (xs.filter (!rm ·)) =
        .panic .nilDeref m := by
  intro xs
  induction xs with
  | nil => intro _ _ h; simp [segB] at h
  | cons x xs ih =>
    intro avail G hseg hsz hp hmm hav hout
    have hout' : ∀ x' ∈ xs, rm x' = false → ∀ w, f.value? x' = some w → ∀ a ∈ w.args,
        blk.contains a = false → ∃ y, G.regs[a]? = some (some y) :=
      fun x' hx' => hout x' (List.mem_cons_of_mem _ hx')
    unfold segB at hseg
    by_cases hrx : rm x = true
    · simp only [hrx, ite_true] at hseg
      rw [List.filter_cons_of_neg (by simp [hrx])]
      exact ih avail G hseg hsz hp hmm hav hout'
    · have hrx' : rm x = false := by simpa using hrx
      simp only [hrx', Bool.false_eq_true, ite_false] at hseg
      cases hw : f.value? x with
      | none => rw [hw] at hseg; cases hseg
      | some w =>
      rw [hw] at hseg
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hseg
      obtain ⟨hav', hrest⟩ := hseg
      rw [List.filter_cons_of_pos (by simp [hrx']), evalAllL_cons]
      obtain ⟨w', hgw, he⟩ := R.val hrx' hw
      rw [stepVL_of (by rw [nlSched_f]; exact hgw), ← evalValueL_eraseV, he, evalValueL_eraseV]
      -- every argument has a register
      have hset : ∀ a ∈ w.args, ∃ y, G.regs[a]? = some (some y) := by
        intro a ha
        unfold argsAvailB at hav'
        have h1 := Array.all_eq_true.1 hav'
        obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 ha
        have h2 := h1 k hk
        simp only [Bool.or_eq_true, Bool.not_eq_true'] at h2
        rcases h2 with h2 | h2
        · exact hav _ (List.contains_iff_mem.1 h2) (R.usedV x w hrx' hw _ ha)
        · exact hout x List.mem_cons_self hrx' w hw _ ha h2
      obtain ⟨argv, hmap, hvals⟩ := args_read hset
      rw [evalValueL_bind hmap]
      rcases hrest with hf | ⟨⟨⟨hsafe, hxp⟩, hxm⟩, hseg'⟩
      · -- the faulting value
        have hfo := hf
        unfold faultsOnB at hfo
        simp only [Bool.and_eq_true, beq_iff_eq] at hfo
        have hback : w.args.back? = some mm := hfo.1.2
        have hpan := faults_panic (env := env) (ctx := Ctx.makeSched tabs g) (fr := G)
          (ty := (Ctx.makeSched tabs g).tys[w.id]?.getD .other) hf
          (fun k hk => arg_val hvals hk hp) (last_val hvals hback hmm) hpv hb
        rw [show (⟨f.lowered, true⟩ : LMode).faulting = true from rfl, hpan]
        rfl
      · have hlast : w.args.back? = some mm → argv.getLast? = some (.mem m) :=
          fun hb' => last_val hvals hb' hmm
        rcases safe_res (env := env) (ctx := Ctx.makeSched tabs g) (fr := G)
            (ty := (Ctx.makeSched tabs g).tys[w.id]?.getD .other) hsafe hlast with
          ⟨r, hr⟩ | hr
        · rw [show (⟨f.lowered, true⟩ : LMode).faulting = true from rfl, hr]
          simp only [Res.bind]
          have hxlt : x < G.regs.size := by rw [hsz]; exact lt_of_value? hw
          refine ih (x :: avail) _ hseg' (by rw [set_size, hsz]) ?_ ?_ ?_ ?_
          · rw [Frame.set_regs_ne hxp]; exact hp
          · rw [Frame.set_regs_ne hxm]; exact hmm
          · intro a ha hra
            rcases List.mem_cons.1 ha with rfl | ha
            · exact set_some hxlt (.inl rfl)
            · exact set_some hxlt (.inr (hav a ha hra))
          · intro x' hx' hrx'' w'' hw'' a ha hb''
            exact set_some hxlt (.inr (hout' x' hx' hrx'' w'' hw'' a ha hb''))
        · rw [show (⟨f.lowered, true⟩ : LMode).faulting = true from rfl, hr]
          rfl

/-! ## A block's values -/

/-- How the target's evaluation of a block's values relates to the source's: the same panic, or
agreeing frames (a `stuck` source asks nothing). -/
def ResRel (rm : ID → Bool) : Res Frame → Res Frame → Prop
  | .ok FS, rT => ∃ FT, rT = .ok FT ∧ Agree rm FS FT
  | .panic e m, rT => rT = .panic e m
  | .stuck _, _ => True

private theorem stepVL_none {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {x : ID}
    (h : ctx.f.value? x = none) : ∃ msg, stepVL md env ctx fr x = .stuck msg := by
  unfold stepVL; rw [h]; exact ⟨_, rfl⟩

/-- **A block's values** (`ResRel`): the target evaluates the source's order without the removed
values. -/
theorem block_sim (R : NLRel tabs f g rm) {env : Env} {blk : Array ID} :
    ∀ (o pre : List ID) (FS FT : Frame), blockB f rm blk pre o = true → Agree rm FS FT →
      FS.regs.size = f.valueTab.size →
      (∀ a ∈ pre, rm a = false → ∃ y, FS.regs[a]? = some (some y)) →
      (∀ x ∈ o, rm x = false → ∀ w, f.value? x = some w → ∀ a ∈ w.args,
        blk.contains a = false → ∃ y, FS.regs[a]? = some (some y)) →
      (∀ x ∈ o, ∀ w, f.value? x = some w → w.id = x) →
      ResRel rm (evalAllL ⟨f.lowered, true⟩ env (Ctx.makeSched tabs f) FS o)
        (evalAllL ⟨f.lowered, true⟩ env (Ctx.makeSched tabs g) FT (o.filter (!rm ·))) := by
  intro o
  induction o with
  | nil => intro _ FS FT _ hA _ _ _ _; exact ⟨FT, rfl, hA⟩
  | cons x xs ih =>
    intro pre FS FT hbl hA hsz hpre hout hids
    unfold blockB at hbl
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hbl
    obtain ⟨hx, hbl'⟩ := hbl
    have hout' : ∀ x' ∈ xs, rm x' = false → ∀ w, f.value? x' = some w → ∀ a ∈ w.args,
        blk.contains a = false → ∃ y, FS.regs[a]? = some (some y) :=
      fun x' hx' => hout x' (List.mem_cons_of_mem _ hx')
    have hids' : ∀ x' ∈ xs, ∀ w, f.value? x' = some w → w.id = x' :=
      fun x' hx' => hids x' (List.mem_cons_of_mem _ hx')
    rw [evalAllL_cons]
    cases hfx : f.value? x with
    | none =>
      obtain ⟨msg, hst⟩ := stepVL_none (md := ⟨f.lowered, true⟩) (env := env) (fr := FS)
        (ctx := Ctx.makeSched tabs f) (by rw [nlSched_f]; exact hfx)
      rw [hst]; trivial
    | some w =>
    rw [stepVL_of (by rw [nlSched_f]; exact hfx)]
    have hxlt : x < FS.regs.size := by rw [hsz]; exact lt_of_value? hfx
    -- the frames after `x` keep the facts
    have hpre' : ∀ y : Val, ∀ a ∈ x :: pre, rm a = false →
        ∃ z, (FS.set x y).regs[a]? = some (some z) := by
      intro y a ha hra
      rcases List.mem_cons.1 ha with rfl | ha
      · exact set_some hxlt (.inl rfl)
      · exact set_some hxlt (.inr (hpre a ha hra))
    have hout'' : ∀ y : Val, ∀ x' ∈ xs, rm x' = false → ∀ w, f.value? x' = some w →
        ∀ a ∈ w.args, blk.contains a = false → ∃ z, (FS.set x y).regs[a]? = some (some z) :=
      fun y x' hx' hr w hw a ha hb => set_some hxlt (.inr (hout' x' hx' hr w hw a ha hb))
    by_cases hrx : rm x = true
    · -- a removed check
      have hrem : removedB f rm blk x pre xs = true := by
        rcases hx with h | h
        · rw [hrx] at h; cases h
        · exact h
      unfold removedB at hrem
      rw [hfx] at hrem
      simp only [Bool.and_eq_true, beq_iff_eq] at hrem
      obtain ⟨hop, hrest⟩ := hrem
      split at hrest
      · rename_i p mm hpm
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hrest
        obtain ⟨⟨hrp, hrmm⟩, hseg⟩ := hrest
        rw [List.filter_cons_of_neg (by simp [hrx])]
        cases hres : evalValueL ⟨f.lowered, true⟩ env (Ctx.makeSched tabs f) FS w with
        | ok y =>
          exact ih (x :: pre) (FS.set x y) FT hbl' (hA.set_rm hrx y) (by rw [set_size, hsz])
            (hpre' y) (hout'' y) hids'
        | stuck msg => trivial
        | panic e m =>
          show evalAllL _ env _ FT _ = .panic e m
          cases hm : w.args.toList.mapM (fun a =>
              Res.ofOption s!"v{w.id}: argument v{a} has no value" (FS.regs[a]?).join) with
          | panic e' m' => exact absurd hm mapM_ofOption_ne_panic
          | stuck msg => unfold evalValueL at hres; rw [hm] at hres; cases hres
          | ok argv =>
          rw [evalValueL_bind hm] at hres
          cases hev : evalOpL true env (Ctx.makeSched tabs f) FS w argv
              ((Ctx.makeSched tabs f).tys[w.id]?.getD .other) with
          | ok r => rw [show (⟨f.lowered, true⟩ : LMode).faulting = true from rfl, hev] at hres
                    cases hres
          | stuck msg => rw [show (⟨f.lowered, true⟩ : LMode).faulting = true from rfl, hev] at hres
                         cases hres
          | panic e' m' =>
          rw [show (⟨f.lowered, true⟩ : LMode).faulting = true from rfl, hev] at hres
          cases hres
          obtain ⟨rfl, hlast, a, b, hhead, haddr, hnil⟩ := nc_panic hop hev
          have hvals := mapM_vals hm
          rw [hpm] at hvals
          -- the pointer and the memory registers
          cases argv with
          | nil => simp at hvals
          | cons ap rest =>
          cases rest with
          | nil => simp at hvals
          | cons am rest =>
          cases rest with
          | cons _ _ => simp at hvals
          | nil =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hvals
          obtain ⟨hpv, hmv⟩ := hvals
          simp only [List.head?_cons, Option.some.injEq] at hhead
          rw [← hhead] at haddr
          simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
          subst hlast
          have hp : FS.regs[p]? = some (some ap) := by
            cases h : FS.regs[p]? with
            | none => rw [h] at hpv; cases hpv
            | some o => rw [h] at hpv; cases o with
              | none => cases hpv
              | some z => simp only [Option.join_some, Option.some.injEq] at hpv; rw [hpv]
          have hmm' : FS.regs[mm]? = some (some (.mem m)) := by
            cases h : FS.regs[mm]? with
            | none => rw [h] at hmv; cases hmv
            | some o => rw [h] at hmv; cases o with
              | none => cases hmv
              | some z => simp only [Option.join_some, Option.some.injEq] at hmv; rw [hmv]
          refine seg_panic R haddr hnil xs pre FT hseg (by rw [hA.2.1, hsz])
            (by rw [hA.2.2 p hrp, hp]) (by rw [hA.2.2 mm hrmm, hmm']) ?_ ?_
          · intro a ha hra; rw [hA.2.2 a hra]; exact hpre a ha hra
          · intro x' hx' hr w' hw' a ha hb
            rw [hA.2.2 a (R.usedV x' w' hr hw' a ha)]
            exact hout' x' hx' hr w' hw' a ha hb
      · cases hrest
    · -- a kept value
      have hrx' : rm x = false := by simpa using hrx
      rw [List.filter_cons_of_pos (by simp [hrx']), evalAllL_cons]
      obtain ⟨w', hgw, he⟩ := R.val hrx' hfx
      rw [stepVL_of (by rw [nlSched_f]; exact hgw)]
      cases hres : evalValueL ⟨f.lowered, true⟩ env (Ctx.makeSched tabs f) FS w with
      | stuck msg => trivial
      | ok y =>
        have hset := evalValueL_args_def (fun msg h => by rw [hres] at h; cases h)
        rw [R.eval hA hrx' hfx (hids x List.mem_cons_self w hfx) he hset, hres]
        exact ih (x :: pre) (FS.set x y) (FT.set x y) hbl' (hA.set_both x y)
          (by rw [set_size, hsz]) (hpre' y) (hout'' y) hids'
      | panic e m =>
        have hset := evalValueL_args_def (fun msg h => by rw [hres] at h; cases h)
        rw [R.eval hA hrx' hfx (hids x List.mem_cons_self w hfx) he hset, hres]
        rfl

end GoFV.Proof.NilLateL
