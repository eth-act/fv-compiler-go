import GoFV.Proof.Pass.LateLowerVal
import GoFV.Proof.Low.TabsAgreeL

variable [GoFV.SSA.Sem.Addrs]

/-!
# `late lower` refines its input (issue #385)

When the validator `lateB` (`GoFV.Opt.LateLowerCheck`) accepts `late lower`'s result `g` for its
input `f`, `g` runs as `f` under `runL` (`lateLower_refinesL`): a lock-step simulation
(`runLoopL_sim`) whose frames agree on the values of `f` (`FRel`), the registers of `f`'s
producers holding their extension (`ExtAt`). Each block lists `f`'s values and the new constants;
its `runL` order is `f`'s with the new constants interleaved, each before its readers
(`blkOK`), so evaluating it (`evalAll_sim`) evaluates the constants (`MOVDconst`, never failing)
and `f`'s values alike: an unchanged value reads the same registers, a rewritten one
(`step_val`) evaluates to what its source does (`LateLowerVal`: the dropped extension of a
producer's register, the register op of an immediate op on the materialized constant,
`SLLconst [1]` as `ADD`, `ZERO` as `MOVDconst [0]`, `MOVDnop` as `MOVDreg`). The `Phi`s and the
terminators read values of `f` only. The tables of `g` agree with `f`'s for `f`
(`tabsAgreeL`, `Low.runL_tabsAgreeL`).
-/

namespace GoFV.Proof.LateLowerL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.LateLowerCheck GoFV.Proof

attribute [local irreducible] kahn schedValid greedy

/-! ## The validator's facts -/

/-- What `lateB` decides beyond `tabsAgreeL`, in the tables of the output. -/
structure Hyp (T : Tables) (f g : Func) : Prop where
  flow : f.lowered = true
  glow : g.lowered = true
  entry : g.entry = f.entry
  own : g.ownAux = f.ownAux
  val : ∀ i, valOK (shapesL T f) (shapesL T g) f g i = true
  blk : ∀ b, blkOK f g b = true
  sx : sxOK f g = true

theorem value?_none {f : Func} {i : ID} (h : f.valueTab.size ≤ i) : f.value? i = none := by
  simp [Func.value?, Array.getElem?_eq_none h]

theorem block?_none {f : Func} {i : ID} (h : f.blockTab.size ≤ i) : f.block? i = none := by
  simp [Func.block?, Array.getElem?_eq_none h]

theorem hyp_of {tabs T : Tables} {f g : Func} (h : lateB tabs T f g = true) :
    LowerCheck.tabsAgreeL tabs T f = true ∧ Hyp T f g := by
  unfold lateB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hta, hfl⟩, hgl⟩, hen⟩, hown⟩, hbs⟩, hval⟩, hblk⟩, hsx⟩ := h
  refine ⟨hta, hfl, hgl, hen, hown, ?_, ?_, hsx⟩
  · intro i
    by_cases hi : i < max f.valueTab.size g.valueTab.size
    · exact hval i hi
    · unfold valOK
      have hm := Nat.le_of_not_lt hi
      rw [value?_none (f := f) (i := i) (Nat.le_trans (Nat.le_max_left _ _) hm),
        value?_none (f := g) (i := i) (Nat.le_trans (Nat.le_max_right _ _) hm)]
  · intro b
    by_cases hb : b < f.blockTab.size
    · exact hblk b hb
    · unfold blkOK
      have hm := Nat.le_of_not_lt hb
      rw [block?_none (f := f) (i := b) hm, block?_none (f := g) (i := b) (hbs ▸ hm)]

section
variable {T : Tables} {f g : Func}

/-- What `valOK` says of a value of `f`. -/
theorem valOK_some (H : Hyp T f g) {x : ID} {u : Value} (hu : f.value? x = some u) :
    ∃ w, g.value? x = some w ∧ u.id = x ∧ w.id = u.id ∧ w.type = u.type ∧
      ((w.op = u.op ∧ w.aux = u.aux ∧ w.auxInt = u.auxInt ∧ w.args = u.args ∧
          ∀ a ∈ u.args, inF f a = true) ∨
        (u.op ≠ .Phi ∧ rwOK (shapesL T f) (shapesL T g) f g u w = true)) := by
  have h := H.val x
  unfold valOK at h
  rw [hu] at h
  cases hw : g.value? x with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      List.all_eq_true, Array.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨w, rfl, h1, h2, h3, ?_⟩
    rcases h4 with ⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩ | ⟨h5, h6⟩
    · exact .inl ⟨h5, h6, h7, h8, fun a ha => by
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
        exact h9 i hi⟩
    · exact .inr ⟨h5, h6⟩

/-- What `valOK` says of a value of `g` that `f` does not have: a constant without arguments. -/
theorem valOK_fresh (H : Hyp T f g) {x : ID} {w : Value} (hf : f.value? x = none)
    (hw : g.value? x = some w) : w.op = .ARM64MOVDconst ∧ w.args = #[] ∧ w.id = x := by
  have h := H.val x
  unfold valOK at h
  rw [hf, hw] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem inF_of {x : ID} {u : Value} (h : f.value? x = some u) : inF f x = true := by
  simp [inF, h]

theorem inF_some {x : ID} (h : inF f x = true) : ∃ u, f.value? x = some u := by
  simp only [inF, Option.isSome_iff_exists] at h; exact h

theorem inF_none {x : ID} (h : inF f x = false) : f.value? x = none := by
  simpa [inF] using h

theorem lt_of_value? {x : ID} {u : Value} (h : f.value? x = some u) : x < f.valueTab.size := by
  simp only [Func.value?, Option.join_eq_some_iff] at h
  exact (Array.getElem?_eq_some_iff.1 h).1

theorem shapesL_get {x : ID} {u : Value} (h : f.value? x = some u) :
    (shapesL T f)[x]? = some ((typeShapesL T)[u.type]?.getD .other) := by
  simp only [Func.value?, Option.join_eq_some_iff] at h
  simp [shapesL, h, valueTy]

/-! ## The contexts -/

theorem makeL_tys (h : f.lowered = true) : (Ctx.makeL T f).tys = shapesL T f := by
  simp [Ctx.makeL, h, shapesL]

/-- `g`'s context is `f`'s with `g`, its shapes and its orders (the parameters, results, frame
and defers come from the tables and `OwnAux`). -/
theorem ctxT_eq (H : Hyp T f g) :
    Ctx.makeL T g =
      { (Ctx.makeL T f) with
        f := g, tys := (Ctx.makeL T g).tys, sched := (Ctx.makeL T g).sched } := by
  unfold Ctx.makeL Ctx.make abiParams
  simp only [H.flow, H.glow, ite_true, H.own]

theorem tys_eq (H : Hyp T f g) {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hw : g.value? x = some w) (ht : w.type = u.type) :
    (Ctx.makeL T g).tys[x]? = (Ctx.makeL T f).tys[x]? := by
  rw [makeL_tys H.flow, makeL_tys H.glow, shapesL_get hu, shapesL_get hw, ht]

/-! ## `evalOpL` reads the function only for `MOVDreg`/`MOVDnop` -/

private theorem arm64Op_noF {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (F : Func) (hm : v.op ≠ .ARM64MOVDreg)
    (hn : v.op ≠ .ARM64MOVDnop) :
    arm64Op faulting env { ctx with f := F } fr v argv ty = arm64Op faulting env ctx fr v argv ty := by
  unfold arm64Op
  rw [show nilFaults faulting { ctx with f := F } v argv = nilFaults faulting ctx v argv from rfl]
  cases nilFaults faulting ctx v argv with
  | some m => rfl
  | none =>
    dsimp only
    split
    all_goals first | rfl | (exfalso; simp_all; done)

private theorem evalOpL_noF {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (F : Func) (hm : v.op ≠ .ARM64MOVDreg)
    (hn : v.op ≠ .ARM64MOVDnop) :
    evalOpL faulting env { ctx with f := F } fr v argv ty = evalOpL faulting env ctx fr v argv ty := by
  rw [evalOpL_eq, evalOpL_eq]
  split
  · exact evalOp_congr rfl rfl rfl rfl rfl rfl rfl
  · split
    · exact arm64Op_noF F hm hn
    · rfl

theorem params_eq (H : Hyp T f g) : (Ctx.makeL T g).params = (Ctx.makeL T f).params := by
  rw [params_makeL, params_makeL]; unfold Ctx.make abiParams; rw [H.own]

theorem act_eq : (Ctx.makeL T g).act = (Ctx.makeL T f).act := by
  rw [act_makeL, act_makeL]; rfl

/-- `evalOpL` of an unchanged value of `f` in `g`'s context. -/
theorem evalOpL_same (H : Hyp T f g) {fl : Bool} {env : Env} {fr : Frame} {u w : Value}
    {argv : List Val} {ty : Ty}
    (hop : w.op = u.op) (haux : w.aux = u.aux) (hai : w.auxInt = u.auxInt) (hid : w.id = u.id)
    (hargs : w.args = u.args)
    (hsx : (u.op = .ARM64MOVDreg ∨ u.op = .ARM64MOVDnop) → sxIn g w = sxIn f u) :
    evalOpL fl env (Ctx.makeL T g) fr w argv ty = evalOpL fl env (Ctx.makeL T f) fr u argv ty := by
  have ht : (Ctx.makeL T g).tabs = (Ctx.makeL T f).tabs := by rw [tabs_makeL, tabs_makeL]
  by_cases hm : u.op = .ARM64MOVDreg ∨ u.op = .ARM64MOVDnop
  · refine evalOpL_congr hop haux hai hid ht (params_eq H) act_eq ?_
    have := hsx hm
    unfold sxIn at this
    simpa [sxOf, makeL_f] using this
  · have h1 : w.op ≠ .ARM64MOVDreg := fun h => hm (.inl (hop ▸ h))
    have h2 : w.op ≠ .ARM64MOVDnop := fun h => hm (.inr (hop ▸ h))
    rw [← evalOpL_noF (ctx := Ctx.makeL T g) f h1 h2]
    exact evalOpL_congr hop haux hai hid ht (params_eq H) act_eq (by simp [sxOf, hargs, makeL_f])

/-- Two values with the same arguments and ID whose `evalOpL`s agree evaluate alike in frames
that agree on the arguments. -/
theorem evalValueL_of_op {md : LMode} {env : Env} {ctxS ctxT : Ctx} {frS frT : Frame}
    {u w : Value} (hfr : frT = { frS with regs := frT.regs })
    (hreg : ∀ a ∈ u.args, frT.regs[a]? = frS.regs[a]?) (hid : w.id = u.id) (hargs : w.args = u.args)
    (hty : ctxT.tys[u.id]? = ctxS.tys[u.id]?)
    (hop : ∀ argv ty, evalOpL md.faulting env ctxT frS w argv ty =
      evalOpL md.faulting env ctxS frS u argv ty) :
    evalValueL md env ctxT frT w = evalValueL md env ctxS frS u := by
  rw [← evalValueL_congr (fr := frS) hfr (fun a ha => (hreg a (hargs ▸ ha)).symm)]
  unfold evalValueL
  rw [hargs, hid, hty]
  simp only [hop]

/-- An unchanged value of `f` evaluates in `g`'s context and frame as in `f`'s. -/
theorem evalValueL_same (H : Hyp T f g) {md : LMode} {env : Env} {frS frT : Frame} {u w : Value}
    (hfr : frT = { frS with regs := frT.regs }) (hreg : ∀ a ∈ u.args, frT.regs[a]? = frS.regs[a]?)
    (hop : w.op = u.op) (haux : w.aux = u.aux) (hai : w.auxInt = u.auxInt) (hid : w.id = u.id)
    (hargs : w.args = u.args)
    (hty : (Ctx.makeL T g).tys[u.id]? = (Ctx.makeL T f).tys[u.id]?)
    (hsx : (u.op = .ARM64MOVDreg ∨ u.op = .ARM64MOVDnop) → sxIn g w = sxIn f u) :
    evalValueL md env (Ctx.makeL T g) frT w = evalValueL md env (Ctx.makeL T f) frS u :=
  evalValueL_of_op hfr hreg hid hargs hty fun _ _ => evalOpL_same H hop haux hai hid hargs hsx

/-! ## The frame relation -/

/-- `runL`'s mode on lowered functions. -/
abbrev mdL : LMode := ⟨true, false⟩

/-- The value a new constant `c` of `g` (`wc`) evaluates to. -/
def cval (T : Tables) (g : Func) (c : ID) (wc : Value) : Val :=
  mdL.retype ((Ctx.makeL T g).tys[c]?.getD .other)
    (Arm64.res ((Ctx.makeL T g).tys[c]?.getD .other) (Arm64.imm wc.auxInt))

/-- The frames of `f` (source) and `g` (target): equal but for the registers, which agree on
the values of `f`; the producers' registers hold their extension. -/
structure FRel (T : Tables) (f g : Func) (frS frT : Frame) : Prop where
  fr : frT = { frS with regs := frT.regs }
  agree : ∀ i, inF f i = true → frT.regs[i]? = frS.regs[i]?
  szS : frS.regs.size = f.valueTab.size
  szT : frT.regs.size = g.valueTab.size
  prod : ∀ x u, f.value? x = some u → ∀ s k, prodSig u.op = some (s, k) → ∀ y,
    frS.regs[x]? = some (some y) → ExtAt s k ((Ctx.makeL T f).tys[x]?.getD .other) y

theorem sx_of (H : Hyp T f g) {x : ID} {w : Value} (hw : g.value? x = some w)
    (hm : w.op = .ARM64MOVDreg ∨ w.op = .ARM64MOVDnop) : sxIn g w = sxIn f w := by
  have h := H.sx
  unfold sxOK at h
  rw [Array.all_eq_true] at h
  simp only [Func.value?, Option.join_eq_some_iff] at hw
  obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.1 hw
  have := h x hlt
  rw [hx] at this
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
  rcases this with h1 | h1
  · exfalso; rcases hm with h2 | h2 <;> simp_all
  · exact h1

theorem sxIn_args {F : Func} {v v' : Value} (h : v'.args = v.args) : sxIn F v' = sxIn F v := by
  unfold sxIn; rw [h]

/-- A value that panics read its arguments and its `evalOpL` panicked. -/
theorem evalValueL_panic_args {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {e : Panic} {m : Mem} (h : evalValueL md env ctx fr v = .panic e m) :
    ∃ argv, evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) = .panic e m := by
  cases hm : argsL fr v with
  | ok argv =>
    rw [evalValueL_of_args hm] at h
    cases he : evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [he] at h; cases h
    | panic e' m' => rw [he] at h; cases h; exact ⟨argv, he⟩
    | stuck msg => rw [he] at h; cases h
  | panic e m => exact absurd hm mapM_ofOption_ne_panic
  | stuck msg =>
    unfold evalValueL at h; simp only [argsL] at hm; rw [hm] at h; cases h

/-- A pure arm64 value does not panic. -/
theorem pure_not_panic {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {e : Panic}
    {m : Mem} (hg : v.op.generic = false) (ha : GoFV.Opt.LowerTerm.actOp v.op = false)
    (hr : isRoot v.op = false) : evalValueL md env ctx fr v ≠ .panic e m := by
  intro h
  obtain ⟨argv, h⟩ := evalValueL_panic_args h
  rw [evalOpL_pure hg ha hr] at h
  cases h

theorem argsL_agree {frS frT : Frame} {v : Value} (hfr : frT = { frS with regs := frT.regs })
    (h : ∀ a ∈ v.args, frT.regs[a]? = frS.regs[a]?) : argsL frT v = argsL frS v := by
  unfold argsL
  exact mapM_congr' _ fun a ha => by rw [h a (Array.mem_toList_iff.1 ha)]

/-- **A value of `f` and its counterpart in `g`** evaluate alike in related frames, when `g`'s
reads its new constants. -/
theorem step_val (H : Hyp T f g) {env : Env} {frS frT : Frame} (R : FRel T f g frS frT)
    {x : ID} {u w : Value} (hu : f.value? x = some u) (hw : g.value? x = some w)
    (hc : ∀ c ∈ w.args, inF f c = false →
      ∃ wc, g.value? c = some wc ∧ frT.regs[c]? = some (some (cval T g c wc))) :
    (∀ y, evalValueL mdL env (Ctx.makeL T f) frS u = .ok y →
      evalValueL mdL env (Ctx.makeL T g) frT w = .ok y) ∧
    (∀ e m, evalValueL mdL env (Ctx.makeL T f) frS u = .panic e m →
      evalValueL mdL env (Ctx.makeL T g) frT w = .panic e m) := by
  obtain ⟨w', hw', hid, hwid, htype, hcase⟩ := valOK_some H hu
  rw [hw] at hw'; cases hw'
  have hty : (Ctx.makeL T g).tys[u.id]? = (Ctx.makeL T f).tys[u.id]? := by
    rw [hid]; exact tys_eq H hu hw htype
  have hregs : ∀ a, inF f a = true → frT.regs[a]? = frS.regs[a]? := R.agree
  -- both sides equal
  have same : evalValueL mdL env (Ctx.makeL T g) frT w =
      evalValueL mdL env (Ctx.makeL T f) frS u →
      (∀ y, evalValueL mdL env (Ctx.makeL T f) frS u = .ok y →
        evalValueL mdL env (Ctx.makeL T g) frT w = .ok y) ∧
      (∀ e m, evalValueL mdL env (Ctx.makeL T f) frS u = .panic e m →
        evalValueL mdL env (Ctx.makeL T g) frT w = .panic e m) :=
    fun h => ⟨fun y hy => h.trans hy, fun e m hp => h.trans hp⟩
  rcases hcase with ⟨hop, haux, hai, hargs, hin⟩ | ⟨hnp, hrw⟩
  · refine same (evalValueL_same H R.fr (fun a ha => hregs a (hin a ha)) hop haux hai hwid hargs
      hty fun hm => ?_)
    rw [sx_of H hw (hop ▸ hm), sxIn_args hargs]
  unfold rwOK at hrw
  simp only [Bool.or_eq_true] at hrw
  rcases hrw with (((h91 | h98) | h103) | hext) | himm
  · -- `MOVDreg` → `MOVDnop`
    unfold rw91 at h91
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h91
    obtain ⟨⟨⟨hu1, hw1⟩, hargs⟩, hin⟩ := h91
    refine same (evalValueL_of_op R.fr (fun a ha => ?_) hwid hargs hty fun argv ty => ?_)
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
      exact hregs _ (hin i hi)
    · have hmw : w.op = .ARM64MOVDreg ∨ w.op = .ARM64MOVDnop := .inr hw1
      have hmu : u.op = .ARM64MOVDreg ∨ u.op = .ARM64MOVDnop := .inl hu1
      rw [evalOpL_act (movd_generic hmw) (movd_act hmw), evalOpL_act (movd_generic hmu)
        (movd_act hmu), arm64Op_movd hmw, arm64Op_movd hmu]
      have hs : sxIn g w = sxIn f u := by rw [sx_of H hw hmw, sxIn_args hargs]
      unfold sxIn at hs
      rw [makeL_f, makeL_f, hs]
  · -- `MOVDconst [0]` → `ZERO`
    unfold rw98 at h98
    simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h98
    obtain ⟨⟨⟨⟨hu1, hu0⟩, hw1⟩, hua⟩, hwa⟩ := h98
    refine same (evalValueL_of_op R.fr (fun a ha => by rw [hua] at ha; simp at ha) hwid
      (by rw [hua, hwa]) hty fun argv ty => ?_)
    rw [evalOpL_pure (by rw [hw1]; rfl) (by rw [hw1]; rfl) (by rw [hw1]; decide),
      evalOpL_pure (by rw [hu1]; rfl) (by rw [hu1]; rfl) (by rw [hu1]; decide), hw1, hu1, hu0,
      zero_eval]
  · -- `SLLconst [1] x` → `ADD x x`
    unfold rw103 at h103
    simp only [Bool.and_eq_true, beq_iff_eq] at h103
    obtain ⟨⟨⟨hu1, hu0⟩, hw1⟩, hx⟩ := h103
    split at hx
    · rename_i x0 hl
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨hwa, hin⟩ := hx
      have hua : u.args = #[x0] := by
        rcases hu' : u.args with ⟨l⟩; rw [hu'] at hl; simp at hl; rw [hl]
      have hgu : u.op.generic = false := by rw [hu1]; rfl
      have hau : GoFV.Opt.LowerTerm.actOp u.op = false := by rw [hu1]; rfl
      have hru : isRoot u.op = false := by rw [hu1]; decide
      refine ⟨fun y hy => ?_, fun e m hp => absurd hp (pure_not_panic hgu hau hru)⟩
      obtain ⟨argv, hm, r, hr, rfl⟩ := evalValueL_ok_args hy
      obtain ⟨a, ha, rfl⟩ := argsL_one_inv hua hm
      have hTa : frT.regs[x0]? = some (some a) := by rw [hregs _ hin, ha]
      rw [evalValueL_of_args (argsL_two hwa hTa hTa), hwid, hty,
        evalOpL_pure (by rw [hw1]; rfl) (by rw [hw1]; rfl) (by rw [hw1]; decide), hw1,
        sll1_eval (ax := u.aux)]
      rw [evalOpL_pure hgu hau hru, hu1, hu0] at hr
      cases hr; rfl
    · cases hx
  · -- a dropped extension
    unfold rwExt at hext
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hext
    obtain ⟨hmw, hx⟩ := hext
    split at hx
    · rename_i x0 hl
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨hwa, hx⟩ := hx
      have hua : u.args = #[x0] := by
        rcases hu' : u.args with ⟨l⟩; rw [hu'] at hl; simp at hl; rw [hl]
      split at hx
      · rename_i sE kE sP kP he hp
        obtain ⟨px, hpx, hpp⟩ : ∃ px, f.value? x0 = some px ∧ prodSig px.op = some (sP, kP) := by
          cases hfx : f.value? x0 with
          | none => rw [hfx] at hp; cases hp
          | some px => rw [hfx] at hp; exact ⟨px, rfl, hp⟩
        obtain ⟨hge, hae, hre, hev, hk2, hk64⟩ := ext_cases he
        obtain ⟨hk0, hkP⟩ := prod_bits hpp
        obtain ⟨hse, hs0, hs1⟩ := prod_signExtends hpp
        refine ⟨fun y hy => ?_, fun e m hp => absurd hp (pure_not_panic hge hae hre)⟩
        obtain ⟨argv, hm, r, hr, rfl⟩ := evalValueL_ok_args hy
        obtain ⟨a, ha, rfl⟩ := argsL_one_inv hua hm
        have hTa : frT.regs[x0]? = some (some a) := by rw [hregs _ (inF_of hpx), ha]
        have hE := R.prod x0 px hpx sP kP hpp a ha
        rw [evalOpL_pure hge hae hre, hev] at hr
        cases hr
        have hmw' : w.op = .ARM64MOVDreg ∨ w.op = .ARM64MOVDnop := hmw
        rw [evalValueL_of_args (argsL_one hwa hTa), hwid, hty,
          evalOpL_act (movd_generic hmw') (movd_act hmw'), arm64Op_movd hmw']
        have hsx : ((w.args[0]?.bind (Ctx.makeL T g).f.value?).map
            (Arm64.signExtendsIn (Ctx.makeL T g).f.value?)).getD false = sP := by
          have hs := sx_of H hw hmw'
          unfold sxIn at hs
          rw [makeL_f, hs, hwa]
          simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.bind_some, hpx,
            Option.map_some, Option.getD_some]
          unfold Arm64.signExtendsIn
          rw [hse]
          split
          · rename_i h; exact absurd h hs0
          · rename_i h; exact absurd h hs1
          · exact Bool.or_false _
        rw [hsx]
        rw [makeL_tys H.flow] at hE
        have hd := drop_eq (ty := (Ctx.makeL T f).tys[u.id]?.getD .other) hk0 hkP hk2 hk64 hE hx
        rw [hd]; rfl
      · cases hx
    · cases hx
  · -- an immediate op on a new constant
    unfold rwImm at himm
    simp only [Bool.and_eq_true, Option.any_eq_true, beq_iff_eq] at himm
    obtain ⟨⟨o', ho', hwo⟩, hx⟩ := himm
    split at hx
    · rename_i x0 x1 c hl hl'
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      obtain ⟨⟨hx1, hin⟩, hfr⟩ := hx
      rw [hx1] at hl'
      have hua : u.args = #[x0] := by
        rcases hu' : u.args with ⟨l⟩; rw [hu'] at hl; simp at hl; rw [hl]
      have hwa : w.args = #[x0, c] := by
        rcases hw' : w.args with ⟨l⟩; rw [hw'] at hl'; simp at hl'; rw [hl']
      obtain ⟨hgu, hau, hru, hgw, haw, hrw, hev⟩ := imm_eval ho'
      rw [hwo] at hgw haw hrw
      refine ⟨fun y hy => ?_, fun e m hp => absurd hp (pure_not_panic hgu hau hru)⟩
      obtain ⟨argv, hm, r, hr, rfl⟩ := evalValueL_ok_args hy
      obtain ⟨a, ha, rfl⟩ := argsL_one_inv hua hm
      have hTa : frT.regs[x0]? = some (some a) := by rw [hregs _ hin, ha]
      unfold freshK at hfr
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfr
      obtain ⟨⟨hcf, hw64⟩, hcw⟩ := hfr
      obtain ⟨wc, hwc, hTc⟩ := hc c (by rw [hwa]; simp) hcf
      rw [hwc] at hcw
      simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at hcw
      obtain ⟨⟨-, -⟩, hk⟩ := hcw
      have hcv : cval T g c wc = .int .w64 (Arm64.imm u.auxInt) := by
        unfold cval
        have : (Ctx.makeL T g).tys[c]? = some (.int .w64) := by
          rw [makeL_tys H.glow]
          unfold isW64 at hw64
          split at hw64
          · rename_i h; exact h
          · cases hw64
        rw [this, hk]
        simp [LMode.retype, Val.retypeL, Val.widen, Val.retype, Arm64.res]
      rw [hcv] at hTc
      rw [evalValueL_of_args (argsL_two hwa hTa hTc), hwid, hty, evalOpL_pure hgw haw hrw,
        ← hwo, hev]
      rw [evalOpL_pure hgu hau hru] at hr
      cases hr; rfl
    · cases hx

/-! ## A block's values -/

variable {frS frT : Frame}

/-- The new constants of `seen` hold their value in the target frame. -/
def Seen (T : Tables) (f g : Func) (seen : List ID) (frT : Frame) : Prop :=
  ∀ c ∈ seen, inF f c = false →
    ∃ wc, g.value? c = some wc ∧ frT.regs[c]? = some (some (cval T g c wc))

theorem FRel.set (R : FRel T f g frS frT) {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hw : g.value? x = some w) {y : Val}
    (hp : ∀ s k, prodSig u.op = some (s, k) → ExtAt s k ((Ctx.makeL T f).tys[x]?.getD .other) y) :
    FRel T f g (frS.set x y) (frT.set x y) := by
  obtain ⟨hfr, hag, hs, ht, hpr⟩ := R
  have hxs : x < frS.regs.size := by rw [hs]; exact lt_of_value? hu
  have hxt : x < frT.regs.size := by rw [ht]; exact lt_of_value? hw
  refine ⟨?_, fun i hi => ?_, by simp [Frame.set, hs], by simp [Frame.set, ht], ?_⟩
  · rw [hfr]; rfl
  · by_cases hix : x = i
    · subst hix; rw [Frame.set_regs_self hxs, Frame.set_regs_self hxt]
    · rw [Frame.set_regs_ne hix, Frame.set_regs_ne hix, hag i hi]
  · intro x' u' hu' s k hk y' hy'
    by_cases hix : x = x'
    · subst hix
      rw [hu] at hu'; cases hu'
      rw [Frame.set_regs_self hxs] at hy'; cases hy'
      exact hp s k hk
    · rw [Frame.set_regs_ne hix] at hy'
      exact hpr x' u' hu' s k hk y' hy'

theorem FRel.setT (R : FRel T f g frS frT) {c : ID} (hc : inF f c = false) (y : Val) :
    FRel T f g frS (frT.set c y) := by
  obtain ⟨hfr, hag, hs, ht, hpr⟩ := R
  refine ⟨?_, fun i hi => ?_, hs, by simp [Frame.set, ht], hpr⟩
  · rw [hfr]; rfl
  · have : c ≠ i := fun h => by subst h; rw [hc] at hi; cases hi
    rw [Frame.set_regs_ne this, hag i hi]

theorem fresh_eval {env : Env} {fr : Frame} {x : ID} {w : Value} (hop : w.op = .ARM64MOVDconst)
    (ha : w.args = #[]) (hid : w.id = x) :
    evalValueL mdL env (Ctx.makeL T g) fr w = .ok (cval T g x w) := by
  rw [evalValueL_of_args (argsL_nil ha), evalOpL_pure (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide), hop, hid]
  rfl

theorem prodSig_phi : prodSig .Phi = none := by decide

/-- **Evaluating a block's order** in `g` (`oT`) does what evaluating `f`'s (`oT` without the new
constants) does. -/
theorem evalAll_sim (H : Hyp T f g) {env : Env} :
    ∀ (oT seen : List ID) (frS frT : Frame), FRel T f g frS frT → Seen T f g seen frT →
      freshBefore f g seen oT = true → (∀ x ∈ oT, (g.value? x).isSome = true) →
      (∀ frS', evalAllL mdL env (Ctx.makeL T f) frS (oT.filter (inF f)) = .ok frS' →
        ∃ frT', evalAllL mdL env (Ctx.makeL T g) frT oT = .ok frT' ∧ FRel T f g frS' frT') ∧
      (∀ e m, evalAllL mdL env (Ctx.makeL T f) frS (oT.filter (inF f)) = .panic e m →
        evalAllL mdL env (Ctx.makeL T g) frT oT = .panic e m)
  | [], _, frS, frT, R, _, _, _ => by
    refine ⟨fun frS' h => ?_, fun e m h => ?_⟩
    · cases h; exact ⟨frT, rfl, R⟩
    · cases h
  | x :: xs, seen, frS, frT, R, hS, hb, hall => by
    unfold freshBefore at hb
    rw [Bool.and_eq_true] at hb
    obtain ⟨hx, hb⟩ := hb
    have hall' : ∀ z ∈ xs, (g.value? z).isSome = true := fun z hz => hall z (List.mem_cons_of_mem _ hz)
    obtain ⟨w, hw⟩ : ∃ w, g.value? x = some w :=
      Option.isSome_iff_exists.1 (hall x List.mem_cons_self)
    cases hxf : inF f x
    · -- a new constant: only the target evaluates it
      rw [List.filter_cons_of_neg (by simp [hxf])]
      obtain ⟨hop, hargs, hid⟩ := valOK_fresh H (inF_none hxf) hw
      have hT : evalAllL mdL env (Ctx.makeL T g) frT (x :: xs) =
          evalAllL mdL env (Ctx.makeL T g) (frT.set x (cval T g x w)) xs := by
        rw [evalAllL_cons, stepVL_of (by rw [makeL_f]; exact hw), fresh_eval hop hargs hid]
      rw [hT]
      have hxt : x < frT.regs.size := by rw [R.szT]; exact lt_of_value? hw
      refine evalAll_sim H xs (x :: seen) frS _ (R.setT hxf _) (fun c hc hcf => ?_) hb hall'
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨w, hw, Frame.set_regs_self hxt⟩
      · obtain ⟨wc, hwc, hr⟩ := hS c hc hcf
        by_cases hcx : x = c
        · subst hcx; rw [hw] at hwc; cases hwc; exact ⟨w, hw, Frame.set_regs_self hxt⟩
        · exact ⟨wc, hwc, by rw [Frame.set_regs_ne hcx]; exact hr⟩
    · -- a value of `f`: both evaluate it alike
      rw [List.filter_cons_of_pos hxf]
      obtain ⟨u, hu⟩ := inF_some hxf
      have hc : ∀ c ∈ w.args, inF f c = false →
          ∃ wc, g.value? c = some wc ∧ frT.regs[c]? = some (some (cval T g c wc)) := by
        intro c hc hcf
        rw [hw] at hx
        simp only [Option.map_some, Option.getD_some, Array.all_eq_true, Bool.or_eq_true] at hx
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hc
        rcases hx i hi with h | h
        · rw [hcf] at h; cases h
        · exact hS _ (List.contains_iff_mem.1 h) hcf
      obtain ⟨hok, hpan⟩ := step_val H R hu hw hc
      rw [evalAllL_cons, evalAllL_cons, stepVL_of (by rw [makeL_f]; exact hu),
        stepVL_of (by rw [makeL_f]; exact hw)]
      cases hev : evalValueL mdL env (Ctx.makeL T f) frS u with
      | ok y =>
        rw [hok y hev]
        dsimp only
        have hid : u.id = x := (valOK_some H hu).choose_spec.2.1
        have R' := R.set hu hw (y := y) fun s k hk => by
          have := prod_evalValueL rfl rfl hk hev
          rw [hid] at this; exact this
        refine evalAll_sim H xs (x :: seen) _ _ R' (fun c hc hcf => ?_) hb hall'
        rcases List.mem_cons.1 hc with rfl | hc
        · rw [hxf] at hcf; cases hcf
        · obtain ⟨wc, hwc, hr⟩ := hS c hc hcf
          have hcx : x ≠ c := fun h => by subst h; rw [hxf] at hcf; cases hcf
          exact ⟨wc, hwc, by rw [Frame.set_regs_ne hcx]; exact hr⟩
      | panic e m =>
        rw [hpan e m hev]
        exact ⟨fun _ h => (by cases h), fun _ _ h => by cases h; rfl⟩
      | stuck msg => exact ⟨fun _ h => (by cases h), fun _ _ h => by cases h⟩

/-! ## `Phi`s -/

theorem rw_not_phi {u w : Value} (h : rwOK (shapesL T f) (shapesL T g) f g u w = true) :
    w.op ≠ .Phi := by
  unfold rwOK at h
  simp only [Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · unfold rw91 at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; rw [h.1.1.2]; decide
  · unfold rw98 at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; rw [h.1.1.2]; decide
  · unfold rw103 at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; rw [h.1.2]; decide
  · unfold rwExt at h; simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases h.1 with h | h <;> rw [h] <;> decide
  · unfold rwImm at h
    simp only [Bool.and_eq_true, Option.any_eq_true, beq_iff_eq] at h
    obtain ⟨⟨o', ho', hwo⟩, -⟩ := h
    rw [← hwo]
    have hm := find_mem ho'
    simp only [immOps, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
      ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide

private theorem filterMapM_filterF {α : Type} {step : ID → Res (Option α)} {p : ID → Bool} :
    ∀ {l : List ID}, (∀ z ∈ l, p z = false → step z = .ok none) →
      l.filterMapM step = (l.filter p).filterMapM step
  | [], _ => rfl
  | z :: l, h => by
    have ih := filterMapM_filterF (step := step) (p := p) (l := l)
      (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hp : p z with
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp]), List.filterMapM_cons, h z List.mem_cons_self hp]
      exact ih
    | true =>
      rw [List.filter_cons_of_pos hp, List.filterMapM_cons, List.filterMapM_cons, ih]

private theorem filterMapM_congrF {α : Type} {s1 s2 : ID → Res (Option α)} :
    ∀ {l : List ID}, (∀ z ∈ l, s1 z = s2 z) → l.filterMapM s1 = l.filterMapM s2
  | [], _ => rfl
  | z :: l, h => by
    rw [List.filterMapM_cons, List.filterMapM_cons, h z List.mem_cons_self,
      filterMapM_congrF (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- `g`'s block collects the `Phi`s `f`'s does. -/
theorem phis_eq (H : Hyp T f g) (R : FRel T f g frS frT) {fb gb : Block} (i : Nat)
    (hvals : gb.values.toList.filter (inF f) = fb.values.toList)
    (hall : ∀ x ∈ gb.values.toList, (g.value? x).isSome = true) :
    gb.values.toList.filterMapM (phiStepL mdL (Ctx.makeL T g) frT i) =
      fb.values.toList.filterMapM (phiStepL mdL (Ctx.makeL T f) frS i) := by
  rw [filterMapM_filterF (p := inF f) fun z hz hzf => ?_, hvals]
  · refine filterMapM_congrF fun z hz => ?_
    have hzf : inF f z = true := by
      rw [← hvals] at hz; exact (List.mem_filter.1 hz).2
    obtain ⟨u, hu⟩ := inF_some hzf
    obtain ⟨w, hw, hid, hwid, htype, hcase⟩ := valOK_some H hu
    unfold phiStepL
    rw [makeL_f, makeL_f, hu, hw]
    dsimp only
    rcases hcase with ⟨hop, -, -, hargs, hin⟩ | ⟨hnp, hrw⟩
    · rw [hop, hargs]
      split
      · split
        · rename_i a ha
          have ha' : a ∈ u.args := Array.mem_of_getElem? ha
          rw [R.agree a (hin a ha'), tys_eq H hu hw htype]
        · rfl
      · rfl
    · have h1 : (u.op == .Phi) = false := by simpa using hnp
      have h2 : (w.op == .Phi) = false := by simpa using rw_not_phi hrw
      simp only [h1, h2, Bool.false_eq_true, ite_false]
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hall z hz)
    obtain ⟨hop, -, -⟩ := valOK_fresh H (inF_none hzf) hw
    unfold phiStepL
    rw [makeL_f, hw]
    simp [hop]

theorem FRel.setPhis (H : Hyp T f g) :
    ∀ (ps : List (ID × Val)) {frS frT : Frame}, FRel T f g frS frT →
      (∀ p ∈ ps, ∃ u, f.value? p.1 = some u ∧ u.op = .Phi) →
      FRel T f g { frS with regs := setPhis ps frS.regs } { frT with regs := setPhis ps frT.regs }
  | [], _, _, R, _ => by
    obtain ⟨hfr, hag, hs, ht, hpr⟩ := R
    exact ⟨by rw [hfr], hag, hs, ht, hpr⟩
  | (id, x) :: ps, _, _, R, hps => by
    obtain ⟨u, hu, hphi⟩ := hps (id, x) List.mem_cons_self
    obtain ⟨w, hw, -⟩ := valOK_some H hu
    have R1 := R.set hu hw (y := x) fun s k hk => by rw [hphi, prodSig_phi] at hk; cases hk
    exact FRel.setPhis H ps R1 fun p hp => hps p (List.mem_cons_of_mem _ hp)

/-! ## Blocks -/

theorem sched_get {F : Func} (b : ID) :
    ((Ctx.makeL T F).sched[b]?).join = (F.block? b).bind (schedule F) := by
  rw [sched_makeL]
  cases hb : F.block? b with
  | none =>
    simp only [Ctx.make, Array.getElem?_map, Option.bind_none]
    unfold Func.block? at hb
    cases h : F.blockTab[b]? with
    | none => rfl
    | some o => rw [h] at hb; simp at hb; subst hb; rfl
  | some fb => rw [sched_of_block hb]; rfl

/-- `blkOK` for the order of block `b` (by ID). -/
theorem sched_rel (H : Hyp T f g) (b : ID) :
    (((Ctx.makeL T f).sched[b]?).join = none ∧ ((Ctx.makeL T g).sched[b]?).join = none) ∨
      ∃ oS oT, ((Ctx.makeL T f).sched[b]?).join = some oS ∧
        ((Ctx.makeL T g).sched[b]?).join = some oT ∧ oT.toList.filter (inF f) = oS.toList ∧
        freshBefore f g [] oT.toList = true ∧ ∀ x ∈ oT.toList, (g.value? x).isSome = true := by
  have h := H.blk b
  rw [sched_get, sched_get]
  unfold blkOK at h
  cases hfb : f.block? b with
  | none =>
    rw [hfb] at h
    cases hgb : g.block? b with
    | none => exact .inl ⟨rfl, rfl⟩
    | some gb => rw [hgb] at h; cases h
  | some fb =>
    rw [hfb] at h
    cases hgb : g.block? b with
    | none => rw [hgb] at h; cases h
    | some gb =>
      rw [hgb] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨-, hs⟩ := h
      cases hsf : schedule f fb with
      | none => rw [hsf] at hs; cases hs
      | some oS =>
        cases hsg : schedule g gb with
        | none => rw [hsf, hsg] at hs; cases hs
        | some oT =>
          rw [hsf, hsg] at hs
          simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at hs
          obtain ⟨⟨h1, h2⟩, h3⟩ := hs
          refine .inr ⟨oS, oT, by simp [hsf], by simp [hsg], h1, h3, fun x hx => ?_⟩
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
          simpa using h2 i (by simpa using hi)

/-- The facts `blkOK` gives of a block of `f`. -/
theorem blk_of (H : Hyp T f g) {b : ID} {fb : Block} (hfb : f.block? b = some fb) :
    ∃ gb, g.block? b = some gb ∧
      { gb with values := fb.values, pos := fb.pos, likely := fb.likely } = fb ∧
      gb.values.toList.filter (inF f) = fb.values.toList ∧
      (∀ x ∈ gb.values.toList, (g.value? x).isSome = true) ∧ ∀ c ∈ fb.controls, inF f c = true := by
  have h := H.blk b
  unfold blkOK at h
  rw [hfb] at h
  cases hgb : g.block? b with
  | none => rw [hgb] at h; cases h
  | some gb =>
    rw [hgb] at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h
    refine ⟨gb, rfl, h1, h2, fun x hx => ?_, fun c hc => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
      simpa using h3 i (by simpa using hi)
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hc
      exact h4 i hi

theorem stepTermL_rel {frS frT : Frame} {fb gb : Block}
    (hgb : { gb with values := fb.values, pos := fb.pos, likely := fb.likely } = fb)
    (hag : ∀ c ∈ fb.controls, frT.regs[c]? = frS.regs[c]?) :
    stepTermL frT gb = stepTermL frS fb := by
  have h1 : stepTermL frT gb = stepTermL frT fb := by rw [← hgb]; rfl
  have hc : ∀ k, Sem.control frT fb k = Sem.control frS fb k := by
    intro k
    unfold Sem.control
    cases hk : fb.controls[k]? with
    | none => rfl
    | some c => simp only [hag c (Array.mem_of_getElem? hk)]
  rw [h1]
  unfold stepTermL stepTerm
  simp only [hc]

/-- **One block entry**: `g`'s does what `f`'s does, in related frames. -/
theorem block_sim (H : Hyp T f g) {env : Env} (R : FRel T f g frS frT) (bid : ID) (i : Nat) :
    StepSim (fun S T' _ _ => FRel T f g S T') (blockStepL mdL env (Ctx.makeL T f) frS bid i)
      (blockStepL mdL env (Ctx.makeL T g) frT bid i) := by
  unfold blockStepL
  rw [makeL_f, makeL_f]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  obtain ⟨gb, hgb, hshape, hvals, hall, hctl⟩ := blk_of H hfb
  rw [hgb]
  dsimp only
  have hid : gb.id = fb.id := by rw [← hshape]
  rw [enterBlockL_eq, enterBlockL_eq, phis_eq H R i hvals hall, hid]
  cases hps : fb.values.toList.filterMapM (phiStepL mdL (Ctx.makeL T f) frS i) with
  | panic e m => exact absurd hps filterMapM_phiL_not_panic
  | stuck msg => exact True.intro
  | ok ps =>
  dsimp only [Res.bind]
  have hps' : ∀ p ∈ ps, ∃ u, f.value? p.1 = some u ∧ u.op = .Phi := by
    intro p hp
    obtain ⟨-, h2, -⟩ := filterMapM_phiL hps
    obtain ⟨-, v, -, -, hv, hphi, -⟩ := phiStepL_some (h2 p hp)
    rw [makeL_f] at hv
    exact ⟨v, hv, hphi⟩
  have R0 := FRel.setPhis H ps R hps'
  rcases sched_rel H fb.id with ⟨h1, h2⟩ | ⟨oS, oT, h1, h2, hfil, hfb', hallT⟩
  · rw [h1, h2]; exact True.intro
  rw [h1, h2]
  dsimp only [Res.ofOption, Res.bind]
  obtain ⟨hok, hpan⟩ := evalAll_sim H (env := env) oT.toList [] _ _ R0
    (fun c hc => absurd hc List.not_mem_nil) hfb' hallT
  rw [hfil] at hok hpan
  cases hev : evalAllL mdL env (Ctx.makeL T f) { frS with regs := setPhis ps frS.regs } oS.toList with
  | panic e m => rw [hpan e m hev]; exact rfl
  | stuck msg => exact True.intro
  | ok frS' =>
  obtain ⟨frT', hT, R'⟩ := hok frS' hev
  rw [hT]
  dsimp only
  rw [stepTermL_rel hshape fun c hc => R'.agree c (hctl c hc)]
  cases stepTermL frS' fb with
  | ok n =>
    cases n with
    | goto e => exact ⟨frT', rfl, R'⟩
    | ret rs m => exact ⟨rs, rfl, RefinesList.refl rs⟩
  | panic e m => rfl
  | stuck msg => exact True.intro

/-! ## The refinement -/

theorem entry_rel (H : Hyp T f g) (env : Env) (args : List Val) (mem : Mem) :
    FRel T f g (entryFrame env (Ctx.makeL T f) args mem) (entryFrame env (Ctx.makeL T g) args mem) := by
  have he : entryFrame env (Ctx.makeL T g) args mem =
      { entryFrame env (Ctx.makeL T f) args mem with
        regs := Array.replicate g.valueTab.size none } := by
    rw [ctxT_eq H]
    unfold entryFrame frameMem frameAllocs
    rfl
  rw [he]
  refine ⟨rfl, fun x hx => ?_, ?_, by simp, fun x u hu s k _ y hy => ?_⟩
  · obtain ⟨u, hu⟩ := inF_some hx
    obtain ⟨w, hw, -⟩ := valOK_some H hu
    have h1 := lt_of_value? hu
    have h2 := lt_of_value? hw
    simp [entryFrame, makeL_f, h1, h2]
  · simp [entryFrame, makeL_f]
  · simp [entryFrame, makeL_f, Array.getElem?_replicate] at hy

theorem refinesL_of_hyp (H : Hyp T f g) : RefinesL T g T f := by
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold runL runCtxL at hd ⊢
  rw [H.flow] at hd ⊢
  rw [H.glow, params_eq H]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn, Bool.false_eq_true, ite_false] at hd
    have hc := ctxT_eq H
    have hout : (Ctx.makeL T g).outs = (Ctx.makeL T f).outs := by rw [hc]
    have hdef : (Ctx.makeL T g).defers = (Ctx.makeL T f).defers := by rw [hc]
    have hent : (Ctx.makeL T g).f.entry = (Ctx.makeL T f).f.entry := by
      rw [makeL_f, makeL_f]; exact H.entry
    rw [hout, hdef, act_eq (f := f) (g := g), hent]
    exact finish_refines hd (runLoopL_sim (fun S T' _ _ => FRel T f g S T')
      (fun _ _ bid i R => block_sim H R bid i) fuel _ _ _ _ (entry_rel H env args mem)
      (finish_defined hd))

end

/-- **`late lower` refines its input** (`runL`) when `lateB` accepts its result (module doc). -/
theorem lateLower_refinesL {penv : PassEnv} {f : Func} {out : PassOut}
    (_h : lateLower penv f = .ok out) (hv : lateB penv.tables out.tables f out.func = true) :
    RefinesL out.tables out.func penv.tables f := by
  obtain ⟨hta, H⟩ := hyp_of hv
  intro env args mem fuel hd
  rw [← Low.runL_tabsAgreeL hta] at hd ⊢
  exact refinesL_of_hyp H env args mem fuel hd

end GoFV.Proof.LateLowerL
