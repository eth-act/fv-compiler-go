import GoFV.Proof.Pass.LateLowerNarrow
import GoFV.Proof.Low.TabsAgreeL

variable [GoFV.SSA.Sem.Addrs]

/-!
# `late lower` refines its input (issue #385)

When the validator `lateB` (`GoFV.Opt.LateLowerCheck`) accepts `late lower`'s result `g` for its
input `f`, `g` runs as `f` under `runL` (`lateLower_refinesL`): a lock-step simulation
(`runLoopL_sim`) whose frames agree on the values of both (`FRel`), the registers of `f`'s
producers holding their extension (`ExtAt`), those at the `bool` shape a boolean (`BoolV`), and the
register of each value gone from `g` (line 29's `MOVBUreg` of a condition `x`) the integer 0 or 1
of `x`'s boolean (`NarrowR`). Each block lists `f`'s values but the gone ones, and the new
constants; its `runL` order is `f`'s without the gone values, with the new constants interleaved,
each before its readers (`blkOK`), so evaluating it (`evalAll_sim`) evaluates the constants
(`MOVDconst`, never failing) in the target only, the gone values (`gone_eval`) in the source only,
and the others alike: an unchanged value reads the same registers, or `x` where `f`'s read a gone
value, as a register (`step_val`, `LateLowerNarrow`); a rewritten one evaluates to what its source
does (`LateLowerVal`: the dropped extension of a producer's register, the register op of an
immediate op on the materialized constant, `SLLconst [1]` as `ADD`, `ZERO` as `MOVDconst [0]`,
`MOVDnop` as `MOVDreg`). A gone value is read only while `x` holds what it was computed from
(`winOK`: along a block, the gone values whose `x` ran after them, `FRelW`'s `W`, are not read, and
none is left at its end). The `Phi`s read `x` at an integer shape where `f`'s read a gone value
(`phis_rel`); the terminators read values of both. The tables of `g` agree with `f`'s for `f`
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
  blk : ∀ b, blkOK f g (goneL f g) b = true
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

/-- What `valOK` says of a value of `f` and `g`. -/
theorem valOK_some (H : Hyp T f g) {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hw : g.value? x = some w) :
    u.id = x ∧ w.id = u.id ∧ w.type = u.type ∧
      ((w.op = u.op ∧ w.aux = u.aux ∧ w.auxInt = u.auxInt ∧
          argsOK (shapesL T f) f g u w = true) ∨
        (u.op ≠ .Phi ∧ (∀ a ∈ u.args, inF g a = true) ∧
          rwOK (shapesL T f) (shapesL T g) f g u w = true)) := by
  have h := H.val x
  unfold valOK at h
  rw [hu, hw] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    Array.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  rcases h4 with ⟨⟨⟨h5, h6⟩, h7⟩, h8⟩ | ⟨⟨h5, h6⟩, h7⟩
  · exact .inl ⟨h5, h6, h7, h8⟩
  · exact .inr ⟨h5, fun a ha => by
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
      exact h6 i hi, h7⟩

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

/-- **A value of `f` gone from `g`** is line 29's `MOVBUreg` (`rw29`) of a condition `x` of both
at the `bool` shape (not a `Phi`), itself at an integer shape. -/
theorem gone_of (H : Hyp T f g) {v : ID} (hv : gone f g v = true) :
    ∃ u x ux, f.value? v = some u ∧ g.value? v = none ∧ u.id = v ∧ u.op = .ARM64MOVBUreg ∧
      u.args = #[x] ∧ base f v = some x ∧ isInt (shapesL T f)[v]? = true ∧ inF g x = true ∧
      isBool (shapesL T f)[x]? = true ∧ f.value? x = some ux ∧ ux.op ≠ .Phi := by
  simp only [gone, Bool.and_eq_true, Bool.not_eq_true'] at hv
  obtain ⟨u, hu⟩ := inF_some hv.1
  have hw := inF_none hv.2
  have h := H.val v
  unfold valOK at h
  rw [hu, hw] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hid, h⟩ := h
  unfold rw29 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hop, hint⟩, h⟩ := h
  split at h
  · rename_i x hl
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hg, hb⟩, hc⟩ := h
    have hua : u.args = #[x] := by
      rcases hu' : u.args with ⟨l⟩; rw [hu'] at hl; simp at hl; rw [hl]
    cases hx : f.value? x with
    | none => rw [hx] at hc; cases hc
    | some ux =>
      rw [hx] at hc
      simp only [Option.map_some, Option.getD_some] at hc
      refine ⟨u, x, ux, hu, hw, hid, hop, hua, by simp [base, hu, hua], hid ▸ hint, hg, hb, hx,
        fun hp => ?_⟩
      rw [hp] at hc
      exact absurd hc (by decide)
  · cases h

/-- What `argsOK` says, position by position. -/
theorem argsOK_spec {tys : Array Ty} {u w : Value} (h : argsOK tys f g u w = true) :
    w.args.size = u.args.size ∧ ∀ j a, u.args[j]? = some a → ∃ b, w.args[j]? = some b ∧
      ((b = a ∧ inF f a = true ∧ inF g a = true) ∨
        (gone f g a = true ∧ base f a = some b ∧ regPos tys u j = true)) := by
  unfold argsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hs, hall⟩ := h
  refine ⟨hs, fun j a ha => ?_⟩
  have hj : j < u.args.size := (Array.getElem?_eq_some_iff.1 ha).1
  have := hall j hj
  rw [ha] at this
  cases hb : w.args[j]? with
  | none => rw [hb] at this; cases this
  | some b =>
    rw [hb] at this
    unfold argOK at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
    refine ⟨b, rfl, ?_⟩
    rcases this with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
    · exact .inl ⟨h1.symm, h2, h3⟩
    · exact .inr ⟨h1, h2, h3⟩

/-- `argsOK` with no gone argument: the same arguments, values of both. -/
theorem argsOK_eq {tys : Array Ty} {u w : Value} (h : argsOK tys f g u w = true)
    (hg : ∀ a ∈ u.args, inF g a = true) :
    w.args = u.args ∧ ∀ a ∈ u.args, inF f a = true ∧ inF g a = true := by
  obtain ⟨hs, hj⟩ := argsOK_spec h
  have hpos : ∀ j (hj' : j < u.args.size), w.args[j]? = some u.args[j] ∧
      inF f u.args[j] = true ∧ inF g u.args[j] = true := by
    intro j hj'
    obtain ⟨b, hb, hc⟩ := hj j u.args[j] (by simp [hj'])
    rcases hc with ⟨rfl, h1, h2⟩ | ⟨h1, -, -⟩
    · exact ⟨hb, h1, h2⟩
    · simp only [gone, hg _ (Array.getElem_mem hj'), Bool.not_true, Bool.and_false] at h1
      cases h1
  refine ⟨Array.ext hs fun j h1 h2 => ?_, fun a ha => ?_⟩
  · have := (hpos j h2).1
    rw [Array.getElem?_eq_getElem h1] at this
    exact Option.some.inj this
  · obtain ⟨j, hj', rfl⟩ := Array.mem_iff_getElem.1 ha
    exact (hpos j hj').2

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

theorem sxOf_default (v : Value) : sxOf default v = none := by
  unfold sxOf
  cases v.args[0]? with
  | none => rfl
  | some a => first | rfl | simp [Func.value?]

/-- `evalOpL` of a value of `f` other than `MOVDreg`/`MOVDnop` and its counterpart in `g` with the
same op (whatever their arguments) in related frames. -/
theorem evalOpL_swap (H : Hyp T f g) {fl : Bool} {env : Env} {frS frT : Frame} {u w : Value}
    (hfr : frT = { frS with regs := frT.regs }) (hop : w.op = u.op) (haux : w.aux = u.aux)
    (hai : w.auxInt = u.auxInt) (hid : w.id = u.id) (hm : u.op ≠ .ARM64MOVDreg)
    (hn : u.op ≠ .ARM64MOVDnop) (argv : List Val) (ty : Ty) :
    evalOpL fl env (Ctx.makeL T g) frT w argv ty = evalOpL fl env (Ctx.makeL T f) frS u argv ty := by
  rw [hfr, evalOpL_frame,
    ← evalOpL_noF (ctx := Ctx.makeL T g) default (hop ▸ hm) (hop ▸ hn),
    ← evalOpL_noF (ctx := Ctx.makeL T f) default hm hn]
  exact evalOpL_congr hop haux hai hid (by rw [tabs_makeL, tabs_makeL]) (params_eq H) act_eq
    (by rw [sxOf_default, sxOf_default])

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
the values of both; the producers' registers hold their extension, those at the `bool` shape a
boolean; the register of a gone value (its `x`: `base`) not in `W` is the integer 0 or 1 of
`x`'s boolean (`NarrowR`). -/
structure FRelW (T : Tables) (f g : Func) (W : List ID) (frS frT : Frame) : Prop where
  fr : frT = { frS with regs := frT.regs }
  agree : ∀ i, inF f i = true → inF g i = true → frT.regs[i]? = frS.regs[i]?
  szS : frS.regs.size = f.valueTab.size
  szT : frT.regs.size = g.valueTab.size
  prod : ∀ x u, f.value? x = some u → ∀ s k, prodSig u.op = some (s, k) → ∀ y,
    frS.regs[x]? = some (some y) → ExtAt s k ((Ctx.makeL T f).tys[x]?.getD .other) y
  bool : ∀ (x : ID) (y : Val), (Ctx.makeL T f).tys[x]? = some .bool → frS.regs[x]? = some (some y) → BoolV y
  narrow : ∀ (v x : ID), gone f g v = true → base f v = some x → v ∉ W → ∀ (s : Val),
    frS.regs[v]? = some (some s) → ∃ t, frT.regs[x]? = some (some t) ∧ NarrowR s t

/-- `FRelW` between blocks: no gone value open. -/
abbrev FRel (T : Tables) (f g : Func) (frS frT : Frame) : Prop := FRelW T f g [] frS frT

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

/-! ## Gone arguments -/

private theorem mapM_spec' {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L →
      L.length = l.length ∧ ∀ (k : Nat) a, l[k]? = some a → ∃ z, r a = some z ∧ L[k]? = some z
  | [], L, h => by
    rw [List.mapM_nil] at h; cases h; exact ⟨rfl, fun _ _ h => by simp at h⟩
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : r a with
    | none => rw [ha] at h; cases h
    | some z =>
      rw [ha] at h
      change (l.mapM (fun a => Res.ofOption (m a) (r a))).bind (fun L' => .ok (z :: L')) = _ at h
      cases hl : l.mapM (fun a => Res.ofOption (m a) (r a)) with
      | panic e mm => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h
      | ok L' =>
        rw [hl] at h; cases h
        obtain ⟨h1, h2⟩ := mapM_spec' hl
        refine ⟨by simp [h1], fun k b hb => ?_⟩
        cases k with
        | zero => simp at hb; subst hb; exact ⟨z, ha, rfl⟩
        | succ k => exact h2 k b (by simpa using hb)

private theorem mapM_of' {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID}, (∀ a ∈ l, ∃ z, r a = some z) →
      ∃ L, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L ∧ L.length = l.length ∧
        ∀ (k : Nat) a z, l[k]? = some a → r a = some z → L[k]? = some z
  | [], _ => ⟨[], rfl, rfl, fun _ _ _ h => by simp at h⟩
  | a :: l, h => by
    obtain ⟨z, hz⟩ := h a List.mem_cons_self
    obtain ⟨L, hL, hlen, hk⟩ := mapM_of' (m := m) (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨z :: L, ?_, by simp [hlen], fun k b z' hb hz' => ?_⟩
    · rw [List.mapM_cons, hz]
      change (l.mapM (fun a => Res.ofOption (m a) (r a))).bind (fun L' => .ok (z :: L')) = _
      rw [hL]; rfl
    · cases k with
      | zero => simp at hb; subst hb; rw [hz] at hz'; cases hz'; rfl
      | succ k => exact hk k b z' (by simpa using hb) hz'

/-- The arguments a value of `g` reads where its source in `f` reads `argvS`: `argvS` but at the
positions `u` reads as a register (`regPos`), where they may be the `NarrowR` counterpart. -/
def ArgRel (tys : Array Ty) (u : Value) (argvS argvT : List Val) : Prop :=
  argvT.length = argvS.length ∧ ∀ j s, argvS[j]? = some s → ∃ t, argvT[j]? = some t ∧
    (t = s ∨ (regPos tys u j = true ∧ NarrowR s t))

/-- **The arguments of a value of `g`** whose source's are `argsOK`: a gone one read as its `x`. -/
theorem argsL_rel {W : List ID} {frS frT : Frame} (R : FRelW T f g W frS frT) {u w : Value}
    (hargs : argsOK (shapesL T f) f g u w = true) (hW : ∀ a ∈ u.args, gone f g a = true → a ∉ W)
    {argvS : List Val} (hS : argsL frS u = .ok argvS) :
    ∃ argvT, argsL frT w = .ok argvT ∧ ArgRel (shapesL T f) u argvS argvT := by
  obtain ⟨hsz, hspec⟩ := argsOK_spec hargs
  obtain ⟨hlS, hS⟩ := mapM_spec' hS
  -- each argument of `w` has a register
  have hpos : ∀ j a, u.args[j]? = some a → ∀ s, (frS.regs[a]?).join = some s →
      ∃ b t, w.args[j]? = some b ∧ (frT.regs[b]?).join = some t ∧
        (t = s ∨ (regPos (shapesL T f) u j = true ∧ NarrowR s t)) := by
    intro j a ha s hs
    obtain ⟨b, hb, hc⟩ := hspec j a ha
    rcases hc with ⟨rfl, h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨b, s, hb, by rw [R.agree b h1 h2]; exact hs, .inl rfl⟩
    · have hs' : frS.regs[a]? = some (some s) := by
        cases h : frS.regs[a]? with
        | none => rw [h] at hs; cases hs
        | some o => rw [h] at hs; simp at hs; rw [hs]
      obtain ⟨t, ht, hn⟩ := R.narrow a b h1 h2 (hW a (Array.mem_of_getElem? ha) h1) s hs'
      exact ⟨b, t, hb, by rw [ht]; rfl, .inr ⟨h3, hn⟩⟩
  have hall : ∀ b ∈ w.args.toList, ∃ t, (frT.regs[b]?).join = some t := by
    intro b hb
    obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
    have hj' : j < u.args.size := by simp at hj; omega
    obtain ⟨s, hs, -⟩ := hS j u.args[j] (by simp [hj'])
    obtain ⟨b', t, hb', ht, -⟩ := hpos j u.args[j] (by simp [hj']) s hs
    have : w.args[j]? = some b := by rw [← hjb]; simp
    rw [this] at hb'; cases hb'
    exact ⟨t, ht⟩
  obtain ⟨argvT, hT, hlT, hk⟩ := mapM_of'
    (m := fun a => s!"v{w.id}: argument v{a} has no value") hall
  refine ⟨argvT, hT, by rw [hlT, hlS]; simp [hsz], fun j s hs => ?_⟩
  have hj : j < u.args.size := by
    have := (List.getElem?_eq_some_iff.1 hs).1; rw [hlS] at this; simpa using this
  obtain ⟨s', hs', hjs⟩ := hS j u.args[j] (by simp [hj])
  rw [hs] at hjs; cases hjs
  obtain ⟨b, t, hb, ht, hc⟩ := hpos j u.args[j] (by simp [hj]) s hs'
  exact ⟨t, hk j b t (by rw [Array.getElem?_toList]; exact hb) ht, hc⟩

theorem regLikeL_of : ∀ {l l' : List Val}, l'.length = l.length →
    (∀ (j : Nat) s, l[j]? = some s → ∃ t, l'[j]? = some t ∧ (t = s ∨ NarrowR s t)) → RegLikeL l l'
  | [], [], _, _ => .nil
  | s :: l, t :: l', hl, h => by
    obtain ⟨t', ht, hc⟩ := h 0 s rfl
    simp at ht; subst ht
    refine .cons ?_ (regLikeL_of (by simpa using hl) fun j s hs => h (j + 1) s (by simpa using hs))
    rcases hc with rfl | hn
    · exact .refl _
    · exact regLike_of hn
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- A store whose result is not `stuck` read an address, a value and a memory. -/
theorem st_shape {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} (ho : u.op ∈ stOps)
    {argv : List Val} {ty : Ty} {r : Res Val} (h : arm64Op false env ctx fr u argv ty = r)
    (hr : ∀ msg, r ≠ .stuck msg) : ∃ a x m, argv = [a, x, .mem m] := by
  simp only [stOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold arm64Op at h
  rcases ho with ho | ho | ho | ho <;>
  · simp only [show nilFaults false ctx u argv = none from rfl, ho] at h
    split at h
    · exact ⟨_, _, _, rfl⟩
    · exfalso; subst h; split at hr <;> exact hr _ rfl

/-- **A reader of a gone value** (a `regOps` op or a store, `regPos`) does on its target
arguments what it does on its source's. -/
theorem reader_eq {fl : Bool} (hfl : fl = false) {env : Env} {ctx : Ctx} {fr : Frame} {u : Value}
    {tys : Array Ty} (ho : u.op ∈ regOps ∨ u.op ∈ stOps) {argvS argvT : List Val} {ty : Ty}
    (hrel : ArgRel tys u argvS argvT) {r : Res Val} (hS : evalOpL fl env ctx fr u argvS ty = r)
    (hr : ∀ msg, r ≠ .stuck msg) : evalOpL fl env ctx fr u argvT ty = r := by
  subst hfl
  obtain ⟨hl, hj⟩ := hrel
  rcases ho with ho | ho
  · obtain ⟨hg, ha, hroot, -⟩ := regOps_pure _ ho
    rw [evalOpL_pure hg ha hroot] at hS ⊢
    rw [← hS, evalPure_rl ho (regLikeL_of hl fun j s hs => ?_)]
    obtain ⟨t, ht, hc⟩ := hj j s hs
    exact ⟨t, ht, hc.imp_right (·.2)⟩
  · obtain ⟨hg, ha, -⟩ := stOps_act _ ho
    have hnr : u.op ∉ regOps := fun h => (regOps_pure _ h).2.2.2.2.2.2 ho
    have hpos : ∀ j, j ≠ 1 → regPos tys u j = false := by
      intro j hj1
      have hnp : u.op ≠ .Phi := (stOps_act _ ho).2.2.2.2
      simp [regPos, hnr, hj1, hnp]
    rw [evalOpL_act hg ha] at hS ⊢
    obtain ⟨a, xs, m, rfl⟩ := st_shape ho hS hr
    have h0 := hj 0 a rfl
    have h1 := hj 1 xs rfl
    have h2 := hj 2 (.mem m) rfl
    obtain ⟨a', ha', hc0⟩ := h0
    obtain ⟨xt, hxt, hc1⟩ := h1
    obtain ⟨m', hm', hc2⟩ := h2
    have e0 : a' = a := hc0.resolve_right fun h => by rw [hpos 0 (by omega)] at h; cases h.1
    have e2 : m' = .mem m := hc2.resolve_right fun h => by rw [hpos 2 (by omega)] at h; cases h.1
    have hn : NarrowR xs xt := by
      rcases hc1 with rfl | ⟨-, hn⟩
      · exact .inl rfl
      · exact hn
    have hT : argvT = [a, xt, .mem m] := by
      simp only [List.length_cons, List.length_nil] at hl
      match argvT, hl, ha', hxt, hm' with
      | [a₁, x₁, m₁], _, h1, h2, h3 =>
        simp at h1 h2 h3; rw [h1, h2, h3, e0, e2]
    rw [hT, st_narrow ho hn, hS]

/-- **A value of `f` and its counterpart in `g`** evaluate alike in related frames, when `g`'s
reads its new constants and no gone value of `W` (and no `Phi` reads one). -/
theorem step_val (H : Hyp T f g) {env : Env} {W : List ID} {frS frT : Frame}
    (R : FRelW T f g W frS frT) {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hw : g.value? x = some w)
    (hc : ∀ c ∈ w.args, inF f c = false →
      ∃ wc, g.value? c = some wc ∧ frT.regs[c]? = some (some (cval T g c wc)))
    (hW : ∀ a ∈ u.args, gone f g a = true → a ∉ W ∧ u.op ≠ .Phi) :
    (∀ y, evalValueL mdL env (Ctx.makeL T f) frS u = .ok y →
      evalValueL mdL env (Ctx.makeL T g) frT w = .ok y) ∧
    (∀ e m, evalValueL mdL env (Ctx.makeL T f) frS u = .panic e m →
      evalValueL mdL env (Ctx.makeL T g) frT w = .panic e m) := by
  obtain ⟨hid, hwid, htype, hcase⟩ := valOK_some H hu hw
  have hty : (Ctx.makeL T g).tys[u.id]? = (Ctx.makeL T f).tys[u.id]? := by
    rw [hid]; exact tys_eq H hu hw htype
  -- both sides equal
  have same : evalValueL mdL env (Ctx.makeL T g) frT w =
      evalValueL mdL env (Ctx.makeL T f) frS u →
      (∀ y, evalValueL mdL env (Ctx.makeL T f) frS u = .ok y →
        evalValueL mdL env (Ctx.makeL T g) frT w = .ok y) ∧
      (∀ e m, evalValueL mdL env (Ctx.makeL T f) frS u = .panic e m →
        evalValueL mdL env (Ctx.makeL T g) frT w = .panic e m) :=
    fun h => ⟨fun y hy => h.trans hy, fun e m hp => h.trans hp⟩
  rcases hcase with ⟨hop, haux, hai, hargs⟩ | ⟨hnp, hG, hrw⟩
  · by_cases hng : ∀ a ∈ u.args, inF g a = true
    · obtain ⟨hargs', hin⟩ := argsOK_eq hargs hng
      refine same (evalValueL_same H R.fr (fun a ha => R.agree a (hin a ha).1 (hin a ha).2) hop
        haux hai hwid hargs' hty fun hm => ?_)
      rw [sx_of H hw (hop ▸ hm), sxIn_args hargs']
    -- a gone argument: `u` reads it as a register
    have hng' : ∃ a ∈ u.args, inF g a = false := by
      refine Classical.byContradiction fun hne => hng fun a ha => ?_
      cases h : inF g a
      · exact absurd ⟨a, ha, h⟩ hne
      · rfl
    obtain ⟨a0, ha0, hg0⟩ := hng'
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 ha0
    obtain ⟨-, hspec⟩ := argsOK_spec hargs
    obtain ⟨b, -, hc0⟩ := hspec j u.args[j] (by simp [hj])
    obtain ⟨hgone, hpos⟩ : gone f g u.args[j] = true ∧ regPos (shapesL T f) u j = true := by
      rcases hc0 with ⟨-, -, h⟩ | ⟨h1, -, h3⟩
      · rw [hg0] at h; cases h
      · exact ⟨h1, h3⟩
    have hnphi : u.op ≠ .Phi := (hW _ ha0 hgone).2
    have hfam : u.op ∈ regOps ∨ u.op ∈ stOps := by
      unfold regPos at hpos
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hpos
      rcases hpos with (h | ⟨h, -⟩) | ⟨h, -⟩
      · exact .inl h
      · exact .inr h
      · exact absurd h hnphi
    have hnm : u.op ≠ .ARM64MOVDreg ∧ u.op ≠ .ARM64MOVDnop := by
      rcases hfam with h | h
      · exact ⟨(regOps_pure _ h).2.2.2.1, (regOps_pure _ h).2.2.2.2.1⟩
      · exact ⟨(stOps_act _ h).2.2.1, (stOps_act _ h).2.2.2.1⟩
    have hswap := evalOpL_swap H (fl := mdL.faulting) (env := env) R.fr hop haux hai hwid
      hnm.1 hnm.2
    have hWa : ∀ a ∈ u.args, gone f g a = true → a ∉ W := fun a ha h => (hW a ha h).1
    -- the target evaluates its arguments and the op as the source does
    have key : ∀ argvS, argsL frS u = .ok argvS → ∀ r,
        evalOpL mdL.faulting env (Ctx.makeL T f) frS u argvS
          ((Ctx.makeL T f).tys[u.id]?.getD .other) = r → (∀ msg, r ≠ .stuck msg) →
        evalValueL mdL env (Ctx.makeL T g) frT w =
          r.bind fun r => .ok (mdL.retype ((Ctx.makeL T f).tys[u.id]?.getD .other) r) := by
      intro argvS hmS r hr hns
      obtain ⟨argvT, hmT, hrel⟩ := argsL_rel R hargs hWa hmS
      rw [evalValueL_of_args hmT, hwid, hty, hswap, reader_eq rfl hfam hrel hr hns]
    refine ⟨fun y hy => ?_, fun e m hp => ?_⟩
    · obtain ⟨argvS, hmS, r, hr, rfl⟩ := evalValueL_ok_args hy
      rw [key argvS hmS (.ok r) hr nofun]; rfl
    · cases hmS : argsL frS u with
      | ok argvS =>
        rw [evalValueL_of_args hmS] at hp
        cases he : evalOpL mdL.faulting env (Ctx.makeL T f) frS u argvS
            ((Ctx.makeL T f).tys[u.id]?.getD .other) with
        | ok r => rw [he] at hp; cases hp
        | panic e' m' =>
          rw [he] at hp; cases hp
          rw [key argvS hmS _ he nofun]; rfl
        | stuck msg => rw [he] at hp; cases hp
      | panic e m => exact absurd hmS mapM_ofOption_ne_panic
      | stuck msg =>
        unfold evalValueL at hp; simp only [argsL] at hmS; rw [hmS] at hp; cases hp
  have hregs : ∀ a ∈ u.args, inF f a = true → frT.regs[a]? = frS.regs[a]? :=
    fun a ha hf => R.agree a hf (hG a ha)
  unfold rwOK at hrw
  simp only [Bool.or_eq_true] at hrw
  rcases hrw with (((h91 | h98) | h103) | hext) | himm
  · -- `MOVDreg` → `MOVDnop`
    unfold rw91 at h91
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h91
    obtain ⟨⟨⟨hu1, hw1⟩, hargs⟩, hin⟩ := h91
    refine same (evalValueL_of_op R.fr (fun a ha => ?_) hwid hargs hty fun argv ty => ?_)
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
      exact hregs _ (Array.getElem_mem hi) (hin i hi)
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
      have hTa : frT.regs[x0]? = some (some a) := by rw [hregs _ (by rw [hua]; simp) hin, ha]
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
        have hTa : frT.regs[x0]? = some (some a) := by rw [hregs _ (by rw [hua]; simp) (inF_of hpx), ha]
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
      have hTa : frT.regs[x0]? = some (some a) := by rw [hregs _ (by rw [hua]; simp) hin, ha]
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

variable {frS frT : Frame} {W : List ID}

/-- The new constants of `seen` hold their value in the target frame. -/
def Seen (T : Tables) (f g : Func) (seen : List ID) (frT : Frame) : Prop :=
  ∀ c ∈ seen, inF f c = false →
    ∃ wc, g.value? c = some wc ∧ frT.regs[c]? = some (some (cval T g c wc))

theorem tys_bool {x : ID} (H : Hyp T f g) (h : isBool (shapesL T f)[x]? = true) :
    (Ctx.makeL T f).tys[x]? = some .bool := by
  rw [makeL_tys H.flow]
  unfold isBool at h
  split at h
  · rename_i h'; exact h'
  · cases h

theorem tys_int {x : ID} (H : Hyp T f g) (h : isInt (shapesL T f)[x]? = true) :
    ∃ w, (Ctx.makeL T f).tys[x]? = some (.int w) := by
  rw [makeL_tys H.flow]
  unfold isInt at h
  split at h
  · rename_i w h'; exact ⟨w, h'⟩
  · cases h

/-- A value of both evaluated in both frames: a gone value whose `x` it is opens (`W'`). -/
theorem FRelW.set (R : FRelW T f g W frS frT) {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hw : g.value? x = some w) {y : Val}
    (hp : ∀ s k, prodSig u.op = some (s, k) → ExtAt s k ((Ctx.makeL T f).tys[x]?.getD .other) y)
    (hb : (Ctx.makeL T f).tys[x]? = some .bool → BoolV y) {W' : List ID}
    (hW : ∀ v, gone f g v = true → v ∉ W' → v ∉ W ∧ base f v ≠ some x) :
    FRelW T f g W' (frS.set x y) (frT.set x y) := by
  obtain ⟨hfr, hag, hs, ht, hpr, hbo, hna⟩ := R
  have hxs : x < frS.regs.size := by rw [hs]; exact lt_of_value? hu
  have hxt : x < frT.regs.size := by rw [ht]; exact lt_of_value? hw
  refine ⟨?_, fun i hi hig => ?_, by simp [Frame.set, hs], by simp [Frame.set, ht], ?_, ?_, ?_⟩
  · rw [hfr]; rfl
  · by_cases hix : x = i
    · subst hix; rw [Frame.set_regs_self hxs, Frame.set_regs_self hxt]
    · rw [Frame.set_regs_ne hix, Frame.set_regs_ne hix, hag i hi hig]
  · intro x' u' hu' s k hk y' hy'
    by_cases hix : x = x'
    · subst hix
      rw [hu] at hu'; cases hu'
      rw [Frame.set_regs_self hxs] at hy'; cases hy'
      exact hp s k hk
    · rw [Frame.set_regs_ne hix] at hy'
      exact hpr x' u' hu' s k hk y' hy'
  · intro x' y' hty hy'
    by_cases hix : x = x'
    · subst hix
      rw [Frame.set_regs_self hxs] at hy'; cases hy'
      exact hb hty
    · rw [Frame.set_regs_ne hix] at hy'
      exact hbo x' y' hty hy'
  · intro v x' hv hbx hvW s hsv
    obtain ⟨hvW0, hne⟩ := hW v hv hvW
    have hvx : x ≠ v := by
      rintro rfl
      simp only [gone, inF_of hw, Bool.not_true, Bool.and_false] at hv
      cases hv
    rw [Frame.set_regs_ne hvx] at hsv
    obtain ⟨t, htv, hn⟩ := hna v x' hv hbx hvW0 s hsv
    have hxx : x ≠ x' := fun h => hne (h ▸ hbx)
    exact ⟨t, by rw [Frame.set_regs_ne hxx]; exact htv, hn⟩

/-- A new constant evaluated in the target only. -/
theorem FRelW.setT (H : Hyp T f g) (R : FRelW T f g W frS frT) {c : ID} (hc : inF f c = false)
    (y : Val) : FRelW T f g W frS (frT.set c y) := by
  obtain ⟨hfr, hag, hs, ht, hpr, hbo, hna⟩ := R
  refine ⟨?_, fun i hi hig => ?_, hs, by simp [Frame.set, ht], hpr, hbo, ?_⟩
  · rw [hfr]; rfl
  · have : c ≠ i := fun h => by subst h; rw [hc] at hi; cases hi
    rw [Frame.set_regs_ne this, hag i hi hig]
  · intro v x hv hbx hvW s hsv
    obtain ⟨u, x', ux, -, -, -, -, -, hbx', -, -, -, hux, -⟩ := gone_of H hv
    rw [hbx] at hbx'; cases hbx'
    have : c ≠ x := fun h => by subst h; rw [inF_of hux] at hc; cases hc
    obtain ⟨t, htv, hn⟩ := hna v x hv hbx hvW s hsv
    exact ⟨t, by rw [Frame.set_regs_ne this]; exact htv, hn⟩

/-- A gone value evaluated in the source only (from the register of its `x`): it closes. -/
theorem FRelW.setS (H : Hyp T f g) (R : FRelW T f g W frS frT) {v x : ID} {u : Value}
    (hu : f.value? v = some u) (hv : gone f g v = true) (hbx : base f v = some x) {s : Val}
    (hn : ∃ t, frT.regs[x]? = some (some t) ∧ NarrowR s t)
    (hp : ∀ s' k, prodSig u.op = some (s', k) →
      ExtAt s' k ((Ctx.makeL T f).tys[v]?.getD .other) s) :
    FRelW T f g (W.filter (· != v)) (frS.set v s) frT := by
  obtain ⟨u', x', ux, hu', -, -, -, -, hbx', hint, -, -, -, -⟩ := gone_of H hv
  rw [hu] at hu'; cases hu'
  rw [hbx] at hbx'; cases hbx'
  obtain ⟨hfr, hag, hs, ht, hpr, hbo, hna⟩ := R
  have hvs : v < frS.regs.size := by rw [hs]; exact lt_of_value? hu
  have hvg : inF g v = false := by
    simp only [gone, Bool.and_eq_true, Bool.not_eq_true'] at hv; exact hv.2
  refine ⟨?_, fun i hi hig => ?_, by simp [Frame.set, hs], ht, ?_, ?_, ?_⟩
  · rw [hfr]; rfl
  · have : v ≠ i := fun h => by subst h; rw [hvg] at hig; cases hig
    rw [Frame.set_regs_ne this, hag i hi hig]
  · intro x'' u'' hu'' s' k hk y' hy'
    by_cases hix : v = x''
    · subst hix
      rw [hu] at hu''; cases hu''
      rw [Frame.set_regs_self hvs] at hy'; cases hy'
      exact hp s' k hk
    · rw [Frame.set_regs_ne hix] at hy'
      exact hpr x'' u'' hu'' s' k hk y' hy'
  · intro x'' y' hty hy'
    by_cases hix : v = x''
    · subst hix
      obtain ⟨w', hw'⟩ := tys_int H hint
      rw [hw'] at hty; cases hty
    · rw [Frame.set_regs_ne hix] at hy'
      exact hbo x'' y' hty hy'
  · intro v' x'' hv' hbx'' hvW s' hsv
    by_cases hvv : v = v'
    · subst hvv
      rw [hbx] at hbx''; cases hbx''
      rw [Frame.set_regs_self hvs] at hsv; cases hsv
      exact hn
    · rw [Frame.set_regs_ne hvv] at hsv
      have : v' ∉ W := fun h => hvW (List.mem_filter.2 ⟨h, by simp [Ne.symm hvv]⟩)
      exact hna v' x'' hv' hbx'' this s' hsv

/-- **A gone value** (`MOVBUreg x`) evaluates to the integer 0 or 1 of `x`'s boolean (or `poison`
of `poison`), in the source. -/
theorem gone_eval (H : Hyp T f g) (R : FRelW T f g W frS frT) {env : Env} {v x : ID}
    {u : Value} (hu : f.value? v = some u) (hv : gone f g v = true) (hbx : base f v = some x)
    {s : Val} (h : evalValueL mdL env (Ctx.makeL T f) frS u = .ok s) :
    ∃ t, frT.regs[x]? = some (some t) ∧ NarrowR s t := by
  obtain ⟨u', x', ux, hu', -, hid, hop, hua, hbx', hint, hg, hbool, hux, -⟩ := gone_of H hv
  rw [hu] at hu'; cases hu'
  rw [hbx] at hbx'; cases hbx'
  obtain ⟨argv, hm, r, hr, rfl⟩ := evalValueL_ok_args h
  obtain ⟨a, ha, rfl⟩ := argsL_one_inv hua hm
  obtain ⟨w, hw⟩ := tys_int H hint
  rw [hid, hw] at hr ⊢
  rw [evalOpL_pure (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; decide), hop] at hr
  cases hr
  refine ⟨a, by rw [R.agree x (inF_of hux) hg, ha], ?_⟩
  exact movbu_narrow (md := mdL) rfl (R.bool x a (tys_bool H hbool) ha)

theorem mem_goneL {v : ID} (hv : gone f g v = true) : v ∈ goneL f g := by
  refine List.mem_filter.2 ⟨List.mem_range.2 ?_, hv⟩
  simp only [gone, Bool.and_eq_true] at hv
  obtain ⟨u, hu⟩ := inF_some hv.1
  exact lt_of_value? hu

theorem fresh_eval {env : Env} {fr : Frame} {x : ID} {w : Value} (hop : w.op = .ARM64MOVDconst)
    (ha : w.args = #[]) (hid : w.id = x) :
    evalValueL mdL env (Ctx.makeL T g) fr w = .ok (cval T g x w) := by
  rw [evalValueL_of_args (argsL_nil ha), evalOpL_pure (by rw [hop]; rfl) (by rw [hop]; rfl)
    (by rw [hop]; decide), hop, hid]
  rfl

theorem prodSig_phi : prodSig .Phi = none := by decide

/-- What evaluating the orders `oS` (source) and `oT` (target) from related frames gives. -/
def SimRes (T : Tables) (f g : Func) (env : Env) (frS frT : Frame) (oS oT : List ID) : Prop :=
  (∀ frS', evalAllL mdL env (Ctx.makeL T f) frS oS = .ok frS' →
    ∃ frT', evalAllL mdL env (Ctx.makeL T g) frT oT = .ok frT' ∧ FRel T f g frS' frT') ∧
  (∀ e m, evalAllL mdL env (Ctx.makeL T f) frS oS = .panic e m →
    evalAllL mdL env (Ctx.makeL T g) frT oT = .panic e m)

/-- The target's step over a new constant `c`. -/
theorem fresh_step (H : Hyp T f g) {env : Env} {c : ID} {oT seen : List ID}
    (hcf : inF f c = false) (hall : ∀ x ∈ c :: oT, (g.value? x).isSome = true)
    (hS : Seen T f g seen frT) (hsz : frT.regs.size = g.valueTab.size) :
    ∃ w, evalAllL mdL env (Ctx.makeL T g) frT (c :: oT) =
        evalAllL mdL env (Ctx.makeL T g) (frT.set c (cval T g c w)) oT ∧
      Seen T f g (c :: seen) (frT.set c (cval T g c w)) := by
  obtain ⟨w, hw⟩ : ∃ w, g.value? c = some w :=
    Option.isSome_iff_exists.1 (hall c List.mem_cons_self)
  obtain ⟨hop, hargs, hid⟩ := valOK_fresh H (inF_none hcf) hw
  have hct : c < frT.regs.size := by rw [hsz]; exact lt_of_value? hw
  refine ⟨w, by rw [evalAllL_cons, stepVL_of (by rw [makeL_f]; exact hw),
    fresh_eval hop hargs hid], fun c' hc' hcf' => ?_⟩
  rcases List.mem_cons.1 hc' with rfl | hc'
  · exact ⟨w, hw, Frame.set_regs_self hct⟩
  · obtain ⟨wc, hwc, hr⟩ := hS c' hc' hcf'
    by_cases hcx : c = c'
    · subst hcx; rw [hw] at hwc; cases hwc; exact ⟨w, hw, Frame.set_regs_self hct⟩
    · exact ⟨wc, hwc, by rw [Frame.set_regs_ne hcx]; exact hr⟩

/-- The source's step over a gone value `v`. -/
theorem gone_step (H : Hyp T f g) {env : Env} (R : FRelW T f g W frS frT) {v : ID}
    {oS oT : List ID} (hv : gone f g v = true)
    (rec : ∀ s, FRelW T f g (W.filter (· != v)) (frS.set v s) frT →
      SimRes T f g env (frS.set v s) frT oS oT) :
    SimRes T f g env frS frT (v :: oS) oT := by
  obtain ⟨u, x, -, hu, -, hid, hop, -, hbx, -, -, -, -, -⟩ := gone_of H hv
  unfold SimRes
  rw [evalAllL_cons, stepVL_of (by rw [makeL_f]; exact hu)]
  cases hev : evalValueL mdL env (Ctx.makeL T f) frS u with
  | ok s =>
    dsimp only
    exact rec s (R.setS H hu hv hbx (gone_eval H R hu hv hbx hev) fun s' k hk => by
      have := prod_evalValueL rfl rfl hk hev
      rw [hid] at this; exact this)
  | panic e m =>
    exact absurd hev (pure_not_panic (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; decide))
  | stuck msg => exact ⟨fun _ h => (by cases h), fun _ _ h => by cases h⟩

/-- **Evaluating a block's order** in `g` (`oT`) does what evaluating `f`'s (`oS`) does: `oT` is
`oS` without the gone values, with the new constants interleaved. -/
theorem evalAll_sim (H : Hyp T f g) {env : Env} :
    ∀ (oS oT seen W : List ID) (frS frT : Frame), FRelW T f g W frS frT → Seen T f g seen frT →
      freshBefore f g seen oT = true → (∀ x ∈ oT, (g.value? x).isSome = true) →
      (∀ x ∈ oS, inF f x = true) → oT.filter (inF f) = oS.filter (inF g) →
      winOK f g (goneL f g) W oS = true → SimRes T f g env frS frT oS oT
  | [], [], _, W, frS, frT, R, _, _, _, _, _, hwin => by
    have hW : W = [] := by simpa [winOK] using hwin
    subst hW
    exact ⟨fun frS' h => by cases h; exact ⟨frT, rfl, R⟩, fun e m h => by cases h⟩
  | [], c :: oT, seen, W, frS, frT, R, hS, hb, hall, hfS, hfil, hwin => by
    have hcf : inF f c = false := by
      cases h : inF f c
      · rfl
      · rw [List.filter_cons_of_pos h] at hfil; cases hfil
    unfold freshBefore at hb
    rw [Bool.and_eq_true] at hb
    obtain ⟨w, hT, hS'⟩ := fresh_step H (env := env) hcf hall hS R.szT
    rw [List.filter_cons_of_neg (by simp [hcf])] at hfil
    have := evalAll_sim H (env := env) [] oT (c :: seen) W frS _ (R.setT H hcf _) hS' hb.2
      (fun z hz => hall z (List.mem_cons_of_mem _ hz)) hfS hfil hwin
    unfold SimRes at this ⊢
    rw [hT]; exact this
  | v :: oS, [], seen, W, frS, frT, R, hS, hb, hall, hfS, hfil, hwin => by
    cases hvg : inF g v
    · have hv : gone f g v = true := by simp [gone, hfS v List.mem_cons_self, hvg]
      rw [List.filter_cons_of_neg (p := inF g) (by simp [hvg])] at hfil
      simp only [winOK, hvg, Bool.false_eq_true, ite_false] at hwin
      exact gone_step H R hv fun s R' => evalAll_sim H (env := env) oS [] seen _ _ frT R' hS hb hall
        (fun z hz => hfS z (List.mem_cons_of_mem _ hz)) hfil hwin
    · rw [List.filter_cons_of_pos hvg] at hfil; cases hfil
  | v :: oS, c :: oT, seen, W, frS, frT, R, hS, hb, hall, hfS, hfil, hwin => by
    have hvf := hfS v List.mem_cons_self
    have hfS' : ∀ z ∈ oS, inF f z = true := fun z hz => hfS z (List.mem_cons_of_mem _ hz)
    have hall' : ∀ z ∈ oT, (g.value? z).isSome = true :=
      fun z hz => hall z (List.mem_cons_of_mem _ hz)
    cases hvg : inF g v
    · -- a gone value: only the source evaluates it
      have hv : gone f g v = true := by simp [gone, hvf, hvg]
      rw [List.filter_cons_of_neg (p := inF g) (by simp [hvg])] at hfil
      simp only [winOK, hvg, Bool.false_eq_true, ite_false] at hwin
      exact gone_step H R hv fun s R' => evalAll_sim H (env := env) oS (c :: oT) seen _ _ frT R' hS hb hall
        hfS' hfil hwin
    cases hcf : inF f c
    · -- a new constant: only the target evaluates it
      unfold freshBefore at hb
      rw [Bool.and_eq_true] at hb
      obtain ⟨w, hT, hS'⟩ := fresh_step H (env := env) hcf hall hS R.szT
      rw [List.filter_cons_of_neg (by simp [hcf])] at hfil
      have := evalAll_sim H (env := env) (v :: oS) oT (c :: seen) W frS _ (R.setT H hcf _) hS' hb.2 hall'
        hfS hfil hwin
      unfold SimRes at this ⊢
      rw [hT]; exact this
    -- a value of both: both evaluate it alike
    rw [List.filter_cons_of_pos hcf, List.filter_cons_of_pos hvg] at hfil
    obtain ⟨hcv, hfil'⟩ := List.cons.inj hfil
    clear hfil
    subst v
    unfold freshBefore at hb
    rw [Bool.and_eq_true] at hb
    obtain ⟨hx, hb⟩ := hb
    simp only [winOK, hvg, ite_true, Bool.and_eq_true] at hwin
    obtain ⟨hrd, hwin⟩ := hwin
    obtain ⟨u, hu⟩ := inF_some hcf
    obtain ⟨w, hw⟩ : ∃ w, g.value? c = some w :=
      Option.isSome_iff_exists.1 (hall c List.mem_cons_self)
    have hW : ∀ a ∈ u.args, gone f g a = true → a ∉ W ∧ u.op ≠ .Phi := by
      intro a ha hga
      rw [hu] at hrd
      simp only [Option.map_some, Option.getD_some, Array.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem,
        Bool.not_eq_true] at hrd
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
      rcases hrd i hi with h | ⟨h1, h2⟩
      · rw [hga] at h; cases h
      · exact ⟨fun h => by simp_all, h1⟩
    have hc : ∀ c' ∈ w.args, inF f c' = false →
        ∃ wc, g.value? c' = some wc ∧ frT.regs[c']? = some (some (cval T g c' wc)) := by
      intro c' hc' hcf'
      rw [hw] at hx
      simp only [Option.map_some, Option.getD_some, Array.all_eq_true, Bool.or_eq_true] at hx
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hc'
      rcases hx i hi with h | h
      · rw [hcf'] at h; cases h
      · exact hS _ (List.contains_iff_mem.1 h) hcf'
    obtain ⟨hok, hpan⟩ := step_val H R hu hw hc hW
    unfold SimRes
    rw [evalAllL_cons, evalAllL_cons, stepVL_of (by rw [makeL_f]; exact hu),
      stepVL_of (by rw [makeL_f]; exact hw)]
    cases hev : evalValueL mdL env (Ctx.makeL T f) frS u with
    | ok y =>
      rw [hok y hev]
      dsimp only
      have hid : u.id = c := (valOK_some H hu hw).1
      have R' := R.set (W' := W ++ (goneL f g).filter fun v' => base f v' == some c) hu hw
        (y := y) (fun s k hk => by
          have := prod_evalValueL rfl rfl hk hev
          rw [hid] at this; exact this)
        (fun hty => by
          obtain ⟨argv, -, r, -, rfl⟩ := evalValueL_ok_args hev
          rw [hid, hty]
          exact boolV_retype rfl r)
        (fun v' hv' hnot => by
          simp only [List.mem_append, List.mem_filter, beq_iff_eq, not_or, not_and] at hnot
          exact ⟨hnot.1, hnot.2 (mem_goneL hv')⟩)
      refine evalAll_sim H (env := env) oS oT (c :: seen) _ _ _ R' (fun c' hc' hcf' => ?_) hb hall' hfS'
        hfil' hwin
      rcases List.mem_cons.1 hc' with rfl | hc'
      · rw [hcf] at hcf'; cases hcf'
      · obtain ⟨wc, hwc, hr⟩ := hS c' hc' hcf'
        have hcx : c ≠ c' := fun h => by subst h; rw [hcf] at hcf'; cases hcf'
        exact ⟨wc, hwc, by rw [Frame.set_regs_ne hcx]; exact hr⟩
    | panic e m =>
      rw [hpan e m hev]
      exact ⟨fun _ h => (by cases h), fun _ _ h => by cases h; rfl⟩
    | stuck msg => exact ⟨fun _ h => (by cases h), fun _ _ h => by cases h⟩
termination_by oS oT _ _ _ _ _ _ _ _ _ _ _ => oS.length + oT.length

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

private theorem filterMapM_imp {α : Type} {s1 s2 : ID → Res (Option α)} :
    ∀ {l : List ID} {ps : List α}, (∀ z ∈ l, ∀ r, s1 z = .ok r → s2 z = .ok r) →
      l.filterMapM s1 = .ok ps → l.filterMapM s2 = .ok ps
  | [], _, _, hs => hs
  | z :: l, ps, h, hs => by
    have ih := fun ps' => @filterMapM_imp α s1 s2 l ps'
      (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.filterMapM_cons] at hs ⊢
    cases h1 : s1 z with
    | ok r =>
      rw [h z List.mem_cons_self r h1]
      rw [h1] at hs
      cases h2 : l.filterMapM s1 with
      | ok ps' => rw [ih ps' h2]; rw [h2] at hs; exact hs
      | panic e m => cases r <;> (rw [h2] at hs; cases hs)
      | stuck msg => cases r <;> (rw [h2] at hs; cases hs)
    | panic e m => rw [h1] at hs; cases hs
    | stuck msg => rw [h1] at hs; cases hs

theorem regOps_phi : regOps.contains .Phi = false := by decide

theorem stOps_phi : stOps.contains .Phi = false := by decide

/-- A `Phi` of both reads what its source reads, or `x` at an integer shape for a gone value. -/
theorem phi_rel (H : Hyp T f g) (R : FRel T f g frS frT) (i : Nat) {z : ID}
    (hzf : inF f z = true) (hzg : inF g z = true) {r : Option (ID × Val)}
    (h : phiStepL mdL (Ctx.makeL T f) frS i z = .ok r) :
    phiStepL mdL (Ctx.makeL T g) frT i z = .ok r := by
  obtain ⟨u, hu⟩ := inF_some hzf
  obtain ⟨w, hw⟩ := inF_some hzg
  obtain ⟨hid, -, htype, hcase⟩ := valOK_some H hu hw
  unfold phiStepL at h ⊢
  rw [makeL_f] at h ⊢
  rw [hu] at h
  rw [hw]
  dsimp only at h ⊢
  rcases hcase with ⟨hop, -, -, hargs⟩ | ⟨hnp, -, hrw⟩
  · rw [hop]
    by_cases hphi : u.op = .Phi
    · simp only [hphi, beq_self_eq_true, ite_true] at h ⊢
      obtain ⟨-, hspec⟩ := argsOK_spec hargs
      cases ha : u.args[i]? with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h
        obtain ⟨b, hb, hc⟩ := hspec i a ha
        rw [hb]
        dsimp only at h ⊢
        cases hs : (frS.regs[a]?).join with
        | none => rw [hs] at h; cases h
        | some s =>
          rw [hs] at h
          cases h
          rcases hc with ⟨rfl, h1, h2⟩ | ⟨h1, h2, h3⟩
          · rw [R.agree b h1 h2, hs, tys_eq H hu hw htype]
          · have hs' : frS.regs[a]? = some (some s) := by
              cases h' : frS.regs[a]? with
              | none => rw [h'] at hs; cases hs
              | some o => rw [h'] at hs; simp at hs; rw [hs]
            obtain ⟨t, ht, hn⟩ := R.narrow a b h1 h2 (by simp) s hs'
            rw [ht, tys_eq H hu hw htype]
            unfold regPos at h3
            rw [hphi, regOps_phi, stOps_phi] at h3
            simp only [Bool.false_or, Bool.false_and, beq_self_eq_true, Bool.true_and] at h3
            obtain ⟨w', hw'⟩ := tys_int H (hid ▸ h3)
            simp only [Option.join_some, hw', Option.getD_some]
            rw [retype_narrow (md := mdL) rfl w' hn]
    · have h1 : (u.op == .Phi) = false := by simpa using hphi
      simp only [h1, Bool.false_eq_true, ite_false] at h ⊢
      exact h
  · have h1 : (u.op == .Phi) = false := by simpa using hnp
    have h2 : (w.op == .Phi) = false := by simpa using rw_not_phi hrw
    simp only [h1, h2, Bool.false_eq_true, ite_false] at h ⊢
    exact h

/-- `g`'s block collects the `Phi`s `f`'s does. -/
theorem phis_rel (H : Hyp T f g) (R : FRel T f g frS frT) {fb gb : Block} (i : Nat)
    (hvals : gb.values.toList.filter (inF f) = fb.values.toList.filter (inF g))
    (hfin : ∀ x ∈ fb.values.toList, inF f x = true)
    (hall : ∀ x ∈ gb.values.toList, (g.value? x).isSome = true) {ps : List (ID × Val)}
    (hS : fb.values.toList.filterMapM (phiStepL mdL (Ctx.makeL T f) frS i) = .ok ps) :
    gb.values.toList.filterMapM (phiStepL mdL (Ctx.makeL T g) frT i) = .ok ps := by
  rw [filterMapM_filterF (p := inF g) fun z hz hzg => ?_] at hS
  · rw [filterMapM_filterF (p := inF f) fun z hz hzf => ?_, hvals]
    · refine filterMapM_imp (fun z hz r hr => ?_) hS
      obtain ⟨hz1, hz2⟩ := List.mem_filter.1 hz
      exact phi_rel H R i (hfin z hz1) hz2 hr
    · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hall z hz)
      obtain ⟨hop, -, -⟩ := valOK_fresh H (inF_none hzf) hw
      unfold phiStepL
      rw [makeL_f, hw]
      simp [hop]
  · have hv : gone f g z = true := by simp [gone, hfin z hz, hzg]
    obtain ⟨u, -, -, hu, -, -, hop, -⟩ := gone_of H hv
    unfold phiStepL
    rw [makeL_f, hu]
    simp [hop]

theorem FRelW.setPhis (H : Hyp T f g) :
    ∀ (ps : List (ID × Val)) {frS frT : Frame}, FRelW T f g W frS frT →
      (∀ p ∈ ps, ∃ u, f.value? p.1 = some u ∧ u.op = .Phi ∧
        ∃ y, p.2 = mdL.retype ((Ctx.makeL T f).tys[p.1]?.getD .other) y) →
      FRelW T f g W { frS with regs := setPhis ps frS.regs }
        { frT with regs := setPhis ps frT.regs }
  | [], _, _, R, _ => by
    obtain ⟨hfr, hag, hs, ht, hpr, hbo, hna⟩ := R
    exact ⟨by rw [hfr], hag, hs, ht, hpr, hbo, hna⟩
  | (id, x) :: ps, _, _, R, hps => by
    obtain ⟨u, hu, hphi, y, hy⟩ := hps (id, x) List.mem_cons_self
    simp only at hu hy
    obtain ⟨w, hw⟩ : ∃ w, g.value? id = some w := by
      cases hg : g.value? id with
      | some w => exact ⟨w, rfl⟩
      | none =>
        have hg' : inF g id = false := by simp [inF, hg]
        have hv : gone f g id = true := by simp [gone, inF_of hu, hg']
        obtain ⟨u', -, -, hu', -, -, hop, -⟩ := gone_of H hv
        rw [hu] at hu'; cases hu'
        rw [hphi] at hop; cases hop
    have R1 := R.set (W' := W) hu hw (y := x)
      (fun s k hk => by rw [hphi, prodSig_phi] at hk; cases hk)
      (fun hty => by
        rw [hy, hty]
        exact boolV_retype rfl y)
      (fun v hv hvW => by
        refine ⟨hvW, fun hb => ?_⟩
        obtain ⟨-, x', ux, -, -, -, -, -, hbx, -, -, -, hux, hnp⟩ := gone_of H hv
        rw [hb] at hbx; cases hbx
        rw [hu] at hux; cases hux
        exact hnp hphi)
    exact FRelW.setPhis H ps R1 fun p hp => hps p (List.mem_cons_of_mem _ hp)

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
        ((Ctx.makeL T g).sched[b]?).join = some oT ∧
        oT.toList.filter (inF f) = oS.toList.filter (inF g) ∧ (∀ x ∈ oS.toList, inF f x = true) ∧
        (∀ x ∈ oT.toList, (g.value? x).isSome = true) ∧ freshBefore f g [] oT.toList = true ∧
        winOK f g (goneL f g) [] oS.toList = true := by
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
          obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hs
          refine .inr ⟨oS, oT, by simp [hsf], by simp [hsg], h1, fun x hx => ?_, fun x hx => ?_,
            h4, h5⟩
          · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
            simpa using h2 i (by simpa using hi)
          · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
            simpa using h3 i (by simpa using hi)

/-- The facts `blkOK` gives of a block of `f`. -/
theorem blk_of (H : Hyp T f g) {b : ID} {fb : Block} (hfb : f.block? b = some fb) :
    ∃ gb, g.block? b = some gb ∧
      { gb with values := fb.values, pos := fb.pos, likely := fb.likely } = fb ∧
      gb.values.toList.filter (inF f) = fb.values.toList.filter (inF g) ∧
      (∀ x ∈ fb.values.toList, inF f x = true) ∧
      (∀ x ∈ gb.values.toList, (g.value? x).isSome = true) ∧
      ∀ c ∈ fb.controls, inF f c = true ∧ inF g c = true := by
  have h := H.blk b
  unfold blkOK at h
  rw [hfb] at h
  cases hgb : g.block? b with
  | none => rw [hgb] at h; cases h
  | some gb =>
    rw [hgb] at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, -⟩ := h
    refine ⟨gb, rfl, h1, h2, fun x hx => ?_, fun x hx => ?_, fun c hc => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
      simpa using h3 i (by simpa using hi)
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
      simpa using h4 i (by simpa using hi)
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hc
      exact h5 i hi

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
  obtain ⟨gb, hgb, hshape, hvals, hfin, hall, hctl⟩ := blk_of H hfb
  rw [hgb]
  dsimp only
  have hid : gb.id = fb.id := by rw [← hshape]
  rw [enterBlockL_eq, enterBlockL_eq, hid]
  cases hps : fb.values.toList.filterMapM (phiStepL mdL (Ctx.makeL T f) frS i) with
  | panic e m => exact absurd hps filterMapM_phiL_not_panic
  | stuck msg => exact True.intro
  | ok ps =>
  rw [phis_rel H R i hvals hfin hall hps]
  dsimp only [Res.bind]
  have hps' : ∀ p ∈ ps, ∃ u, f.value? p.1 = some u ∧ u.op = .Phi ∧
      ∃ y, p.2 = mdL.retype ((Ctx.makeL T f).tys[p.1]?.getD .other) y := by
    intro p hp
    obtain ⟨-, h2, -⟩ := filterMapM_phiL hps
    obtain ⟨h1, v, -, y, hv, hphi, -, -, hy⟩ := phiStepL_some (h2 p hp)
    rw [makeL_f] at hv
    exact ⟨v, h1 ▸ hv, hphi, y, by rw [hy, h1]⟩
  have R0 := FRelW.setPhis H ps R hps'
  rcases sched_rel H fb.id with ⟨h1, h2⟩ | ⟨oS, oT, h1, h2, hfil, hfS, hallT, hfb', hwin⟩
  · rw [h1, h2]; exact True.intro
  rw [h1, h2]
  dsimp only [Res.ofOption, Res.bind]
  obtain ⟨hok, hpan⟩ := evalAll_sim H (env := env) oS.toList oT.toList [] [] _ _ R0
    (fun c hc => absurd hc List.not_mem_nil) hfb' hallT hfS hfil hwin
  cases hev : evalAllL mdL env (Ctx.makeL T f) { frS with regs := setPhis ps frS.regs } oS.toList with
  | panic e m => rw [hpan e m hev]; exact rfl
  | stuck msg => exact True.intro
  | ok frS' =>
  obtain ⟨frT', hT, R'⟩ := hok frS' hev
  rw [hT]
  dsimp only
  rw [stepTermL_rel hshape fun c hc => R'.agree c (hctl c hc).1 (hctl c hc).2]
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
  refine ⟨rfl, fun x hx hxg => ?_, ?_, by simp, fun x u hu s k _ y hy => ?_,
    fun x y _ hy => ?_, fun v x _ _ _ s hs => ?_⟩
  · obtain ⟨u, hu⟩ := inF_some hx
    obtain ⟨w, hw⟩ := inF_some hxg
    have h1 := lt_of_value? hu
    have h2 := lt_of_value? hw
    simp [entryFrame, makeL_f, h1, h2]
  · simp [entryFrame, makeL_f]
  · simp [entryFrame, makeL_f, Array.getElem?_replicate] at hy
  · simp [entryFrame, makeL_f, Array.getElem?_replicate] at hy
  · simp [entryFrame, makeL_f, Array.getElem?_replicate] at hs

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
