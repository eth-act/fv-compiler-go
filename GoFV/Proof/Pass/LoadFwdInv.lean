import GoFV.Proof.Pass.LoadFwdDrop
import GoFV.Proof.Pass.NilSeeds
import GoFV.Proof.AtomSimEnter

/-!
# The forwarding layer's source invariant (issue #69)

A `Zero` or zero `Store` into the block a size-specialised malloc call just returned
(`generic.rules:1352`/`:1357`/`:1362`) changes no byte under `Env.AllocZero`. The forwarding
layer's simulation (`LoadFwd.fwd_refines`) keeps the source invariant `fwdInv`:

* `P` (`ConstReg`): the register of an argument-less term node (a constant such as `Const64`,
  `ConstBool`) is `poison` or its value;
* `Q` (`FreshQ`): the register of a fresh malloc call (`RewriteCheck.freshCall`) is `poison` or a
  tuple whose first component points to a heap block that is all zero in its memory component;
* `E`: `Env.AllocZero`.

A fresh call's evaluation gives such a tuple (`fresh_eval`): its size and `needzero` arguments
are the registers of a positive `Const64` and of `ConstBool [1]`, retyped at the ABI's `uintptr`
and `bool` (`AllocReq`), so the contract returns a pointer to an all-zero heap block
(`Env.AllocZero.atAct`), and `encodeResults` only writes the outgoing-arguments area.
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.CSE GoFV.Proof.CSE.Mem GoFV.Proof.Pass.Rewrite

section
variable {tabs : Tables} {f : Func}

/-- The register of an argument-less term node of `f` is `poison` or its value. -/
def ConstReg (tabs : Tables) (f : Func) (a : ID) (y : Val) : Prop :=
  ∀ v, f.value? a = some v → termOp v.op = true → v.args.size = 0 →
    y = .poison ∨ y = (GoFV.Proof.Rules.opVal tabs v.op (tabs.ty v.type) v.auxInt v.aux []).retype
      (tabs.ty v.type)

/-- The arguments a register file holds for an argument list. -/
private theorem argVals_rv {fr : Frame} : ∀ {l : List ID} {vs : List Val},
    l.mapM (fun a => (fr.regs[a]?).join) = some vs → vs = l.map (rv fr)
  | [], vs, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | a :: l, vs, h => by
    rw [List.mapM_cons] at h
    cases ha : (fr.regs[a]?).join with
    | none => simp [ha] at h
    | some x =>
      cases hl : l.mapM (fun a => (fr.regs[a]?).join) with
      | none => simp [ha, hl] at h
      | some xs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rw [argVals_rv hl, List.map_cons]
        simp [rv, ha]

/-- What a `StaticLECall` that returns gives: the contract's call on the arguments retyped at
the ABI's parameters, without `poison`, on the memory argument, and the results retyped at the
ABI's results before the memory `encodeResults` gives. -/
private theorem callOp_static {env : Env} {ctx : Ctx} {v : Value} {argv : List Val} {r : Val}
    (hop : v.op = .StaticLECall) (h : callOp env ctx v argv = .ok r) :
    ∃ name c m rs m' ps m'' addrs, v.aux.bind ctx.tabs.callee? = some name ∧
      (env.atAct ctx.act).extern name = some c ∧ argv.getLast? = some (.mem m) ∧
      (retypeResults ctx.tabs ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter
        (!·.out)) argv.dropLast).any Val.hasPoison = false ∧
      c (retypeResults ctx.tabs ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter
        (!·.out)) argv.dropLast) none (m.poisonBelow (.outargs ctx.act) (callFrame ctx.tabs v.aux
        ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter (!·.out)))) =
          .returned rs m' ∧
      encodeResults ctx.tabs ctx.act ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter
        (·.out)) (retypeResults ctx.tabs ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter
        (·.out)) rs) m' = some (ps, m'') ∧
      r = .tuple (retypeResults ctx.tabs
        ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter (·.out)) rs ++
          [.mem m'', addrs]) := by
  unfold callOp at h
  simp only [callTarget, hop, nilClosure_none] at h
  have hb : (Op.StaticLECall == Op.StaticCall || Op.StaticLECall == Op.ClosureCall ||
      Op.StaticLECall == Op.InterCall) = false := by decide
  simp only [Res.ofOption, bind, Res.bind, pure, hb, Bool.false_eq_true, ite_false,
    Option.map_none, Option.getD_none, Bool.or_false] at h
  split at h
  · next m hm =>
    split at h
    · cases h
    next hpz =>
    split at h
    · cases h
    cases hname : v.aux.bind ctx.tabs.callee? with
    | none => rw [hname] at h; cases h
    | some name =>
    rw [hname] at h
    simp only at h
    cases hc : (env.atAct ctx.act).extern name with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      simp only at h
      split at h
      · next rs m' hret =>
        split at h
        · next pm he =>
          cases h
          split at he
          · rename_i a heq
            injection he with he'
            subst he'
            exact ⟨name, c, m, rs, m', a.1, a.2, _, rfl, hc, hm, by simpa using hpz, hret, heq, rfl⟩
          · cases he
        all_goals cases h
      · cases h
      · cases h
  · cases h

/-- `Mem.write` keeps the other blocks. -/
theorem write_find_ne {m m' : Mem} {q : Ptr} {bs : Array Byte} (hw : m.write q bs = some m')
    {b : Blk} (hb : q.blk ≠ b) : m'.find? b = m.find? b := by
  unfold Mem.write at hw
  split at hw
  · cases hw; rfl
  cases ha : m.find? q.blk with
  | none => rw [ha] at hw; cases hw
  | some a =>
    rw [ha] at hw
    simp only [Option.bind_eq_bind, Option.bind_some] at hw
    split at hw
    · cases hw
      rw [find?_set, if_neg hb]
    · cases hw

/-- `encodeResults` keeps the blocks other than the outgoing-arguments area. -/
theorem encodeResults_find {tabs : Tables} {act : Nat} {b : Blk} (hb : b ≠ .outargs act) :
    ∀ {ps : List ABIParam} {rs : List Val} {m : Mem} {res : List Val × Mem},
      encodeResults tabs act ps rs m = some res → res.2.find? b = m.find? b
  | [], [], m, res, h => by simp only [encodeResults, Option.some.injEq] at h; subst h; rfl
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [encodeResults] at h
  | p :: ps, r :: rs, m, res, h => by
    unfold encodeResults at h
    dsimp only at h
    split at h
    · cases hwr : m.write ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (encode (tabs.ty p.type) r) with
      | none => rw [hwr] at h; cases h
      | some m1 =>
        rw [hwr] at h
        rw [encodeResults_find hb h, write_find_ne hwr (Ne.symm hb)]
    · cases he : encodeResults tabs act ps rs m with
      | none => rw [he] at h; cases h
      | some r' =>
        rw [he] at h
        cases h
        exact encodeResults_find (res := r') hb he

private theorem retype_i64 (x : BitVec 64) : (Val.int .w64 x).retype (.int .w64) = .int .w64 x := by
  show (if (Width.w64).bits ≤ (Width.w64).bits then Val.int .w64 (x.setWidth 64) else .poison) = _
  rw [if_pos (Nat.le_refl _), BitVec.setWidth_eq]

private theorem retype_bool (b : Bool) : (Val.bool b).retype .bool = .bool b := rfl

/-- A `Const64` term of the 64-bit integer shape denotes its auxint. -/
private theorem const64_reg {s : Value} (hop : s.op = .Const64) (hty : tabs.ty s.type = .int .w64)
    (y : Val) (h : y = .poison ∨ y = (GoFV.Proof.Rules.opVal tabs s.op (tabs.ty s.type) s.auxInt
      s.aux []).retype (tabs.ty s.type)) :
    y = .poison ∨ y = .int .w64 (BitVec.ofInt 64 s.auxInt.toInt) := by
  rcases h with h | h
  · exact .inl h
  · right
    rw [h, GoFV.Proof.Rules.opVal_pure (by rw [hop]; rfl), hop, hty]
    rw [show evalPure .Const64 (.int .w64) s.auxInt s.aux [] = Conv.const .w64 s.auxInt from rfl]
    exact retype_i64 _

/-- A `ConstBool [1]` term of the boolean shape denotes `true`. -/
private theorem constBool_reg {z : Value} (hop : z.op = .ConstBool) (hai : z.auxInt = 1)
    (hty : tabs.ty z.type = .bool) (y : Val) (h : y = .poison ∨ y = (GoFV.Proof.Rules.opVal tabs
      z.op (tabs.ty z.type) z.auxInt z.aux []).retype (tabs.ty z.type)) :
    y = .poison ∨ y = .bool true := by
  rcases h with h | h
  · exact .inl h
  · right
    rw [h, GoFV.Proof.Rules.opVal_pure (by rw [hop]; rfl), hop, hai, hty]
    rfl

/-- **A fresh malloc call's register** (`freshCall`): under `Env.AllocZero`, its evaluation is a
tuple whose first component points to a heap block that is all zero in its memory, or `poison`. -/
theorem fresh_eval {env : Env} (hA : env.AllocZero) {fr : Frame} {c : ID} {cv : Value}
    (hfc : freshCall tabs f c = true) (hcv : f.value? c = some cv) (hid : cv.id = c)
    (hP : ∀ a, ConstReg tabs f a (rv fr a)) {y : Val}
    (hev : evalValue env (Ctx.make tabs f) fr cv = .ok y) : FreshReg y := by
  unfold freshCall at hfc
  rw [hcv] at hfc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hfc
  obtain ⟨hmc, hfc⟩ := hfc
  obtain ⟨⟨⟨⟨⟨hnew, hsz4⟩, hty⟩, hout1⟩, hins⟩, hargs⟩ := hfc
  -- the call's fields (`mallocCall`)
  have hmc' := hmc
  unfold NilCheck.mallocCall at hmc'
  rw [hcv] at hmc'
  simp only [Bool.and_eq_true, beq_iff_eq] at hmc'
  obtain ⟨⟨⟨hop, hname⟩, -⟩, hout⟩ := hmc'
  obtain ⟨e0, ts, hts⟩ : ∃ e0 ts, tabs.ty cv.type = .tuple (.ptr e0 :: .mem :: ts) := by
    split at hty
    · exact ⟨_, _, by assumption⟩
    · cases hty
  -- the arguments
  obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := fr) (v := cv)
    (by rw [hev]; nofun)
  rw [evalValue_of_argVals hvs] at hev
  have htys : (Ctx.make tabs f).tys[cv.id]?.getD .other = .tuple (.ptr e0 :: .mem :: ts) := by
    rw [hid, tys_of_value hcv]; simpa using hts
  rw [htys] at hev
  obtain ⟨r, hr, rfl⟩ := bind_ok hev
  have hco : evalOp env (Ctx.make tabs f) fr cv vs (.tuple (.ptr e0 :: .mem :: ts)) =
      callOp env (Ctx.make tabs f) cv vs := by simp only [evalOp, hop]
  rw [hco] at hr
  obtain ⟨name, c', m, rs, m', ps, m'', addrs, hn, hc, hlast, hnp, hret, henc, rfl⟩ :=
    callOp_static hop hr
  have hn' : cv.aux.bind tabs.callee? = some name := hn
  rw [hn'] at hname hnew
  simp only [Option.map_some, Option.getD_some] at hname
  have hnew' : name ≠ "runtime.newobject" := fun h => hnew (by rw [h])
  have hvs' := argVals_rv hvs
  obtain ⟨a0, a1, a2, a3, hl⟩ : ∃ a0 a1 a2 a3, cv.args.toList = [a0, a1, a2, a3] := by
    have hlen : cv.args.toList.length = 4 := by simpa using hsz4
    generalize cv.args.toList = L at hlen ⊢
    match L, hlen with
    | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩
  rw [hl] at hvs'
  subst hvs'
  simp only [List.map_cons, List.map_nil] at hlast hnp hret
  have h0 : cv.args[0]! = a0 := by
    rw [getElem!_pos cv.args 0 (by omega), ← Array.getElem_toList]; simp [hl]
  have h2 : cv.args[2]! = a2 := by
    rw [getElem!_pos cv.args 2 (by omega), ← Array.getElem_toList]; simp [hl]
  rw [h0, h2] at hargs
  -- the size and `needzero` registers
  cases hs : f.value? a0 with
  | none => rw [hs] at hargs; cases hargs
  | some s =>
  cases hz : f.value? a2 with
  | none => rw [hs, hz] at hargs; cases hargs
  | some z =>
  rw [hs, hz] at hargs
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hargs
  obtain ⟨⟨⟨⟨⟨⟨⟨hsop, hsa⟩, hspos⟩, hsty⟩, hzop⟩, hza⟩, hzai⟩, hzty⟩ := hargs
  have hsty' : tabs.ty s.type = .int .w64 := by
    revert hsty; cases tabs.ty s.type <;> simp
    rename_i w; cases w <;> simp
  have hzty' : tabs.ty z.type = .bool := by
    revert hzty; cases tabs.ty z.type <;> simp
  have hr0 := const64_reg hsop hsty' _ (hP a0 s hs (by rw [hsop]; rfl) hsa)
  have hr2 := constBool_reg hzop hzai hzty' _ (hP a2 z hz (by rw [hzop]; rfl) hza)
  -- the ABI's parameters
  obtain ⟨i0, i1, i2, hins', hi0, hi2⟩ : ∃ i0 i1 i2,
      ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out)) = [i0, i1, i2] ∧
        tabs.ty i0.type = .int .w64 ∧ tabs.ty i2.type = .bool := by
    split at hins
    · next heq =>
      generalize hL : ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out)) = L
        at heq
      match L, heq with
      | [i0, i1, i2], heq =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at heq
        exact ⟨i0, i1, i2, rfl, heq.1, heq.2.2.1⟩
      | [], heq | [_], heq | [_, _], heq | _ :: _ :: _ :: _ :: _, heq => simp at heq
    · cases hins
  have hctx : (Ctx.make tabs f).tabs = tabs := rfl
  rw [hctx, hins'] at hnp hret
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
  simp only [List.map_cons, List.map_nil, List.dropLast_cons₂, List.dropLast_singleton,
    retypeResults, hi0, hi2] at hnp hret
  -- the contract's request (`AllocReq`)
  rcases hr0 with hr0 | hr0
  · rw [hr0, AtomSim.retype_poison] at hnp; simp [Val.hasPoison] at hnp
  rcases hr2 with hr2 | hr2
  · rw [hr2, AtomSim.retype_poison] at hnp; simp [Val.hasPoison] at hnp
  rw [hr0, hr2, retype_i64, retype_bool] at hret
  have hreq : AllocReq name [.int .w64 (BitVec.ofInt 64 s.auxInt.toInt),
      (rv fr a1).retype (tabs.ty i1.type), .bool true] (m.poisonBelow (.outargs (Ctx.make tabs f).act) (callFrame tabs cv.aux [i0, i1, i2])) := by
    simp only [AllocReq, hnew', ite_false]
    refine ⟨_, _, _, rfl, ?_⟩
    show 0 < (BitVec.ofInt 64 s.auxInt.toBitVec.toInt).toInt
    rw [BitVec.ofInt_toInt]
    exact hspos
  have hret' : c' [.int .w64 (BitVec.ofInt 64 s.auxInt.toInt), (rv fr a1).retype (tabs.ty i1.type),
      .bool true] none (m.poisonBelow (.outargs (Ctx.make tabs f).act) (callFrame tabs cv.aux [i0, i1, i2])) = .returned rs m' := hret
  obtain ⟨p, k, hhead, hk, hzero⟩ := (hA.atAct _) name c' hname hc _ _ _ _ _ hret' hreq
  -- the result: one register-shaped pointer
  obtain ⟨o, hos⟩ : ∃ o, ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out)) = [o] := by
    generalize ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out)) = L at hout1
    match L, hout1 with
    | [o], _ => exact ⟨o, rfl⟩
  rw [hctx, hos] at henc
  rw [hos] at hout
  simp only [hctx, hos]
  obtain ⟨rest, hrest⟩ := Nil.retypeResults_head (tabs := tabs) (outs := [o]) hhead hout
  rw [hrest] at henc ⊢
  have hrest0 : rest = [] := by
    cases rest with
    | nil => rfl
    | cons x xs =>
      exfalso
      unfold encodeResults at henc
      split at henc <;> simp [encodeResults] at henc
  subst hrest0
  have hz'' : m''.BlockZero p.blk := by
    intro a ha
    have := encodeResults_find (b := p.blk) (by rw [hk]; nofun) henc
    rw [this] at ha
    exact hzero a ha
  simp only [List.cons_append, List.nil_append, Val.retype, Val.retypePre]
  split
  · rename_i vs' hvs''
    cases hr : Val.retypePre ts [addrs] with
    | none => rw [hr] at hvs''; cases hvs''
    | some l =>
      rw [hr] at hvs''
      cases hvs''
      exact .inr ⟨p, k, m'', l, rfl, hk, hz''⟩
  · exact .inl rfl

/-- Setting the `Phi`s keeps the registers of fresh malloc calls. -/
theorem fresh_phis {fr : Frame} {bb : Block} {i : Nat} {ps : List (ID × Val)}
    (hps : bb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps) {c : ID}
    (hc : freshCall tabs f c = true) : rv { fr with regs := setPhis ps fr.regs } c = rv fr c := by
  have hnm : c ∉ ps.map Prod.fst := by
    intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    obtain ⟨-, h2, -⟩ := filterMapM_phi hps
    obtain ⟨-, v, -, -, hv, hph, -⟩ := phiStep_some (h2 p hp)
    obtain ⟨cv, hcv, hop⟩ := freshCall_value hc
    change f.value? p.1 = some v at hv
    rw [hcv] at hv
    cases hv
    rw [hop] at hph
    cases hph
  unfold rv
  rw [setPhis_not_mem ps fr.regs c hnm]

/-- **The forwarding layer's source invariant** (issue #69): constants' registers hold their
values (`ConstReg`), fresh malloc calls' registers their zeroed blocks (`FreshQ`), under
`Env.AllocZero`. -/
def fwdInv (tabs : Tables) (f : Func) : SrcInv tabs f where
  P _ a y := ConstReg tabs f a y
  L _ _ := True
  Q _ ρ := FreshQ tabs f ρ
  E env := env.AllocZero
  start := ⟨trivial, fun _ _ _ _ _ => .inl rfl⟩
  qstart _ _ := .inl rfl
  poisonAtom _ _ _ _ _ _ _ := .inl rfl
  qpois _ ρ ρ' hQ h c hc := by
    rcases h c with h | h <;> rw [h]
    · exact hQ c hc
    · exact .inl rfl
  edge _ _ _ fr _ _ _ _ hinv hq _ _ _ _ _ _ := by
    refine ⟨trivial, hinv, ?_, ?_⟩
    · intro _ _ _ _ v hv hph _ _ v' hv' ht _
      rw [hv] at hv'; cases hv'; rw [hph] at ht; cases ht
    · intro _ _ _ hps c hc
      rw [fresh_phis hps hc]
      exact hq c hc
  term _ _ _ x _ v hv _ ρ _ v' hv' _ hsz := by
    rw [hv] at hv'
    cases hv'
    right
    rw [List.eq_nil_of_length_eq_zero (by simpa using hsz : v.args.toList.length = 0)]
    rfl
  atom _ _ _ _ _ v hv ht _ _ v' hv' ht' _ := by
    rw [hv] at hv'; cases hv'; rw [ht] at ht'; cases ht'
  qstep _ _ _ x _ v hv hid _ _ hE fr y he hinv hq c hc := by
    rw [rv_set]
    split
    · next h =>
      obtain ⟨rfl, -⟩ := h
      exact fresh_eval hE hc hv hid hinv he
    · exact hq c hc

end

end GoFV.Proof.Pass.LoadFwd
