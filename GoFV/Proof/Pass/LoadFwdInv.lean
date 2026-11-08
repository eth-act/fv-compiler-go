import GoFV.Proof.Pass.LoadFwdDrop
import GoFV.Proof.Pass.LoadFwdMoveSrc
import GoFV.Proof.Pass.NilSeeds
import GoFV.Proof.AtomSimEnter
import GoFV.Proof.RoImage

variable [GoFV.SSA.Sem.Addrs]

/-!
# The forwarding layer's source invariant (issue #69)

A `Zero` or zero `Store` into the block a malloc call just returned
(`generic.rules:1352`/`:1357`/`:1362`) changes no byte under `Env.AllocZero`. The forwarding
layer's simulation (`LoadFwd.fwd_refines`) keeps the source invariant `fwdInv`:

* `P` (`ConstReg`): the register of an argument-less term node (a constant such as `Const64`,
  `ConstBool`) or of an `Addr` is `poison` or its value;
* `Q` (`FwdQ`): the register of a fresh malloc call (`RewriteCheck.freshCall`) is `poison` or a
  tuple whose first component points to a heap block that is all zero in its memory component
  (`FreshQ`), and, if `f` passes `WBCheck.memTyOK`, every memory a register holds has the
  read-only symbols `ro` (`RoMem`);
* `E`: `Env.AllocZero`, `Env.KeepsRo`, and the initial memory has the symbols `ro`.

A fresh call's evaluation gives such a tuple (`fresh_eval`). A size-specialised one
(`fresh_eval_sc`): its size and `needzero` arguments are the registers of a positive `Const64`
and of `ConstBool [1]`, retyped at the ABI's `uintptr` and `bool`. A `newobject`
(`fresh_eval_new`): its type argument is the register of an `Addr` of a symbol of `ro` whose type
descriptor has a positive size (`fwdRoOK`, `newSymOK`), which the call's memory holds (`RoMem`).
Either is the request `AllocReq`, so the contract returns a pointer to an all-zero heap block
(`Env.AllocZero.atAct`), and `encodeResults` only writes the outgoing-arguments area
(`fresh_of_req`).
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.CSE GoFV.Proof.CSE.Mem GoFV.Proof.Pass.Rewrite

section
variable {tabs : Tables} {f : Func}

/-- The register of an argument-less term node or of an `Addr` (whose value does not depend on
its argument) of `f` is `poison` or its value. -/
def ConstReg (tabs : Tables) (f : Func) (a : ID) (y : Val) : Prop :=
  ∀ v, f.value? a = some v → termOp v.op = true → (v.args.size = 0 ∨ v.op = .Addr) →
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
        ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter (!·.out))
        (!env.noSpill name))) =
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

/-- A `StaticLECall` panics only when its contract does: on the arguments retyped at the ABI's
parameters, without `poison`, and the memory argument. -/
private theorem callOp_static_panic {env : Env} {ctx : Ctx} {v : Value} {argv : List Val}
    {e : Panic} {m0 : Mem} (hop : v.op = .StaticLECall) (h : callOp env ctx v argv = .panic e m0) :
    ∃ name c m, v.aux.bind ctx.tabs.callee? = some name ∧
      (env.atAct ctx.act).extern name = some c ∧ argv.getLast? = some (.mem m) ∧
      (retypeResults ctx.tabs ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter
        (!·.out)) argv.dropLast).any Val.hasPoison = false ∧
      c (retypeResults ctx.tabs ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter
        (!·.out)) argv.dropLast) none (m.poisonBelow (.outargs ctx.act) (callFrame ctx.tabs v.aux
        ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter (!·.out))
        (!env.noSpill name))) = .panicked e m0 := by
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
      · split at h
        all_goals (try cases h)
        rename_i heq
        split at heq <;> cases heq
      · next e' m' hp =>
        cases h
        exact ⟨name, c, m, rfl, hc, hm, by simpa using hpz, hp⟩
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

theorem retype_i64 (x : BitVec 64) : (Val.int .w64 x).retype (.int .w64) = .int .w64 x := by
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

/-- **A malloc call's register under a request** (issue #69): a malloc-family `StaticLECall`
(`NilCheck.mallocCall`) of a type `(ptr, mem, …)` with one ABI result, whose contract is asked
for zeroed bytes (`AllocReq` of the arguments it gets, `hreq`), evaluates under `Env.AllocZero`
to a tuple whose first component points to a heap block that is all zero in its memory, or to
`poison`. -/
private theorem fresh_of_req {env : Env} (hA : env.AllocZero) {fr : Frame} {c : ID} {cv : Value}
    (hmc : NilCheck.mallocCall tabs f c = true) (hcv : f.value? c = some cv) (hid : cv.id = c)
    (hty : ∃ e0 ts, tabs.ty cv.type = .tuple (.ptr e0 :: .mem :: ts))
    (hout1 : ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out)).length = 1)
    (hreq : ∀ name m n, cv.aux.bind tabs.callee? = some name →
      (cv.args.toList.map (rv fr)).getLast? = some (.mem m) →
      (retypeResults tabs ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter
        (!·.out)) (cv.args.toList.map (rv fr)).dropLast).any Val.hasPoison = false →
      AllocReq name (retypeResults tabs ((((callABI? tabs cv.aux).map (·.params.toList)).getD
        []).filter (!·.out)) (cv.args.toList.map (rv fr)).dropLast)
        (m.poisonBelow (.outargs (Ctx.make tabs f).act) n))
    {y : Val} (hev : evalValue env (Ctx.make tabs f) fr cv = .ok y) : FreshReg y := by
  have hmc' := hmc
  unfold NilCheck.mallocCall at hmc'
  rw [hcv] at hmc'
  simp only [Bool.and_eq_true, beq_iff_eq] at hmc'
  obtain ⟨⟨⟨hop, hname⟩, -⟩, hout⟩ := hmc'
  obtain ⟨e0, ts, hts⟩ := hty
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
  rw [hn'] at hname
  simp only [Option.map_some, Option.getD_some] at hname
  have hvs' := argVals_rv hvs
  subst hvs'
  have hctx : (Ctx.make tabs f).tabs = tabs := rfl
  rw [hctx] at hnp hret
  -- the contract's request (`AllocReq`)
  obtain ⟨p, k, hhead, hk, hzero⟩ :=
    (hA.atAct _) name c' hname hc _ _ _ _ _ hret (hreq name m _ hn' hlast hnp)
  -- the result: one register-shaped pointer
  obtain ⟨o, hos⟩ : ∃ o,
      ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out)) = [o] := by
    generalize ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out)) = L
      at hout1
    match L, hout1 with
    | [o], _ => exact ⟨o, rfl⟩
  rw [hctx, hos] at henc
  rw [hos] at hout
  simp only [hctx, hos]
  obtain ⟨rest, hrest⟩ : ∃ rest, retypeResults tabs [o] rs = p.word :: rest := by
    match rs, hhead with
    | .ptr p :: rs, rfl =>
      simp only at hout
      unfold NilCheck.ptrShaped at hout
      refine ⟨retypeResults tabs [] rs, ?_⟩
      simp only [retypeResults]
      split at hout
      · next e he => rw [he]; rfl
      · cases hout
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
  change FreshReg (match Option.map (fun x => p.word.retype (.ptr e0) :: x)
      (Option.map (fun x => Val.mem m'' :: x) (Val.retypePre ts [addrs])) with
    | some vs' => Val.tuple vs' | none => .poison)
  rw [Ptr.word_retype_ptr]
  cases Val.retypePre ts [addrs] with
  | none => exact .inl rfl
  | some l => exact .inr ⟨p, k, m'', l, rfl, hk, hz''⟩

/-- **A size-specialised fresh call's register** (`freshSC`): its size and `needzero` arguments
are the registers of a positive `Const64` and of `ConstBool [1]`, the request `AllocReq`. -/
theorem fresh_eval_sc {env : Env} (hA : env.AllocZero) {fr : Frame} {c : ID} {cv : Value}
    (hmc : NilCheck.mallocCall tabs f c = true) (hcv : f.value? c = some cv) (hid : cv.id = c)
    (hsc : freshSC tabs f cv = true) (hP : ∀ a, ConstReg tabs f a (rv fr a)) {y : Val}
    (hev : evalValue env (Ctx.make tabs f) fr cv = .ok y) : FreshReg y := by
  unfold freshSC at hsc
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hsc
  obtain ⟨⟨⟨⟨⟨hnew, hsz4⟩, hty⟩, hout1⟩, hins⟩, hargs⟩ := hsc
  refine fresh_of_req hA hmc hcv hid ?_ hout1 ?_ hev
  · split at hty
    · exact ⟨_, _, by assumption⟩
    · cases hty
  intro name m _ hn _ hnp
  have hnew' : name ≠ "runtime.newobject" := fun h => hnew (by rw [hn, h])
  obtain ⟨a0, a1, a2, a3, hl⟩ : ∃ a0 a1 a2 a3, cv.args.toList = [a0, a1, a2, a3] := by
    have hlen : cv.args.toList.length = 4 := by simpa using hsz4
    generalize cv.args.toList = L at hlen ⊢
    match L, hlen with
    | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩
  have h0 : cv.args[0]! = a0 := by
    rw [getElem!_pos cv.args 0 (by omega), ← Array.getElem_toList]; simp [hl]
  have h2 : cv.args[2]! = a2 := by
    rw [getElem!_pos cv.args 2 (by omega), ← Array.getElem_toList]; simp [hl]
  rw [h0, h2] at hargs
  rw [hl] at hnp ⊢
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
  have hr0 := const64_reg hsop hsty' _ (hP a0 s hs (by rw [hsop]; rfl) (.inl hsa))
  have hr2 := constBool_reg hzop hzai hzty' _ (hP a2 z hz (by rw [hzop]; rfl) (.inl hza))
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
  rw [hins'] at hnp ⊢
  simp only [List.map_cons, List.map_nil, List.dropLast_cons₂, List.dropLast_singleton,
    retypeResults, hi0, hi2] at hnp ⊢
  rcases hr0 with hr0 | hr0
  · rw [hr0, AtomSim.retype_poison] at hnp; simp [Val.hasPoison] at hnp
  rcases hr2 with hr2 | hr2
  · rw [hr2, AtomSim.retype_poison] at hnp; simp [Val.hasPoison] at hnp
  rw [hr0, hr2, retype_i64, retype_bool]
  simp only [AllocReq, hnew', ite_false]
  refine ⟨_, _, _, rfl, ?_⟩
  show 0 < (BitVec.ofInt 64 s.auxInt.toBitVec.toInt).toInt
  rw [BitVec.ofInt_toInt]
  exact hspos

/-- A pointer to the start of a global retyped at any shape is itself or `poison` (a global has
no address). -/
private theorem retype_global (n : String) (t : Ty) :
    (Val.ptr ⟨.global n, 0⟩).retype t = .ptr ⟨.global n, 0⟩ ∨
      (Val.ptr ⟨.global n, 0⟩).retype t = .poison := by
  cases t with
  | int w => cases w <;> first | exact .inl rfl | exact .inr rfl
  | ptr e => exact .inl rfl
  | _ => exact .inr rfl

/-- `Runtime.typeInfo` of a pointer to the start of a global whose bytes `roTypeInfo?` reads. -/
theorem typeInfo_global {M : Mem} {n : String} {a : Alloc} (hf : M.find? (.global n) = some a)
    {s pb : Nat} (h : roTypeInfo? a = some (s, pb)) :
    Runtime.typeInfo M ⟨.global n, 0⟩ = some (s, pb) := by
  unfold roTypeInfo? at h
  split at h
  · rename_i hsz
    split at h
    · rename_i s' pb' h1 h2
      cases h
      have r1 : M.read ⟨.global n, 0⟩ 8 = some (a.data.extract 0 8) := by
        simp [Mem.read, hf, Blk.endsInWindow, Blk.window?] <;> omega
      have r2 : M.read ⟨.global n, 8⟩ 8 = some (a.data.extract 8 16) := by
        simp [Mem.read, hf, Blk.endsInWindow, Blk.window?] <;> omega
      simp only [Runtime.typeInfo, Runtime.readWord, Ptr.add]
      rw [show (0 : BitVec 64) + BitVec.ofNat 64 0 = 0 by decide,
        show (0 : BitVec 64) + BitVec.ofNat 64 8 = 8 by decide, r1, r2]
      simp [h1, h2]
    · cases h
  · cases h

/-- Poisoning the start of a block leaves the bytes of the other blocks. -/
theorem read_poisonBelow_ne {m : Mem} {b : Blk} {p : Ptr} (k n : Nat) (h : p.blk ≠ b) :
    (m.poisonBelow b k).read p n = m.read p n := by
  unfold Mem.poisonBelow
  cases hf : m.find? b with
  | none => rfl
  | some a =>
    simp only [Mem.read, find?_set, ite_eq_right (fun e : b = p.blk => h e.symm)]

/-- `Runtime.typeInfo` reads only the descriptor's block. -/
theorem typeInfo_poisonBelow_ne {m : Mem} {b : Blk} {p : Ptr} (k : Nat) (h : p.blk ≠ b) :
    Runtime.typeInfo (m.poisonBelow b k) p = Runtime.typeInfo m p := by
  simp only [Runtime.typeInfo, Runtime.readWord,
    read_poisonBelow_ne (p := p.add _) k _ (show (p.add _).blk ≠ b from h)]

/-- **A `newobject` fresh call's register** (`freshNew`): its type argument is the register of an
`Addr` of a symbol of `ro` whose type descriptor has a positive size (`newSymOK`), which the
call's memory holds (`RoMem`): the request `AllocReq`. -/
theorem fresh_eval_new {ro : List (String × Alloc)} {env : Env} (hA : env.AllocZero) {fr : Frame}
    {c : ID} {cv : Value} (hmc : NilCheck.mallocCall tabs f c = true)
    (hcv : f.value? c = some cv) (hid : cv.id = c) (hnw : freshNew tabs f cv = true)
    (hsym : newSymOK tabs ro f c = true) (hP : ∀ a, ConstReg tabs f a (rv fr a))
    (hR : ∀ a, MemInv.MemsOK (RoMem ro) (rv fr a)) {y : Val}
    (hev : evalValue env (Ctx.make tabs f) fr cv = .ok y) : FreshReg y := by
  unfold freshNew at hnw
  simp only [Bool.and_eq_true, beq_iff_eq] at hnw
  obtain ⟨⟨⟨⟨⟨hnew, hsz2⟩, hty⟩, hout1⟩, hins⟩, haddr⟩ := hnw
  refine fresh_of_req hA hmc hcv hid ?_ hout1 ?_ hev
  · split at hty
    · exact ⟨_, _, by assumption⟩
    · cases hty
  intro name m n hn hlast hnp
  rw [hn] at hnew
  cases hnew
  obtain ⟨a0, a1, hl⟩ : ∃ a0 a1, cv.args.toList = [a0, a1] := by
    have hlen : cv.args.toList.length = 2 := by simpa using hsz2
    generalize cv.args.toList = L at hlen ⊢
    match L, hlen with
    | [a0, a1], _ => exact ⟨a0, a1, rfl⟩
  have h0 : cv.args[0]! = a0 := by
    rw [getElem!_pos cv.args 0 (by omega), ← Array.getElem_toList]; simp [hl]
  rw [h0] at haddr
  rw [hl] at hlast hnp ⊢
  simp only [List.map_cons, List.map_nil, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.some.injEq] at hlast
  have hRm : RoMem ro m := by
    have := hR a1
    rw [hlast] at this
    exact MemInv.MemsOK.mem this
  -- the ABI's parameter
  obtain ⟨i0, hins', e, hi0⟩ : ∃ i0,
      ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out)) = [i0] ∧
        ∃ e, tabs.ty i0.type = .ptr e := by
    split at hins
    · next heq =>
      generalize hL : ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out)) = L
        at heq
      match L, heq with
      | [i0], heq =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at heq
        exact ⟨i0, rfl, _, heq.1⟩
      | [], heq | _ :: _ :: _, heq => simp at heq
    · cases hins
  rw [hins'] at hnp ⊢
  simp only [List.map_cons, List.map_nil, List.dropLast_cons₂, List.dropLast_singleton,
    retypeResults, hi0] at hnp ⊢
  -- the `Addr` and its read-only symbol
  unfold newSymOK at hsym
  rw [hcv] at hsym
  simp only [Option.any_some] at hsym
  rw [h0] at hsym
  cases hav : f.value? a0 with
  | none => rw [hav] at haddr; cases haddr
  | some av =>
  rw [hav] at haddr hsym
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at haddr hsym
  obtain ⟨hop, -⟩ := haddr
  cases hsn : WBCheck.symName? tabs av.aux with
  | none => rw [hsn] at hsym; cases hsym
  | some nm =>
  rw [hsn] at hsym
  simp only [Option.any_some, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hsym
  obtain ⟨e', he', hen, hti⟩ := hsym
  cases hti' : roTypeInfo? e'.2 with
  | none => rw [hti'] at hti; cases hti
  | some sp =>
  rw [hti'] at hti
  simp only [Option.any_some, decide_eq_true_eq] at hti
  have haddrv : GoFV.Proof.Rules.addrVal tabs av.aux = .ptr ⟨.global nm, 0⟩ := by
    unfold WBCheck.symName? at hsn
    unfold GoFV.Proof.Rules.addrVal
    split at hsn
    · rename_i hx; rw [hx]; cases hsn; rfl
    · cases hsn
  -- the type argument: the symbol's pointer
  rcases hP a0 av hav (by rw [hop]; rfl) (.inr hop) with h0' | h0'
  · rw [h0', AtomSim.retype_poison] at hnp; simp [Val.hasPoison] at hnp
  rw [h0', hop, GoFV.Proof.Rules.opVal_addr, haddrv] at hnp ⊢
  rcases retype_global nm (tabs.ty av.type) with h1 | h1
  rotate_left
  · rw [h1, AtomSim.retype_poison] at hnp; simp [Val.hasPoison] at hnp
  rw [h1]
  have hf : m.find? (.global nm) = some e'.2 := hen ▸ (hRm e'.1 e'.2 he').2
  simp only [AllocReq, ite_true]
  refine ⟨_, ⟨.global nm, 0⟩, sp.1, sp.2, rfl, rfl, ?_, by omega⟩
  rw [typeInfo_poisonBelow_ne _ (by nofun)]
  exact typeInfo_global hf hti'

/-- **A fresh malloc call's register** (`freshCall`): under `Env.AllocZero`, and for `newobject`
`fwdRoOK` with the read-only symbols in every register's memory, its evaluation is a tuple whose
first component points to a heap block that is all zero in its memory, or `poison`. -/
theorem fresh_eval {ro : List (String × Alloc)} {env : Env} (hA : env.AllocZero) {fr : Frame}
    {c : ID} {cv : Value} (hfc : freshCall tabs f c = true) (hcv : f.value? c = some cv)
    (hid : cv.id = c) (hro : fwdRoOK tabs ro f = true) (hP : ∀ a, ConstReg tabs f a (rv fr a))
    (hR : WBCheck.memTyOK tabs f = true → ∀ a, MemInv.MemsOK (RoMem ro) (rv fr a)) {y : Val}
    (hev : evalValue env (Ctx.make tabs f) fr cv = .ok y) : FreshReg y := by
  have hfc' := hfc
  unfold freshCall at hfc'
  rw [hcv] at hfc'
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hfc'
  obtain ⟨hmc, hsc | hnw⟩ := hfc'
  · exact fresh_eval_sc hA hmc hcv hid hsc hP hev
  · have hmem : c ∈ (List.range f.valueTab.size).filter fun c =>
        NilCheck.mallocCall tabs f c && (f.value? c).any (freshNew tabs f) := by
      simp only [List.mem_filter, List.mem_range, hmc, hcv, Option.any_some, hnw, Bool.and_self,
        and_true]
      exact lt_of_value? hcv
    unfold fwdRoOK at hro
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hro
    rcases hro with hro | ⟨hmt, hall⟩
    · rw [hro] at hmem; cases hmem
    · exact fresh_eval_new hA hmc hcv hid hnw (hall c hmem) hP (hR hmt) hev

/-! ### `growslice` calls (`generic.rules:2128`) -/

/-- The register `y` of a `growslice` call (`RewriteCheck.growV`) whose length argument holds
`a`: `poison`, or a tuple whose first component is `poison` or a slice of length `a` (retyped at
the 64-bit integer shape, the call's parameter). -/
def GrowRes (a y : Val) : Prop :=
  y = .poison ∨ ∃ s rest, y = .tuple (s :: rest) ∧
    (s = .poison ∨ ∃ p L cap, a.retype (.int .w64) = .int .w64 L ∧ s = .agg [p, .int .w64 L, cap])

/-- The forwarding layer's relation of atoms to their arguments (`SrcInv.R`): a `growslice`
call's register on its arguments' values `argv` (`GrowRes` of the length argument). -/
def growR (tabs : Tables) (v : Value) (argv : List Val) (y : Val) : Prop :=
  growV tabs v = true → GrowRes (argv[1]?.getD .poison) y

/-- A slice of length `L` retyped at a slice shape: `poison` or a slice of length `L`. -/
theorem retype_slice_len (e : Option Nat) (p cap : Val) (L : BitVec 64) :
    (Val.agg [p, .int .w64 L, cap]).retype (.slice e) = .poison ∨
      ∃ p' cap', (Val.agg [p, .int .w64 L, cap]).retype (.slice e) = .agg [p', .int .w64 L, cap'] := by
  have hI : (Val.int .w64 L).retypeI64 = .int .w64 L := by
    show (if (Width.w64).bits ≤ (Width.w64).bits then Val.int .w64 (L.setWidth 64) else .poison) = _
    simp
  have h : (Val.agg [p, .int .w64 L, cap]).retype (.slice e) =
      Val.ofSlice [p.retypePtr, .int .w64 L, cap.retypeI64] := by
    show Val.ofSlice [p.retypePtr, (Val.int .w64 L).retypeI64, cap.retypeI64] = _
    rw [hI]
  rw [h]
  unfold Val.ofSlice
  split
  · exact .inr ⟨_, _, rfl⟩
  · exact .inl rfl

/-- A tuple retyped at a tuple shape: `poison` or its first component retyped first. -/
theorem tuple_retype_cons (t : Ty) (ts : List Ty) (v : Val) (vs : List Val) :
    (Val.tuple (v :: vs)).retype (.tuple (t :: ts)) = .poison ∨
      ∃ l, (Val.tuple (v :: vs)).retype (.tuple (t :: ts)) = .tuple (v.retype t :: l) := by
  have h : (Val.tuple (v :: vs)).retype (.tuple (t :: ts)) =
      (match (Val.retypePre ts vs).map (Val.retype t v :: ·) with
       | some vs' => .tuple vs'
       | none => .poison) := rfl
  rw [h]
  cases Val.retypePre ts vs with
  | none => exact .inl rfl
  | some l => exact .inr ⟨l, rfl⟩

/-- A value retyped at the 64-bit integer shape: `poison`, a 64-bit integer or a pointer. -/
theorem retype_i64_cases (v : Val) :
    v.retype (.int .w64) = .poison ∨ (∃ L, v.retype (.int .w64) = .int .w64 L) ∨
      ∃ q, v.retype (.int .w64) = .ptr q := by
  cases v with
  | int w x =>
    have h : (Val.int w x).retype (.int .w64) =
        if (Width.w64).bits ≤ w.bits then Val.int .w64 (x.setWidth 64) else .poison := rfl
    rw [h]
    split
    · exact .inr (.inl ⟨_, rfl⟩)
    · exact .inl rfl
  | ptr p =>
    have h : (Val.ptr p).retype (.int .w64) = p.word := rfl
    rw [h]
    rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact .inr (.inr ⟨_, rfl⟩)
    · exact .inr (.inl ⟨_, rfl⟩)
    · exact .inl rfl
  | _ => exact .inl rfl

/-- **A `growslice` call's register** (`growV`): under `Env.GrowLen`, its evaluation is a tuple
whose first component is a slice whose length is the length argument, or `poison` (`GrowRes`):
the contract gets the argument retyped at the 64-bit integer shape, not `poison` (the call would
be stuck) and not a pointer (`Env.GrowLen`), and its slice is retyped at the call's result
shapes. -/
theorem grow_eval {env : Env} (hG : env.GrowLen) {fr : Frame} {c : ID} {cv : Value}
    (hcv : f.value? c = some cv) (hid : cv.id = c) (hgv : growV tabs cv = true) {y : Val}
    (hev : evalValue env (Ctx.make tabs f) fr cv = .ok y) :
    GrowRes ((cv.args.toList.map (rv fr))[1]?.getD .poison) y := by
  have hgv' := hgv
  unfold growV at hgv'
  simp only [Bool.and_eq_true, beq_iff_eq] at hgv'
  obtain ⟨⟨⟨⟨⟨hop, hsz⟩, hname⟩, hty⟩, hout⟩, hin⟩ := hgv'
  obtain ⟨e0, ts, hts⟩ : ∃ e0 ts, tabs.ty cv.type = .tuple (.slice e0 :: ts) := by
    split at hty
    · exact ⟨_, _, by assumption⟩
    · cases hty
  obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := fr) (v := cv)
    (by rw [hev]; nofun)
  rw [evalValue_of_argVals hvs] at hev
  have htys : (Ctx.make tabs f).tys[cv.id]?.getD .other = .tuple (.slice e0 :: ts) := by
    rw [hid, tys_of_value hcv]; simpa using hts
  rw [htys] at hev
  obtain ⟨r, hr, rfl⟩ := bind_ok hev
  have hco : evalOp env (Ctx.make tabs f) fr cv vs (.tuple (.slice e0 :: ts)) =
      callOp env (Ctx.make tabs f) cv vs := by simp only [evalOp, hop]
  rw [hco] at hr
  obtain ⟨name, c', m, rs, m', ps, m'', addrs, hn, hc, -, hnp, hret, -, rfl⟩ :=
    callOp_static hop hr
  have hvs' := argVals_rv hvs
  subst hvs'
  have hctx : (Ctx.make tabs f).tabs = tabs := rfl
  rw [hctx] at hnp hret hn
  simp only [hctx]
  rw [hn] at hname
  simp only [Option.any_some, Bool.or_eq_true, beq_iff_eq] at hname
  obtain ⟨a0, a1, a2, a3, a4, a5, hl⟩ :
      ∃ a0 a1 a2 a3 a4 a5, cv.args.toList = [a0, a1, a2, a3, a4, a5] := by
    have hlen : cv.args.toList.length = 6 := by simpa using hsz
    generalize cv.args.toList = L at hlen ⊢
    match L, hlen with
    | [a0, a1, a2, a3, a4, a5], _ => exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩
  -- the ABI's parameters: the second one of the 64-bit integer shape, one slice result
  obtain ⟨i0, i1, irest, hins, hi1⟩ : ∃ i0 i1 irest,
      ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out)) =
        i0 :: i1 :: irest ∧ tabs.ty i1.type = .int .w64 := by
    generalize ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out)) = L
      at hin
    rcases L with _ | ⟨i0, _ | ⟨i1, irest⟩⟩
    · cases hin
    · cases hin
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at hin
      refine ⟨i0, i1, irest, rfl, ?_⟩
      split at hin
      · assumption
      · cases hin
  obtain ⟨o, e1, hos, ho⟩ : ∃ o e1,
      ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out)) = [o] ∧
        tabs.ty o.type = .slice e1 := by
    generalize ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out)) = L
      at hout
    rcases L with _ | ⟨o, _ | ⟨o', L⟩⟩
    · cases hout
    · refine ⟨o, ?_⟩
      simp only at hout
      split at hout
      · exact ⟨_, rfl, by assumption⟩
      · cases hout
    · cases hout
  rw [hins, hl] at hnp hret
  rw [hos, hl]
  simp only [List.map_cons, List.map_nil, List.dropLast_cons_cons, List.dropLast_singleton,
    retypeResults, hi1, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at hnp hret ⊢
  -- the contract's length argument: a 64-bit integer
  obtain ⟨hnptr, hlen⟩ := (hG.atAct _) name c' hname hc _ _ _ _ _ hret
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at hnptr hlen
  rcases retype_i64_cases (rv fr a1) with hA | ⟨L, hA⟩ | ⟨q, hA⟩
  · rw [hA] at hnp; simp [Val.hasPoison, Val.anyPoison] at hnp
  · obtain ⟨p, cap, rest, rfl⟩ := hlen L (by rw [hA])
    simp only [retypeResults, ho, List.cons_append]
    rcases tuple_retype_cons (.slice e0) ts _ (rest ++ [.mem m'', addrs]) with h | ⟨l, h⟩ <;>
      rw [h]
    · exact .inl rfl
    · refine .inr ⟨_, l, rfl, ?_⟩
      rcases retype_slice_len e1 p cap L with h1 | ⟨p', cap', h1⟩ <;> rw [h1]
      · exact .inl (AtomSim.retype_poison _)
      · rcases retype_slice_len e0 p' cap' L with h2 | ⟨p'', cap'', h2⟩ <;> rw [h2]
        · exact .inl rfl
        · exact .inr ⟨p'', L, cap'', hA, rfl⟩
  · exact absurd (by rw [hA]) (hnptr q)

/-! ### Folded `ifaceeq`/`efaceeq` calls (`generic.rules:2279`, `:2287`) -/

theorem wordTy_cases {t : Ty} (h : wordTy t = true) : t = .int .w64 ∨ ∃ e, t = .ptr e := by
  cases t with
  | int w => cases w <;> first | exact .inl rfl | cases h
  | ptr e => exact .inr ⟨e, rfl⟩
  | _ => cases h

/-- A value retyped at a word shape (`wordTy`) keeps a pointer word inside its window. -/
theorem asPtrWord_retype_word_of {t : Ty} (ht : wordTy t = true) {v : Val} {q : Ptr}
    (hq : q.inWindow = true) (h : v.asPtrWord = some q) : (v.retype t).asPtrWord = some q := by
  rcases wordTy_cases ht with rfl | ⟨e, rfl⟩
  · cases v with
    | int w x =>
      cases w
      · cases h
      · cases h
      · cases h
      · rw [retype_i64]; exact h
    | ptr p =>
      simp only [Val.asPtrWord, Option.some.injEq] at h; subst h
      exact Ptr.word_asPtrWord hq
    | _ => cases h
  · refine (Val.asPtrWord_retype_ptr e fun p hp => ?_).trans h
    subst hp; simp only [Val.asPtrWord, Option.some.injEq] at h; subst h; exact hq

/-- A value whose retype at a word shape holds no `poison` is a pointer word. -/
theorem asPtrWord_of_retype_word {t : Ty} (ht : wordTy t = true) {v : Val}
    (h : (v.retype t).hasPoison = false) : ∃ p, v.asPtrWord = some p := by
  rcases wordTy_cases ht with rfl | ⟨e, rfl⟩
  · cases v with
    | int w x => cases w <;> first | exact ⟨_, rfl⟩ | cases h
    | ptr p => exact ⟨p, rfl⟩
    | _ => cases h
  · cases v with
    | int w x => cases w <;> first | exact ⟨_, rfl⟩ | cases h
    | ptr p => exact ⟨p, rfl⟩
    | _ => cases h

/-- A value whose retype at a word shape holds no `poison` keeps its pointer word (a pointer
outside its window would retype to `poison`). -/
theorem asPtrWord_retype_word_np {t : Ty} (ht : wordTy t = true) {v : Val}
    (h : (v.retype t).hasPoison = false) : (v.retype t).asPtrWord = v.asPtrWord := by
  obtain ⟨p, hp⟩ := asPtrWord_of_retype_word ht h
  rw [hp]
  cases hw : p.inWindow
  · exfalso
    cases v with
    | ptr p' =>
      simp only [Val.asPtrWord, Option.some.injEq] at hp; subst hp
      rcases wordTy_cases ht with rfl | ⟨e, rfl⟩
      · have he : (Val.ptr p').retype (.int .w64) = p'.word := rfl
        rw [he, Ptr.word_of_not_inWindow hw] at h; cases h
      · have he : (Val.ptr p').retype (.ptr e) = p'.word := rfl
        rw [he, Ptr.word_of_not_inWindow hw] at h; cases h
    | int w x =>
      cases w
      · cases hp
      · cases hp
      · cases hp
      · simp only [Val.asPtrWord, Option.some.injEq] at hp; subst hp
        rw [Ptr.ofAddr_inWindow] at hw; cases hw
    | _ => cases hp
  · exact asPtrWord_retype_word_of ht hw hp

theorem ifaceTy_cases {t : Ty} (h : ifaceTy t = true) :
    ∃ o0 t0 o1 t1 sz, t = .agg [(o0, t0), (o1, t1)] sz ∧ wordTy t0 = true := by
  unfold ifaceTy at h
  split at h
  · exact ⟨_, _, _, _, _, rfl, h⟩
  · cases h

/-- An aggregate retyped at an interface shape: `poison`, or its two components retyped. -/
theorem retype_iface (o0 o1 sz : Nat) (t0 t1 : Ty) (w : Val) (rest : List Val) :
    (Val.agg (w :: rest)).retype (.agg [(o0, t0), (o1, t1)] sz) = .poison ∨
      ∃ w1 : Val, (Val.agg (w :: rest)).retype (.agg [(o0, t0), (o1, t1)] sz) =
        .agg [w.retype t0, w1.retype t1] := by
  match rest with
  | [] => exact .inl rfl
  | [w1] => exact .inr ⟨w1, rfl⟩
  | _ :: _ :: _ => exact .inl rfl

/-- The `Addr` of a symbol `eqSymName?` names is the start of its global. -/
theorem addrVal_of_eqSymName {ax : AuxRef} {s : String} (h : eqSymName? tabs ax = some s) :
    GoFV.Proof.Rules.addrVal tabs (some ax) = .ptr ⟨.global s, 0⟩ := by
  unfold eqSymName? at h
  simp only [GoFV.Proof.Rules.addrVal, Option.bind_some]
  split at h
  · simp only [Option.some.injEq] at h; subst h; simp_all
  · cases h

private theorem evalPure_itab (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    evalPure .ITab ty ai ax args = Comp.select 0 args := rfl

private theorem evalPure_imake (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    evalPure .IMake ty ai ax args = Comp.make args := rfl

/-- The ops of a descriptor chain (`eqDescW`, `eqDescI`) are term nodes. -/
theorem eqDesc_term {n : Nat} {a : ID} {ax : AuxRef}
    (h : eqDescW tabs f n a = some ax ∨ eqDescI tabs f n a = some ax) :
    ∃ u, f.value? a = some u ∧ termOp u.op = true := by
  cases n with
  | zero => rcases h with h | h <;> simp [eqDescW, eqDescI] at h
  | succ n =>
    cases hu : f.value? a with
    | none => rcases h with h | h <;> simp [eqDescW, eqDescI, hu] at h
    | some u =>
      refine ⟨u, rfl, ?_⟩
      by_cases h1 : u.op = .Addr; · rw [h1]; decide
      by_cases h2 : u.op = .Copy; · rw [h2]; decide
      by_cases h3 : u.op = .ITab; · rw [h3]; decide
      by_cases h4 : u.op = .IMake; · rw [h4]; decide
      rcases h with h | h <;> simp [eqDescW, eqDescI, hu, h1, h2, h3, h4] at h

/-- A word of a descriptor chain (`eqDescW`) of symbol `s`. -/
def DescW (s : String) (y : Val) : Prop := y = .poison ∨ y.asPtrWord = some ⟨.global s, 0⟩

/-- An interface of a descriptor chain (`eqDescI`) of symbol `s`. -/
def DescI (s : String) (y : Val) : Prop :=
  y = .poison ∨ ∃ w rest, y = .agg (w :: rest) ∧ DescW s w

/-- The register `y` of value `a` of `f`: `DescW` if `a` is a word, `DescI` if an interface,
of a descriptor chain whose `Addr` names `s`. -/
def DescReg (tabs : Tables) (f : Func) (a : ID) (y : Val) : Prop :=
  (∀ n ax s, eqDescW tabs f n a = some ax → eqSymName? tabs ax = some s → DescW s y) ∧
  (∀ n ax s, eqDescI tabs f n a = some ax → eqSymName? tabs ax = some s → DescI s y)

theorem descReg_poison (a : ID) : DescReg tabs f a .poison :=
  ⟨fun _ _ _ _ _ => .inl rfl, fun _ _ _ _ _ => .inl rfl⟩

/-- The registers of values that are no term nodes: `DescReg`, vacuously. -/
theorem descReg_atom {a : ID} {u : Value} (hu : f.value? a = some u) (ht : termOp u.op = false)
    (y : Val) : DescReg tabs f a y := by
  refine ⟨fun n ax s h _ => ?_, fun n ax s h _ => ?_⟩ <;>
  · obtain ⟨u', hu', ht'⟩ := eqDesc_term (by first | exact .inl h | exact .inr h)
    rw [hu] at hu'; cases hu'; rw [ht] at ht'; cases ht'

/-- One step of a descriptor chain on registers: a term node of a chain on arguments whose
registers are `DescReg` is. -/
theorem descReg_term {x : ID} {v : Value} (hv : f.value? x = some v) {ρ : ID → Val}
    (hargs : ∀ a ∈ v.args, DescReg tabs f a (ρ a)) :
    DescReg tabs f x ((GoFV.Proof.Rules.opVal tabs v.op (tabs.ty v.type) v.auxInt v.aux
      (v.args.toList.map ρ)).retype (tabs.ty v.type)) := by
  have hmem : ∀ i, i < v.args.size → v.args[i]! ∈ v.args := fun i hi => by
    rw [getElem!_pos v.args i hi]; exact Array.getElem_mem _
  constructor
  · intro n ax s hW hs
    cases n with
    | zero => simp [eqDescW] at hW
    | succ n =>
    simp only [eqDescW, hv] at hW
    have hw : wordTy (tabs.ty v.type) = true := by
      cases h : wordTy (tabs.ty v.type)
      · simp [h] at hW
      · rfl
    simp only [hw, Bool.not_true, Bool.false_eq_true, ite_false] at hW
    by_cases h1 : v.op = .Addr
    · simp only [h1, beq_self_eq_true, ite_true] at hW
      right
      rw [h1, GoFV.Proof.Rules.opVal_addr, hW, addrVal_of_eqSymName hs]
      exact asPtrWord_retype_word_of hw (Ptr.inWindow_zero _) rfl
    simp only [show (v.op == .Addr) = false from beq_eq_false_iff_ne.2 h1, Bool.false_eq_true,
      ite_false] at hW
    by_cases h2 : v.op = .Copy ∧ v.args.size = 1
    · simp only [h2, beq_self_eq_true, Bool.and_self, ite_true] at hW
      have hR := (hargs _ (hmem 0 (by omega))).1 n ax s hW hs
      rw [toList_one h2.2, List.map_cons, List.map_nil, h2.1,
        GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy]
      rcases hR with h | h
      · rw [h]; exact .inl (AtomSim.retype_poison _)
      · exact .inr (asPtrWord_retype_word_of hw (Ptr.inWindow_zero _) h)
    have h2' : (v.op == .Copy && v.args.size == 1) = false := by
      simpa [Bool.and_eq_true, beq_iff_eq] using h2
    simp only [h2', Bool.false_eq_true, ite_false] at hW
    by_cases h3 : v.op = .ITab ∧ v.args.size = 1
    · simp only [h3, beq_self_eq_true, Bool.and_self, ite_true] at hW
      have hR := (hargs _ (hmem 0 (by omega))).2 n ax s hW hs
      rw [toList_one h3.2, List.map_cons, List.map_nil, h3.1,
        GoFV.Proof.Rules.opVal_pure (op := Op.ITab) rfl, evalPure_itab]
      rcases hR with h | ⟨w, rest, h, hw'⟩
      · rw [h]; exact .inl (AtomSim.retype_poison _)
      · rw [h]
        show DescW s (w.retype _)
        rcases hw' with h' | h'
        · rw [h']; exact .inl (AtomSim.retype_poison _)
        · exact .inr (asPtrWord_retype_word_of hw (Ptr.inWindow_zero _) h')
    have h3' : (v.op == .ITab && v.args.size == 1) = false := by
      simpa [Bool.and_eq_true, beq_iff_eq] using h3
    simp only [h3', Bool.false_eq_true, ite_false] at hW
    cases hW
  · intro n ax s hI hs
    cases n with
    | zero => simp [eqDescI] at hI
    | succ n =>
    simp only [eqDescI, hv] at hI
    have hi : ifaceTy (tabs.ty v.type) = true := by
      cases h : ifaceTy (tabs.ty v.type)
      · simp [h] at hI
      · rfl
    simp only [hi, Bool.not_true, Bool.false_eq_true, ite_false] at hI
    obtain ⟨o0, t0, o1, t1, sz, hty, hw0⟩ := ifaceTy_cases hi
    by_cases h1 : v.op = .IMake ∧ v.args.size = 2
    · simp only [h1, beq_self_eq_true, Bool.and_self, ite_true] at hI
      have hR := (hargs _ (hmem 0 (by omega))).1 n ax s hI hs
      rw [toList_two h1.2, List.map_cons, List.map_cons, List.map_nil, h1.1,
        GoFV.Proof.Rules.opVal_pure (op := Op.IMake) rfl, evalPure_imake, hty]
      refine .inr ⟨_, _, rfl, ?_⟩
      rcases hR with h | h
      · rw [h]; exact .inl (AtomSim.retype_poison _)
      · exact .inr (asPtrWord_retype_word_of hw0 (Ptr.inWindow_zero _) h)
    have h1' : (v.op == .IMake && v.args.size == 2) = false := by
      simpa [Bool.and_eq_true, beq_iff_eq] using h1
    simp only [h1', Bool.false_eq_true, ite_false] at hI
    by_cases h2 : v.op = .Copy ∧ v.args.size = 1
    · simp only [h2, beq_self_eq_true, Bool.and_self, ite_true] at hI
      have hR := (hargs _ (hmem 0 (by omega))).2 n ax s hI hs
      rw [toList_one h2.2, List.map_cons, List.map_nil, h2.1,
        GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy, hty]
      rcases hR with h | ⟨w, rest, h, hw'⟩
      · rw [h]; exact .inl (AtomSim.retype_poison _)
      · rw [h]
        rcases retype_iface o0 o1 sz t0 t1 w rest with h' | ⟨w1, h'⟩ <;> rw [h']
        · exact .inl rfl
        · refine .inr ⟨_, _, rfl, ?_⟩
          rcases hw' with h'' | h''
          · rw [h'']; exact .inl (AtomSim.retype_poison _)
          · exact .inr (asPtrWord_retype_word_of hw0 (Ptr.inWindow_zero _) h'')
    have h2' : (v.op == .Copy && v.args.size == 1) = false := by
      simpa [Bool.and_eq_true, beq_iff_eq] using h2
    simp only [h2', Bool.false_eq_true, ite_false] at hI
    cases hI

/-- **A descriptor chain as a term** (`eqDescW`/`eqDescI`, at most `n` deep, its `Addr` naming
`s`): past the fuel `n` its word is the start of `s`'s global (an interface: a pair whose first
component is), whatever the atoms. -/
theorem desc_den {ρ : ID → Val} {s : String} : ∀ (n : Nat) (a : ID) (ax : AuxRef),
    eqSymName? tabs ax = some s →
    (eqDescW tabs f n a = some ax → ∀ k, n ≤ k →
      (den f.value? tabs ρ k a).asPtrWord = some ⟨.global s, 0⟩) ∧
    (eqDescI tabs f n a = some ax → ∀ k, n ≤ k → ∃ w w1,
      den f.value? tabs ρ k a = .agg [w, w1] ∧ w.asPtrWord = some ⟨.global s, 0⟩)
  | 0, a, ax, _ => ⟨fun h => by simp [eqDescW] at h, fun h => by simp [eqDescI] at h⟩
  | n + 1, a, ax, hs => by
    have IH := fun b => desc_den (ρ := ρ) n b ax hs
    constructor
    · intro hW k hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      cases hv : f.value? a with
      | none => simp [eqDescW, hv] at hW
      | some v =>
      simp only [eqDescW, hv] at hW
      have hw : wordTy (tabs.ty v.type) = true := by
        cases h : wordTy (tabs.ty v.type)
        · simp [h] at hW
        · rfl
      simp only [hw, Bool.not_true, Bool.false_eq_true, ite_false] at hW
      by_cases h1 : v.op = .Addr
      · simp only [h1, beq_self_eq_true, ite_true] at hW
        rw [den_succ_term hv (by rw [h1]; decide), h1,
          GoFV.Proof.Rules.opVal_addr, hW, addrVal_of_eqSymName hs]
        exact asPtrWord_retype_word_of hw (Ptr.inWindow_zero _) rfl
      simp only [show (v.op == .Addr) = false from beq_eq_false_iff_ne.2 h1, Bool.false_eq_true,
        ite_false] at hW
      by_cases h2 : v.op = .Copy ∧ v.args.size = 1
      · simp only [h2, beq_self_eq_true, Bool.and_self, ite_true] at hW
        rw [den_succ_term hv (by rw [h2.1]; decide), toList_one h2.2,
          List.map_cons, List.map_nil, h2.1, GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl,
          evalPure_copy]
        exact asPtrWord_retype_word_of hw (Ptr.inWindow_zero _) ((IH _).1 hW k (by omega))
      have h2' : (v.op == .Copy && v.args.size == 1) = false := by
        simpa [Bool.and_eq_true, beq_iff_eq] using h2
      simp only [h2', Bool.false_eq_true, ite_false] at hW
      by_cases h3 : v.op = .ITab ∧ v.args.size = 1
      · simp only [h3, beq_self_eq_true, Bool.and_self, ite_true] at hW
        rw [den_succ_term hv (by rw [h3.1]; decide), toList_one h3.2,
          List.map_cons, List.map_nil, h3.1, GoFV.Proof.Rules.opVal_pure (op := Op.ITab) rfl,
          evalPure_itab]
        obtain ⟨w, w1, h, hw'⟩ := (IH _).2 hW k (by omega)
        rw [h]
        exact asPtrWord_retype_word_of hw (Ptr.inWindow_zero _) hw'
      have h3' : (v.op == .ITab && v.args.size == 1) = false := by
        simpa [Bool.and_eq_true, beq_iff_eq] using h3
      simp only [h3', Bool.false_eq_true, ite_false] at hW
      cases hW
    · intro hI k hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      cases hv : f.value? a with
      | none => simp [eqDescI, hv] at hI
      | some v =>
      simp only [eqDescI, hv] at hI
      have hi : ifaceTy (tabs.ty v.type) = true := by
        cases h : ifaceTy (tabs.ty v.type)
        · simp [h] at hI
        · rfl
      simp only [hi, Bool.not_true, Bool.false_eq_true, ite_false] at hI
      obtain ⟨o0, t0, o1, t1, sz, hty, hw0⟩ := ifaceTy_cases hi
      by_cases h1 : v.op = .IMake ∧ v.args.size = 2
      · simp only [h1, beq_self_eq_true, Bool.and_self, ite_true] at hI
        rw [den_succ_term hv (by rw [h1.1]; decide), toList_two h1.2, List.map_cons,
          List.map_cons, List.map_nil, h1.1, GoFV.Proof.Rules.opVal_pure (op := Op.IMake) rfl,
          evalPure_imake, hty]
        exact ⟨_, _, rfl, asPtrWord_retype_word_of hw0 (Ptr.inWindow_zero _) ((IH _).1 hI k (by omega))⟩
      have h1' : (v.op == .IMake && v.args.size == 2) = false := by
        simpa [Bool.and_eq_true, beq_iff_eq] using h1
      simp only [h1', Bool.false_eq_true, ite_false] at hI
      by_cases h2 : v.op = .Copy ∧ v.args.size = 1
      · simp only [h2, beq_self_eq_true, Bool.and_self, ite_true] at hI
        rw [den_succ_term hv (by rw [h2.1]; decide), toList_one h2.2, List.map_cons,
          List.map_nil, h2.1, GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy, hty]
        obtain ⟨w, w1, h, hw'⟩ := (IH _).2 hI k (by omega)
        rw [h]
        exact ⟨_, _, rfl, asPtrWord_retype_word_of hw0 (Ptr.inWindow_zero _) hw'⟩
      have h2' : (v.op == .Copy && v.args.size == 1) = false := by
        simpa [Bool.and_eq_true, beq_iff_eq] using h2
      simp only [h2', Bool.false_eq_true, ite_false] at hI
      cases hI

theorem tuple_bm_of_matches {t : Ty} (h : (t matches .tuple [.bool, .mem]) = true) :
    t = .tuple [.bool, .mem] := by
  split at h
  · rfl
  · cases h

theorem bool_of_matches {t : Ty} (h : (t matches .bool) = true) : t = .bool := by
  split at h
  · rfl
  · cases h

theorem eqCallSig_spec {cv : Value} (h : eqCallSig tabs cv = true) :
    cv.op = .StaticLECall ∧ cv.args.size = 4 ∧
    (∃ n, cv.aux.bind tabs.callee? = some n ∧ (n = "runtime.ifaceeq" ∨ n = "runtime.efaceeq")) ∧
    tabs.ty cv.type = .tuple [.bool, .mem] ∧
    (∃ o, (((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out) = [o] ∧
      tabs.ty o.type = .bool ∧ o.regs.isEmpty = false) ∧
    (∃ p0 p1 p2, (((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out) =
      [p0, p1, p2] ∧ wordTy (tabs.ty p0.type) = true ∧ wordTy (tabs.ty p1.type) = true ∧
      wordTy (tabs.ty p2.type) = true) := by
  unfold eqCallSig at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hop, hsz⟩, hn⟩, hty⟩, hout⟩, hin⟩ := h
  refine ⟨hop, hsz, ?_, tuple_bm_of_matches hty, ?_, ?_⟩
  · cases hc : cv.aux.bind tabs.callee? with
    | none => rw [hc] at hn; cases hn
    | some n =>
      rw [hc] at hn
      simp only [Option.any_some, Bool.or_eq_true, beq_iff_eq] at hn
      exact ⟨n, rfl, hn⟩
  · generalize ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out)) = L
      at hout ⊢
    rcases L with _ | ⟨o, _ | ⟨o', L⟩⟩
    · cases hout
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hout
      exact ⟨o, rfl, bool_of_matches hout.1, hout.2⟩
    · cases hout
  · generalize ((((callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out)) = L
      at hin ⊢
    rcases L with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, L⟩⟩⟩⟩
    · cases hin
    · cases hin
    · cases hin
    · simp only [Bool.and_eq_true] at hin
      exact ⟨p0, p1, p2, rfl, hin.1.1, hin.1.2, hin.2⟩
    · cases hin

theorem eqCallV_spec {eq : List String × List String} {cv : Value}
    (h : eqCallV tabs eq f cv = true) :
    eqCallSig tabs cv = true ∧ ∃ ax s, eqDescW tabs f 8 cv.args[0]! = some ax ∧
      eqSymName? tabs ax = some s ∧ s ∈ eqList tabs eq cv := by
  unfold eqCallV at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases hd : eqDescW tabs f 8 cv.args[0]! with
  | none => rw [hd] at h2; cases h2
  | some ax =>
    rw [hd] at h2
    cases hs : eqSymName? tabs ax with
    | none => simp [hs] at h2
    | some s =>
      simp only [Option.bind_some, hs, Option.any_some, List.contains_iff_mem] at h2
      exact ⟨ax, s, rfl, hs, h2⟩

theorem eqCallOK_spec {eq : List String × List String} {g : Func} {u w : Value}
    (h : eqCallOK tabs eq f g u w = true) :
    eqCallV tabs eq f u = true ∧ w.op = .MakeResult ∧ w.args.size = 2 ∧
      copyReach tabs f.valueTab f.valueTab.size u.args[3]! w.args[1]! = true ∧
      listedB g w.args[0]! = true ∧
      ∃ q, g.value? w.args[0]! = some q ∧ q.op = .EqPtr ∧ q.args.size = 2 ∧
        tabs.ty q.type = .bool ∧
        copyReach tabs f.valueTab f.valueTab.size u.args[1]! q.args[0]! = true ∧
        copyReach tabs f.valueTab f.valueTab.size u.args[2]! q.args[1]! = true := by
  unfold eqCallOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hv, hop⟩, hsz⟩, hm⟩, hl⟩, hq⟩ := h
  refine ⟨hv, hop, hsz, hm, hl, ?_⟩
  cases hqv : g.value? w.args[0]! with
  | none => rw [hqv] at hq; cases hq
  | some q =>
    rw [hqv] at hq
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hq
    exact ⟨q, rfl, h1, h2, bool_of_matches h3, h4, h5⟩

/-- The list a call's descriptor symbol is in names the call's callee. -/
theorem eqList_mem {eq : List String × List String} {cv : Value} {n s : String}
    (hn : cv.aux.bind tabs.callee? = some n)
    (hn2 : n = "runtime.ifaceeq" ∨ n = "runtime.efaceeq") (hs : s ∈ eqList tabs eq cv) :
    n = "runtime.ifaceeq" ∧ s ∈ eq.1 ∨ n = "runtime.efaceeq" ∧ s ∈ eq.2 := by
  unfold eqList at hs
  rw [hn] at hs
  rcases hn2 with rfl | rfl
  · exact .inl ⟨rfl, by simpa using hs⟩
  · have hne : (some "runtime.efaceeq" == some "runtime.ifaceeq") = false := by decide
    rw [hne] at hs
    exact .inr ⟨rfl, by simpa using hs⟩

/-- The register `y` of a folded call (`eqCallSig`) on its arguments' values `argv`: the tuple of
the pointer equality of its data words, a memory refined by its memory argument, and the result
addresses. -/
def EqRes (argv : List Val) (y : Val) : Prop :=
  ∃ M M' addrs p q, argv[3]? = some (.mem M) ∧ Mem.Refines M' M ∧
    (argv[1]?.getD Val.poison).asPtrWord = some p ∧ (argv[2]?.getD Val.poison).asPtrWord = some q ∧
    y = .tuple [.bool (p.eq q), .mem M', addrs]

/-- The forwarding layer's relation of a folded call (`eqCallSig`) to its arguments (issue #69):
if its descriptor points at the start of a symbol of its list (`eqList`), its register is
`EqRes` (`Sem.Env.IfaceEq`). -/
def eqR (tabs : Tables) (eq : List String × List String) (v : Value) (argv : List Val) (y : Val) :
    Prop :=
  eqCallSig tabs v = true → ∀ s, s ∈ eqList tabs eq v →
    (argv[0]?.getD Val.poison).asPtrWord = some ⟨.global s, 0⟩ → EqRes argv y

/-- **A folded call's register** (`eqCallSig`): under `Env.IfaceEq`, a call whose descriptor
points at the start of a symbol of its list returns the pointer equality of its data words (the
contract gets them retyped at the ABI's word shapes, which keep the words, and not `poison`) and
the memory it was given (its argument with the outgoing-arguments area poisoned, which the
argument refines), and `encodeResults` stores nothing for its register `bool` result. -/
theorem eq_eval {eq : List String × List String} {env : Env} (hI : env.IfaceEq eq) {fr : Frame}
    {c : ID} {cv : Value} (hcv : f.value? c = some cv) (hid : cv.id = c) {y : Val}
    (hev : evalValue env (Ctx.make tabs f) fr cv = .ok y) :
    eqR tabs eq cv (cv.args.toList.map (rv fr)) y := by
  intro hsig s hs hd
  obtain ⟨hop, hsz, ⟨n, hn, hn2⟩, hty, ⟨o, hos, hoty, horeg⟩, ⟨p0, p1, p2, hins, hw0, hw1, hw2⟩⟩ :=
    eqCallSig_spec hsig
  have hn' := eqList_mem hn hn2 hs
  obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := fr) (v := cv)
    (by rw [hev]; nofun)
  rw [evalValue_of_argVals hvs] at hev
  have htys : (Ctx.make tabs f).tys[cv.id]?.getD .other = .tuple [.bool, .mem] := by
    rw [hid, tys_of_value hcv]; simpa using hty
  rw [htys] at hev
  obtain ⟨r, hr, rfl⟩ := bind_ok hev
  have hco : evalOp env (Ctx.make tabs f) fr cv vs (.tuple [.bool, .mem]) =
      callOp env (Ctx.make tabs f) cv vs := by simp only [evalOp, hop]
  rw [hco] at hr
  obtain ⟨name, c', m, rs, m', ps, m'', addrs, hname, hc, hlast, hnp, hret, henc, rfl⟩ :=
    callOp_static hop hr
  have hvs' := argVals_rv hvs
  subst hvs'
  have hctx : (Ctx.make tabs f).tabs = tabs := rfl
  simp only [hctx] at hnp hret hname henc ⊢
  rw [hn] at hname
  cases hname
  obtain ⟨a0, a1, a2, a3, hl⟩ : ∃ a0 a1 a2 a3, cv.args.toList = [a0, a1, a2, a3] := by
    have hlen : cv.args.toList.length = 4 := by simpa using hsz
    generalize cv.args.toList = L at hlen ⊢
    match L, hlen with
    | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩
  rw [hins, hl] at hnp hret
  rw [hl] at hlast hd
  rw [hos] at henc
  simp only [hos, hl]
  simp only [List.map_cons, List.map_nil, List.dropLast_cons_cons, List.dropLast_singleton,
    retypeResults] at hnp hret
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff] at hnp
  obtain ⟨hp0, hp1, hp2⟩ := hnp
  obtain ⟨p, hp⟩ := asPtrWord_of_retype_word hw1 hp1
  obtain ⟨q, hq⟩ := asPtrWord_of_retype_word hw2 hp2
  simp only [List.map_cons, List.map_nil, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.some.injEq] at hlast
  simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.getD_some] at hd
  rw [(hI.atAct (Ctx.make tabs f).act) n c' hc s hn' _ _ _ p q _
    (asPtrWord_retype_word_of hw0 (Ptr.inWindow_zero _) hd)
    (by rw [asPtrWord_retype_word_np hw1 hp1, hp]) (by rw [asPtrWord_retype_word_np hw2 hp2, hq])] at hret
  cases hret
  have hb : PtrOps.eqPtr false [(rv fr a1).retype (tabs.ty p1.type), (rv fr a2).retype (tabs.ty p2.type)] =
      .bool (p.eq q) := by
    first
      | (simp only [PtrOps.eqPtr, asPtrWord_retype_word_np hw1 hp1, asPtrWord_retype_word_np hw2 hp2,
          hp, hq]; done)
      | (simp only [PtrOps.eqPtr, asPtrWord_retype_word_np hw1 hp1, asPtrWord_retype_word_np hw2 hp2,
          hp, hq]
         cases p.eq q <;> rfl)
  rw [hb] at henc ⊢
  simp only [retypeResults, hoty] at henc ⊢
  simp only [encodeResults, horeg, Bool.false_eq_true, ite_false, bind, Option.bind,
    pure, List.append_nil, Option.some.injEq, Prod.mk.injEq] at henc
  obtain ⟨-, rfl⟩ := henc
  exact ⟨m, _, addrs, p, q, by simp [hlast], GoFV.Proof.Seg.poisonBelow_refines _ _ _,
    by simpa using hp, by simpa using hq, rfl⟩

/-- **A folded call does not panic** under `Env.IfaceEq` when its descriptor's register is
`poison` (the call is stuck) or points at the start of a symbol of its list (`DescW`, which
`DescReg` gives the descriptor chain): its contract returns. -/
theorem eq_noPanic {eq : List String × List String} {env : Env} (hI : env.IfaceEq eq)
    {fr : Frame} {cv : Value} (hsig : eqCallSig tabs cv = true) {s : String}
    (hs : s ∈ eqList tabs eq cv) (hd : DescW s (rv fr cv.args[0]!)) (e : Panic) (m0 : Mem) :
    evalValue env (Ctx.make tabs f) fr cv ≠ .panic e m0 := by
  intro hev
  obtain ⟨hop, hsz, ⟨n, hn, hn2⟩, -, -, ⟨p0, p1, p2, hins, hw0, hw1, hw2⟩⟩ := eqCallSig_spec hsig
  have hn' := eqList_mem hn hn2 hs
  obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := fr) (v := cv)
    (by rw [hev]; nofun)
  rw [evalValue_of_argVals hvs] at hev
  have hco : evalOp env (Ctx.make tabs f) fr cv vs ((Ctx.make tabs f).tys[cv.id]?.getD .other) =
      callOp env (Ctx.make tabs f) cv vs := by simp only [evalOp, hop]
  rw [hco] at hev
  have hr : callOp env (Ctx.make tabs f) cv vs = .panic e m0 := by
    cases h : callOp env (Ctx.make tabs f) cv vs <;> rw [h] at hev <;> cases hev <;> rfl
  obtain ⟨name, c', M, hname, hc, -, hnp, hpan⟩ := callOp_static_panic hop hr
  have hvs' := argVals_rv hvs
  subst hvs'
  have hctx : (Ctx.make tabs f).tabs = tabs := rfl
  rw [hctx] at hnp hpan hname
  rw [hn] at hname
  cases hname
  obtain ⟨a0, a1, a2, a3, hl⟩ : ∃ a0 a1 a2 a3, cv.args.toList = [a0, a1, a2, a3] := by
    have hlen : cv.args.toList.length = 4 := by simpa using hsz
    generalize cv.args.toList = L at hlen ⊢
    match L, hlen with
    | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩
  have ha0 : cv.args[0]! = a0 := by
    have : cv.args.toList[0]? = some a0 := by rw [hl]; rfl
    rw [Array.getElem?_toList] at this
    rw [getElem!_pos cv.args 0 (by omega)]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by omega)).symm.trans this)
  rw [ha0] at hd
  rw [hins, hl] at hnp hpan
  simp only [List.map_cons, List.map_nil, List.dropLast_cons_cons, List.dropLast_singleton,
    retypeResults] at hnp hpan
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff] at hnp
  obtain ⟨hp0, hp1, hp2⟩ := hnp
  obtain ⟨p, hp⟩ := asPtrWord_of_retype_word hw1 hp1
  obtain ⟨q, hq⟩ := asPtrWord_of_retype_word hw2 hp2
  have hdw : (rv fr a0).asPtrWord = some ⟨.global s, 0⟩ := by
    rcases hd with h | h
    · rw [h, AtomSim.retype_poison] at hp0; cases hp0
    · exact h
  rw [(hI.atAct (Ctx.make tabs f).act) n c' hc s hn' _ _ _ p q _
    (asPtrWord_retype_word_of hw0 (Ptr.inWindow_zero _) hdw)
    (by rw [asPtrWord_retype_word_np hw1 hp1, hp]) (by rw [asPtrWord_retype_word_np hw2 hp2, hq])] at hpan
  cases hpan

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

/-- The forwarding layer's frame invariant (issue #69): fresh malloc calls' registers
(`FreshQ`), for an `f` that passes `WBCheck.memTyOK` the read-only symbols `ro` in every memory
a register holds, and argument pointers' registers avoiding the frame temporaries (`ArgAv`). -/
def FwdQ (tabs : Tables) (ro : List (String × Alloc)) (f : Func) (ρ : ID → Val) : Prop :=
  FreshQ tabs f ρ ∧ (WBCheck.memTyOK tabs f = true → ∀ a, MemInv.MemsOK (RoMem ro) (ρ a)) ∧
    ArgAv tabs f ρ

private theorem memsOK_rv {P : Mem → Prop} {fr : Frame}
    (h : ∀ (x : Nat) (y : Val), fr.regs[x]? = some (some y) → MemInv.MemsOK P y) (a : ID) :
    MemInv.MemsOK P (rv fr a) := by
  cases hx : fr.regs[a]? with
  | none => unfold rv; rw [hx]; exact MemInv.memsOK_poison
  | some o =>
    cases o with
    | none => unfold rv; rw [hx]; exact MemInv.memsOK_poison
    | some y => rw [rv_of hx]; exact h a y hx

/-- One value's evaluation keeps the read-only symbols in the memories (`MemInv.sinv_step`). -/
private theorem ro_step {ro : List (String × Alloc)} {env : Env} (hK : env.KeepsRo)
    (hm : WBCheck.memTyOK tabs f = true) {b : ID} {bb : Block} (hb : b ∈ f.blocks)
    (hbb : f.block? b = some bb) {x : ID} (hx : x ∈ bb.values) {v : Value}
    (hv : f.value? x = some v) (hid : v.id = x) {fr : Frame} (h0 : RoMem ro fr.mem0)
    (hR : ∀ a, MemInv.MemsOK (RoMem ro) (rv fr a)) {y : Val}
    (he : evalValue env (Ctx.make tabs f) fr v = .ok y) : MemInv.MemsOK (RoMem ro) y := by
  have hxb : x ∈ WBCheck.vals f b := by
    simp only [WBCheck.vals, hbb, Option.map_some, Option.getD_some]; exact hx
  have hok := MemInv.memTyOK_val hm hb hxb hv
  refine MemInv.evalValue_mems (fun a z hz => by have := hR a; rwa [rv_of hz] at this)
    (fun argv ha r hr => ?_) he
  rcases hok with hfree | hop | hit
  · rw [hid]
    exact MemInv.memsOK_of_mems_nil (MemInv.retype_memFree _ (MemInv.tys_memFree hv hfree) r)
  · exact (MemInv.evalOp_mems (roMem_pred ro) (hK.contractsOK ro) h0 hop ha hr).retype _
  · exact (MemInv.memsOK_of_mems_nil (MemInv.evalOp_memFreeOps_mems hit hr)).retype _

/-- Setting the `Phi`s keeps the registers of argument pointers. -/
theorem argPtr_phis {fr : Frame} {bb : Block} {i : Nat} {ps : List (ID × Val)}
    (hps : bb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps) {n : Nat} {c : ID}
    (hc : argPtrB tabs f n c = true) : rv { fr with regs := setPhis ps fr.regs } c = rv fr c := by
  have hnm : c ∉ ps.map Prod.fst := by
    intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    obtain ⟨-, h2, -⟩ := filterMapM_phi hps
    obtain ⟨-, v, -, -, hv, hph, -⟩ := phiStep_some (h2 p hp)
    obtain ⟨cv, hcv, hop⟩ := argPtrB_not_phi hc
    change f.value? p.1 = some v at hv
    rw [hcv] at hv
    cases hv
    exact hop hph
  unfold rv
  rw [setPhis_not_mem ps fr.regs c hnm]

/-- The forwarding layer's relation of atoms to their arguments (`SrcInv.R`): `growslice` calls
(`growR`) and folded `ifaceeq`/`efaceeq` calls (`eqR`). -/
def fwdR (tabs : Tables) (eq : List String × List String) (v : Value) (argv : List Val)
    (y : Val) : Prop :=
  growR tabs v argv y ∧ eqR tabs eq v argv y

/-- **The forwarding layer's source invariant** (issue #69): constants' and `Addr`s' registers
hold their values (`ConstReg`) and descriptor chains' registers their symbol's start
(`DescReg`), fresh malloc calls' registers their zeroed blocks, memories the read-only symbols
`ro` and argument pointers no pointer into a frame temporary (`FwdQ`), under `Env.AllocZero`,
`Env.KeepsRo`, `Env.GrowLen` and `Env.IfaceEq eq` from an initial memory with the symbols and
argument images without such pointers; `growslice` calls' registers slices of their length
argument (`growR`, `grow_eval`), folded calls' registers the equality of their data words
(`eqR`, `eq_eval`). -/
def fwdInv (tabs : Tables) (ro : List (String × Alloc)) (eq : List String × List String)
    (f : Func) (hro : fwdRoOK tabs ro f = true) : SrcInv tabs f where
  P _ a y := ConstReg tabs f a y ∧ DescReg tabs f a y
  L _ _ := True
  Q _ ρ := FwdQ tabs ro f ρ
  E env m im := env.AllocZero ∧ env.KeepsRo ∧ RoMem ro m ∧
    (∀ img ∈ im, GoFV.Proof.DAE.BAv Temp0 img) ∧ env.GrowLen ∧ env.IfaceEq eq
  R := fwdR tabs eq
  start := ⟨trivial, fun a => ⟨fun _ _ _ _ => .inl rfl, descReg_poison a⟩⟩
  qstart := ⟨fun _ _ => .inl rfl, fun _ _ => MemInv.memsOK_poison, argAv_poison tabs f⟩
  poisonAtom _ a _ := ⟨fun _ _ _ _ => .inl rfl, descReg_poison a⟩
  qpois _ ρ ρ' hQ h := by
    refine ⟨fun c hc => ?_, fun hm a => ?_, argAv_pois hQ.2.2 h⟩
    · rcases h c with h | h <;> rw [h]
      · exact hQ.1 c hc
      · exact .inl rfl
    · rcases h a with h | h <;> rw [h]
      · exact hQ.2.1 hm a
      · exact MemInv.memsOK_poison
  edge _ _ _ fr _ _ _ _ hinv hq _ _ _ _ _ _ := by
    refine ⟨trivial, hinv, ?_, ?_⟩
    · intro _ _ _ _ v hv hph _ _
      refine ⟨fun v' hv' ht _ => ?_, descReg_atom hv (by rw [hph]; rfl) _⟩
      rw [hv] at hv'; cases hv'; rw [hph] at ht; cases ht
    · intro _ ps _ hps
      refine ⟨fun c hc => ?_, fun hm => memsOK_rv (MemInv.setPhis_mems ps fr.regs
        (fun p hp => ?_) fun a z hz => ?_), fun n c hc => ?_⟩
      · rw [fresh_phis hps hc]; exact hq.1 c hc
      · obtain ⟨-, hsome, -⟩ := filterMapM_phi hps
        obtain ⟨-, v, a, y, -, -, -, hy, hp2⟩ := phiStep_some (hsome p hp)
        rw [hp2]
        have := hq.2.1 hm a
        rw [rv_of hy] at this
        exact this.retype _
      · have := hq.2.1 hm a
        rwa [rv_of hz] at this
      · rw [argPtr_phis hps hc]; exact hq.2.2 n c hc
  term _ _ _ x _ v hv _ ρ hargs := by
    refine ⟨fun v' hv' _ hsz => ?_, descReg_term hv fun a ha => (hargs a ha).2⟩
    rw [hv] at hv'
    cases hv'
    right
    rcases hsz with hsz | hop
    · rw [List.eq_nil_of_length_eq_zero (by simpa using hsz : v.args.toList.length = 0)]
      rfl
    · simp only [hop, GoFV.Proof.Rules.opVal_addr]
  atom _ _ _ _ _ v hv ht _ y :=
    ⟨fun v' hv' ht' _ => (by rw [hv] at hv'; cases hv'; rw [ht] at ht'; cases ht'),
      descReg_atom hv ht _⟩
  qstep _ _ hb hbb x hx v hv hid _ _ fr hE y he hinv hq := by
    refine ⟨fun c hc => ?_, fun hm a => ?_, argAv_set hE.2.2.2.1 hv he hq.2.2⟩
    · rw [rv_set]
      split
      · next h =>
        obtain ⟨rfl, -⟩ := h
        exact fresh_eval hE.1 hc hv hid hro (fun a => (hinv a).1) hq.2.1 he
      · exact hq.1 c hc
    · rw [rv_set]
      split
      · exact ro_step hE.2.1 hm hb hbb hx hv hid hE.2.2.1 (hq.2.1 hm) he
      · exact hq.2.1 hm a
  rstep _ _ hv hid _ _ _ _ hE _ he :=
    ⟨fun hgv => grow_eval hE.2.2.2.2.1 hv hid hgv he, eq_eval hE.2.2.2.2.2 hv hid he⟩

end

end GoFV.Proof.Pass.LoadFwd
