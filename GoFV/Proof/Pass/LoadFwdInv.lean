import GoFV.Proof.Pass.LoadFwdDrop
import GoFV.Proof.Pass.LoadFwdMoveSrc
import GoFV.Proof.Pass.NilSeeds
import GoFV.Proof.AtomSimEnter
import GoFV.Proof.RoImage

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
(`FreshQ`), and, for an `f` that passes `WBCheck.memTyOK`, the read-only symbols `ro` in every
memory a register holds. -/
def FwdQ (tabs : Tables) (ro : List (String × Alloc)) (f : Func) (ρ : ID → Val) : Prop :=
  FreshQ tabs f ρ ∧ (WBCheck.memTyOK tabs f = true → ∀ a, MemInv.MemsOK (RoMem ro) (ρ a))

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

/-- **The forwarding layer's source invariant** (issue #69): constants' and `Addr`s' registers
hold their values (`ConstReg`), fresh malloc calls' registers their zeroed blocks and memories the
read-only symbols `ro` (`FwdQ`), under `Env.AllocZero` and `Env.KeepsRo` from an initial memory
with the symbols. -/
def fwdInv (tabs : Tables) (ro : List (String × Alloc)) (f : Func)
    (hro : fwdRoOK tabs ro f = true) : SrcInv tabs f where
  P _ a y := ConstReg tabs f a y
  L _ _ := True
  Q _ ρ := FwdQ tabs ro f ρ
  E env m := env.AllocZero ∧ env.KeepsRo ∧ RoMem ro m
  start := ⟨trivial, fun _ _ _ _ _ => .inl rfl⟩
  qstart := ⟨fun _ _ => .inl rfl, fun _ _ => MemInv.memsOK_poison⟩
  poisonAtom _ _ _ _ _ _ _ := .inl rfl
  qpois _ ρ ρ' hQ h := by
    refine ⟨fun c hc => ?_, fun hm a => ?_⟩
    · rcases h c with h | h <;> rw [h]
      · exact hQ.1 c hc
      · exact .inl rfl
    · rcases h a with h | h <;> rw [h]
      · exact hQ.2 hm a
      · exact MemInv.memsOK_poison
  edge _ _ _ fr _ _ _ _ hinv hq _ _ _ _ _ _ := by
    refine ⟨trivial, hinv, ?_, ?_⟩
    · intro _ _ _ _ v hv hph _ _ v' hv' ht _
      rw [hv] at hv'; cases hv'; rw [hph] at ht; cases ht
    · intro _ ps _ hps
      refine ⟨fun c hc => ?_, fun hm => memsOK_rv (MemInv.setPhis_mems ps fr.regs
        (fun p hp => ?_) fun a z hz => ?_)⟩
      · rw [fresh_phis hps hc]; exact hq.1 c hc
      · obtain ⟨-, hsome, -⟩ := filterMapM_phi hps
        obtain ⟨-, v, a, y, -, -, -, hy, hp2⟩ := phiStep_some (hsome p hp)
        rw [hp2]
        have := hq.2 hm a
        rw [rv_of hy] at this
        exact this.retype _
      · have := hq.2 hm a
        rwa [rv_of hz] at this
  term _ _ _ x _ v hv _ ρ _ v' hv' _ hsz := by
    rw [hv] at hv'
    cases hv'
    right
    rcases hsz with hsz | hop
    · rw [List.eq_nil_of_length_eq_zero (by simpa using hsz : v.args.toList.length = 0)]
      rfl
    · simp only [hop, GoFV.Proof.Rules.opVal_addr]
  atom _ _ _ _ _ v hv ht _ _ v' hv' ht' _ := by
    rw [hv] at hv'; cases hv'; rw [ht] at ht'; cases ht'
  qstep _ _ hb hbb x hx v hv hid _ _ fr hE y he hinv hq := by
    refine ⟨fun c hc => ?_, fun hm a => ?_⟩
    · rw [rv_set]
      split
      · next h =>
        obtain ⟨rfl, -⟩ := h
        exact fresh_eval hE.1 hc hv hid hro hinv hq.2 he
      · exact hq.1 c hc
    · rw [rv_set]
      split
      · exact ro_step hE.2.1 hm hb hbb hx hv hid hE.2.2 (hq.2 hm) he
      · exact hq.2 hm a

end

end GoFV.Proof.Pass.LoadFwd
