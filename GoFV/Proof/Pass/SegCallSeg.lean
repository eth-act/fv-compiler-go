import GoFV.Proof.Pass.SegSound

/-!
# Segments: the call segments (issue #151)

`generic.rules:1638` and `:1730` replace `x = SelectN [0] c` of a call
`c = StaticLECall/StaticCall {runtime.memclrNoHeapPointers} p n m` (resp.
`{runtime.memmove} d s n m`), the size `n` a constant term of value `[n]` (`constSize`: e.g.
`Mul64 (StringLen (ConstString {s})) (Const64 [1])`), that `GoFV.Opt.MemCall.simpleCall` accepts by
`x = Zero [n] p m` (resp. `Move [n] d s m`); `callSeg?` checks this, the call is dropped
(`D = [c]`) and no value is fresh (`N = []`).

`callSeg_sound` discharges the segment's obligation `SegSound` (in environments with the runtime
model's memory contracts, `Env.MemOps`):

* the call never panics (`callOp_memclr_not_panic`, `callOp_memmove_not_panic`), and `SelectN` is
  no root;
* in a source frame where the call is available (`CSE.Mem.Avail`, it is a root of `f`), its
  arguments have registers: the pointers are pointers (`Proof.Typed` at a pointer shape leaves a
  pointer or `poison`, and a `poison` pointer makes the contract stuck: `callOp_memclr_ptr`,
  `callOp_memmove_ptr`), the size is its constant term's value (`termConst_reg`: each node of an
  available term evaluates from its arguments' registers); so the call's memory `Mc`
  refines the plain write `M'` (`callOp_memclr`, `callOp_memmove`), which the target's
  `Zero`/`Move` computes from the same registers; the source's `SelectN [0]` of the call's tuple
  (retyped at the call's and at `x`'s type) is `Mc` or `poison`, refined by the target's `M'`
  retyped at the same type (`selectN_refines`).

Non-vacuity: `callSeg_witness` (`callSeg?` accepts a concrete `memclrNoHeapPointers` call) and
`callSeg_witness_str` (a `memclrNoHeapPointers` call whose size is the length of a string
constant times 1).
-/

namespace GoFV.Proof.Seg

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Opt.MemCall
open GoFV.Proof.CSE.Mem (Avail)
open GoFV.Proof.AtomSim (Reg rv evalValue_of_regs regs_of_ok regs_of_panic rv_of)

/-! ## The checks -/

/-- What `callSeg?` checks: `fv` is `SelectN [0] c` of a call `c`, either a
`memclrNoHeapPointers(p, n)` call with `gv = Zero [n] p m` or a `memmove(d, s, n)` call with
`gv = Move [n] d s m`; the dropped values are `[c]`, no value is fresh. -/
private theorem callSeg_spec {tabs : Tables} {f g : Func} {fv gv : Value} {D N : List ID}
    (h : callSeg? tabs f g fv gv = some (D, N)) :
    ∃ c cv, D = [c] ∧ N = [] ∧ fv.op = .SelectN ∧ fv.args.toList = [c] ∧ fv.auxInt = 0 ∧
      f.value? c = some cv ∧
      ((∃ p n m, cv.args.toList = [p, n, m] ∧ simpleCall tabs cv 2 = true ∧
          calleeIs tabs cv "runtime.memclrNoHeapPointers" = true ∧ gv.op = .Zero ∧
          gv.args = #[p, m] ∧ constSize tabs f n gv.auxInt = true ∧ ptrArgB tabs f p = true) ∨
       (∃ d s n m, cv.args.toList = [d, s, n, m] ∧ simpleCall tabs cv 3 = true ∧
          calleeIs tabs cv "runtime.memmove" = true ∧ gv.op = .Move ∧
          gv.args = #[d, s, m] ∧ constSize tabs f n gv.auxInt = true ∧
          ptrArgB tabs f d = true ∧ ptrArgB tabs f s = true)) := by
  unfold callSeg? at h
  split at h
  next c hop hargs =>
    split at h
    next cv hcv =>
      split at h
      next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        split at h
        next p n m hl =>
          split at h
          next hk =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hk
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hk
            exact ⟨c, cv, rfl, rfl, hop, hargs, hc.1, hcv,
              .inl ⟨p, n, m, hl, h1, h2, h3, h4, h5, h6⟩⟩
          next => cases h
        next d s n m hl =>
          split at h
          next hk =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hk
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hk
            exact ⟨c, cv, rfl, rfl, hop, hargs, hc.1, hcv,
              .inr ⟨d, s, n, m, hl, h1, h2, h3, h4, h5, h6, h7⟩⟩
          next => cases h
        next => cases h
      next => cases h
    next => cases h
  next => cases h

private theorem constSize_spec {tabs : Tables} {f : Func} {n : ID} {k : Int64}
    (h : constSize tabs f n k = true) :
    termConst tabs f 4 n = some (.int .w64 (BitVec.ofInt 64 k.toInt)) := by
  simp only [constSize, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  split at h
  next x hx => rw [hx, beq_iff_eq.1 h]
  next => cases h

/-- **A constant term's register** in a frame where it is available is its value
(`termConst`): each node evaluated from its arguments' registers (`evalValue_term`). -/
private theorem termConst_reg {env : Env} {tabs : Tables} {f : Func} {S : Frame}
    {A : ID → Prop} (hA : Avail env tabs f S A) (hid : ∀ z v, A z → f.value? z = some v → v.id = z) :
    ∀ (k : Nat) (a : ID) (y : Val), A a → termConst tabs f k a = some y →
      S.regs[a]? = some (some y)
  | 0, _, _, _, h => by simp [termConst] at h
  | k + 1, a, y, ha, h => by
    obtain ⟨v, y', hv, hr, hev⟩ := hA.val a ha
    simp only [termConst, hv] at h
    split at h
    next ht =>
      obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 h
      have hnphi : v.op ≠ .Phi := fun e => by rw [e] at ht; exact absurd ht (by decide)
      have hl : ∀ (l : List ID) (cs : List Val), (∀ b ∈ l, A b) →
          l.mapM (termConst tabs f k) = some cs → l.map (rv S) = cs := by
        intro l
        induction l with
        | nil => intro cs _ h; simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; simp [h]
        | cons b l ih =>
          intro cs hb h
          rw [List.mapM_cons] at h
          cases hc : termConst tabs f k b with
          | none => rw [hc] at h; cases h
          | some c =>
            cases hcs' : l.mapM (termConst tabs f k) with
            | none => rw [hc, hcs'] at h; cases h
            | some cs' =>
              rw [hc, hcs'] at h
              cases h
              rw [List.map_cons, rv_of (termConst_reg hA hid k b c (hb b List.mem_cons_self) hc),
                ih cs' (fun x hx => hb x (List.mem_cons_of_mem _ hx)) hcs']
      have hargs := hl _ cs (fun b hb => hA.cl a v ha hv hnphi b (Array.mem_toList_iff.1 hb)) hcs
      have hy' := GoFV.Proof.AtomSim.evalValue_term ht (hev hnphi)
      rw [hid a v ha hv, tys_of_value hv, Option.getD_some, hargs] at hy'
      rw [hr, hy']
      rfl
    next => cases h

private theorem ptrArgB_spec {tabs : Tables} {f : Func} {p : ID} (h : ptrArgB tabs f p = true) :
    ∃ pv o, f.value? p = some pv ∧ tabs.ty pv.type = .ptr o := by
  unfold ptrArgB at h
  rw [Option.any_eq_true] at h
  obtain ⟨pv, hpv, hk⟩ := h
  revert hk
  cases ht : tabs.ty pv.type with
  | ptr o => exact fun _ => ⟨pv, o, hpv, ht⟩
  | _ => intro hk; cases hk

/-! ## Registers -/

/-- A pointer-shaped word: a pointer or `poison`. -/
private def PtrW (a : Val) : Prop := a = .poison ∨ ∃ P, a = .ptr P

/-- A register of a `Typed` frame at a pointer shape is a pointer or `poison`. -/
private theorem ptrW_of_typed {ctx : Ctx} {S : Frame} (hT : Proof.Typed ctx S) {p : ID}
    {o : Option Nat}
    (hty : ctx.tys[p]? = some (.ptr o)) {y : Val} (hy : S.regs[p]? = some (some y)) : PtrW y := by
  have h := hT p y hy
  rw [hty, Option.getD_some] at h
  cases y with
  | poison => exact .inl rfl
  | ptr P => exact .inr ⟨P, rfl⟩
  | int w x => cases w <;> cases h
  | _ => cases h

private theorem ofPieces_ptrW (o : Option Nat) {a : Val} (ha : PtrW a) :
    ofPieces (.ptr o) [a] = a := by
  rcases ha with rfl | ⟨P, rfl⟩
  · rw [ABI.ofPieces_eq_build rfl
      (by show ABI.List.Forall₂ _ _ [(0, _)]; exact .cons rfl .nil)]; rfl
  · exact ofPieces_ptr o P

private theorem decodeArgs_twoW {tabs : Tables} {act : Nat} {m : Mem} {ps : List ABIParam}
    (h : inShapes tabs 2 ps = true) {a : Val} (ha : PtrW a) (x : BitVec 64) :
    decodeArgs tabs act m (ps.filter (!·.out)) [a, .int .w64 x] = some [a, .int .w64 x] := by
  have hl : ps.length = 2 := by simp only [inShapes, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1
  rcases ps with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩ <;> simp at hl
  simp only [inShapes, List.dropLast, List.all, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.all, Bool.and_eq_true, Bool.and_true] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  obtain ⟨h11, h12, o, h13⟩ := inShape_ptr h1
  obtain ⟨h21, h22, h23⟩ := inShape_int h2
  simp only [List.filter, h11, h21, Bool.not_false]
  rw [decodeArgs_reg h12, decodeArgs_reg h22, h13, h23, ofPieces_ptrW o ha, ofPieces_int]
  rfl

private theorem decodeArgs_threeW {tabs : Tables} {act : Nat} {m : Mem} {ps : List ABIParam}
    (h : inShapes tabs 3 ps = true) {a b : Val} (ha : PtrW a) (hb : PtrW b) (x : BitVec 64) :
    decodeArgs tabs act m (ps.filter (!·.out)) [a, b, .int .w64 x] = some [a, b, .int .w64 x] := by
  have hl : ps.length = 3 := by simp only [inShapes, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1
  rcases ps with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, rest⟩⟩⟩⟩ <;> simp at hl
  simp only [inShapes, List.dropLast, List.all, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.all, Bool.and_eq_true, Bool.and_true] at h
  obtain ⟨⟨-, h1, h2⟩, h3⟩ := h
  obtain ⟨h11, h12, o, h13⟩ := inShape_ptr h1
  obtain ⟨h21, h22, o', h23⟩ := inShape_ptr h2
  obtain ⟨h31, h32, h33⟩ := inShape_int h3
  simp only [List.filter, h11, h21, h31, Bool.not_false]
  rw [decodeArgs_reg h12, decodeArgs_reg h22, decodeArgs_reg h32, h13, h23, h33,
    ofPieces_ptrW o ha, ofPieces_ptrW o' hb, ofPieces_int]
  rfl

/-- A returning `memclrNoHeapPointers` call got a pointer, not `poison`. -/
private theorem callOp_memclr_ptr {env : Env} (hE : env.MemOps) {ctx : Ctx} {v : Value} {a : Val}
    {x : BitVec 64} {mm y : Val} (hs : simpleCall ctx.tabs v 2 = true)
    (hn : calleeIs ctx.tabs v "runtime.memclrNoHeapPointers" = true) (ha : PtrW a)
    (hc : callOp env ctx v [a, .int .w64 x, mm] = .ok y) : ∃ P, a = .ptr P := by
  obtain ⟨name, M, args, c, rs, m', r, hname, -, hargs, hx, hr, -, -⟩ :=
    callOp_ok (simpleCall_op hs) hc
  rw [calleeIs_eq hn] at hname; cases hname
  have hA := callOp_args hs (fun ps h => decodeArgs_twoW h ha x) hargs
  subst hA
  obtain rfl := hE.1 c hx
  rcases ha with rfl | ha
  · simp [Runtime.memclr, Runtime.ok?, Runtime.asPtr] at hr
  · exact ha

/-- A returning `memmove` call got pointers, not `poison`. -/
private theorem callOp_memmove_ptr {env : Env} (hE : env.MemOps) {ctx : Ctx} {v : Value} {a b : Val}
    {x : BitVec 64} {mm y : Val} (hs : simpleCall ctx.tabs v 3 = true)
    (hn : calleeIs ctx.tabs v "runtime.memmove" = true) (ha : PtrW a) (hb : PtrW b)
    (hc : callOp env ctx v [a, b, .int .w64 x, mm] = .ok y) : ∃ P Q, a = .ptr P ∧ b = .ptr Q := by
  obtain ⟨name, M, args, c, rs, m', r, hname, -, hargs, hx, hr, -, -⟩ :=
    callOp_ok (simpleCall_op hs) hc
  rw [calleeIs_eq hn] at hname; cases hname
  have hA := callOp_args hs (fun ps h => decodeArgs_threeW h ha hb x) hargs
  subst hA
  obtain rfl := hE.2 c hx
  rcases ha with rfl | ⟨P, rfl⟩ <;> rcases hb with rfl | ⟨Q, rfl⟩
  · simp [Runtime.memmove, Runtime.ok?, Runtime.asPtr] at hr
  · simp [Runtime.memmove, Runtime.ok?, Runtime.asPtr] at hr
  · simp [Runtime.memmove, Runtime.ok?, Runtime.asPtr] at hr
  · exact ⟨P, Q, rfl, rfl⟩

/-! ## Evaluation -/

private theorem evalOp_call {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty}
    (hop : v.op = .StaticLECall ∨ v.op = .StaticCall) :
    evalOp env ctx fr v argv ty = callOp env ctx v argv := by
  rcases hop with hop | hop <;> simp only [evalOp, hop]

private theorem evalOp_selectN {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty}
    (hop : v.op = .SelectN) : evalOp env ctx fr v argv ty = .ok (Tuple.selectN v.auxInt argv) := by
  simp only [evalOp, frameVal, hop]
  rfl

private theorem evalOp_mem {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty}
    (hop : v.op = .Zero ∨ v.op = .Move) : evalOp env ctx fr v argv ty = memRoot ctx v argv := by
  rcases hop with hop | hop <;> simp only [evalOp, hop]

private theorem call_root {f : Func} {c : ID} {cv : Value} (hcv : f.value? c = some cv)
    (hop : cv.op = .StaticLECall ∨ cv.op = .StaticCall) : CSE.rootNode f c = true := by
  unfold CSE.rootNode
  rw [hcv]
  rcases hop with hop | hop <;> rw [Option.map_some, Option.getD_some, hop] <;> decide

private theorem selectN_not_root {f : Func} {x : ID} {fv : Value} (hfv : f.value? x = some fv)
    (hop : fv.op = .SelectN) : CSE.rootNode f x = false := by
  unfold CSE.rootNode
  rw [hfv, Option.map_some, Option.getD_some, hop]
  decide

/-- `SelectN [0]` of a memory call's tuple, retyped at any shape, is refined by a memory the
call's refines. -/
private theorem selectN_refines {Mc M' : Mem} (hR : Mem.Refines Mc M') (t : Ty) :
    Sem.Refines (Tuple.selectN 0 [(Val.tuple [.mem Mc, .agg []]).retype t]) (.mem M') := by
  have hm : ∀ t, Sem.Refines ((Val.mem Mc).retype t) (.mem M') := fun t => by
    cases t <;> first | exact .mem hR | exact .poison _
  cases t with
  | tuple ts =>
    rcases ts with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, ts⟩⟩⟩
    · exact .mem hR
    · exact hm t0
    · exact hm t0
    · exact .poison _
  | _ => exact .poison _

/-! ## The obligation -/

/-- The anchor `x = SelectN [0] c` of `f` with the call `c` that never panics: the segment's
roots never panic. -/
private theorem call_no_panic {env : Env} {tabs : Tables} {f : Func} {x c : ID} {fv cv : Value}
    (hfv : f.value? x = some fv) (hop : fv.op = .SelectN) (hcv : f.value? c = some cv)
    (hcop : cv.op = .StaticLECall ∨ cv.op = .StaticCall)
    (hnp : ∀ argv e m, callOp env (Ctx.make tabs f) cv argv ≠ .panic e m) :
    ∀ s ∈ [c] ++ [x], CSE.rootNode f s = true → ∀ sv fr e m, f.value? s = some sv →
      evalValue env (Ctx.make tabs f) fr sv ≠ .panic e m := by
  intro s hs hr sv fr e mm hsv hpan
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · rw [hcv] at hsv; cases hsv
    rw [evalValue_of_regs (regs_of_panic hpan), evalOp_call hcop] at hpan
    cases hco : callOp env (Ctx.make tabs f) cv (cv.args.toList.map (rv fr)) with
    | panic e' m' => exact hnp _ _ _ hco
    | ok r => rw [hco] at hpan; cases hpan
    | stuck msg => rw [hco] at hpan; cases hpan
  · rw [selectN_not_root hfv hop] at hr; cases hr

/-- The target's anchor: it writes `M'` from `S`, and the source's `SelectN [0]` of the call
(whose memory `Mc` refines `M'`) is refined by it. -/
private theorem anchor_finish {env : Env} {tabs : Tables} {f g : Func} {x c : ID} {fv gv : Value}
    {S : Frame} {A : ID → Prop} (hA : Avail env tabs f S A)
    (hid : ∀ z v, A z → f.value? z = some v → v.id = z) (hsz : g.valueTab.size ≤ S.regs.size)
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) (hgid : gv.id = x)
    (hty : gv.type = fv.type) (hop : fv.op = .SelectN) (hfa : fv.args.toList = [c])
    (hai : fv.auxInt = 0) {Mc M' : Mem} {tc : Ty}
    (hyc : S.regs[c]? = some (some ((Val.tuple [.mem Mc, .agg []]).retype tc)))
    (hR : Mem.Refines Mc M') (hreg : ∀ a ∈ gv.args, Reg S a)
    (hev : evalOp env (Ctx.make tabs g) S gv (gv.args.toList.map (rv S)) (tabs.ty gv.type) =
      .ok (.mem M')) :
    ∃ S', evalAll env (Ctx.make tabs g) S ([] ++ [x]) = .ok S' ∧
      (A x → ∃ y y', S.regs[x]? = some (some y) ∧ S'.regs[x]? = some (some y') ∧
        Sem.Refines y y') := by
  have htg : (Ctx.make tabs g).tys[gv.id]?.getD .other = tabs.ty gv.type := by
    rw [hgid, tys_of_value hgv]; rfl
  have he : evalValue env (Ctx.make tabs g) S gv = .ok ((Val.mem M').retype (tabs.ty gv.type)) := by
    rw [evalValue_of_regs hreg, htg, hev]; rfl
  have hf : (Ctx.make tabs g).f = g := rfl
  refine ⟨{ S with regs := S.regs.set! x (some ((Val.mem M').retype (tabs.ty gv.type))) }, ?_, ?_⟩
  · simp only [List.nil_append, evalAll, hf, hgv, he]
  · intro hAx
    obtain ⟨fv', y, hfv', hy, hev'⟩ := hA.val x hAx
    rw [hfv] at hfv'; cases hfv'
    have hev' := hev' (by rw [hop]; intro h; cases h)
    have hfid := hid x fv hAx hfv
    rw [evalValue_of_regs (regs_of_ok hev'), hfa, evalOp_selectN hop, hfid, tys_of_value hfv,
      Option.getD_some, hai] at hev'
    simp only [List.map_cons, List.map_nil, rv_of hyc] at hev'
    refine ⟨y, (Val.mem M').retype (tabs.ty gv.type), hy, ?_, ?_⟩
    · simp only [Array.set!_eq_setIfInBounds]
      exact Array.getElem?_setIfInBounds_self_of_lt
        (Nat.lt_of_lt_of_le (lt_of_value? hgv) hsz)
    · cases hev'
      rw [hty]
      exact retype_mono _ (selectN_refines hR tc)

/-- The `memclrNoHeapPointers` segment (`generic.rules:1638`). -/
private theorem memclr_sound {env : Env} (hE : env.MemOps) {tabs : Tables} {f g : Func}
    {x c p n m : ID}
    {fv gv cv : Value} (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (hgid : gv.id = x) (hty : gv.type = fv.type) (hop : fv.op = .SelectN)
    (hfa : fv.args.toList = [c]) (hai : fv.auxInt = 0) (hcv : f.value? c = some cv)
    (hca : cv.args.toList = [p, n, m]) (hs : simpleCall tabs cv 2 = true)
    (hn : calleeIs tabs cv "runtime.memclrNoHeapPointers" = true) (hgop : gv.op = .Zero)
    (hga : gv.args = #[p, m]) (hcs : constSize tabs f n gv.auxInt = true)
    (hp : ptrArgB tabs f p = true) {Q : Mem → Prop} : SegSound Q env tabs f g x [c] [] := by
  have hcop := simpleCall_op hs
  refine ⟨call_no_panic hfv hop hcv hcop fun argv e mm =>
    callOp_memclr_not_panic (ctx := Ctx.make tabs f) hE hs hn argv e mm, ?_⟩
  intro S A hA hT _ hid hsz hroots
  have hAc : A c := hroots c (by simp) (call_root hcv hcop)
  have hnphi : cv.op ≠ .Phi := by rcases hcop with h | h <;> rw [h] <;> intro h' <;> cases h'
  have hmem : ∀ a ∈ [p, n, m], A a := fun a ha =>
    hA.cl c cv hAc hcv hnphi a (by rw [Array.mem_def, hca]; exact ha)
  obtain ⟨yp, hyp⟩ := hA.reg (hmem p (by simp))
  obtain ⟨yn, hyn⟩ := hA.reg (hmem n (by simp))
  obtain ⟨ym, hym⟩ := hA.reg (hmem m (by simp))
  -- the size is its constant term's value
  have hyn' : yn = .int .w64 (BitVec.ofInt 64 gv.auxInt.toInt) :=
    Option.some.inj (Option.some.inj
      (hyn.symm.trans (termConst_reg hA hid 4 n _ (hmem n (by simp)) (constSize_spec hcs))))
  subst hyn'
  -- the pointer is a pointer or `poison`
  obtain ⟨pv, o, hpv, hpt⟩ := ptrArgB_spec hp
  have hpw : PtrW yp := ptrW_of_typed hT (by rw [tys_of_value hpv, hpt]) hyp
  -- the call
  obtain ⟨yc, hyc⟩ := hA.reg hAc
  have hevc := hA.eval hAc hcv hnphi hyc
  rw [evalValue_of_regs (regs_of_ok hevc), evalOp_call hcop, hca] at hevc
  simp only [List.map_cons, List.map_nil, rv_of hyp, rv_of hyn, rv_of hym] at hevc
  cases hco : callOp env (Ctx.make tabs f) cv
      [yp, .int .w64 (BitVec.ofInt 64 gv.auxInt.toInt), ym] with
  | panic e mm => rw [hco] at hevc; cases hevc
  | stuck msg => rw [hco] at hevc; cases hevc
  | ok r =>
    rw [hco] at hevc; cases hevc
    obtain ⟨P, rfl⟩ := callOp_memclr_ptr (ctx := Ctx.make tabs f) hE hs hn hpw hco
    obtain ⟨M, M', Mc, rfl, hw, rfl, hR⟩ := callOp_memclr (ctx := Ctx.make tabs f) hE hs hn hco
    rw [const64_toInt] at hw
    refine anchor_finish hA hid hsz hfv hgv hgid hty hop hfa hai hyc hR ?_ ?_
    · rw [hga]; intro a ha
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨_, hyp⟩
      · exact ⟨_, hym⟩
    · rw [hga]
      show evalOp _ _ _ _ [rv S p, rv S m] _ = _
      rw [rv_of hyp, rv_of hym, evalOp_mem (.inl hgop)]
      simp only [memRoot, hgop, hw]
      rfl

/-- The `memmove` segment (`generic.rules:1730`). -/
private theorem memmove_sound {env : Env} (hE : env.MemOps) {tabs : Tables} {f g : Func}
    {x c d s n m : ID} {fv gv cv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hgid : gv.id = x) (hty : gv.type = fv.type)
    (hop : fv.op = .SelectN) (hfa : fv.args.toList = [c]) (hai : fv.auxInt = 0)
    (hcv : f.value? c = some cv) (hca : cv.args.toList = [d, s, n, m])
    (hs : simpleCall tabs cv 3 = true) (hn : calleeIs tabs cv "runtime.memmove" = true)
    (hgop : gv.op = .Move) (hga : gv.args = #[d, s, m])
    (hcs : constSize tabs f n gv.auxInt = true) (hd : ptrArgB tabs f d = true)
    (hsp : ptrArgB tabs f s = true) {Q : Mem → Prop} : SegSound Q env tabs f g x [c] [] := by
  have hcop := simpleCall_op hs
  refine ⟨call_no_panic hfv hop hcv hcop fun argv e mm =>
    callOp_memmove_not_panic (ctx := Ctx.make tabs f) hE hs hn argv e mm, ?_⟩
  intro S A hA hT _ hid hsz hroots
  have hAc : A c := hroots c (by simp) (call_root hcv hcop)
  have hnphi : cv.op ≠ .Phi := by rcases hcop with h | h <;> rw [h] <;> intro h' <;> cases h'
  have hmem : ∀ a ∈ [d, s, n, m], A a := fun a ha =>
    hA.cl c cv hAc hcv hnphi a (by rw [Array.mem_def, hca]; exact ha)
  obtain ⟨yd, hyd⟩ := hA.reg (hmem d (by simp))
  obtain ⟨ys, hys⟩ := hA.reg (hmem s (by simp))
  obtain ⟨yn, hyn⟩ := hA.reg (hmem n (by simp))
  obtain ⟨ym, hym⟩ := hA.reg (hmem m (by simp))
  -- the size is its constant term's value
  have hyn' : yn = .int .w64 (BitVec.ofInt 64 gv.auxInt.toInt) :=
    Option.some.inj (Option.some.inj
      (hyn.symm.trans (termConst_reg hA hid 4 n _ (hmem n (by simp)) (constSize_spec hcs))))
  subst hyn'
  -- the pointers are pointers or `poison`
  obtain ⟨dv, o, hdv, hdt⟩ := ptrArgB_spec hd
  have hdw : PtrW yd := ptrW_of_typed hT (by rw [tys_of_value hdv, hdt]) hyd
  obtain ⟨sv, o', hsv, hst⟩ := ptrArgB_spec hsp
  have hsw : PtrW ys := ptrW_of_typed hT (by rw [tys_of_value hsv, hst]) hys
  -- the call
  obtain ⟨yc, hyc⟩ := hA.reg hAc
  have hevc := hA.eval hAc hcv hnphi hyc
  rw [evalValue_of_regs (regs_of_ok hevc), evalOp_call hcop, hca] at hevc
  simp only [List.map_cons, List.map_nil, rv_of hyd, rv_of hys, rv_of hyn, rv_of hym] at hevc
  cases hco : callOp env (Ctx.make tabs f) cv
      [yd, ys, .int .w64 (BitVec.ofInt 64 gv.auxInt.toInt), ym] with
  | panic e mm => rw [hco] at hevc; cases hevc
  | stuck msg => rw [hco] at hevc; cases hevc
  | ok r =>
    rw [hco] at hevc; cases hevc
    obtain ⟨P, Q, rfl, rfl⟩ := callOp_memmove_ptr (ctx := Ctx.make tabs f) hE hs hn hdw hsw hco
    obtain ⟨M, bs, M', Mc, rfl, hrd, hw, rfl, hR⟩ :=
      callOp_memmove (ctx := Ctx.make tabs f) hE hs hn hco
    rw [const64_toInt] at hrd
    refine anchor_finish hA hid hsz hfv hgv hgid hty hop hfa hai hyc hR ?_ ?_
    · rw [hga]; intro a ha
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨_, hyd⟩
      · exact ⟨_, hys⟩
      · exact ⟨_, hym⟩
    · rw [hga]
      show evalOp _ _ _ _ [rv S d, rv S s, rv S m] _ = _
      rw [rv_of hyd, rv_of hys, rv_of hym, evalOp_mem (.inr hgop)]
      simp only [memRoot, hgop, hrd, hw]
      rfl

/-- **The call segments are sound** (`generic.rules:1638`, `:1730`): in environments with the
runtime model's memory contracts, a segment `callSeg?` accepts at the anchor `x` (redefined in
place with its ID and type, as `segOK` checks) discharges `SegSound`. -/
theorem callSeg_sound {tabs : Tables} {f g : Func} {x : ID} {fv gv : Value} {D N : List ID}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) (hgid : gv.id = x)
    (hty : gv.type = fv.type) (h : callSeg? tabs f g fv gv = some (D, N)) {env : Env}
    (hE : env.MemOps) {Q : Mem → Prop} : SegSound Q env tabs f g x D N := by
  obtain ⟨c, cv, rfl, rfl, hop, hfa, hai, hcv, ⟨p, n, m, hca, hs, hn, hgop, hga, hcs, hp⟩ |
    ⟨d, s, n, m, hca, hs, hn, hgop, hga, hcs, hd, hsp⟩⟩ := callSeg_spec h
  · exact memclr_sound hE hfv hgv hgid hty hop hfa hai hcv hca hs hn hgop hga hcs hp
  · exact memmove_sound hE hfv hgv hgid hty hop hfa hai hcv hca hs hn hgop hga hcs hd hsp

/-! ## Non-vacuity -/

/-- `mcTabs` with the types `int64` (0), `*T` (1) and `mem` (2). -/
private def csTabs : Tables :=
  { mcTabs "runtime.memclrNoHeapPointers" with
    types := #[some { (default : TypeDef) with kind := .INT64, size := some 8 },
      some { (default : TypeDef) with kind := .PTR, size := some 8 },
      some { (default : TypeDef) with kind := .SSA, str := GoStr.ofString "mem" }] }

private def csVal (id : ID) (op : Op) (type : TypeRef) (auxInt : Int64) (aux : Option AuxRef)
    (args : Array ID) : Value :=
  { (default : Value) with id, op, type, auxInt, aux, args, block := 1 }

/-- `v1 = StaticLECall {memclrNoHeapPointers} v2 v3 v4` (`v2 = SP`, `v3 = Const64 [16]`,
`v4 = InitMem`), `v5 = SelectN [0] v1`. -/
private def csF : Func :=
  { (default : Func) with
    valueTab := #[none, some (csVal 1 .StaticLECall 2 0 (some 0) #[2, 3, 4]),
      some (csVal 2 .SP 1 0 none #[]), some (csVal 3 .Const64 0 16 none #[]),
      some (csVal 4 .InitMem 2 0 none #[]), some (csVal 5 .SelectN 2 0 none #[1])] }

/-- `csF` with `v5 = Zero [16] v2 v4`. -/
private def csG : Func :=
  { csF with
    valueTab := #[none, none, some (csVal 2 .SP 1 0 none #[]),
      some (csVal 3 .Const64 0 16 none #[]),
      some (csVal 4 .InitMem 2 0 none #[]), some (csVal 5 .Zero 2 16 none #[2, 4])] }

/-- Non-vacuity of `callSeg_sound`: `callSeg?` accepts `SelectN [0]` of a
`memclrNoHeapPointers(SP, 16)` call becoming `Zero [16] SP mem`, dropping the call. -/
theorem callSeg_witness :
    callSeg? csTabs csF csG (csVal 5 .SelectN 2 0 none #[1]) (csVal 5 .Zero 2 16 none #[2, 4]) =
      some ([1], []) := by
  decide +kernel

example : SegSound (fun _ => True) Env.runtime csTabs csF csG 5 [1] [] :=
  callSeg_sound (fv := csVal 5 .SelectN 2 0 none #[1]) (gv := csVal 5 .Zero 2 16 none #[2, 4])
    rfl rfl rfl rfl callSeg_witness Env.runtime_memOps

/-- The string constant `"0123456789abcdef"`. -/
private def csStr : AuxDef where
  fmt := GoStr.ofString "0123456789abcdef"
  kind := .str (GoStr.ofString "0123456789abcdef") (GoStr.ofString "go:string.0")

/-- `csTabs` with the type `string` (3) and the string constant `csStr` (aux 2). -/
private def csTabsS : Tables :=
  { csTabs with
    types := csTabs.types.push (some { (default : TypeDef) with kind := .STRING, size := some 16 })
    auxes := csTabs.auxes.push (some csStr) }

/-- `csF` with the size `v3 = Mul64 v6 v7` (`v6 = StringLen v8`, `v7 = Const64 [1]`,
`v8 = ConstString {"0123456789abcdef"}`), as `copy`'s size before value rules fold it. -/
private def csFS : Func :=
  { (default : Func) with
    valueTab := #[none, some (csVal 1 .StaticLECall 2 0 (some 0) #[2, 3, 4]),
      some (csVal 2 .SP 1 0 none #[]), some (csVal 3 .Mul64 0 0 none #[6, 7]),
      some (csVal 4 .InitMem 2 0 none #[]), some (csVal 5 .SelectN 2 0 none #[1]),
      some (csVal 6 .StringLen 0 0 none #[8]), some (csVal 7 .Const64 0 1 none #[]),
      some (csVal 8 .ConstString 3 0 (some 2) #[])] }

/-- `csFS` with `v5 = Zero [16] v2 v4`. -/
private def csGS : Func :=
  { csFS with
    valueTab := #[none, none, some (csVal 2 .SP 1 0 none #[]),
      some (csVal 3 .Mul64 0 0 none #[6, 7]),
      some (csVal 4 .InitMem 2 0 none #[]), some (csVal 5 .Zero 2 16 none #[2, 4]),
      some (csVal 6 .StringLen 0 0 none #[8]), some (csVal 7 .Const64 0 1 none #[]),
      some (csVal 8 .ConstString 3 0 (some 2) #[])] }

/-- Non-vacuity of the constant-term size (`termConst`): `callSeg?` accepts `SelectN [0]` of a
`memclrNoHeapPointers(SP, len("0123456789abcdef") * 1)` call becoming `Zero [16] SP mem`. -/
theorem callSeg_witness_str :
    callSeg? csTabsS csFS csGS (csVal 5 .SelectN 2 0 none #[1]) (csVal 5 .Zero 2 16 none #[2, 4]) =
      some ([1], []) := by
  decide +kernel

end GoFV.Proof.Seg
