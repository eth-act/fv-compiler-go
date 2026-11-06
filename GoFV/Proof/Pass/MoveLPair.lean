import GoFV.Proof.Pass.MoveLRel
import GoFV.Proof.Pass.MoveLPairMem

/-!
# `pair`'s cases of `relB`: selectors of pair loads and pair stores evaluate as their sources

A selector `Select_i l` of a pair load `l` evaluates as the load of element `i` (offset `i`
widths up, `evalValueL_selPair`): the pair load addresses its elements by `pairAddr`, the
`symAddr` of each element's offset, and at a two-component tuple shape whose components are the
selectors' shapes its components are the loads at those shapes. A pair store evaluates as the
second of its two adjacent stores (`evalValueL_stPair`): it writes the two elements in order at
the two stores' addresses (`Arm64.storePair`). When the higher store came first
(`evalValueL_stPairRev`), the two writes are disjoint and commute (`write_adj_comm`).
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-! ## Evaluation on given argument registers -/

/-- The registers of `l` hold `L`. -/
def RegsHold (fr : Frame) : List ID → List Val → Prop
  | [], [] => True
  | a :: l, z :: L => fr.regs[a]? = some (some z) ∧ RegsHold fr l L
  | _, _ => False

theorem mapM_regs {fr : Frame} {m : ID → String} :
    ∀ {l : List ID} {L : List Val}, RegsHold fr l L →
      l.mapM (fun a => Res.ofOption (m a) (fr.regs[a]?).join) = .ok L
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | a :: l, z :: L, ⟨h, t⟩ => by
    rw [List.mapM_cons, h, mapM_regs t]
    rfl

/-- A value whose arguments hold `L` evaluates its op on `L`. -/
theorem evalValueL_of_regs {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {L : List Val} (h : RegsHold fr v.args.toList L) :
    evalValueL md env ctx fr v =
      (evalOpL md.faulting env ctx fr v L (ctx.tys[v.id]?.getD .other)).bind
        fun r => .ok (md.retype (ctx.tys[v.id]?.getD .other) r) := by
  unfold evalValueL
  rw [mapM_regs h]
  rfl

theorem res_bind_ok {r : Res Val} {k : Val → Val} {y : Val}
    (h : r.bind (fun x => .ok (k x)) = .ok y) : ∃ x, r = .ok x ∧ y = k x := by
  cases r with
  | ok x => cases h; exact ⟨x, rfl, rfl⟩
  | panic e m => cases h
  | stuck msg => cases h

/-! ## Addresses -/

/-- `symAddr` reads of the context the tables and the activation, of the value its aux and
auxint. -/
theorem symAddr_congr {ctx ctx' : Ctx} {v v' : Value} {a : Val} (htabs : ctx'.tabs = ctx.tabs)
    (hact : ctx'.act = ctx.act) (haux : v'.aux = v.aux) (hai : v'.auxInt = v.auxInt) :
    symAddr ctx' v' a = symAddr ctx v a := by
  unfold symAddr
  rw [htabs, hact, haux, hai]

/-- Whether `symAddr` is defined does not depend on the offset. -/
theorem symAddr_none_auxInt {ctx : Ctx} {v : Value} {a : Val} (k : Int64)
    (h : symAddr ctx v a = none) : symAddr ctx { v with auxInt := k } a = none := by
  unfold symAddr at h ⊢
  dsimp only at h ⊢
  split
  · rename_i n hn
    rw [hn] at h
    dsimp only at h
    split
    · rename_i hk; rw [hk] at h; cases h
    · rename_i hk; rw [hk] at h; cases h
    · rfl
  · rename_i hn
    rw [hn] at h
    dsimp only at h
    unfold Arm64.addr at h ⊢
    cases a <;> simp_all

theorem pairAddr_none {ctx : Ctx} {v : Value} {n : Nat} {a : Val} (h : symAddr ctx v a = none) :
    pairAddr ctx v n a = none := by
  unfold pairAddr; rw [h]; rfl

theorem pairAddr_some {ctx : Ctx} {v : Value} {n : Nat} {a : Val} {p : Ptr}
    (h : symAddr ctx v a = some p) :
    ∃ q, pairAddr ctx v n a = some (p, q) ∧
      symAddr ctx { v with auxInt := v.auxInt + Int64.ofNat n } a = some q := by
  cases hq : symAddr ctx { v with auxInt := v.auxInt + Int64.ofNat n } a with
  | none =>
    have := symAddr_none_auxInt v.auxInt hq
    simp only at this
    rw [h] at this; cases this
  | some q =>
    refine ⟨q, ?_, rfl⟩
    unfold pairAddr; rw [h, hq]; rfl

/-! ## The ops -/

theorem nilFaults_false {ctx : Ctx} {v : Value} {argv : List Val} :
    nilFaults false ctx v argv = none := rfl

/-- A pairable load and its pair load: `arm64Op`'s `ld` and `ldPair` of one width (not 16) and
sign extension. -/
theorem arm64Op_ldPair {fop pop : Op} {w : Nat} (h : ldPairOf fop = some (w, pop)) :
    ∃ sg, w ≠ 16 ∧ fop.generic = false ∧ actOp fop = true ∧ pop.generic = false ∧
      actOp pop = true ∧
      (∀ (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) (za zm : Val) (ty : Ty), v.op = fop →
        arm64Op false env ctx fr v [za, zm] ty = .ok (match zm with
          | .mem m => (symAddr ctx v za).elim .poison (Arm64.loadN ty w sg m)
          | _ => .poison)) ∧
      (∀ (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) (za zm : Val) (ty : Ty), v.op = pop →
        arm64Op false env ctx fr v [za, zm] ty = .ok (match zm with
          | .mem m => (pairAddr ctx v w za).elim .poison
              (fun pq => Arm64.loadPair ty w sg m pq.1 pq.2)
          | _ => .poison)) := by
  refine ⟨decide (fop = .ARM64MOVWload), ?_⟩
  cases fop <;> simp only [ldPairOf, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  all_goals
    simp only [reduceCtorEq, decide_false, decide_true]
    exact ⟨by decide, rfl, rfl, rfl, rfl,
        fun env ctx fr v za zm ty hop => by
          unfold arm64Op; simp only [nilFaults_false, hop]; cases zm <;> simp only,
        fun env ctx fr v za zm ty hop => by
          unfold arm64Op; simp only [nilFaults_false, hop]; cases zm <;> simp only⟩

/-- A pairable store and its pair store: `arm64Op`'s `st` and `stPair` of one width. -/
theorem arm64Op_stPair {fop pop : Op} {w : Nat} (h : stPairOf fop = some (w, pop)) :
    fop.generic = false ∧ actOp fop = true ∧ pop.generic = false ∧ actOp pop = true ∧
      (∀ (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) (za zx zm : Val) (ty : Ty) (r : Val),
        v.op = fop → arm64Op false env ctx fr v [za, zx, zm] ty = .ok r →
        ∃ M P M', zm = .mem M ∧ symAddr ctx v za = some P ∧ Arm64.storeN w P zx M = some M' ∧
          r = .mem M') ∧
      (∀ (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) (za zx zy : Val) (M : Mem) (ty : Ty)
        (P Q : Ptr) (M' : Mem), v.op = pop → pairAddr ctx v w za = some (P, Q) →
        Arm64.storePair w P Q zx zy M = some M' →
        arm64Op false env ctx fr v [za, zx, zy, .mem M] ty = .ok (.mem M')) := by
  cases fop <;> simp only [stPairOf, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  all_goals
    refine ⟨rfl, rfl, rfl, rfl, fun env ctx fr v za zx zm ty r hop h => ?_,
      fun env ctx fr v za zx zy M ty P Q M' hop hpq hw => ?_⟩
    · unfold arm64Op at h
      simp only [hop, nilFaults_false] at h
      cases zm with
      | mem M =>
        cases hp : symAddr ctx v za with
        | none => simp only [hp] at h; split at h <;> cases h
        | some P =>
          simp only [hp, writeRes] at h
          split at h
          · rename_i M' hs
            simp only [Res.ok.injEq] at h
            exact ⟨M, P, M', rfl, rfl, hs, h.symm⟩
          · cases h
      | _ => simp only at h; split at h <;> cases h
    · unfold arm64Op
      simp only [hop, nilFaults_false, hpq, hw]
      rfl

/-- A tuple selector's lowered evaluation. -/
theorem evalOpL_sel {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {ty : Ty}
    {x : Val} {i : Nat} (h : selIdx v.op = some i) :
    evalOpL faulting env ctx fr v [x] ty = .ok (Tuple.select i [x]) := by
  have hop : v.op = .Select0 ∧ i = 0 ∨ v.op = .Select1 ∧ i = 1 := by
    revert h; cases v.op <;> simp [selIdx] <;> intro h <;> omega
  rcases hop with ⟨hop, rfl⟩ | ⟨hop, rfl⟩ <;>
  · have hg : v.op.generic = true := by rw [hop]; rfl
    rw [evalOpL_generic _ _ _ _ _ _ hg]
    have hr : isRoot v.op = false := by rw [hop]; rfl
    rw [CSE.evalOp_tail hr (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun)]
    have hf : frameVal ctx v = none := by unfold frameVal; rw [hop]
    rw [hf]
    show Res.ok (evalPure v.op ty v.auxInt v.aux [x]) = _
    rw [hop]; rfl

/-! ## Shapes -/

theorem retypeL_tuple2 (c0 c1 : Ty) (e0 e1 : Val) :
    Val.retypeL (.tuple [c0, c1]) (.tuple [e0, e1]) = .tuple [e0.retypeL c0, e1.retypeL c1] := by
  simp only [Val.retypeL, Val.widen, Val.widenList, Val.retype, Val.retypePre]
  rfl

theorem retypeL_poison (t : Ty) : Val.retypeL t .poison = .poison := by
  unfold Val.retypeL
  cases t <;> rfl

theorem retype_mem {md : LMode} {t : Ty} {M M' : Mem} (h : md.retype t (.mem M) = .mem M') :
    M' = M := by
  unfold LMode.retype Val.retypeL at h
  split at h <;> cases t <;> simp_all [Val.widen, Val.retype]

/-! ## Selectors of pair loads -/

/-- **A selector of a pair load evaluates as the load of its element** (`relB`'s pair-load
case), the pair load at a two-component tuple shape whose component `i` is the selector's and
the load's shape. -/
theorem evalValueL_selPair {md : LMode} (hlow : md.low = true) (hnf : md.faulting = false)
    {env : Env} {ctxT ctxS : Ctx} (htabs : ctxT.tabs = ctxS.tabs) (hact : ctxT.act = ctxS.act)
    {gv lv fv : Value} {i w : Nat} {pop : Op} {l p' m' p mm : ID}
    (hsel : selIdx gv.op = some i) (hgl : gv.args.toList = [l])
    (hld : ldPairOf fv.op = some (w, pop)) (hlop : lv.op = pop) (haux : lv.aux = fv.aux)
    (hai : fv.auxInt = lv.auxInt + Int64.ofNat (i * w)) (hla : lv.args.toList = [p', m'])
    (hfa : fv.args.toList = [p, mm]) {c0 c1 : Ty}
    (hcl : ctxT.tys[lv.id]?.getD .other = .tuple [c0, c1])
    (hcx : ctxT.tys[gv.id]?.getD .other = [c0, c1].getD i .other)
    (hcy : ctxS.tys[fv.id]?.getD .other = ctxT.tys[gv.id]?.getD .other)
    {frT frS : Frame} {rl zp zm : Val} (hl : frT.regs[l]? = some (some rl))
    (hlev : evalValueL md env ctxT frT lv = .ok rl)
    (hp : frT.regs[p']? = some (some zp)) (hp' : frS.regs[p]? = some (some zp))
    (hm : frT.regs[m']? = some (some zm)) (hm' : frS.regs[mm]? = some (some zm)) :
    evalValueL md env ctxT frT gv = evalValueL md env ctxS frS fv := by
  obtain ⟨sg, h16, hfg, hfa', hpg, hpa, hld1, hld2⟩ := arm64Op_ldPair hld
  have hi : i = 0 ∨ i = 1 := by
    revert hsel; cases gv.op <;> simp [selIdx] <;> omega
  -- the pair load
  rw [evalValueL_of_regs (L := [zp, zm]) (by rw [hla]; exact ⟨hp, hm, trivial⟩), hnf,
    evalOpL_act (hlop ▸ hpg) (hlop ▸ hpa), hld2 _ _ _ _ _ _ _ hlop] at hlev
  cases hlev
  -- the selector and the load
  rw [evalValueL_of_regs (L := [_]) (by rw [hgl]; exact ⟨hl, trivial⟩), evalOpL_sel hsel,
    evalValueL_of_regs (L := [zp, zm]) (by rw [hfa]; exact ⟨hp', hm', trivial⟩), hnf,
    evalOpL_act hfg hfa', hld1 _ _ _ _ _ _ _ rfl]
  simp only [Res.bind, LMode.retype, hlow, ite_true]
  rw [hcy, hcx, hcl]
  congr 1
  cases zm with
  | mem M =>
    dsimp only
    cases hs : symAddr ctxT lv zp with
    | none =>
      have hf : symAddr ctxS fv zp = none := by
        rw [symAddr_congr (v := { lv with auxInt := lv.auxInt + Int64.ofNat (i * w) })
          htabs.symm hact.symm haux.symm hai]
        exact symAddr_none_auxInt _ hs
      rw [pairAddr_none hs, hf]
      rcases hi with rfl | rfl <;> simp [Option.elim, retypeL_poison, Tuple.select]
    | some P =>
      obtain ⟨Q, hpq, hq⟩ := pairAddr_some (n := w) hs
      rw [hpq]
      simp only [Option.elim, Arm64.loadPair, Arm64.tupleTy, retypeL_tuple2, Arm64.loadElt, h16,
        ite_false]
      rcases hi with rfl | rfl
      · have hf : symAddr ctxS fv zp = some P := by
          rw [symAddr_congr (v := lv) htabs.symm hact.symm haux.symm
            (by rw [hai, Nat.zero_mul]; exact Int64.add_zero _)]
          exact hs
        rw [hf]
        simp [Tuple.select, Val.retypeL_idem]
      · have hf : symAddr ctxS fv zp = some Q := by
          rw [symAddr_congr (v := { lv with auxInt := lv.auxInt + Int64.ofNat w }) htabs.symm
            hact.symm haux.symm (by rw [hai, Nat.one_mul])]
          exact hq
        rw [hf]
        simp [Tuple.select, Val.retypeL_idem]
  | _ => rcases hi with rfl | rfl <;> simp [retypeL_poison, Tuple.select]

/-! ## Pair stores -/

/-- **A pair store evaluates as the second of its two stores** (`relB`'s pair-store case). -/
theorem evalValueL_stPair {md : LMode} (hnf : md.faulting = false) {env : Env}
    {ctxT ctxS : Ctx} (htabs : ctxT.tabs = ctxS.tabs) (hact : ctxT.act = ctxS.act)
    {gv fv mv : Value} {w : Nat} {pop : Op} {p' a' b' m' p b ym a mm : ID}
    (hw : stPairOf fv.op = some (w, pop)) (hga : gv.args.toList = [p', a', b', m'])
    (hfa : fv.args.toList = [p, b, ym]) (hop : gv.op = pop) (hmop : mv.op = fv.op)
    (hmaux : mv.aux = fv.aux) (hgaux : gv.aux = fv.aux) (hgai : gv.auxInt = mv.auxInt)
    (hfai : fv.auxInt = mv.auxInt + Int64.ofNat w) (hma : mv.args.toList = [p, a, mm])
    (hty : ctxT.tys[gv.id]? = ctxS.tys[fv.id]?) {frT frS : Frame} {zp za zb zm rm wv : Val}
    (h1 : frT.regs[p']? = some (some zp)) (h1' : frS.regs[p]? = some (some zp))
    (h2 : frT.regs[a']? = some (some za)) (h2' : frS.regs[a]? = some (some za))
    (h3 : frT.regs[b']? = some (some zb)) (h3' : frS.regs[b]? = some (some zb))
    (h4 : frT.regs[m']? = some (some zm)) (h4' : frS.regs[mm]? = some (some zm))
    (hym : frS.regs[ym]? = some (some rm)) (hmev : evalValueL md env ctxS frS mv = .ok rm)
    (hfev : evalValueL md env ctxS frS fv = .ok wv) :
    evalValueL md env ctxT frT gv = .ok wv := by
  obtain ⟨hfg, hfa', hpg, hpa, hst, hstp⟩ := arm64Op_stPair hw
  -- the first store
  rw [evalValueL_of_regs (L := [zp, za, zm]) (by rw [hma]; exact ⟨h1', h2', h4', trivial⟩),
    hnf, evalOpL_act (hmop ▸ hfg) (hmop ▸ hfa')] at hmev
  obtain ⟨r0, hr0, rfl⟩ := res_bind_ok hmev
  obtain ⟨M0, P, M1, rfl, hP, hs1, rfl⟩ := hst _ _ _ _ _ _ _ _ _ hmop hr0
  -- the second store
  rw [evalValueL_of_regs (L := [zp, zb, _]) (by rw [hfa]; exact ⟨h1', h3', hym, trivial⟩),
    hnf, evalOpL_act hfg hfa'] at hfev
  obtain ⟨r1, hr1, rfl⟩ := res_bind_ok hfev
  obtain ⟨M1', Q, M2, hM1, hQ, hs2, rfl⟩ := hst _ _ _ _ _ _ _ _ _ rfl hr1
  have e := retype_mem hM1
  subst e
  -- the pair store
  have hP' : symAddr ctxT gv zp = some P := by
    rw [symAddr_congr htabs hact (hgaux.trans hmaux.symm) hgai, hP]
  have hQ' : symAddr ctxT { gv with auxInt := gv.auxInt + Int64.ofNat w } zp = some Q := by
    rw [symAddr_congr (v' := { gv with auxInt := gv.auxInt + Int64.ofNat w }) (v := fv) htabs hact
      hgaux (by rw [hgai, hfai]), hQ]
  obtain ⟨Q', hpq, hq'⟩ := pairAddr_some (n := w) hP'
  rw [hq'] at hQ'; cases hQ'
  have hsp : Arm64.storePair w P Q za zb M0 = some M2 := by
    unfold Arm64.storePair
    unfold Arm64.storeN at hs1 hs2
    rw [hs1]; exact hs2
  rw [evalValueL_of_regs (L := [zp, za, zb, _]) (by
      rw [hga]; exact ⟨h1, h2, h3, h4, trivial⟩),
    hnf, evalOpL_act (hop ▸ hpg) (hop ▸ hpa), hstp _ _ _ _ _ _ _ _ _ _ _ _ hop hpq hsp, hty]
  rfl

private theorem stPairOf_width {op pop : Op} {w : Nat} (h : stPairOf op = some (w, pop)) :
    0 < w ∧ w ≤ 8 := by
  cases op <;> simp only [stPairOf, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    omega

private theorem storeBytes_size' {n : Nat} (hn : n ≤ 8) (v : Val) :
    (Arm64.storeBytes n v).size = n := by
  unfold Arm64.storeBytes
  split
  · simp [ptrBytes]
  · split
    · next h => simpa using h
    · simp
  · split
    · simp [hn, intBytes]
    · simp

/-- **A pair store evaluates as the second of two reversed stores** (`relB`'s reversed
pair-store case): the source stores the element one width up first; the two writes are
disjoint and commute. -/
theorem evalValueL_stPairRev {md : LMode} (hnf : md.faulting = false) {env : Env}
    {ctxT ctxS : Ctx} (htabs : ctxT.tabs = ctxS.tabs) (hact : ctxT.act = ctxS.act)
    {gv fv mv : Value} {w : Nat} {pop : Op} {p' a' b' m' p a ym b mm : ID}
    (hw : stPairOf fv.op = some (w, pop)) (hga : gv.args.toList = [p', a', b', m'])
    (hfa : fv.args.toList = [p, a, ym]) (hop : gv.op = pop) (hmop : mv.op = fv.op)
    (hmaux : mv.aux = fv.aux) (hgaux : gv.aux = fv.aux) (hgai : gv.auxInt = fv.auxInt)
    (hmai : mv.auxInt = fv.auxInt + Int64.ofNat w) (hma : mv.args.toList = [p, b, mm])
    (hty : ctxT.tys[gv.id]? = ctxS.tys[fv.id]?) {frT frS : Frame} {zp za zb zm rm wv : Val}
    (h1 : frT.regs[p']? = some (some zp)) (h1' : frS.regs[p]? = some (some zp))
    (h2 : frT.regs[a']? = some (some za)) (h2' : frS.regs[a]? = some (some za))
    (h3 : frT.regs[b']? = some (some zb)) (h3' : frS.regs[b]? = some (some zb))
    (h4 : frT.regs[m']? = some (some zm)) (h4' : frS.regs[mm]? = some (some zm))
    (hym : frS.regs[ym]? = some (some rm)) (hmev : evalValueL md env ctxS frS mv = .ok rm)
    (hfev : evalValueL md env ctxS frS fv = .ok wv) :
    evalValueL md env ctxT frT gv = .ok wv := by
  obtain ⟨hfg, hfa', hpg, hpa, hst, hstp⟩ := arm64Op_stPair hw
  -- the first store, one width up
  rw [evalValueL_of_regs (L := [zp, zb, zm]) (by rw [hma]; exact ⟨h1', h3', h4', trivial⟩),
    hnf, evalOpL_act (hmop ▸ hfg) (hmop ▸ hfa')] at hmev
  obtain ⟨r0, hr0, rfl⟩ := res_bind_ok hmev
  obtain ⟨M0, Q, M1, rfl, hQ, hs1, rfl⟩ := hst _ _ _ _ _ _ _ _ _ hmop hr0
  -- the second store
  rw [evalValueL_of_regs (L := [zp, za, _]) (by rw [hfa]; exact ⟨h1', h2', hym, trivial⟩),
    hnf, evalOpL_act hfg hfa'] at hfev
  obtain ⟨r1, hr1, rfl⟩ := res_bind_ok hfev
  obtain ⟨M1', P, M2, hM1, hP, hs2, rfl⟩ := hst _ _ _ _ _ _ _ _ _ rfl hr1
  have e := retype_mem hM1
  subst e
  -- the two writes commute
  have hQf : symAddr ctxS { fv with auxInt := fv.auxInt + Int64.ofNat w } zp = some Q := by
    rw [symAddr_congr (v' := { fv with auxInt := fv.auxInt + Int64.ofNat w }) (v := mv) rfl rfl
      hmaux.symm hmai.symm, hQ]
  obtain ⟨hw0, hw8⟩ := stPairOf_width hw
  unfold Arm64.storeN at hs1 hs2
  obtain ⟨M1'', hs1', hs2'⟩ := write_adj_comm hw0 (by omega) hP hQf (storeBytes_size' hw8 _)
    (storeBytes_size' hw8 _) hs1 hs2
  -- the pair store
  have hP' : symAddr ctxT gv zp = some P := by
    rw [symAddr_congr htabs hact hgaux hgai, hP]
  have hQ' : symAddr ctxT { gv with auxInt := gv.auxInt + Int64.ofNat w } zp = some Q := by
    rw [symAddr_congr (v' := { gv with auxInt := gv.auxInt + Int64.ofNat w }) (v := mv) htabs hact
      (hgaux.trans hmaux.symm) (by rw [hgai, hmai]), hQ]
  obtain ⟨Q', hpq, hq'⟩ := pairAddr_some (n := w) hP'
  rw [hq'] at hQ'; cases hQ'
  have hsp : Arm64.storePair w P Q za zb M0 = some M2 := by
    unfold Arm64.storePair
    rw [hs1']; exact hs2'
  rw [evalValueL_of_regs (L := [zp, za, zb, _]) (by
      rw [hga]; exact ⟨h1, h2, h3, h4, trivial⟩),
    hnf, evalOpL_act (hop ▸ hpg) (hop ▸ hpa), hstp _ _ _ _ _ _ _ _ _ _ _ _ hop hpq hsp, hty]
  rfl

end GoFV.Proof.MoveL
