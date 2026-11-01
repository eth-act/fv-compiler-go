import GoFV.Proof.Pass.ECCall
import GoFV.Proof.Pass.ECArgSel

/-!
# `expand calls`: stack-assigned call results (issue #28)

A call's stack-assigned result is written by `encodeResults` into the outgoing-arguments area of
the call's result memory, in both forms of the call (`callOp`). After `expand calls`, the result
`SelectN [i] c` is a Make-tree whose leaves `Load` the result's leaf slots
(`OffPtr [off + o] SP`) from the call's memory `SelectN [#pieces] c` (`ECCheck.stkLeavesOK`).

`ecr_encodeResults_read`: the stack results read back from the memory `encodeResults` returns
(the slots are disjoint, `outsOK`). `ecr_callOp_src`: the source's call returns its results,
that memory and the result addresses. `obl_selectStack`: the target's tree builds a refinement
of the source's result: each leaf loads, from a memory refining the source's, the bytes of the
leaf in the result's encoding (`load_mono`, `toPieces = leafVals`, `build_leafVals`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.Order GoFV.Proof.AtomSim
open GoFV.Proof.CSE.Mem

/-! ## `encodeResults` writes the stack results -/

/-- The pointer of a result's slot in the outgoing-arguments area of activation `act`. -/
abbrev ecrSlot (act : Nat) (p : ABIParam) : Ptr := ⟨.outargs act, BitVec.ofInt 64 p.offset⟩

private theorem ofInt_toNat {o : Int} (h0 : 0 ≤ o) (h : o < 2 ^ 24) :
    (BitVec.ofInt 64 o).toNat = o.toNat := by
  rw [ecs_ofInt h0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- Reads separate from every stack slot of `ps` are unchanged by `encodeResults`. -/
theorem ecr_encodeResults_keep {tabs : Tables} {act : Nat} {P : Ptr} {n : Nat} :
    ∀ {ps : List ABIParam} {rs : List Val} {m : Mem} {res : List Val × Mem},
      encodeResults tabs act ps rs m = some res →
      (∀ q ∈ ps, q.regs.isEmpty = true → Sep P n (ecrSlot act q) (tabs.ty q.type).size) →
      res.2.read P n = m.read P n
  | [], [], m, res, h, _ => by
    simp only [encodeResults, Option.some.injEq] at h
    subst h; rfl
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => by simp [encodeResults] at h
  | p :: ps, r :: rs, m, res, h, hs => by
    unfold encodeResults at h
    dsimp only at h
    split at h
    · rename_i hst
      cases hwr : m.write (ecrSlot act p) (encode (tabs.ty p.type) r) with
      | none => rw [hwr] at h; cases h
      | some m' =>
        rw [hwr] at h
        rw [ecr_encodeResults_keep h (fun q hq => hs q (List.mem_cons_of_mem _ hq)),
          read_write_sep hwr (by rw [GoFV.SSA.Sem.encode_size]; exact hs p List.mem_cons_self hst)]
    · cases he : encodeResults tabs act ps rs m with
      | none => rw [he] at h; cases h
      | some r' =>
        rw [he] at h
        cases h
        exact ecr_encodeResults_keep (res := r') he (fun q hq => hs q (List.mem_cons_of_mem _ hq))

/-- **The stack results read back** from the memory `encodeResults` returns. -/
theorem ecr_encodeResults_read {tabs : Tables} {act : Nat} :
    ∀ {ps : List ABIParam} {rs : List Val} {m : Mem} {res : List Val × Mem},
      encodeResults tabs act ps rs m = some res →
      (ps.filter (·.regs.isEmpty)).Pairwise
        (fun p q => p.offset + ((tabs.ty p.type).size : Int) ≤ q.offset) →
      (∀ q ∈ ps, q.regs.isEmpty = true → 0 ≤ q.offset ∧ q.offset + (tabs.ty q.type).size < 2 ^ 24) →
      ∀ p r, (p, r) ∈ ps.zip rs → p.regs.isEmpty = true →
        res.2.read (ecrSlot act p) (tabs.ty p.type).size = some (encode (tabs.ty p.type) r)
  | [], _, _, _, _, _, _, _, _, hm, _ => by simp at hm
  | _ :: _, [], _, _, _, _, _, _, _, hm, _ => by simp at hm
  | p :: ps, r :: rs, m, res, h, hpw, hb, p', r', hm, hst' => by
    unfold encodeResults at h
    dsimp only at h
    split at h
    · rename_i hst
      rw [List.filter_cons_of_pos (by simpa using hst)] at hpw
      cases hwr : m.write (ecrSlot act p) (encode (tabs.ty p.type) r) with
      | none => rw [hwr] at h; cases h
      | some m' =>
        rw [hwr] at h
        rcases List.mem_cons.1 hm with he | hm
        · cases he
          rw [ecr_encodeResults_keep h, ← GoFV.SSA.Sem.encode_size (tabs.ty p.type) r]
          · exact GoFV.Proof.Pass.LoadFwd.read_write_self hwr
          intro q hq hqs
          have hpq := List.rel_of_pairwise_cons hpw (List.mem_filter.2 ⟨hq, by simpa using hqs⟩)
          obtain ⟨hp0, hp24⟩ := hb p List.mem_cons_self hst
          obtain ⟨hq0, hq24⟩ := hb q (List.mem_cons_of_mem _ hq) hqs
          refine .inr (.inr (.inr (.inl ?_)))
          rw [ofInt_toNat hp0 (by omega), ofInt_toNat hq0 (by omega)]
          omega
        · exact ecr_encodeResults_read h (List.Pairwise.of_cons hpw)
            (fun q hq => hb q (List.mem_cons_of_mem _ hq)) p' r' hm hst'
    · rename_i hst
      rw [List.filter_cons_of_neg (by simpa using hst)] at hpw
      cases he : encodeResults tabs act ps rs m with
      | none => rw [he] at h; cases h
      | some r'' =>
        rw [he] at h
        cases h
        rcases List.mem_cons.1 hm with he' | hm
        · cases he'; exact absurd hst' hst
        · exact ecr_encodeResults_read (res := r'') he hpw (fun q hq => hb q (List.mem_cons_of_mem _ hq)) p' r' hm hst'


/-- **The source's call** (pre-`expand calls` form) returns its Go-typed results (of their
shapes), the memory `encodeResults` returns (the stack results written into the outgoing area)
and the result addresses. -/
theorem ecr_callOp_src {env : Env} {ctx : Ctx} {u : Value} {argv : List Val} {y : Val}
    {abi : CallABI}
    (hpre : (u.op == .StaticCall || u.op == .ClosureCall || u.op == .InterCall) = false)
    (habi : callABI? ctx.tabs u.aux = some abi) (h : callOp env ctx u argv = .ok y) :
    ∃ rs m a m0 P, y = .tuple (rs ++ [.mem m, a]) ∧
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (ctx.tabs.ty p.type) = true)
        (outsOf abi) rs ∧
      encodeResults ctx.tabs ctx.act (outsOf abi) rs m0 = some (P, m) := by
  unfold callOp at h
  rw [habi] at h
  revert h
  generalize callTarget ctx u argv = T1
  rcases T1 with ⟨callee?, clo, rest⟩
  intro h
  dsimp only at h
  cases callee? with
  | none => cases h
  | some callee =>
    dsimp only [bind, Res.bind, Res.ofOption] at h
    cases hl : rest.getLast? with
    | none => rw [hl] at h; cases h
    | some mv =>
      rw [hl] at h
      cases mv with
      | mem m =>
        dsimp only at h
        simp only [hpre, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.getD_some] at h
        dsimp only [pure, Res.bind] at h
        split at h
        · cases h
        split at h
        · cases h
        cases hx : env.extern callee with
        | none => rw [hx] at h; cases h
        | some c =>
          rw [hx] at h
          dsimp only at h
          cases ho : c rest.dropLast clo (m.poisonBlock (Blk.outargs ctx.act)) with
          | returned rs0 m' =>
            rw [ho] at h
            dsimp only at h
            cases he : encodeResults ctx.tabs ctx.act (List.filter (fun x => x.out) abi.params.toList)
                (retypeResults ctx.tabs (List.filter (fun x => x.out) abi.params.toList) rs0) m' with
            | none => rw [he] at h; cases h
            | some r =>
              rw [he] at h
              cases h
              have hlen := ecc_encodeResults_length he
              rw [ecc_retypeResults_length] at hlen
              exact ⟨_, _, _, m', r.1, rfl, ecc_retypeResults hlen, he⟩
          | panicked e m' => rw [ho] at h; cases h
          | stuck msg => rw [ho] at h; cases h
      | _ => cases h
/-- `outsOK`'s stack slots: inside the area's window, disjoint and in order. -/
theorem ecr_outsOK {tabs : Tables} {ps : List ABIParam} (h : outsOK tabs ps = true) :
    (∀ p ∈ ps, p.regs.isEmpty = true → 0 ≤ p.offset ∧ p.offset + (tabs.ty p.type).size < 2 ^ 24) ∧
    (ps.filter (·.regs.isEmpty)).Pairwise
      (fun p q => p.offset + ((tabs.ty p.type).size : Int) ≤ q.offset) := by
  unfold outsOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun p hp hst => ?_, ecs_slotsSorted_pairwise h.2⟩
  have := h.1 p hp
  rw [Bool.and_eq_true, hst, if_pos rfl, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq] at this
  exact this.2

/-! ## The target's leaves -/

theorem ecr_stkLeaves_get {sh : Array Ty} {g : Func} {nw : ID → Bool} {c : ID} {k : Nat}
    {off : Int} : ∀ {os : List (Nat × Ty)} {ls : List ID}, stkLeavesOK sh g nw c k off os ls = true →
      ∀ (j : Nat) (l : ID) (e : Nat × Ty), ls[j]? = some l → os[j]? = some e →
        ∃ wl, g.value? l = some wl ∧ wl.op = .Load ∧ wl.args.size = 2 ∧
          spOffOK sh g nw wl.args[0]! (off + e.1) = true ∧ memSelOK sh g c k wl.args[1]! = true
  | [], [], _, _, _, _, hl, _ => by simp at hl
  | [], _ :: _, h, _, _, _, _, _ | _ :: _, [], h, _, _, _, _, _ => by simp [stkLeavesOK] at h
  | (o, lt) :: os, l :: ls, h, j, l', e, hl, he => by
    simp only [stkLeavesOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases j with
    | zero =>
      cases hl; cases he
      split at h1
      · rename_i wl hwl
        simp only [Bool.and_eq_true, beq_iff_eq] at h1
        exact ⟨wl, hwl, h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩
      · cases h1
    | succ j => exact ecr_stkLeaves_get h2 j l' e hl he

private theorem ecr_mapM_mem {α β : Type} {F : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM F = some ys → ∀ y ∈ ys, ∃ x ∈ xs, F x = some y
  | [], ys, h, y, hy => by
    simp only [List.mapM_nil] at h
    cases h; cases hy
  | x :: xs, ys, h, y, hy => by
    simp only [List.mapM_cons] at h
    cases hx : F x with
    | none => rw [hx] at h; cases h
    | some b =>
      cases hr : xs.mapM F with
      | none => rw [hx, hr] at h; cases h
      | some bs =>
        rw [hx, hr] at h
        cases h
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨x', hx', h'⟩ := ecr_mapM_mem hr y hy
          exact ⟨x', List.mem_cons_of_mem _ hx', h'⟩

/-- A Make-tree's leaves are its root or new values of `E` (and of `P`), when the root's new
arguments are. -/
theorem ecr_mkTree_E {env : Env} {tabs : Tables} {g : Func} {nw : ID → Bool} {T : Frame}
    {E P : ID → Prop} (hN : NewCons env (Ctx.make tabs g) nw T E)
    (hP : ∀ z, P z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, nw a = true → P a) :
    ∀ {n : Nat} {z : ID} {t : Ty} {ls : List ID} {w : Value},
      mkTree (typeShapes tabs) g nw n z t = some ls → g.value? z = some w → P z →
      (∀ a ∈ w.args, nw a = true → E a) → ∀ l ∈ ls, l = z ∨ (E l ∧ P l)
  | 0, _, _, _, _, hm, _, _, _ => by cases hm
  | n + 1, z, t, ls, w, hm, hw, hPz, hE => by
    rw [mkTree, hw] at hm
    dsimp only at hm
    split at hm
    · cases hm
    split at hm
    · rename_i fs m hfs
      split at hm
      · cases hmap : (fs.zip w.args.toList).mapM (fun (e : (Nat × Ty) × ID) =>
            if nw e.2 then mkTree (typeShapes tabs) g nw n e.2 e.1.2 else none) with
        | none => rw [hmap] at hm; cases hm
        | some lss =>
          rw [hmap] at hm
          cases hm
          intro l hl
          obtain ⟨b, hb, hlb⟩ := List.mem_flatten.1 (by simpa using hl)
          obtain ⟨e, he, hfe⟩ := ecr_mapM_mem hmap b hb
          have hea : e.2 ∈ w.args := Array.mem_toList_iff.1 (List.of_mem_zip he).2
          split at hfe
          · rename_i hna
            have hEa := hE e.2 hea hna
            have hPa := (hP z hPz w hw).2 e.2 hea hna
            obtain ⟨-, wa, ya, hwa, hEargs, -, -⟩ := hN e.2 hEa
            rcases ecr_mkTree_E hN hP hfe hwa hPa hEargs l hlb with rfl | h
            · exact .inr ⟨hEa, hPa⟩
            · exact .inr h
          · cases hfe
      · cases hm
    · split at hm
      · cases hm; intro l hl; cases hl
      · cases hm
    · split at hm
      · cases hm; intro l hl; exact .inl (List.mem_singleton.1 hl)
      · cases hm

theorem ecr_eval_load {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} (h : w.op = .Load)
    (hr : ∀ a ∈ w.args, Reg fr a) :
    evalValue env ctx fr w = .ok ((loadOp (ctx.tys[w.id]?.getD .other)
      (w.args.toList.map (rv fr))).retype (ctx.tys[w.id]?.getD .other)) := by
  rw [ecT_eval_term (by rw [h]; decide) (by rw [h]; decide) hr, h]; rfl

theorem ecr_load_atom {s : Ty} (hs : atom s = true) (m : Mem) (p : Ptr) :
    m.load s p = match m.read p s.size with
      | some bs => decode bs 0 s
      | none => .poison := by
  cases s <;> first | rfl | simp [atom] at hs

theorem ecr_atom_eqE {s t : Ty} (h : eqE s t = true) (ht : atom t = true) : atom s = true := by
  have he : erase s = erase t := Ty.eq_of_beq h
  cases t <;> simp only [atom, Bool.false_eq_true] at ht <;>
    cases s <;> simp_all [erase, atom]

/-- **A leaf loaded from a stack result's slot**: the leaf's bytes in the result's encoding. -/
theorem ecr_leaf_load {m : Mem} {p0 : Nat} {t : Ty} {bs : Array Byte} (hw : wf t = true)
    (hrd : m.read (ecsSlot p0) t.size = some bs) (hb : p0 + t.size < 2 ^ 64)
    {o : Nat} {lt s : Ty} (hl : (o, lt) ∈ leaves t) (hs : eqE s lt = true) :
    m.load s (ecsSlot (p0 + o)) = decode bs o lt := by
  obtain ⟨hk, hat⟩ := mem_leaves hw hl
  rw [ecr_load_atom (ecr_atom_eqE hs hat), ecT_eqE_size hs]
  obtain ⟨bs', h1, h2⟩ : ∃ bs', m.read (ecsSlot (p0 + o)) lt.size = some bs' ∧
      Agree bs' 0 bs o lt.size := by
    by_cases h0 : lt.size = 0
    · refine ⟨#[], ?_, fun k hk => absurd hk (by omega)⟩
      unfold Mem.read; simp [h0]
    · exact ⟨_, ecs_read_sub hk h0 hrd hb, fun k hk => by
        rw [Nat.zero_add, GoFV.Proof.ABI.getElem?_extract_add, if_pos hk]⟩
  rw [h1]
  dsimp only
  rw [ecT_eqE_decode hs, decode_agree lt (wf_atom hat) h2]

/-- The leaf values of a value: its leaves' bytes in its encoding. -/
theorem ecr_leafVals_get {t : Ty} {r : Val} (hw : wf t = true) (hr : r.hasTy t = true) {j : Nat}
    {e : Nat × Ty} (he : (leaves t)[j]? = some e) :
    (leafVals t r)[j]? = some (decode (encode t r) e.1 e.2) := by
  rw [← toPieces_eq_leafVals hw hr]
  unfold toPieces
  simp only [List.getElem?_map, he, Option.map_some]

/-- The leaves of a stack-assigned result's tree (`stackLoads`). -/
theorem ecr_stackLoads {tabs : Tables} {f g : Func} {x c : ID} {u cu : Value} {p : ABIParam}
    (hu : f.value? x = some u) (hop : u.op = .SelectN) (hargs : u.args.toList = [c])
    (hcu : f.value? c = some cu) (hcall : (callOpMap cu.op).isSome = true)
    (hi0 : 0 ≤ u.auxInt.toInt)
    (hp : (callOuts tabs cu.aux)[u.auxInt.toInt.toNat]? = some p) (hpst : p.regs.isEmpty = true) :
    stackLoads tabs (typeShapes tabs) f g x =
      (mkTree (typeShapes tabs) g (isNewB f) (tabs.types.size + 1) x (tabs.ty p.type)).getD [] := by
  unfold stackLoads
  rw [hu]; dsimp only; rw [hargs]; dsimp only; rw [hcu]; dsimp only
  rw [if_pos (by simp [hop, hcall, hi0]), hp]
  dsimp only
  rw [if_pos hpst]

/-- **The obligation of a stack-assigned call result**: given that the source register of the
call holds its evaluation (`HS c`) and the target registers of the leaves' source `SP`s and
memories hold theirs (`HT`). -/
theorem obl_selectStack {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {c : ID}
    {cu cw : Value} {HS HT : ID → Prop} {p : ABIParam}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hop : u.op = .SelectN)
    (hargs : u.args.toList = [c]) (hcu : f.value? c = some cu) (hcw : g.value? c = some cw)
    (hcall : (callOpMap cu.op).isSome = true)
    (hcok : callOK tabs (typeShapes tabs) f g cu cw = true)
    (hinv : invalidated g x = false) (hok : selectOK tabs (typeShapes tabs) f g x u w = true)
    (hp : (callOuts tabs cu.aux)[u.auxInt.toInt.toNat]? = some p) (hpst : p.regs.isEmpty = true)
    (huid : u.id = x) (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hHS : HS c)
    (hHT : ∀ l ∈ stackLoads tabs (typeShapes tabs) f g x,
      (isNewB f (loadSP g l) = false → HT (loadSP g l)) ∧
      (isNewB f (loadMem g l) = false → HT (loadMem g l))) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  intro u' w' hu' hw' env _ frS T _ hRegs E hN hEw hRT hRS hfr hSH hTH
  rw [hu] at hu'; cases hu'
  rw [hw] at hw'; cases hw'
  rw [funext (ecCv_of_not_special (tabs := tabs) (ecA_sel_not_special hu hop hinv))]
  have hcmem : c ∈ u.args := Array.mem_toList_iff.1 (by rw [hargs]; exact List.mem_singleton.2 rfl)
  obtain ⟨yc, hyc⟩ := hRS c hcmem
  obtain ⟨yc', hyc', hR⟩ := hfr c (by simp [ecFront, hu, hargs]) yc hyc
  obtain ⟨hinvc, hoo, htup, hrtup⟩ := ecA_callOK_facts hcw hcok
  have hwfo := ec_outsOK_wf hoo
  obtain ⟨hbnd, hpw⟩ := ecr_outsOK hoo
  rw [ecA_cv_call hcu hcall hinvc, ecT_shapeOf_value hcw] at hR
  obtain ⟨rus, hrus, hrusl, -, hrusm⟩ := ecA_regTupleOf_get hrtup
  rw [hrus] at hR
  -- the ABI
  obtain ⟨op, k, abi, hmap, habi⟩ : ∃ op k abi, callOpMap cu.op = some (op, k) ∧
      callABI? tabs cu.aux = some abi := by
    unfold callOK at hcok
    split at hcok
    · rename_i op k abi hm ha; exact ⟨op, k, abi, hm, ha⟩
    · cases hcok
  have hco : callOuts tabs cu.aux = outsOf abi := by unfold callOuts; rw [habi]; rfl
  obtain ⟨hopu, hpre, -, -⟩ := ecc_callOpMap hmap
  -- the source's call: its evaluation
  obtain ⟨hcid, yc0, hyc0, hevc⟩ := hSH c hHS cu hcu
  rw [hyc] at hyc0
  cases hyc0
  have hopu' : cu.op = .StaticLECall ∨ cu.op = .ClosureLECall ∨ cu.op = .InterLECall ∨
      cu.op = .StaticCall ∨ cu.op = .ClosureCall ∨ cu.op = .InterCall := by
    rcases hopu with h | h | h <;> simp [h]
  rw [evalValue_of_regs (regs_of_ok hevc), ecc_evalOp_call hopu'] at hevc
  cases hco0 : callOp env (Ctx.make tabs f) cu (cu.args.toList.map (rv frS)) with
  | panic e m => rw [hco0] at hevc; cases hevc
  | stuck msg => rw [hco0] at hevc; cases hevc
  | ok y0 =>
  rw [hco0] at hevc
  obtain ⟨rs, m, a, m0, P, rfl, hF, henc⟩ := ecr_callOp_src hpre habi hco0
  rw [← hco] at hF henc
  obtain ⟨us, hus, husl, hue, hul⟩ := ecf_tupleOf htup
  rw [ecf_valueTy] at hus
  have hycv : yc = .tuple (rs ++ [.mem m, a]) := by
    simp only [Res.bind, Res.ok.injEq] at hevc
    rw [← hevc, hcid, tys_of_value hcu, Option.getD_some, hus, Val.retype_of_hasTy]
    show Val.hasTyPre _ us = true
    exact ecc_hasTyPre_call (tl := [a]) hF hue (by rw [husl, List.length_map]) hul m
  subst hycv
  -- the selected result
  have hi0 : 0 ≤ u.auxInt.toInt := by
    unfold selectOK at hok
    rw [hargs] at hok; dsimp only at hok; rw [hcu] at hok; dsimp only at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.2
  have hi : u.auxInt.toInt = ((u.auxInt.toInt.toNat : Nat) : Int) := by omega
  have hilt := ecA_lt_of_getElem? hp
  have hrl := ecf_forall₂_length hF
  obtain ⟨r, hr⟩ : ∃ r, rs[u.auxInt.toInt.toNat]? = some r :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hpr : (p, r) ∈ (callOuts tabs cu.aux).zip rs :=
    List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hp, hr⟩)
  have hrt : r.hasTy (tabs.ty p.type) = true := by
    obtain ⟨_, h1, h2⟩ := ecT_forall₂_get' hF u.auxInt.toInt.toNat r hr
    rw [hp] at h1; cases h1; exact h2
  have hwf := hwfo p (List.mem_of_getElem? hp)
  -- the source's evaluation of `x`
  have htS : (Ctx.make tabs f).tys[u.id]?.getD .other = shapeOf (typeShapes tabs) f x := by
    rw [huid, shapeOf_eq]
  rw [ecT_eval_selectN hop hRS, hargs, List.map_cons, List.map_nil, rv_of hyc, htS,
    ecA_selectN_tuple hi, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), hr,
    Option.getD_some]
  -- the target's tree
  unfold selectOK at hok
  rw [hargs] at hok; dsimp only at hok; rw [hcu] at hok; dsimp only at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨-, hok⟩ := hok
  have hne : (u.auxInt.toInt.toNat == (callOuts tabs cu.aux).length) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  rw [hne] at hok
  simp only [Bool.false_eq_true, ↓reduceIte, hp] at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨heq, hok⟩ := hok
  cases hmt : mkTree (typeShapes tabs) g (isNewB f) (tabs.types.size + 1) x (tabs.ty p.type) with
  | none => rw [hmt] at hok; cases hok
  | some ls =>
  rw [hmt] at hok
  dsimp only at hok
  simp only [Bool.and_eq_true, hpst, ↓reduceIte] at hok
  obtain ⟨hlen, hstk⟩ := hok
  have hlen' : ls.length = (leaves (tabs.ty p.type)).length := beq_iff_eq.1 hlen
  have hls : stackLoads tabs (typeShapes tabs) f g x = ls := by
    rw [ecr_stackLoads hu hop hargs hcu hcall hi0 hp hpst, hmt]; rfl
  rw [hls] at hHT
  obtain ⟨yT, hevT⟩ := ecT_root_ok (env := env) (T := T) hmt hw hRT fun hx => by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨e, he⟩ : ∃ e, (leaves (tabs.ty p.type))[j]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by have := ecA_lt_of_getElem? hj; omega)⟩
    obtain ⟨wl, hwl, hwop, -⟩ := ecr_stkLeaves_get hstk j x e hj he
    rw [hw] at hwl
    cases hwl
    exact ⟨_, ecr_eval_load hwop hRT⟩
  rw [hevT]
  refine .ok ?_
  obtain ⟨ys, F, S, hyT⟩ := ecT_node hN hL _ x _ ls w yT hmt hw hLx hEw hevT
  rw [eqE_retype heq, hyT, Val.retype_of_hasTy hrt]
  -- the target's call memory refines the source's
  have hl0 : (callOuts tabs cu.aux).length ≤ (rs ++ [.mem m, a]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  obtain ⟨D, hD, mT, hDK, hmT⟩ : ∃ D, yc' = .tuple D ∧ ∃ mT,
      D[(leafTys tabs (callOuts tabs cu.aux)).length]? = some (.mem mT) ∧ Mem.Refines m mT := by
    rw [ecA_convTuple_eq] at hR
    obtain ⟨C', hC', hg⟩ := ecA_retypePre_get (ts := rus)
      (vs := ecA_convList tabs (callOuts tabs cu.aux) (rs ++ [.mem m, a]))
      (by rw [ecA_convList_length tabs _ _ hwfo hl0]; simp only [List.length_append,
        List.length_cons, List.length_nil]; omega)
    have hre : (Val.tuple (ecA_convList tabs (callOuts tabs cu.aux) (rs ++ [.mem m, a]))).retype
        (.tuple rus) = .tuple C' := by simp only [Val.retype, hC']
    rw [hre] at hR
    cases hR with
    | tuple hRL =>
      have hC := ecA_convList_rest tabs _ _ hwfo hl0 0
      rw [Nat.add_zero, Nat.add_zero, List.getElem?_append_right (by omega), hrl, Nat.sub_self,
        List.getElem?_cons_zero] at hC
      have hC2 := hg _ _ _ hrusm hC
      obtain ⟨d, hd, hRd⟩ := ecT_refinesList_get hRL _ _ hC2
      cases hRd with
      | mem hmm => exact ⟨_, rfl, _, hd, hmm⟩
  subst hD
  -- the source's stack result in the call's memory
  obtain ⟨hp0, hp24⟩ := hbnd p (List.mem_of_getElem? hp) hpst
  have hrd : m.read (ecsSlot p.offset.toNat) (tabs.ty p.type).size =
      some (encode (tabs.ty p.type) r) := by
    have h := ecr_encodeResults_read henc hpw hbnd p r hpr hpst
    have e : ecrSlot (Ctx.make tabs f).act p = ecsSlot p.offset.toNat := by
      simp only [ecrSlot, ecsSlot, ecs_ofInt hp0]; rfl
    rw [e] at h
    exact h
  refine Sem.Refines.trans (b := (build (tabs.ty p.type) (leafVals (tabs.ty p.type) r)).retype
    (tabs.ty p.type)) ?_ (Sem.retype_mono _ (build_mono ?_))
  · have := Sem.retype_mono (tabs.ty p.type) (build_leafVals hwf hrt)
    rw [Val.retype_of_hasTy hrt] at this
    exact this
  refine ecT_refinesList_of_get ?_ fun j a' b ha hb => ?_
  · rw [leafVals_length hwf, ← S.length_eq, F.length_eq]
  obtain ⟨l, hl, wl, hwl, hid, hev⟩ := ecT_forall₂_get' F j b hb
  obtain ⟨e, he, hsh⟩ := ecT_forall₂_get S j l hl
  have hsh' : eqE (shapeOf (typeShapes tabs) g l) e.2 = true := hsh
  obtain ⟨wl', hwl', hwop, hsz, hq, hms⟩ := ecr_stkLeaves_get hstk j l e hl he
  rw [hwl] at hwl'
  cases hwl'
  have hlmem : l ∈ ls := List.mem_of_getElem? hl
  obtain ⟨hHsp, hHm⟩ := hHT l hlmem
  -- the leaf's new arguments are held
  have hEarg : ∀ z ∈ wl.args, isNewB f z = true → E z ∧ L z := by
    rcases ecr_mkTree_E hN hL hmt hw hLx hEw l hlmem with rfl | ⟨hEl, hLl⟩
    · rw [hw] at hwl
      cases hwl
      exact fun z hz hn => ⟨hEw z hz hn, (hL _ hLx _ hw).2 z hz hn⟩
    · obtain ⟨-, wl2, -, hwl2, hcl, -, -⟩ := hN l hEl
      change g.value? l = some wl2 at hwl2
      rw [hwl] at hwl2
      cases hwl2
      exact fun z hz hn => ⟨hcl z hz hn, (hL l hLl wl hwl).2 z hz hn⟩
  have hargs2 : wl.args.toList = [wl.args[0]!, wl.args[1]!] := ec_args_two hsz
  have hm0 : wl.args[0]! ∈ wl.args := by
    rw [← Array.mem_toList_iff, hargs2]; exact List.mem_cons_self
  have hm1 : wl.args[1]! ∈ wl.args := by
    rw [← Array.mem_toList_iff, hargs2]; exact List.mem_cons_of_mem _ List.mem_cons_self
  -- the address
  have hqnew : isNewB f wl.args[0]! = true := by
    unfold spOffOK at hq
    simp only [Bool.and_eq_true] at hq
    exact hq.1.1.1
  obtain ⟨hEq, hLq⟩ := hEarg _ hm0 hqnew
  have hqv := ecs_addr hN hL hq hEq hLq fun qw hqw hn => by
    have e : loadSP g l = qw.args[0]! := by unfold loadSP; rw [hwl]; simp [hqw]
    rw [← e] at hn ⊢
    exact hTH _ (hHsp hn)
  -- the memory
  have hmsH : EcTgtHolds env tabs g T wl.args[1]! := by
    cases hn : isNewB f wl.args[1]! with
    | true =>
      obtain ⟨hE1, hL1⟩ := hEarg _ hm1 hn
      exact ecs_holds_of_new hN hL hE1 hL1
    | false =>
      have e : loadMem g l = wl.args[1]! := by unfold loadMem; rw [hwl]; rfl
      rw [← e] at hn ⊢
      exact hTH _ (hHm hn)
  unfold memSelOK at hms
  cases hmw : g.value? wl.args[1]! with
  | none => rw [hmw] at hms; cases hms
  | some mw =>
  rw [hmw] at hms
  simp only [Bool.and_eq_true, beq_iff_eq] at hms
  obtain ⟨⟨⟨hmop, hmargs⟩, hmai⟩, hmsh⟩ := hms
  have hshm : shapeOf (typeShapes tabs) g wl.args[1]! = .mem := by
    split at hmsh
    · assumption
    · cases hmsh
  obtain ⟨hmid, ym, hym, hevm⟩ := hmsH mw hmw
  rw [ecT_eval_selectN hmop (regs_of_ok hevm), hmargs, List.map_cons, List.map_nil, rv_of hyc',
    ecA_selectN_tuple hmai, List.getD_eq_getElem?_getD, hDK, Option.getD_some, hmid,
    ← shapeOf_eq, hshm] at hevm
  cases hevm
  -- the leaf's evaluation
  rw [ecr_eval_load hwop (regs_of_ok hev), hargs2, List.map_cons, List.map_cons, List.map_nil,
    rv_of hqv, rv_of hym, hid, ← shapeOf_eq] at hev
  cases hev
  have hat := (mem_leaves hwf (List.mem_of_getElem? he)).2
  rw [ecr_leafVals_get hwf hrt he] at ha
  cases ha
  have hslot : (p.offset + (e.1 : Int)).toNat = p.offset.toNat + e.1 := by omega
  have h1 := GoFV.SSA.Sem.load_mono hmT (shapeOf (typeShapes tabs) g l)
    (ecsSlot (p.offset.toNat + e.1))
  rw [ecr_leaf_load hwf hrd (by omega) (List.mem_of_getElem? he) hsh'] at h1
  have h2 := Sem.retype_mono (shapeOf (typeShapes tabs) g l) h1
  have hLa : (decode (encode (tabs.ty p.type) r) e.1 e.2).retype (shapeOf (typeShapes tabs) g l) =
      decode (encode (tabs.ty p.type) r) e.1 e.2 := by
    rw [eqE_retype hsh', Val.retype_of_hasTy (decode_hasTy (wf_atom hat))]
  rw [hLa] at h2
  rw [hslot]
  exact h2

end GoFV.Proof.EC
