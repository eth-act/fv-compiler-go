import GoFV.Proof.Pass.ECWide
import GoFV.Proof.Pass.ECSlots

/-!
# `expand calls`: the function's own results (issue #28)

`expand calls` turns a `MakeResult` of the function's results into the register pieces of its
register-assigned results on a chain of new `Store`s of the leaves of its stack-assigned results
into their frame slots (`LocalAddr {result}`, `ECCheck.resultOK`); `goResults` then reads a
stack-assigned result from its slot.

* The conversion of the `MakeResult` (`convRes`) writes the encodings of the source's
  stack-assigned results into their slots (`resMem`); the target's leaf stores refine those
  writes (`ECWide.ecw_split`): `obl_result`.
* The stores evaluate where the source's `Ret` returns: their slots are writable in the source's
  final memory (`EcQ`: kept by the contracts, `Env.FrameKeep`) and so in the target's
  (`ecr_storeObl`, a `RetObl`).
* `ecRR` relates the source's results and memory to the target's pieces and a memory refining the
  slot writes: `finish` reads the slots back (`ecr_goResults_own`) and the frame is freed alike
  (`ecr_resMem_freeFrame`): `finish_ecRR`; `ret_result`.
* The slots are allocated by the entry frame (`ecr_entry`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.AtomSim

/-! ## What the checker gives -/

/-- The facts `ownOutsOK` gives about the function's own results. -/
structure EcOwn (tabs : Tables) (f : Func) : Prop where
  ok : ∀ p ∈ ownOuts tabs f, ecfOK tabs p
  distinct : namesDistinct (((ownOuts tabs f).filter (·.regs.isEmpty)).map (·.name)) = true
  pieces : (∃ p ∈ ownOuts tabs f, p.regs.isEmpty = true) →
    (leafTys tabs (ownOuts tabs f)).length ≠ (ownOuts tabs f).length
  memTy : (∃ p ∈ ownOuts tabs f, p.regs.isEmpty = true) → WBCheck.memTyOK tabs f = true
  slot : ∀ p ∈ ownOuts tabs f, p.regs.isEmpty = true → resSlotOK tabs (localsOf tabs f) p = true

theorem ecr_resSlotOK {tabs : Tables} {L : Array (AuxRef × Nat × Option Nat)} {p : ABIParam}
    (h : resSlotOK tabs L p = true) :
    wf (tabs.ty p.type) = true ∧ (tabs.ty p.type).size < 2 ^ 24 ∧ ∃ n, p.name = some n ∧
      tabs.forgeable n = true ∧ (∃ e ∈ L, e.1 = n) ∧ ∀ e ∈ L, e.1 = n → (tabs.ty p.type).size ≤ e.2.1 := by
  unfold resSlotOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hw, hs⟩, h⟩ := h
  refine ⟨hw, hs, ?_⟩
  split at h
  · next n hn =>
    simp only [Bool.and_eq_true, Array.any_eq_true, Array.all_eq_true, beq_iff_eq, Bool.or_eq_true,
      bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hf, i, hi, he⟩, hall⟩ := h
    refine ⟨n, hn, hf, ⟨_, Array.getElem_mem hi, he⟩, fun e he hen => ?_⟩
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem he
    rcases hall j hj with h | h
    · exact absurd hen h
    · exact h
  · cases h

theorem ecr_ownOuts {tabs : Tables} {f : Func} (h : ownOutsOK tabs f = true) : EcOwn tabs f := by
  unfold ownOutsOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with h | ⟨⟨⟨hall, hd⟩, hl⟩, hm⟩
  · have hreg := ecf_reg_of h
    have hns : ∀ p ∈ ownOuts tabs f, p.regs.isEmpty = false := fun p hp => (hreg p hp).1
    have hfil : (ownOuts tabs f).filter (·.regs.isEmpty) = [] :=
      List.filter_eq_nil_iff.2 fun p hp => by simp [hns p hp]
    refine ⟨fun p hp => ecfOK_of_reg (hreg p hp), by rw [hfil]; rfl, ?_, ?_, ?_⟩
    · rintro ⟨p, hp, he⟩; rw [hns p hp] at he; cases he
    · rintro ⟨p, hp, he⟩; rw [hns p hp] at he; cases he
    · intro p hp he; rw [hns p hp] at he; cases he
  · have hp' := List.all_eq_true.1 hall
    refine ⟨fun p hp => ?_, hd, fun _ => hl, fun _ => hm, fun p hp he => by
      have := hp' p hp; rw [he] at this; simpa using this⟩
    have h1 := hp' p hp
    by_cases he : p.regs.isEmpty = true
    · simp only [he, ↓reduceIte] at h1
      obtain ⟨hw, -, n, hn, -⟩ := ecr_resSlotOK h1
      exact ⟨hw, fun h => absurd he (by rw [h]; decide), fun _ => ⟨n, hn⟩⟩
    · simp only [he, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h1
      exact ⟨h1.1, fun _ => h1.2, fun h => absurd h he⟩

/-! ## The slot writes -/

/-- `resMem` with register-assigned results only writes nothing. -/
theorem ecr_resMem_reg {tabs : Tables} :
    ∀ {ps : List ABIParam}, (∀ p ∈ ps, p.regs.isEmpty = false) → ∀ (rs : List Val) (m : Mem),
      resMem tabs ps rs m = some m
  | [], _, rs, m => by cases rs <;> rfl
  | p :: ps, h, rs, m => by
    cases rs with
    | nil => rfl
    | cons r rs =>
      simp only [resMem, h p List.mem_cons_self, Bool.false_eq_true, ↓reduceIte]
      exact ecr_resMem_reg (fun q hq => h q (List.mem_cons_of_mem _ hq)) rs m

/-- Setting an element that the filter drops, over one it drops, keeps the filter. -/
theorem ecr_filter_set {α : Type} (P : α → Bool) {x : α} (hx : P x = false) :
    ∀ (l : List α) (i : Nat), (∀ y, l[i]? = some y → P y = false) → (l.set i x).filter P = l.filter P
  | [], _, _ => rfl
  | y :: l, 0, hi => by
    simp only [List.set_cons_zero, List.filter_cons, hx, hi y rfl, Bool.false_eq_true, ↓reduceIte]
  | y :: l, i + 1, hi => by
    simp only [List.set_cons_succ, List.filter_cons]
    rw [ecr_filter_set P hx l i (fun z hz => hi z (by simpa using hz))]

/-- A write into a frame variable of activation 0 changes nothing the freed frame keeps. -/
theorem ecr_freeFrame_set {m : Mem} {n : AuxRef} (a : Alloc) :
    (m.set (.local 0 n) a).freeFrame 0 = m.freeFrame 0 := by
  unfold Mem.set Mem.freeFrame
  split
  · next i hi =>
    simp only [Mem.mk.injEq, and_true]
    apply Array.toList_inj.1
    rw [Array.toList_filter, Array.toList_filter, Array.set!_eq_setIfInBounds,
      Array.toList_setIfInBounds]
    refine ecr_filter_set _ rfl _ i fun y hy => ?_
    obtain ⟨hlt, hb, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hi
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hlt] at hy
    cases hy
    have hb' : m.blocks[i].1 = .local 0 n := by simpa using hb
    rw [hb']; rfl
  · simp only [Mem.mk.injEq, and_true]
    rw [Array.filter_push]
    simp

/-- A write into a frame variable of activation 0 changes nothing the freed frame keeps. -/
theorem ecr_freeFrame_write {m m' : Mem} {n : AuxRef} {o : BitVec 64} {bs : Array Byte}
    (hw : m.write ⟨.local 0 n, o⟩ bs = some m') : m'.freeFrame 0 = m.freeFrame 0 := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true] at hw; cases hw; rfl
  simp only [he, Bool.false_eq_true, ite_false] at hw
  cases ha : m.find? (.local 0 n) with
  | none => simp only [ha] at hw; cases hw
  | some a =>
    simp only [ha, Option.bind_eq_bind, Option.bind_some] at hw
    split at hw
    · cases hw; exact ecr_freeFrame_set _
    · cases hw

/-- The slot writes change nothing the freed frame keeps. -/
theorem ecr_resMem_freeFrame {tabs : Tables} :
    ∀ {ps : List ABIParam} {rs : List Val} {m M : Mem}, resMem tabs ps rs m = some M →
      M.freeFrame 0 = m.freeFrame 0
  | [], _, _, _, h | _ :: _, [], _, _, h => by simp only [resMem, Option.some.injEq] at h; rw [h]
  | p :: ps, r :: rs, m, M, h => by
    simp only [resMem] at h
    split at h
    · split at h
      · rename_i n _
        cases hw : m.write ⟨.local 0 n, 0⟩ (encode (tabs.ty p.type) r) with
        | none => rw [hw] at h; cases h
        | some m1 =>
          rw [hw, Option.bind_some] at h
          rw [ecr_resMem_freeFrame h, ecr_freeFrame_write hw]
      · cases h
    · exact ecr_resMem_freeFrame h

/-- The slot writes keep the reads of a frame variable that is no stack-assigned result's. -/
theorem ecr_resMem_read_other {tabs : Tables} {n : AuxRef} {k : Nat} :
    ∀ {ps : List ABIParam} {rs : List Val} {m M : Mem}, resMem tabs ps rs m = some M →
      (∀ p ∈ ps, p.regs.isEmpty = true → p.name ≠ some n) →
      M.read ⟨.local 0 n, 0⟩ k = m.read ⟨.local 0 n, 0⟩ k
  | [], _, _, _, h, _ | _ :: _, [], _, _, h, _ => by
    simp only [resMem, Option.some.injEq] at h; rw [h]
  | p :: ps, r :: rs, m, M, h, hn => by
    have hn' : ∀ q ∈ ps, q.regs.isEmpty = true → q.name ≠ some n :=
      fun q hq => hn q (List.mem_cons_of_mem _ hq)
    simp only [resMem] at h
    split at h
    · rename_i hs
      split at h
      · rename_i n0 hn0
        cases hw : m.write ⟨.local 0 n0, 0⟩ (encode (tabs.ty p.type) r) with
        | none => rw [hw] at h; cases h
        | some m1 =>
          rw [hw, Option.bind_some] at h
          rw [ecr_resMem_read_other h hn']
          refine CSE.Mem.read_write_sep hw (.inr (.inr (.inl fun he => ?_)))
          cases he
          exact hn p List.mem_cons_self hs hn0
      · cases h
    · exact ecr_resMem_read_other h hn'

theorem ecr_namesDistinct_cons {n : Option AuxRef} {ns : List (Option AuxRef)}
    (h : namesDistinct (n :: ns) = true) : n ∉ ns ∧ namesDistinct ns = true := by
  simp only [namesDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun hm => ?_, h.2⟩
  have := List.contains_iff_mem.2 hm
  rw [h.1] at this; cases this

/-- **The slot writes read back**: a stack-assigned result's slot holds its encoding (the
stack-assigned results have distinct names). -/
theorem ecr_resMem_read {tabs : Tables} :
    ∀ {ps : List ABIParam} {rs : List Val} {m M : Mem}, resMem tabs ps rs m = some M →
      namesDistinct ((ps.filter (·.regs.isEmpty)).map (·.name)) = true →
      ∀ p r n, (p, r) ∈ ps.zip rs → p.regs.isEmpty = true → p.name = some n →
        M.read ⟨.local 0 n, 0⟩ (tabs.ty p.type).size = some (encode (tabs.ty p.type) r)
  | [], _, _, _, _, _, _, _, _, hm, _, _ => by simp at hm
  | _ :: _, [], _, _, _, _, _, _, _, hm, _, _ => by simp at hm
  | p0 :: ps, r0 :: rs, m, M, h, hd, p, r, n, hm, hs, hn => by
    simp only [resMem] at h
    by_cases hs0 : p0.regs.isEmpty = true
    · simp only [hs0, ↓reduceIte] at h
      simp only [List.filter_cons, hs0, ↓reduceIte, List.map_cons] at hd
      obtain ⟨hnot, hd'⟩ := ecr_namesDistinct_cons hd
      split at h
      · rename_i n0 hn0
        cases hw : m.write ⟨.local 0 n0, 0⟩ (encode (tabs.ty p0.type) r0) with
        | none => rw [hw] at h; cases h
        | some m1 =>
          rw [hw, Option.bind_some] at h
          rcases List.mem_cons.1 hm with he | hm'
          · simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            rw [hn0] at hn; cases hn
            rw [ecr_resMem_read_other h fun q hq hqs hqn => hnot (by
              rw [hn0, ← hqn]
              exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, hqs⟩, rfl⟩)]
            have := GoFV.Proof.Pass.LoadFwd.read_write_self hw
            rwa [encode_size] at this
          · exact ecr_resMem_read h hd' p r n hm' hs hn
      · cases h
    · simp only [hs0, Bool.false_eq_true, ↓reduceIte] at h
      simp only [List.filter_cons, hs0, Bool.false_eq_true, ↓reduceIte] at hd
      rcases List.mem_cons.1 hm with he | hm'
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact absurd hs hs0
      · exact ecr_resMem_read h hd p r n hm' hs hn

/-! ## `finish` reads the slots back -/

/-- A value of a well-formed shape decodes back from its encoding. -/
theorem ecr_decode_encode {t : Ty} (hw : wf t = true) {r : Val} (hr : r.hasTy t = true)
    (hp : r.hasPoison = false) : decode (encode t r) 0 t = r :=
  (ecf_refines_eq _ hw (roundtrip hw hr) hp hr).symm

/-- **The post path of `goResults`** on the retyped register pieces, from a memory whose slots
hold the stack-assigned results' encodings: each result back. -/
theorem ecr_post_own {tabs : Tables} (act : Nat) (m : Mem) :
    {ps : List ABIParam} → {rs : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      (∀ p ∈ ps, ecfOK tabs p) → Val.anyPoison rs = false →
      (∀ p r n, (p, r) ∈ ps.zip rs → p.regs.isEmpty = true → p.name = some n →
        m.read ⟨.local act n, 0⟩ (tabs.ty p.type).size = some (encode (tabs.ty p.type) r)) →
      {rts : List Ty} → List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs ps) rts →
      ∃ bufs, goResults.post act m (ecfRegs tabs ps rs rts) (ps.map (ecfOut tabs)) = .ok bufs ∧
        (bufs.zip (ps.map (ecfOut tabs))).map (fun (bs, (_, t, _)) => decode bs 0 t) = rs
  | _, _, .nil, _, _, _, _, _ => ⟨[], by
      simp only [ecfRegs, ecfPieces, List.zip_nil_left, List.flatMap_nil, List.zipWith_nil_right]
      unfold goResults.post; rfl, rfl⟩
  | p :: ps, r :: rs, .cons hr hf, hok, hp, hrd, rts, hrts => by
    simp only [Val.anyPoison, Bool.or_eq_false_iff] at hp
    have hok' : ∀ q ∈ ps, ecfOK tabs q := fun q hq => hok q (List.mem_cons_of_mem _ hq)
    have hrd' : ∀ q s n, (q, s) ∈ ps.zip rs → q.regs.isEmpty = true → q.name = some n →
        m.read ⟨.local act n, 0⟩ (tabs.ty q.type).size = some (encode (tabs.ty q.type) s) :=
      fun q s n hm => hrd q s n (by simp only [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hm)
    obtain ⟨hw, -, hname⟩ := hok p List.mem_cons_self
    cases he : p.regs.isEmpty
    · have hreg := ecfReg_of_ok (hok p List.mem_cons_self) he
      have ⟨hne, _, hlen⟩ := hreg
      obtain ⟨r1, r2, h1, h2, hQ⟩ := ecf_regs_cons (rs := rs) (r := r) hreg hrts
      obtain ⟨bufs, hb, hd⟩ := ecr_post_own act m hf hok' hp.2 hrd' h2
      have hk : p.regs.size ≠ 0 := by
        intro h0; rw [Array.isEmpty_iff_size_eq_zero.2 h0] at hne; cases hne
      have hlv : (List.zipWith Val.retype r1 (leafVals (tabs.ty p.type) r)).length = p.regs.size := by
        rw [List.length_zipWith, leafVals_length hw, ecf_forall₂_length h1, List.length_map,
          Nat.min_self, hlen]
      refine ⟨((leaves (tabs.ty p.type)).zip (List.zipWith Val.retype r1 (leafVals (tabs.ty p.type) r))).foldl
        (fun buf ((o, lt), v) => putBytes buf o (encode lt v))
        (Array.replicate (tabs.ty p.type).size Byte.poison) :: bufs, ?_, ?_⟩
      · rw [hQ, List.map_cons]
        unfold goResults.post
        simp only [beq_iff_eq, hk, ↓reduceIte, hlen, bne_self_eq_false, List.length_append,
          Bool.false_or, decide_eq_true_eq]
        have hnl : ¬ (List.zipWith Val.retype r1 (leafVals (tabs.ty p.type) r)).length +
            (ecfRegs tabs ps rs r2).length < p.regs.size := by omega
        simp only [hnl, ↓reduceIte]
        rw [List.take_left' hlv, List.drop_left' hlv, hb]
        rfl
      · simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
        refine ⟨?_, hd⟩
        show ofPieces (tabs.ty p.type) (List.zipWith Val.retype r1 (leafVals (tabs.ty p.type) r)) = r
        exact ecf_ofPieces_reg hw hr hp.1 h1
    · obtain ⟨n, hn⟩ := hname he
      rw [leafTys_cons_stack tabs he] at hrts
      obtain ⟨bufs, hb, hd⟩ := ecr_post_own act m hf hok' hp.2 hrd' hrts
      have hk : p.regs.size = 0 := Array.isEmpty_iff_size_eq_zero.1 he
      have hQ : ecfRegs tabs (p :: ps) (r :: rs) rts = ecfRegs tabs ps rs rts := by
        simp only [ecfRegs]; rw [ecf_pieces_cons_stack he]
      have hrd0 := hrd p r n (by simp) he hn
      refine ⟨encode (tabs.ty p.type) r :: bufs, ?_, ?_⟩
      · rw [hQ, List.map_cons]
        unfold goResults.post
        simp only [ecfOut, hk, beq_self_eq_true, ↓reduceIte, hn, hb]
        change Res.ok ((m.read ⟨.local act n, 0⟩ (tabs.ty p.type).size).getD
          (Array.replicate (tabs.ty p.type).size Byte.poison) :: bufs) = _
        rw [hrd0]; rfl
      · simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
        exact ⟨ecr_decode_encode hw hr hp.1, hd⟩

/-- **The target's `goResults` with stack-assigned results**: fewer or more register pieces than
results, so the post path, which reads the slots back. -/
theorem ecr_goResults_own {tabs : Tables} {ps : List ABIParam} {rs : List Val}
    {outs : Array (Option AuxRef × Ty × Nat)} (houts : outs.toList = ps.map (ecfOut tabs))
    (hf : List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs)
    (hok : ∀ p ∈ ps, ecfOK tabs p) (hpc : (leafTys tabs ps).length ≠ ps.length)
    (hp : Val.anyPoison rs = false) (act : Nat) (m : Mem)
    (hrd : ∀ p r n, (p, r) ∈ ps.zip rs → p.regs.isEmpty = true → p.name = some n →
      m.read ⟨.local act n, 0⟩ (tabs.ty p.type).size = some (encode (tabs.ty p.type) r))
    {rts : List Ty} (hrts : List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs ps) rts) :
    goResults outs act (ecfRegs tabs ps rs rts) m = .ok rs := by
  unfold goResults
  dsimp only
  rw [houts]
  have hlen : (ecfRegs tabs ps rs rts).length ≠ (ps.map (ecfOut tabs)).length := by
    rw [ecf_regs_length (ecf_forall₂_length hf) hok hrts,
      ← ecf_forall₂_length (ecf_pieces_hasTy (ecf_forall₂_length hf) hok), List.length_map]
    exact hpc
  have hpre : ((ecfRegs tabs ps rs rts).length == (ps.map (ecfOut tabs)).length &&
      ((ecfRegs tabs ps rs rts).zip (ps.map (ecfOut tabs))).all fun (v, (_, t, _)) => v.hasTy t) =
      false := by
    rw [show ((ecfRegs tabs ps rs rts).length == (ps.map (ecfOut tabs)).length) = false from
      beq_eq_false_iff_ne.2 hlen, Bool.false_and]
  simp only [hpre, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨bufs, hb, hd⟩ := ecr_post_own act m hf hok hp hrd hrts
  rw [hb]
  show (if _ then _ else _) = _
  rw [hd, Val.any_hasPoison, hp]
  rfl

/-- **`finish` relates `ecRR` outcomes**: the source's results are decoded from themselves, the
target's from its register pieces and its slots (`ecr_resMem_read`); the frame is freed alike
(`ecr_resMem_freeFrame`). -/
theorem finish_ecRR {tabs : Tables} {f : Func} (hown : EcOwn tabs f) :
    ∀ rs m rs' m', ecRR tabs f rs m rs' m' →
      (finish (Ctx.make tabs f).outs 0 (.returned rs m)).Defined →
      OutcomeRefines 0 (finish (Ctx.make tabs f).outs 0 (.returned rs m))
        (finish (Ctx.make tabs f).outs 0 (.returned rs' m')) := by
  intro rs m rs' m' ⟨hf, rts, hrts, hP, M, hM, hm⟩ hd
  have hp : Val.anyPoison rs = false := by
    cases h : Val.anyPoison rs
    · rfl
    · simp only [finish, h, ↓reduceIte] at hd; exact hd.elim
  have hwf : ∀ p ∈ ownOuts tabs f, wf (tabs.ty p.type) = true := fun p hp => (hown.ok p hp).1
  have hPp := ecf_regs_np hf hown.ok hp hrts
  have hsrc : finish (Ctx.make tabs f).outs 0 (.returned rs m) = .returned rs (m.freeFrame 0) := by
    simp only [finish, hp, Bool.false_eq_true, ↓reduceIte,
      ecf_goResults_src (ecf_outs tabs f) hf hwf hp 0 m]
  have hgo : goResults (Ctx.make tabs f).outs 0 (ecfRegs tabs (ownOuts tabs f) rs rts) M = .ok rs := by
    by_cases hs : ∃ p ∈ ownOuts tabs f, p.regs.isEmpty = true
    · exact ecr_goResults_own (ecf_outs tabs f) hf hown.ok (hown.pieces hs) hp 0 M
        (ecr_resMem_read hM hown.distinct) hrts
    · have hreg : ∀ p ∈ ownOuts tabs f, ecfReg tabs p := fun p hp' =>
        ecfReg_of_ok (hown.ok p hp') (by
          cases h : p.regs.isEmpty
          · rfl
          · exact absurd ⟨p, hp', h⟩ hs)
      exact ecf_goResults_reg (ecf_outs tabs f) hf hreg hp hrts 0 M
  have hmid : finish (Ctx.make tabs f).outs 0 (.returned (ecfRegs tabs (ownOuts tabs f) rs rts) M) =
      .returned rs (m.freeFrame 0) := by
    simp only [finish, hPp, Bool.false_eq_true, ↓reduceIte, hgo, ecr_resMem_freeFrame hM]
  have h1 : OutcomeRefines 0 (finish (Ctx.make tabs f).outs 0 (.returned rs m))
      (finish (Ctx.make tabs f).outs 0 (.returned (ecfRegs tabs (ownOuts tabs f) rs rts) M)) := by
    rw [hsrc, hmid]; exact OutcomeRefines.refl trivial
  have h2 := finish_refines (outs := (Ctx.make tabs f).outs) (act := 0) (k := 0)
    (by rw [hmid]; trivial) (OutcomeRefines.returned hP hm)
  exact h1.trans h2

/-! ## The `Ret` control: a `MakeResult` -/

/-- Writable slots take the slot writes. -/
theorem ecr_resMem_some_of {tabs : Tables} {ctx : Ctx} (hact : ctx.act = 0) :
    ∀ {ps : List ABIParam}, (∀ p ∈ ps, p.regs.isEmpty = true →
      (∃ n, p.name = some n) ∧ ecfOut tabs p ∈ ctx.outs.toList) →
      ∀ (rs : List Val) {m : Mem}, SlotsOK ctx m → ∃ M, resMem tabs ps rs m = some M
  | [], _, rs, m, _ => ⟨m, by cases rs <;> rfl⟩
  | _ :: _, _, [], m, _ => ⟨m, rfl⟩
  | p :: ps, h, r :: rs, m, hS => by
    have h' := fun q hq => h q (List.mem_cons_of_mem _ hq)
    by_cases hs : p.regs.isEmpty = true
    · obtain ⟨⟨n, hn⟩, ho⟩ := h p List.mem_cons_self hs
      have hcw : m.canWrite ⟨.local 0 n, 0⟩ (encode (tabs.ty p.type) r).size = true := by
        rw [encode_size]
        by_cases h0 : (tabs.ty p.type).size = 0
        · rw [h0]; unfold Mem.canWrite; simp
        · have ho' : (some n, tabs.ty p.type, 0) ∈ ctx.outs.toList := by
            have hk : p.regs.size = 0 := Array.isEmpty_iff_size_eq_zero.1 hs
            simpa [ecfOut, hn, hk] using ho
          have := hS n (tabs.ty p.type) ho' (by omega)
          rwa [hact] at this
      obtain ⟨m1, hw⟩ := ecs_write_of_canWrite hcw
      obtain ⟨M, hM⟩ := ecr_resMem_some_of hact h' rs ((slotsOK_pred ctx).write hS hw)
      exact ⟨M, by simp only [resMem, hs, ↓reduceIte, hn, hw, Option.bind_some, hM]⟩
    · obtain ⟨M, hM⟩ := ecr_resMem_some_of hact h' rs hS
      exact ⟨M, by simp only [resMem, hs, Bool.false_eq_true, ↓reduceIte, hM]⟩

/-- **The slot writes succeed** on a memory with the result slots (`EcQ`). -/
theorem ecr_resMem_some {tabs : Tables} {f : Func} (hown : EcOwn tabs f) {m : Mem}
    (hq : EcQ tabs f m) (rs : List Val) : ∃ M, resMem tabs (ownOuts tabs f) rs m = some M := by
  by_cases hs : ∃ p ∈ ownOuts tabs f, p.regs.isEmpty = true
  · refine ecr_resMem_some_of rfl (fun p hp he => ⟨(hown.ok p hp).2.2 he, ?_⟩) rs (hq (hown.memTy hs))
    rw [ecf_outs]; exact List.mem_map_of_mem hp
  · exact ⟨m, ecr_resMem_reg (fun p hp => by
      cases h : p.regs.isEmpty
      · rfl
      · exact absurd ⟨p, hp, h⟩ hs) rs m⟩

/-- **The `Ret` control of `expand calls`** (a converted `MakeResult`): the target returns the
register pieces of the source's results, retyped at the target `MakeResult`'s register shapes
(`regTupleOf`), and a memory refining the source's with the stack-assigned results in their
slots (`convRes`; the slot writes succeed by `EcQ`). -/
theorem ret_result {tabs : Tables} {f g : Func} {c : ID} {u w : Value}
    (hu : f.value? c = some u) (hw : g.value? c = some w) (hop : u.op = .MakeResult)
    (hok : resultOK tabs (typeShapes tabs) f g u w = true) (hown : EcOwn tabs f) :
    ∀ y y', RegOK (Ctx.make tabs f) c y → Sem.Refines (ecCv tabs f g c y) y' →
      ∀ rs m, retOf y = some (rs, m) → Val.anyPoison rs = false → EcQ tabs f m →
        ∃ rs' m', retOf y' = some (rs', m') ∧ ecRR tabs f rs m rs' m' := by
  intro y y' hry hyy rs m hro hp hq
  unfold resultOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hwop, hn⟩, -⟩, -⟩, -⟩, -⟩, htup⟩, hrt⟩ := hok
  obtain ⟨us, hus, husl, hue, -⟩ := ecf_tupleOf htup
  obtain ⟨rts, hus', hrts⟩ := ecf_regTupleOf hrt
  obtain ⟨hty, hlen, -⟩ := hry
  rw [tys_of_value hu, Option.getD_some, ← ecf_valueTy, hus] at hty
  cases y with
  | tuple vs =>
    have hvs := hlen u vs hu hop rfl
    have hvs' : vs = rs ++ [.mem m] := ecf_retOf_inv hro
    subst hvs'
    have hrl : rs.length = (ownOuts tabs f).length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hvs; omega
    have hF := ecf_hasTyPre_results (tabs := tabs) hrl hty (by rw [husl, List.length_map]) hue
    have hPt := ecf_pieces_hasTy (tabs := tabs) hrl hown.ok
    have hlen' : rts.length = (ecfPieces tabs (ownOuts tabs f) rs).length :=
      (ecf_forall₂_length hrts).trans (ecf_forall₂_length hPt)
    obtain ⟨M, hM⟩ := ecr_resMem_some hown hq rs
    rw [ecc_cv_result hu hop (ecf_not_invalidated hw (by rw [hwop]; decide)), ecf_convRes hrl, hM,
      shapeOf, hw, hus'] at hyy
    dsimp only at hyy
    rw [ecf_retype_tuple hlen'] at hyy
    cases hyy with
    | tuple hl =>
      obtain ⟨c1, c2, rfl, h1, h2⟩ := ecf_refinesList_append_inv hl
      cases h2 with
      | cons hm hnil =>
        cases hnil
        cases hm with
        | mem hm =>
          have hQp := ecf_regs_np hF hown.ok hp hrts
          exact ⟨c1, _, ecf_retOf ((h1.noPoison hQp).1) _, hF, rts, hrts, h1, M, hM, hm⟩
  | _ => simp [retOf] at hro

/-! ## The `MakeResult`: register pieces and slot stores -/

theorem ecr_zip_fst_snd {α β : Type} : ∀ (l : List (α × β)), (l.map (·.1)).zip (l.map (·.2)) = l
  | [] => rfl
  | (a, b) :: l => by simp only [List.map_cons, List.zip_cons_cons, ecr_zip_fst_snd l]

/-- `argPairs`, mapped: the zip of the parameters and the mapped arguments, filtered. -/
theorem ecr_argPairs_zip {reg : Bool} {β : Type} (F : ID → β) :
    ∀ {ps : List ABIParam} {as : List ID}, as.length = ps.length →
      ((argPairs reg ps as).map (·.1)).zip (((argPairs reg ps as).map (·.2)).map F) =
        (ps.zip (as.map F)).filter fun e => !e.1.regs.isEmpty == reg
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp at h
  | p :: ps, a :: as, h => by
    have ih := ecr_argPairs_zip (reg := reg) F (ps := ps) (as := as) (by simpa using h)
    unfold argPairs at ih ⊢
    simp only [List.zip_cons_cons, List.map_cons, List.filter_cons]
    split <;> simp_all

theorem ecr_argPairs_fst {reg : Bool} {ps : List ABIParam} {as : List ID} (h : as.length = ps.length) :
    (argPairs reg ps as).map (·.1) = ps.filter fun p => !p.regs.isEmpty == reg := by
  have := congrArg (List.map (·.1)) (ecr_argPairs_zip (reg := reg) id h)
  rw [List.map_fst_zip (by simp)] at this
  rw [this, List.map_id]
  clear this
  induction ps generalizing as with
  | nil => rfl
  | cons p ps ih =>
    cases as with
    | nil => simp at h
    | cons a as =>
      simp only [List.map_cons, List.zip_cons_cons, List.filter_cons, id]
      split <;> simp_all

theorem ecr_argPairs_mem {reg : Bool} {ps : List ABIParam} {as : List ID} {e : ABIParam × ID}
    (h : e ∈ argPairs reg ps as) : e.1 ∈ ps ∧ e.2 ∈ as ∧ (!e.1.regs.isEmpty == reg) = true := by
  unfold argPairs at h
  obtain ⟨hz, hp⟩ := List.mem_filter.1 h
  exact ⟨(List.of_mem_zip hz).1, (List.of_mem_zip hz).2, hp⟩

/-- The register pieces of the results are the leaves of the register-assigned ones. -/
theorem ecr_pieces_filter (tabs : Tables) :
    ∀ (l : List (ABIParam × Val)), l.flatMap (fun (p, r) => regLeafVals tabs p r) =
      (l.filter fun e => !e.1.regs.isEmpty == true).flatMap fun (p, r) => leafVals (tabs.ty p.type) r
  | [] => rfl
  | (p, r) :: l => by
    rw [List.flatMap_cons, ecr_pieces_filter tabs l]
    cases h : p.regs.isEmpty
    · rw [List.filter_cons_of_pos (by simp [h]), List.flatMap_cons]; dsimp only
      rw [regLeafVals_reg h]
    · rw [List.filter_cons_of_neg (by simp [h])]; dsimp only
      rw [regLeafVals_stack h, List.nil_append]

/-- The shapes `piecesOK` checks: each argument's is its parameter's. -/
theorem ecr_piecesOK_eqE {tabs : Tables} {sh : Array Ty} {f g : Func} :
    ∀ (ps : List ABIParam) (as pcs : List ID), piecesOK tabs sh f g ps as pcs = true →
      ∀ e ∈ ps.zip as, eqE (shapeOf sh f e.2) (tabs.ty e.1.type) = true
  | [], _, _, _, e, he | _ :: _, [], _, _, e, he => by simp at he
  | p :: ps, a :: as, pcs, h, e, he => by
    unfold piecesOK at h
    simp only [Bool.and_eq_true] at h
    simp only [List.zip_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact h.1.1.1.1
    · exact ecr_piecesOK_eqE ps as _ h.2 e he

theorem ecr_forall₂_of_zip {P : ABIParam → Val → Prop} (F : ID → Val) :
    ∀ {ps : List ABIParam} {as : List ID}, as.length = ps.length → (∀ e ∈ ps.zip as, P e.1 (F e.2)) →
      List.Forall₂ P ps (as.map F)
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp at h
  | p :: ps, a :: as, hl, h =>
    .cons (h (p, a) (by simp)) (ecr_forall₂_of_zip F (by simpa using hl)
      fun e he => h e (by simp only [List.zip_cons_cons]; exact List.mem_cons_of_mem _ he))

/-- **The results have their shapes**, from the shapes `piecesOK` checks for the register- and
the stack-assigned ones. -/
theorem ecr_forall₂_hasTy {tabs : Tables} {f g : Func} {frS T : Frame} {outs : List ABIParam}
    {as : List ID} {pcs qs : List ID} (hl : as.length = outs.length)
    (hrp : piecesOK tabs (typeShapes tabs) f g ((argPairs true outs as).map (·.1))
      ((argPairs true outs as).map (·.2)) pcs = true)
    (hsp : piecesOK tabs (typeShapes tabs) f g ((argPairs false outs as).map (·.1))
      ((argPairs false outs as).map (·.2)) qs = true)
    (hrel : ∀ a ∈ as, EcArgRel tabs f g frS T a) :
    List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) outs
      (as.map (rv frS)) := by
  refine ecr_forall₂_of_zip _ hl fun e he => ?_
  have heq : eqE (shapeOf (typeShapes tabs) f e.2) (tabs.ty e.1.type) = true := by
    cases hr : (!e.1.regs.isEmpty == true)
    · have hm : e ∈ argPairs false outs as := List.mem_filter.2 ⟨he, by simpa using hr⟩
      exact ecr_piecesOK_eqE _ _ _ hsp e (by rw [ecr_zip_fst_snd]; exact hm)
    · have hm : e ∈ argPairs true outs as := List.mem_filter.2 ⟨he, hr⟩
      exact ecr_piecesOK_eqE _ _ _ hrp e (by rw [ecr_zip_fst_snd]; exact hm)
  obtain ⟨y, hyS, hry, -⟩ := hrel e.2 (List.of_mem_zip he).2
  rw [rv_of hyS]
  have := hry.1
  rw [← shapeOf_eq, eqE_hasTy heq] at this
  exact this

/-- The writes of the leaf slots `S` (result `n`'s slot at offset `o`, of shape `lt`) of the
values `xs`. -/
def ecrSlotWrites (S : List (AuxRef × Nat × Ty)) (xs : List Val) : List (Ptr × Array Byte) :=
  (S.zip xs).map fun e => ((⟨.local 0 e.1.1, 0⟩ : Ptr).add (BitVec.ofNat 64 e.1.2.1), encode e.1.2.2 e.2)

theorem ecr_slotWrites_leaves (n : AuxRef) :
    ∀ (L : List (Nat × Ty)) (xs : List Val),
      ecrSlotWrites (L.map fun (o, lt) => (n, o, lt)) xs = ecwLeafWrites ⟨.local 0 n, 0⟩ L xs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | (o, lt) :: L, x :: xs => by
    have ih := ecr_slotWrites_leaves n L xs
    unfold ecrSlotWrites ecwLeafWrites at ih ⊢
    simp only [List.map_cons, List.zip_cons_cons, ih]

theorem ecr_slotWrites_append {S1 S2 : List (AuxRef × Nat × Ty)} {xs1 xs2 : List Val}
    (h : S1.length = xs1.length) :
    ecrSlotWrites (S1 ++ S2) (xs1 ++ xs2) = ecrSlotWrites S1 xs1 ++ ecrSlotWrites S2 xs2 := by
  simp [ecrSlotWrites, List.zip_append h]

theorem ecr_resSlots_cons (tabs : Tables) (p : ABIParam) (ps : List ABIParam) :
    resSlots tabs (p :: ps) = (match p.name with
      | some n => (leaves (tabs.ty p.type)).map fun (o, lt) => (n, o, lt)
      | none => []) ++ resSlots tabs ps := by
  simp only [resSlots, List.flatMap_cons]; rfl

theorem ecr_resSlots_mem {tabs : Tables} :
    ∀ {ps : List ABIParam} {e : AuxRef × Nat × Ty}, e ∈ resSlots tabs ps →
      ∃ p ∈ ps, p.name = some e.1 ∧ (e.2.1, e.2.2) ∈ leaves (tabs.ty p.type)
  | [], _, h => by simp [resSlots] at h
  | p :: ps, e, h => by
    rw [ecr_resSlots_cons] at h
    rcases List.mem_append.1 h with h | h
    · cases hn : p.name with
      | none => rw [hn] at h; cases h
      | some n =>
        rw [hn] at h
        obtain ⟨⟨o, lt⟩, hl, rfl⟩ := List.mem_map.1 h
        exact ⟨p, List.mem_cons_self, hn, hl⟩
    · obtain ⟨q, hq, h1, h2⟩ := ecr_resSlots_mem h
      exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩

/-- **The slot stores refine the slot writes**: the leaf writes of pieces refining the
stack-assigned results' leaves, on a memory refining the source's, refine `resMem`
(`ECWide.ecw_split` per result). -/
theorem ecr_split {tabs : Tables} :
    ∀ {ps : List ABIParam} {rs : List Val} {m M m' : Mem} {xs : List Val},
      resMem tabs ps rs m = some M → Mem.Refines m m' →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      (∀ p ∈ ps, wf (tabs.ty p.type) = true) →
      RefinesList (((ps.zip rs).filter fun e => !e.1.regs.isEmpty == false).flatMap
        fun (p, r) => leafVals (tabs.ty p.type) r) xs →
      ∃ MT, writeAll m' (ecrSlotWrites (resSlots tabs (ps.filter fun p => !p.regs.isEmpty == false)) xs) =
        some MT ∧ Mem.Refines M MT
  | [], _, m, M, m', xs, h, hm, .nil, _, hx => by
    simp only [resMem, Option.some.injEq] at h; subst h
    cases hx; exact ⟨m', rfl, hm⟩
  | p :: ps, r :: rs, m, M, m', xs, h, hm, .cons hr hf, hwf, hx => by
    have hwf' := fun q hq => hwf q (List.mem_cons_of_mem _ hq)
    by_cases hs : p.regs.isEmpty = true
    · simp only [resMem, hs, ↓reduceIte] at h
      split at h
      · rename_i n hn
        cases hw : m.write ⟨.local 0 n, 0⟩ (encode (tabs.ty p.type) r) with
        | none => rw [hw] at h; cases h
        | some m1 =>
          rw [hw, Option.bind_some] at h
          rw [List.zip_cons_cons, List.filter_cons_of_pos (by simp [hs]), List.flatMap_cons] at hx
          obtain ⟨x1, x2, rfl, h1, h2⟩ := ecf_refinesList_append_inv hx
          have hw0 := hwf p List.mem_cons_self
          obtain ⟨MT1, hW1, hR1⟩ := ecw_split _ hw0 r hr ⟨.local 0 n, 0⟩ m m' m1 x1 hm hw h1
          obtain ⟨MT, hW, hR⟩ := ecr_split h hR1 hf hwf' h2
          refine ⟨MT, ?_, hR⟩
          have hlen : ((leaves (tabs.ty p.type)).map fun (o, lt) => (n, o, lt)).length = x1.length := by
            rw [List.length_map, ← h1.length_eq, leafVals_length hw0]
          rw [List.filter_cons_of_pos (by simp [hs]), ecr_resSlots_cons, hn]
          dsimp only
          rw [ecr_slotWrites_append hlen, ecr_slotWrites_leaves, writeAll_append hW1, hW]
      · cases h
    · simp only [resMem, hs, Bool.false_eq_true, ↓reduceIte] at h
      have hs' : p.regs.isEmpty = false := by simpa using hs
      simp only [List.zip_cons_cons, List.filter_cons, hs', Bool.not_false, beq_iff_eq,
        Bool.true_eq_false, ↓reduceIte] at hx
      obtain ⟨MT, hW, hR⟩ := ecr_split h hm hf hwf' hx
      refine ⟨MT, ?_, hR⟩
      simp only [List.filter_cons, hs', Bool.not_false, beq_iff_eq, Bool.true_eq_false, ↓reduceIte]
      exact hW

/-- The facts of the result stores (`resStoresOK`), per store. -/
theorem ecr_resStores_get {tabs : Tables} {sh : Array Ty} {g : Func} {nw : ID → Bool} :
    ∀ {ss : List (AuxRef × Nat × Ty)} {zs : List ID}, resStoresOK tabs sh g nw ss zs = true →
      ss.length = zs.length ∧ ∀ (k : Nat) z, zs[k]? = some z → ∃ n o lt zw, ss[k]? = some (n, o, lt) ∧
        g.value? z = some zw ∧ 0 < lt.size ∧ eqE (auxTy tabs zw.aux) lt = true ∧
        localAddrOK sh g nw n (resBase g o zw.args[0]!) = true ∧
        wideAddrOK sh g nw (resBase g o zw.args[0]!) o zw.args[0]! = true ∧ shapeOf sh g z = .mem
  | [], [], _ => ⟨rfl, fun _ _ h => by simp at h⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [resStoresOK] at h
  | (n, o, lt) :: ss, z :: zs, h => by
    simp only [resStoresOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hl, hg⟩ := ecr_resStores_get h2
    refine ⟨by simp [hl], fun k z' hk => ?_⟩
    cases k with
    | zero =>
      cases hk
      cases hz : g.value? z with
      | none => rw [hz] at h1; cases h1
      | some zw =>
        rw [hz] at h1
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨⟨⟨⟨hpos, haux⟩, hla⟩, ha⟩, hsh⟩ := h1
        refine ⟨n, o, lt, zw, rfl, rfl, hpos, haux, hla, ha, ?_⟩
        split at hsh
        · assumption
        · cases hsh
    | succ k => exact hg k z' hk

/-- The base of a leaf address is a new value of `E` when the address is. -/
theorem ecr_base_EL {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    {p a : ID} {o : Nat} (hok : wideAddrOK (typeShapes tabs) g (isNewB f) p o a = true)
    (hEa : isNewB f a = true → E a ∧ L a) : isNewB f p = true → E p ∧ L p := by
  intro hp
  unfold wideAddrOK at hok
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
  rcases hok with ⟨-, rfl⟩ | ⟨hn, hm⟩
  · exact hEa hp
  · obtain ⟨hEa, hLa⟩ := hEa hn
    obtain ⟨-, aw, -, haw, hcl, -⟩ := hNC a hEa
    change g.value? a = some aw at haw
    rw [haw] at hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    have hpa : p ∈ aw.args := by rw [← Array.mem_toList_iff, hm.1.2]; simp
    exact ⟨hcl p hpa hp, (hL a hLa aw haw).2 p hpa hp⟩

/-- A new `LocalAddr {n}` of a `Blk.local` variable (`forgeable`) holds the start of the
variable's frame block of activation 0. -/
theorem ecr_localAddr {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    {n : AuxRef} {p : ID} (hok : localAddrOK (typeShapes tabs) g (isNewB f) n p = true)
    (hfg : tabs.forgeable n = true) (hEL : isNewB f p = true → E p ∧ L p) :
    rv T p = .ptr ⟨.local 0 n, 0⟩ := by
  unfold localAddrOK at hok
  rw [Bool.and_eq_true] at hok
  obtain ⟨hn, hm⟩ := hok
  obtain ⟨hEp, hLp⟩ := hEL hn
  obtain ⟨-, pw, y, hpw, -, hy, hev⟩ := hNC p hEp
  change g.value? p = some pw at hpw
  rw [hpw] at hm
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨hop, hax⟩, hsh⟩ := hm
  have hid := (hL p hLp pw hpw).1
  rw [evalValue_of_regs (regs_of_ok hev)] at hev
  have he : evalOp env (Ctx.make tabs g) T pw (pw.args.toList.map (rv T))
      ((Ctx.make tabs g).tys[pw.id]?.getD .other) = .ok (.ptr ⟨.local 0 n, 0⟩) := by
    have hb : frameBlk (Ctx.make tabs g).tabs (Ctx.make tabs g).act n = .local 0 n := by
      unfold frameBlk; rw [show (Ctx.make tabs g).tabs = tabs from rfl, hfg]; rfl
    delta evalOp frameVal; rw [hop, hax]; simp only [Option.map_some, hb]; rfl
  rw [he] at hev
  cases hev
  rw [rv_of hy, hid, ← shapeOf_eq]
  split at hsh
  · rename_i e he'
    rw [he']; rfl
  · cases hsh

theorem ecr_retype_poison (t : Ty) (y : Val) : Sem.Refines (Val.retype t .poison) y := by
  have : Val.retype t .poison = .poison := by cases t <;> rfl
  rw [this]; exact .poison _

/-- A `MakeResult` tuple whose last component is no memory converts to `poison`. -/
theorem ecr_convRes_nonmem {tabs : Tables} {ps : List ABIParam} {rs : List Val} {v : Val}
    (hv : ∀ m, v ≠ .mem m) : convRes tabs ps (.tuple (rs ++ [v])) = .poison := by
  unfold convRes
  dsimp only
  rw [List.getLast?_concat]
  show (match some v with
    | some (.mem m) => _
    | _ => Val.poison) = _
  cases v with
  | mem m => exact absurd rfl (hv m)
  | _ => rfl

/-- **The `MakeResult` obligation** with the `IMake` facts: the target's register pieces refine
the source's results' (`ec_pieces` on the register-assigned ones), and its result stores, from a
memory refining the source's, write leaves refining the stack-assigned results' (`ec_pieces` on
the stored values) at their slots (`ecr_localAddr`, `ECWide.ecw_addr`), so its memory refines the
slot writes (`ecr_split`, `convRes`). -/
theorem obl_result_imk {tabs : Tables} {f g : Func} {x : ID} {u w : Value}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hop : u.op = .MakeResult)
    (hok : resultOK tabs (typeShapes tabs) f g u w = true) (hown : EcOwn tabs f) (huid : u.id = x)
    (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    EcOblImk tabs f g (fun _ => False) (fun _ => False) x := by
  intro u' w' hu' hw' env _ frS T _ hRS E hNC hEw hRw hRu hfront himk _ _
  rw [hu] at hu'; cases hu'
  rw [hw] at hw'; cases hw'
  unfold resultOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hwop, hn⟩, hws⟩, hmsp⟩, hrp⟩, hst⟩, htup⟩, hrt⟩ := hok
  cases hzs : resStores f g u w with
  | none => rw [hzs] at hst; cases hst
  | some zs =>
  rw [hzs] at hst
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Array.contains_iff_mem] at hst
  obtain ⟨⟨hrs, hsp⟩, hsv⟩ := hst
  have hsu := ecc_args_split1 u.args (by omega)
  have hsw := ecc_args_split1 w.args hws
  have hi : invalidated g x = false := by
    unfold invalidated; rw [hw]; dsimp only; rw [hwop]; decide
  have hasl : (u.args.extract 0 (u.args.size - 1)).toList.length = (ownOuts tabs f).length := by
    simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
      List.length_take, Array.length_toList]
    omega
  have hmemu : ∀ a ∈ (u.args.extract 0 (u.args.size - 1)).toList, a ∈ u.args :=
    fun a ha => Array.mem_toList_iff.1 (ecc_mem_of_split hsu ha)
  have hrel : ∀ a ∈ (u.args.extract 0 (u.args.size - 1)).toList, EcArgRel tabs f g frS T a :=
    fun a ha => ecc_argRel hi hu hRS hRu hfront (hmemu a ha)
  have hG := ecr_forall₂_hasTy hasl hrp hsp hrel
  have hwf : ∀ p ∈ ownOuts tabs f, wf (tabs.ty p.type) = true := fun p hp => (hown.ok p hp).1
  -- the register pieces
  have hP := ec_pieces hNC hL hRS _ _ _ hrp
    (fun p hp => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
      exact hwf _ (ecr_argPairs_mem he).1)
    (fun q hq => hRw q (Array.mem_toList_iff.1 (ecc_mem_of_split hsw hq)))
    (fun q hq hn' => have hq' := Array.mem_toList_iff.1 (ecc_mem_of_split hsw hq)
      ⟨hEw q hq' hn', (hL x hLx w hw).2 q hq' hn'⟩)
    (fun a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      exact hrel _ (ecr_argPairs_mem he).2.1)
    (fun a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      exact himk _ (hmemu _ (ecr_argPairs_mem he).2.1))
    (fun q hq yq hyq hn' => hfront q (ecFront_tgt hi hw
      (Array.mem_toList_iff.1 (ecc_mem_of_split hsw hq)) hn') yq hyq)
  rw [ecr_argPairs_zip _ hasl, ← ecr_pieces_filter] at hP
  -- the chain of result stores
  have hch : storeChain g (isNewB f) (g.valueTab.size + 1) w.args[w.args.size - 1]!
      u.args[u.args.size - 1]! = some zs := hzs
  have hwl : w.args[w.args.size - 1]! ∈ w.args := by rw [← Array.mem_toList_iff, hsw]; simp
  have hELt : zs ≠ [] → E w.args[w.args.size - 1]! ∧ L w.args[w.args.size - 1]! := fun hne => by
    have hn' := ecs_storeChain_new hch hne
    exact ⟨hEw _ hwl hn', (hL x hLx w hw).2 _ hwl hn'⟩
  have hELz := ecs_chain_E hNC hL _ hch hELt
  have hsp1 := ecr_argPairs_fst (reg := false) hasl
  rw [hsp1] at hrs
  obtain ⟨-, hget⟩ := ecr_resStores_get hrs
  have hshs : ∀ z ∈ zs, shapeOf (typeShapes tabs) g z = .mem := fun z hz => by
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hz
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := hget k z hk
    exact h
  -- the stored values refine the stack-assigned results' leaves
  have hzsv : ∀ q ∈ zs.map (storeVal g), ∃ wz : Value, q ∈ wz.args ∧
      (∀ a ∈ wz.args, Reg T a) ∧ (∀ a ∈ wz.args, isNewB f a = true → E a ∧ L a) := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hq
    obtain ⟨hEz, hLz⟩ := hELz z hz
    obtain ⟨-, wz, yz, hwz, hcl, -, hev⟩ := hNC z hEz
    change g.value? z = some wz at hwz
    obtain ⟨wz', -, -, hwz', -, -, hsz', -⟩ := ecs_chain_mem hch hz
    rw [hwz] at hwz'; cases hwz'
    refine ⟨wz, ?_, regs_of_ok hev, fun a ha hn' => ⟨hcl a ha hn', (hL z hLz wz hwz).2 a ha hn'⟩⟩
    have hsv' : storeVal g z = wz.args[1]! := by unfold storeVal; rw [hwz]; rfl
    rw [hsv']; exact ecw_mem_three hsz' 1 (by decide)
  have hS := ec_pieces hNC hL hRS _ _ _ hsp
    (fun p hp => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
      exact hwf _ (ecr_argPairs_mem he).1)
    (fun q hq => by
      obtain ⟨wz, hq', hreg, -⟩ := hzsv q hq
      exact hreg q hq')
    (fun q hq hn' => by
      obtain ⟨wz, hq', -, hEL⟩ := hzsv q hq
      exact hEL q hq' hn')
    (fun a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      exact hrel _ (ecr_argPairs_mem he).2.1)
    (fun a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      exact himk _ (hmemu _ (ecr_argPairs_mem he).2.1))
    (fun q hq yq hyq hn' => by
      have hqu : q ∈ u.args := by
        rcases hsv q hq with h | h
        · rw [hn'] at h; cases h
        · exact h
      exact hfront q (ecFront_src hi hu hqu) yq hyq)
  rw [ecr_argPairs_zip _ hasl] at hS
  -- the evaluations
  have hm : u.args[u.args.size - 1]! ∈ u.args := by rw [← Array.mem_toList_iff, hsu]; simp
  have hRw' : ∀ a ∈ w.args, Reg T a := hRw
  have hwid := (hL x hLx w hw).1
  rw [evalValue_of_regs hRu, evalValue_of_regs hRw', evalOp_term (by rw [hop]; decide),
    evalOp_term (by rw [hwop]; decide), hop, hwop, GoFV.Proof.Rules.opVal_pure (by decide),
    GoFV.Proof.Rules.opVal_pure (by decide), ecc_evalPure_result, ecc_evalPure_result,
    huid, hwid, tys_of_value hu, tys_of_value hw, Option.getD_some, Option.getD_some, hsu, hsw,
    List.map_append, List.map_append, List.map_cons, List.map_cons, List.map_nil, List.map_nil]
  refine .ok ?_
  obtain ⟨us, hus, husl, hue, hul⟩ := ecf_tupleOf htup
  rw [ecf_valueTy] at hus
  rw [hus]
  show Sem.Refines (ecCv tabs f g x (match Val.retypePre us _ with
    | some vs' => Val.tuple vs'
    | none => Val.poison)) _
  rw [ecc_retypePre hG hue (by rw [husl, List.length_map]) hul]
  dsimp only
  rw [ecc_cv_result hu hop hi]
  -- the source's memory
  cases hmv : rv frS u.args[u.args.size - 1]! with
  | mem m0 =>
    obtain ⟨M0', hM0T, hM0R⟩ := ecw_front_mem hmsp hmv (hRu _ hm)
      (hfront _ (ecFront_src hi hu hm))
    obtain ⟨MT, hMT, hWT, hpt⟩ := ecw_chain hNC hL _ hch hELt hshs M0' hM0T
    rw [hMT, show Val.retype .mem (.mem m0) = .mem m0 from rfl,
      ecf_convRes (by rw [List.length_map, hasl])]
    cases hM : resMem tabs (ownOuts tabs f)
        ((u.args.extract 0 (u.args.size - 1)).toList.map (rv frS)) m0 with
    | none => exact ecr_retype_poison _ _
    | some M =>
      dsimp only
      obtain ⟨MT', hWT', hR⟩ := ecr_split hM hM0R hG hwf hS
      -- the target's writes are the slot writes
      have hlist : zs.map (ecwW tabs g T) =
          ecrSlotWrites (resSlots tabs ((ownOuts tabs f).filter fun p => !p.regs.isEmpty == false))
            ((zs.map (storeVal g)).map (rv T)) := by
        apply List.ext_getElem?
        intro k
        unfold ecrSlotWrites
        rw [List.getElem?_map, List.getElem?_map]
        cases hk : zs[k]? with
        | none =>
          have hn' : ((resSlots tabs ((ownOuts tabs f).filter fun p => !p.regs.isEmpty == false)).zip
              ((zs.map (storeVal g)).map (rv T)))[k]? = none := by
            rw [List.getElem?_eq_none_iff] at hk ⊢
            simp only [List.length_zip, List.length_map]
            omega
          rw [hn']; rfl
        | some z =>
          obtain ⟨n, o, lt, zw, hle, hzw, -, haux, hla, haddr, -⟩ := hget k z hk
          have hz : ((resSlots tabs ((ownOuts tabs f).filter fun p => !p.regs.isEmpty == false)).zip
              ((zs.map (storeVal g)).map (rv T)))[k]? = some ((n, o, lt), rv T (storeVal g z)) :=
            List.getElem?_zip_eq_some.2 ⟨hle, by rw [List.getElem?_map, List.getElem?_map, hk]; rfl⟩
          rw [hz]
          simp only [Option.map_some, ecwW, hzw]
          have hsv' : storeVal g z = zw.args[1]! := by unfold storeVal; rw [hzw]; rfl
          obtain ⟨hEzz, hLzz⟩ := hELz z (List.mem_of_getElem? hk)
          obtain ⟨zw', -, -, hzw', -, -, hzsz, -⟩ := ecs_chain_mem hch (List.mem_of_getElem? hk)
          rw [hzw] at hzw'; cases hzw'
          obtain ⟨-, zw', -, hzw'', hcl, -, -⟩ := hNC z hEzz
          change g.value? z = some zw' at hzw''
          rw [hzw] at hzw''; cases hzw''
          have hq0 := ecw_mem_three hzsz 0 (by decide)
          have hEa : isNewB f zw.args[0]! = true → E zw.args[0]! ∧ L zw.args[0]! := fun hn' =>
            ⟨hcl _ hq0 hn', (hL z hLzz zw hzw).2 _ hq0 hn'⟩
          -- the slot's variable is a `Blk.local`
          obtain ⟨p, hp, hpn, -⟩ := ecr_resSlots_mem (List.mem_of_getElem? hle)
          obtain ⟨hpo, hps⟩ := List.mem_filter.1 hp
          obtain ⟨-, -, n', hn', hfg, -⟩ := ecr_resSlotOK (hown.slot p hpo (by simpa using hps))
          rw [hpn] at hn'; cases hn'
          have hbase := ecr_localAddr hNC hL hla hfg (ecr_base_EL hNC hL haddr hEa)
          have hP' := ecw_ptr_eq (ecw_addr hNC hL haddr hbase hEa)
            (hpt z (List.mem_of_getElem? hk) zw hzw)
          rw [hP', hsv', ecw_encode_eqE haux]
      rw [← hlist, hWT] at hWT'
      cases hWT'
      rw [shapeOf, hw, ecf_valueTy]
      exact retype_mono _ (.tuple (RefinesList.append hP (.cons (.mem hR) .nil)))
  | _ =>
    all_goals
      rw [ecr_convRes_nonmem (by intro m h; cases h)]
      exact ecr_retype_poison _ _

/-- **The `MakeResult` obligation.** -/
theorem obl_result {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hop : u.op = .MakeResult)
    (hok : resultOK tabs (typeShapes tabs) f g u w = true) (hown : EcOwn tabs f) (huid : u.id = x)
    (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hH : ∀ a ∈ u.args, EcoImkHeld tabs f g HS HT a) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x :=
  obl_of_imk (obl_result_imk hu hw hop hok hown huid L hLx hL) hu hH (fun _ h => h.elim)
    fun _ h => h.elim

/-! ## The result stores evaluate -/

theorem ecr_retypePre_last {t : Ty} {v : Val} :
    ∀ {us : List Ty} {vs vs' : List Val}, Val.retypePre us (vs ++ [v]) = some vs' →
      us.length = vs.length + 1 → us.getLast? = some t → vs'.getLast? = some (v.retype t)
  | [], _, _, _, hl, _ => by simp at hl
  | [u], [], vs', h, _, hl => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    simp only [List.nil_append, Val.retypePre, Option.map_some, Option.some.injEq] at h
    subst h; rfl
  | [_], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _ :: _, [], _, _, hl, _ => by simp at hl
  | u :: u' :: us, a :: vs, vs', h, hl, ht => by
    simp only [List.cons_append, Val.retypePre] at h
    cases h' : Val.retypePre (u' :: us) (vs ++ [v]) with
    | none => rw [h'] at h; cases h
    | some ws =>
      rw [h', Option.map_some, Option.some.injEq] at h
      subst h
      have ih := ecr_retypePre_last h' (by simpa using hl) (by simpa using ht)
      have hne : ws ≠ [] := by intro h0; rw [h0] at ih; cases ih
      rw [List.getLast?_cons_of_ne_nil hne, ih]

/-- **The obligation of a result store** (`RetObl`, against the block's `MakeResult` control
`x`): once the source completes the block, its `Ret` reads a memory whose result slots are
writable (`EcQ`), so is the target's below the store (`Mem.Refines`; the stores below keep the
allocations), and the store's address is in its slot (`ecr_localAddr`, `ECWide.ecw_addr`). -/
theorem ecr_storeObl {tabs : Tables} {f g : Func} {x z : ID} {u w : Value} {HT : ID → Prop}
    (hu : f.value? x = some u) (huid : u.id = x)
    (hop : u.op = .MakeResult) (hok : resultOK tabs (typeShapes tabs) f g u w = true)
    (hown : EcOwn tabs f) {zs : List ID} (hzs : resStores f g u w = some zs) (hz : z ∈ zs)
    (L : ID → Prop)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hLz : L z) :
    RetObl tabs f g (ecCv tabs f g) (isNewB f) [u.args[u.args.size - 1]!] HT x z := by
  intro wz hwz env G T _ E hNC hEw hRw hfront _ hsrc hret hQ
  unfold resultOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hn⟩, -⟩, hmsp⟩, -⟩, hst⟩, htup⟩, -⟩ := hok
  rw [hzs] at hst
  simp only [Bool.and_eq_true] at hst
  obtain ⟨⟨hrs, -⟩, -⟩ := hst
  have hsu := ecc_args_split1 u.args (by omega)
  have hasl : (u.args.extract 0 (u.args.size - 1)).toList.length = (ownOuts tabs f).length := by
    simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
      List.length_take, Array.length_toList]
    omega
  rw [ecr_argPairs_fst (reg := false) hasl] at hrs
  obtain ⟨-, hget⟩ := ecr_resStores_get hrs
  have hm : u.args[u.args.size - 1]! ∈ u.args := by rw [← Array.mem_toList_iff, hsu]; simp
  -- the source's memory at the `Ret`
  obtain ⟨-, y, hy, hev⟩ := hsrc u hu
  obtain ⟨rs, m, hro⟩ := hret y hy
  have hRu := regs_of_ok hev
  obtain ⟨us, hus, husl, -, hul⟩ := ecf_tupleOf htup
  rw [ecf_valueTy] at hus
  rw [evalValue_of_regs hRu, evalOp_term (by rw [hop]; decide), hop,
    GoFV.Proof.Rules.opVal_pure (by decide), ecc_evalPure_result, huid, tys_of_value hu,
    Option.getD_some, hsu, List.map_append, List.map_cons, List.map_nil, hus] at hev
  have hy' := (Res.ok.inj hev).symm
  rw [hy'] at hro
  have hmv : rv G u.args[u.args.size - 1]! = .mem m := by
    simp only [Val.retype] at hro
    split at hro
    · rename_i vs' hpre
      have hl := ecr_retypePre_last hpre (by rw [husl, List.length_map, List.length_map, hasl]) hul
      rw [ecf_retOf_inv hro, List.getLast?_concat, Option.some.injEq] at hl
      cases hv : rv G u.args[u.args.size - 1]! with
      | mem m' => rw [hv] at hl; cases hl; rfl
      | _ => rw [hv] at hl; cases hl
    · simp [retOf] at hro
  have hGm : G.regs[u.args[u.args.size - 1]!]? = some (some (.mem m)) := by
    rw [← hmv]; exact reg_rv (hRu _ hm)
  obtain ⟨M0', hM0T, hM0R⟩ := ecw_front_mem hmsp hmv (hRu _ hm) (hfront _ (List.mem_singleton_self _))
  -- `z` in the chain
  have hch : storeChain g (isNewB f) (g.valueTab.size + 1) w.args[w.args.size - 1]!
      u.args[u.args.size - 1]! = some zs := hzs
  obtain ⟨wz', n', zs', hwz', -, hzop, hzsz, hc, rest, hsplit⟩ := ecs_chain_mem hch hz
  rw [hwz] at hwz'; cases hwz'
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hz
  obtain ⟨n, o, lt, zw, hle, hzw, hpos, haux, hla, haddr, hsh⟩ := hget k z hk
  rw [hwz] at hzw; cases hzw
  obtain ⟨hwid, hLcl⟩ := hL z hLz wz hwz
  have hzargs := ecs_args_three hzsz
  have hEL : zs' ≠ [] → E wz.args[2]! ∧ L wz.args[2]! := fun hne => by
    have hn := ecs_storeChain_new hc hne
    exact ⟨hEw _ (ecw_mem_three hzsz 2 (by decide)) hn, hLcl _ (ecw_mem_three hzsz 2 (by decide)) hn⟩
  have hshs' : ∀ z' ∈ zs', shapeOf (typeShapes tabs) g z' = .mem := fun z' hz' => by
    obtain ⟨k', hk'⟩ := List.getElem?_of_mem (show z' ∈ zs by rw [hsplit]; simp [hz'])
    obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := hget k' z' hk'
    exact h
  obtain ⟨Mb, hMb, hWb, -⟩ := ecw_chain hNC hL n' hc hEL hshs' M0' hM0T
  -- the slot is writable
  obtain ⟨p, hp, hpn, hpl⟩ := ecr_resSlots_mem (List.mem_of_getElem? hle)
  obtain ⟨hpo, hps⟩ := List.mem_filter.1 hp
  have hps' : p.regs.isEmpty = true := by simpa using hps
  obtain ⟨hwfp, -, n', hn', hfg, -⟩ := ecr_resSlotOK (hown.slot p hpo hps')
  rw [hpn] at hn'; cases hn'
  have hol : o + lt.size ≤ (tabs.ty p.type).size := (mem_leaves hwfp hpl).1
  have hout : (some n, tabs.ty p.type, 0) ∈ (Ctx.make tabs f).outs.toList := by
    rw [ecf_outs]
    exact List.mem_map.2 ⟨p, hpo, by simp [ecfOut, hpn, Array.isEmpty_iff_size_eq_zero.1 hps']⟩
  have hcw0 : m.canWrite ⟨.local 0 n, 0⟩ (tabs.ty p.type).size = true :=
    hQ _ _ hGm (hown.memTy ⟨p, hpo, hps'⟩) n _ hout (by omega)
  rw [← hM0R.canWrite, ← ecs_canWrite_congr (writeAll_attr hWb)] at hcw0
  have hcw := ecs_canWrite_sub (k := o) (l := lt.size) hol
    (show Mb.canWrite ⟨.local 0 n, BitVec.ofNat 64 0⟩ _ = true from hcw0) (Nat.two_pow_pos 64)
  have hqa : (⟨.local 0 n, 0⟩ : Ptr).add (BitVec.ofNat 64 o) = ⟨.local 0 n, BitVec.ofNat 64 (0 + o)⟩ := by
    simp [Ptr.add]
  obtain ⟨Mfull, hWfull⟩ := ecs_write_of_canWrite (m := Mb) (p := ⟨.local 0 n, 0⟩)
    (bs := Array.replicate (tabs.ty p.type).size Byte.poison) (by rw [Array.size_replicate]; exact hcw0)
  have hwin : ((⟨.local 0 n, 0⟩ : Ptr).add (BitVec.ofNat 64 o)).inWindow = true :=
    StructStore.inWindow_of_write hWfull (by rw [Array.size_replicate]; omega)
  -- the store's address
  have hq0 := ecw_mem_three hzsz 0 (by decide)
  have hEa : isNewB f wz.args[0]! = true → E wz.args[0]! ∧ L wz.args[0]! := fun hn' =>
    ⟨hEw _ hq0 hn', hLcl _ hq0 hn'⟩
  have hbase := ecr_localAddr hNC hL hla hfg (ecr_base_EL hNC hL haddr hEa)
  have ha : rv T wz.args[0]! = .ptr ((⟨.local 0 n, 0⟩ : Ptr).add (BitVec.ofNat 64 o)) := by
    rcases ecw_addr hNC hL haddr hbase hEa with h | h
    · exact h
    · rw [h]; unfold PtrOps.ptrRes; rw [if_pos hwin]
  -- the write
  have hsz' : (encode (auxTy tabs wz.aux) (rv T wz.args[1]!)).size = lt.size := by
    rw [encode_size, ecT_eqE_size haux]
  obtain ⟨M2, hW2⟩ := ecs_write_of_canWrite (m := Mb)
    (p := (⟨.local 0 n, 0⟩ : Ptr).add (BitVec.ofNat 64 o))
    (bs := encode (auxTy tabs wz.aux) (rv T wz.args[1]!)) (by rw [hsz', hqa]; exact hcw)
  have htyz : (Ctx.make tabs g).tys[wz.id]?.getD .other = .mem := by
    rw [hwid, ← shapeOf_eq]; exact hsh
  exact ⟨_, ecs_store_eval hzop hRw hzargs htyz ha hMb hW2⟩

/-! ## The entry frame allocates the slots -/

/-- Setting the frame allocations of variables `l`, each of its size, gives variable `n` (a
`Blk.local`) a writable allocation of at least `sz0` bytes when one of them is `n` and each of
them that is `n` has at least `sz0` bytes. -/
theorem ecr_foldl_slot {tabs : Tables} {n : AuxRef} {sz0 : Nat} (hf : tabs.forgeable n = true)
    (step : Mem → AuxRef × Nat × Option Nat → Mem)
    (hstep : ∀ m e, ∃ d : Array Byte, step m e = m.set (frameBlk tabs 0 e.1) { data := d } ∧
      d.size = e.2.1) :
    ∀ (l : List (AuxRef × Nat × Option Nat)) (m : Mem), (∀ e ∈ l, e.1 = n → sz0 ≤ e.2.1) →
      ((∃ e ∈ l, e.1 = n) ∨
        ∃ a, m.find? (.local 0 n) = some a ∧ a.writable = true ∧ sz0 ≤ a.data.size) →
      ∃ a, (l.foldl step m).find? (.local 0 n) = some a ∧ a.writable = true ∧ sz0 ≤ a.data.size
  | [], m, _, h => by
    rcases h with ⟨e, he, -⟩ | h
    · cases he
    · exact h
  | e :: l, m, hl, h => by
    rw [List.foldl_cons]
    refine ecr_foldl_slot hf step hstep l _ (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) ?_
    obtain ⟨d, hd, hds⟩ := hstep m e
    rw [hd, CSE.Mem.find?_set]
    by_cases he : e.1 = n
    · right
      rw [if_pos (by rw [he]; exact frameBlk_local hf 0)]
      exact ⟨_, rfl, rfl, by rw [hds]; exact hl e List.mem_cons_self he⟩
    · rcases h with ⟨e', he', hen⟩ | ⟨a, ha, hw, hs⟩
      · rcases List.mem_cons.1 he' with rfl | he'
        · exact absurd hen he
        · exact .inl ⟨e', he', hen⟩
      · right
        have hne : frameBlk tabs 0 e.1 ≠ .local 0 n := by
          unfold frameBlk
          split
          · intro h; cases h; exact he rfl
          · intro h; cases h
        rw [if_neg hne]
        exact ⟨a, ha, hw, hs⟩

theorem ecr_foldl_canWrite {tabs : Tables} {n : AuxRef} {sz0 : Nat} (hf : tabs.forgeable n = true)
    (hlt : sz0 < 2 ^ 24) (step : Mem → AuxRef × Nat × Option Nat → Mem)
    (hstep : ∀ m e, ∃ d : Array Byte, step m e = m.set (frameBlk tabs 0 e.1) { data := d } ∧
      d.size = e.2.1)
    (l : List (AuxRef × Nat × Option Nat)) (m : Mem) (hl : ∀ e ∈ l, e.1 = n → sz0 ≤ e.2.1)
    (hex : ∃ e ∈ l, e.1 = n) : (l.foldl step m).canWrite ⟨.local 0 n, 0⟩ sz0 = true := by
  obtain ⟨a, ha, hw, hs⟩ := ecr_foldl_slot hf step hstep l m hl (.inl hex)
  unfold Mem.canWrite
  rw [ha]
  have hw' : sz0 < 2 ^ 64 := by omega
  have h0 : ((⟨.local 0 n, 0⟩ : Ptr).off.toNat) = 0 := rfl
  have hwin : (Blk.local 0 n).endsInWindow sz0 = true := by
    simp only [Blk.endsInWindow, Blk.window?, decide_eq_true_eq]; omega
  simp only [h0, Nat.zero_add, hw, hwin, Bool.true_and, Bool.and_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  right; simp only [Bool.and_eq_true, decide_eq_true_eq, hs, hw', and_self]

/-- **The entry frame allocates the result slots** (`resSlotOK`: each stack-assigned result's
variable is a `Blk.local` listed among the frame variables, each listing at least the result's
size, inside the frame blocks' window). -/
theorem ecr_entry {tabs : Tables} {f : Func} (hown : EcOwn tabs f) (env : Env) (args : List Val)
    (mem : Mem) : EcQ tabs f (entryFrame env (Ctx.make tabs f) args mem).mem0 := by
  intro _ n t ho hpos
  rw [ecf_outs] at ho
  obtain ⟨p, hp, hpe⟩ := List.mem_map.1 ho
  simp only [ecfOut, Prod.mk.injEq] at hpe
  obtain ⟨hpn, hpt, hpk⟩ := hpe
  have hps : p.regs.isEmpty = true := Array.isEmpty_iff_size_eq_zero.2 hpk
  obtain ⟨-, hlt, n', hn', hfg, ⟨e0, he0, he0n⟩, hle⟩ := ecr_resSlotOK (hown.slot p hp hps)
  rw [hpn] at hn'; cases hn'
  subst hpt
  show Mem.canWrite (frameAllocs (Ctx.make tabs f) _ _) ⟨.local 0 n, 0⟩ _ = true
  unfold frameAllocs
  dsimp only
  rw [← Array.foldl_toList]
  refine ecr_foldl_canWrite hfg hlt _ ?_ (Ctx.make tabs f).locals.toList _
    (fun e he hen => hle e (Array.mem_toList_iff.1 he) hen)
    ⟨e0, Array.mem_toList_iff.2 he0, he0n⟩
  intro m e
  obtain ⟨n', sz, pi⟩ := e
  refine ⟨_, rfl, ?_⟩
  dsimp only
  split
  · split
    · rename_i h; simpa using h
    · simp
  · simp

end GoFV.Proof.EC
