import GoFV.Proof.Pass.LoadFwdFixed
import GoFV.Proof.Pass.LoadFwdMoveSrc
import GoFV.Proof.Pass.RewriteTerm
import GoFV.Proof.AtomSim

/-!
# Load-of-Store forwarding refines its input (issues #151, #69)

`fwd_refines`: if `RewriteCheck.fwdRel tabs f g` (`g` is `f` with Loads replaced by `Copy x` of
the value a `Store` wrote, through `Store`s at disjoint addresses, at a pointer equal to the
Load's, and memory roots whose write changes no byte replaced by `Copy` of their memory, every
other value unchanged), `g` refines `f` under monotone contracts whose malloc-family contracts
return zeroed blocks (`Env.AllocZero`) from initial memories with the read-only symbols `ro`
(`RoImage`, for `newobject`'s type sizes, `fwdRoOK`), by the generalised atom simulation
(`AtomSim.atomSimXE_refines`, invariant `fwdInv`: constants' registers hold their values, fresh
malloc calls' registers their zeroed blocks). Its premises hold because every value listed in
`f` is refined by the same value in `g` as a term (`fwd_den`), for valuations whose memory roots
hold the writes of their arguments and whose `LocalAddr`s their frame variables (`MemAtoms`): by
induction on `fwdRank` (a replaced Load's stored value ranks below it), a replaced Load reads,
through the writes of the disjoint `Store`s (`disjoint_sep`, `load_write_sep`), the write of the
stored value's term at the Load's pointer (`samePtr_den`), and reads that value back
(`load_write`): `chain_load`; a dropped root's write is refined by its memory (`drop_mem`).
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.Pass.Rewrite GoFV.Proof.CSE.Mem

/-- What `fwdRel` (with the read-only symbols `ro`) establishes. -/
structure FwdFacts (tabs : Tables) (ro : List (String × Alloc)) (f g : Func) : Prop where
  atoms : atomsXOK f g = true
  cf : closedOK f = true
  cg : closedOK g = true
  blocks : g.blocks = f.blocks
  bext : ∀ b ∈ f.blocks, ∀ fb, f.block? b = some fb → ∃ gb, g.block? b = some gb ∧
    gb = { fb with values := gb.values } ∧ ∀ x ∈ fb.values, x ∈ gb.values
  rank : fwdRankOK f (fwdRank f) = true
  rep : ∀ x < f.valueTab.size, fwdRepOK tabs ro f g x = true

theorem blocksExtOK_spec {f g : Func} (h : blocksExtOK f g = true) :
    g.blocks = f.blocks ∧ ∀ b ∈ f.blocks, ∀ fb, f.block? b = some fb → ∃ gb,
      g.block? b = some gb ∧ gb = { fb with values := gb.values } ∧ ∀ x ∈ fb.values, x ∈ gb.values := by
  unfold blocksExtOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun b hb fb hfb => ?_⟩
  have := (Array.all_eq_true_iff_forall_mem.1 h.2) b hb
  rw [hfb] at this
  cases hgb : g.block? b with
  | none => rw [hgb] at this; cases this
  | some gb =>
    rw [hgb] at this
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem,
      Array.contains_iff_mem] at this
    exact ⟨gb, rfl, this.1, this.2⟩

theorem fwdRel_spec {tabs : Tables} {ro : List (String × Alloc)} {f g : Func}
    (h : fwdRel tabs ro f g = true) : FwdFacts tabs ro f g := by
  unfold fwdRel at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h6⟩, h7⟩ := h
  have h45 := blocksExtOK_spec h4
  exact ⟨h1, h2, h3, h45.1, h45.2, h6, h7⟩

/-- The rank of a listed non-`Phi` value is above its arguments'. -/
theorem fwdRankOK_spec {f : Func} {rk : Array Nat} (h : fwdRankOK f rk = true) {z : ID}
    (hz : LM f z)
    {u : Value} (hu : f.value? z = some u) (hph : u.op ≠ .Phi) :
    ∀ a ∈ u.args, rk[a]?.getD 0 < rk[z]?.getD 0 := by
  unfold fwdRankOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  have := h z (lt_of_value? hu)
  rw [hu] at this
  simp only [LM] at hz
  rcases this with h1 | h1
  · exact absurd hz h1
  · simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hph
    · intro a ha
      simpa using (Array.all_eq_true_iff_forall_mem.1 h1) a ha

mutual
/-- `fwdErase` keeps how a shape retypes. -/
theorem fwdErase_retype : (t : Ty) → Val.retype (fwdErase t) = Val.retype t
  | .ptr e => funext fun v => retype_ptr_elem none e v
  | .slice e => by
    funext v
    cases v <;> try rfl
    rename_i vs
    rcases vs with _ | ⟨p, _ | ⟨l, _ | ⟨c, _ | ⟨d, vs⟩⟩⟩⟩ <;> rfl
  | .agg fs n => by
    funext v
    cases v <;> first | rfl | simp only [fwdErase, Val.retype, fwdEraseFields_retype fs]
  | .int _ | .bool | .blob _ | .empty | .opaque _ | .other | .mem | .tuple _ | .str => rfl
theorem fwdEraseFields_retype : (fs : List (Nat × Ty)) →
    Val.retypeFields (fwdEraseFields fs) = Val.retypeFields fs
  | [] => rfl
  | (o, t) :: fs => by
    funext vs
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [fwdEraseFields, Val.retypeFields, fwdErase_retype t, fwdEraseFields_retype fs]
end

/-- `fwdTyEq` shapes retype alike. -/
theorem fwdTyEq_retype {t s : Ty} (h : fwdTyEq t s = true) : Val.retype t = Val.retype s := by
  simp only [fwdTyEq, Bool.and_eq_true] at h
  rw [← fwdErase_retype t, ← fwdErase_retype s, Ty.eq_of_beq h.2]

theorem fwdTyEq_fwdTy {t s : Ty} (h : fwdTyEq t s = true) : fwdTy t = true := by
  simp only [fwdTyEq, Bool.and_eq_true] at h
  exact h.1

mutual
/-- `fwdErase` keeps how a shape encodes. -/
theorem fwdErase_encode : (t : Ty) → (v : Val) → encode (fwdErase t) v = encode t v
  | .ptr _, v => by
    cases v with
    | int w x => cases w <;> rfl
    | _ => rfl
  | .slice _, v => by cases v <;> rfl
  | .agg fs n, v => by
    cases v <;> first | rfl | simp only [fwdErase, encode, fwdEraseFields_encode fs]
  | .int _, _ | .bool, _ | .blob _, _ | .empty, _ | .opaque _, _ | .other, _ | .mem, _
  | .tuple _, _ | .str, _ => rfl
theorem fwdEraseFields_encode : (fs : List (Nat × Ty)) → (buf : Array Byte) → (vs : List Val) →
    encodeFields buf (fwdEraseFields fs) vs = encodeFields buf fs vs
  | [], _, _ => rfl
  | _ :: _, _, [] => rfl
  | (o, t) :: fs, buf, v :: vs => by
    simp only [fwdEraseFields, encodeFields, fwdErase_encode t v, fwdEraseFields_encode fs]
end

/-- `fwdTyEq` shapes encode alike. -/
theorem fwdTyEq_encode {t s : Ty} (h : fwdTyEq t s = true) (v : Val) :
    encode s v = encode t v := by
  simp only [fwdTyEq, Bool.and_eq_true] at h
  rw [← fwdErase_encode t, ← fwdErase_encode s, Ty.eq_of_beq h.2]

/-- A `Store` at shape `s` (`fwdStoreTy t s`) writes a value of shape `t` as a write at `t`. -/
theorem fwdStoreTy_encode {t s : Ty} (h : fwdStoreTy t s = true) {v : Val} (hv : v.retype t = v) :
    encode s v = encode t v := by
  unfold fwdStoreTy at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨hp, hs⟩
  · exact fwdTyEq_encode h v
  · obtain ⟨e, rfl⟩ : ∃ e, t = .ptr e := by cases t <;> simp_all [isPtrTy]
    obtain rfl : s = .int .w64 := by
      revert hs
      cases s <;> first | (intro hs; cases hs) | skip
      rename_i w
      cases w <;> first | (intro; rfl) | (intro hs; cases hs)
    rcases ptr_fixed (t := .ptr e) rfl hv with rfl | ⟨x, rfl⟩ | ⟨q, rfl⟩ <;> rfl


/-- A `Move`'s copy: two pointer words, a memory, the bytes read at the source and the written
memory. -/
theorem memDef_move {tabs : Tables} {s : Value} (hs : s.op = .Move)
    {a b c y : Val} (h : memDef tabs s [a, b, c] = some y) :
    ∃ d q m0 bs M', a.asPtrWord = some d ∧ b.asPtrWord = some q ∧ c = .mem m0 ∧
      m0.read q s.auxInt.toInt.toNat = some bs ∧ m0.write d bs = some M' ∧ y = .mem M' := by
  cases c <;> try (simp [memDef, hs] at h; done)
  rename_i m0
  simp only [memDef, hs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨d, hd, q, hq, bs, hr, M', hw, rfl⟩ := h
  exact ⟨d, q, m0, bs, M', hd, hq, rfl, hr, hw, rfl⟩

theorem listedB_spec {g : Func} {y : ID} (h : listedB g y = true) : listedDefs g y = g.value? y := by
  unfold listedB at h
  unfold listedDefs
  cases hv : g.value? y with
  | none => rfl
  | some v =>
    rw [hv] at h
    simp only [Option.any_some] at h
    simp only [Option.filter, h, ite_true]

theorem fwdMoveOK_spec {tabs : Tables} {f : Func} {u top offp : Value}
    (h : fwdMoveOK tabs f u top offp = true) :
    u.op = .Load ∧ u.args.size = 2 ∧ top.op = .Load ∧ top.type = u.type ∧ top.args.size = 2 ∧
    offp.op = .OffPtr ∧ offp.args.size = 1 ∧ isPtrTy (tabs.ty offp.type) = true ∧
    0 ≤ offp.auxInt.toInt ∧ 0 < (tabs.ty u.type).size ∧ ∃ mv, f.value? u.args[1]! = some mv ∧
    mv.op = .Move ∧ mv.args.size = 3 ∧ top.args[1]! = mv.args[2]! ∧ offp.args[0]! = mv.args[1]! ∧
    offp.auxInt.toInt.toNat + (tabs.ty u.type).size ≤ mv.auxInt.toInt.toNat ∧
    (ptrBase tabs f 8 u.args[0]!).2 =
      (ptrBase tabs f 8 mv.args[0]!).2 + BitVec.ofInt 64 offp.auxInt.toInt ∧
    baseSameB tabs f 8 (ptrBase tabs f 8 u.args[0]!).1 (ptrBase tabs f 8 mv.args[0]!).1 = true := by
  unfold fwdMoveOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
  split at h
  · next mv hmv =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩ := h
    exact ⟨mv, hmv, g1, g2, g3, g4, g5, g6, g7⟩
  · cases h

theorem fwdMoveRep_spec {tabs : Tables} {f g : Func} {u w : Value}
    (h : fwdMoveRep tabs f g u w = true) :
    w.op = .Copy ∧ w.args.size = 1 ∧ listedB g w.args[0]! = true ∧ ∃ top,
      g.value? w.args[0]! = some top ∧ top.args.size = 2 ∧ listedB g top.args[0]! = true ∧
      ∃ offp, g.value? top.args[0]! = some offp ∧ fwdMoveOK tabs f u top offp = true := by
  unfold fwdMoveRep at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  split at h
  · next top htop =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨g1, g2⟩, h⟩ := h
    split at h
    · next offp hoffp => exact ⟨top, htop, g1, g2, offp, hoffp, h⟩
    · cases h
  · cases h

theorem ofInt_nonneg {i : Int} (h : 0 ≤ i) : BitVec.ofInt 64 i = BitVec.ofNat 64 i.toNat := by
  have := BitVec.ofInt_natCast 64 i.toNat
  rwa [Int.toNat_of_nonneg h] at this

/-- The arguments of a list of values are refined by some fuel. -/
theorem fuel_list {α : Type} {F : α → Val} {G : Nat → α → Val}
    (hG : ∀ a m m', m ≤ m' → Sem.Refines (G m a) (G m' a)) :
    ∀ l : List α, (∀ a ∈ l, ∃ m, Sem.Refines (F a) (G m a)) →
      ∃ m, ∀ a ∈ l, Sem.Refines (F a) (G m a)
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, h => by
    obtain ⟨m1, h1⟩ := h a List.mem_cons_self
    obtain ⟨m2, h2⟩ := fuel_list hG l fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨max m1 m2, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h1.trans (hG _ _ _ (Nat.le_max_left _ _))
    · exact (h2 b hb).trans (hG _ _ _ (Nat.le_max_right _ _))

theorem const64Op_cases {op : Op} (h : const64Op op = true) : op = .Const64 ∨ op = .Const64F := by
  unfold const64Op at h
  simpa only [Bool.or_eq_true, beq_iff_eq] using h

theorem const64_term {op : Op} (h : const64Op op = true) : termOp op = true := by
  rcases const64Op_cases h with rfl | rfl <;> rfl

/-- `Const64` and `Const64F` denote the 64-bit integer of their auxint. -/
theorem opVal_const64 {tabs : Tables} {op : Op} (h : const64Op op = true) (ty : Ty) (ai : Int64)
    (ax : Option AuxRef) (args : List Val) :
    GoFV.Proof.Rules.opVal tabs op ty ai ax args = .int .w64 (BitVec.ofInt 64 ai.toInt) := by
  rcases const64Op_cases h with rfl | rfl <;>
    rw [GoFV.Proof.Rules.opVal_pure rfl] <;> rfl

theorem fwdConstOK_spec {tabs : Tables} {f : Func} {u w : Value}
    (h : fwdConstOK tabs f u w = true) :
    u.op = .Load ∧ u.args.size = 2 ∧ const64Op w.op = true ∧ ∃ c cv, f.value? c = some cv ∧
      const64Op cv.op = true ∧ cv.auxInt = w.auxInt ∧
      fwdTyEq (tabs.ty u.type) (tabs.ty cv.type) = true ∧ fwdOK tabs f u c = true := by
  unfold fwdConstOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hld, hsz⟩, hwc⟩, -⟩, h⟩ := h
  refine ⟨hld, hsz, hwc, ?_⟩
  split at h
  · next c _ =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨h, hok⟩ := h
    split at h
    · next cv hcv =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hcc, hai⟩, hty⟩ := h
      exact ⟨c, cv, hcv, hcc, hai, hty, hok⟩
    · cases h
  · cases h

theorem storedOK_spec {tabs : Tables} {f : Func} {t : Ty} {a x : ID}
    (h : storedOK tabs f t a x = true) :
    ∃ av, f.value? a = some av ∧ copyReach tabs f.valueTab f.valueTab.size a x = true ∧
      fwdTyEq t (tabs.ty av.type) = true := by
  unfold storedOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hcr, h⟩ := h
  split at h
  · next av hav => exact ⟨av, hav, hcr, h⟩
  · cases h

/-- **A `Load` through a `Store` chain** (`fwdChain`): the memory read at the Load's pointer
holds, through the disjoint writes, the write of the stored value, which it reads back. -/
theorem chain_load {tabs : Tables} {f : Func} {ρ : ID → Val} (hT : Term.Typed f.value? tabs ρ)
    (hM : MemAtoms f.value? tabs ρ) {p x : ID} {t : Ty} {kp : Nat} {P : Ptr}
    (hp : (den f.value? tabs ρ kp p).asPtrWord = some P) :
    ∀ (d : Nat) (m : ID), fwdChain tabs f p t x d m = true → ∀ {k : Nat} {M : Mem},
      den f.value? tabs ρ k m = .mem M → ∃ K, Sem.Refines (M.load t P) (den f.value? tabs ρ K x)
  | 0, _, h, _, _, _ => by simp [fwdChain] at h
  | d + 1, m, h, k, M, hm => by
    unfold fwdChain at h
    cases hs : f.value? m with
    | none => rw [hs] at h; cases h
    | some s =>
    cases hx : f.value? x with
    | none => rw [hs, hx] at h; cases h
    | some xv =>
    rw [hs, hx] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hcop, hcsz⟩, hch⟩ | ⟨⟨hsop, hssz⟩, h⟩
    · -- a `Copy` of memory
      have ht : termOp s.op = true := by rw [hcop]; rfl
      cases k with
      | zero => simp [den] at hm
      | succ k =>
      rw [den_succ_term hs ht, toList_one hcsz, List.map_cons, List.map_nil, hcop,
        GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy] at hm
      have hm' : den f.value? tabs ρ k s.args[0]! = .mem M := retype_eq_mem hm
      exact chain_load hT hM hp d _ hch hm'
    have hmem : memOp s.op = true := by rcases hsop with h | h <;> rw [h] <;> rfl
    -- `ρ` holds the `Store`'s write
    cases k with
    | zero => simp [den] at hm
    | succ k =>
    have hsat : ¬ IsTerm f.value? m := not_term_of hs (by rw [memOp_not_term hmem]; decide)
    rw [den_succ_atom hsat] at hm
    obtain ⟨N, hN⟩ := hM m s hs hmem (by rw [hm]; nofun)
    obtain ⟨y, hy, hρs⟩ := hN N (Nat.le_refl _)
    rw [toList_three hssz, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hy
    obtain ⟨q, m0, M', hq, hm0, hwr, rfl⟩ := memDef_store hsop hy
    rw [hm] at hρs
    have hMM := retype_mem hρs.symm
    subst hMM
    rcases h with ⟨⟨⟨⟨hst, hsame⟩, hsty⟩, -⟩⟩ | ⟨hdis, hch⟩
    · -- the `Store` of a value standing for `x` at the Load's pointer
      obtain ⟨av, hav, hcr, haty⟩ := storedOK_spec hst
      rw [samePtr_den hM hsame hp hq]
      have hak : (den f.value? tabs ρ N s.args[1]!).retype t = den f.value? tabs ρ N s.args[1]! := by
        rw [fwdTyEq_retype haty]; exact den_fix hT hav N
      rw [fwdStoreTy_encode hsty hak] at hwr
      exact ⟨N, (load_write (fwdTyEq_fwdTy haty) hak hwr).trans
        (copyReach_den (M := f.valueTab) hT _ _ _ hcr N)⟩
    · -- a `Store` at a disjoint pointer
      have hsep := disjoint_sep hM hdis hp hq
      rw [load_write_sep hwr (by rw [GoFV.Proof.CSE.Mem.encode_size]; exact hsep)]
      exact chain_load hT hM hp d _ hch hm0

/-- **A memory reached through listed copies of `g`** (`memCopyReach`) holds what its start
holds (only a memory retypes to a memory, `retype_eq_mem`). -/
theorem memCopyReach_den {g : Func} {tabs : Tables} {ρ : ID → Val} :
    ∀ (N : Nat) {a w : ID}, memCopyReach g N a w = true → ∀ {k : Nat} {M : Mem},
      den (listedDefs g) tabs ρ k a = .mem M → ∃ k', den (listedDefs g) tabs ρ k' w = .mem M
  | 0, a, w, h, k, M, hk => by
    simp only [memCopyReach, beq_iff_eq] at h; subst h; exact ⟨k, hk⟩
  | N + 1, a, w, h, k, M, hk => by
    unfold memCopyReach at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with rfl | ⟨hl, h⟩
    · exact ⟨k, hk⟩
    cases hx : g.value? a with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hop, hsz⟩, hr⟩ := h
      have hL : listedDefs g a = some x := by rw [listedB_spec hl, hx]
      cases k with
      | zero => simp [den] at hk
      | succ k =>
        rw [den_succ_term hL (by rw [hop]; rfl), hop, toList_one hsz, List.map_cons, List.map_nil,
          GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy] at hk
        exact memCopyReach_den N hr (retype_eq_mem hk)

section
variable {tabs : Tables} {ro : List (String × Alloc)} {f g : Func} (F : FwdFacts tabs ro f g)
include F

/-- A value listed in `f` is listed in `g`, as `g`'s value. -/
theorem marked_g {x : ID} {u w : Value} (hx : LM f x) (hu : f.value? x = some u)
    (hw : g.value? x = some w) (hwb : w.block = u.block) : listedDefs g x = some w := by
  obtain ⟨b, hb, fb, hfb, hxv, u', hu', hub⟩ := listedMarks_sound f x hx
  rw [hu] at hu'; cases hu'
  obtain ⟨gb, hgb, -, hsub⟩ := F.bext b hb fb hfb
  rw [listedDefs_of_marked ⟨b, F.blocks ▸ hb, gb, hgb, hsub x hxv, w, hw, hwb.trans hub⟩, hw]

/-- The definition of a listed value of `g`: `fwdRepOK`. -/
theorem rep_of {x : ID} {u : Value} (hu : f.value? x = some u) :
    ∃ w, g.value? x = some w ∧ w.id = u.id ∧ w.block = u.block ∧ w.type = u.type ∧
      ((w.op = u.op ∧ w.auxInt = u.auxInt ∧ w.aux = u.aux ∧ w.args = u.args) ∨
       (w.op = .Copy ∧ w.args.size = 1 ∧ fwdOK tabs f u (w.args[0]?.getD 0) = true) ∨
       fwdConstOK tabs f u w = true ∨ dropOK tabs f g u w = true ∨
       fwdMoveRep tabs f g u w = true ∨ moveSrcOK tabs f u w = true ∨
       fixedOK tabs ro f u w = true) := by
  have h := F.rep x (lt_of_value? hu)
  unfold fwdRepOK fwdNewOK at h
  rw [hu] at h
  cases hw : g.value? x with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hid, hblk⟩, hty⟩, h⟩ := h
    refine ⟨w, rfl, hid, hblk, hty, ?_⟩
    rcases h with (⟨⟨⟨hop, hai⟩, hax⟩, hargs⟩ | (((⟨⟨hop, hsz⟩, hok⟩ | hc) | hd) | hs) | hx) | hm
    · exact .inl ⟨hop, hai, hax, hargs⟩
    · exact .inr (.inl ⟨hop, hsz, hok⟩)
    · exact .inr (.inr (.inl hc))
    · exact .inr (.inr (.inr (.inl hd)))
    · exact .inr (.inr (.inr (.inr (.inr (.inl hs)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr hx)))))
    · exact .inr (.inr (.inr (.inr (.inl hm))))

/-- The arguments of a value listed in `f` are listed. -/
theorem lm_arg {x : ID} {u : Value} (hx : LM f x) (hu : f.value? x = some u) :
    ∀ a ∈ u.args, LM f a := by
  obtain ⟨b, hb, fb, hfb, hxv, u', hu', -⟩ := listedMarks_sound f x hx
  rw [hu] at hu'; cases hu'
  exact (closedOK_facts F.cf b hb fb hfb).2 x hxv u hu

/-- A value reached through copies from a listed value is listed and ranks no higher. -/
theorem copyReach_rank : ∀ (N : Nat) {a w : ID}, copyReach tabs f.valueTab N a w = true →
    LM f a → LM f w ∧ (fwdRank f)[w]?.getD 0 ≤ (fwdRank f)[a]?.getD 0
  | 0, a, w, h, ha => by
    simp only [copyReach, beq_iff_eq] at h; subst h; exact ⟨ha, Nat.le_refl _⟩
  | N + 1, a, w, h, ha => by
    unfold copyReach at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨ha, Nat.le_refl _⟩
    have hget : ∀ z, Defs.get? f.valueTab z = f.value? z := fun _ => rfl
    rw [hget] at h
    cases hx : f.value? a with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hop, hsz⟩, -⟩, hr⟩ := h
      have hc0 : x.args[0]! ∈ x.args := by
        rw [getElem!_pos x.args 0 (by omega)]; exact Array.getElem_mem _
      have hph : x.op ≠ .Phi := by rw [hop]; decide
      obtain ⟨hlw, hrw⟩ := copyReach_rank N hr (lm_arg F ha hx _ hc0)
      exact ⟨hlw, Nat.le_trans hrw (Nat.le_of_lt (fwdRankOK_spec F.rank ha hx hph _ hc0))⟩

/-- The value a `Store` chain (`fwdChain`) reads back is listed and ranks below the chain's
memory. -/
theorem chain_rank {p x : ID} {t : Ty} :
    ∀ (d : Nat) (m : ID), fwdChain tabs f p t x d m = true → LM f m →
      LM f x ∧ (fwdRank f)[x]?.getD 0 < (fwdRank f)[m]?.getD 0
  | 0, _, h, _ => by simp [fwdChain] at h
  | d + 1, m, h, hm => by
    unfold fwdChain at h
    cases hs : f.value? m with
    | none => rw [hs] at h; cases h
    | some s =>
    cases hx : f.value? x with
    | none => rw [hs, hx] at h; cases h
    | some xv =>
    rw [hs, hx] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hcop, hcsz⟩, hch⟩ | ⟨⟨hsop, hssz⟩, h⟩
    · have hc : s.args[0]! ∈ s.args := by
        rw [getElem!_pos s.args 0 (by omega)]; exact Array.getElem_mem _
      have hph : s.op ≠ .Phi := by rw [hcop]; decide
      obtain ⟨hlx, hrx⟩ := chain_rank d _ hch (lm_arg F hm hs _ hc)
      exact ⟨hlx, Nat.lt_trans hrx (fwdRankOK_spec F.rank hm hs hph _ hc)⟩
    have hsph : s.op ≠ .Phi := by rcases hsop with h | h <;> rw [h] <;> decide
    have hmem : ∀ i, i < 3 → s.args[i]! ∈ s.args := fun i hi => by
      rw [getElem!_pos s.args i (by omega)]; exact Array.getElem_mem _
    rcases h with ⟨⟨⟨⟨hst, -⟩, -⟩, -⟩⟩ | ⟨-, hch⟩
    · obtain ⟨av, hav, hcr, -⟩ := storedOK_spec hst
      obtain ⟨hlx, hrx⟩ := copyReach_rank F _ hcr (lm_arg F hm hs _ (hmem 1 (by omega)))
      exact ⟨hlx, Nat.lt_of_le_of_lt hrx (fwdRankOK_spec F.rank hm hs hsph _ (hmem 1 (by omega)))⟩
    · have hc := hmem 2 (by omega)
      obtain ⟨hlx, hrx⟩ := chain_rank d _ hch (lm_arg F hm hs _ hc)
      exact ⟨hlx, Nat.lt_trans hrx (fwdRankOK_spec F.rank hm hs hsph _ hc)⟩

/-- **A `Load` from a `Move`'s destination** (`fwdMoveRep`): it reads, in the `Move`'s memory, the
source at the same offset, as the fresh `Load` that its `Copy` in `g` reads does. -/
theorem move_den {ρ ρ' : ID → Val} (hT : Term.Typed f.value? tabs ρ)
    (hM : MemAtoms f.value? tabs ρ) {x : ID} {u w : Value} (hx : LM f x)
    (hu : f.value? x = some u) (hL : listedDefs g x = some w) (hwty : w.type = u.type)
    (h : fwdMoveRep tabs f g u w = true)
    (hIH : ∀ a, (fwdRank f)[a]?.getD 0 < (fwdRank f)[x]?.getD 0 → LM f a → ∀ n, ∃ m,
      Sem.Refines (den f.value? tabs ρ n a) (den (listedDefs g) tabs ρ' m a)) (n : Nat) :
    ∃ m, Sem.Refines (den f.value? tabs ρ (n + 1) x) (den (listedDefs g) tabs ρ' m x) := by
  obtain ⟨hwop, hwsz, hly, top, htop, htsz, hlo, offp, hoffp, h⟩ := fwdMoveRep_spec h
  obtain ⟨hld, hsz2, htopop, htty, -, hoop, hosz, hoty, hopos, hsize, mv, hmv, hmop, hmsz, htm,
    hos, hlen, hoff, hbase⟩ := fwdMoveOK_spec h
  have hLt : termOp u.op = true := by rw [hld]; decide
  have hu1 : u.args[1]! ∈ u.args := by
    rw [getElem!_pos u.args 1 (by omega)]; exact Array.getElem_mem _
  have hmem : ∀ i, i < 3 → mv.args[i]! ∈ mv.args := fun i hi => by
    rw [getElem!_pos mv.args i (by omega)]; exact Array.getElem_mem _
  have hmph : mv.op ≠ .Phi := by rw [hmop]; decide
  have hph : u.op ≠ .Phi := by rw [hld]; decide
  have hlm : LM f u.args[1]! := lm_arg F hx hu _ hu1
  have hrm := fwdRankOK_spec F.rank hx hu hph _ hu1
  -- the source: a Load from the Move
  rw [den_succ_term hu hLt, toList_two hsz2, List.map_cons, List.map_cons, List.map_nil, hld,
    GoFV.Proof.Rules.opVal_pure (op := Op.Load) rfl, evalPure_load]
  by_cases hcase : ∃ a M, (den f.value? tabs ρ n u.args[0]!).asPtrWord = some a ∧
    den f.value? tabs ρ n u.args[1]! = .mem M
  rotate_left
  · rw [loadOp_other hcase, AtomSim.retype_poison]; exact ⟨0, .poison _⟩
  obtain ⟨P, M, hpa, hsM⟩ := hcase
  rw [hsM]
  simp only [loadOp, hpa]
  cases n with
  | zero => simp [den, Val.asPtrWord] at hpa
  | succ n =>
  have hmat : ¬ IsTerm f.value? u.args[1]! := not_term_of hmv (by rw [hmop]; decide)
  rw [den_succ_atom hmat] at hsM
  obtain ⟨N0, hN0⟩ := hM _ mv hmv (by rw [hmop]; rfl) (by rw [hsM]; nofun)
  obtain ⟨y, hy, hρy⟩ := hN0 (N0 + n) (Nat.le_add_right _ _)
  rw [toList_three hmsz, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hy
  obtain ⟨d, q, m0, bs, M', hd, hq, hm0, hr, hw, rfl⟩ := memDef_move hmop hy
  rw [hsM] at hρy
  have hMM : M' = M := retype_mem hρy.symm
  rw [hMM] at hw
  -- the pointer: the Move's destination plus the offset
  have hc := ofInt_nonneg hopos
  obtain ⟨k1, q1, h1, e1⟩ := ptrBase_den 8 u.args[0]! _ P hpa
  obtain ⟨k2, q2, h2, e2⟩ := ptrBase_den 8 mv.args[0]! _ d hd
  have hq12 := baseSame_den hM 8 _ _ hbase h1 h2
  have hP : P = d.add (BitVec.ofNat 64 offp.auxInt.toInt.toNat) := by
    rw [e1, e2, hoff, hq12, ptr_add_add, hc]
  -- the bytes: the Move's destination holds the source's
  have hN : mv.auxInt.toInt.toNat ≠ 0 := by omega
  have hbs := read_size hN hr
  have hl : M.load (tabs.ty u.type) P =
      m0.load (tabs.ty u.type) (q.add (BitVec.ofNat 64 offp.auxInt.toInt.toNat)) := by
    rw [hP]
    apply load_congr_read
    rw [read_sub (read_write_self hw) hsize (by omega), read_sub hr hsize (by omega)]
  rw [hl]
  -- the target's arguments: the Move's source and memory
  have hl1 : LM f mv.args[1]! := lm_arg F hlm hmv _ (hmem 1 (by omega))
  have hl2 : LM f mv.args[2]! := lm_arg F hlm hmv _ (hmem 2 (by omega))
  have hr1 := fwdRankOK_spec F.rank hlm hmv hmph _ (hmem 1 (by omega))
  have hr2 := fwdRankOK_spec F.rank hlm hmv hmph _ (hmem 2 (by omega))
  obtain ⟨m1, hm1⟩ := hIH _ (by omega) hl1 (N0 + n)
  obtain ⟨m2, hm2⟩ := hIH _ (by omega) hl2 (N0 + n)
  rw [hm0] at hm2
  have hsrc : (den (listedDefs g) tabs ρ' (m1 + m2) mv.args[1]!).asPtrWord = some q :=
    (hm1.trans (den_fuel_mono _ _ _ _ _ _ (Nat.le_add_right _ _))).asPtrWord hq
  obtain ⟨e, he⟩ : ∃ e, tabs.ty offp.type = .ptr e := by
    revert hoty; cases tabs.ty offp.type <;> simp [isPtrTy]
  have hoffw : ((PtrOps.offPtr offp.auxInt [den (listedDefs g) tabs ρ' (m1 + m2) mv.args[1]!]).retype
      (tabs.ty offp.type)).asPtrWord = some (q.add (BitVec.ofNat 64 offp.auxInt.toInt.toNat)) := by
    rw [he, Val.asPtrWord_retype_ptr, PtrOps.offPtr_asPtrWord, hsrc, Option.bind_some, hc]
    simp only [Ptr.step?, read_inWindow hr (show
      offp.auxInt.toInt.toNat < mv.auxInt.toInt.toNat by omega), ite_true]
  have hmemR : Sem.Refines (.mem m0) (den (listedDefs g) tabs ρ' (m1 + m2 + 1) mv.args[2]!) :=
    hm2.trans (den_fuel_mono _ _ _ _ _ _ (by omega))
  generalize hz : den (listedDefs g) tabs ρ' (m1 + m2 + 1) mv.args[2]! = z at hmemR
  cases hmemR with
  | mem hmr =>
  rename_i m0'
  -- the target: `Copy` of the fresh `Load (OffPtr [o] src) mem`
  have hLy : listedDefs g w.args[0]! = some top := by rw [listedB_spec hly, htop]
  have hLo : listedDefs g top.args[0]! = some offp := by rw [listedB_spec hlo, hoffp]
  refine ⟨m1 + m2 + 1 + 1 + 1, ?_⟩
  rw [den_succ_term hL (by rw [hwop]; decide), hwop, toList_one hwsz, List.map_cons,
    List.map_nil, GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy, hwty,
    den_succ_term hLy (by rw [htopop]; decide), htopop, toList_two htsz, List.map_cons,
    List.map_cons, List.map_nil, GoFV.Proof.Rules.opVal_pure (op := Op.Load) rfl, evalPure_load,
    htty, htm, hz, den_succ_term hLo (by rw [hoop]; decide), hoop, toList_one hosz,
    List.map_cons, List.map_nil, GoFV.Proof.Rules.opVal_pure (op := Op.OffPtr) rfl,
    evalPure_offPtr, hos]
  simp only [loadOp, hoffw, Val.retype_idem]
  exact retype_mono _ (load_mono hmr _ _)

/-- **A dropped memory root** (`dropOK`): its write is refined by its memory, which the `Copy`
replacing it in `g` reads: `w`'s argument through copies of `f` (listed, below `x`), or the
root's memory argument (below `x`) through copies of `g` (`memCopyReach_den`). -/
theorem drop_den {ρ ρ' : ID → Val} (hT : Term.Typed f.value? tabs ρ)
    (hM : MemAtoms f.value? tabs ρ) (hQ : FreshQ tabs f ρ) {x : ID} {u w : Value} (hx : LM f x)
    (hu : f.value? x = some u) (hL : listedDefs g x = some w) (hwty : w.type = u.type)
    (h : dropOK tabs f g u w = true)
    (hIH : ∀ a, (fwdRank f)[a]?.getD 0 < (fwdRank f)[x]?.getD 0 → LM f a → ∀ n, ∃ m,
      Sem.Refines (den f.value? tabs ρ n a) (den (listedDefs g) tabs ρ' m a)) (n : Nat) :
    ∃ m, Sem.Refines (den f.value? tabs ρ (n + 1) x) (den (listedDefs g) tabs ρ' m x) := by
  obtain ⟨hwop, hwsz, hop, -⟩ := dropOK_spec h
  have hmem : memOp u.op = true := by rcases hop with h | h <;> rw [h] <;> rfl
  have hph : u.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> decide
  rw [den_succ_atom (not_term_of hu (by rw [memOp_not_term hmem]; decide))]
  by_cases hp : ρ x = .poison
  · rw [hp]; exact ⟨0, .poison _⟩
  obtain ⟨N, hN⟩ := hM x u hu hmem hp
  obtain ⟨y, hy, hρx⟩ := hN N (Nat.le_refl _)
  obtain ⟨M1, rfl, hcase⟩ := drop_mem hT hM hQ h hy
  -- the memory `w`'s argument holds in `g`
  obtain ⟨m, M0', hz, hR⟩ : ∃ m M0', den (listedDefs g) tabs ρ' m w.args[0]! = .mem M0' ∧
      Mem.Refines M1 M0' := by
    rcases hcase with ⟨i, hi, hcr, M0, hc, hR⟩ | ⟨i, hi, hcr, M0, hc, hR⟩
    · -- `w`'s argument in `f`: listed, below `x`
      have hui : u.args[i]! ∈ u.args := by
        rw [getElem!_pos u.args i hi]; exact Array.getElem_mem _
      obtain ⟨hlc, hrc⟩ := copyReach_rank F _ hcr (lm_arg F hx hu _ hui)
      have hrx := fwdRankOK_spec F.rank hx hu hph _ hui
      obtain ⟨m, hm⟩ := hIH _ (by omega) hlc N
      rw [hc] at hm
      obtain ⟨M0', hz, hR'⟩ := refines_mem' hm
      exact ⟨m, M0', hz, hR.trans hR'⟩
    · -- the root's memory argument, below `x`, then the copies of `g`
      have hui : u.args[i]! ∈ u.args := by
        rw [getElem!_pos u.args i hi]; exact Array.getElem_mem _
      obtain ⟨m, hm⟩ := hIH _ (fwdRankOK_spec F.rank hx hu hph _ hui) (lm_arg F hx hu _ hui) N
      rw [hc] at hm
      obtain ⟨M0', hz, hR'⟩ := refines_mem' hm
      obtain ⟨m', hz'⟩ := memCopyReach_den _ hcr hz
      exact ⟨m', M0', hz', hR.trans hR'⟩
  refine ⟨m + 1, ?_⟩
  rw [den_succ_term hL (by rw [hwop]; rfl), hwop, toList_one hwsz, List.map_cons, List.map_nil,
    GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy, hwty, hz, hρx, shape_of hu]
  exact retype_mono _ (.mem hR)

/-- **Values as terms**: each value listed in `f` is refined by the same value listed in `g`,
for valuations whose memory roots hold the writes of their arguments, under the forwarding
layer's frame invariant (`FwdQ`: fresh malloc calls' registers, the read-only symbols `ro` in the
registers' memories). -/
theorem fwd_den {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ') (hT : Term.Typed f.value? tabs ρ)
    (hM : MemAtoms f.value? tabs ρ) (hQ : FwdQ tabs ro f ρ) :
    ∀ (r : Nat) (x : ID), (fwdRank f)[x]?.getD 0 = r → LM f x → ∀ n, ∃ m,
      Sem.Refines (den f.value? tabs ρ n x) (den (listedDefs g) tabs ρ' m x) := by
  intro r
  refine Nat.strongRecOn r ?_
  intro r ih x hr hx n
  cases n with
  | zero => exact ⟨0, .poison _⟩
  | succ n =>
  have hxv := listedMarks_sound f x hx
  obtain ⟨-, -, -, -, -, u, hu, -⟩ := hxv
  obtain ⟨w, hw, -, hwb, hwty, hrep⟩ := rep_of F hu
  have hL := marked_g F hx hu hw hwb
  have hIH : ∀ a, (fwdRank f)[a]?.getD 0 < r → LM f a → ∀ n, ∃ m,
      Sem.Refines (den f.value? tabs ρ n a) (den (listedDefs g) tabs ρ' m a) :=
    fun a ha hla => ih _ ha a rfl hla
  rcases hrep with ⟨hop, hai, hax, hargs⟩ | ⟨hop, hsz, hok⟩ | hok | hdrop | hmv | hms | hfx
  rotate_left 3
  · exact drop_den F hT hM hQ.1 hx hu hL hwty hdrop (fun a ha hla => hIH a (hr ▸ ha) hla) n
  · exact move_den F hT hM hx hu hL hwty hmv (fun a ha hla => hIH a (hr ▸ ha) hla) n
  · -- a `Move` with a changed source: an atom of both
    obtain ⟨huop, hwop, -⟩ := moveSrcOK_spec hms
    refine ⟨1, ?_⟩
    rw [den_succ_atom (not_term_of hu (by rw [huop]; decide)),
      den_succ_atom (not_term_of hL (by rw [hwop]; decide))]
    exact hρ x
  · -- a fixed load from a read-only symbol
    exact ⟨1, fixed_den hM hQ F.cf hu (lm_arg F hx hu) hL hwty hfx n⟩
  · by_cases ht : termOp u.op = true
    · have hph : u.op ≠ .Phi := fun h => by rw [h] at ht; cases ht
      obtain ⟨m, hm⟩ := fuel_list (F := fun a => den f.value? tabs ρ n a)
        (G := fun m a => den (listedDefs g) tabs ρ' m a)
        (fun a m m' h => den_fuel_mono _ _ _ m m' a h) u.args.toList fun a ha =>
          hIH a (hr ▸ fwdRankOK_spec F.rank hx hu hph a (Array.mem_toList_iff.1 ha))
            (lm_arg F hx hu a (Array.mem_toList_iff.1 ha)) n
      refine ⟨m + 1, ?_⟩
      rw [den_succ_term hu ht, den_succ_term hL (hop ▸ ht), hop, hwty, hai, hax, hargs]
      exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_map hm))
    · refine ⟨1, ?_⟩
      rw [den_succ_atom (not_term_of hu ht), den_succ_atom (not_term_of hL (hop ▸ ht))]
      exact hρ x
  · -- `x` is a Load forwarded to `Copy c`
    obtain ⟨c, hc⟩ : ∃ c, c = w.args[0]?.getD 0 := ⟨_, rfl⟩
    rw [← hc] at hok
    unfold fwdOK at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hld, hsz2⟩, hch⟩ := hok
    have hph : u.op ≠ .Phi := by rw [hld]; decide
    have hLt : termOp u.op = true := by rw [hld]; decide
    have hu1 : u.args[1]! ∈ u.args := by
      rw [getElem!_pos u.args 1 (by omega)]; exact Array.getElem_mem _
    -- the ranks: `c` below the chain's memory, below the Load
    have hls : LM f u.args[1]! := lm_arg F hx hu _ hu1
    obtain ⟨hlc, hrc'⟩ := chain_rank F 8 _ hch hls
    have hrc : (fwdRank f)[c]?.getD 0 < r := by
      have := fwdRankOK_spec F.rank hx hu hph _ hu1
      omega
    -- the target: `Copy c`
    have hcopy : termOp Op.Copy = true := by decide
    have hw0 : w.args.toList = [c] := by
      apply List.ext_getElem (by simp [hsz])
      intro i h1 h2
      have : i = 0 := by simp [hsz] at h1; omega
      subst this
      simp [hc, Array.getElem?_eq_getElem (show 0 < w.args.size by omega)]
    have hden_t : ∀ m, den (listedDefs g) tabs ρ' (m + 1) x =
        (den (listedDefs g) tabs ρ' m c).retype (tabs.ty u.type) := fun m => by
      rw [den_succ_term hL (hop ▸ hcopy), hop, hw0, List.map_cons, List.map_nil,
        GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy, hwty]
    -- the source: a Load through the chain
    rw [den_succ_term hu hLt, toList_two hsz2, List.map_cons, List.map_cons, List.map_nil, hld,
      GoFV.Proof.Rules.opVal_pure (op := Op.Load) rfl, evalPure_load]
    by_cases hcase : ∃ a M, (den f.value? tabs ρ n u.args[0]!).asPtrWord = some a ∧
      den f.value? tabs ρ n u.args[1]! = .mem M
    · obtain ⟨a, M, hpa, hsM⟩ := hcase
      rw [hsM]
      simp only [loadOp, hpa]
      obtain ⟨K, hK⟩ := chain_load hT hM hpa 8 _ hch hsM
      obtain ⟨m, hm⟩ := hIH c hrc hlc K
      refine ⟨m + 1, ?_⟩
      rw [hden_t m]
      exact retype_mono _ (hK.trans hm)
    · rw [loadOp_other hcase, AtomSim.retype_poison]; exact ⟨0, .poison _⟩
  · -- `x` is a Load replaced by the constant of the bits it reads back
    obtain ⟨hld, hsz2, hwc, c, cv, hcv, hcc, hai, hty, hok⟩ := fwdConstOK_spec hok
    unfold fwdOK at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨-, hch⟩ := hok
    have hLt : termOp u.op = true := by rw [hld]; decide
    rw [den_succ_term hu hLt, toList_two hsz2, List.map_cons, List.map_cons, List.map_nil, hld,
      GoFV.Proof.Rules.opVal_pure (op := Op.Load) rfl, evalPure_load]
    refine ⟨0 + 1, ?_⟩
    rw [den_succ_term hL (const64_term hwc), opVal_const64 hwc, hwty]
    by_cases hcase : ∃ a M, (den f.value? tabs ρ n u.args[0]!).asPtrWord = some a ∧
      den f.value? tabs ρ n u.args[1]! = .mem M
    · obtain ⟨a, M, hpa, hsM⟩ := hcase
      rw [hsM]
      simp only [loadOp, hpa]
      obtain ⟨K, hK⟩ := chain_load hT hM hpa 8 _ hch hsM
      have h1 := hK.trans (den_fuel_mono _ _ _ K (K + 1) c (Nat.le_succ K))
      rw [den_succ_term hcv (const64_term hcc), opVal_const64 hcc, hai,
        ← fwdTyEq_retype hty] at h1
      have h2 := retype_mono (tabs.ty u.type) h1
      rwa [retype_idem] at h2
    · rw [loadOp_other hcase, AtomSim.retype_poison]; exact .poison _

/-- **A changed `Move` source writes a refined memory** (`moveSrcOK`): the source's `Move` copies
from `tmp` in a memory where `tmp` holds what the inner `Move` read at `src` (or `poison`), and
`src` still holds it (`moveSrc_mem`). -/
theorem moveSrc_chgRef {u w : Value} (hargs : ∀ a ∈ u.args, LM f a)
    (h : moveSrcOK tabs f u w = true) :
    ChgRefP (FwdQ tabs ro f) f.value? tabs u (listedDefs g) w := by
  intro ρ ρ' hρ hT _ hQ hM k y hy
  obtain ⟨huop, hwop, hu3, hw3, hai, -, hc0, hc2, mv, hmv, hcase⟩ := moveSrcOK_spec h
  have hu0 : u.args[0]! ∈ u.args := by
    rw [getElem!_pos u.args 0 (by omega)]; exact Array.getElem_mem _
  have hu2 : u.args[2]! ∈ u.args := by
    rw [getElem!_pos u.args 2 (by omega)]; exact Array.getElem_mem _
  have hl0 := (copyReach_rank F _ hc0 (hargs _ hu0)).1
  have hl2 := (copyReach_rank F _ hc2 (hargs _ hu2)).1
  rw [toList_three hu3, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hy
  obtain ⟨Dp, T, M, bs, M', hD, hT1, hMm, hrT, hwD, rfl⟩ := memDef_move huop hy
  -- `w`'s destination and memory in `f`
  have hD' : (den f.value? tabs ρ k w.args[0]!).asPtrWord = some Dp :=
    (copyReach_den (M := f.valueTab) hT _ _ _ hc0 k).asPtrWord hD
  obtain ⟨M2, hM2, hMM2⟩ : ∃ M2, den f.value? tabs ρ k w.args[2]! = .mem M2 ∧ Mem.Refines M M2 := by
    have hc := copyReach_den (M := f.valueTab) hT _ _ _ hc2 k
    rw [show den (Defs.get? f.valueTab) tabs ρ k u.args[2]! = .mem M from hMm] at hc
    obtain ⟨M2, h1, h2⟩ := refines_mem' hc
    exact ⟨M2, h1, h2⟩
  have hmvop : memOp mv.op = true := by
    rcases hcase with hi | ⟨_, _, hvd, -⟩
    · rw [(moveInnerOK_spec hi).1]; rfl
    · rw [hvd]; rfl
  have hat2 : ¬ IsTerm f.value? w.args[2]! :=
    not_term_of hmv (by rw [memOp_not_term hmvop]; decide)
  cases k with
  | zero => simp [den] at hM2
  | succ k =>
  have hM2' := hM2
  rw [den_succ_atom hat2] at hM2'
  obtain ⟨N, hN⟩ := hM w.args[2]! mv hmv hmvop (by rw [hM2']; exact fun h => by cases h)
  -- the inner `Move` at large fuel, given its register `.mem Mi`
  have inner : ∀ {im : Value} {B : Option Blk} {z : ID}, f.value? z = some im →
      moveInnerOK tabs f u w im B = true → ∀ {Mi : Mem}, ρ z = .mem Mi →
      ∃ K, ∃ T2 S, ∃ M0 : Mem, ∃ bs0, (den f.value? tabs ρ K im.args[0]!).asPtrWord = some T2 ∧
        (den f.value? tabs ρ K im.args[1]!).asPtrWord = some S ∧
        M0.read S u.auxInt.toInt.toNat = some bs0 ∧ M0.write T2 bs0 = some Mi := by
    intro im B z him hi Mi hz
    obtain ⟨hiop, hi3, hiai, -⟩ := moveInnerOK_spec hi
    obtain ⟨N', hN'⟩ := hM z im him (by rw [hiop]; rfl) (by rw [hz]; exact fun h => by cases h)
    obtain ⟨y3, hy3, hz3⟩ := hN' N' (Nat.le_refl _)
    rw [toList_three hi3, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hy3
    obtain ⟨T2, S, M0, bs0, M1, h0, h1, -, hr, hw, rfl⟩ := memDef_move hiop hy3
    rw [hz] at hz3
    have hM1 := retype_mem hz3.symm
    subst hM1
    exact ⟨N', T2, S, M0, bs0, h0, h1, by rw [← hiai]; exact hr, hw⟩
  -- the inner `Move`: its pointers, the bytes it copied, and `M2` against its memory
  obtain ⟨im, K, hlim, hi3, hsp, hcr1, hdj, T2, S, M0, M1, bs0, hT2, hS, hr0, hw0, h21, hr21⟩ :
      ∃ im : Value, ∃ K, (∀ a ∈ im.args, LM f a) ∧ im.args.size = 3 ∧
        samePtrB tabs f u.args[1]! im.args[0]! = true ∧
        copyReach tabs f.valueTab f.valueTab.size im.args[1]! w.args[1]! = true ∧
        disjointB tabs f im.args[1]! u.auxInt.toInt.toNat im.args[0]! u.auxInt.toInt.toNat = true ∧
        ∃ T2 S, ∃ M0 M1 : Mem, ∃ bs0, (den f.value? tabs ρ K im.args[0]!).asPtrWord = some T2 ∧
          (den f.value? tabs ρ K im.args[1]!).asPtrWord = some S ∧
          M0.read S u.auxInt.toInt.toNat = some bs0 ∧ M0.write T2 bs0 = some M1 ∧
          Mem.Refines M2 M1 ∧ M2.read S u.auxInt.toInt.toNat = M1.read S u.auxInt.toInt.toNat := by
    rcases hcase with hi | ⟨n, im, hvd, hsz, han, him, hi⟩
    · -- `w`'s memory is the inner `Move`
      obtain ⟨-, hi3, -, hsp, hcr1, hdj, -⟩ := moveInnerOK_spec hi
      obtain ⟨K, T2, S, M0, bs0, hT2, hS, hr0, hw0⟩ := inner hmv hi hM2'
      exact ⟨mv, K, lm_arg F hl2 hmv, hi3, hsp, hcr1, hdj, T2, S, M0, M2, bs0, hT2, hS, hr0, hw0,
        Mem.Refines.refl _, rfl⟩
    · -- `w`'s memory is a `VarDef` (of frame variable `n`) of the inner `Move`
      obtain ⟨himop, hi3, -, hsp, hcr1, hdj, hB⟩ := moveInnerOK_spec hi
      obtain ⟨y2, hy2, hz2⟩ := hN (max N 1) (Nat.le_max_left _ _)
      rw [toList_one hsz, List.map_cons, List.map_nil] at hy2
      obtain ⟨Mi, n', hMi, hn', rfl⟩ := memDef_varDef hvd hy2
      rw [han] at hn'
      cases hn'
      have hl0' : mv.args[0]! ∈ mv.args := by
        rw [getElem!_pos mv.args 0 (by omega)]; exact Array.getElem_mem _
      have hlim := lm_arg F (lm_arg F hl2 hmv _ hl0') him
      obtain ⟨K1, hK1⟩ : ∃ K1, max N 1 = K1 + 1 := ⟨max N 1 - 1, by omega⟩
      rw [hK1, den_succ_atom (not_term_of him (by rw [himop]; decide))] at hMi
      obtain ⟨K, T2, S, M0, bs0, hT2, hS, hr0, hw0⟩ := inner him hi hMi
      rw [hM2'] at hz2
      have hM2e := retype_mem hz2.symm
      subst hM2e
      obtain ⟨Bs, hBs, hne⟩ := hB _ rfl
      obtain ⟨kq, q, hq, hSq⟩ := ptrBase_den 8 im.args[1]! K S hS
      have hq' := baseBlk_den hM hBs hq
      have hSb : S.blk ≠ frameBlk tabs 0 n := by
        rw [hSq, hq']; simpa [Ptr.add] using hne
      exact ⟨im, K, hlim, hi3, hsp, hcr1, hdj, T2, S, M0, Mi, bs0, hT2, hS, hr0, hw0,
        GoFV.Proof.Seg.poisonBlock_refines _ _, read_poisonBlock_ne _ hSb⟩
  -- the source's pointers against the inner `Move`'s
  have hTe : T = T2 := samePtr_den hM hsp hT1 hT2
  subst hTe
  have hsep := disjoint_sep hM hdj hS hT2
  -- the target's arguments: refined as terms (`fwd_den`)
  have him1 : im.args[1]! ∈ im.args := by
    rw [getElem!_pos im.args 1 (by omega)]; exact Array.getElem_mem _
  have hl1 := (copyReach_rank F _ hcr1 (hlim _ him1)).1
  have hS' : (den f.value? tabs ρ K w.args[1]!).asPtrWord = some S :=
    (copyReach_den (M := f.valueTab) hT _ _ _ hcr1 K).asPtrWord hS
  obtain ⟨m0, hm0⟩ := fwd_den F hρ hT hM hQ _ _ rfl hl0 (k + 1)
  obtain ⟨m1, hm1⟩ := fwd_den F hρ hT hM hQ _ _ rfl hl1 K
  obtain ⟨m2, hm2⟩ := fwd_den F hρ hT hM hQ _ _ rfl hl2 (k + 1)
  rw [hM2] at hm2
  obtain ⟨Mt, hMt, hM2t⟩ := refines_mem' hm2
  have hd0 : (den (listedDefs g) tabs ρ' (max m0 (max m1 m2)) w.args[0]!).asPtrWord = some Dp :=
    (hm0.trans (den_fuel_mono _ _ _ _ _ _ (Nat.le_max_left _ _))).asPtrWord hD'
  have hd1 : (den (listedDefs g) tabs ρ' (max m0 (max m1 m2)) w.args[1]!).asPtrWord = some S :=
    (hm1.trans (den_fuel_mono _ _ _ _ _ _ (by omega))).asPtrWord hS'
  obtain ⟨Mt', hMt', hMtt⟩ : ∃ Mt', den (listedDefs g) tabs ρ' (max m0 (max m1 m2)) w.args[2]! =
      .mem Mt' ∧ Mem.Refines Mt Mt' := by
    have := den_fuel_mono (listedDefs g) tabs ρ' m2 (max m0 (max m1 m2)) w.args[2]! (by omega)
    rw [hMt] at this
    exact refines_mem' this
  obtain ⟨bs', W, hr', hw', hMW⟩ :=
    moveSrc_mem hMM2 h21 hr21 hr0 hw0 hsep hrT hwD (hM2t.trans hMtt)
  refine ⟨max m0 (max m1 m2), .mem W, ?_, .mem hMW⟩
  rw [toList_three hw3, List.map_cons, List.map_cons, List.map_cons, List.map_nil, hMt']
  simp [memDef, hwop, hai, hd0, hd1, hr', hw', -Int64.toNat_toInt]

/-- Each value listed in `f` refines as a term in `g`, under the forwarding layer's frame
invariant (`FwdQ`). -/
theorem fwd_termRefP {x : ID} (hx : LM f x) (P : ID → Val → Prop)
    (S : ID → Prop) : TermRefP P (FwdQ tabs ro f) S f.value? tabs x (listedDefs g) tabs x :=
  fun _ _ hρ hT _ _ _ hQ hM n => fwd_den F hρ hT hM hQ _ x rfl hx n

theorem fwd_atomArgs (hro : fwdRoOK tabs ro f = true) :
    AtomArgsRefX (fwdInv tabs ro f hro) g := by
  intro b hb gb hgb a ha u hu ht
  have hbf : b ∈ f.blocks := F.blocks ▸ hb
  obtain ⟨fb, gb', hfb, hgb', BA⟩ := (atomsXOK_spec F.atoms).block b hbf
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨haf, u', hu', hop, hty, hai, -, hsz, -, -⟩ := BA.sub a ha u hu ht
  obtain ⟨w, hw, -, -, -, hrep⟩ := rep_of F hu'
  rw [hu] at hw; cases hw
  have hargs := (closedOK_facts F.cf b hbf fb hfb).2 a haf u' hu'
  have hsame : (u.aux = u'.aux ∧ u.args = u'.args) ∨ moveSrcOK tabs f u' u = true := by
    rcases hrep with ⟨-, -, hax, h⟩ | ⟨h, -⟩ | h | h | h | h | h
    · exact .inl ⟨hax, h⟩
    · rw [h] at ht; cases ht
    · rcases const64Op_cases (fwdConstOK_spec h).2.2.1 with h | h <;> rw [h] at ht <;> cases ht
    · rw [(dropOK_spec h).1] at ht; cases ht
    · rw [(fwdMoveRep_spec h).1] at ht; cases ht
    · exact .inr h
    · rw [fixedOK_term h] at ht; cases ht
  rcases hsame with hsame | hms
  · refine .inl ⟨u', hu', hop, hty, hai, hsame.1.symm, hsz, fun i hi => ?_⟩
    have hi' : i < u'.args.size := hsame.2 ▸ hi
    rw [hsame.2]
    have hx := hargs u'.args[i]! (by rw [getElem!_pos u'.args i hi']; exact Array.getElem_mem hi')
    exact ⟨fun _ => fwd_termRefP F hx _ _, fun _ _ _ _ _ _ _ => fwd_termRefP F hx _ _⟩
  · obtain ⟨huop, hwop, -⟩ := moveSrcOK_spec hms
    exact .inr ⟨u', hu', huop.trans hwop.symm, .inr hwop, moveSrc_chgRef F hargs hms⟩

theorem fwd_steps (hro : fwdRoOK tabs ro f = true) :
    StepRefsP (fwdInv tabs ro f hro) g := by
  refine ControlsRefP.toStepRefsP (fun b hb fb gb hfb hgb => ?_) fun b hb fb gb hfb hgb => ?_
  · have hbf : b ∈ f.blocks := F.blocks ▸ hb
    obtain ⟨gb', hgb', hext, -⟩ := F.bext b hbf fb hfb
    rw [hgb] at hgb'; cases hgb'
    rw [hext]
    refine ⟨rfl, fun k hk => fwd_termRefP F ((closedOK_facts F.cf b hbf fb hfb).1 _
      (by rw [getElem!_pos fb.controls k hk]; exact Array.getElem_mem hk)) _ _⟩
  · have hbf : b ∈ f.blocks := F.blocks ▸ hb
    obtain ⟨gb', hgb', hext, -⟩ := F.bext b hbf fb hfb
    rw [hgb] at hgb'; cases hgb'
    rw [hext]
    exact ⟨rfl, rfl, rfl⟩

end

/-- **Load-of-Store forwarding (and dropping identity writes, fixed loads) refines its input**
under monotone contracts whose malloc-family contracts return zeroed blocks, from initial
memories with the read-only symbols `ro` (which `fwdRoOK` reads `newobject`'s type sizes from and
fixed loads read, `fixedOK`) under contracts that keep them. -/
theorem fwd_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {ro : List (String × Alloc)}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ()) (h : fwdRel tabs ro f g = true)
    (hro : fwdRoOK tabs ro f = true) :
    RefinesFrom (fun env _ mem => env.Mono ∧ env.AllocZero ∧ RoImage ro env mem) tabs g tabs f :=
  have F := fwdRel_spec h
  (atomSimXE_refines hf hg (atomsXOK_spec F.atoms) (fwdInv tabs ro f hro) (fwd_atomArgs F hro)
    (fwd_steps F hro)).mono fun _ _ _ h =>
    ⟨h.1, h.2.1, h.2.2.1, (MemInv.sinv_entry (fun a h hg hw => roMem_set a h hg hw) h.2.2.2).1⟩

end GoFV.Proof.Pass.LoadFwd
