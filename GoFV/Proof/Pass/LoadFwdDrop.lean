import GoFV.Proof.Pass.LoadFwdPtr
import GoFV.Proof.Pass.DSEMem

/-!
# Dropped identity writes (issue #151)

The forwarding layer turns a memory root whose write changes no byte into a `Copy` of its memory
(`RewriteCheck.dropOK`): a `Store` of a zero-sized type (`generic.rules:1005`), a `Store` of a
constant term of value `0`, `false` or `poison` (`zeroConst`: `Const64 [0]`, `SliceLen (ConstSlice)`,
…; `termConst_den`) into bytes a `Zero` cleared (`:943`, `:948`, `:954`, `:961`), a
`Zero` of a `Zero` of the same size at an equal pointer (`:2158`). `drop_mem`: the dropped
root's memory is refined by its memory argument's, as every byte written refines the byte
already there (`write_refines_self`): the encoding of a `0`, `false` or `poison` has `0` or
`poison` bytes (`encode_zero`), the cleared bytes read back through the disjoint writes of the
chain (`zeroChain_read`), and a zero-sized write is the identity.
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.CSE.Mem GoFV.Proof.Pass.Rewrite

/-! ## Writes of the bytes already there -/

/-- **Writing back the bytes a read gave** changes nothing. -/
theorem write_read_id {m m' : Mem} {p : Ptr} {bs : Array Byte} (hr : m.read p bs.size = some bs)
    (hw : m.write p bs = some m') : m' = m := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true] at hw; cases hw; rfl
  simp only [he, Bool.false_eq_true, ite_false] at hw
  have hsz : bs.size ≠ 0 := by simpa [Array.isEmpty_iff_size_eq_zero] using he
  obtain ⟨a, ha, h1, -, -, hbs⟩ := read_some hsz hr
  rw [ha] at hw
  simp only [Option.bind_eq_bind, Option.bind_some] at hw
  split at hw
  · cases hw
    have hdata : (List.range bs.size).foldl (fun d i => d.set! (p.off.toNat + i) bs[i]!) a.data =
        a.data := by
      apply Array.ext_getElem?
      intro j
      by_cases hj : p.off.toNat ≤ j ∧ j < p.off.toNat + bs.size
      · obtain ⟨i, rfl⟩ : ∃ i, j = p.off.toNat + i := ⟨j - p.off.toNat, by omega⟩
        have hi : i < bs.size := by omega
        rw [foldl_set_put p.off.toNat bs i (List.range bs.size) a.data List.nodup_range
          (List.mem_range.2 hi) (by omega), getElem!_pos bs i hi, ← Array.getElem?_eq_getElem hi]
        conv => lhs; rw [hbs]
        rw [Array.getElem?_extract_of_lt (by omega), Array.getElem?_eq_getElem (by omega)]
      · exact foldl_set_get p.off.toNat bs j _ _ fun i hi he => hj ⟨by omega, by
          have := List.mem_range.1 hi; omega⟩
    rw [hdata]
    exact GoFV.Proof.DSE.set_self ha
  · cases hw

/-- **A write of bytes refining those already there** (in a refinement `m'` of the written
memory `m`) gives a memory `m'` refines. -/
theorem write_refines_self {m m' m1 : Mem} (h : Mem.Refines m m') {p : Ptr} {bs bs0 : Array Byte}
    (hr : m'.read p bs.size = some bs0) (hw : m.write p bs = some m1) (hb : BytesRefineA bs bs0) :
    Mem.Refines m1 m' := by
  obtain ⟨m1', hw', hR⟩ := h.write hb hw
  rw [hb.size_eq] at hr
  rw [write_read_id hr hw'] at hR
  exact hR

/-- Bytes that are `0` or `poison` are refined by zeros. -/
theorem zeros_refine : ∀ {l : List Byte}, (∀ c ∈ l, c = .b 0 ∨ c = .poison) →
    BytesRefine l (List.replicate l.length (.b 0))
  | [], _ => .nil
  | c :: l, h => by
    refine .cons ?_ (zeros_refine fun c hc => h c (List.mem_cons_of_mem _ hc))
    rcases h c List.mem_cons_self with rfl | rfl
    · exact .refl _
    · exact .poison _

/-! ## Zero values -/

/-- A `0`, `false` or `poison`. -/
def ZeroV (v : Val) : Prop := v = .poison ∨ v = .bool false ∨ ∃ w, v = .int w 0

theorem intBytes_zero (n : Nat) : ∀ c ∈ (intBytes n 0).toList, c = .b 0 ∨ c = .poison := by
  intro c hc
  simp only [intBytes, Nat.zero_div, Array.toList_map, List.mem_map] at hc
  obtain ⟨_, -, rfl⟩ := hc
  exact .inl rfl

theorem replicate_poison_zero (n : Nat) :
    ∀ c ∈ (Array.replicate n Byte.poison).toList, c = .b 0 ∨ c = .poison := by
  intro c hc
  simp only [Array.toList_replicate, List.mem_replicate] at hc
  exact .inr hc.2

/-- **The bytes of a zero value**, at every shape, are `0` or `poison`. -/
theorem encode_zero {v : Val} (h : ZeroV v) (t : Ty) :
    ∀ c ∈ (encode t v).toList, c = .b 0 ∨ c = .poison := by
  rcases h with rfl | rfl | ⟨w, rfl⟩
  · rw [encode_poison]; exact replicate_poison_zero _
  · cases t with
    | bool => intro c hc; simp [encode] at hc; exact .inl hc
    | _ => simp only [encode]; exact replicate_poison_zero _
  · cases t with
    | int w' =>
      simp only [encode]
      split
      · simpa using intBytes_zero w'.bytes
      · exact replicate_poison_zero _
    | ptr e =>
      cases w with
      | w64 => simpa [encode] using intBytes_zero 8
      | _ => simp only [encode]; exact replicate_poison_zero _
    | _ => simp only [encode]; exact replicate_poison_zero _

/-! ## The dropped roots -/

/-- `Val.retype` fixes `mem` only at the memory shape. -/
theorem retype_mem {t : Ty} {M M' : Mem} (h : (Val.mem M').retype t = .mem M) : M' = M := by
  cases t <;> simp [Val.retype] at h
  exact h

/-- Only a memory retypes to a memory. -/
theorem retype_eq_mem {t : Ty} {v : Val} {M : Mem} (h : v.retype t = .mem M) : v = .mem M := by
  unfold Val.retype at h
  split at h <;> (repeat' split at h) <;>
    (try simp only [Val.ofStr, Val.ofSlice] at h) <;> (try split at h) <;> simp_all

/-- A `Store`'s write: a pointer word, a memory and the written memory. -/
theorem memDef_store {tabs : Tables} {s : Value} (hs : s.op = .Store ∨ s.op = .StoreWB)
    {a b c y : Val} (h : memDef tabs s [a, b, c] = some y) :
    ∃ q m0 M', a.asPtrWord = some q ∧ c = .mem m0 ∧
      m0.write q (encode (auxTy tabs s.aux) b) = some M' ∧ y = .mem M' := by
  rcases hs with hs | hs <;>
  · cases c <;> try (simp [memDef, hs] at h; done)
    rename_i m0
    simp only [memDef, hs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, M', hw, rfl⟩ := h
    exact ⟨q, m0, M', hq, rfl, hw, rfl⟩

/-- A `Zero`'s write: a pointer word, a memory and the written memory. -/
theorem memDef_zero {tabs : Tables} {s : Value} (hs : s.op = .Zero) {a c y : Val}
    (h : memDef tabs s [a, c] = some y) :
    ∃ q m0 M', a.asPtrWord = some q ∧ c = .mem m0 ∧
      m0.write q (Array.replicate s.auxInt.toInt.toNat (.b 0)) = some M' ∧ y = .mem M' := by
  cases c <;> try (simp [memDef, hs] at h; done)
  rename_i m0
  simp only [memDef, hs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, M', hw, rfl⟩ := h
  exact ⟨q, m0, M', hq, rfl, hw, rfl⟩

theorem zeroConst_spec {tabs : Tables} {f : Func} {x : ID} (h : zeroConst tabs f x = true) :
    ∃ y, termConst tabs f 4 x = some y ∧ ZeroV y := by
  unfold zeroConst at h
  split at h
  · next hx => exact ⟨_, hx, .inl rfl⟩
  · next hx => exact ⟨_, hx, .inr (.inl rfl)⟩
  · next w c hx => exact ⟨_, hx, .inr (.inr ⟨w, by rw [beq_iff_eq.1 h]⟩)⟩
  · cases h

/-- A value refined by a zero value is one. -/
theorem zeroV_of_refines {a b : Val} (h : Sem.Refines a b) (hb : ZeroV b) : ZeroV a := by
  cases h with
  | poison => exact .inl rfl
  | int => exact hb
  | bool => exact hb
  | _ => rcases hb with h | h | ⟨_, h⟩ <;> cases h

section
variable {tabs : Tables} {f : Func} {ρ : ID → Val}

/-- **A `zeroConst` denotes a zero value** at every fuel: below the term's depth a value its
value refines (`den_fuel_mono`). -/
theorem zeroConst_den {x : ID} (h : zeroConst tabs f x = true) (k : Nat) :
    ZeroV (den f.value? tabs ρ k x) := by
  obtain ⟨y, hy, hz⟩ := zeroConst_spec h
  have h2 := den_fuel_mono f.value? tabs ρ k (max k 4) x (Nat.le_max_left _ _)
  rw [termConst_den 4 x y hy (max k 4) (Nat.le_max_right _ _)] at h2
  exact zeroV_of_refines h2 hz

/-- **Cleared bytes through a chain** (`zeroChain`): the memory holds zeros at the pointer, read
through the disjoint writes from the `Zero` that cleared them. -/
theorem zeroChain_read (hT : Term.Typed f.value? tabs ρ) (hM : MemAtoms f.value? tabs ρ)
    {p : ID} {n : Nat} (hn : n ≠ 0) {kp : Nat} {P : Ptr}
    (hp : (den f.value? tabs ρ kp p).asPtrWord = some P) :
    ∀ (d : Nat) (m : ID), zeroChain tabs f p n d m = true → ∀ {k : Nat} {M : Mem},
      den f.value? tabs ρ k m = .mem M → M.read P n = some (Array.replicate n (.b 0))
  | 0, _, h, _, _, _ => by simp [zeroChain] at h
  | d + 1, m, h, k, M, hm => by
    unfold zeroChain at h
    cases hs : f.value? m with
    | none => rw [hs] at h; cases h
    | some s =>
    rw [hs] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with (⟨⟨hcop, hcsz⟩, hch⟩ | ⟨⟨⟨hsop, hssz⟩, hdis⟩, hch⟩) | ⟨⟨⟨hzop, hzsz⟩, hle⟩, hbase⟩
    · -- a `Copy` of memory
      have ht : termOp s.op = true := by rw [hcop]; rfl
      cases k with
      | zero => simp [den] at hm
      | succ k =>
      rw [den_succ_term hs ht, toList_one hcsz, List.map_cons, List.map_nil, hcop,
        GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy] at hm
      exact zeroChain_read hT hM hn hp d _ hch (retype_eq_mem hm)
    · -- a `Store` at a disjoint pointer
      have hmem : memOp s.op = true := by rcases hsop with h | h <;> rw [h] <;> rfl
      cases k with
      | zero => simp [den] at hm
      | succ k =>
      rw [den_succ_atom (not_term_of hs (by rw [memOp_not_term hmem]; decide))] at hm
      obtain ⟨N, hN⟩ := hM m s hs hmem (by rw [hm]; nofun)
      obtain ⟨y, hy, hρs⟩ := hN N (Nat.le_refl _)
      rw [toList_three hssz, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hy
      obtain ⟨q, m0, M', hq, hm0, hwr, rfl⟩ := memDef_store hsop hy
      rw [hm] at hρs
      have hMM := retype_mem hρs.symm
      subst hMM
      rw [read_write_sep hwr (by rw [GoFV.Proof.CSE.Mem.encode_size]; exact disjoint_sep hM hdis hp hq)]
      exact zeroChain_read hT hM hn hp d _ hch hm0
    · -- the `Zero`
      have hmem : memOp s.op = true := by rw [hzop]; rfl
      cases k with
      | zero => simp [den] at hm
      | succ k =>
      rw [den_succ_atom (not_term_of hs (by rw [memOp_not_term hmem]; decide))] at hm
      obtain ⟨N, hN⟩ := hM m s hs hmem (by rw [hm]; nofun)
      obtain ⟨y, hy, hρs⟩ := hN N (Nat.le_refl _)
      rw [toList_two hzsz, List.map_cons, List.map_cons, List.map_nil] at hy
      obtain ⟨q, m0, M', hq, -, hwr, rfl⟩ := memDef_zero hzop hy
      rw [hm] at hρs
      have hMM := retype_mem hρs.symm
      subst hMM
      -- the pointer: `q` plus the offset
      obtain ⟨k1, q1, h1, e1⟩ := ptrBase_den 8 p _ P hp
      obtain ⟨k2, q2, h2, e2⟩ := ptrBase_den 8 s.args[0]! _ q hq
      have hq12 := baseSame_den hM 8 _ _ hbase h1 h2
      have hP : P = q.add (BitVec.ofNat 64
          ((ptrBase tabs f 8 p).2 - (ptrBase tabs f 8 s.args[0]!).2).toNat) := by
        rw [e1, e2, hq12, ptr_add_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          BitVec.add_comm (ptrBase tabs f 8 s.args[0]!).2, BitVec.sub_add_cancel]
      have hrd := read_write_self hwr
      rw [Array.size_replicate] at hrd
      rw [hP, read_sub hrd (Nat.pos_of_ne_zero hn) hle, Array.extract_replicate]
      congr 2
      omega

theorem dropOK_spec {u w : Value} (h : dropOK tabs f u w = true) :
    w.op = .Copy ∧ w.args.size = 1 ∧ (u.op = .Store ∨ u.op = .Zero) ∧ ∃ i < u.args.size,
      copyReach tabs f.valueTab f.valueTab.size u.args[i]! w.args[0]! = true := by
  unfold dropOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, hs⟩, (⟨⟨⟨hop, hsz⟩, hcr⟩, -⟩ | ⟨⟨⟨hop, hsz⟩, hcr⟩, -⟩)⟩ := h
  · exact ⟨hc, hs, .inl hop, 2, by omega, hcr⟩
  · exact ⟨hc, hs, .inr hop, 1, by omega, hcr⟩

/-- A memory refined by a value is a memory. -/
theorem refines_mem' {M : Mem} {v : Val} (h : Sem.Refines (.mem M) v) :
    ∃ M', v = .mem M' ∧ Mem.Refines M M' := by
  cases h with
  | mem h => exact ⟨_, rfl, h⟩

/-- **A dropped write is refined by its memory** (`dropOK`): the root's memory is refined by
the memory of `w`'s argument. -/
theorem drop_mem (hT : Term.Typed f.value? tabs ρ) (hM : MemAtoms f.value? tabs ρ) {u w : Value}
    (h : dropOK tabs f u w = true) {k : Nat} {y : Val}
    (hy : memDef tabs u (u.args.toList.map (den f.value? tabs ρ k)) = some y) :
    ∃ M1 M0, y = .mem M1 ∧ den f.value? tabs ρ k w.args[0]! = .mem M0 ∧ Mem.Refines M1 M0 := by
  unfold dropOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨-, (⟨⟨⟨hsop, hssz⟩, hcr⟩, hcase⟩ | ⟨⟨⟨hzop, hzsz⟩, hcr⟩, hcase⟩)⟩ := h
  · -- a `Store`
    rw [toList_three hssz, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hy
    obtain ⟨q, m0, M', hq, hm0, hwr, rfl⟩ := memDef_store (.inl hsop) hy
    have hc := copyReach_den (M := f.valueTab) hT _ _ _ hcr k
    rw [show den (Defs.get? f.valueTab) tabs ρ k u.args[2]! = .mem m0 from hm0] at hc
    obtain ⟨m0', hm0', hR⟩ := refines_mem' hc
    refine ⟨M', m0', rfl, hm0', Mem.Refines.trans ?_ hR⟩
    have hsz : (encode (auxTy tabs u.aux) (den f.value? tabs ρ k u.args[1]!)).size =
        (auxTy tabs u.aux).size := GoFV.Proof.CSE.Mem.encode_size _ _
    by_cases h0 : (auxTy tabs u.aux).size = 0
    · -- a zero-sized write changes nothing
      have he : (encode (auxTy tabs u.aux) (den f.value? tabs ρ k u.args[1]!)).isEmpty = true := by
        rw [Array.isEmpty_iff_size_eq_zero, hsz, h0]
      unfold Mem.write at hwr
      simp only [he, ite_true] at hwr
      cases hwr
      exact Mem.Refines.refl _
    rcases hcase with h0' | ⟨hzc, hch⟩
    · exact absurd h0' h0
    have hrd := zeroChain_read hT hM h0 hq 8 _ hch hm0
    rw [← hsz] at hrd
    refine write_refines_self (Mem.Refines.refl _) hrd hwr ?_
    have := zeros_refine (encode_zero (zeroConst_den (ρ := ρ) hzc k) (auxTy tabs u.aux))
    simpa [BytesRefineA] using this
  · -- a `Zero` of a `Zero`
    rw [toList_two hzsz, List.map_cons, List.map_cons, List.map_nil] at hy
    obtain ⟨q, m0, M', hq, hm0, hwr, rfl⟩ := memDef_zero hzop hy
    have hc := copyReach_den (M := f.valueTab) hT _ _ _ hcr k
    rw [show den (Defs.get? f.valueTab) tabs ρ k u.args[1]! = .mem m0 from hm0] at hc
    obtain ⟨m0', hm0', hR⟩ := refines_mem' hc
    refine ⟨M', m0', rfl, hm0', ?_⟩
    cases hz : f.value? w.args[0]! with
    | none => rw [hz] at hcase; cases hcase
    | some z =>
    rw [hz] at hcase
    simp only [Bool.and_eq_true, beq_iff_eq] at hcase
    obtain ⟨⟨⟨hzz, hz2⟩, hai⟩, hsame⟩ := hcase
    have hmem : memOp z.op = true := by rw [hzz]; rfl
    cases k with
    | zero => simp [den] at hm0
    | succ k =>
    change den f.value? tabs ρ (k + 1) w.args[0]! = _ at hm0'
    rw [den_succ_atom (not_term_of hz (by rw [memOp_not_term hmem]; decide))] at hm0'
    obtain ⟨N, hN⟩ := hM _ z hz hmem (by rw [hm0']; nofun)
    obtain ⟨y2, hy2, hρ2⟩ := hN N (Nat.le_refl _)
    rw [toList_two hz2, List.map_cons, List.map_cons, List.map_nil] at hy2
    obtain ⟨Q, m00, M2, hQ, -, hw2, rfl⟩ := memDef_zero hzz hy2
    rw [hm0'] at hρ2
    have hMM := retype_mem hρ2.symm
    subst hMM
    have hqQ := samePtr_den hM hsame hq hQ
    subst hqQ
    have hrd := read_write_self hw2
    rw [hai] at hrd
    exact write_refines_self hR hrd hwr (BytesRefineA.refl _)

end

end GoFV.Proof.Pass.LoadFwd
