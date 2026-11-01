import GoFV.Proof.Pass.MemCombineList

/-!
# memcombine: descriptions, loads and ops (issue #35)

* Memory bytes: a valid concrete read gives each of its bytes as a one-byte read
  (`byteAt_of_read`), so the bytes `mb` of a load in range are defined (`mb_sem`).
* `Backed bs sd`: every memory byte of a description lies in one of its loads (`symOf_backed`), so
  a description without opaque bytes whose loads are valid is defined (`semL_of_backed`).
* `symOp_cases`: the op cases of `symOp`; the `…W_spec` lemmas give each op class's evaluation.
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.MemCombine.Check GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-! ## Memory bytes -/

theorem ptrAt_add (P : Ptr) (I : BitVec 64) (o : _root_.Int) (k : Nat) :
    ptrAt P I (o + k) = (ptrAt P I o).add (BitVec.ofNat 64 k) := by
  simp only [ptrAt, Ptr.add, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]

theorem ptrAt_le {P : Ptr} {I : BitVec 64} {o o' : _root_.Int} (h : o ≤ o') :
    ptrAt P I o' = (ptrAt P I o).add (BitVec.ofNat 64 (o' - o).toNat) := by
  rw [← ptrAt_add]
  congr 1
  omega

theorem read_size {M : Mem} {Q : Ptr} {n : Nat} {bs : Array Byte} (h : M.read Q n = some bs) :
    bs.size = n := by
  by_cases hn : n = 0
  · subst hn; cases h; rfl
  · obtain ⟨a, -, h1, -, -, rfl⟩ := (read_eq_some hn).1 h
    simp only [Array.size_extract]
    omega

theorem byteAt_of_read {M : Mem} {Q : Ptr} {n : Nat} {bs : Array Byte} (h : M.read Q n = some bs)
    {j : Nat} (hj : j < n) {c : BitVec 8} (hc : bs[j]? = some (.b c)) :
    byteAt M (Q.add (BitVec.ofNat 64 j)) = some c := by
  unfold byteAt
  rw [read_extract h (j := j) (k := 1) (by omega)]
  have hs := read_size h
  have : (bs.extract j (j + 1))[0]? = bs[j]? := by
    simp [Array.getElem?_extract, show j < bs.size by omega]
    omega
  simp only [this, hc]

/-- All bytes of an array are concrete: each index holds one. -/
theorem concrete_getElem? {bs : Array Byte} (hc : Concrete bs) {j : Nat} (hj : j < bs.size) :
    ∃ c, bs[j]? = some (.b c) := by
  obtain ⟨c, hc'⟩ := hc bs[j] (Array.mem_toList_iff.2 (Array.getElem_mem hj))
  exact ⟨c, by rw [Array.getElem?_eq_getElem hj, hc']⟩

/-- A memory byte inside a concrete read is defined, as that byte. -/
theorem mb_sem {V : ID → Val} {m b : ID} {i : Option ID} {o o' : _root_.Int} {n : Nat}
    {M : Mem} {P : Ptr} {I : BitVec 64} {bs : Array Byte} (hm : V m = .mem M) (hp : V b = .ptr P)
    (hI : idxVal V i = some I) (hrd : M.read (ptrAt P I o) n = some bs) (h1 : o ≤ o')
    (h2 : o' < o + n) {c : BitVec 8} (hc : bs[(o' - o).toNat]? = some (.b c)) :
    (SB.mb m b i o').sem V = some c := by
  simp only [SB.sem, hm, hp, hI]
  rw [ptrAt_le h1]
  exact byteAt_of_read hrd (by omega) hc

/-! ## Memory bytes lie in loads -/

/-- Every memory byte of `bs` lies in a load of `sd`. -/
def Backed (bs : List SB) (sd : List LoadRec) : Prop :=
  ∀ m b i o, SB.mb m b i o ∈ bs → ∃ r ∈ sd, r.mem = m ∧ r.base = b ∧ r.idx = i ∧ r.off ≤ o ∧
    o < r.off + r.size

theorem Backed.sub {bs bs' : List SB} {sd sd' : List LoadRec} (h : Backed bs sd)
    (hb : ∀ s ∈ bs', s.isMb = true → s ∈ bs) (hs : ∀ r ∈ sd, r ∈ sd') : Backed bs' sd' :=
  fun m b i o hm => by
    obtain ⟨r, hr, h'⟩ := h m b i o (hb _ hm rfl)
    exact ⟨r, hs r hr, h'⟩

/-- A description without opaque bytes, whose memory bytes lie in valid loads, is defined. -/
theorem semL_of_backed {V : ID → Val} {l : List SB} {sd : List LoadRec} (hv : noVb l = true)
    (hb : Backed l sd) (hl : ∀ r ∈ sd, LoadOK V r) : ∃ C, semL V l = some C := by
  apply semL_of_forall
  intro s hs
  cases s with
  | lit c => exact ⟨c, rfl⟩
  | vb y k =>
    have := List.all_eq_true.1 hv _ hs
    simp [SB.vbId?] at this
  | mb m b i o =>
    obtain ⟨r, hr, rfl, rfl, rfl, h1, h2⟩ := hb m b i o hs
    obtain ⟨M, P, I, bs, hm, hp, hI, -, hrd, hc⟩ := hl r hr
    obtain ⟨c, hc'⟩ := concrete_getElem? hc (j := (o - r.off).toNat) (by rw [read_size hrd]; omega)
    exact ⟨c, mb_sem hm hp hI hrd h1 h2 hc'⟩

/-! ## The op cases of `symOp` -/

theorem symArg_spec {rec : ID → Option Desc} {a : ID} {w : Width} {r : Desc}
    (h : symArg rec a w = some r) : rec a = some r ∧ r.1.length = w.bytes := by
  unfold symArg at h
  cases hr : rec a with
  | none => rw [hr] at h; cases h
  | some r' =>
    rw [hr] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h; exact ⟨rfl, ‹_›⟩
    · cases h

theorem keepB_spec {tgt : Bool} {kept dropped : List SB} {sd : List LoadRec} {r : Desc}
    (h : keepB tgt kept dropped sd = some r) : r = (kept, sd) ∧ (tgt = true → noVb dropped = true) := by
  unfold keepB at h
  split at h
  · cases h
    rename_i hc
    refine ⟨rfl, fun ht => ?_⟩
    subst ht
    simpa using hc
  · cases h

/-- The op cases of `symOp`. -/
theorem symOp_cases {tabs : Tables} {D : ID → Option Value} {tgt : Bool} {rec : ID → Option Desc} {v : Value}
    {wt : Width} {r : Desc} (h : symOp tabs D tgt rec v wt = some r) :
    (∃ w, constW v.op = some w ∧ v.args.size = 0 ∧ r = (litBytes w.bytes v.auxInt.toInt, [])) ∨
    (v.op = .Copy ∧ v.args.size = 1 ∧ rec v.args[0]! = some r) ∨
    (v.op = .Load ∧ symLoad tabs D tgt v wt = some r) ∨
    (∃ w w' a, zextW v.op = some (w, w') ∧ v.args.size = 1 ∧ symArg rec v.args[0]! w = some a ∧
      r = (a.1 ++ zeros (w'.bytes - w.bytes), a.2)) ∨
    (∃ w w' a, truncW v.op = some (w, w') ∧ v.args.size = 1 ∧ symArg rec v.args[0]! w = some a ∧
      keepB tgt (a.1.take w'.bytes) (a.1.drop w'.bytes) a.2 = some r) ∨
    (∃ w, lshW v.op = some w ∧ symLsh tabs D tgt rec w v = some r) ∨
    (∃ w, rshuW v.op = some w ∧ symRsh tabs D tgt rec w v = some r) ∨
    (∃ w a, bswapW v.op = some w ∧ v.args.size = 1 ∧ symArg rec v.args[0]! w = some a ∧
      r = (a.1.reverse, a.2)) ∨
    (∃ w, orW v.op = some w ∧ symOr rec w v = some r) := by
  unfold symOp at h
  split at h
  · rename_i w hw
    split at h
    · cases h; exact .inl ⟨w, hw, ‹_›, rfl⟩
    · cases h
  split at h
  · split at h
    · exact .inr (.inl ⟨‹_›, ‹_›, h⟩)
    · cases h
  split at h
  · exact .inr (.inr (.inl ⟨‹_›, h⟩))
  split at h
  · rename_i w w' hw
    split at h
    · cases ha : symArg rec v.args[0]! w with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h; cases h
        exact .inr (.inr (.inr (.inl ⟨w, w', a, hw, ‹_›, ha, rfl⟩)))
    · cases h
  split at h
  · rename_i w w' hw
    split at h
    · cases ha : symArg rec v.args[0]! w with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h
        exact .inr (.inr (.inr (.inr (.inl ⟨w, w', a, hw, ‹_›, ha, h⟩))))
    · cases h
  split at h
  · rename_i w hw
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨w, hw, h⟩)))))
  split at h
  · rename_i w hw
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨w, hw, h⟩))))))
  split at h
  · rename_i w hw
    split at h
    · cases ha : symArg rec v.args[0]! w with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h; cases h
        exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨w, a, hw, ‹_›, ha, rfl⟩)))))))
    · cases h
  split at h
  · rename_i w hw
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨w, hw, h⟩)))))))
  · cases h

theorem symLoad_spec {tabs : Tables} {D : ID → Option Value} {tgt : Bool} {v : Value} {wt : Width} {r : Desc}
    (h : symLoad tabs D tgt v wt = some r) :
    v.args.size = 2 ∧ (tgt = false → wt.bytes < 8) ∧
    ptrTyped tabs D (splitP tabs D 64 v.args[0]! none 0).1 = true ∧
    r = ((List.range wt.bytes).map fun (k : Nat) => .mb v.args[1]! (splitP tabs D 64 v.args[0]! none 0).1
        (splitP tabs D 64 v.args[0]! none 0).2.1 ((splitP tabs D 64 v.args[0]! none 0).2.2 + (k : _root_.Int)),
      [⟨v.args[0]!, v.args[1]!, (splitP tabs D 64 v.args[0]! none 0).1,
        (splitP tabs D 64 v.args[0]! none 0).2.1, (splitP tabs D 64 v.args[0]! none 0).2.2, wt.bytes⟩]) := by
  unfold symLoad at h
  split at h
  · rename_i hc
    simp only at h
    split at h
    · cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hc
      refine ⟨hc.1, fun ht => ?_, ‹_›, rfl⟩
      rcases hc.2 with h | h
      · rw [ht] at h; cases h
      · simpa using h
    · cases h
  · cases h

theorem shiftBytes_spec {tabs : Tables} {D : ID → Option Value} {w : Width} {s : ID} {k : Nat}
    (h : shiftBytes tabs D w s = some k) :
    ∃ c, const64 tabs D s = some c ∧ 0 ≤ c ∧ c = 8 * k ∧ 8 * k < w.bits := by
  unfold shiftBytes at h
  cases hc : const64 tabs D s with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    simp only at h
    split at h
    · cases h
      rename_i hh
      exact ⟨c, rfl, hh.1, by omega, by omega⟩
    · cases h

theorem symLsh_spec {tabs : Tables} {D : ID → Option Value} {tgt : Bool} {rec : ID → Option Desc} {w : Width}
    {v : Value} {r : Desc} (h : symLsh tabs D tgt rec w v = some r) :
    ∃ k a, v.args.size = 2 ∧ shiftBytes tabs D w v.args[1]! = some k ∧
      symArg rec v.args[0]! w = some a ∧
      keepB tgt (zeros k ++ a.1.take (w.bytes - k)) (a.1.drop (w.bytes - k)) a.2 = some r := by
  unfold symLsh at h
  split at h
  · split at h
    · rename_i k hk
      cases ha : symArg rec v.args[0]! w with
      | none => rw [ha] at h; cases h
      | some a => rw [ha] at h; exact ⟨k, a, ‹_›, hk, rfl, h⟩
    · cases h
  · cases h

theorem symRsh_spec {tabs : Tables} {D : ID → Option Value} {tgt : Bool} {rec : ID → Option Desc} {w : Width}
    {v : Value} {r : Desc} (h : symRsh tabs D tgt rec w v = some r) :
    ∃ k a, v.args.size = 2 ∧ shiftBytes tabs D w v.args[1]! = some k ∧
      symArg rec v.args[0]! w = some a ∧
      keepB tgt (a.1.drop k ++ zeros k) (a.1.take k) a.2 = some r := by
  unfold symRsh at h
  split at h
  · split at h
    · rename_i k hk
      cases ha : symArg rec v.args[0]! w with
      | none => rw [ha] at h; cases h
      | some a => rw [ha] at h; exact ⟨k, a, ‹_›, hk, rfl, h⟩
    · cases h
  · cases h

theorem symOr_spec {rec : ID → Option Desc} {w : Width} {v : Value} {r : Desc}
    (h : symOr rec w v = some r) :
    ∃ a b c, v.args.size = 2 ∧ symArg rec v.args[0]! w = some a ∧ symArg rec v.args[1]! w = some b ∧
      orBytes a.1 b.1 = some c ∧ r = (c, a.2 ++ b.2) := by
  unfold symOr at h
  split at h
  · cases ha : symArg rec v.args[0]! w with
    | none => rw [ha] at h; cases h
    | some a =>
      cases hb : symArg rec v.args[1]! w with
      | none => rw [ha, hb] at h; cases h
      | some b =>
        rw [ha, hb] at h
        cases hc : orBytes a.1 b.1 with
        | none => simp [hc] at h
        | some c =>
          simp only [Option.bind_some, hc, Option.map_some, Option.some.injEq] at h
          exact ⟨a, b, c, ‹_›, rfl, rfl, hc, h.symm⟩
  · cases h

/-! ## The ops' evaluation -/

theorem constW_spec {op : Op} {w : Width} (h : constW op = some w) :
    termOp op = true ∧ Rules.frameOp op = false ∧
      ∀ ty ai aux args, evalPure op ty ai aux args = Conv.const w ai := by
  unfold constW at h
  split at h <;> cases h <;> exact ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem zextW_spec {op : Op} {w w' : Width} (h : zextW op = some (w, w')) :
    termOp op = true ∧ Rules.frameOp op = false ∧ w.bytes ≤ w'.bytes ∧
      ∀ ty ai aux args, evalPure op ty ai aux args = Conv.zeroExt w w' args := by
  unfold zextW at h
  split at h <;> cases h <;> exact ⟨rfl, rfl, by decide, fun _ _ _ _ => rfl⟩

theorem truncW_spec {op : Op} {w w' : Width} (h : truncW op = some (w, w')) :
    termOp op = true ∧ Rules.frameOp op = false ∧ w'.bytes ≤ w.bytes ∧
      ∀ ty ai aux args, evalPure op ty ai aux args = Conv.trunc w w' args := by
  unfold truncW at h
  split at h <;> cases h <;> exact ⟨rfl, rfl, by decide, fun _ _ _ _ => rfl⟩

theorem lshW_spec {op : Op} {w : Width} (h : lshW op = some w) :
    termOp op = true ∧ Rules.frameOp op = false ∧
      ∀ ty ai aux args, evalPure op ty ai aux args = Shift.lsh w .w64 (ai == 1) args := by
  unfold lshW at h
  split at h <;> cases h <;> exact ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem rshuW_spec {op : Op} {w : Width} (h : rshuW op = some w) :
    termOp op = true ∧ Rules.frameOp op = false ∧
      ∀ ty ai aux args, evalPure op ty ai aux args = Shift.rshu w .w64 (ai == 1) args := by
  unfold rshuW at h
  split at h <;> cases h <;> exact ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem bswapW_spec {op : Op} {w : Width} (h : bswapW op = some w) :
    termOp op = true ∧ Rules.frameOp op = false ∧
      ∀ ty ai aux args, evalPure op ty ai aux args = Int.bswap w args := by
  unfold bswapW at h
  split at h <;> cases h <;> exact ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem orW_spec {op : Op} {w : Width} (h : orW op = some w) :
    termOp op = true ∧ Rules.frameOp op = false ∧
      ∀ ty ai aux args, evalPure op ty ai aux args = Int.or w args := by
  unfold orW at h
  split at h <;> cases h <;> exact ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem copy_spec : termOp .Copy = true ∧ Rules.frameOp .Copy = false := ⟨rfl, rfl⟩

theorem load_spec : termOp .Load = true ∧ Rules.frameOp .Load = false := ⟨rfl, rfl⟩

/-- `symOp` describes term ops only, none of them a frame op. -/
theorem symOp_term {tabs : Tables} {D : ID → Option Value} {tgt : Bool} {rec : ID → Option Desc} {v : Value}
    {wt : Width} {r : Desc} (h : symOp tabs D tgt rec v wt = some r) :
    termOp v.op = true ∧ Rules.frameOp v.op = false := by
  rcases symOp_cases h with ⟨w, hw, -⟩ | ⟨ho, -⟩ | ⟨ho, -⟩ | ⟨w, w', a, hw, -⟩ | ⟨w, w', a, hw, -⟩ |
    ⟨w, hw, -⟩ | ⟨w, hw, -⟩ | ⟨w, a, hw, -⟩ | ⟨w, hw, -⟩
  · exact ⟨(constW_spec hw).1, (constW_spec hw).2.1⟩
  · rw [ho]; exact copy_spec
  · rw [ho]; exact load_spec
  · exact ⟨(zextW_spec hw).1, (zextW_spec hw).2.1⟩
  · exact ⟨(truncW_spec hw).1, (truncW_spec hw).2.1⟩
  · exact ⟨(lshW_spec hw).1, (lshW_spec hw).2.1⟩
  · exact ⟨(rshuW_spec hw).1, (rshuW_spec hw).2.1⟩
  · exact ⟨(bswapW_spec hw).1, (bswapW_spec hw).2.1⟩
  · exact ⟨(orW_spec hw).1, (orW_spec hw).2.1⟩

end GoFV.Proof.MemCombine
