import GoFV.Proof.Rules.ConstString
import GoFV.Proof.PtrAddr
import GoFV.Proof.Pass.LoadFwdMem
import GoFV.Rules.Generated.Generic.Values06

/-!
# Rule lemma: a `MemEq` of 25 to 32 bytes as two `MemEq`s (`generic.rules:1628`)

`(MemEq p q (Const64 [c]) mem) && c >= 25 && c <= 32 && … => (AndB (MemEq p q (Const64 [16])
mem) (MemEq (OffPtr p [16]) (OffPtr q [16]) (Const64 [c-16]) mem))` under `Rule.Sound` (issue
#69). A source `memEq` that is not `poison` read `c` bytes at `p` and at `q` (`memEq_some`); the
first 16 and the last `c - 16` of them are reads at `p`/`q` and at `p + 16`/`q + 16`
(`LoadFwd.read_sub`), which lie inside their windows (`LoadFwd.read_inWindow`), so `OffPtr [16]`
retyped at the operand's word shape reads as them (`offPtr16_asPtrWord`). The bytes compare
equal iff both halves do (`beq_split`), and the halves hold no `poison` byte either. Unlike the
splits `:1600`–`:1621`, the rule loads nothing: it holds at pointer fragments too.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

private theorem c_cases {c : Int} (h1 : 25 ≤ c) (h2 : c ≤ 32) :
    c = 25 ∨ c = 26 ∨ c = 27 ∨ c = 28 ∨ c = 29 ∨ c = 30 ∨ c = 31 ∨ c = 32 := by omega

/-- The length `c - 16` of the second `MemEq` (the auxint `wrapInt`s it). -/
private theorem len_sub (c : Int) (h1 : 25 ≤ c) (h2 : c ≤ 32) :
    (BitVec.ofInt 64 (wrapInt 64 true (c - 16))).toNat = c.toNat - 16 := by
  rcases c_cases h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem any_extract {a : Array Byte} (h : a.any (· == .poison) = false) (i j : Nat) :
    (a.extract i j).any (· == .poison) = false := by
  rw [Array.any_eq_false] at h ⊢
  intro x hx
  simp only [Array.size_extract] at hx
  rw [Array.getElem_extract]
  exact h _ (by omega)

/-- Byte arrays of one size are equal iff their first `k` and their remaining bytes are. -/
private theorem beq_split {a b : Array Byte} {n k : Nat} (ha : a.size = n) (hb : b.size = n)
    (hk : k ≤ n) :
    (a == b) = (a.extract 0 k == b.extract 0 k && a.extract k n == b.extract k n) := by
  have ea : a = a.extract 0 k ++ a.extract k n := by
    rw [Array.extract_append_extract, Nat.zero_min, Nat.max_eq_right hk, ← ha, Array.extract_size]
  have eb : b = b.extract 0 k ++ b.extract k n := by
    rw [Array.extract_append_extract, Nat.zero_min, Nat.max_eq_right hk, ← hb, Array.extract_size]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, Bool.and_eq_true]
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; rw [ea, eb, h1, h2]

section

variable [GoFV.SSA.Sem.Addrs]

/-- A `memEq` that is not `poison`: its operands' reads and their comparison. -/
private theorem memEq_some {x y n m : Val} (h : memEq [x, y, n, m] ≠ .poison) :
    ∃ p q w k M a b, x.asPtrWord = some p ∧ y.asPtrWord = some q ∧ n = .int w k ∧ m = .mem M ∧
      M.read p k.toNat = some a ∧ M.read q k.toNat = some b ∧
      a.any (· == .poison) = false ∧ b.any (· == .poison) = false ∧
      memEq [x, y, n, m] = .bool (a == b) := by
  unfold memEq at h
  split at h
  · rename_i p0 q0 w k M heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := heq
    split at h
    · rename_i p q hp hq
      split at h
      · rename_i a b ha hb
        split at h
        · exact absurd rfl h
        · rename_i hnp
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hnp
          refine ⟨p, q, w, k, M, a, b, hp, hq, rfl, rfl, ha, hb, hnp.1, hnp.2, ?_⟩
          simp [memEq, hp, hq, ha, hb, hnp.1, hnp.2]
      · exact absurd rfl h
    · exact absurd rfl h
  · exact absurd rfl h

/-- `OffPtr [16] x`, retyped at `x`'s shape, reads as `p + 16` when that is inside its window. -/
private theorem offPtr16_asPtrWord {x : Val} {t : Ty} {p : Ptr} (hx : x.asPtrWord = some p)
    (ht : x.hasTy t = true) (hw : (p.add (BitVec.ofNat 64 16)).inWindow = true) :
    (Val.retype t (PtrOps.offPtr (Int64.ofInt 16) [x])).asPtrWord =
      some (p.add (BitVec.ofNat 64 16)) := by
  have h16 : BitVec.ofInt 64 (Int64.ofInt 16).toInt = BitVec.ofNat 64 16 := by decide
  cases x with
  | ptr p0 =>
    simp only [Val.asPtrWord, Option.some.injEq] at hx; subst hx
    simp only [PtrOps.offPtr, h16, PtrOps.ptrRes, hw, ite_true]
    cases t with
    | ptr e => rw [Ptr.word_retype_ptr, Ptr.word_asPtrWord hw]
    | int w =>
      cases w <;> simp [Val.hasTy] at ht
      rw [Ptr.word_retype_i64, Ptr.word_asPtrWord hw]
    | _ => simp [Val.hasTy] at ht
  | int w a =>
    cases w <;> simp only [Val.asPtrWord, reduceCtorEq, Option.some.injEq] at hx
    subst hx
    simp only [PtrOps.offPtr, h16, PtrOps.wordRes, hw, ite_true]
    cases t with
    | ptr e => simp [Val.retype, Val.asPtrWord, Ptr.ofAddr_add_of_inWindow hw]
    | int w =>
      cases w <;> simp [Val.hasTy] at ht
      simp [Val.retype, Val.asPtrWord, Ptr.ofAddr_add_of_inWindow hw]
    | _ => simp [Val.hasTy] at ht
  | _ => simp [Val.asPtrWord] at hx

/-- The length constant `c` (25..32) at any shape of the `Const64` that reads as an integer. -/
private theorem retype_len {t : Ty} {c : Int} (h1 : 25 ≤ c) (h2 : c ≤ 32) {w : Width}
    {k : BitVec w.bits} (h : Val.retype t (Val.i64 (BitVec.ofInt 64 c)) = .int w k) :
    k.toNat = c.toNat := by
  cases t <;> simp only [Val.retype, reduceCtorEq] at h
  · split at h
    · cases h
      cases w <;> rcases c_cases h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · cases h
  · cases h; rcases c_cases h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `generic.rules:1628`: `(MemEq p q (Const64 [c]) mem) && c >= 25 && c <= 32 && canLoadUnaligned(config) && config.RegSize == 8 => (AndB (MemEq p q (Const64 <typ.Int64> [16]) mem) (MemEq (OffPtr <p.Type> p [16]) (OffPtr <q.Type> q [16]) (Const64 <typ.Int64> [c-16]) mem))` -/
theorem r_generic_1628_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1628 := by
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  have h0 : (e.leaf [0]).hasTy (e.ty [0]) = true := ‹_›
  have h1 : (e.leaf [1]).hasTy (e.ty [1]) = true := ‹_›
  have hc1 : (e.auxInt [2]).toInt ≥ 25 := ‹_›
  have hc2 : (e.auxInt [2]).toInt ≤ 32 := ‹_›
  generalize (e.auxInt [2]).toInt = c at hty hc1 hc2 ⊢
  generalize e.leaf [0] = x at h0 hty ⊢
  generalize e.leaf [1] = y at h1 hty ⊢
  generalize e.leaf [3] = m at hty ⊢
  by_cases hp : memEq [x, y, Val.retype (e.ty [2]) (Val.i64 (BitVec.ofInt 64 c)), m] = .poison
  · rw [hp]; exact Refines.poison _
  obtain ⟨p, q, w, k, M, a, b, hxp, hyq, hn, rfl, hra, hrb, hpa, hpb, hsrc⟩ := memEq_some hp
  rw [retype_len hc1 hc2 hn] at hra hrb
  rw [hsrc] at hty ⊢
  have htb : e.ty [] = .bool := by
    revert hty; cases e.ty [] <;> simp [Val.hasTy]
  have hsz : ∀ {s : Ptr} {bs : Array Byte}, M.read s c.toNat = some bs → bs.size = c.toNat := by
    intro s bs h
    obtain ⟨A, -, hA1, -, -, rfl⟩ := Pass.LoadFwd.read_some (by omega) h
    simp only [Array.size_extract]; omega
  have hp0 : ∀ s : Ptr, s.add (BitVec.ofNat 64 0) = s := fun s => by simp [Ptr.add]
  have hc16 : 16 + (c.toNat - 16) = c.toNat := by omega
  have hra1 := Pass.LoadFwd.read_sub hra (o := 0) (k := 16) (by omega) (by omega)
  have hrb1 := Pass.LoadFwd.read_sub hrb (o := 0) (k := 16) (by omega) (by omega)
  have hra2 := Pass.LoadFwd.read_sub hra (o := 16) (k := c.toNat - 16) (by omega) (by omega)
  have hrb2 := Pass.LoadFwd.read_sub hrb (o := 16) (k := c.toNat - 16) (by omega) (by omega)
  rw [hp0, Nat.zero_add] at hra1 hrb1
  rw [hc16] at hra2 hrb2
  have hx16 := offPtr16_asPtrWord hxp h0 (Pass.LoadFwd.read_inWindow hra (o := 16) (by omega))
  have hy16 := offPtr16_asPtrWord hyq h1 (Pass.LoadFwd.read_inWindow hrb (o := 16) (by omega))
  have h16 : (16#64 : BitVec 64).toNat = 16 := rfl
  have e1 : memEq [x, y, Val.int .w64 16#64, .mem M] =
      .bool (a.extract 0 16 == b.extract 0 16) := by
    simp only [memEq, hxp, hyq, h16, hra1, hrb1, any_extract hpa, any_extract hpb, Bool.or_false,
      Bool.false_eq_true, ite_false]
  have e2 : memEq [Val.retype (e.ty [0]) (PtrOps.offPtr (Int64.ofInt 16) [x]),
      Val.retype (e.ty [1]) (PtrOps.offPtr (Int64.ofInt 16) [y]),
      Val.int .w64 (BitVec.ofInt 64 (wrapInt 64 true (c - 16))), .mem M] =
      .bool (a.extract 16 c.toNat == b.extract 16 c.toNat) := by
    simp only [memEq, hx16, hy16, len_sub c hc1 hc2, hra2, hrb2, any_extract hpa,
      any_extract hpb, Bool.or_false, Bool.false_eq_true, ite_false]
  rw [e1, e2, beq_split (hsz hra) (hsz hrb) (show 16 ≤ c.toNat by omega), htb]
  cases (a.extract 0 16 == b.extract 0 16) <;>
    cases (a.extract 16 c.toNat == b.extract 16 c.toNat) <;> exact Refines.refl _

end

/-! ## Non-vacuity -/

/-- `generic.rules:1628` at `MemEq s s 32 mem`, `s` a global holding 32 zero bytes. -/
theorem inst_r_generic_1628 [GoFV.SSA.Sem.Addrs] :
    Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1628
      (PEnv.ofLists [([0], .ptr ⟨.global "s", 0⟩), ([1], .ptr ⟨.global "s", 0⟩),
          ([3], .mem { blocks := #[(.global "s", { data := Array.replicate 32 (.b 0) })] })]
        [([], .bool), ([0], .ptr none), ([1], .ptr none), ([2], .int .w64), ([3], .mem)]
        (.int .w64) [([2], 32)])
      (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1628]
  rule_eval
  simp [memEq, Mem.read, Mem.find?, Val.asPtrWord, Ptr.held, Ptr.convertible,
    Ptr.addr?, Blk.base?, Addrs.baseOf_global, Ptr.inWindow, Blk.window?, Blk.endsInWindow,
    Width.bits]
  have h : (Array.replicate 32 (Byte.b 0#8)).any (fun a => a == Byte.poison) 0 32 = false := by
    decide +kernel
  simp [h, Val.hasTy]

end GoFV.Proof.Rules
