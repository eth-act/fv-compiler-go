import GoFV.Proof.Pass.LoadFwdInv
import GoFV.Proof.Pass.RewriteTerm

variable [GoFV.SSA.Sem.Addrs]

/-!
# Fixed loads from read-only symbols (issue #69)

`generic.rules:2251`/`:2255` (`rewriteFixedLoad`) replace a `Load` from a read-only symbol at a
constant offset (a relocation target in a `.dict.` symbol, a type descriptor's size word, …) by
the `Addr` or constant it reads; the forwarding layer validates each instance
(`RewriteCheck.fixedOK`): the Load's pointer is an `Addr` of a symbol of `ro` at a constant
offset, and the read from the symbol's allocation alone is `poison` or the new value.

In a function that passes `WBCheck.memTyOK`, the forwarding layer's frame invariant (`FwdQ`)
puts the read-only symbols `ro` into every memory a register holds, hence into every memory a
listed value denotes as a term (`den_memsOK`: terms that may hold memories are copies and
selections, `pureMemOps`). The Load reads a memory holding the symbol's allocation, so it reads
what `fixedSrc` reads (`fixed_den`).
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.CSE.Mem GoFV.Proof.Pass.Rewrite

/-- The term ops among the ops whose values may hold memories are copies, selections and the
atomic loads (`MemInv.pureMemOps`). -/
theorem term_memOp {o : Op} (hop : WBCheck.memOpOK o = true) (ht : termOp o = true) :
    o ∈ MemInv.pureMemOps := by
  have key : ∀ o ∈ WBCheck.memOps ++ WBCheck.atomicRootOps, termOp o = true →
      o ∈ MemInv.pureMemOps := by decide
  refine key o ?_ ht
  simp only [WBCheck.memOpOK, Bool.or_eq_true, List.contains_iff_mem] at hop
  exact List.mem_append.2 hop

theorem pureMemOps_frameOp : ∀ o ∈ MemInv.pureMemOps, GoFV.Proof.Rules.frameOp o = false := by
  decide

theorem memFreeOps_frameOp : ∀ o ∈ WBCheck.memFreeOps, GoFV.Proof.Rules.frameOp o = false := by
  decide

/-- The term ops of `memFreeOps` (integer ops of tuple type) give values without memories. -/
theorem evalPure_memFreeOps {o : Op} (hop : WBCheck.memFreeOps.contains o = true)
    (ht : termOp o = true) (ty : Ty) (k : Int64) (ax : Option AuxRef) (argv : List Val) :
    (evalPure o ty k ax argv).mems = [] := by
  have hm : o ∈ WBCheck.memFreeOps := List.contains_iff_mem.1 hop
  simp only [WBCheck.memFreeOps, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact MemInv.int2_mems .w32 _ (fun _ _ => rfl) argv
  · exact MemInv.int2_mems .w64 _ (fun _ _ => rfl) argv
  · exact MemInv.int2_mems .w32 _ (fun _ _ => rfl) argv
  · exact MemInv.int2_mems .w64 _ (fun _ _ => rfl) argv
  · exact MemInv.int3_mems .w64 _ (fun _ _ _ => by split <;> rfl) argv
  · exact MemInv.int3_mems .w64 _ (fun _ _ _ => by split <;> rfl) argv
  · exact MemInv.int3_mems .w64 _ (fun _ _ _ => by split <;> rfl) argv
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

/-- **The memories a listed value denotes**: in a function that passes `WBCheck.memTyOK`, the
memories inside a listed value's term are among the registers' (`P` holds of them all). -/
theorem den_memsOK {tabs : Tables} {f : Func} {P : Mem → Prop}
    (hm : WBCheck.memTyOK tabs f = true) (hcf : closedOK f = true) {ρ : ID → Val}
    (hρ : ∀ a, MemInv.MemsOK P (ρ a)) :
    ∀ (k : Nat) (x : ID), LM f x → MemInv.MemsOK P (den f.value? tabs ρ k x)
  | 0, _, _ => MemInv.memsOK_poison
  | k + 1, x, hx => by
    cases hv : f.value? x with
    | none =>
      rw [den_succ_atom (fun ⟨v, h, _⟩ => by rw [hv] at h; cases h)]
      exact hρ x
    | some v =>
      by_cases ht : termOp v.op = true
      · rw [den_succ_term hv ht]
        obtain ⟨b, hb, fb, hfb, hxv, u', hu', -⟩ := listedMarks_sound f x hx
        rw [hv] at hu'; cases hu'
        have hxb : x ∈ WBCheck.vals f b := by
          simp only [WBCheck.vals, hfb, Option.map_some, Option.getD_some]; exact hxv
        have hargs : ∀ a ∈ v.args.toList.map (den f.value? tabs ρ k), MemInv.MemsOK P a := by
          intro a ha
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
          exact den_memsOK hm hcf hρ k y
            ((closedOK_facts hcf b hb fb hfb).2 x hxv v hv y (Array.mem_toList_iff.1 hy))
        rcases MemInv.memTyOK_val hm hb hxb hv with hfree | hop | hit
        · exact MemInv.memsOK_of_mems_nil (MemInv.retype_memFree _ hfree _)
        · have hp := term_memOp hop ht
          rw [GoFV.Proof.Rules.opVal_pure (pureMemOps_frameOp _ hp)]
          exact (MemInv.evalPure_mems hp _ _ _ hargs).retype _
        · rw [GoFV.Proof.Rules.opVal_pure
            (memFreeOps_frameOp _ (List.contains_iff_mem.1 hit))]
          exact MemInv.memsOK_of_mems_nil
            (MemInv.nil_of_retype _ _ (evalPure_memFreeOps hit ht _ _ _ _))
      · rw [den_succ_atom (not_term_of hv ht)]
        exact hρ x

theorem fixedEq_spec {a b : Val} (h : fixedEq a b = true) : a = .poison ∨ a = b := by
  unfold fixedEq at h
  split at h
  · exact .inl rfl
  · split at h
    · next hw => subst hw; simp only [beq_iff_eq] at h; subst h; exact .inr rfl
    · cases h
  · simp only [beq_iff_eq] at h; subst h; exact .inr rfl
  · cases h

/-- What `fixedOK` checks. -/
theorem fixedOK_spec {tabs : Tables} {ro : List (String × Alloc)} {f : Func} {u w : Value}
    (h : fixedOK tabs ro f u w = true) :
    u.op = .Load ∧ u.args.size = 2 ∧
      (w.op = .Addr ∨ (((w.op = .Const64 ∨ w.op = .Const32) ∨ w.op = .Const8) ∧ w.args.size = 0)) ∧
      ∃ n e s r, baseBlk? tabs f (ptrBase tabs f 8 u.args[0]!).1 = some (.global n) ∧ e ∈ ro ∧
        e.1 = n ∧ fixedSrc n e.2 (tabs.ty u.type) (ptrBase tabs f 8 u.args[0]!).2 = some s ∧
        GoFV.Proof.Rules.opValC tabs w.op (tabs.ty u.type) w.auxInt w.aux [] = some r ∧
        fixedEq s (r.retypeC (tabs.ty u.type)) = true ∧
        WBCheck.memTyOK tabs f = true := by
  unfold fixedOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hld, hsz⟩, hw⟩, hb⟩, hmt⟩ := h
  refine ⟨hld, hsz, hw, ?_⟩
  split at hb
  · next n hB =>
    obtain ⟨e, he, hen⟩ := List.any_eq_true.1 hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hen
    obtain ⟨hen, hq⟩ := hen
    split at hq
    · next s r hs hr => exact ⟨n, e, s, r, hB, he, hen, hs, hr, hq, hmt⟩
    · cases hq
  · cases hb

/-- `fixedSrc` reads what a load from the allocation alone reads under every instance. -/
theorem fixedSrc_eq {n : String} {a : Alloc} {t : Ty} {o : BitVec 64} {s : Val}
    (h : fixedSrc n a t o = some s) :
    ((({} : Mem).set (.global n) a).load t ((⟨.global n, 0⟩ : Ptr).add o)).retype t = s := by
  unfold fixedSrc at h
  simp only at h
  split at h
  · rename_i hm
    split at h
    · rename_i hv
      cases h
      rw [← Mem.loadC_eq hm, Val.retypeC_eq hv]
    · cases h
  · cases h

/-- The new definition of a fixed load is a term node. -/
theorem fixedOK_term {tabs : Tables} {ro : List (String × Alloc)} {f : Func} {u w : Value}
    (h : fixedOK tabs ro f u w = true) : termOp w.op = true := by
  obtain ⟨-, -, hw, -⟩ := fixedOK_spec h
  rcases hw with h | ⟨(h | h) | h, -⟩ <;> rw [h] <;> rfl

theorem loadOp_other {t : Ty} {p m : Val} (h : ¬ ∃ a M, p.asPtrWord = some a ∧ m = .mem M) :
    loadOp t [p, m] = .poison := by
  unfold loadOp
  split
  · rename_i a M heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl, -⟩ := heq
    split
    · rename_i q hq; exact absurd ⟨q, M, hq, rfl⟩ h
    · rfl
  · rfl

/-- Reads that see the same allocation of the pointer's block are equal. -/
theorem read_congr_find {m m' : Mem} {p : Ptr} (h : m.find? p.blk = m'.find? p.blk) (n : Nat) :
    m.read p n = m'.read p n := by
  unfold Mem.read
  rw [h]

/-- **A fixed load** (`fixedOK`): the Load reads a memory holding the read-only symbol's
allocation (`den_memsOK`, `FwdQ`), at the symbol's block (`ptrBase_den`, `baseBlk_den`), so it
reads what `fixedSrc` reads from the allocation alone: `poison` or the new definition's value. -/
theorem fixed_den {tabs : Tables} {ro : List (String × Alloc)} {f : Func} {g : ID → Option Value}
    {ρ ρ' : ID → Val} (hM : MemAtoms f.value? tabs ρ) (hQ : FwdQ tabs ro f ρ)
    (hcf : closedOK f = true) {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hargs : ∀ a ∈ u.args, LM f a) (hL : g x = some w) (hwty : w.type = u.type)
    (h : fixedOK tabs ro f u w = true) (n : Nat) :
    Sem.Refines (den f.value? tabs ρ (n + 1) x) (den g tabs ρ' 1 x) := by
  obtain ⟨hld, hsz, hw, n0, e, s, r, hB, he, hen, hs, hr, hfx, hmt⟩ := fixedOK_spec h
  have hLt : termOp u.op = true := by rw [hld]; decide
  show Sem.Refines _ (den g tabs ρ' (0 + 1) x)
  rw [den_succ_term hu hLt, toList_two hsz, List.map_cons, List.map_cons, List.map_nil, hld,
    GoFV.Proof.Rules.opVal_pure (op := Op.Load) rfl, evalPure_load,
    den_succ_term hL (fixedOK_term h), hwty]
  have htgt : GoFV.Proof.Rules.opVal tabs w.op (tabs.ty u.type) w.auxInt w.aux
      (w.args.toList.map (den g tabs ρ' 0)) =
      GoFV.Proof.Rules.opVal tabs w.op (tabs.ty u.type) w.auxInt w.aux [] := by
    rcases hw with hA | ⟨-, h0⟩
    · rw [hA, GoFV.Proof.Rules.opVal_addr, GoFV.Proof.Rules.opVal_addr]
    · rw [List.eq_nil_of_length_eq_zero (by simpa using h0 : w.args.toList.length = 0)]
      rfl
  rw [htgt]
  by_cases hcase : ∃ a M, (den f.value? tabs ρ n u.args[0]!).asPtrWord = some a ∧
      den f.value? tabs ρ n u.args[1]! = .mem M
  · obtain ⟨P, M, hpa, hsM⟩ := hcase
    rw [hsM]
    simp only [loadOp, hpa]
    obtain ⟨k', q, hq, hPq⟩ := ptrBase_den 8 u.args[0]! n P hpa
    have hq' := baseBlk_den hM hB hq
    subst hq' hPq hen
    have hu1 : u.args[1]! ∈ u.args := by
      rw [getElem!_pos u.args 1 (by omega)]; exact Array.getElem_mem _
    have hR : RoMem ro M := by
      have := den_memsOK hmt hcf (hQ.2.1 hmt) n _ (hargs _ hu1)
      rw [hsM] at this
      exact this.mem
    have hld' : M.load (tabs.ty u.type) ((⟨.global e.1, 0⟩ : Ptr).add (ptrBase tabs f 8 u.args[0]!).2)
        = (({} : Mem).set (.global e.1) e.2).load (tabs.ty u.type)
          ((⟨.global e.1, 0⟩ : Ptr).add (ptrBase tabs f 8 u.args[0]!).2) := by
      apply load_congr_read
      apply read_congr_find
      show M.find? (.global e.1) = (({} : Mem).set (.global e.1) e.2).find? (.global e.1)
      rw [(hR e.1 e.2 he).2, find?_set]
      simp
    rw [hld']
    obtain ⟨hr, hrl⟩ := GoFV.Proof.Rules.opValC_eq hr
    rw [fixedSrc_eq hs, hr, ← Val.retypeC_eq hrl]
    rcases fixedEq_spec hfx with h0 | h0
    · rw [h0]; exact .poison _
    · rw [h0]; exact .refl _
  · rw [loadOp_other hcase, AtomSim.retype_poison]; exact .poison _

end GoFV.Proof.Pass.LoadFwd
