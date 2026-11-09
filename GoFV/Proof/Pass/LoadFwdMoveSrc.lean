import GoFV.Proof.Pass.LoadFwdDrop
import GoFV.Proof.Pass.SegCall

variable [GoFV.SSA.Sem.Addrs]

/-!
# Changed `Move` sources: the memory facts (issue #151)

`generic.rules:2146`/`:2155` turn `Move dst tmp m` with `m = Move tmp' src _` (or `VarDef` of
it) into `Move dst src m` (`RewriteCheck.moveSrcOK`). In the source, `m` holds at `tmp` the bytes
the inner `Move` read at `src` (or `poison`, if the `VarDef` poisoned `tmp`'s frame variable);
`src` is disjoint from `tmp` and outside that variable, so `m` still holds those bytes at `src`:
`moveSrc_mem` is the memory argument, `moveSrcOK_spec`/`moveInnerOK_spec` what the validator
checked.
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.CSE.Mem

/-- Poisoning a block leaves the bytes of the other blocks. -/
theorem read_poisonBlock_ne {m : Mem} {b : Blk} {p : Ptr} (n : Nat) (h : p.blk ≠ b) :
    (m.poisonBlock b).read p n = m.read p n := by
  unfold Mem.poisonBlock
  cases hf : m.find? b with
  | none => rfl
  | some a =>
    simp only [Mem.read, find?_set, ite_eq_right (fun e : b = p.blk => h e.symm)]

private theorem read_size' {M : Mem} {p : Ptr} {n : Nat} {bs : Array Byte}
    (h : M.read p n = some bs) : bs.size = n := by
  by_cases hn : n = 0
  · subst hn; cases h; rfl
  · exact read_size hn h

/-- **The memory argument of a changed `Move` source.** The source copies `n` bytes from `T` in
`M` to `Dp`; `M` is refined by `M2`, which is refined by `M1` and agrees with it at `S`; `M1` is
`M0` with the `n` bytes at `S` copied to `T`, and `S`, `T` are separate. Then a memory `Mt`
refining `M2` has the bytes at `S`, and copying them to `Dp` refines the source's copy. -/
theorem moveSrc_mem {M M2 M1 M0 Mt M' : Mem} {T S Dp : Ptr} {n : Nat} {bs bs0 : Array Byte}
    (hM : Mem.Refines M M2) (h21 : Mem.Refines M2 M1) (hr21 : M2.read S n = M1.read S n)
    (hr0 : M0.read S n = some bs0) (hw0 : M0.write T bs0 = some M1) (hsep : Sep S n T n)
    (hrT : M.read T n = some bs) (hwD : M.write Dp bs = some M') (ht : Mem.Refines M2 Mt) :
    ∃ bs' Mt', Mt.read S n = some bs' ∧ Mt.write Dp bs' = some Mt' ∧ Mem.Refines M' Mt' := by
  have hsz : bs0.size = n := read_size' hr0
  have h1T : M1.read T n = some bs0 := hsz ▸ read_write_self hw0
  obtain ⟨b1, hb1, hbb1⟩ := (hM.trans h21).read hrT
  rw [h1T] at hb1
  cases hb1
  have h2S : M2.read S n = some bs0 := by
    rw [hr21, read_write_sep hw0 (by rw [hsz]; exact hsep), hr0]
  obtain ⟨b', hb', hbb'⟩ := ht.read h2S
  obtain ⟨Mt', hw', hMM⟩ := (hM.trans ht).write (BytesRefine.trans hbb1 hbb') hwD
  exact ⟨b', Mt', hb', hw', hMM⟩

/-- A `VarDef`'s value: its memory with its frame variable (activation 0) poisoned. -/
theorem memDef_varDef {tabs : Tables} {s : Value} (hs : s.op = .VarDef) {a y : Val}
    (h : memDef tabs s [a] = some y) :
    ∃ m n, a = .mem m ∧ s.aux = some n ∧ y = .mem (m.poisonBlock (frameBlk tabs 0 n)) := by
  cases a <;> try (simp [memDef, hs] at h; done)
  rename_i m
  simp only [memDef, hs, Option.map_eq_some_iff] at h
  obtain ⟨n, hn, rfl⟩ := h
  exact ⟨m, n, rfl, hn, rfl⟩

theorem moveInnerOK_spec {tabs : Tables} {f : Func} {u w im : Value} {B : Option Blk}
    (h : moveInnerOK tabs f u w im B = true) :
    im.op = .Move ∧ im.args.size = 3 ∧ im.auxInt = u.auxInt ∧
      samePtrB tabs f u.args[1]! im.args[0]! = true ∧
      copyReach tabs f.valueTab f.valueTab.size im.args[1]! w.args[1]! = true ∧
      disjointB tabs f im.args[1]! u.auxInt.toInt.toNat im.args[0]! u.auxInt.toInt.toNat = true ∧
      ∀ b, B = some b →
        (∃ Bs, baseBlk? tabs f (ptrBase tabs f 8 im.args[1]!).1 = some Bs ∧ Bs ≠ b) ∨
          tempBlk b = true ∧ argPtrB tabs f 8 im.args[1]! = true := by
  unfold moveInnerOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hop, hsz⟩, hai⟩, hsp⟩, hcr⟩, hdj⟩, hB⟩ := h
  refine ⟨hop, hsz, hai, hsp, hcr, hdj, fun b hb => ?_⟩
  subst hb
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hB
  rcases hB with hB | hB
  · left
    cases hk : baseBlk? tabs f (ptrBase tabs f 8 im.args[1]!).1 with
    | none => rw [hk] at hB; cases hB
    | some Bs =>
      rw [hk] at hB
      simp only [Option.any_some, bne_iff_ne, ne_eq] at hB
      exact ⟨Bs, rfl, hB⟩
  · exact .inr hB

theorem moveSrcOK_spec {tabs : Tables} {f : Func} {u w : Value} (h : moveSrcOK tabs f u w = true) :
    u.op = .Move ∧ w.op = .Move ∧ u.args.size = 3 ∧ w.args.size = 3 ∧ w.auxInt = u.auxInt ∧
      w.aux = u.aux ∧
      copyReach tabs f.valueTab f.valueTab.size u.args[0]! w.args[0]! = true ∧
      copyReach tabs f.valueTab f.valueTab.size u.args[2]! w.args[2]! = true ∧
      ∃ mv, f.value? w.args[2]! = some mv ∧
        (moveInnerOK tabs f u w mv none = true ∨
          ∃ n im, mv.op = .VarDef ∧ mv.args.size = 1 ∧ mv.aux = some n ∧
            f.value? mv.args[0]! = some im ∧
            moveInnerOK tabs f u w im (some (frameBlk tabs 0 n)) = true) := by
  unfold moveSrcOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨huop, hwop⟩, hu3⟩, hw3⟩, hai⟩, hax⟩, hc0⟩, hc2⟩, hm⟩ := h
  refine ⟨huop, hwop, hu3, hw3, hai, hax, hc0, hc2, ?_⟩
  cases hmv : f.value? w.args[2]! with
  | none => rw [hmv] at hm; cases hm
  | some mv =>
    rw [hmv] at hm
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
    refine ⟨mv, rfl, ?_⟩
    rcases hm with hm | ⟨⟨hvd, hsz⟩, hm⟩
    · exact .inl hm
    · refine .inr ?_
      cases han : mv.aux with
      | none => rw [han] at hm; cases hm
      | some n =>
        cases him : f.value? mv.args[0]! with
        | none => rw [han, him] at hm; cases hm
        | some im =>
          rw [han, him] at hm
          exact ⟨n, im, hvd, hsz, rfl, rfl, hm⟩

end GoFV.Proof.Pass.LoadFwd
