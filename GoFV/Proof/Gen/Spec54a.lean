import GoFV.Gen.Check54a
import GoFV.Proof.Gen.Spec53a
import GoFV.Proof.Gen.Spec19

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `vkind54a` and `loopOK` accepted (`GoFV/Gen/Check54a.lean`)

`VK54a`: the values of G54's group A and what they emit: `LoweredZeroLoop [n] p mem` with its
temporary as the counter (`zero`), `LoweredMoveLoop [n] dst src mem` (`move`), each the loop of
`loopPats` and the tail (`vkind54a_spec`). `vkind54a` is `none` off `op54a` (`vkind54a_none`), and
every `VK54a` value's op is `op54a`'s (`vk54a_op`). `loopOK_spec`: at a loop value's start in the PC
table, `loopTgt` holds; `loopTgt_spec`: the Progs of a loop at that index split into the counter's
`MOVD`, the body, `SUB`, `CBNZ` and the tail, the `CBNZ` branching to the Prog after the `MOVD`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind54a` accepted, and what it emits. -/
inductive VK54a (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- `LoweredZeroLoop [n] p mem`: the loop with counter the temporary `t`, four `STP.P` a turn,
  then `zeroTail`'s stores of the `n mod 64` bytes left. -/
  | zero {t : Nat} {rp rc : Int} :
      v.op = .ARM64LoweredZeroLoop → (lc.temps[v.id]?).join = some t → v.args.size = 2 →
      memTy (lc.ty v.id) = true → lc.home v.id = none → argObj lc v 0 = .ok (64, rp) →
      memArg lc v 1 = .ok () → objOf? t = some rc → 64 ≤ v.auxInt.toInt →
      argDest lc v 0 = true → t < 26 → rc ≠ rp →
      zeroCovers (v.auxInt.toInt.toNat % 64) (zeroOffs (v.auxInt.toInt.toNat % 64)) = true →
      VK54a lc v (.progs (loopPats rc v.auxInt.toInt (zeroBody rp) ++
        (zeroOffs (v.auxInt.toInt.toNat % 64)).map (zeroPat rp)))
  /-- `LoweredMoveLoop [n] dst src mem`: no code if `dst` and `src` share their register, else the
  loop with counter `R24`, two `FLDPQ.P`/`FSTPQ.P` pairs a turn, then `moveTail`'s chunks. -/
  | move {rd rs : Int} :
      v.op = .ARM64LoweredMoveLoop → (lc.temps[v.id]?).join = none → v.args.size = 3 →
      memTy (lc.ty v.id) = true → lc.home v.id = none → argObj lc v 0 = .ok (64, rd) →
      argObj lc v 1 = .ok (64, rs) → memArg lc v 2 = .ok () → 64 ≤ v.auxInt.toInt →
      argDest lc v 0 = true → argDest lc v 1 = true → rd ≠ r24A → rs ≠ r24A → rd ≠ r25A →
      rs ≠ r25A →
      moveCovers (v.auxInt.toInt.toNat % 64) (moveOffs (v.auxInt.toInt.toNat % 64)) = true →
      VK54a lc v (.progs (if rd == rs then [] else
        loopPats r24A v.auxInt.toInt (moveBody rs rd) ++
          (moveOffs (v.auxInt.toInt.toNat % 64)).flatMap (movePats rs rd)))

/-- What `zeroLoopKind` accepted. -/
theorem zeroLoopKind_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64LoweredZeroLoop) (h : zeroLoopKind lc v = .ok kd) : VK54a lc v kd := by
  unfold zeroLoopKind at h
  cases ht : (lc.temps[v.id]?).join with
  | none => rw [ht] at h; simp [ex_throw] at h
  | some t =>
    rw [ht] at h
    simp only at h
    obtain ⟨hsh, h1⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsh
    obtain ⟨⟨c, rp⟩, hpo, h2⟩ := ex_bind_eq_ok h1
    obtain ⟨⟨⟩, hma, h3⟩ := ex_bind_eq_ok h2
    cases hrc : objOf? t with
    | none => rw [hrc] at h3; simp [ex_throw] at h3
    | some rc =>
      rw [hrc] at h3
      simp only at h3
      obtain ⟨hw, h4⟩ := ex_guard h3
      obtain ⟨hcov, h5⟩ := ex_guard h4
      simp only [ex_pure, Except.ok.injEq] at h5
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hw
      obtain ⟨⟨⟨⟨rfl, h64⟩, hdst⟩, ht26⟩, hne⟩ := hw
      rw [← h5]
      exact .zero hop ht hsh.1.1 hsh.1.2 hsh.2 hpo hma hrc h64 hdst ht26 hne hcov

/-- What `moveLoopKind` accepted. -/
theorem moveLoopKind_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64LoweredMoveLoop) (h : moveLoopKind lc v = .ok kd) : VK54a lc v kd := by
  unfold moveLoopKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  obtain ⟨hsh, h1⟩ := ex_guard h
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  obtain ⟨⟨cd, rd⟩, hdo, h2⟩ := ex_bind_eq_ok h1
  obtain ⟨⟨cs, rs⟩, hso, h3⟩ := ex_bind_eq_ok h2
  obtain ⟨⟨⟩, hma, h4⟩ := ex_bind_eq_ok h3
  obtain ⟨hw, h5⟩ := ex_guard h4
  obtain ⟨hcov, h6⟩ := ex_guard h5
  simp only [ex_pure, Except.ok.injEq] at h6
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, h64⟩, hd0⟩, hd1⟩, h24d⟩, h24s⟩, h25d⟩, h25s⟩ := hw
  rw [← h6]
  exact .move hop ht hsh.1.1 hsh.1.2 hsh.2 hdo hso hma h64 hd0 hd1 h24d h24s h25d h25s hcov

/-- What `vkind54a` accepted. -/
theorem vkind54a_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (h : vkind54a lc v = some (.ok kd)) : VK54a lc v kd := by
  unfold vkind54a at h
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    exact zeroLoopKind_spec (by simpa using hc) h
  next =>
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      exact moveLoopKind_spec (by simpa using hc) h
    next => cases h

/-- Off the ops of G54's group A, `vkind54a` is `none`. -/
theorem vkind54a_none {lc : LocCtx} {v : Value} (h : op54a v.op = false) :
    vkind54a lc v = none := by
  simp only [op54a, Bool.or_eq_false_iff] at h
  simp only [vkind54a, h.1, h.2, Bool.false_eq_true, ↓reduceIte]

/-- A value `VK54a` accepted has an op of G54's group A. -/
theorem vk54a_op {lc : LocCtx} {v : Value} {kd : VKind2} (h : VK54a lc v kd) :
    op54a v.op = true := by
  cases h with
  | zero hop => rw [hop]; rfl
  | move hop => rw [hop]; rfl

/-- What `argDest` decided: the argument is in register `r < 26`. -/
theorem argDest_spec {lc : LocCtx} {v : Value} {i : Nat} (h : argDest lc v i = true) :
    ∃ a r, v.args[i]? = some a ∧ lc.home a = some (.reg r) ∧ r < 26 := by
  unfold argDest at h
  cases ha : v.args[i]? with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h
    simp only [Option.bind_some] at h
    cases hr : regHome? lc a with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      exact ⟨a, r, rfl, regHome?_eq.1 hr, by simpa using h⟩

/-! ## The loops' targets -/

private theorem mem_of_lookup54 {l : List (ID × List Nat)} {b : ID} {r : List Nat}
    (h : l.lookup b = some r) : (b, r) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨a, x⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hba
      cases h
      simp only [beq_iff_eq] at hba
      subst hba
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- `loopOK` at a loop value: `loopTgt` at its start. -/
theorem loopOK_spec {lc : LocCtx} {ps : Array Prog} {tab : PcTab} (h : loopOK lc ps tab = true)
    {bid : ID} {row : List Nat} (hrow : tab.lookup bid = some row) {b : Block}
    (hb : lc.ctx.f.block? bid = some b) {i : Nat} {id : ID} (hi : b.values[i]? = some id)
    {v : Value} (hv : lc.ctx.f.value? id = some v) (hop : loopOp lc v = true) :
    loopTgt ps (row.getD i 0) = true := by
  unfold loopOK at h
  have hmem : (bid, row) ∈ tab := mem_of_lookup54 hrow
  have := List.all_eq_true.1 h _ hmem
  simp only [hb] at this
  have hi' : i < b.values.size := (Array.getElem?_eq_some_iff.1 hi).1
  have := List.all_eq_true.1 this i (List.mem_range.2 hi')
  simpa [hi, hv, hop] using this

/-- `skipFrom` stops at the first Prog that is not a no-op. -/
theorem skipFrom_eq (ps : Array Prog) {k : Nat} (hk : k < ps.size)
    (hnk : noop ps[k] = false) : ∀ (fuel j : Nat), j ≤ k → k - j < fuel →
      (∀ l (hl : l < ps.size), j ≤ l → l < k → noop ps[l] = true) → skipFrom ps j fuel = k
  | 0, j, _, h, _ => by omega
  | fuel + 1, j, hjk, hf, hno => by
    unfold skipFrom
    have hj : j < ps.size := by omega
    rw [Array.getElem?_eq_getElem hj]
    simp only
    by_cases hjk' : j = k
    · subst hjk'
      rw [if_neg (by rw [hnk]; nofun)]
    · rw [if_pos (hno j hj (Nat.le_refl _) (by omega))]
      exact skipFrom_eq ps hk hnk fuel (j + 1) (by omega) (by omega)
        (fun l hl h1 h2 => hno l hl (by omega) h2)

/-- A Prog `pat` matches only Progs that are not no-ops: after `OneAt2` from `j`, the index is
`nextIdx ps j`. -/
theorem oneAt2_next {ps : Array Prog} {j j' : Nat} {pat : Pat} (h : OneAt2 ps j pat j')
    (hpat : ∀ p, pat.ok p = true → noop p = false) : j' = nextIdx ps j := by
  obtain ⟨k, hjk, rfl, hk, hok, hno⟩ := h
  unfold nextIdx
  rw [skipFrom_eq ps hk (hpat _ hok) ps.size j hjk (by omega) hno]

/-- A Prog whose opcode is not a pseudo-op nor `HINT` is not a no-op. -/
theorem noop_of_as {p : Prog} (h1 : p.isSkip = false) (h2 : p.as ≠ .HINT) : noop p = false := by
  simp [noop, h1, Shape.ok, h2]

theorem okP_noop {sh : Shape} {p : Prog} (hs : sh.as ≠ .TEXT ∧ sh.as ≠ .FUNCDATA ∧
    sh.as ≠ .PCDATA ∧ sh.as ≠ .NOP ∧ sh.as ≠ .HINT) (h : sh.okP p = true) : noop p = false := by
  simp only [Shape.okP, Bool.and_eq_true, beq_iff_eq] at h
  have has := h.1.1.1.1.1.1
  refine noop_of_as ?_ (by rw [has]; exact hs.2.2.2.2)
  simp only [Prog.isSkip, has]
  obtain ⟨h1, h2, h3, h4, -⟩ := hs
  split <;> simp_all

theorem shape_noop {sh : Shape} {p : Prog} (hs : sh.as ≠ .TEXT ∧ sh.as ≠ .FUNCDATA ∧
    sh.as ≠ .PCDATA ∧ sh.as ≠ .NOP ∧ sh.as ≠ .HINT) (h : sh.ok p = true) : noop p = false := by
  simp only [Shape.ok, Bool.and_eq_true, beq_iff_eq] at h
  have has := h.1.1.1.1.1.1
  refine noop_of_as ?_ (by rw [has]; exact hs.2.2.2.2)
  simp only [Prog.isSkip, has]
  obtain ⟨h1, h2, h3, h4, -⟩ := hs
  split <;> simp_all

theorem cbnzPat_noop {rc : Int} {p : Prog} (h : (cbnzPat rc).ok p = true) : noop p = false := by
  simp only [cbnzPat, Bool.and_eq_true, beq_iff_eq] at h
  have has := h.1.1.1.1.1
  exact noop_of_as (by simp [Prog.isSkip, has]) (by rw [has]; nofun)

/-- A pattern whose Progs are not no-ops. -/
def Pat.Code (pat : Pat) : Prop := ∀ p, pat.ok p = true → noop p = false

theorem stpPPat_code (rp : Int) : (stpPPat rp).Code := fun _ h =>
  okP_noop (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nofun) h

theorem fldpqPPat_code (rs : Int) : (fldpqPPat rs).Code := fun _ h =>
  okP_noop (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nofun) h

theorem fstpqPPat_code (rd : Int) : (fstpqPPat rd).Code := fun _ h =>
  okP_noop (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nofun) h

/-- `ManyAt2` of a list of patterns, split at an append. -/
theorem manyAt2_append {ps : Array Prog} : ∀ {j j' : Nat} {a b : List Pat},
    ManyAt2 ps j (a ++ b) j' → ∃ k, ManyAt2 ps j a k ∧ ManyAt2 ps k b j'
  | j, _, [], _, h => ⟨j, rfl, h⟩
  | j, _, pat :: a, _, h => by
    obtain ⟨k, h1, h2⟩ := h
    obtain ⟨k', h3, h4⟩ := manyAt2_append h2
    exact ⟨k', ⟨k, h1, h3⟩, h4⟩

/-- The Progs of a loop: the counter's `MOVD` (index `k1 - 1`), the four body Progs to `kb`, `SUB`
and `CBNZ` (index `kc - 1`), the tail; when `loopTgt` holds at the start, the `CBNZ` branches to
the Prog at `k1`. -/
theorem loopTgt_spec {ps : Array Prog} {j j' : Nat} {rc n : Int} {b1 b2 b3 b4 : Pat}
    {tail : List Pat} (h : ManyAt2 ps j (loopPats rc n [b1, b2, b3, b4] ++ tail) j')
    (hc1 : b1.Code) (hc2 : b2.Code) (hc3 : b3.Code) (hc4 : b4.Code)
    (ht : loopTgt ps j = true) :
    ∃ k1 kb ks kc, OneAt2 ps j (.ofShape { as := .MOVD, from_ := constA (n / 64), to := regA rc })
        k1 ∧ ManyAt2 ps k1 [b1, b2, b3, b4] kb ∧
      OneAt2 ps kb (.ofShape { as := .SUB, from_ := constA 1, to := regA rc }) ks ∧
      OneAt2 ps ks (cbnzPat rc) kc ∧ ManyAt2 ps kc tail j' ∧
      ∃ (h1 : k1 < ps.size) (h2 : kc - 1 < ps.size), ps[kc - 1].to = brA ps[k1].id := by
  obtain ⟨k, hl, htl⟩ := manyAt2_append h
  simp only [loopPats, List.cons_append, List.nil_append] at hl
  obtain ⟨k1, hm, k2, hb1, k3, hb2, k4, hb3, kb, hb4, ks, hsub, kc, hcb, hnil⟩ := hl
  simp only [ManyAt2] at hnil
  subst hnil
  have e1 := oneAt2_next hm (fun _ hp => shape_noop (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nofun) hp)
  have e2 := oneAt2_next hb1 hc1
  have e3 := oneAt2_next hb2 hc2
  have e4 := oneAt2_next hb3 hc3
  have e5 := oneAt2_next hb4 hc4
  have e6 := oneAt2_next hsub
    (fun _ hp => shape_noop (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nofun) hp)
  have e7 := oneAt2_next hcb (fun _ hp => cbnzPat_noop hp)
  refine ⟨k1, kb, ks, k, hm, ⟨k2, hb1, k3, hb2, k4, hb3, kb, hb4, rfl⟩, hsub, hcb, htl, ?_⟩
  simp only [loopTgt] at ht
  rw [← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7] at ht
  split at ht
  · rename_i hh hc hh1 hc1'
    obtain ⟨hk1, rfl⟩ := Array.getElem?_eq_some_iff.1 hh1
    obtain ⟨hkc, rfl⟩ := Array.getElem?_eq_some_iff.1 hc1'
    exact ⟨hk1, hkc, by simpa using ht⟩
  · cases ht

end GoFV.Gen.Check
