import GoFV.Gen.Check19
import GoFV.Proof.Gen.Spec18

/-!
# What the genssa validator's slice G19 accepted (`docs/plans/proofs3.md` §4)

`checkG19 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G19.lean`) uses (`checkG19_spec`): G18's (`Spec18.lean`) with G19's value check
(`vkind19_spec`, `VK19`: G18's values and the bounds panics), and the `PCDATA_PanicBounds` at each
bounds panic's `CALL` (`pbOK_spec`). `pbInfo_spec`: a bounds panic's operands and encoding.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind19` accepted of a value that is not an entry value, and what it emits. -/
inductive VK19 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G18 (not a bounds panic). -/
  | g18 {kd : VKind2} : pbOp v.op = false → VK18 lc g v kd → VK19 lc g v kd
  /-- A bounds panic: the memory shape and no home, its operands and encoding (`pbInfo`); the
  `MOVD`s of its moved constants and the `CALL`. -/
  | pb {c : Nat} {mvs : List (Nat × Int)} : pbOp v.op = true → memTy (lc.ty v.id) = true →
      lc.home v.id = none → pbInfo lc v = .ok (c, mvs) → VK19 lc g v (.progs (pbPats g mvs))

/-- What `pbKind` accepted. -/
theorem pbKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : pbKind lc g v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ memTy (lc.ty v.id) = true ∧ lc.home v.id = none ∧
      ∃ c mvs, pbInfo lc v = .ok (c, mvs) ∧ kd = .progs (pbPats g mvs) := by
  unfold pbKind at h
  obtain ⟨ht, h1⟩ := ex_guard h
  obtain ⟨hs, h2⟩ := ex_guard h1
  obtain ⟨⟨c, mvs⟩, hi, h3⟩ := ex_bind_eq_ok h2
  simp only [ex_pure, Except.ok.injEq] at h3
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  exact ⟨ht, hs.1, hs.2, c, mvs, hi, h3.symm⟩

/-- What `vkind19` accepted of a value that is not an entry value: no temporary, and `VK19`. -/
theorem vkind19_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind19 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK19 lc g v kd := by
  unfold vkind19 at h
  by_cases hop : pbOp v.op = true
  · rw [if_pos hop] at h
    obtain ⟨ht, hmt, hhn, c, mvs, hi, rfl⟩ := pbKind_spec h
    exact ⟨ht, .pb hop hmt hhn hi⟩
  · rw [if_neg hop] at h
    obtain ⟨ht, h18⟩ := vkind18_spec h hen
    exact ⟨ht, .g18 (by simpa using hop) h18⟩

theorem pbReg_spec {v : Value} {r : Int} {k : Nat} (h : pbReg v r = .ok k) :
    r = GoFV.Asm.ARM64.REG_R0 + k ∧ k ≤ 15 := by
  unfold pbReg at h
  obtain ⟨hr, h1⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  subst h1
  omega

theorem pbKindOf_spec {v : Value} {k : Nat} (h : pbKindOf v = .ok k) :
    v.auxInt.toInt = k ∧ k ≤ 16 := by
  unfold pbKindOf at h
  obtain ⟨hr, h1⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  subst h1
  omega

theorem pbConst_spec {c : Int} (h : pbConst c = true) : c = (c.toNat : Int) ∧ c.toNat ≤ 31 := by
  simp only [pbConst, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- What `pbInfo` accepted: the kind, and per op the operands (a register `REG_R0 + k`, `k ≤ 15`,
of class 64, or an aux constant), the memory last, the encoding and the moves. -/
theorem pbInfo_spec {lc : LocCtx} {v : Value} {c : Nat} {mvs : List (Nat × Int)}
    (h : pbInfo lc v = .ok (c, mvs)) : ∃ k : Nat, v.auxInt.toInt = k ∧ k ≤ 16 ∧
    ((v.op = .ARM64LoweredPanicBoundsRR ∧ v.args.size = 3 ∧ ∃ (rx ry : Int) (xv yv : Nat),
        argObj lc v 0 = .ok (64, rx) ∧ argObj lc v 1 = .ok (64, ry) ∧ memArg lc v 2 = .ok () ∧
        rx = GoFV.Asm.ARM64.REG_R0 + xv ∧ xv ≤ 15 ∧ ry = GoFV.Asm.ARM64.REG_R0 + yv ∧ yv ≤ 15 ∧
        c = pbEnc (k / 2) (pbSigned k) true true xv yv ∧ mvs = []) ∨
     (v.op = .ARM64LoweredPanicBoundsRC ∧ v.args.size = 2 ∧ ∃ (rx : Int) (xv : Nat) (cy : Int),
        argObj lc v 0 = .ok (64, rx) ∧ memArg lc v 1 = .ok () ∧
        rx = GoFV.Asm.ARM64.REG_R0 + xv ∧ xv ≤ 15 ∧ pbcOf lc v = some cy ∧
        ((pbConst cy = true ∧ c = pbEnc (k / 2) (pbSigned k) true false xv cy.toNat ∧ mvs = []) ∨
         (pbConst cy = false ∧
          c = pbEnc (k / 2) (pbSigned k) true true xv (if xv = 0 then 1 else 0) ∧
          mvs = [(if xv = 0 then 1 else 0, cy)]))) ∨
     (v.op = .ARM64LoweredPanicBoundsCR ∧ v.args.size = 2 ∧ ∃ (ry : Int) (yv : Nat) (cx : Int),
        argObj lc v 0 = .ok (64, ry) ∧ memArg lc v 1 = .ok () ∧
        ry = GoFV.Asm.ARM64.REG_R0 + yv ∧ yv ≤ 15 ∧ pbcOf lc v = some cx ∧ pbConst cx = true ∧
        c = pbEnc (k / 2) (pbSigned k) false true cx.toNat yv ∧ mvs = []) ∨
     (v.op = .ARM64LoweredPanicBoundsCC ∧ v.args.size = 1 ∧ ∃ (cx cy : Int),
        memArg lc v 0 = .ok () ∧ pbccOf lc v = some (cx, cy) ∧
        c = pbEnc (k / 2) (pbSigned k) (!pbConst cx) (!pbConst cy)
          (if pbConst cx then cx.toNat else 0) (if pbConst cy then cy.toNat else 1) ∧
        mvs = (if pbConst cx then [] else [(0, cx)]) ++ (if pbConst cy then [] else [(1, cy)]))) := by
  unfold pbInfo at h
  obtain ⟨k, hk, h⟩ := ex_bind_eq_ok h
  obtain ⟨hk1, hk2⟩ := pbKindOf_spec hk
  refine ⟨k, hk1, hk2, ?_⟩
  split at h
  · rename_i hop
    dsimp only at h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨cx, rx⟩, hax, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨cy, ry⟩, hay, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hm, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    dsimp only at hw
    obtain ⟨xv, hxv, h⟩ := ex_bind_eq_ok h
    obtain ⟨yv, hyv, h⟩ := ex_bind_eq_ok h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    simp only [beq_iff_eq] at hsz
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨hrx, hxl⟩ := pbReg_spec hxv
    obtain ⟨hry, hyl⟩ := pbReg_spec hyv
    exact .inl ⟨hop, hsz, rx, ry, xv, yv, hw.1 ▸ hax, hw.2 ▸ hay, hm, hrx, hxl, hry, hyl, h.1.symm,
      h.2.symm⟩
  · rename_i hop
    dsimp only at h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨cx, rx⟩, hax, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hm, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    dsimp only at hw
    obtain ⟨xv, hxv, h⟩ := ex_bind_eq_ok h
    simp only [beq_iff_eq] at hsz hw
    obtain ⟨hrx, hxl⟩ := pbReg_spec hxv
    cases hc : pbcOf lc v with
    | none => rw [hc] at h; dsimp only at h; simp [ex_throw] at h
    | some cy =>
      rw [hc] at h
      refine .inr (.inl ⟨hop, hsz, rx, xv, cy, hw ▸ hax, hm, hrx, hxl, rfl, ?_⟩)
      by_cases hp : pbConst cy = true
      · simp only [hp, ↓reduceIte, ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact .inl ⟨hp, h.1.symm, h.2.symm⟩
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, ex_pure, Except.ok.injEq, Prod.mk.injEq,
          beq_iff_eq] at h
        exact .inr ⟨by simpa using hp, h.1.symm, h.2.symm⟩
  · rename_i hop
    dsimp only at h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨cy, ry⟩, hay, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hm, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    dsimp only at hw
    obtain ⟨yv, hyv, h⟩ := ex_bind_eq_ok h
    simp only [beq_iff_eq] at hsz hw
    obtain ⟨hry, hyl⟩ := pbReg_spec hyv
    cases hc : pbcOf lc v with
    | none => rw [hc] at h; dsimp only at h; simp [ex_throw] at h
    | some cx =>
      rw [hc] at h
      obtain ⟨hp, h⟩ := ex_guard h
      simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact .inr (.inr (.inl ⟨hop, hsz, ry, yv, cx, hw ▸ hay, hm, hry, hyl, rfl, hp, h.1.symm,
        h.2.symm⟩))
  · rename_i hop
    dsimp only at h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hm, h⟩ := ex_bind_eq_ok h
    simp only [beq_iff_eq] at hsz
    cases hc : pbccOf lc v with
    | none => rw [hc] at h; dsimp only at h; simp [ex_throw] at h
    | some cc =>
      obtain ⟨cx, cy⟩ := cc
      rw [hc] at h
      simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
      refine .inr (.inr (.inr ⟨hop, hsz, cx, cy, hm, rfl, ?_, ?_⟩))
      · rw [← h.1]; cases pbConst cx <;> cases pbConst cy <;> rfl
      · rw [← h.2]; cases pbConst cx <;> cases pbConst cy <;> rfl
  · simp [ex_throw] at h

private theorem mem_of_lookup {l : List (ID × List Nat)} {b : ID} {r : List Nat}
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

/-- What `pbOK` checked: at a bounds panic at index `i` of block `bid` whose PC table row is `row`,
the `PCDATA_PanicBounds` in force at the Prog before `row`'s entry `i + 1` is its encoding. -/
theorem pbOK_spec {lc : LocCtx} {ps : List Prog} {tab : PcTab} (h : pbOK lc ps tab = true)
    {bid : ID} {row : List Nat} (hrow : tab.lookup bid = some row) {b : Block}
    (hb : lc.ctx.f.block? bid = some b) {i : Nat} {id : ID} (hi : b.values[i]? = some id)
    {v : Value} (hv : lc.ctx.f.value? id = some v) (hop : pbOp v.op = true) {c : Nat}
    {mvs : List (Nat × Int)} (hinfo : pbInfo lc v = .ok (c, mvs)) :
    pbData ps (row.getD (i + 1) 0 - 1) = some (constA c) := by
  unfold pbOK at h
  have hmem : (bid, row) ∈ tab := mem_of_lookup hrow
  have := List.all_eq_true.1 h _ hmem
  simp only [hb] at this
  have hi' : i < b.values.size := (Array.getElem?_eq_some_iff.1 hi).1
  have := List.all_eq_true.1 this i (List.mem_range.2 hi')
  simp only [hi, Option.bind_some, hv, hop, Bool.not_true, Bool.false_or, hinfo] at this
  simpa using this

/-- What `checkG19` accepted: G18's facts with G19's value check, and `pbOK`. -/
theorem checkG19_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG19 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind19 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true := by
  unfold checkG19 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  cases hf : List.find? (fun x => !homeOK10 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨-, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb⟩
    by_cases hi : i < lc.homes.size
    · have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
      simpa using this
    · have hh : lc.home i = none := by
        simp only [LocCtx.home]
        rw [getElem?_neg lc.homes i hi]
        rfl
      unfold homeOK10 homeOK4 homeOK3 homeOK2 homeOK
      rw [hh]
      rfl

end GoFV.Gen.Check
