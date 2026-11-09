import GoFV.Gen.Check28
import GoFV.Proof.Gen.Spec27

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G28 accepted (`docs/plans/proofs3.md` §4)

`checkG28 lc ps bstart g = .ok (tab, kt)` unfolded: on a function with an arm64 op, G27's facts
(`checkG28_spec`) with G28's value check (`vkind28_spec`, `VK28`: G27's values, and
`LoweredMemEq` as `CALL runtime.memequal(SB)`); on one without, G27's (`checkG27_of_28`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind28` accepted of a value that is not an entry value, and what it emits. -/
inductive VK28 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G27 (not `LoweredMemEq`). -/
  | g27 {kd : VKind2} : v.op ≠ .ARM64LoweredMemEq → VK27 lc g v kd → VK28 lc g v kd
  /-- `LoweredMemEq p q n mem`: `CALL runtime.memequal(SB)`. -/
  | memEq {a0 a1 a2 : ID} :
      v.op = .ARM64LoweredMemEq → v.args.size = 4 → lc.home v.id = some (.reg 0) →
      lc.ty v.id = .bool → v.args[0]? = some a0 → v.args[1]? = some a1 → v.args[2]? = some a2 →
      lc.home a0 = some (.reg 0) → lc.home a1 = some (.reg 1) → lc.home a2 = some (.reg 2) →
      cls (lc.ty a0) = some 64 → cls (lc.ty a1) = some 64 → cls (lc.ty a2) = some 64 →
      memArg lc v 3 = .ok () → VK28 lc g v (.prog (memEqPat g))

theorem memEqArg_spec {lc : LocCtx} {v : Value} {i : Nat} (h : memEqArg lc v i = true) :
    ∃ a, v.args[i]? = some a ∧ lc.home a = some (.reg i) ∧ cls (lc.ty a) = some 64 := by
  unfold memEqArg at h
  split at h
  · rename_i a ha
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨a, ha, h.1, h.2⟩
  · cases h

theorem boolTy_spec {t : Ty} (h : boolTy t = true) : t = .bool := by
  cases t <;> first | rfl | cases h

/-- What `memEqKind` accepted: no temporary, and `VK28`'s `memEq`. -/
theorem memEqKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64LoweredMemEq) (h : memEqKind lc g v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK28 lc g v kd := by
  unfold memEqKind at h
  by_cases ht : (lc.temps[v.id]?).join = none
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hs, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
    simp only [ex_pure, Except.ok.injEq] at h
    subst h
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨⟨⟨⟨hsz, hh⟩, hty⟩, h0⟩, h1⟩, h2⟩ := hs
    obtain ⟨a0, ha0, hh0, hc0⟩ := memEqArg_spec h0
    obtain ⟨a1, ha1, hh1, hc1⟩ := memEqArg_spec h1
    obtain ⟨a2, ha2, hh2, hc2⟩ := memEqArg_spec h2
    exact ⟨ht, .memEq hop hsz hh (boolTy_spec hty) ha0 ha1 ha2 hh0 hh1 hh2 hc0 hc1 hc2 hma⟩
  · have hne : ((lc.temps[v.id]?).join != none) = true := by simpa using ht
    simp only [hne, ↓reduceIte] at h
    exact (ex_throw_bind h).elim

/-- What `vkind28` accepted of a value that is not an entry value: no temporary, and `VK28`. -/
theorem vkind28_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind28 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK28 lc g v kd := by
  unfold vkind28 at h
  by_cases hop : v.op = .ARM64LoweredMemEq
  · simp only [hop, BEq.rfl, ↓reduceIte] at h
    exact memEqKind_spec hop h
  · have hne : (v.op == .ARM64LoweredMemEq) = false := by simpa using hop
    rw [hne] at h
    obtain ⟨htm, h27⟩ := vkind27_spec h hen
    exact ⟨htm, .g27 hop h27⟩

/-- On a function with no arm64 op, G28 is G27. -/
theorem checkG27_of_28 {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG28 lc ps bstart g = r) : checkG27 lc ps bstart g = r := by
  simpa [checkG27, checkG28, hl] using h

/-- What `checkG28` accepted of a function with an arm64 op: G27's facts with G28's value check. -/
theorem checkG28_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG28 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind28 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK lc = true := by
  simp only [checkG28, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
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
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd⟩
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

/-- The fields of the `CALL` of `LoweredMemEq`: the target `runtime.memequal(SB)`. -/
theorem memEqPat_spec {g : G2In} {p : Prog} (h : (memEqPat g).ok p = true) :
    p.as = .CALL ∧ p.from_ = {} ∧ p.reg = 0 ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧
      p.regTo2 = 0 ∧ p.to.type = .MEM ∧ p.to.name = .EXTERN ∧ p.to.offset = 0 ∧
      ∃ y, p.to.sym = some y ∧ g.syms[y]? = some memEqSym := by
  obtain ⟨has, hf, hr, ht, hsc, hrest, hr2⟩ := plain_spec h
  simp only [beq_iff_eq] at hf
  unfold memEqTarget at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨ht1, ht2⟩, -⟩, -⟩, ht5⟩, ht6⟩ := ht
  refine ⟨has, hf, hr, hsc, hrest, hr2, ht1, ht2, ht5, ?_⟩
  split at ht6
  · rename_i y hy
    exact ⟨y, hy, by simpa using ht6⟩
  · cases ht6

end GoFV.Gen.Check
