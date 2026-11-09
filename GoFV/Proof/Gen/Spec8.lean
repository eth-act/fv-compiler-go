import GoFV.Gen.Check8
import GoFV.Proof.Gen.Spec7

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G8 accepted (`docs/plans/proofs3.md` §4)

`checkG8 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G8.lean`) uses (`checkG8_spec`): G7's (`Spec7.lean`) with G8's value check
(`vkind8_spec`, `VK8`: G7's values, the write-barrier buffer requests and their selections).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind8` accepted of a value that is not an entry value, and what it emits. -/
inductive VK8 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G7. -/
  | g7 {kd : VKind2} : VK7 lc g v kd → VK8 lc g v kd
  /-- `LoweredWB [n] mem`, `1 ≤ n ≤ 8`, of the shape `(pointer, mem)` homed in `(R25, -)`:
  `CALL runtime.gcWriteBarrier<n>(SB)`. -/
  | wb : v.op = .ARM64LoweredWB → 1 ≤ v.auxInt.toInt → v.auxInt.toInt ≤ 8 → v.args.size = 1 →
      lc.home v.id = some (.pair (some wbReg) none) → wbTy (lc.ty v.id) = true →
      memArg lc v 0 = .ok () → VK8 lc g v (.prog (wbPat g v.auxInt.toInt))
  /-- `Select0` of a write-barrier request, homed in `R25` at a 64-bit shape: no code. -/
  | sel0 {c : ID} : v.op = .Select0 → v.args.size = 1 → v.args[0]? = some c → wbArg lc c = true →
      lc.home v.id = some (.reg wbReg) → cls (lc.ty v.id) = some 64 → VK8 lc g v .none
  /-- `Select1` of a write-barrier request, the memory with no home: no code. -/
  | sel1 {c : ID} : v.op = .Select1 → v.args.size = 1 → v.args[0]? = some c → wbArg lc c = true →
      memTy (lc.ty v.id) = true → lc.home v.id = none → VK8 lc g v .none

/-- What `vkind8` accepted of a value that is not an entry value: no temporary, and `VK8`. -/
theorem vkind8_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : vkind8 lc g v = .ok kd)
    (hen : entryOp3 v.op = false) : (lc.temps[v.id]?).join = none ∧ VK8 lc g v kd := by
  unfold vkind8 at h
  split at h
  · rename_i hop
    by_cases ht : (lc.temps[v.id]?).join = none
    · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hs, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
      obtain ⟨⟨⟨⟨h1, h8⟩, hsz⟩, hh⟩, hty⟩ := hs
      obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      exact ⟨ht, VK8.wb hop h1 h8 hsz hh hty hma⟩
    · simp [ht, ex_throw, ex_bind_error] at h
  · rename_i hop
    split at h
    · rename_i c hc
      by_cases hw : wbArg lc c = true
      · simp only [hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        by_cases ht : (lc.temps[v.id]?).join = none
        · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨hsz, h⟩ := ex_guard h
          simp only [beq_iff_eq] at hsz
          simp only [hop, beq_self_eq_true, ↓reduceIte] at h
          obtain ⟨hs, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq] at hs
          simp only [ex_pure, Except.ok.injEq] at h
          subst h
          exact ⟨ht, VK8.sel0 hop hsz hc hw hs.1 hs.2⟩
        · simp [ht, ex_throw, ex_bind_error] at h
      · simp only [hw, Bool.not_false, ↓reduceIte] at h
        obtain ⟨ht, h7⟩ := vkind7_spec h hen
        exact ⟨ht, VK8.g7 h7⟩
    · obtain ⟨ht, h7⟩ := vkind7_spec h hen
      exact ⟨ht, VK8.g7 h7⟩
  · rename_i hop
    split at h
    · rename_i c hc
      by_cases hw : wbArg lc c = true
      · simp only [hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        by_cases ht : (lc.temps[v.id]?).join = none
        · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨hsz, h⟩ := ex_guard h
          simp only [beq_iff_eq] at hsz
          simp only [hop, show (Op.Select1 == Op.Select0) = false by decide, Bool.false_eq_true,
            ↓reduceIte] at h
          obtain ⟨hs, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq] at hs
          simp only [ex_pure, Except.ok.injEq] at h
          subst h
          exact ⟨ht, VK8.sel1 hop hsz hc hw hs.1 hs.2⟩
        · simp [ht, ex_throw, ex_bind_error] at h
      · simp only [hw, Bool.not_false, ↓reduceIte] at h
        obtain ⟨ht, h7⟩ := vkind7_spec h hen
        exact ⟨ht, VK8.g7 h7⟩
    · obtain ⟨ht, h7⟩ := vkind7_spec h hen
      exact ⟨ht, VK8.g7 h7⟩
  · obtain ⟨ht, h7⟩ := vkind7_spec h hen
    exact ⟨ht, VK8.g7 h7⟩

/-- The fields of the `CALL` of `LoweredWB [n]`: the target `runtime.gcWriteBarrier<n>(SB)`. -/
theorem wbPat_spec {g : G2In} {n : Int} {p : Prog} (h : (wbPat g n).ok p = true) :
    p.as = .CALL ∧ p.from_ = {} ∧ p.reg = 0 ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧
      p.regTo2 = 0 ∧ p.to.type = .MEM ∧ p.to.name = .EXTERN ∧ p.to.offset = 0 ∧
      ∃ y, p.to.sym = some y ∧ g.syms[y]? = some (wbSym n) := by
  obtain ⟨has, hf, hr, ht, hsc, hrest, hr2⟩ := plain_spec h
  simp only [beq_iff_eq] at hf
  unfold wbTarget at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨ht1, ht2⟩, -⟩, -⟩, ht5⟩, ht6⟩ := ht
  refine ⟨has, hf, hr, hsc, hrest, hr2, ht1, ht2, ht5, ?_⟩
  split at ht6
  · rename_i y hy
    exact ⟨y, hy, by simpa using ht6⟩
  · cases ht6

/-- What `checkG8` accepted: G7's facts with G8's value check. -/
theorem checkG8_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG8 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind8 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK4 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG8 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  cases hf : List.find? (fun x => !homeOK4 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb⟩
    by_cases hi : i < lc.homes.size
    · have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
      simpa using this
    · have hh : lc.home i = none := by
        simp only [LocCtx.home]
        rw [getElem?_neg lc.homes i hi]
        rfl
      unfold homeOK4 homeOK3 homeOK2 homeOK
      rw [hh]

end GoFV.Gen.Check
