import GoFV.Gen.Check9
import GoFV.Proof.Gen.Spec8

/-!
# What the genssa validator's slice G9 accepted (`docs/plans/proofs3.md` §4)

`checkG9 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G9.lean`) uses (`checkG9_spec`): G8's (`Spec8.lean`) with G9's value check
(`vkind9_spec`, `VK9`: G8's values but the static calls, and the static calls with distinct
result registers at register shapes).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind9` accepted of a value that is not an entry value, and what it emits. -/
inductive VK9 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G8 other than a static call. -/
  | g8 {kd : VKind2} : v.op ≠ .ARM64CALLstatic → VK8 lc g v kd → VK9 lc g v kd
  /-- A static call: register arguments in their ABI registers, results in distinct ABI result
  registers (`results` home, or no home and no result) at register shapes, then the memory;
  `CALL sym(SB)`. -/
  | call {name : GoStr} {abi : Nat} {cabi : CallABI} {ins outs : List Nat} {mem : ID} :
      v.op = .ARM64CALLstatic → callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
      callRegs cabi = .ok (ins, outs) → outs.Nodup → v.args.back? = some mem →
      memTy (lc.ty mem) = true → lc.home mem = none → (∀ r ∈ ins ++ outs, r < 16) →
      v.args.toList.dropLast.length = ins.length →
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r)) →
      (lc.home v.id = some (.results (outs.map some).toArray) ∨ (lc.home v.id = none ∧ outs = [])) →
      callTy outs.length (lc.ty v.id) = true → VK9 lc g v (.prog (callPat g name abi))

/-- The fields of a Prog `callPat` accepts: `CALL name(SB)`. -/
theorem callPat_spec {g : G2In} {name : GoStr} {abi : Nat} {p : Prog}
    (h : (callPat g name abi).ok p = true) :
    p.as = .CALL ∧ p.from_ = {} ∧ p.reg = 0 ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧
      p.regTo2 = 0 ∧ p.to.type = .MEM ∧ p.to.name = .EXTERN ∧ p.to.offset = 0 ∧
      ∃ y, p.to.sym = some y ∧ g.syms[y]? = some (name, abi) := by
  obtain ⟨has, hf, hr, ht, hsc, hrest, hr2⟩ := plain_spec h
  simp only [beq_iff_eq] at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨⟨ht1, ht2⟩, -⟩, -⟩, ht5⟩, ht6⟩ := ht
  refine ⟨has, hf, hr, hsc, hrest, hr2, ht1, ht2, ht5, ?_⟩
  split at ht6
  · rename_i y hy
    exact ⟨y, hy, by simpa using ht6⟩
  · cases ht6

/-- What `vkind9` accepted of a value that is not an entry value: no temporary, and `VK9`. -/
theorem vkind9_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : vkind9 lc g v = .ok kd)
    (hen : entryOp3 v.op = false) : (lc.temps[v.id]?).join = none ∧ VK9 lc g v kd := by
  unfold vkind9 at h
  by_cases hop : v.op = .ARM64CALLstatic
  · simp only [hop, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    by_cases ht : (lc.temps[v.id]?).join = none
    · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      refine ⟨ht, ?_⟩
      split at h
      next name abi cabi hcall =>
        obtain ⟨⟨ins, outs⟩, hcr, h⟩ := ex_bind_eq_ok h
        obtain ⟨hnd, h⟩ := ex_guard h
        simp only [decide_eq_true_eq] at hnd
        split at h
        next m hm =>
          obtain ⟨hmem, h⟩ := ex_guard h
          obtain ⟨h16, h⟩ := ex_guard h
          obtain ⟨hlen, h⟩ := ex_guard h
          obtain ⟨hargs, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq] at hmem hlen
          simp only [List.all_eq_true, decide_eq_true_eq] at h16
          have hargs' : ∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins →
              lc.home a = some (.reg r) := by
            intro a r har
            have := (List.all_eq_true.mp hargs) (a, r) har
            simpa only [beq_iff_eq, regHome?_eq] using this
          have hres : lc.home v.id = some (.results (outs.map some).toArray) ∨
              (lc.home v.id = none ∧ outs = []) := by
            split at h
            next rs hrs =>
              obtain ⟨hc, -⟩ := ex_guard h
              simp only [beq_iff_eq] at hc
              left
              rw [hrs, ← hc]
            next hn =>
              obtain ⟨hc, -⟩ := ex_guard h
              exact Or.inr ⟨hn, List.isEmpty_iff.mp hc⟩
            next => simp [ex_throw, ex_bind_error] at h
          split at h
          all_goals first
            | (simp [ex_throw, ex_bind_error] at h; done)
            | (obtain ⟨-, h⟩ := ex_guard h
               obtain ⟨hct, h⟩ := ex_guard h
               cases h)
          all_goals exact VK9.call hop hcall hcr hnd hm hmem.1 hmem.2 h16 hlen hargs' hres hct
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    · simp [ht, ex_throw, ex_bind_error] at h
  · simp only [bne_iff_ne, ne_eq, hop, not_false_eq_true, ↓reduceIte] at h
    obtain ⟨ht, h8⟩ := vkind8_spec h hen
    exact ⟨ht, VK9.g8 hop h8⟩

/-- What `checkG9` accepted: G8's facts with G9's value check. -/
theorem checkG9_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG9 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind9 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK4 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG9 at h
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
