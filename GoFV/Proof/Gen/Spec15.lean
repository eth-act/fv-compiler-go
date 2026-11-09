import GoFV.Gen.Check15
import GoFV.Proof.Gen.Spec14

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G15 accepted (`docs/plans/proofs3.md` §4)

`checkG15 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G15.lean`) uses (`checkG15_spec`): G14's (`Spec14.lean`) with G15's value check
(`vkind15_spec`, `VK15`: G14's values but static calls, and G9's static calls on the ABI without
its zero-sized stack inputs, `callRegsZ`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind15` accepted of a value that is not an entry value, and what it emits. -/
inductive VK15 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G14 other than a static call. -/
  | g14 {kd : VKind2} : v.op ≠ .ARM64CALLstatic → VK14 lc g v kd → VK15 lc g v kd
  /-- A static call as `VK9.call`, its ABI without its zero-sized stack inputs (`callRegsZ`). -/
  | call {name : GoStr} {abi : Nat} {cabi : CallABI} {ins outs : List Nat} {mem : ID} :
      v.op = .ARM64CALLstatic → callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
      callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) → outs.Nodup → v.args.back? = some mem →
      memTy (lc.ty mem) = true → lc.home mem = none → (∀ r ∈ ins ++ outs, r < 16) →
      v.args.toList.dropLast.length = ins.length →
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r)) →
      (lc.home v.id = some (.results (outs.map some).toArray) ∨ (lc.home v.id = none ∧ outs = [])) →
      callTy outs.length (lc.ty v.id) = true → VK15 lc g v (.prog (callPat g name abi))

/-- What `callKind15` accepted: `VK15.call`. -/
theorem callKind15_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64CALLstatic) (h : callKind15 lc g v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK15 lc g v kd := by
  unfold callKind15 at h
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
        all_goals exact VK15.call hop hcall hcr hnd hm hmem.1 hmem.2 h16 hlen hargs' hres hct
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  · simp [ht, ex_throw, ex_bind_error] at h

/-- What `vkind15` accepted of a value that is not an entry value: no temporary, and `VK15`. -/
theorem vkind15_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind15 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK15 lc g v kd := by
  unfold vkind15 at h
  by_cases hop : v.op = .ARM64CALLstatic
  · simp only [hop, beq_self_eq_true, ↓reduceIte] at h
    exact callKind15_spec hop h
  · simp only [beq_iff_eq, hop, ↓reduceIte] at h
    obtain ⟨ht, h14⟩ := vkind14_spec h hen
    exact ⟨ht, .g14 hop h14⟩

/-- What `checkG15` accepted: G14's facts with G15's value check. -/
theorem checkG15_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG15 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind15 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG15 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
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
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb⟩
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
