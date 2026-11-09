import GoFV.Gen.Check41
import GoFV.Proof.Gen.Spec40

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG41` accepted (`GoFV/Gen/Check41.lean`)

`VK41`: G38's kinds (`VK38`, through `vkind40`) and the compares `CMNconst`, `CMPshiftLL`,
`CMPshiftRL` (`vkind41_spec`); on `InitMem`, `vkind41` is `vkind40` (`vkind41_initMem`).
`checkG41L_spec` is `checkG40L_spec` with `vkind41`, and `checkG41_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind41` accepted of a value that is not an entry value, and what it emits. -/
inductive VK41 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G38. -/
  | g38 {kd : VKind2} : v.op ≠ .ARM64CMNconst → cmpSh41? v.op = none → VK38 lc g v kd →
      VK41 lc g v kd
  /-- `CMNconst [k] x`: `CMN $k, Rn`, `x` of 64 bits. -/
  | cmn {rn : Int} : v.op = .ARM64CMNconst → v.args.size = 1 → (lc.ty v.id).isFlags = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rn) →
      VK41 lc g v (.prog (.ofShape { as := .CMN, from_ := constA v.auxInt.toInt, reg := rn }))
  /-- `CMPshiftLL`, `CMPshiftRL [k] x y`: `CMP Rm SHIFT k, Rn`, `x` and `y` of 64 bits. -/
  | cmpSh {typ : Nat} {rn rm : Int} : cmpSh41? v.op = some typ → v.args.size = 2 →
      (lc.ty v.id).isFlags = true → lc.home v.id = none → 0 ≤ v.auxInt.toInt →
      v.auxInt.toInt < 64 → argObj lc v 0 = .ok (64, rn) → argObj lc v 1 = .ok (64, rm) →
      VK41 lc g v (.prog (.ofShape
        { as := .CMP, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn }))

theorem cmpSh41?_some {op : Op} {typ : Nat} (h : cmpSh41? op = some typ) :
    op = .ARM64CMPshiftLL ∧ typ = 0 ∨ op = .ARM64CMPshiftRL ∧ typ = 1 := by
  unfold cmpSh41? at h
  split at h <;> cases h
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-- What `cmnKind` accepted: no temporary, and `VK41`'s `cmn`. -/
theorem cmnKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64CMNconst) (h : cmnKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK41 lc g v kd := by
  unfold cmnKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsh, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨hca, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hca
  subst hca
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  exact ⟨ht, .cmn hop hsh.1.1 hsh.1.2 hsh.2 hao⟩

/-- What `cmpShKind` accepted: no temporary, and `VK41`'s `cmpSh`. -/
theorem cmpShKind_spec {lc : LocCtx} {g : G2In} {v : Value} {typ : Nat} {kd : VKind2}
    (hop : cmpSh41? v.op = some typ) (h : cmpShKind lc v typ = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK41 lc g v kd := by
  unfold cmpShKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsh, h⟩ := ex_guard h
  obtain ⟨hk, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨hcab, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hcab hsh
  obtain ⟨rfl, rfl⟩ := hcab
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  exact ⟨ht, .cmpSh hop hsh.1.1 hsh.1.2 hsh.2 hk.1 hk.2 hao hbo⟩

/-- What `vkind41` accepted of a value that is not an entry value: no temporary, and `VK41`. -/
theorem vkind41_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind41 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK41 lc g v kd := by
  unfold vkind41 at h
  by_cases hc : v.op = .ARM64CMNconst
  · simp only [hc, beq_self_eq_true, ↓reduceIte] at h
    exact cmnKind_spec hc h
  · have hc' : (v.op == .ARM64CMNconst) = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
    cases hs : cmpSh41? v.op with
    | some typ =>
      rw [hs] at h
      exact cmpShKind_spec hs h
    | none =>
      rw [hs] at h
      obtain ⟨ht, h38⟩ := vkind40_spec h hen
      exact ⟨ht, .g38 hc hs h38⟩

/-- On `InitMem`, `vkind41` is `vkind40`. -/
theorem vkind41_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind41 lc g v = vkind40 lc g v := by
  simp [vkind41, cmpSh41?, hop]

/-- On a function with no arm64 op, G41's check is G33. -/
theorem checkG33_of_41L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG41L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG41L, hl] using h

/-- What `checkG41L` accepted of a function with an arm64 op: G38's facts with G41's value
check. -/
theorem checkG41L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG41L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind41 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG41L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
  simp only [Bool.and_eq_true] at hmovd
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
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd.1, hmovd.2⟩
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

/-- What `checkG41` accepted: `refsLive`, and G41's check on the context without the removed
homes. -/
theorem checkG41_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG41 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG41L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG41 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
