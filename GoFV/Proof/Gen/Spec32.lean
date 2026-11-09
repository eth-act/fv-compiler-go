import GoFV.Gen.Check32
import GoFV.Proof.Gen.Spec30

/-!
# What the genssa validator's slice G32 accepted (`docs/plans/proofs3.md` §4)

`checkG32 lc ps bstart g = .ok (tab, kt)` unfolded: on a function with an arm64 op, G29's facts
(`checkG32_spec`) with G32's value check (`vkind32_spec`, `VK32`: G28's values, the register,
constant and unary ops, `CSINC` and the store-release ops); on one without, G30's
(`checkG30_of_32`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind32` accepted of a value that is not an entry value, and what it emits. -/
inductive VK32 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G28 (none of G32's ops). -/
  | g28 {kd : VKind2} : bin32? v.op = none → binK32? v.op = none → un32? v.op = none →
      stlr? v.op = none → v.op ≠ .ARM64CSINC → VK28 lc g v kd → VK32 lc g v kd
  /-- `op x y`: `op Rm, Rn, Rd`. -/
  | bin {as : As} {ca cb c : Nat} {rn rm rd : Int} :
      bin32? v.op = some as → v.args.size = 2 → argObj lc v 0 = .ok (ca, rn) →
      argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) →
      (8 ≤ c ∧ c ≤ ca ∧ c ≤ cb ∨ c = 1 ∧ ca = 1 ∧ cb = 1 ∧ boolBin as = true) →
      VK32 lc g v (.prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }))
  /-- `op [k] x`: `op $k, Rn, Rd`. -/
  | binK {as : As} {ca c : Nat} {rn rd : Int} :
      binK32? v.op = some as → v.args.size = 1 → argObj lc v 0 = .ok (ca, rn) →
      resObj lc v = .ok (c, rd) →
      (8 ≤ c ∧ c ≤ ca ∨ c = 1 ∧ ca = 1 ∧ as = .EOR ∧ v.auxInt.toInt = 1) →
      VK32 lc g v (.prog (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }))
  /-- `op x`: `op Rm, Rd`. -/
  | un {as : As} {ca c : Nat} {rm rd : Int} :
      un32? v.op = some as → v.args.size = 1 → argObj lc v 0 = .ok (ca, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → c ≤ ca →
      VK32 lc g v (.prog (.ofShape { as, from_ := regA rm, to := regA rd }))
  /-- `CSINC [cc] x y f`: `CSINC cond, Rx, Ry, Rd`. -/
  | csinc {f : ID} {o : Op} {cc rn rm rd : Int} {ca cb c : Nat} :
      v.op = .ARM64CSINC → v.args.size = 3 → v.args[2]? = some f → (lc.ty f).isFlags = true →
      lc.home f = none → ccOp? v.auxInt = some o → (Cond.ofOp o).isSome = true →
      ARM64.condBits o = some cc → argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → c ≤ ca → c ≤ cb →
      VK32 lc g v (.prog ⟨csincOK cc rn rm rd, "CSINC"⟩)
  /-- `op p x mem`: `op Rx, (Rp)`, `x` of the access's width. -/
  | stlr {as : As} {n ca cs : Nat} {rn rs : Int} :
      stlr? v.op = some (as, n) → v.args.size = 3 → memTy (lc.ty v.id) = true →
      lc.home v.id = none → v.aux = none → v.auxInt.toInt = 0 → argObj lc v 0 = .ok (ca, rn) →
      argObj lc v 1 = .ok (cs, rs) → memArg lc v 2 = .ok () → ca = 64 → cs = 8 * n →
      VK32 lc g v (.prog ⟨plain as (· == regA rs) (· == memA rn 0), as.name⟩)

/-- What `bin32Kind` accepted: no temporary, and `VK32`'s `bin`. -/
theorem bin32Kind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {kd : VKind2}
    (hop : bin32? v.op = some as) (h : bin32Kind lc v as = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK32 lc g v kd := by
  unfold bin32Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  refine ⟨ht, .bin hop hsz hao hbo hro ?_⟩
  rcases hw with ⟨⟨h8, hca⟩, hcb⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · exact .inl ⟨h8, hca, hcb⟩
  · exact .inr ⟨h1, h2, h3, h4⟩

/-- What `binK32Kind` accepted: no temporary, and `VK32`'s `binK`. -/
theorem binK32Kind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {kd : VKind2}
    (hop : binK32? v.op = some as) (h : binK32Kind lc v as = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK32 lc g v kd := by
  unfold binK32Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  refine ⟨ht, .binK hop hsz hao hro ?_⟩
  rcases hw with ⟨h8, hca⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · exact .inl ⟨h8, hca⟩
  · exact .inr ⟨h1, h2, h3, h4⟩

/-- What `un32Kind` accepted: no temporary, and `VK32`'s `un`. -/
theorem un32Kind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {kd : VKind2}
    (hop : un32? v.op = some as) (h : un32Kind lc v as = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK32 lc g v kd := by
  unfold un32Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rm⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨ht, .un hop hsz hao hro hw.1 hw.2⟩

/-- What `csincKind` accepted: no temporary, and `VK32`'s `csinc`. -/
theorem csincKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64CSINC) (h : csincKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK32 lc g v kd := by
  unfold csincKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  obtain ⟨hsz, h⟩ := ex_guard h
  simp only [beq_iff_eq] at hsz
  split at h
  next f hf =>
    obtain ⟨hfl, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hfl
    split at h
    next o ho =>
      obtain ⟨hco, h⟩ := ex_guard h
      split at h
      next cc hcc =>
        obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
        obtain ⟨hw, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
        simp only [ex_pure, Except.ok.injEq] at h
        subst h
        exact VK32.csinc hop hsz hf hfl.1 hfl.2 ho hco hcc hao hbo hro hw.1.1 hw.1.2 hw.2
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next => simp [ex_throw] at h

/-- What `stlrKind` accepted: no temporary, and `VK32`'s `stlr`. -/
theorem stlrKind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {n : Nat} {kd : VKind2}
    (hop : stlr? v.op = some (as, n)) (h : stlrKind lc v as n = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK32 lc g v kd := by
  unfold stlrKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsh, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cs, rs⟩, hso, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh hw
  obtain ⟨⟨⟨⟨hsz, hmt⟩, hhn⟩, haux⟩, hk⟩ := hsh
  exact ⟨ht, .stlr hop hsz hmt hhn haux hk hao hso hma hw.1 hw.2⟩

/-- What `vkind32` accepted of a value that is not an entry value: no temporary, and `VK32`. -/
theorem vkind32_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind32 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK32 lc g v kd := by
  unfold vkind32 at h
  cases h1 : bin32? v.op with
  | some as => rw [h1] at h; exact bin32Kind_spec h1 h
  | none =>
  cases h2 : binK32? v.op with
  | some as => rw [h1, h2] at h; exact binK32Kind_spec h2 h
  | none =>
  cases h3 : un32? v.op with
  | some as => rw [h1, h2, h3] at h; exact un32Kind_spec h3 h
  | none =>
  cases h4 : stlr? v.op with
  | some p =>
    obtain ⟨as, n⟩ := p
    rw [h1, h2, h3, h4] at h
    exact stlrKind_spec h4 h
  | none =>
    rw [h1, h2, h3, h4] at h
    by_cases hc : v.op = .ARM64CSINC
    · simp only [hc, beq_self_eq_true, ↓reduceIte] at h
      exact csincKind_spec hc h
    · have hc' : (v.op == .ARM64CSINC) = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨htm, h28⟩ := vkind28_spec h hen
      exact ⟨htm, .g28 h1 h2 h3 h4 hc h28⟩

/-- On a function with no arm64 op, G32 is G30. -/
theorem checkG30_of_32 {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG32 lc ps bstart g = r) : checkG30 lc ps bstart g = r := by
  simpa [checkG30, checkG32, hl] using h

/-- What `checkG32` accepted of a function with an arm64 op: G29's facts with G32's value check. -/
theorem checkG32_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG32 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind32 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK29 lc = true := by
  simp only [checkG32, hl, ↓reduceIte] at h
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

end GoFV.Gen.Check
