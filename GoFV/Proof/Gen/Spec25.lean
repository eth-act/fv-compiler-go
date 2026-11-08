import GoFV.Gen.Check25
import GoFV.Proof.Gen.Spec24

/-!
# What the genssa validator's slice G25 accepted (`docs/plans/proofs3.md` §4)

`checkG25 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G25.lean`) uses (`checkG25_spec`): G24's (`Spec24.lean`) with G25's value check
(`vkind25_spec`, `VK25`: G24's values, `CSEL`/`CSEL0` as `CSEL`, `TSTconst`/`TSTWconst` as
`TST`/`TSTW`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind25` accepted of a value that is not an entry value, and what it emits. -/
inductive VK25 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G24 (no select or bit test). -/
  | g24 {kd : VKind2} : (v.op == .ARM64CSEL || v.op == .ARM64CSEL0) = false →
      (v.op == .ARM64TSTconst || v.op == .ARM64TSTWconst) = false → VK24 lc g v kd →
      VK25 lc g v kd
  /-- `CSEL [cc] x y f`: `CSEL cond, Rx, Ry, Rd`. -/
  | csel {f : ID} {o : Op} {cc rn rm rd : Int} {ca cb c : Nat} :
      v.op = .ARM64CSEL → v.args.size = 3 → v.args[2]? = some f → (lc.ty f).isFlags = true →
      lc.home f = none → ccOp? v.auxInt = some o → (Cond.ofOp o).isSome = true →
      ARM64.condBits o = some cc → argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → c ≤ ca → c ≤ cb →
      VK25 lc g v (.prog ⟨cselOK cc rn rm rd, "CSEL"⟩)
  /-- `CSEL0 [cc] x f`: `CSEL cond, Rx, ZR, Rd`. -/
  | csel0 {f : ID} {o : Op} {cc rn rd : Int} {ca c : Nat} :
      v.op = .ARM64CSEL0 → v.args.size = 2 → v.args[1]? = some f → (lc.ty f).isFlags = true →
      lc.home f = none → ccOp? v.auxInt = some o → (Cond.ofOp o).isSome = true →
      ARM64.condBits o = some cc → argObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) →
      8 ≤ c → c ≤ ca → VK25 lc g v (.prog ⟨cselOK cc rn (ARM64.REG_R0 + 31) rd, "CSEL"⟩)
  /-- `TSTconst [k] x`: `TST $k, Rn`, the bits it reads of `x` known (`tstOK`). -/
  | tst {rn : Int} {ca : Nat} : v.op = .ARM64TSTconst → v.args.size = 1 →
      (lc.ty v.id).isFlags = true → lc.home v.id = none → argObj lc v 0 = .ok (ca, rn) →
      tstOK 64 ca v.auxInt.toInt = true →
      VK25 lc g v (.prog (.ofShape { as := .TST, from_ := constA v.auxInt.toInt, reg := rn }))
  /-- `TSTWconst [k] x`: `TSTW $k, Rn`, the bits it reads of `x` known (`tstOK`). -/
  | tstw {rn : Int} {ca : Nat} : v.op = .ARM64TSTWconst → v.args.size = 1 →
      (lc.ty v.id).isFlags = true → lc.home v.id = none → argObj lc v 0 = .ok (ca, rn) →
      tstOK 32 ca v.auxInt.toInt = true →
      VK25 lc g v (.prog (.ofShape { as := .TSTW, from_ := constA v.auxInt.toInt, reg := rn }))

/-- What `cselKind` accepted: no temporary, and `VK25`'s `csel` or `csel0`. -/
theorem cselKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64CSEL ∨ v.op = .ARM64CSEL0) (h : cselKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK25 lc g v kd := by
  unfold cselKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  rcases hop with hop | hop
  · have hc0 : (v.op == .ARM64CSEL0) = false := by rw [hop]; decide
    simp only [hc0, Bool.false_eq_true, ↓reduceIte] at h
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
          exact VK25.csel hop hsz hf hfl.1 hfl.2 ho hco hcc hao hbo hro hw.1.1 hw.1.2 hw.2
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  · have hc0 : (v.op == .ARM64CSEL0) = true := by rw [hop]; decide
    simp only [hc0, ↓reduceIte] at h
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
          simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at hbo
          obtain ⟨rfl, rfl⟩ := hbo
          obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
          obtain ⟨hw, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
          simp only [ex_pure, Except.ok.injEq] at h
          subst h
          exact VK25.csel0 hop hsz hf hfl.1 hfl.2 ho hco hcc hao hro hw.1.1 hw.1.2
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h

/-- What `tstKind` accepted: no temporary, and `VK25`'s `tst` or `tstw`. -/
theorem tstKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64TSTconst ∨ v.op = .ARM64TSTWconst) (h : tstKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK25 lc g v kd := by
  unfold tstKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  obtain ⟨hsh, h⟩ := ex_guard h
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  rcases hop with hop | hop
  · have ht0 : (v.op == .ARM64TSTconst) = true := by rw [hop]; decide
    simp only [ht0, ↓reduceIte] at hw ⊢
    exact VK25.tst hop hsh.1.1 hsh.1.2 hsh.2 hao hw
  · have ht0 : (v.op == .ARM64TSTconst) = false := by rw [hop]; decide
    simp only [ht0, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact VK25.tstw hop hsh.1.1 hsh.1.2 hsh.2 hao hw

/-- What `vkind25` accepted of a value that is not an entry value: no temporary, and `VK25`. -/
theorem vkind25_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind25 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK25 lc g v kd := by
  unfold vkind25 at h
  cases hc : (v.op == .ARM64CSEL || v.op == .ARM64CSEL0) with
  | true =>
    simp only [hc, ↓reduceIte] at h
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    exact cselKind_spec hc h
  | false =>
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    cases ht : (v.op == .ARM64TSTconst || v.op == .ARM64TSTWconst) with
    | true =>
      simp only [ht, ↓reduceIte] at h
      simp only [Bool.or_eq_true, beq_iff_eq] at ht
      exact tstKind_spec ht h
    | false =>
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨htm, h24⟩ := vkind24_spec h hen
      exact ⟨htm, .g24 hc ht h24⟩

/-- What `checkG25` accepted: G24's facts with G25's value check. -/
theorem checkG25_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG25 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind25 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK lc = true := by
  unfold checkG25 at h
  obtain ⟨hl, h⟩ := ex_guard h
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
