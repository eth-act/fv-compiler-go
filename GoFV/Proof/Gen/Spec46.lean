import GoFV.Gen.Check46
import GoFV.Proof.Gen.Spec45

/-!
# What `checkG46` accepted (`GoFV/Gen/Check46.lean`)

`VK46`: G45's kinds (`VK45`, through `vkind45`) and G46's float arithmetic, conversions, compares
and fused multiply-adds (`fkind46_spec`); on `InitMem`, `vkind46` is `vkind45`
(`vkind46_initMem`). `checkG46L_spec` is `checkG45L_spec` with `vkind46`, and `checkG46_spec`
splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind46` accepted of a value that is not an entry value, and what it emits. -/
inductive VK46 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G45. -/
  | g45 {kd : VKind2} : VK45 lc g v kd → VK46 lc g v kd
  /-- `FADD`/`FSUB`/`FMUL`/`FDIV`: `op Fm, Fn, Fd`. -/
  | fbin {n : Nat} {ft : BitVec 2} {opc : BitVec 4} {rn rm rd : Int} :
      fp2Of v.op = some (n, ft, opc) → v.args.size = 2 → fargObj lc v 0 = .ok (8 * n, rn) →
      fargObj lc v 1 = .ok (8 * n, rm) → fresObj lc v = .ok (8 * n, rd) →
      VK46 lc g v (.prog (.ofShape { as := opAsm v.op, from_ := regA rm, reg := rn, to := regA rd }))
  /-- `FNEG`/`FABS`/`FSQRT`/`FCVTSD`/`FCVTDS`: `op Fa, Fd`. -/
  | fun1 {ns nd : Nat} {ft : BitVec 2} {opc : BitVec 6} {ra rd : Int} :
      fp1Of v.op = some (ns, nd, ft, opc) → v.args.size = 1 → fargObj lc v 0 = .ok (8 * ns, ra) →
      fresObj lc v = .ok (8 * nd, rd) →
      VK46 lc g v (.prog (.ofShape { as := opAsm v.op, from_ := regA ra, to := regA rd }))
  /-- `SCVTF`/`UCVTF`: `op Rn, Fd`. -/
  | cvtf {u : Bool} {ns nd ca : Nat} {rn rd : Int} :
      cvtfOf v.op = some (u, ns, nd) → v.args.size = 1 → argObj lc v 0 = .ok (ca, rn) →
      8 * ns ≤ ca → fresObj lc v = .ok (8 * nd, rd) →
      VK46 lc g v (.prog (.ofShape { as := opAsm v.op, from_ := regA rn, to := regA rd }))
  /-- `FCVTZS`/`FCVTZU`: `op Fn, Rd`. -/
  | fcvtz {u : Bool} {ns nd : Nat} {rn rd : Int} :
      fcvtzOf v.op = some (u, ns, nd) → v.args.size = 1 → fargObj lc v 0 = .ok (8 * ns, rn) →
      resObj lc v = .ok (8 * nd, rd) →
      VK46 lc g v (.prog (.ofShape { as := opAsm v.op, from_ := regA rn, to := regA rd }))
  /-- `FCMPS`/`FCMPD`: `FCMP Fm, Fn`. -/
  | fcmp {n : Nat} {ft : BitVec 2} {rn rm : Int} :
      fcmpOf v.op = some (n, ft, false) → (lc.ty v.id).isFlags = true → lc.home v.id = none →
      v.args.size = 2 → fargObj lc v 0 = .ok (8 * n, rn) → fargObj lc v 1 = .ok (8 * n, rm) →
      VK46 lc g v (.prog (.ofShape { as := opAsm v.op, from_ := regA rm, reg := rn }))
  /-- `FCMPS0`/`FCMPD0`: `FCMP $(0.0), Fn`. -/
  | fcmp0 {n : Nat} {ft : BitVec 2} {rn : Int} :
      fcmpOf v.op = some (n, ft, true) → (lc.ty v.id).isFlags = true → lc.home v.id = none →
      v.args.size = 1 → fargObj lc v 0 = .ok (8 * n, rn) →
      VK46 lc g v (.prog (.ofShape { as := opAsm v.op, from_ := fzeroA, reg := rn }))
  /-- `FMADD`/`FNMSUB`: `op Fm, Fa, Fn, Fd`. -/
  | fma {n : Nat} {ft : BitVec 2} {o : Bool} {ra rm rn rd : Int} :
      fp3Of v.op = some (n, ft, o, o) → v.args.size = 3 → fargObj lc v 0 = .ok (8 * n, ra) →
      fargObj lc v 1 = .ok (8 * n, rm) → fargObj lc v 2 = .ok (8 * n, rn) →
      fresObj lc v = .ok (8 * n, rd) → VK46 lc g v (.prog (fmaPat v.op ra rm rn rd))

section Helpers

variable {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}

theorem fbin46_spec {n : Nat} {ft : BitVec 2} {opc : BitVec 4} (hop : fp2Of v.op = some (n, ft, opc))
    (h : fbin46 lc v n = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK46 lc g v kd := by
  unfold fbin46 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cd, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hw
  exact ⟨ht, .fbin hop hsz hao hbo hro⟩

theorem fun46_spec {ns nd : Nat} {ft : BitVec 2} {opc : BitVec 6}
    (hop : fp1Of v.op = some (ns, nd, ft, opc)) (h : fun46 lc v ns nd = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK46 lc g v kd := by
  unfold fun46 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, ra⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cd, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨ht, .fun1 hop hsz hao hro⟩

theorem cvtf46_spec {u : Bool} {ns nd : Nat} (hop : cvtfOf v.op = some (u, ns, nd))
    (h : cvtf46 lc v ns nd = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK46 lc g v kd := by
  unfold cvtf46 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cd, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at ht hsz hw
  obtain ⟨hle, rfl⟩ := hw
  exact ⟨ht, .cvtf hop hsz hao hle hro⟩

theorem fcvtz46_spec {u : Bool} {ns nd : Nat} (hop : fcvtzOf v.op = some (u, ns, nd))
    (h : fcvtz46 lc v ns nd = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK46 lc g v kd := by
  unfold fcvtz46 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cd, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨ht, .fcvtz hop hsz hao hro⟩

theorem fcmp46_spec {n : Nat} {ft : BitVec 2} {zero : Bool} (hop : fcmpOf v.op = some (n, ft, zero))
    (h : fcmp46 lc v n zero = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK46 lc g v kd := by
  unfold fcmp46 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hfl, h⟩ := ex_guard h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hfl
  refine ⟨ht, ?_⟩
  cases zero with
  | true =>
    simp only [↓reduceIte] at h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    cases h
    simp only [beq_iff_eq] at hsz hw
    subst hw
    exact .fcmp0 hop hfl.1 hfl.2 hsz hao
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨cb, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    cases h
    simp only [beq_iff_eq, Bool.and_eq_true] at hsz hw
    obtain ⟨rfl, rfl⟩ := hw
    exact .fcmp hop hfl.1 hfl.2 hsz hao hbo

theorem fma46_spec {n : Nat} {ft : BitVec 2} {o : Bool} (hop : fp3Of v.op = some (n, ft, o, o))
    (h : fma46 lc v n = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK46 lc g v kd := by
  unfold fma46 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, ra⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cm, rm⟩, hmo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cn, rn⟩, hno, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cd, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hw
  exact ⟨ht, .fma hop hsz hao hmo hno hro⟩

end Helpers

/-- What `fkind46` accepted: no temporary, and one of `VK46`'s float values. -/
theorem fkind46_spec {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (h : fkind46 lc v e = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK46 lc g v kd := by
  unfold fkind46 at h
  split at h
  · exact fbin46_spec (by assumption) h
  split at h
  · exact fun46_spec (by assumption) h
  split at h
  · exact cvtf46_spec (by assumption) h
  split at h
  · exact fcvtz46_spec (by assumption) h
  split at h
  · exact fcmp46_spec (by assumption) h
  split at h
  · rename_i hop
    split at h
    · rename_i hoo
      subst hoo
      exact fma46_spec hop h
    · cases h
  · cases h

/-- What `vkind46` accepted of a value that is not an entry value: no temporary, and `VK46`. -/
theorem vkind46_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind46 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK46 lc g v kd := by
  unfold vkind46 at h
  cases h45 : vkind45 lc g v with
  | ok kd' =>
    rw [h45] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind45_spec h45 hen
    exact ⟨ht, .g45 hVK⟩
  | error e =>
    rw [h45] at h
    exact fkind46_spec h

/-- On `InitMem`, `vkind46` is `vkind45`. -/
theorem vkind46_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind46 lc g v = vkind45 lc g v := by
  unfold vkind46
  cases vkind45 lc g v with
  | ok _ => rfl
  | error e => simp [fkind46, hop, fp2Of, fp1Of, cvtfOf, fcvtzOf, fcmpOf, fp3Of]

/-- On a function with no arm64 op, G46's check is G33. -/
theorem checkG33_of_46L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG46L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG46L, hl] using h

/-- What `checkG46L` accepted of a function with an arm64 op: G45's facts with G46's value
check. -/
theorem checkG46L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG46L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind46 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG46L, hl, ↓reduceIte] at h
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

/-- What `checkG46` accepted: `refsLive`, and G46's check on the context without the removed
homes. -/
theorem checkG46_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG46 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG46L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG46 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
