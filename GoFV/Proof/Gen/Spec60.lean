import GoFV.Gen.Check60
import GoFV.Proof.Gen.Spec59
import GoFV.Proof.Gen.Spec56

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG60` accepted (`GoFV/Gen/Check60.lean`)

`VK60`: a float constant (`FMOVSconst`/`FMOVDconst`, no temporary, homed in an `F` register of its
class) with G56's `fconstPat56`, or G59's kinds (`VK59`) of every other value. On `InitMem`,
`vkind60` is `vkind59` (`vkind60_initMem`). On an op of none of G56's, G58's and G59's groups
`vkind60` is `vkind48` (`vkind60_eq48`); what `vkind48` accepts is `vkind57`'s or G48's (`kind48`:
a static call on `callRegsS`, or an access off `SP`, `kind48_cases`); so on an op of none of
G52–G59's groups what `vkind60` accepts `vkind49` or `kind48` accepts (`vkind60_ok49`).
`checkG60L_spec` is `checkG59L_spec` with `vkind60`, and `checkG60_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind60` accepted of a value that is not an entry value. -/
inductive VK60 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G59 that is no float constant. -/
  | g59 {kd : VKind2} : v.op ≠ .ARM64FMOVSconst → v.op ≠ .ARM64FMOVDconst → VK59 lc g v kd →
      VK60 lc g v kd
  /-- A float constant: `FMOVS`/`FMOVD $c, Fd`, or the load of its constant symbol. -/
  | fconst {c : Nat} {rd : Int} : (v.op = .ARM64FMOVSconst ∨ v.op = .ARM64FMOVDconst) →
      (lc.temps[v.id]?).join = none → v.args.size = 0 → fresObj lc v = .ok (c, rd) →
      c = 8 * fBytes v.op → VK60 lc g v (.prog (fconstPat56 g v c rd))

/-- What `vkind60` accepted of a value that is not an entry value. -/
theorem vkind60_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind60 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK60 lc g v kd := by
  unfold vkind60 at h
  by_cases hop : v.op = .ARM64FMOVSconst ∨ v.op = .ARM64FMOVDconst
  · have hb : (v.op == .ARM64FMOVSconst || v.op == .ARM64FMOVDconst) = true := by
      rcases hop with h' | h' <;> simp [h']
    unfold vkind56a at h
    simp only [hb, ↓reduceIte] at h
    obtain ⟨ht, h⟩ := ex_guard h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
    obtain ⟨hc, h⟩ := ex_guard h
    cases h
    simp only [beq_iff_eq] at ht hsz hc
    exact .fconst hop ht hsz hro hc
  · have h1 : v.op ≠ .ARM64FMOVSconst := fun h' => hop (.inl h')
    have h2 : v.op ≠ .ARM64FMOVDconst := fun h' => hop (.inr h')
    rw [vkind56a_none h1 h2] at h
    exact .g59 h1 h2 (vkind59_spec h hen)

/-- On `InitMem`, `vkind60` is `vkind59`. -/
theorem vkind60_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind60 lc g v = vkind59 lc g v := by
  unfold vkind60
  rw [vkind56a_none (by rw [hop]; nofun) (by rw [hop]; nofun)]

/-- On an op of none of G57's groups, `vkind57` is `vkind55`. -/
theorem vkind57_eq55 {lc : LocCtx} {g : G2In} {v : Value} (h7a : op57a v.op = false)
    (h7b : op57b v.op = false) : vkind57 lc g v = vkind55 lc g v := by
  unfold vkind57
  rw [vkind57a_none h7a, vkind57b_none h7b]
  cases vkind55 lc g v <;> rfl

/-- On an op of none of G56's, G58's and G59's groups, `vkind60` is `vkind48`. -/
theorem vkind60_eq48 {lc : LocCtx} {g : G2In} {v : Value} (h6 : op56 v.op = false)
    (h8 : op58a v.op = false) (h9 : op59p v.op = false) : vkind60 lc g v = vkind48 lc g v := by
  have h1 : v.op ≠ .ARM64FMOVSconst := fun h' => by simp [op56, h'] at h6
  have h2 : v.op ≠ .ARM64FMOVDconst := fun h' => by simp [op56, h'] at h6
  unfold vkind60 vkind59 vkind58
  rw [vkind56a_none h1 h2, vkind59p_none h9, vkind58a_none h8]
  cases vkind48 lc g v <;> rfl

/-- What `vkind48` accepted, `vkind57` or G48's `kind48` accepted. -/
theorem vkind48_ok {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind48 lc g v = .ok kd) : vkind57 lc g v = .ok kd ∨ ∃ e, kind48 lc g v e = .ok kd := by
  unfold vkind48 at h
  cases h57 : vkind57 lc g v with
  | ok kd' => rw [h57] at h; exact .inl h
  | error e => rw [h57] at h; exact .inr ⟨e, h⟩

/-- What G48's `kind48` accepted: a static call (`callKind48`, on `callRegsS`), or an access off
`SP` without an aux whose base is homed in the Go register `SP` (`spKind48`). -/
theorem kind48_cases {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (h : kind48 lc g v e = .ok kd) :
    (v.op = .ARM64CALLstatic ∧ callKind48 lc g v = .ok kd) ∨
      (v.op ≠ .ARM64CALLstatic ∧ v.aux = none ∧ spArg lc v = true ∧ spBase48 lc v = true ∧
        spKind48 lc v = .ok kd) := by
  unfold kind48 at h
  split at h
  next hop => exact .inl ⟨hop, h⟩
  next hop =>
    split at h
    next hsp =>
      split at h
      next => cases h
      next =>
        split at h
        next => cases h
        next hb =>
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hb
          exact .inr ⟨hop, hsp.1, hsp.2, hb, h⟩
    next => cases h

/-- On an op of none of G52's–G59's groups, what `vkind60` accepted `vkind49` or G48's `kind48`
accepted. -/
theorem vkind60_ok49 {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h7a : op57a v.op = false) (h7b : op57b v.op = false) (h8 : op58a v.op = false)
    (h9 : op59p v.op = false) (h6 : op56 v.op = false) (h5a : op55a v.op = false)
    (h5b : op55b v.op = false) (h2 : op52b v.op = false) (h3 : op53a v.op = false)
    (h4 : op54a v.op = false) (h : vkind60 lc g v = .ok kd) :
    vkind49 lc g v = .ok kd ∨ ∃ e, kind48 lc g v e = .ok kd := by
  rw [vkind60_eq48 h6 h8 h9] at h
  rcases vkind48_ok h with h | h
  · rw [vkind57_eq55 h7a h7b, vkind55_eq54 h5a h5b, vkind54_eq49 h2 h3 h4] at h
    exact .inl h
  · exact .inr h

/-- On a function with no arm64 op, G60's check is G33. -/
theorem checkG33_of_60L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG60L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG60L, hl] using h

/-- What `checkG60L` accepted of a function with an arm64 op: G59's facts with G60's value
check. -/
theorem checkG60L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG60L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind60 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true ∧
      spHomes48 lc = true := by
  simp only [checkG60L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hlp, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
  simp only [Bool.and_eq_true] at hmovd
  cases hf : List.find? (fun x => !homeOK10 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨-, h⟩ := ex_guard h
    obtain ⟨hsph, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd.1, hmovd.2, hlp,
      hsph⟩
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

/-- What `checkG60` accepted: `refsLive`, and `checkG60L` on `liveCtx`. -/
theorem checkG60_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG60 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG60L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG60 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
