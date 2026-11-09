import GoFV.Gen.Check45
import GoFV.Proof.Gen.Spec44

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG45` accepted (`GoFV/Gen/Check45.lean`)

`VK45`: G44's kinds (`VK44`, through `vkind44`) and G45's float register-index loads and stores
(`fkind45_spec`); on `InitMem`, `vkind45` is `vkind44` (`vkind45_initMem`). `checkG45L_spec` is
`checkG44L_spec` with `vkind45`, and `checkG45_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind45` accepted of a value that is not an entry value, and what it emits. -/
inductive VK45 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G44. -/
  | g44 {kd : VKind2} : VK44 lc g v kd → VK45 lc g v kd
  /-- `FMOV{S,D}loadidx{,4,8}` of `n` bytes at `ptr + idx · 2^sh`: `FMOVS`/`FMOVD (Rp)(Ri<<sh), Fd`. -/
  | fldIdx {n sh c : Nat} {rn ri rd : Int} : fLoadIdxOp? v.op = some (n, sh) → v.args.size = 3 →
      argObj lc v 0 = .ok (64, rn) → argObj lc v 1 = .ok (64, ri) → memArg lc v 2 = .ok () →
      fresObj lc v = .ok (c, rd) → c = 8 * n →
      VK45 lc g v (.prog ⟨plain (fmovAs c) (· == idxA rn ri sh) (· == regA rd), (fmovAs c).name⟩)
  /-- `FMOV{S,D}storeidx{,4,8}` of a float of `n` bytes at `ptr + idx · 2^sh`:
  `FMOVS`/`FMOVD Fs, (Rp)(Ri<<sh)`. -/
  | fstIdx {n sh cs : Nat} {rn ri rs : Int} : fStoreIdxOp? v.op = some (n, sh) → v.args.size = 4 →
      memTy (lc.ty v.id) = true → lc.home v.id = none → argObj lc v 0 = .ok (64, rn) →
      argObj lc v 1 = .ok (64, ri) → fargObj lc v 2 = .ok (cs, rs) → cs = 8 * n →
      memArg lc v 3 = .ok () →
      VK45 lc g v (.prog ⟨plain (fmovAs cs) (· == regA rs) (· == idxA rn ri sh), (fmovAs cs).name⟩)

/-- What `fkind45` accepted: no temporary, and one of `VK45`'s float register-index accesses. -/
theorem fkind45_spec {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (h : fkind45 lc v e = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK45 lc g v kd := by
  unfold fkind45 at h
  split at h
  next =>
    obtain ⟨ht, h⟩ := ex_guard h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨ci, ri⟩, hio, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
    obtain ⟨hc, h⟩ := ex_guard h
    cases h
    simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw hc
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨ht, .fldIdx (by assumption) hsz hao hio hma hro hc⟩
  next =>
    obtain ⟨ht, h⟩ := ex_guard h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨ci, ri⟩, hio, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    obtain ⟨⟨cs, rs⟩, hso, h⟩ := ex_bind_eq_ok h
    obtain ⟨hc, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
    cases h
    simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw hc
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨ht, .fstIdx (by assumption) hsz.1.1 hsz.1.2 hsz.2 hao hio hso hc hma⟩
  next => cases h

/-- What `vkind45` accepted of a value that is not an entry value: no temporary, and `VK45`. -/
theorem vkind45_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind45 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK45 lc g v kd := by
  unfold vkind45 at h
  cases h44 : vkind44 lc g v with
  | ok kd' =>
    rw [h44] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind44_spec h44 hen
    exact ⟨ht, .g44 hVK⟩
  | error e =>
    rw [h44] at h
    exact fkind45_spec h

/-- On `InitMem`, `vkind45` is `vkind44`. -/
theorem vkind45_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind45 lc g v = vkind44 lc g v := by
  unfold vkind45
  cases vkind44 lc g v with
  | ok _ => rfl
  | error e => simp [fkind45, hop, fLoadIdxOp?, fStoreIdxOp?, ex_throw]

/-- On a function with no arm64 op, G45's check is G33. -/
theorem checkG33_of_45L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG45L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG45L, hl] using h

/-- What `checkG45L` accepted of a function with an arm64 op: G44's facts with G45's value
check. -/
theorem checkG45L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG45L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind45 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG45L, hl, ↓reduceIte] at h
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

/-- What `checkG45` accepted: `refsLive`, and G45's check on the context without the removed
homes. -/
theorem checkG45_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG45 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG45L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG45 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
