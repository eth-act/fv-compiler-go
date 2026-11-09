import GoFV.Gen.Check44
import GoFV.Proof.Gen.Spec43

/-!
# What `checkG44` accepted (`GoFV/Gen/Check44.lean`)

`VK44`: G42's kinds (`VK42`, through `vkind43`) and G44's float moves (`fkind44_spec`); on
`InitMem`, `vkind44` is `vkind43` (`vkind44_initMem`). The operands: `fargObj_spec`,
`fresObj_spec` (a V register `objV? r = some k`, obj register `REG_F0 + k`, a float shape).
`checkG44L_spec` is `checkG43L_spec` with `vkind44`, and `checkG44_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- An obj register of a V register: `REG_F0 + k` with `objV? r = V k`. -/
theorem fobjOf?_some {r : Nat} {o : Int} (h : fobjOf? r = some o) :
    ∃ k : Nat, k < 32 ∧ o = ARM64.REG_F0 + k ∧ objV? r = some (BitVec.ofNat 5 k) := by
  unfold fobjOf? at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨kk, hkk, rfl⟩ := h
  refine ⟨kk.toNat, kk.isLt, rfl, ?_⟩
  rw [hkk, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem fargObj_spec {lc : LocCtx} {v : Value} {i c : Nat} {o : Int}
    (h : fargObj lc v i = .ok (c, o)) :
    ∃ a r, v.args[i]? = some a ∧ lc.home a = some (.reg r) ∧ fobjOf? r = some o ∧
      fTy (lc.ty a) = true ∧ cls (lc.ty a) = some c := by
  unfold fargObj at h
  cases ha : v.args[i]? with
  | none => simp [ha, ex_throw] at h
  | some a =>
    cases hr : regHome? lc a with
    | none => simp [ha, hr, ex_throw] at h
    | some r =>
      cases ho : fobjOf? r with
      | none => simp [ha, hr, ho, ex_throw] at h
      | some o' =>
        cases hf : fTy (lc.ty a) with
        | false => simp [ha, hr, ho, hf, ex_throw, ex_bind_error] at h
        | true =>
          cases hc : cls (lc.ty a) with
          | none => simp [ha, hr, ho, hf, hc, ex_throw] at h
          | some c' =>
            simp only [ha, hr, ho, hf, hc, ex_pure, ↓reduceIte, Except.ok.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨a, r, rfl, regHome?_eq.mp hr, ho, hf, hc⟩

theorem fresObj_spec {lc : LocCtx} {v : Value} {c : Nat} {o : Int} (h : fresObj lc v = .ok (c, o)) :
    ∃ r, lc.home v.id = some (.reg r) ∧ fobjOf? r = some o ∧ fTy (lc.ty v.id) = true ∧
      cls (lc.ty v.id) = some c := by
  unfold fresObj at h
  cases hr : regHome? lc v.id with
  | none => simp [hr, ex_throw] at h
  | some r =>
    cases ho : fobjOf? r with
    | none => simp [hr, ho, ex_throw] at h
    | some o' =>
      cases hf : fTy (lc.ty v.id) with
      | false => simp [hr, ho, hf, ex_throw, ex_bind_error] at h
      | true =>
        cases hc : cls (lc.ty v.id) with
        | none => simp [hr, ho, hf, hc, ex_throw] at h
        | some c' =>
          simp only [hr, ho, hf, hc, ex_pure, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨r, regHome?_eq.mp hr, ho, rfl, rfl⟩

/-- A float shape is `.int .w32` or `.int .w64`, of class 32 or 64. -/
theorem fTy_spec {t : Ty} (h : fTy t = true) :
    (t = .int .w32 ∧ cls t = some 32) ∨ (t = .int .w64 ∧ cls t = some 64) := by
  cases t with
  | int w => cases w <;> simp_all [fTy, cls, Width.bits]
  | _ => simp [fTy] at h

/-- What `vkind44` accepted of a value that is not an entry value, and what it emits. -/
inductive VK44 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G42 (G43's values other than `InitMem`). -/
  | g42 {kd : VKind2} : VK42 lc g v kd → VK44 lc g v kd
  /-- A `Copy` of a float register to itself: no code. -/
  | fcopyNone {c : Nat} {ra : Int} : v.op = .Copy → v.args.size = 1 →
      fargObj lc v 0 = .ok (c, ra) → fresObj lc v = .ok (c, ra) → VK44 lc g v .none
  /-- A `Copy` of a float register to another: `FMOVS`/`FMOVD Fs, Fd`. -/
  | fcopy {c : Nat} {ra rd : Int} : v.op = .Copy → v.args.size = 1 →
      fargObj lc v 0 = .ok (c, ra) → fresObj lc v = .ok (c, rd) →
      VK44 lc g v (.prog (.ofShape { as := fmovAs c, from_ := regA ra, to := regA rd }))
  /-- `FMOVSload`/`FMOVDload` of `n = fBytes` bytes at the access `src`: `FMOVS`/`FMOVD`. -/
  | fload {c : Nat} {rd : Int} {src : Addr → Bool} :
      (v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload) → v.args.size = 2 →
      accessA lc g v = .ok src → memArg lc v 1 = .ok () → fresObj lc v = .ok (c, rd) →
      c = 8 * fBytes v.op →
      VK44 lc g v (.prog ⟨plain (fmovAs c) src (· == regA rd), (fmovAs c).name⟩)
  /-- `FMOVSstore`/`FMOVDstore` of a float of `n = fBytes` bytes at the access `dst`. -/
  | fstore {cs : Nat} {rs : Int} {dst : Addr → Bool} :
      (v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore) → v.args.size = 3 →
      memTy (lc.ty v.id) = true → lc.home v.id = none → accessA lc g v = .ok dst →
      fargObj lc v 1 = .ok (cs, rs) → memArg lc v 2 = .ok () → cs = 8 * fBytes v.op →
      VK44 lc g v (.prog ⟨plain (fmovAs cs) (· == regA rs) dst, (fmovAs cs).name⟩)
  /-- `FMOVSgpfp`/`FMOVDgpfp` of an integer register of class `ca ≥ c`: `FMOVS`/`FMOVD Rn, Fd`. -/
  | gpfp {ca c : Nat} {rn rd : Int} : (v.op = .ARM64FMOVSgpfp ∨ v.op = .ARM64FMOVDgpfp) →
      v.args.size = 1 → argObj lc v 0 = .ok (ca, rn) → fresObj lc v = .ok (c, rd) →
      c = 8 * fBytes v.op → c ≤ ca →
      VK44 lc g v (.prog (.ofShape { as := fmovAs c, from_ := regA rn, to := regA rd }))
  /-- `FMOVSfpgp`/`FMOVDfpgp` of a float to an integer register of its class:
  `FMOVS`/`FMOVD Fn, Rd`. -/
  | fpgp {ca c : Nat} {rn rd : Int} : (v.op = .ARM64FMOVSfpgp ∨ v.op = .ARM64FMOVDfpgp) →
      v.args.size = 1 → fargObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) →
      ca = 8 * fBytes v.op → c = 8 * fBytes v.op →
      VK44 lc g v (.prog (.ofShape { as := fmovAs c, from_ := regA rn, to := regA rd }))
  /-- `FMOVSconst`/`FMOVDconst`: `FMOVS`/`FMOVD $c, Fd`. -/
  | fconst {c : Nat} {rd : Int} : (v.op = .ARM64FMOVSconst ∨ v.op = .ARM64FMOVDconst) →
      v.args.size = 0 → fresObj lc v = .ok (c, rd) → c = 8 * fBytes v.op →
      VK44 lc g v (.prog (.ofShape { as := fmovAs c, from_ := fconstA v, to := regA rd }))

/-- What `fkind44` accepted: no temporary, and one of `VK44`'s float moves. -/
theorem fkind44_spec {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (h : fkind44 lc g v e = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK44 lc g v kd := by
  unfold fkind44 at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  split at h
  next hop =>
    obtain ⟨-, h⟩ := ex_guard h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, ra⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
    obtain ⟨hc, h⟩ := ex_guard h
    simp only [beq_iff_eq] at hsz hc
    subst hc
    split at h
    next he =>
      cases h
      simp only [beq_iff_eq] at he
      subst he
      exact .fcopyNone hop hsz ha hr
    next => cases h; exact .fcopy hop hsz ha hr
  all_goals first
    | (rename_i hop
       obtain ⟨hsz, h⟩ := ex_guard h
       obtain ⟨src, hsrc, h⟩ := ex_bind_eq_ok h
       obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
       obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
       obtain ⟨hc, h⟩ := ex_guard h
       cases h
       simp only [beq_iff_eq] at hsz hc
       exact .fload (by simp [hop]) hsz hsrc hma hr hc)
    | (rename_i hop
       obtain ⟨hsz, h⟩ := ex_guard h
       simp only [Bool.and_eq_true, beq_iff_eq] at hsz
       obtain ⟨dst, hdst, h⟩ := ex_bind_eq_ok h
       obtain ⟨⟨cs, rs⟩, hso, h⟩ := ex_bind_eq_ok h
       obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
       obtain ⟨hc, h⟩ := ex_guard h
       cases h
       simp only [beq_iff_eq] at hc
       exact .fstore (by simp [hop]) hsz.1.1 hsz.1.2 hsz.2 hdst hso hma hc)
    | (rename_i hop
       obtain ⟨hsz, h⟩ := ex_guard h
       obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
       obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
       obtain ⟨hc, h⟩ := ex_guard h
       cases h
       simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hsz hc
       exact .gpfp (by simp [hop]) hsz hao hro hc.1 hc.2)
    | (rename_i hop
       obtain ⟨hsz, h⟩ := ex_guard h
       obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
       obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
       obtain ⟨hc, h⟩ := ex_guard h
       cases h
       simp only [beq_iff_eq, Bool.and_eq_true] at hsz hc
       exact .fpgp (by simp [hop]) hsz hao hro hc.1 hc.2)
    | (rename_i hop
       obtain ⟨hsz, h⟩ := ex_guard h
       obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
       obtain ⟨hc, h⟩ := ex_guard h
       cases h
       simp only [beq_iff_eq] at hsz hc
       exact .fconst (by simp [hop]) hsz hro hc)
    | exact (ex_throw_bind (b := kd) (f := fun (_ : Unit) => Except.ok kd) h).elim
    | cases h

/-- What `vkind44` accepted of a value that is not an entry value: no temporary, and `VK44`. -/
theorem vkind44_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind44 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK44 lc g v kd := by
  unfold vkind44 at h
  cases h43 : vkind43 lc g v with
  | ok kd' =>
    rw [h43] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind43_spec h43 hen
    exact ⟨ht, .g42 hVK⟩
  | error e =>
    rw [h43] at h
    cases hf : fOp44 v.op with
    | true =>
      simp only [hf, ↓reduceIte] at h
      exact fkind44_spec h
    | false =>
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at h
      cases h

/-- On `InitMem`, `vkind44` is `vkind43`. -/
theorem vkind44_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind44 lc g v = vkind43 lc g v := by
  unfold vkind44
  cases vkind43 lc g v with
  | ok _ => rfl
  | error e => simp [hop, fOp44]

/-- On an op outside G44's (`fOp44`), `vkind44` is `vkind43`. -/
theorem vkind44_eq43 {lc : LocCtx} {g : G2In} {v : Value} (h : fOp44 v.op = false) :
    vkind44 lc g v = vkind43 lc g v := by
  unfold vkind44
  cases vkind43 lc g v with
  | ok _ => rfl
  | error e => simp [h]

/-- On a function with no arm64 op, G44's check is G33. -/
theorem checkG33_of_44L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG44L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG44L, hl] using h

/-- What `checkG44L` accepted of a function with an arm64 op: G43's facts with G44's value
check. -/
theorem checkG44L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG44L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind44 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG44L, hl, ↓reduceIte] at h
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

/-- What `checkG44` accepted: `refsLive`, and G44's check on the context without the removed
homes. -/
theorem checkG44_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG44 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG44L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG44 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
