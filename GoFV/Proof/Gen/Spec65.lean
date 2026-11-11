import GoFV.Gen.Check65
import GoFV.Proof.Gen.Spec64

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG65` accepted (`GoFV/Gen/Check65.lean`)

`VK65`: G64's kinds (`VK64`), a float load of a frame variable (`VK65.fvload`: `FMOVS`/`FMOVD
off(<nc>), Fd`, the variable `FVar57`) or a float pair store through a register or to a global
(`VK65.fstp`: `FSTPS`/`FSTPD (Fa, Fb), dst`, `dst` G3's `accessA`). On `InitMem`, `vkind65` is
`vkind64` (`vkind65_initMem`). `checkG65L_spec` is `checkG64L_spec` with `vkind65`, and
`checkG65_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind65` accepted of a value that is not an entry value. -/
inductive VK65 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G64. -/
  | g64 {kd : VKind2} : VK64 lc g v kd → VK65 lc g v kd
  /-- A float load of a frame variable: `FMOVS`/`FMOVD off(<nc>), Fd`. -/
  | fvload {nc : AddrName} {off : Int} {rd : Int} (hfv : FVar57 lc g v nc off)
      (htemp : (lc.temps[v.id]?).join = none)
      (hop : v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload) (hsz2 : v.args.size = 2)
      (hma : memArg lc v 1 = .ok ()) (hro : fresObj lc v = .ok (8 * fBytes v.op, rd)) :
      VK65 lc g v (.prog ⟨plain (fmovAs (8 * fBytes v.op)) (slotA · nc off) (· == regA rd),
        (fmovAs (8 * fBytes v.op)).name⟩)
  /-- A float pair store of `n`-byte elements through a register or to a global:
  `FSTPS`/`FSTPD (Fa, Fb), dst`. -/
  | fstp {n : Nat} {rx ry : Int} {dst : Addr → Bool} (htemp : (lc.temps[v.id]?).join = none)
      (hop : fstpOf v.op = some n) (hsz4 : v.args.size = 4) (hmt : memTy (lc.ty v.id) = true)
      (hhn : lc.home v.id = none) (hxo : fargObj lc v 1 = .ok (8 * n, rx))
      (hyo : fargObj lc v 2 = .ok (8 * n, ry)) (hma : memArg lc v 3 = .ok ())
      (hacc : accessA lc g v = .ok dst) :
      VK65 lc g v (.prog ⟨plain (fstpAs n) (· == pairA rx ry) dst, (fstpAs n).name⟩)

section Helpers

variable {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}

private theorem fvload65_spec {nc : AddrName} {off : Int} (hfv : FVar57 lc g v nc off)
    (hop : v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload)
    (h : fvload65 lc v nc off = .ok kd) : VK65 lc g v kd := by
  unfold fvload65 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  cases h
  simp only [beq_iff_eq] at ht hsz hw
  subst hw
  exact .fvload hfv ht hop hsz hma hro

private theorem fstp65_spec {n : Nat} (hop : fstpOf v.op = some n) (h : fstp65 lc g v n = .ok kd) :
    VK65 lc g v kd := by
  unfold fstp65 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨cx, rx⟩, hxo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cy, ry⟩, hyo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  obtain ⟨dst, hacc, h⟩ := ex_bind_eq_ok h
  cases h
  simp only [beq_iff_eq, Bool.and_eq_true] at ht hsz hw
  obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
  obtain ⟨rfl, rfl⟩ := hw
  exact .fstp ht hop hsz hmt hhn hxo hyo hma hacc

end Helpers

/-- What `vkind65a` accepted. -/
theorem vkind65a_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind65a lc g v = some (.ok kd)) : VK65 lc g v kd := by
  unfold vkind65a at h
  by_cases hl : v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload
  · simp only [hl, ↓reduceIte] at h
    cases hf : fvar57? lc g v with
    | none => simp only [hf, Option.map_none, reduceCtorEq] at h
    | some p =>
      obtain ⟨nc, off⟩ := p
      simp only [hf, Option.map_some, Option.some.injEq] at h
      exact fvload65_spec (fvar57?_spec hf) hl h
  · simp only [hl, ↓reduceIte] at h
    cases hn : fstpOf v.op with
    | none => simp only [hn, Option.map_none, reduceCtorEq] at h
    | some n =>
      simp only [hn, Option.map_some, Option.some.injEq] at h
      exact fstp65_spec hn h

/-- What `vkind65` accepted of a value that is not an entry value. -/
theorem vkind65_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind65 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK65 lc g v kd := by
  unfold vkind65 at h
  cases h64 : vkind64 lc g v with
  | ok kd' =>
    rw [h64] at h
    cases h
    exact .g64 (vkind64_spec h64 hen)
  | error e =>
    rw [h64] at h
    simp only at h
    cases ha : vkind65a lc g v with
    | none => rw [ha] at h; cases h
    | some r =>
      rw [ha] at h
      subst h
      exact vkind65a_spec ha

/-- The ops of G65: the float loads and the float pair stores. -/
def op65 (op : Op) : Bool :=
  op == .ARM64FMOVSload || op == .ARM64FMOVDload || op == .ARM64FSTPS || op == .ARM64FSTPD

/-- Off G65's ops, `vkind65a` is `none`. -/
theorem vkind65a_none {lc : LocCtx} {g : G2In} {v : Value} (h : op65 v.op = false) :
    vkind65a lc g v = none := by
  simp only [op65, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hl : ¬ (v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload) := by
    rintro (h | h) <;> contradiction
  have hn : fstpOf v.op = none := by
    unfold fstpOf
    simp [h3, h4]
  simp only [vkind65a, hl, ↓reduceIte, hn, Option.map_none]

/-- On `InitMem`, `vkind65` is `vkind64`. -/
theorem vkind65_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind65 lc g v = vkind64 lc g v := by
  have hn : vkind65a lc g v = none := vkind65a_none (by simp [op65, hop])
  unfold vkind65
  cases vkind64 lc g v <;> simp [hn]

/-- Off G65's ops (`op65`), `vkind65` is `vkind64`. -/
theorem vkind65_eq64 {lc : LocCtx} {g : G2In} {v : Value} (hq : op65 v.op = false) :
    vkind65 lc g v = vkind64 lc g v := by
  have hn : vkind65a lc g v = none := vkind65a_none hq
  unfold vkind65
  cases vkind64 lc g v <;> simp [hn]

/-- On a function with no arm64 op, G65's check is G33. -/
theorem checkG33_of_65L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG65L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG65L, hl] using h

/-- What `checkG65L` accepted of a function with an arm64 op: G64's facts with G65's value check. -/
theorem checkG65L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG65L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind65 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true ∧
      spHomes48 lc = true ∧ atomOK lc ps tab = true := by
  simp only [checkG65L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hlp, h⟩ := ex_guard h
  obtain ⟨hat, h⟩ := ex_guard h
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
      hsph, hat⟩
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

/-- What `checkG65` accepted: `refsLive`, and `checkG65L` on `liveCtx`. -/
theorem checkG65_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG65 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG65L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG65 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
