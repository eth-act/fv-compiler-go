import GoFV.Gen.Check63
import GoFV.Proof.Gen.Spec62

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG63` accepted (`GoFV/Gen/Check63.lean`)

`VK63`: G62's kinds (`VK62`), a float spill (`VK63.fspill`: `FMOVD Fs, off(RSP)`) or a float
reload (`VK63.freload`: `FMOVD off(RSP), Fd`). On `InitMem`, `vkind63` is `vkind62`
(`vkind63_initMem`). `checkG63L_spec` is `checkG62L_spec` with `vkind63`, and `checkG63_spec`
splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind63` accepted of a value that is not an entry value. -/
inductive VK63 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G62. -/
  | g62 {kd : VKind2} : VK62 lc g v kd → VK63 lc g v kd
  /-- A float spill: `FMOVD Fs, off(RSP)` at the slot's frame operand. -/
  | fspill {k : SlotKey} {nc : AddrName} {off : Int} {rs : Int}
      (htemp : (lc.temps[v.id]?).join = none) (hop : v.op = .StoreReg)
      (hh : lc.home v.id = some (.slot k)) (hso : g.slotOp k = some (nc, off))
      (hsz : v.args.size = 1) (hft : fTy (lc.ty v.id) = true) (hcv : cls (lc.ty v.id) = some 64)
      (hao : fargObj lc v 0 = .ok (64, rs)) :
      VK63 lc g v (.prog ⟨plain .FMOVD (· == regA rs) (slotA · nc off), "FMOVD spill"⟩)
  /-- A float reload: `FMOVD off(RSP), Fd` from the slot's frame operand. -/
  | freload {a : ID} {k : SlotKey} {nc : AddrName} {off : Int} {rd : Int}
      (htemp : (lc.temps[v.id]?).join = none) (hop : v.op = .LoadReg) (hsz : v.args.size = 1)
      (ha : v.args[0]? = some a) (hah : lc.home a = some (.slot k))
      (hso : g.slotOp k = some (nc, off)) (hca : cls (lc.ty a) = some 64)
      (hro : fresObj lc v = .ok (64, rd)) :
      VK63 lc g v (.prog ⟨plain .FMOVD (slotA · nc off) (· == regA rd), "FMOVD reload"⟩)

private theorem slotHome?_eq63 {lc : LocCtx} {a : ID} {k : SlotKey} :
    slotHome? lc a = some k ↔ lc.home a = some (.slot k) := by
  unfold slotHome?
  split <;> simp_all

/-- What `fspill63` accepted. -/
theorem fspill63_spec {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (hop : v.op = .StoreReg) (h : fspill63 lc g v e = .ok kd) : VK63 lc g v kd := by
  unfold fspill63 at h
  obtain ⟨-, h⟩ := ex_guard h
  obtain ⟨ht, h⟩ := ex_guard h
  split at h
  · rename_i k hk
    split at h
    · rename_i nc off hso
      obtain ⟨hsz, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq] at hsz
      obtain ⟨⟨c, rs⟩, hao, h⟩ := ex_bind_eq_ok h
      obtain ⟨hc, h⟩ := ex_guard h
      simp only [beq_iff_eq] at hc
      subst hc
      cases h
      exact .fspill (by simpa using ht) hop (slotHome?_eq63.mp hk) hso hsz.1.1 hsz.1.2 hsz.2 hao
    · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
  · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h

/-- What `freload63` accepted. -/
theorem freload63_spec {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (hop : v.op = .LoadReg) (h : freload63 lc g v e = .ok kd) : VK63 lc g v kd := by
  unfold freload63 at h
  obtain ⟨-, h⟩ := ex_guard h
  obtain ⟨ht, h⟩ := ex_guard h
  split at h
  · rename_i a ha
    split at h
    · rename_i k hk
      split at h
      · rename_i nc off hso
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
        obtain ⟨hc, h⟩ := ex_guard h
        simp only [beq_iff_eq] at hc
        subst hc
        cases h
        exact .freload (by simpa using ht) hop hsz.1 ha (slotHome?_eq63.mp hk) hso hsz.2 hro
      · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
    · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
  · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h

/-- What `vkind63` accepted of a value that is not an entry value. -/
theorem vkind63_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind63 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK63 lc g v kd := by
  unfold vkind63 at h
  cases h62 : vkind62 lc g v with
  | ok kd' =>
    rw [h62] at h
    cases h
    exact .g62 (vkind62_spec h62 hen)
  | error e =>
    rw [h62] at h
    simp only at h
    unfold vkind63a at h
    by_cases hs : v.op = .StoreReg
    · simp only [hs, beq_self_eq_true, ↓reduceIte] at h
      exact fspill63_spec hs h
    · by_cases hl : v.op = .LoadReg
      · simp only [hl, beq_self_eq_true, ↓reduceIte, reduceCtorEq] at h
        · exact freload63_spec hl h
      · simp only [beq_iff_eq, hs, hl, ↓reduceIte] at h
        cases h

/-- On `InitMem`, `vkind63` is `vkind62`. -/
theorem vkind63_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind63 lc g v = vkind62 lc g v := by
  have hn : ∀ e, vkind63a lc g v e = none := by simp [vkind63a, hop]
  unfold vkind63
  cases vkind62 lc g v <;> simp [hn]

/-- Off `StoreReg`/`LoadReg`, `vkind63` is `vkind62`. -/
theorem vkind63_eq62 {lc : LocCtx} {g : G2In} {v : Value} (hs : v.op ≠ .StoreReg)
    (hl : v.op ≠ .LoadReg) : vkind63 lc g v = vkind62 lc g v := by
  have hn : ∀ e, vkind63a lc g v e = none := by simp [vkind63a, hs, hl]
  unfold vkind63
  cases vkind62 lc g v <;> simp [hn]

/-- On a function with no arm64 op, G63's check is G33. -/
theorem checkG33_of_63L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG63L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG63L, hl] using h

/-- What `checkG63L` accepted of a function with an arm64 op: G62's facts with G63's value check. -/
theorem checkG63L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG63L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind63 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true ∧
      spHomes48 lc = true ∧ atomOK lc ps tab = true := by
  simp only [checkG63L, hl, ↓reduceIte] at h
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

/-- What `checkG63` accepted: `refsLive`, and `checkG63L` on `liveCtx`. -/
theorem checkG63_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG63 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG63L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG63 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
