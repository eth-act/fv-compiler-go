import GoFV.Gen.Check62
import GoFV.Proof.Gen.Spec61

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG62` accepted (`GoFV/Gen/Check62.lean`)

`VK62`: G61's kinds (`VK61`), or an `Arg` of an incoming stack argument (`VK62.arg`: no code,
homed in the slot of its piece with a `NAME_PARAM` operand). On `InitMem`, `vkind62` is `vkind61`
(`vkind62_initMem`). `checkG62L_spec` is `checkG61L_spec` with `vkind62`, and `checkG62_spec`
splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind62` accepted of a value that is not an entry value. -/
inductive VK62 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G61. -/
  | g61 {kd : VKind2} : VK61 lc g v kd → VK62 lc g v kd
  /-- An `Arg` of an incoming stack argument: no code, homed in the slot of its piece. -/
  | arg {x : AuxRef} {o : Int} (htemp : (lc.temps[v.id]?).join = none) (hop : v.op = .Arg)
      (hsz : v.args.size = 0) (hx : v.aux = some x) (hsp : stackParam lc x = true)
      (hcv : cls (lc.ty v.id) = some 64)
      (hh : lc.home v.id = some (.slot (argKey x v.type v.auxInt.toInt)))
      (hso : g.slotOp (argKey x v.type v.auxInt.toInt) = some (.PARAM, o)) : VK62 lc g v .none

/-- What `argKind62` accepted. -/
theorem argKind62_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .Arg) (h : argKind62 lc g v = .ok kd) : VK62 lc g v kd := by
  unfold argKind62 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  split at h
  · rename_i x hx
    obtain ⟨hsp, h⟩ := ex_guard h
    obtain ⟨hcv, h⟩ := ex_guard h
    obtain ⟨hh, h⟩ := ex_guard h
    split at h
    · rename_i o hso
      cases h
      exact .arg (by simpa using ht) hop (by simpa using hsz) hx hsp (by simpa using hcv)
        (by simpa using hh) hso
    · simp [ex_throw] at h
  · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h

/-- What `vkind62` accepted of a value that is not an entry value. -/
theorem vkind62_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind62 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK62 lc g v kd := by
  unfold vkind62 at h
  cases h61 : vkind61 lc g v with
  | ok kd' =>
    rw [h61] at h
    cases h
    exact .g61 (vkind61_spec h61 hen)
  | error e =>
    rw [h61] at h
    simp only at h
    unfold vkind62a at h
    split at h
    · rename_i r hr
      have hr' : v.op = .Arg ∧ argKind62 lc g v = r := by simpa using hr
      obtain ⟨hop, rfl⟩ := hr'
      exact argKind62_spec hop h
    · cases h

/-- On `InitMem`, `vkind62` is `vkind61`. -/
theorem vkind62_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind62 lc g v = vkind61 lc g v := by
  have hn : vkind62a lc g v = none := by simp [vkind62a, hop]
  unfold vkind62
  cases vkind61 lc g v <;> simp [hn]

/-- Off `Arg`, `vkind62` is `vkind61`. -/
theorem vkind62_eq61 {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op ≠ .Arg) :
    vkind62 lc g v = vkind61 lc g v := by
  have hn : vkind62a lc g v = none := by simp [vkind62a, hop]
  unfold vkind62
  cases vkind61 lc g v <;> simp [hn]

/-- On a function with no arm64 op, G62's check is G33. -/
theorem checkG33_of_62L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG62L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG62L, hl] using h

/-- What `checkG62L` accepted of a function with an arm64 op: G61's facts with G62's value check. -/
theorem checkG62L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG62L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind62 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true ∧
      spHomes48 lc = true ∧ atomOK lc ps tab = true := by
  simp only [checkG62L, hl, ↓reduceIte] at h
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

/-- What `checkG62` accepted: `refsLive`, and `checkG62L` on `liveCtx`. -/
theorem checkG62_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG62 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG62L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG62 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
