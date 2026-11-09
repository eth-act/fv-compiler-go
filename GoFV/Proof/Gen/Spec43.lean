import GoFV.Gen.Check43
import GoFV.Proof.Gen.Spec42

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG43` accepted (`GoFV/Gen/Check43.lean`)

On a value that is not an entry value, `vkind43` is `vkind42` (`vkind43_spec`); on `InitMem` it
accepted a clean position (`vkind43_initMem`: `cleanOK`, `initMemClean`, and `initMemKind`'s
facts). The facts of the clean positions: `keepsTo_succ` (one value less), `initMemClean_spec`
(each position of an `InitMem`), `cleanOK_edge` (a block with a successor in `C` is in `C`, its
values keeping the memory). `vkind43_eq42`: on an op other than `InitMem`, `vkind43` is
`vkind42`. `checkG43L_spec` is `checkG42L_spec` with `vkind43`, and
`checkG43_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The values before `i + 1` keep the memory: those before `i`, and value `i`. -/
theorem keepsTo_succ {lc : LocCtx} {b : Block} {i : Nat} {id : ID} {v : Value}
    (h : keepsTo lc b (i + 1) = true) (hi : b.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) : keepsTo lc b i = true ∧ memKeep lc v = true := by
  unfold keepsTo at h ⊢
  rw [List.range_succ, List.all_append] at h
  simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rw [hi] at h2
  simp only [Option.bind_some, hv, Option.all_some] at h2
  exact h2

/-- A clean position `i + 1`: position `i` is clean, and value `i` keeps the memory. -/
theorem cleanAt_succ {lc : LocCtx} {C : List ID} {bid : ID} {b : Block} {i : Nat} {id : ID}
    {v : Value} (h : cleanAt lc C bid b (i + 1) = true) (hi : b.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) : cleanAt lc C bid b i = true ∧ memKeep lc v = true := by
  unfold cleanAt at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨h1, h2⟩ := keepsTo_succ h.2 hi hv
  exact ⟨⟨h.1, h1⟩, h2⟩

/-- Each position of an `InitMem` is clean under `initMemClean`. -/
theorem initMemClean_spec {lc : LocCtx} {C : List ID} {bid : ID} {b : Block} {i : Nat} {id : ID}
    {v : Value} (h : initMemClean lc C = true) (hbid : bid ∈ lc.ctx.f.blocks.toList)
    (hb : lc.ctx.f.block? bid = some b) (hi : b.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) (hop : v.op = .InitMem) :
    cleanAt lc C bid b i = true := by
  unfold initMemClean at h
  have h1 := List.all_eq_true.1 h bid hbid
  rw [hb] at h1
  simp only [Option.all_some] at h1
  have hlt : i < b.values.size := (Array.getElem?_eq_some_iff.1 hi).1
  have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hlt)
  simp only [hi, Option.bind_some, hv, Option.all_some, hop, bne_self_eq_false,
    Bool.false_or] at h2
  exact h2

/-- A block with a successor in `C`, under `cleanOK`: its end is a clean position. -/
theorem cleanOK_edge {lc : LocCtx} {C : List ID} {bid : ID} {b : Block} {e : Edge}
    (h : cleanOK lc C = true) (hbid : bid ∈ lc.ctx.f.blocks.toList)
    (hb : lc.ctx.f.block? bid = some b) (he : e ∈ b.succs.toList) (hc : C.contains e.b = true) :
    cleanAt lc C bid b b.values.size = true := by
  unfold cleanOK at h
  have h1 := List.all_eq_true.1 h bid hbid
  rw [hb] at h1
  simp only [Option.all_some] at h1
  have h2 := Array.all_eq_true_iff_forall_mem.1 h1 e (Array.mem_toList_iff.1 he)
  simp only [hc, Bool.not_true, Bool.false_or] at h2
  exact h2

/-- What `vkind43` accepted of a value that is not an entry value: `vkind42`'s. -/
theorem vkind43_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind43 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK42 lc g v kd := by
  have hne : (v.op == .InitMem) = false := by
    cases hop : v.op <;> simp_all [entryOp24, entryOp3, entryOp]
  unfold vkind43 at h
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
  exact vkind42_spec h hen

/-- What `vkind43` accepted of an `InitMem`: a clean position (`cleanOK`, `initMemClean`), no
temporary, no argument, no home, shape `mem`, and no code. -/
theorem vkind43_initMem {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind43 lc g v = .ok kd) (hop : v.op = .InitMem) :
    cleanOK lc (cleanBlocks lc) = true ∧ initMemClean lc (cleanBlocks lc) = true ∧
      (lc.temps[v.id]?).join = none ∧ v.args.size = 0 ∧ lc.home v.id = none ∧
      memTy (lc.ty v.id) = true ∧ kd = .none := by
  unfold vkind43 at h
  simp only [hop, beq_self_eq_true, ↓reduceIte] at h
  cases hc : (cleanOK lc (cleanBlocks lc) && initMemClean lc (cleanBlocks lc)) with
  | false =>
    rw [hc] at h
    cases h
  | true =>
    rw [hc] at h
    simp only [↓reduceIte] at h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hc.1, hc.2, initMemKind_spec h⟩

/-- `vkind43` of an op other than `InitMem` is `vkind42`'s. -/
theorem vkind43_eq42 {lc : LocCtx} {g : G2In} {v : Value} (h : v.op ≠ .InitMem) :
    vkind43 lc g v = vkind42 lc g v := by
  unfold vkind43
  simp [h]

/-- On a function with no arm64 op, G43's check is G33. -/
theorem checkG33_of_43L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG43L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG43L, hl] using h

/-- What `checkG43L` accepted of a function with an arm64 op: G42's facts with G43's value
check. -/
theorem checkG43L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG43L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind43 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG43L, hl, ↓reduceIte] at h
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

/-- What `checkG43` accepted: `refsLive`, and G43's check on the context without the removed
homes. -/
theorem checkG43_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG43 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG43L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG43 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check
