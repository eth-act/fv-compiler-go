import GoFV.Gen.Check38
import GoFV.Proof.Gen.Spec37

/-!
# What the genssa validator's slice G38 accepted (`docs/plans/proofs3.md` §4)

`checkG38 lc ps bstart g = .ok (tab, kt)` unfolded: on a function with an arm64 op, G37's facts
(`checkG38_spec`) with G38's value check (`vkind38_spec`, `VK38`: G37's values, the acquire loads
and their components); on one without, G33's (`checkG33_of_38`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind38` accepted of a value that is not an entry value, and what it emits. -/
inductive VK38 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G37 (no acquire load, no component of one). -/
  | g37 {kd : VKind2} : ldar? v.op = none → selLdar lc v = false → VK37 lc g v kd →
      VK38 lc g v kd
  /-- An acquire load of `n` bytes: `op (Rn), Rd`, its component of class `8n` in `Rd`. -/
  | ldar {as : As} {n : Nat} {t0 : Ty} {rn rd : Int} {r : Nat} :
      ldar? v.op = some (as, n) → v.args.size = 2 → v.aux = none → v.auxInt.toInt = 0 →
      lc.ty v.id = .tuple [t0, .mem] → cls t0 = some (8 * n) → argObj lc v 0 = .ok (64, rn) →
      memArg lc v 1 = .ok () → lc.home v.id = some (.pair (some r) none) → r ≠ zeroReg →
      destOK r = true → objOf? r = some rd →
      VK38 lc g v (.prog ⟨plain as (· == memA rn 0) (· == regA rd), as.name⟩)
  /-- `Select0` of an acquire load, homed in the load's register: no code. -/
  | sel0 {c : ID} {r : Nat} {t0 : Ty} :
      v.op = .Select0 → v.args.size = 1 → v.args[0]? = some c →
      ((lc.ctx.f.value? c).any fun u => (ldar? u.op).isSome) = true →
      lc.ty c = .tuple [t0, .mem] → (cls t0).isSome = true →
      lc.home c = some (.pair (some r) none) → lc.home v.id = some (.reg r) → r ≠ zeroReg →
      destOK r = true → (objOf? r).isSome = true → (cls (lc.ty v.id)).isSome = true →
      cls t0 = cls (lc.ty v.id) → VK38 lc g v .none
  /-- `Select1` of an acquire load: the memory, no home, no code. -/
  | sel1 {c : ID} {r : Nat} {t0 : Ty} :
      v.op = .Select1 → v.args.size = 1 → v.args[0]? = some c →
      ((lc.ctx.f.value? c).any fun u => (ldar? u.op).isSome) = true →
      lc.ty c = .tuple [t0, .mem] → (cls t0).isSome = true →
      lc.home c = some (.pair (some r) none) → memTy (lc.ty v.id) = true →
      lc.home v.id = none → VK38 lc g v .none

/-- The register of an acquire load's home. -/
theorem ldarHome?_some {lc : LocCtx} {id : ID} {r : Nat} (h : ldarHome? lc id = some r) :
    lc.home id = some (.pair (some r) none) := by
  unfold ldarHome? at h
  split at h
  · rename_i hh; cases h; exact hh
  · cases h

/-- The shape of an acquire load. -/
theorem ldarTy_spec {n : Nat} {t : Ty} (h : ldarTy n t = true) :
    ∃ t0, t = .tuple [t0, .mem] ∧ cls t0 = some (8 * n) := by
  unfold ldarTy at h
  split at h
  · rename_i t0
    exact ⟨t0, rfl, by simpa using h⟩
  · cases h

/-- The shape of the acquire load a component selects from. -/
theorem ldarSelTy_spec {t : Ty} (h : ldarSelTy t = true) :
    ∃ t0, t = .tuple [t0, .mem] ∧ (cls t0).isSome = true := by
  unfold ldarSelTy at h
  split at h
  · rename_i t0
    exact ⟨t0, rfl, h⟩
  · cases h

/-- What `ldarKind` accepted: no temporary, and `VK38`'s `ldar`. -/
theorem ldarKind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {n : Nat} {kd : VKind2}
    (hop : ldar? v.op = some (as, n)) (h : ldarKind lc v as n = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK38 lc g v kd := by
  unfold ldarKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsh, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨hca, h⟩ := ex_guard h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  cases hh : ldarHome? lc v.id with
  | none => rw [hh] at h; simp [ex_throw] at h
  | some r =>
    rw [hh] at h
    obtain ⟨hr, h⟩ := ex_guard h
    cases ho : objOf? r with
    | none => rw [ho] at h; simp [ex_throw] at h
    | some rd =>
      rw [ho] at h
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      simp only [beq_iff_eq] at ht hca
      subst hca
      simp only [Bool.and_eq_true, beq_iff_eq] at hsh
      obtain ⟨⟨⟨hsz, hax⟩, hk⟩, hty⟩ := hsh
      obtain ⟨t0, hty, hc0⟩ := ldarTy_spec hty
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hr
      exact ⟨ht, .ldar hop hsz (by simpa using hax) hk hty hc0 hao hma (ldarHome?_some hh) hr.1
        hr.2 ho⟩

/-- What `selLdarKind` accepted of a component of an acquire load: no temporary, and `VK38`'s
`sel0` or `sel1`. -/
theorem selLdarKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hsel : selLdar lc v = true) (h : selLdarKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK38 lc g v kd := by
  unfold selLdar at hsel
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hsel
  obtain ⟨hop, hu⟩ := hsel
  unfold selLdarKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  cases hc : v.args[0]? with
  | none => rw [hc] at h; simp [ex_throw] at h
  | some c =>
    rw [hc] at h
    rw [hc, Option.bind_some] at hu
    obtain ⟨hsz, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsz
    obtain ⟨hsz, hst⟩ := hsz
    obtain ⟨t0, htc, hc0⟩ := ldarSelTy_spec hst
    cases hh : ldarHome? lc c with
    | none => rw [hh] at h; simp [ex_throw] at h
    | some r =>
      rw [hh] at h
      rcases hop with hop | hop
      · simp only [hop, beq_self_eq_true, ↓reduceIte] at h
        obtain ⟨hk, h⟩ := ex_guard h
        simp only [ex_pure, Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hk
        obtain ⟨⟨⟨⟨⟨hvh, hrz⟩, hd⟩, hob⟩, hcl⟩, hcc⟩ := hk
        rw [htc] at hcc
        exact ⟨ht, .sel0 hop hsz hc hu htc hc0 (ldarHome?_some hh) hvh hrz hd hob hcl
          (by simpa [tupleTys] using hcc)⟩
      · have h0 : (v.op == .Select0) = false := by rw [hop]; rfl
        simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨hk, h⟩ := ex_guard h
        simp only [ex_pure, Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        exact ⟨ht, .sel1 hop hsz hc hu htc hc0 (ldarHome?_some hh) hk.1 hk.2⟩

/-- What `vkind38` accepted of a value that is not an entry value: no temporary, and `VK38`. -/
theorem vkind38_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind38 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK38 lc g v kd := by
  unfold vkind38 at h
  cases h1 : ldar? v.op with
  | some p =>
    obtain ⟨as, n⟩ := p
    rw [h1] at h
    exact ldarKind_spec h1 h
  | none =>
    rw [h1] at h
    cases hs : selLdar lc v with
    | true =>
      simp only [hs, ↓reduceIte] at h
      exact selLdarKind_spec hs h
    | false =>
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨htm, h37⟩ := vkind37_spec h hen
      exact ⟨htm, .g37 h1 hs h37⟩

/-- On a function with no arm64 op, G38 is G33. -/
theorem checkG33_of_38 {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG38 lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG38, hl] using h

/-- What `checkG38` accepted of a function with an arm64 op: G37's facts with G38's value check. -/
theorem checkG38_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG38 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind38 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG38, hl, ↓reduceIte] at h
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

end GoFV.Gen.Check
