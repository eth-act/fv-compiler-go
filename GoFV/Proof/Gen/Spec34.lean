import GoFV.Gen.Check34
import GoFV.Proof.Gen.Spec33

/-!
# What the genssa validator's slice G34 accepted (`docs/plans/proofs3.md` §4)

`checkG34 lc ps bstart g = .ok (tab, kt)` unfolded: on a function with an arm64 op, G33's facts
with `movdOK34` and `uEdgesOK34` in place of `movdOK31` and `uEdgesOK` (`checkG34_spec`,
`movdOK34_spec`, `uEdgesOK34_entry`, `uEdgesOK34_edge`); on one without, G33's (`checkG33_of_34`),
with empty tables (`uIn34_nl`, `uL34_nl`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The table before value `i + 1` of a function with an arm64 op: the table before value `i`
across value `i`. -/
theorem uL34_succ {lc : LocCtx} {L0 : List (Nat × Nat × Bool)} {blk : Block} {i : Nat} {id : ID}
    {v : Value} (hl : lc.ctx.f.lowered = true) (hi : blk.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) :
    uL34 lc L0 blk (i + 1) = uStep34 lc (uL34 lc L0 blk i) v := by
  simp [uL34, hl, hi, hv]

/-- On a function with no arm64 op, the tables are empty. -/
theorem uIn34_nl {lc : LocCtx} (hl : lc.ctx.f.lowered = false) (b : ID) : uIn34 lc b = [] := by
  simp [uIn34, hl]

theorem uL34_nl {lc : LocCtx} (hl : lc.ctx.f.lowered = false) (blk : Block) (b : ID) :
    ∀ i, uL34 lc (uIn34 lc b) blk i = []
  | 0 => uIn34_nl hl b
  | _ + 1 => by simp [uL34, hl]

/-- What `movdOK34` asks of a `MOVDnop x` or `MOVDreg x`: `x`'s register, class and `signOf` in
the table before it. -/
theorem movdOK34_spec {lc : LocCtx} (h : movdOK34 lc = true) {bid : ID}
    (hbid : bid ∈ lc.ctx.f.blocks.toList) {b : Block} (hb : lc.ctx.f.block? bid = some b)
    {i : Nat} {id : ID} (hi : b.values[i]? = some id) {v : Value}
    (hv : lc.ctx.f.value? id = some v) (hop : v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg)
    {x : ID} (hx : v.args[0]? = some x) :
    ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
      (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ uL34 lc (uIn34 lc bid) b i := by
  unfold movdOK34 at h
  have := List.all_eq_true.1 h _ hbid
  simp only [hb] at this
  have hi' : i < b.values.size := (Array.getElem?_eq_some_iff.1 hi).1
  have := List.all_eq_true.1 this i (List.mem_range.2 hi')
  have hne : (v.op != .ARM64MOVDnop && v.op != .ARM64MOVDreg) = false := by
    rcases hop with h | h <;> rw [h] <;> rfl
  simp only [hi, Option.bind_some, hv, hne, Bool.false_or, hx] at this
  revert this
  cases hr : regHome? lc x with
  | none => simp
  | some r =>
    cases hc : cls (lc.ty x) with
    | none => simp
    | some c =>
      intro hu
      exact ⟨r, c, rfl, rfl, by simpa using hu⟩

/-- `uEdgesOK34`: the entry block starts with nothing. -/
theorem uEdgesOK34_entry {lc : LocCtx} (h : uEdgesOK34 lc = true) :
    uIn34 lc lc.ctx.f.entry = [] := by
  unfold uEdgesOK34 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- `uEdgesOK34`: a successor's start is in its predecessor's end. -/
theorem uEdgesOK34_edge {lc : LocCtx} (h : uEdgesOK34 lc = true) {bid : ID}
    (hbid : bid ∈ lc.ctx.f.blocks.toList) {b : Block} (hb : lc.ctx.f.block? bid = some b)
    {e : Edge} (he : e ∈ b.succs.toList) :
    ∀ x ∈ uIn34 lc e.b, x ∈ uL34 lc (uIn34 lc bid) b b.values.size := by
  unfold uEdgesOK34 at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 bid hbid
  simp only [hb, List.all_eq_true] at this
  intro x hx
  simpa using this e he x hx

/-- On a function with no arm64 op, G34 is G33. -/
theorem checkG33_of_34 {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG34 lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG34, hl] using h

/-- What `checkG34` accepted of a function with an arm64 op: G33's facts with `movdOK34` and
`uEdgesOK34`. -/
theorem checkG34_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG34 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind33 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK34 lc = true ∧ uEdgesOK34 lc = true := by
  simp only [checkG34, hl, ↓reduceIte] at h
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
