import GoFV.Gen.Check37
import GoFV.Proof.Gen.Spec36

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G37 accepted (`docs/plans/proofs3.md` §4)

`checkG37 lc ps bstart g = .ok (tab, kt)` unfolded: on a function with an arm64 op, G36's facts
(`checkG37_spec`) with G37's value check (`vkind37_spec`, `VK37`: G36's values, the register ops
on 64-bit arguments or on the low words, the unary ops, the multiply-adds and `SBFX`); on one
without, G33's (`checkG33_of_37`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind37` accepted of a value that is not an entry value, and what it emits. -/
inductive VK37 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G36 (none of G37's ops). -/
  | g36 {kd : VKind2} : full37? v.op = none → w37? v.op = none → un37? v.op = none →
      madd37? v.op = none → v.op ≠ .ARM64SBFX → VK36 lc g v kd → VK37 lc g v kd
  /-- A register op `op Rm, Rn, Rd` on two 64-bit arguments (`full37?`, `cw = 64`) or on the low
  words of two arguments of at least 32 bits (`w37?`, `cw = 32`). -/
  | bin {as : As} {cw cx cy c : Nat} {rn rm rd : Int} :
      (full37? v.op = some as ∧ cw = 64 ∨ w37? v.op = some as ∧ cw = 32) → v.args.size = 2 →
      argObj lc v 0 = .ok (cx, rn) → argObj lc v 1 = .ok (cy, rm) → resObj lc v = .ok (c, rd) →
      8 ≤ c → cw ≤ cx → cw ≤ cy →
      VK37 lc g v (.prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }))
  /-- A unary op `op Rm, Rd` of an argument of at least `ca` bits. -/
  | un {as : As} {ca cx c : Nat} {rm rd : Int} :
      un37? v.op = some (as, ca) → v.args.size = 1 → argObj lc v 0 = .ok (cx, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → ca ≤ cx →
      VK37 lc g v (.prog (.ofShape { as, from_ := regA rm, to := regA rd }))
  /-- A multiply-add `op Rm, Ra, Rn, Rd`: arguments of at least 32 bits (`W`), or of classes at
  least the result's. -/
  | madd {as : As} {w : Bool} {ca cx cy c : Nat} {ra rm rn rd : Int} :
      madd37? v.op = some (as, w) → v.args.size = 3 → argObj lc v 0 = .ok (ca, ra) →
      argObj lc v 1 = .ok (cx, rm) → argObj lc v 2 = .ok (cy, rn) → resObj lc v = .ok (c, rd) →
      8 ≤ c → (w = true → 32 ≤ ca ∧ 32 ≤ cx ∧ 32 ≤ cy) →
      (w = false → c ≤ ca ∧ c ≤ cx ∧ c ≤ cy) →
      VK37 lc g v (.prog ⟨maddOK as ra rm rn rd, as.name⟩)
  /-- `SBFX [k] x`: `SBFX $lsb, Rn, $width, Rd`, the field within the argument's class. -/
  | sbfx {ca c : Nat} {rn rd : Int} :
      v.op = .ARM64SBFX → v.args.size = 1 → 0 ≤ v.auxInt.toInt → v.auxInt.toInt < 2 ^ 16 →
      argObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) → 8 ≤ c →
      0 < v.auxInt.toInt % 256 → v.auxInt.toInt / 256 + v.auxInt.toInt % 256 ≤ ca →
      VK37 lc g v (.prog ⟨sbfxOK (v.auxInt.toInt / 256) (v.auxInt.toInt % 256) rn rd, "SBFX"⟩)

/-- What `maddOK` fixes of a Prog. -/
theorem maddOK_spec {as : As} {ra rm rn rd : Int} {p : Prog} (h : maddOK as ra rm rn rd p = true) :
    p.as = as ∧ p.from_ = regA rm ∧ p.reg = ra ∧ p.to = regA rd ∧ p.scond = 0 ∧
      p.regTo2 = 0 ∧ ∃ x, p.rest = #[(x, regA rn)] := by
  unfold maddOK at h
  obtain ⟨h, hm⟩ := Eq.mp (Bool.and_eq_true _ _) h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨has, hf⟩, hr⟩, ht⟩, hs⟩, h2⟩ := h
  refine ⟨has, hf, hr, ht, hs, h2, ?_⟩
  generalize p.rest = r at hm ⊢
  rcases r with ⟨_ | ⟨⟨x, a⟩, _ | ⟨y, l⟩⟩⟩
  · exact absurd hm Bool.false_ne_true
  · have h3 : (a == regA rn) = true := hm
    exact ⟨x, by rw [beq_iff_eq.mp h3]⟩
  · exact absurd hm Bool.false_ne_true

/-- What `sbfxOK` fixes of a Prog. -/
theorem sbfxOK_spec {lsb width rn rd : Int} {p : Prog} (h : sbfxOK lsb width rn rd p = true) :
    p.as = .SBFX ∧ p.from_ = constA lsb ∧ p.reg = rn ∧ p.to = regA rd ∧ p.scond = 0 ∧
      p.regTo2 = 0 ∧ ∃ x, p.rest = #[(x, constA width)] := by
  unfold sbfxOK at h
  obtain ⟨h, hm⟩ := Eq.mp (Bool.and_eq_true _ _) h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨has, hf⟩, hr⟩, ht⟩, hs⟩, h2⟩ := h
  refine ⟨has, hf, hr, ht, hs, h2, ?_⟩
  generalize p.rest = r at hm ⊢
  rcases r with ⟨_ | ⟨⟨x, a⟩, _ | ⟨y, l⟩⟩⟩
  · exact absurd hm Bool.false_ne_true
  · have h3 : (a == constA width) = true := hm
    exact ⟨x, by rw [beq_iff_eq.mp h3]⟩
  · exact absurd hm Bool.false_ne_true

/-- What `bin37Kind` accepted: no temporary, and `VK37`'s `bin`. -/
theorem bin37Kind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {cw : Nat} {kd : VKind2}
    (hop : full37? v.op = some as ∧ cw = 64 ∨ w37? v.op = some as ∧ cw = 32)
    (h : bin37Kind lc v as cw = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK37 lc g v kd := by
  unfold bin37Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨cx, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cy, rm⟩, hbo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨ht, .bin hop hsz hao hbo hro hw.1.1 hw.1.2 hw.2⟩

/-- What `un37Kind` accepted: no temporary, and `VK37`'s `un`. -/
theorem un37Kind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {ca : Nat} {kd : VKind2}
    (hop : un37? v.op = some (as, ca)) (h : un37Kind lc v as ca = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK37 lc g v kd := by
  unfold un37Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨cx, rm⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨ht, .un hop hsz hao hro hw.1 hw.2⟩

/-- What `madd37Kind` accepted: no temporary, and `VK37`'s `madd`. -/
theorem madd37Kind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {w : Bool} {kd : VKind2}
    (hop : madd37? v.op = some (as, w)) (h : madd37Kind lc v as w = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK37 lc g v kd := by
  unfold madd37Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, ra⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cx, rm⟩, hxo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨cy, rn⟩, hyo, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨h8, hw⟩ := hw
  refine ⟨ht, .madd hop hsz hao hxo hyo hro h8 (fun hw1 => ?_) (fun hw0 => ?_)⟩
  · subst hw1
    simpa [and_assoc] using hw
  · subst hw0
    simpa [and_assoc] using hw

/-- What `sbfxKind` accepted: no temporary, and `VK37`'s `sbfx`. -/
theorem sbfxKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64SBFX) (h : sbfxKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK37 lc g v kd := by
  unfold sbfxKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsz hw
  exact ⟨ht, .sbfx hop hsz.1.1 hsz.1.2 hsz.2 hao hro hw.1.1 hw.1.2 hw.2⟩

/-- What `vkind37` accepted of a value that is not an entry value: no temporary, and `VK37`. -/
theorem vkind37_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind37 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK37 lc g v kd := by
  unfold vkind37 at h
  cases h1 : full37? v.op with
  | some as => rw [h1] at h; exact bin37Kind_spec (.inl ⟨h1, rfl⟩) h
  | none =>
    cases h2 : w37? v.op with
    | some as => rw [h1, h2] at h; exact bin37Kind_spec (.inr ⟨h2, rfl⟩) h
    | none =>
      cases h3 : un37? v.op with
      | some p =>
        obtain ⟨as, ca⟩ := p
        rw [h1, h2, h3] at h
        exact un37Kind_spec h3 h
      | none =>
        cases h4 : madd37? v.op with
        | some p =>
          obtain ⟨as, w⟩ := p
          rw [h1, h2, h3, h4] at h
          exact madd37Kind_spec h4 h
        | none =>
          rw [h1, h2, h3, h4] at h
          by_cases hs : v.op = .ARM64SBFX
          · simp only [hs, beq_self_eq_true, ↓reduceIte] at h
            exact sbfxKind_spec hs h
          have hs' : (v.op == .ARM64SBFX) = false := by simpa using hs
          simp only [hs', Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨htm, h36⟩ := vkind36_spec h hen
          exact ⟨htm, .g36 h1 h2 h3 h4 hs h36⟩

/-- On a function with no arm64 op, G37 is G33. -/
theorem checkG33_of_37 {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG37 lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG37, hl] using h

/-- What `checkG37` accepted of a function with an arm64 op: G36's facts with G37's value check. -/
theorem checkG37_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG37 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind37 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG37, hl, ↓reduceIte] at h
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
