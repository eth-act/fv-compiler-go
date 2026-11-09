import GoFV.Gen.Check33
import GoFV.Proof.Gen.Spec31

/-!
# What the genssa validator's slice G33 accepted (`docs/plans/proofs3.md` §4)

`checkG33 lc ps bstart g = .ok (tab, kt)` unfolded: on a function with an arm64 op, G31's facts
(`checkG33_spec`) with G33's value check (`vkind33_spec`, `VK33`: G32's values, `CLZ`/`REV`,
`UBFIZ`, `SRAconst` and `CMNWconst`); on one without, G31's (`checkG31_of_33`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind33` accepted of a value that is not an entry value, and what it emits. -/
inductive VK33 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G32 (none of G33's ops). -/
  | g32 {kd : VKind2} : un33? v.op = none → v.op ≠ .ARM64UBFIZ → v.op ≠ .ARM64SRAconst →
      v.op ≠ .ARM64CMNWconst → VK32 lc g v kd → VK33 lc g v kd
  /-- `CLZ x`, `REV x`: `op Rm, Rd`, of a 64-bit argument. -/
  | un {as : As} {ca c : Nat} {rm rd : Int} :
      un33? v.op = some as → v.args.size = 1 → argObj lc v 0 = .ok (ca, rm) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → ca = 64 →
      VK33 lc g v (.prog (.ofShape { as, from_ := regA rm, to := regA rd }))
  /-- `UBFIZ [k] x`: `UBFIZ $lsb, Rn, $width, Rd`. -/
  | ubfiz {ca c : Nat} {rn rd : Int} :
      v.op = .ARM64UBFIZ → v.args.size = 1 → 0 ≤ v.auxInt.toInt → v.auxInt.toInt < 2 ^ 16 →
      argObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) → 8 ≤ c →
      (v.auxInt.toInt % 256 ≤ ca ∨ c ≤ ca) →
      VK33 lc g v (.prog ⟨ubfizOK (v.auxInt.toInt / 256) (v.auxInt.toInt % 256) rn rd, "UBFIZ"⟩)
  /-- `SRAconst [k] x`: `ASR $k, Rn, Rd`, of a 64-bit argument. -/
  | sra {ca c : Nat} {rn rd : Int} :
      v.op = .ARM64SRAconst → v.args.size = 1 → argObj lc v 0 = .ok (ca, rn) →
      resObj lc v = .ok (c, rd) → 8 ≤ c → ca = 64 → 0 ≤ v.auxInt.toInt → v.auxInt.toInt < 64 →
      VK33 lc g v
        (.prog (.ofShape { as := .ASR, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }))
  /-- `CMNWconst [k] x`: `CMNW $k, Rn`. -/
  | cmnw {ca : Nat} {rn : Int} :
      v.op = .ARM64CMNWconst → v.args.size = 1 → (lc.ty v.id).isFlags = true →
      lc.home v.id = none → argObj lc v 0 = .ok (ca, rn) → 32 ≤ ca →
      VK33 lc g v (.prog (.ofShape { as := .CMNW, from_ := constA v.auxInt.toInt, reg := rn }))

/-- What `ubfizOK` fixes of a Prog. -/
theorem ubfizOK_spec {lsb width rn rd : Int} {p : Prog} (h : ubfizOK lsb width rn rd p = true) :
    p.as = .UBFIZ ∧ p.from_ = constA lsb ∧ p.reg = rn ∧ p.to = regA rd ∧ p.scond = 0 ∧
      p.regTo2 = 0 ∧ ∃ x, p.rest = #[(x, constA width)] := by
  unfold ubfizOK at h
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

/-- What `un33Kind` accepted: no temporary, and `VK33`'s `un`. -/
theorem un33Kind_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {kd : VKind2}
    (hop : un33? v.op = some as) (h : un33Kind lc v as = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK33 lc g v kd := by
  unfold un33Kind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rm⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  exact ⟨ht, .un hop hsz hao hro hw.1 hw.2⟩

/-- What `ubfizKind` accepted: no temporary, and `VK33`'s `ubfiz`. -/
theorem ubfizKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64UBFIZ) (h : ubfizKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK33 lc g v kd := by
  unfold ubfizKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hsz hw
  exact ⟨ht, .ubfiz hop hsz.1.1 hsz.1.2 hsz.2 hao hro hw.1 hw.2⟩

/-- What `sraKind` accepted: no temporary, and `VK33`'s `sra`. -/
theorem sraKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64SRAconst) (h : sraKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK33 lc g v kd := by
  unfold sraKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht hsz
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨h8, h64⟩, hk0⟩, hk⟩ := hw
  exact ⟨ht, .sra hop hsz hao hro h8 h64 hk0 hk⟩

/-- What `cmnwKind` accepted: no temporary, and `VK33`'s `cmnw`. -/
theorem cmnwKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64CMNWconst) (h : cmnwKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK33 lc g v kd := by
  unfold cmnwKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsh, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨hw, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [beq_iff_eq] at ht
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsh hw
  obtain ⟨⟨hsz, hfl⟩, hhn⟩ := hsh
  exact ⟨ht, .cmnw hop hsz hfl hhn hao hw⟩

/-- What `vkind33` accepted of a value that is not an entry value: no temporary, and `VK33`. -/
theorem vkind33_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind33 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK33 lc g v kd := by
  unfold vkind33 at h
  cases h1 : un33? v.op with
  | some as => rw [h1] at h; exact un33Kind_spec h1 h
  | none =>
    rw [h1] at h
    by_cases hu : v.op = .ARM64UBFIZ
    · simp only [hu, beq_self_eq_true, ↓reduceIte] at h
      exact ubfizKind_spec hu h
    have hu' : (v.op == .ARM64UBFIZ) = false := by simpa using hu
    simp only [hu', Bool.false_eq_true, ↓reduceIte] at h
    by_cases hs : v.op = .ARM64SRAconst
    · simp only [hs, beq_self_eq_true, ↓reduceIte] at h
      exact sraKind_spec hs h
    have hs' : (v.op == .ARM64SRAconst) = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, ↓reduceIte] at h
    by_cases hc : v.op = .ARM64CMNWconst
    · simp only [hc, beq_self_eq_true, ↓reduceIte] at h
      exact cmnwKind_spec hc h
    have hc' : (v.op == .ARM64CMNWconst) = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨htm, h32⟩ := vkind32_spec h hen
    exact ⟨htm, .g32 h1 hu hs hc h32⟩

/-- On a function with no arm64 op, G33 is G31. -/
theorem checkG31_of_33 {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG33 lc ps bstart g = r) : checkG31 lc ps bstart g = r := by
  simpa [checkG31, checkG33, hl] using h

/-- What `checkG33` accepted of a function with an arm64 op: G31's facts with G33's value check. -/
theorem checkG33_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG33 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind33 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK31 lc = true ∧ uEdgesOK lc = true := by
  simp only [checkG33, hl, ↓reduceIte] at h
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
