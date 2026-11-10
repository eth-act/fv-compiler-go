import GoFV.Gen.Check3
import GoFV.Proof.Gen.Spec2

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G3 accepted (`docs/plans/proofs3.md` §4)

`checkG3 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G3.lean`) uses (`checkG3_spec`): G2's (`Spec2.lean`) with G3's value check
(`vkind3_spec`, `VK3`: G2's values, where a static call has distinct result registers; the loads
and stores of `off(Rn)` or of a global, `AccessOK`; extensions; `AND`/`LSL`/`LSR $k`; `UBFX`;
`CMPW`; `SB`), G3's terminators (`Cx.termG3_spec`, `TermOK3`: `CBZW`/`CBNZW`, `TBZ`/`TBNZ`), its
homes (`homeOK3`) and the class table (`checkK_spec`). The class-map algebra (`KMap.get_bot`,
`KMap.get_set`, `kResults_get_of_not_mem`, `kResults_get_of_mem`, `kStep_get`, `kAt_zero`,
`kAt_succ`) computes the class of each register before each value from the table.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The memory operands an access `v` (address argument 0) may name, as `accessA` accepted them:
`off(Rn)` with `Rn` the 64-bit register of argument 0 and no symbol, or `sym+off(SB)` of a
global with argument `SB`. -/
inductive AccessOK (lc : LocCtx) (g : G2In) (v : Value) : (Addr → Prop) → Prop
  /-- `off(Rn)`: no symbol, the address in a 64-bit register. -/
  | reg {rn : Int} : v.aux = none → argObj lc v 0 = .ok (64, rn) →
      AccessOK lc g v (· = memA rn v.auxInt.toInt)
  /-- `sym+off(SB)`: argument `SB`, the global's symbol. -/
  | glob {x a : Nat} {name : GoStr} {abi : Nat} : v.aux = some x → v.args[0]? = some a →
      (lc.ctx.f.value? a).map (·.op) = some .SB → symOf? lc.ctx.tabs x = some (name, abi) →
      AccessOK lc g v (fun A => A.type = .MEM ∧ A.name = .EXTERN ∧ A.reg = 0 ∧ A.index = 0 ∧
        A.offset = v.auxInt.toInt ∧ ∃ y, A.sym = some y ∧ g.syms[y]? = some (name, abi))

/-- What `accessA` accepted: an `AccessOK` form that every accepted operand has. -/
theorem accessA_spec {lc : LocCtx} {g : G2In} {v : Value} {src : Addr → Bool}
    (h : accessA lc g v = .ok src) :
    ∃ P, AccessOK lc g v P ∧ ∀ A, src A = true → P A := by
  unfold accessA at h
  split at h
  next hx =>
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨hc, h'⟩ := ex_guard h
    simp only [beq_iff_eq] at hc
    subst hc
    simp only [ex_pure, Except.ok.injEq] at h'
    subst h'
    exact ⟨_, AccessOK.reg hx ha, fun A hA => by simpa using hA⟩
  next x hx =>
    split at h
    next a ha =>
      obtain ⟨hsb, h⟩ := ex_guard h
      split at h
      next name abi hs =>
        simp only [ex_pure, Except.ok.injEq] at h
        subst h
        refine ⟨_, AccessOK.glob hx ha (by simpa using hsb) hs, fun A hA => ?_⟩
        simp only [globA, Bool.and_eq_true, beq_iff_eq] at hA
        obtain ⟨⟨⟨⟨⟨hty, hnm⟩, hr⟩, hix⟩, hoff⟩, hsym⟩ := hA
        refine ⟨hty, hnm, hr, hix, hoff, ?_⟩
        split at hsym
        next y hy => exact ⟨y, hy, by simpa using hsym⟩
        next => simp at hsym
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h

private theorem narrowLoad?_as {op : Op} {as : As} {n : Nat} {sg : Bool}
    (h : narrowLoad? op = some (as, n, sg)) : as ≠ .MOVD := by
  unfold narrowLoad? at h
  split at h <;> cases h <;> decide

private theorem narrowStore?_as {op : Op} {as : As} {n : Nat}
    (h : narrowStore? op = some (as, n)) : as ≠ .MOVD := by
  unfold narrowStore? at h
  split at h <;> cases h <;> decide

private theorem loadOp?_movd {op : Op} {n : Nat} {sg : Bool}
    (h : loadOp? op = some (.MOVD, n, sg)) : op = .ARM64MOVDload := by
  unfold loadOp? at h
  split at h
  next hop => simpa using hop
  next => exact absurd rfl (narrowLoad?_as h)

private theorem storeOp?_movd {op : Op} {n : Nat} (h : storeOp? op = some (.MOVD, n)) :
    op = .ARM64MOVDstore := by
  unfold storeOp? at h
  split at h
  next hop => simpa using hop
  next => exact absurd rfl (narrowStore?_as h)

private theorem none_of_forall3 {α β γ : Type} {o : Option (α × β × γ)}
    (h : ∀ a b c, o = some (a, b, c) → False) : o = none := by
  cases o with
  | none => rfl
  | some x => exact (h x.1 x.2.1 x.2.2 rfl).elim

private theorem none_of_forall2 {α β : Type} {o : Option (α × β)}
    (h : ∀ a b, o = some (a, b) → False) : o = none := by
  cases o with
  | none => rfl
  | some x => exact (h x.1 x.2 rfl).elim

private theorem ubfxOK_spec {lsb width rn rd : Int} {p : Prog}
    (h : ubfxOK lsb width rn rd p = true) :
    p.as = .UBFX ∧ p.from_ = constA lsb ∧ p.reg = rn ∧ p.to = regA rd ∧ p.scond = 0 ∧
      p.regTo2 = 0 ∧ ∃ x, p.rest = #[(x, constA width)] := by
  unfold ubfxOK at h
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

/-- What `vkind3` accepted of a value that is not an entry value, and what it emits. -/
inductive VK3 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G2: `vkind3` delegated to `vkind2`, for an op that is none of G3's, or a
  `MOVDload`/`MOVDstore` without symbol; a static call has distinct result registers. -/
  | g2 {kd : VKind2} :
      (loadOp? v.op = none ∧ storeOp? v.op = none ∧ v.op ≠ .SB ∧ extOp? v.op = none ∧
        v.op ≠ .ARM64ANDconst ∧ v.op ≠ .ARM64SLLconst ∧ v.op ≠ .ARM64SRLconst ∧
        v.op ≠ .ARM64UBFX ∧ v.op ≠ .ARM64CMPW ∧ v.op ≠ .ARM64CMPWconst) ∨
      ((v.op = .ARM64MOVDload ∨ v.op = .ARM64MOVDstore) ∧ v.aux = none) →
      (v.op = .ARM64CALLstatic → ∀ name abi cabi ins outs,
        callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) → callRegs cabi = .ok (ins, outs) →
        outs.Nodup) →
      VK2 lc g v kd → VK3 lc g v kd
  /-- A load `MOV… src, Rd` of `n` bytes (sign extension `sg`) from the operand `src` of the
  address argument 0 (`AccessOK`), into a register of at least 8 bits, or a boolean (`MOVBU`). -/
  | load {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int} {src : Addr → Prop} {pat : Pat} :
      loadOp? v.op = some (as, n, sg) → (as = .MOVD → v.aux ≠ none) → v.args.size = 2 →
      AccessOK lc g v src → memArg lc v 1 = .ok () → resObj lc v = .ok (c, rd) →
      (8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false) →
      (∀ p, pat.ok p = true → p.as = as ∧ src p.from_ ∧ p.reg = 0 ∧ p.to = regA rd ∧
        p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0) →
      VK3 lc g v (.prog pat)
  /-- A store `MOV… Rs, dst` of `n` bytes of argument 1 to the operand `dst` of the address
  argument 0 (`AccessOK`): a value at least as wide as the access, or a boolean byte. -/
  | store {as : As} {n cs : Nat} {rs : Int} {dst : Addr → Prop} {pat : Pat} :
      storeOp? v.op = some (as, n) → (as = .MOVD → v.aux ≠ none) → v.args.size = 3 →
      memTy (lc.ty v.id) = true → lc.home v.id = none → AccessOK lc g v dst →
      argObj lc v 1 = .ok (cs, rs) → memArg lc v 2 = .ok () → (8 * n ≤ cs ∨ cs = 1 ∧ n = 1) →
      (∀ p, pat.ok p = true → p.as = as ∧ p.from_ = regA rs ∧ p.reg = 0 ∧ dst p.to ∧
        p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0) →
      VK3 lc g v (.prog pat)
  /-- `SB`: no code, no machine register, a register shape. -/
  | sb : v.op = .SB → v.args.size = 0 → (cls (lc.ty v.id)).isSome = true →
      (lc.home v.id = none ∨ lc.home v.id = some (.reg sbReg)) → VK3 lc g v .none
  /-- The extension `MOV… Rn, Rd` of the low `w` bits (sign extension `sg`): an argument of at
  least `w` bits or a boolean, a result of at least 8 bits. -/
  | ext {as : As} {w : Nat} {sg : Bool} {ca c : Nat} {rn rd : Int} :
      extOp? v.op = some (as, w, sg) → v.args.size = 1 → argObj lc v 0 = .ok (ca, rn) →
      resObj lc v = .ok (c, rd) → (w ≤ ca ∨ ca = 1) → 8 ≤ c →
      VK3 lc g v (.prog (.ofShape { as, from_ := regA rn, to := regA rd }))
  /-- `AND`/`LSL`/`LSR $k, Rn, Rd`: a result of at least 8 bits, no wider than the argument;
  `LSR` of a 64-bit argument; a shift by an amount in `[0, 64)`. -/
  | aluK {as : As} {ca c : Nat} {rn rd : Int} :
      (v.op = .ARM64ANDconst ∧ as = .AND ∨ v.op = .ARM64SLLconst ∧ as = .LSL ∨
        v.op = .ARM64SRLconst ∧ as = .LSR) →
      v.args.size = 1 → argObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) → 8 ≤ c →
      c ≤ ca → (v.op = .ARM64SRLconst → ca = 64) →
      (v.op ≠ .ARM64ANDconst → 0 ≤ v.auxInt.toInt ∧ v.auxInt.toInt < 64) →
      VK3 lc g v (.prog (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }))
  /-- `UBFX $lsb, Rn, $width, Rd` (`auxInt = lsb * 256 + width`): a result of at least 8 bits,
  an argument holding the extracted bits. -/
  | ubfx {ca c : Nat} {rn rd : Int} {pat : Pat} :
      v.op = .ARM64UBFX → v.args.size = 1 → 0 ≤ v.auxInt.toInt → v.auxInt.toInt < 2 ^ 16 →
      argObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) → 8 ≤ c →
      0 < v.auxInt.toInt % 256 → v.auxInt.toInt / 256 + v.auxInt.toInt % 256 ≤ ca →
      (∀ p, pat.ok p = true → p.as = .UBFX ∧ p.from_ = constA (v.auxInt.toInt / 256) ∧
        p.reg = rn ∧ p.to = regA rd ∧ p.scond = 0 ∧ p.regTo2 = 0 ∧
        ∃ x, p.rest = #[(x, constA (v.auxInt.toInt % 256))]) →
      VK3 lc g v (.prog pat)
  /-- `CMPW Rm, Rn` of arguments of at least 32 bits. -/
  | cmpw {ca cb : Nat} {rn rm : Int} : v.op = .ARM64CMPW → v.args.size = 2 →
      (lc.ty v.id).isFlags = true → lc.home v.id = none → argObj lc v 0 = .ok (ca, rn) →
      argObj lc v 1 = .ok (cb, rm) → 32 ≤ ca → 32 ≤ cb →
      VK3 lc g v (.prog (.ofShape { as := .CMPW, from_ := regA rm, reg := rn }))
  /-- `CMPW $k, Rn` of an argument of at least 32 bits. -/
  | cmpwK {ca : Nat} {rn : Int} : v.op = .ARM64CMPWconst → v.args.size = 1 →
      (lc.ty v.id).isFlags = true → lc.home v.id = none → argObj lc v 0 = .ok (ca, rn) →
      32 ≤ ca →
      VK3 lc g v (.prog (.ofShape { as := .CMPW, from_ := constA v.auxInt.toInt, reg := rn }))

/-- What `vkind3` accepted of a value that is not an entry value (of G3: `SB` is not one):
no temporary, and `VK3`. -/
theorem vkind3_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : vkind3 lc g v = .ok kd)
    (hen : entryOp3 v.op = false) : (lc.temps[v.id]?).join = none ∧ VK3 lc g v kd := by
  have ht : (lc.temps[v.id]?).join = none := by
    by_cases ht : (lc.temps[v.id]?).join = none
    · exact ht
    · unfold vkind3 at h
      simp [ht, ex_throw, ex_bind_error] at h
  refine ⟨ht, ?_⟩
  unfold vkind3 at h
  simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  next as n sg hl =>
    split at h
    next hm =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨rfl, hx⟩ := hm
      have hop := loadOp?_movd hl
      have hen2 : entryOp v.op = false := by rw [hop]; rfl
      exact VK3.g2 (Or.inr ⟨Or.inl hop, hx⟩) (fun h' => by rw [hop] at h'; cases h')
        (vkind2_spec h hen2).2
    next hm =>
      obtain ⟨hsz, h⟩ := ex_guard h
      obtain ⟨src, hsrc, h⟩ := ex_bind_eq_ok h
      obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
      obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
      obtain ⟨hw, h⟩ := ex_guard h
      cases h
      simp only [beq_iff_eq] at hsz
      obtain ⟨P, hP, hPs⟩ := accessA_spec hsrc
      refine VK3.load hl (by simpa using hm) hsz hP hma hr (by simpa [and_assoc] using hw) ?_
      intro p hp
      simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hp
      obtain ⟨has, hfrom, hreg, hto, hsc, hrest, hr2⟩ := hp
      exact ⟨has, hPs _ hfrom, hreg, hto, hsc, hrest, hr2⟩
  next hl =>
    have hl' := none_of_forall3 hl
    split at h
    next as n hs =>
      split at h
      next hm =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        obtain ⟨rfl, hx⟩ := hm
        have hop := storeOp?_movd hs
        have hen2 : entryOp v.op = false := by rw [hop]; rfl
        exact VK3.g2 (Or.inr ⟨Or.inr hop, hx⟩) (fun h' => by rw [hop] at h'; cases h')
          (vkind2_spec h hen2).2
      next hm =>
        obtain ⟨hsz, h⟩ := ex_guard h
        obtain ⟨dst, hdst, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨cs, rs⟩, ha, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
        obtain ⟨hw, h⟩ := ex_guard h
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨P, hP, hPs⟩ := accessA_spec hdst
        refine VK3.store hs (by simpa using hm) hsz.1.1 hsz.1.2 hsz.2 hP ha hma
          (by simpa [and_assoc] using hw) ?_
        intro p hp
        simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hp
        obtain ⟨has, hfrom, hreg, hto, hsc, hrest, hr2⟩ := hp
        exact ⟨has, hfrom, hreg, hPs _ hto, hsc, hrest, hr2⟩
    next hs =>
      have hs' := none_of_forall2 hs
      split at h
      next hsb =>
        obtain ⟨hc, h⟩ := ex_guard h
        cases h
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hsb hc
        exact VK3.sb hsb hc.1.1 hc.1.2 hc.2
      next hsb =>
        have hsb' : v.op ≠ .SB := by simpa using hsb
        split at h
        next as w sg he =>
          obtain ⟨hsz, h⟩ := ex_guard h
          obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
          obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
          obtain ⟨hw, h⟩ := ex_guard h
          cases h
          simp only [beq_iff_eq] at hsz
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
          exact VK3.ext he hsz ha hr hw.1 hw.2
        next he =>
          have he' := none_of_forall3 he
          split at h
          next _ hop =>
            obtain ⟨hsz, h⟩ := ex_guard h
            obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
            obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
            obtain ⟨hw, h⟩ := ex_guard h
            cases h
            simp only [beq_iff_eq] at hsz
            simp [hop] at hw
            simp only [hop]
            exact VK3.aluK (Or.inl ⟨hop, rfl⟩) hsz ha hr (by omega) (by omega)
              (fun h' => by rw [hop] at h'; cases h') (fun h' => absurd hop h')
          next _ hop =>
            obtain ⟨hsz, h⟩ := ex_guard h
            obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
            obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
            obtain ⟨hw, h⟩ := ex_guard h
            cases h
            simp only [beq_iff_eq] at hsz
            simp [hop] at hw
            simp only [hop]
            exact VK3.aluK (Or.inr (Or.inl ⟨hop, rfl⟩)) hsz ha hr (by omega) (by omega)
              (fun h' => by rw [hop] at h'; cases h') (fun _ => ⟨by omega, by omega⟩)
          next _ hop =>
            obtain ⟨hsz, h⟩ := ex_guard h
            obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
            obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
            obtain ⟨hw, h⟩ := ex_guard h
            cases h
            simp only [beq_iff_eq] at hsz
            simp [hop] at hw
            simp only [hop]
            exact VK3.aluK (Or.inr (Or.inr ⟨hop, rfl⟩)) hsz ha hr (by omega) (by omega)
              (fun _ => by omega) (fun _ => ⟨by omega, by omega⟩)
          next _ hop =>
            obtain ⟨hsz, h⟩ := ex_guard h
            obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
            obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
            obtain ⟨hw, h⟩ := ex_guard h
            cases h
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsz hw
            exact VK3.ubfx hop hsz.1.1 hsz.1.2 hsz.2 ha hr hw.1.1 hw.1.2 hw.2
              (fun p hp => ubfxOK_spec hp)
          next _ hop =>
            split at h
            next hc =>
              rename_i name abi cabi
              obtain ⟨⟨ins, outs⟩, hcr, h⟩ := ex_bind_eq_ok h
              obtain ⟨hnd, h⟩ := ex_guard h
              have hen2 : entryOp v.op = false := by rw [hop]; rfl
              refine VK3.g2 (Or.inl ⟨hl', hs', hsb', he', by simp [hop], by simp [hop],
                by simp [hop], by simp [hop], by simp [hop], by simp [hop]⟩) ?_ (vkind2_spec h hen2).2
              intro _ name' abi' cabi' ins' outs' hc' hcr'
              rw [hc] at hc'
              cases hc'
              rw [hcr] at hcr'
              cases hcr'
              exact hnd
            next => simp [ex_throw] at h
          next _ hop =>
            obtain ⟨hsz, h⟩ := ex_guard h
            obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
            obtain ⟨⟨cb, rm⟩, hb, h⟩ := ex_bind_eq_ok h
            obtain ⟨hw, h⟩ := ex_guard h
            cases h
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsz hw
            exact VK3.cmpw hop hsz.1.1 hsz.1.2 hsz.2 ha hb hw.1 hw.2
          next _ hop =>
            obtain ⟨hsz, h⟩ := ex_guard h
            obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
            obtain ⟨hw, h⟩ := ex_guard h
            cases h
            simp only [Bool.and_eq_true, beq_iff_eq] at hsz hw
            exact VK3.cmpwK hop hsz.1.1 hsz.1.2 hsz.2 ha hw
          next _ h1 h2 h3 h4 h5 h6 h7 =>
            have hen2 : entryOp v.op = false := by simpa [entryOp3, hsb'] using hen
            exact VK3.g2 (Or.inl ⟨hl', hs', hsb', he', h1, h2, h3, h4, h6, h7⟩)
              (fun h' => absurd h' h5) (vkind2_spec h hen2).2

/-! ## Terminators -/

private theorem arr_one3 {α : Type} {xs : Array α} {e : α} (hs : xs.size = 1)
    (h0 : xs[0]? = some e) : xs = #[e] := by
  rcases xs with ⟨l⟩
  rcases l with _ | ⟨a, _ | ⟨a', l⟩⟩ <;> simp_all

private theorem arr_two3 {α : Type} {xs : Array α} {e0 e1 : α} (hs : xs.size = 2)
    (h0 : xs[0]? = some e0) (h1 : xs[1]? = some e1) : xs = #[e0, e1] := by
  rcases xs with ⟨l⟩
  rcases l with _ | ⟨a, _ | ⟨a', _ | ⟨a'', l⟩⟩⟩ <;> simp_all

/-- What `Cx.termG3` accepted of a 32-bit register test (`ZW`/`NZW`) or a bit test
(`TBZ`/`TBNZ`) with branch `asm` and inverse `inv` (`testBr`), from index `j`: two laid-out
successors, one control in register `r` (obj register `o`) of class `k`, and the branch to one
successor then the fall-through or `JMP` to the other. -/
structure TermOK3 (cx : Cx) (b : Block) (j : Nat) (next : Option (ID × Nat)) (asm inv : As) :
    Prop where
  succs : ∀ e ∈ b.succs.toList, e.b ∈ cx.lc.ctx.f.blocks.toList
  shape : ∃ e0 e1 c r o k, b.succs = #[e0, e1] ∧ b.controls = #[c] ∧
    cx.lc.home c = some (.reg r) ∧ objOf? r = some o ∧ cls (cx.lc.ty c) = some k ∧
    ((b.kind = .ARM64ZW ∨ b.kind = .ARM64NZW) → (32 ≤ k ∨ k = 1) ∧
      (TwoAt cx next j { as := asm, from_ := regA o } e0.b e1.b ∨
        TwoAt cx next j { as := inv, from_ := regA o } e1.b e0.b)) ∧
    ((b.kind = .ARM64TBZ ∨ b.kind = .ARM64TBNZ) → 0 ≤ b.auxInt.toInt ∧
      (b.auxInt.toInt < k ∨ k = 1) ∧
      (TwoAt cx next j { as := asm, from_ := constA b.auxInt.toInt, reg := o } e0.b e1.b ∨
        TwoAt cx next j { as := inv, from_ := constA b.auxInt.toInt, reg := o } e1.b e0.b))

/-- What `Cx.termG3` accepted: G2's terminators (`Cx.termG2_spec`) or a register or bit test. -/
theorem Cx.termG3_spec {cx : Cx} {b : Block} {j : Nat} {next : Option (ID × Nat)}
    (h : cx.termG3 b j next = .ok ()) :
    (testBr b.kind = none ∧ cx.termG2 b j next = .ok ()) ∨
    (∃ asm inv, testBr b.kind = some (asm, inv) ∧ TermOK3 cx b j next asm inv) := by
  unfold Cx.termG3 at h
  split at h
  next hk => exact Or.inl ⟨hk, h⟩
  next asm inv hk =>
    right
    refine ⟨asm, inv, hk, ?_⟩
    obtain ⟨hs, h⟩ := ex_guard h
    have hsucc : ∀ e ∈ b.succs.toList, e.b ∈ cx.lc.ctx.f.blocks.toList := by
      intro e he
      simp only [Array.all_eq_true_iff_forall_mem, Array.contains_iff_mem] at hs
      simpa using hs e (by simpa using he)
    refine ⟨hsucc, ?_⟩
    split at h
    next e0 he0 =>
      split at h
      next e1 he1 =>
        obtain ⟨hc, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        split at h
        next c hc0 =>
          split at h
          next r hr =>
            split at h
            next o ho =>
              split at h
              next k hkc =>
                refine ⟨e0, e1, c, r, o, k, arr_two3 hc.1 he0 he1, arr_one3 hc.2 hc0,
                  regHome?_eq.mp hr, ho, hkc, ?_⟩
                simp only at h
                split at h
                next hzw =>
                  obtain ⟨hw, h⟩ := ex_guard h
                  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hzw hw
                  refine ⟨fun _ => ⟨hw, ?_⟩, ?_⟩
                  · obtain ⟨sh, hsh, h⟩ := ex_bind_eq_ok h
                    simp only [ex_pure, Except.ok.injEq] at hsh
                    subst hsh
                    split at h
                    next heq => exact Or.inl (Cx.two_spec heq)
                    next => exact Or.inr (Cx.two_spec h)
                  · rintro (h1 | h1) <;> rcases hzw with h2 | h2 <;> rw [h1] at h2 <;> cases h2
                next hzw =>
                  obtain ⟨hw, h⟩ := ex_guard h
                  simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hzw
                  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
                    decide_eq_true_eq] at hw
                  refine ⟨?_, fun _ => ⟨hw.1, hw.2, ?_⟩⟩
                  · rintro (h1 | h1)
                    · exact absurd h1 hzw.1
                    · exact absurd h1 hzw.2
                  · obtain ⟨sh, hsh, h⟩ := ex_bind_eq_ok h
                    simp only [ex_pure, Except.ok.injEq] at hsh
                    subst hsh
                    split at h
                    next heq => exact Or.inl (Cx.two_spec heq)
                    next => exact Or.inr (Cx.two_spec h)
              next => simp [ex_throw] at h
            next => simp [ex_throw] at h
          next => simp [ex_throw] at h
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h

/-! ## Class maps -/

/-- Nothing is known at the entry. -/
theorem KMap.get_bot {r : Nat} : KMap.bot.get r = none := by
  unfold KMap.get KMap.bot
  by_cases hr : r < ARM64.registers.size
  · simp [hr]
  · simp [hr]

/-- The class map after one register is set (inside the map). -/
theorem KMap.get_set {K : KMap} {r r' : Nat} {x : Option Nat} :
    KMap.get (K.setIfInBounds r x) r' = if r' = r ∧ r < K.size then x else K.get r' := by
  unfold KMap.get
  rw [Array.getElem?_setIfInBounds]
  by_cases h1 : r = r'
  · subst h1
    by_cases h2 : r < K.size <;> simp [h2]
  · simp [h1, Ne.symm h1]

/-- Writing results keeps the size of the class map. -/
theorem kResults_size : ∀ {K : KMap} {rs : List (Ty × Option Nat)}, (kResults K rs).size = K.size
  | _, [] => rfl
  | K, (t, some r) :: rest => by
    rw [kResults, kResults_size, Array.size_setIfInBounds]
  | K, (_, none) :: rest => by rw [kResults, kResults_size]

/-- A register no result is written to keeps its class. -/
theorem kResults_get_of_not_mem : ∀ {K : KMap} {rs : List (Ty × Option Nat)} {r : Nat},
    (∀ t, (t, some r) ∉ rs) → (kResults K rs).get r = K.get r
  | _, [], _, _ => rfl
  | K, (t, some r0) :: rest, r, h => by
    rw [kResults, kResults_get_of_not_mem (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')),
      KMap.get_set]
    have : r ≠ r0 := fun he => h t (by simp [he])
    simp [this]
  | K, (_, none) :: rest, r, h => by
    rw [kResults, kResults_get_of_not_mem (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

/-- Result register `r` (of shape `t`, inside the map) gets the class of `t` when the result
registers are distinct. -/
theorem kResults_get_of_mem : ∀ {K : KMap} {rs : List (Ty × Option Nat)} {t : Ty} {r : Nat},
    (rs.filterMap (·.2)).Nodup → (t, some r) ∈ rs → r < K.size → (kResults K rs).get r = cls t
  | _, [], _, _, _, h, _ => nomatch h
  | K, (t0, some r0) :: rest, t, r, hnd, hm, hr => by
    simp only [List.filterMap_cons, List.nodup_cons] at hnd
    rw [kResults]
    rcases List.mem_cons.mp hm with he | he
    · simp only [Prod.mk.injEq, Option.some.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [kResults_get_of_not_mem, KMap.get_set]
      · simp [hr]
      · intro t' ht'
        exact hnd.1 (List.mem_filterMap.mpr ⟨_, ht', rfl⟩)
    · exact kResults_get_of_mem hnd.2 he (by rw [Array.size_setIfInBounds]; exact hr)
  | K, (_, none) :: rest, t, r, hnd, hm, hr => by
    simp only [List.filterMap_cons] at hnd
    rw [kResults]
    rcases List.mem_cons.mp hm with he | he
    · simp at he
    · exact kResults_get_of_mem hnd he hr

/-- The class map after `v`: unchanged by a `Phi`; else the class of `v` in its register home
(not `ZERO`, inside the map), the results of a `results` or `pair` home (`kResults`), and
nothing otherwise. -/
theorem kStep_get {lc : LocCtx} {K : KMap} {v : Value} {r : Nat} :
    (kStep lc K v).get r =
      if v.op = .Phi then K.get r else
      match lc.home v.id with
      | some (.reg r0) =>
        if r0 ≠ zeroReg ∧ r = r0 ∧ r0 < K.size then cls (lc.ty v.id) else K.get r
      | some (.results rs) => (kResults K ((tupleTys (lc.ty v.id)).zip rs.toList)).get r
      | some (.pair a b) => (kResults K ((tupleTys (lc.ty v.id)).zip [a, b])).get r
      | _ => K.get r := by
  unfold kStep
  by_cases hp : v.op = .Phi
  · simp [hp]
  · simp only [hp, beq_iff_eq, ↓reduceIte]
    rcases hh : lc.home v.id with _ | (r0 | k | ⟨a, b⟩ | rs)
    · rfl
    · by_cases hz : r0 = zeroReg
      · simp [hz]
      · simp [hz, KMap.get_set]
    · rfl
    · rfl
    · rfl

/-- A `Phi` writes no register. -/
theorem kStep_phi {lc : LocCtx} {K : KMap} {v : Value} (h : v.op = .Phi) : kStep lc K v = K := by
  simp [kStep, h]

/-- A value without register, `results` or `pair` home writes no register. -/
theorem kStep_none {lc : LocCtx} {K : KMap} {v : Value} (hr : ∀ r, lc.home v.id ≠ some (.reg r))
    (hrs : ∀ rs, lc.home v.id ≠ some (.results rs)) (hp : ∀ a b, lc.home v.id ≠ some (.pair a b)) :
    kStep lc K v = K := by
  unfold kStep
  split
  · rfl
  · split
    next r0 hh => exact absurd hh (hr r0)
    next rs hh => exact absurd hh (hrs rs)
    next a b hh => exact absurd hh (hp a b)
    next => rfl

/-- One step keeps the size of the class map. -/
theorem kStep_size {lc : LocCtx} {K : KMap} {v : Value} : (kStep lc K v).size = K.size := by
  unfold kStep
  split
  · rfl
  · split
    · split
      · rfl
      · exact Array.size_setIfInBounds
    · exact kResults_size
    · exact kResults_size
    · rfl

/-- The class map at the start of a block. -/
theorem kAt_zero {lc : LocCtx} {kt : KTab} {bid : ID} {b : Block} :
    kAt lc kt bid b 0 = kt.at bid := by
  simp [kAt, kSteps]

/-- The class map after value `i` of a block is one `kStep` past the map before it. -/
theorem kAt_succ {lc : LocCtx} {kt : KTab} {bid : ID} {b : Block} {i : Nat} {id : ID} {v : Value}
    (h1 : b.values[i]? = some id) (h2 : lc.ctx.f.value? id = some v) :
    kAt lc kt bid b (i + 1) = kStep lc (kAt lc kt bid b i) v := by
  have h1' : b.values.toList[i]? = some id := by simpa using h1
  simp only [kAt, kSteps, List.take_add_one, h1', Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil, h2]

/-! ## The class table -/

private theorem kSteps_cons {lc : LocCtx} {K : KMap} {id : ID} {ids : List ID} {v : Value}
    (hv : lc.ctx.f.value? id = some v) :
    kSteps lc K (id :: ids) = kSteps lc (kStep lc K v) ids := by
  simp only [kSteps, List.foldl_cons, hv]

/-- What `kOK` accepted: every read finds its class. -/
theorem kOK_spec {K : KMap} {rs : List (Nat × Nat)} (h : kOK K rs = true) :
    ∀ rc ∈ rs, K.get rc.1 = some rc.2 := by
  intro rc hrc
  have := List.all_eq_true.mp h rc hrc
  simpa using this

/-- What `kLe K' K` accepted: every class `K'` knows can be read from the class `K` knows. -/
theorem kLe_spec {K' K : KMap} (h : kLe K' K = true) :
    ∀ r c, K'.get r = some c → ∃ c', K.get r = some c' ∧ kNarrow c c' = true := by
  intro r c hr
  have hlt : r < K'.size := by
    refine Nat.lt_of_not_le fun hn => ?_
    simp [KMap.get, Array.getElem?_eq_none_iff.mpr hn] at hr
  have := List.all_eq_true.mp h r (List.mem_range.mpr hlt)
  rw [hr] at this
  simpa [Option.any_eq_true] using this

/-- What `kValues` accepted: its result is the map after the values (`kSteps`), and each value's
reads find their classes in the map before it. -/
theorem kValues_spec {lc : LocCtx} : ∀ {ids : List ID} {K K' : KMap}, kValues lc K ids = .ok K' →
    K' = kSteps lc K ids ∧ ∀ i id v, ids[i]? = some id → lc.ctx.f.value? id = some v →
      ∀ rc ∈ kReads lc v, (kSteps lc K (ids.take i)).get rc.1 = some rc.2
  | [], K, K', h => by
    simp only [kValues, ex_pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i id v hi => by simp at hi⟩
  | id :: ids, K, K', h => by
    simp only [kValues] at h
    cases hv : lc.ctx.f.value? id with
    | none => simp [hv, ex_throw] at h
    | some v =>
      simp only [hv] at h
      obtain ⟨hok, h⟩ := ex_guard h
      obtain ⟨ih1, ih2⟩ := kValues_spec h
      refine ⟨ih1.trans (kSteps_cons hv).symm, ?_⟩
      intro i id' v' hi hv'
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        rw [hv] at hv'
        cases hv'
        simpa [kSteps] using kOK_spec hok
      | succ i =>
        have := ih2 i id' v' (by simpa using hi) hv'
        rwa [List.take_succ_cons, kSteps_cons hv]

private theorem forIn_yield3 {α : Type} {l : List α}
    {f : α → PUnit → Except String (ForInStep PUnit)} {u : PUnit}
    (h : forIn l PUnit.unit f = .ok u) (hf : ∀ a, f a PUnit.unit ≠ .ok (.done PUnit.unit)) :
    ∀ a ∈ l, f a PUnit.unit = .ok (.yield PUnit.unit) := by
  induction l with
  | nil => intro a ha; cases ha
  | cons b l ih =>
    rw [List.forIn_cons] at h
    intro a ha
    cases hb : f b PUnit.unit with
    | error e =>
      rw [hb] at h
      cases (show (Except.error e : Except String PUnit) = .ok u from h)
    | ok s =>
      cases s with
      | done x => cases x; exact absurd hb (hf b)
      | yield x =>
        cases x
        rw [hb] at h
        have h : forIn l PUnit.unit f = .ok u := h
        cases ha with
        | head => exact hb
        | tail _ ha => exact ih h a ha

/-- What `checkK` accepted of the class table `kt`: nothing known at the entry; in each block of
the layout, every value's reads find their classes before it (`kAt`), the control's read finds
its class at the block's end, and every class at the start of each successor can be read from the
class at the end (`kNarrow`). -/
theorem checkK_spec {lc : LocCtx} {kt : KTab} (h : checkK lc kt = .ok ()) :
    kt.at lc.ctx.f.entry = KMap.bot ∧
    ∀ bid ∈ lc.ctx.f.blocks.toList, ∀ b, lc.ctx.f.block? bid = some b →
      (∀ i id v, b.values[i]? = some id → lc.ctx.f.value? id = some v →
        ∀ rc ∈ kReads lc v, (kAt lc kt bid b i).get rc.1 = some rc.2) ∧
      (∀ rc ∈ kControl lc b, (kAt lc kt bid b b.values.size).get rc.1 = some rc.2) ∧
      (∀ e ∈ b.succs.toList, ∀ r c, (kt.at e.b).get r = some c →
        ∃ c', (kAt lc kt bid b b.values.size).get r = some c' ∧ kNarrow c c' = true) := by
  unfold checkK at h
  obtain ⟨he, h⟩ := ex_guard h
  refine ⟨by simpa using he, ?_⟩
  simp only at h
  obtain ⟨u, hfor, -⟩ := ex_bind_eq_ok h
  have hall := forIn_yield3 hfor (by
    intro a hd
    split at hd
    · obtain ⟨K, -, hd⟩ := ex_bind_eq_ok hd
      split at hd
      · obtain ⟨_, -, hd⟩ := ex_bind_eq_ok hd
        cases hd
      · exact ex_throw_bind hd
    · exact ex_throw_bind hd)
  intro bid hbid b hb
  have h1 := hall bid hbid
  simp only [hb] at h1
  obtain ⟨K, hK, h1⟩ := ex_bind_eq_ok h1
  obtain ⟨hc, h1⟩ := ex_guard h1
  obtain ⟨_, hfor2, -⟩ := ex_bind_eq_ok h1
  rw [← Array.forIn_toList] at hfor2
  have hall2 := forIn_yield3 hfor2 (by
    intro a hd
    split at hd
    · cases hd
    · exact ex_throw_bind hd)
  obtain ⟨hK1, hK2⟩ := kValues_spec hK
  have hend : kAt lc kt bid b b.values.size = K := by
    rw [hK1, kAt, List.take_of_length_le (by simp)]
  refine ⟨fun i id v hi hv => hK2 i id v (by simpa using hi) hv, ?_, ?_⟩
  · rw [hend]
    exact kOK_spec hc
  · intro e he r c hr
    rw [hend]
    exact kLe_spec (ex_guard (hall2 e he)).1 r c hr

/-! ## The whole check -/

/-- What `checkG3` accepted: G2's facts with G3's value and terminator checks and homes, and the
returned class table passes `checkK`. -/
theorem checkG3_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG3 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind3 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK3 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG3 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  cases hf : List.find? (fun x => !homeOK3 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb⟩
    by_cases hi : i < lc.homes.size
    · have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
      simpa using this
    · have hh : lc.home i = none := by
        simp only [LocCtx.home]
        rw [getElem?_neg lc.homes i hi]
        rfl
      unfold homeOK3 homeOK2 homeOK
      rw [hh]

end GoFV.Gen.Check
