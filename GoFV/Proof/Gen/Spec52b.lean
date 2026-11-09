import GoFV.Gen.Check52b
import GoFV.Proof.Gen.Spec50

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `vkind52b` accepted (`GoFV/Gen/Check52b.lean`)

`VK52b`: the remainders of G52's group B (`MOD`, `UMOD`, `MODW`, `UMODW`) and the one Prog each
emits, `op Rm, Rn, Rd` with the arguments of at least the class `rem52b?` gives (`vkind52b_spec`).
`vkind52b` is `none` off `op52b` (`vkind52b_none`), and every `VK52b` value's op is one of `op52b`
(`vk52b_op`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind52b` accepted, and what it emits. -/
inductive VK52b (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- `MOD`, `UMOD`, `MODW`, `UMODW x y`: `op Rm, Rn, Rd`, `x` and `y` of at least `cw` bits. -/
  | rem {as : As} {cw cx cy c : Nat} {rn rm rd : Int} :
      rem52b? v.op = some (as, cw) → v.args.size = 2 → argObj lc v 0 = .ok (cx, rn) →
      argObj lc v 1 = .ok (cy, rm) → resObj lc v = .ok (c, rd) → 8 ≤ c → cw ≤ cx → cw ≤ cy →
      VK52b lc v (.prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }))

/-- What `vkind52b` accepted: no temporary, and `VK52b`. -/
theorem vkind52b_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (h : vkind52b lc v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK52b lc v kd := by
  unfold vkind52b at h
  cases hop : rem52b? v.op with
  | none => rw [hop] at h; cases h
  | some p =>
    obtain ⟨as, cw⟩ := p
    rw [hop] at h
    simp only [Option.map_some, Option.some.injEq] at h
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
    exact ⟨ht, .rem hop hsz hao hbo hro hw.1.1 hw.1.2 hw.2⟩

/-- Off the ops of G52's group B, `vkind52b` is `none`. -/
theorem vkind52b_none {lc : LocCtx} {v : Value} (h : op52b v.op = false) :
    vkind52b lc v = none := by
  simp only [op52b, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
  simp only [vkind52b, h, Option.map_none]

/-- A value `VK52b` accepted has an op of G52's group B. -/
theorem vk52b_op {lc : LocCtx} {v : Value} {kd : VKind2} (h : VK52b lc v kd) :
    op52b v.op = true := by
  cases h with
  | rem hop => simp only [op52b, hop, Option.isSome_some]

end GoFV.Gen.Check
