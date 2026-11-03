import GoFV.Proof.Low.SimBase

/-!
# Registers as lowered terms over the atoms (issue #385)

Phase 1's `DenOK` (`GoFV.Proof.AtomSimDen`) for `denL`: `DenOKL low D tabs fr V` says every
value of `V` has a register in `fr`, and for every valuation `ρ` that agrees with the registers
on the atoms of `V`, `denL low D tabs ρ n x` is the register of `x` for all large `n`
(`denOKL_terms`: kept by evaluating term nodes in dependency order).

`argTermRefL_apply` / `termStepRefL_apply` apply `ArgTermRefL` / `TermStepRefL` to the registers of a
source frame (mode `lowS`) and a target frame (mode `lowT`, `lowS → lowT`): the valuations are
the frames' atom registers; on an atom only the source holds, the target's valuation is the
source's register shaped at the target's shape (`rty_le`), which is the source's own shape there.
`stepTermL_eq_stepValsL`: the lowered terminator is `stepValsL` of the controls' registers;
`stepValsL_mono`: it is monotone in them (`Arm64.reg`, `Arm64.taken` read refined controls
alike).
-/

namespace GoFV.Proof.Low.Sim

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Proof.Low GoFV.Proof.Term GoFV.Proof.AtomSim
  GoFV.Opt.LowerCheck

/-! ## Terminators -/

private theorem reg_of {a b : Val} (h : Sem.Refines a b) {x : BitVec 64}
    (hx : Arm64.reg a = some x) : Arm64.reg b = some x := by
  cases h <;> simp_all [Arm64.reg]

private theorem reg32_of {a b : Val} (h : Sem.Refines a b) {x : BitVec 32}
    (hx : Arm64.reg32 a = some x) : Arm64.reg32 b = some x := by
  unfold Arm64.reg32 at *
  cases ha : Arm64.reg a with
  | none => rw [ha] at hx; cases hx
  | some y => rw [ha] at hx; rw [reg_of h ha]; exact hx

private theorem flagBit_cases {a b : Val} (h : Sem.Refines a b) :
    a.flagBit = none ∨ b.flagBit = a.flagBit := by
  cases h <;> simp [Val.flagBit]

private theorem eval_of {c : Cond} {n z cf v n' z' cf' v' : Option Bool} {r : Bool}
    (hn : n = none ∨ n' = n) (hz : z = none ∨ z' = z) (hc : cf = none ∨ cf' = cf)
    (hv : v = none ∨ v' = v) (h : c.eval n z cf v = some r) : c.eval n' z' cf' v' = some r := by
  rcases hn with rfl | rfl <;> rcases hz with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hv with rfl | rfl <;> cases c <;> simp_all [Cond.eval]

private theorem onVal_of {a b : Val} {c : Cond} {r : Bool} (h : Sem.Refines a b)
    (hr : c.onVal a = some r) : c.onVal b = some r := by
  cases h with
  | agg hl =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨_, _⟩⟩⟩⟩⟩
    all_goals first
      | (simp only [Cond.onVal] at hr; cases hr)
      | exact eval_of (flagBit_cases h1) (flagBit_cases h2) (flagBit_cases h3) (flagBit_cases h4) hr
  | _ => simp [Cond.onVal] at hr

private theorem isZero_of {a b : Val} (h : Sem.Refines a b) {r : Bool}
    (hr : Arm64.isZero a = some r) : Arm64.isZero b = some r := by
  cases h with
  | ptr => exact hr
  | poison => simp [Arm64.isZero, Arm64.reg] at hr
  | _ =>
    unfold Arm64.isZero at hr ⊢
    first
      | exact hr
      | (simp only at hr ⊢
         cases hx : Arm64.reg _ with
         | none => rw [hx] at hr; cases hr
         | some x => rw [hx] at hr; rw [reg_of (by assumption) hx]; exact hr)

private theorem noov_of {k : BlockKind} (hk : k = .ARM64LEnoov ∨ k = .ARM64GTnoov) {ai : Int64}
    {a b : Val} (h : Sem.Refines a b) {r : Bool} (hr : Arm64.taken k ai a = some r) :
    Arm64.taken k ai b = some r := by
  cases h with
  | agg hl =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨_, _⟩⟩⟩⟩⟩
    all_goals rcases hk with rfl | rfl
    all_goals first
      | (simp [Arm64.taken] at hr; done)
      | skip
    all_goals
      rcases flagBit_cases h1 with e1 | e1
      · simp [Arm64.taken, e1] at hr
      rcases flagBit_cases h2 with e2 | e2
      · simp [Arm64.taken, e2] at hr
      simp only [Arm64.taken, e1, e2] at hr ⊢; exact hr
  | _ => rcases hk with rfl | rfl <;> simp [Arm64.taken] at hr

private theorem map_of {α : Type} {o o' : Option α} (h : ∀ x, o = some x → o' = some x)
    {g : α → Bool} {r : Bool} (hr : o.map g = some r) : o'.map g = some r := by
  cases ho : o with
  | none => rw [ho] at hr; cases hr
  | some x => rw [ho] at hr; rw [h x ho]; exact hr

/-- `Arm64.taken` reads a refined control alike. -/
theorem taken_of {k : BlockKind} {ai : Int64} {a b : Val} (h : Sem.Refines a b) {r : Bool}
    (hr : Arm64.taken k ai a = some r) : Arm64.taken k ai b = some r := by
  cases k
  case ARM64LEnoov => exact noov_of (.inl rfl) h hr
  case ARM64GTnoov => exact noov_of (.inr rfl) h hr
  all_goals first
    | (cases hr; done)
    | exact onVal_of h hr
    | exact isZero_of h hr
    | exact map_of (fun x hx => isZero_of h hx) hr
    | exact map_of (fun x hx => reg32_of h hx) hr
    | exact map_of (fun x hx => reg_of h hx) hr

/-- With every control in a register, the lowered terminator is `stepValsL` of the registers. -/
theorem stepTermL_eq_stepValsL {fr : Frame} {b : Block} (h : ∀ c ∈ b.controls, Reg fr c) :
    stepTermL fr b = stepValsL b (b.controls.toList.map (rv fr)) := by
  unfold stepTermL stepValsL
  split
  · simp only [control_eq_ctlV h]
    cases b.kind <;> rfl
  · exact stepTerm_eq_stepVals h


/-- **`stepValsL` is monotone** in the controls. -/
theorem stepValsL_mono (b : Block) {cs cs' : List Val} (h : RefinesList cs cs') :
    Res.Rel Next.Refines (stepValsL b cs) (stepValsL b cs') := by
  unfold stepValsL
  split
  · have hc := ctlV_mono (b := b) (b' := b) rfl h 0
    split
    · refine Res.Rel.bind hc fun x y hxy => ?_
      cases hx : Arm64.reg x with
      | none => exact .stuck _ _
      | some k => rw [reg_of hxy hx]; exact succ_refl b _
    · refine Res.Rel.bind hc fun x y hxy => ?_
      cases hx : Arm64.taken _ b.auxInt x with
      | none => exact .stuck _ _
      | some r => rw [taken_of hxy hx]; cases r <;> exact succ_refl b _
  · exact stepVals_mono rfl rfl rfl h

/-! ## `DenOKL` -/

/-- The registers of `V` are the terms' values over the atoms' registers, in mode `low`. -/
def DenOKL (low : Bool) (D : ID → Option Value) (tabs : Tables) (fr : Frame) (V : ID → Prop) :
    Prop :=
  ∀ x, V x → Reg fr x ∧
    ∀ ρ : ID → Val, (∀ a, V a → ¬ IsTermL tabs D a → ρ a = rv fr a) →
      ∃ N, ∀ n, N ≤ n → denL low D tabs ρ n x = rv fr x

section
variable {low : Bool} {D : ID → Option Value} {tabs : Tables}

theorem denOKL_empty (low : Bool) (D : ID → Option Value) (tabs : Tables) (fr : Frame) :
    DenOKL low D tabs fr (fun _ => False) := fun _ h => h.elim

theorem DenOKL.iff {fr : Frame} {V W : ID → Prop} (h : DenOKL low D tabs fr V)
    (hVW : ∀ x, V x ↔ W x) : DenOKL low D tabs fr W := by
  intro x hx
  refine ⟨(h x ((hVW x).2 hx)).1, fun ρ hρ => ?_⟩
  exact (h x ((hVW x).2 hx)).2 ρ fun a ha hat => hρ a ((hVW a).1 ha) hat

theorem DenOKL.restrict {fr : Frame} {V W : ID → Prop} (h : DenOKL low D tabs fr V)
    (hWV : ∀ x, W x → V x) (hW : ClosedL tabs D W) : DenOKL low D tabs fr W := by
  classical
  intro x hx
  refine ⟨(h x (hWV x hx)).1, fun ρ hρ => ?_⟩
  let ρ2 : ID → Val := fun a => if V a ∧ ¬ IsTermL tabs D a then rv fr a else ρ a
  obtain ⟨N, hN⟩ := (h x (hWV x hx)).2 ρ2 (fun a ha hat => by simp [ρ2, ha, hat])
  refine ⟨N, fun n hn => ?_⟩
  rw [← hN n hn]
  exact denL_congr hW (fun a ha hat => by simp [ρ2, hWV a ha, hat, hρ a ha hat]) n x hx

/-- Adding atoms with registers, the registers of `V` unchanged. -/
theorem DenOKL.extend {fr fr' : Frame} {V W : ID → Prop} (h : DenOKL low D tabs fr V)
    (hk : ∀ a, V a → fr'.regs[a]? = fr.regs[a]?)
    (hW : ∀ x, W x → ¬ V x → ¬ IsTermL tabs D x ∧ Reg fr' x) :
    DenOKL low D tabs fr' (fun a => V a ∨ W a) := by
  intro x hx
  by_cases hv : V x
  · obtain ⟨⟨y, hy⟩, hd⟩ := h x hv
    refine ⟨⟨y, by rw [hk x hv]; exact hy⟩, fun ρ hρ => ?_⟩
    obtain ⟨N, hN⟩ := hd ρ (fun a ha hat => by rw [hρ a (.inl ha) hat]; unfold rv; rw [hk a ha])
    exact ⟨N, fun n hn => by rw [hN n hn]; unfold rv; rw [hk x hv]⟩
  · have hw : W x := hx.resolve_left hv
    obtain ⟨hat, hr⟩ := hW x hw hv
    refine ⟨hr, fun ρ hρ => ⟨1, fun n hn => ?_⟩⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [denL_succ_atom hat]; exact hρ x hx hat

theorem DenOKL.frame {fr fr' : Frame} {V : ID → Prop} (h : DenOKL low D tabs fr V)
    (hk : ∀ a, V a → fr'.regs[a]? = fr.regs[a]?) : DenOKL low D tabs fr' V :=
  (h.extend (W := fun _ => False) hk fun _ h => h.elim).iff fun _ =>
    ⟨fun h => h.elim id False.elim, fun h => Or.inl h⟩

theorem DenOKL.list {fr : Frame} {V : ID → Prop} (h : DenOKL low D tabs fr V) {ρ : ID → Val}
    (hρ : ∀ a, V a → ¬ IsTermL tabs D a → ρ a = rv fr a) :
    ∀ {l : List ID}, (∀ a ∈ l, V a) →
      ∃ N, ∀ n, N ≤ n → l.map (denL low D tabs ρ n) = l.map (rv fr)
  | [], _ => ⟨0, fun _ _ => rfl⟩
  | a :: l, hl => by
    obtain ⟨N1, h1⟩ := (h a (hl a List.mem_cons_self)).2 ρ hρ
    obtain ⟨N2, h2⟩ := DenOKL.list h hρ (l := l) fun b hb => hl b (List.mem_cons_of_mem _ hb)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    rw [List.map_cons, List.map_cons, h1 n (by omega), h2 n (by omega)]

/-- Adding a term node whose arguments are in `V`, with its value over their registers. -/
theorem DenOKL.term {fr fr' : Frame} {V : ID → Prop} {x : ID} {v : Value}
    (h : DenOKL low D tabs fr V) (hk : ∀ a, V a → fr'.regs[a]? = fr.regs[a]?)
    (hxV : ¬ V x) (hx : D x = some v) (ht : termVL tabs v = true) (hargs : ∀ a ∈ v.args, V a)
    (hreg : fr'.regs[x]? = some (some (rty low (shp low tabs v.type)
      (opValL tabs v.op (shp low tabs v.type) v.auxInt v.aux (v.args.toList.map (rv fr)))))) :
    DenOKL low D tabs fr' (fun a => V a ∨ a = x) := by
  intro z hz
  by_cases hv : V z
  · obtain ⟨⟨y, hy⟩, hd⟩ := h z hv
    refine ⟨⟨y, by rw [hk z hv]; exact hy⟩, fun ρ hρ => ?_⟩
    obtain ⟨N, hN⟩ := hd ρ (fun a ha hat => by rw [hρ a (.inl ha) hat]; unfold rv; rw [hk a ha])
    exact ⟨N, fun n hn => by rw [hN n hn]; unfold rv; rw [hk z hv]⟩
  · have hzx : z = x := hz.resolve_left hv
    subst hzx
    refine ⟨⟨_, hreg⟩, fun ρ hρ => ?_⟩
    have hρ' : ∀ a, V a → ¬ IsTermL tabs D a → ρ a = rv fr a := fun a ha hat => by
      rw [hρ a (.inl ha) hat]; unfold rv; rw [hk a ha]
    obtain ⟨N, hN⟩ := DenOKL.list h hρ' (l := v.args.toList)
      fun a ha => hargs a (Array.mem_toList_iff.1 ha)
    refine ⟨N + 1, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [denL_succ_term hx ht, hN k (by omega), rv_of hreg]

/-- Term nodes listed after their arguments, with their values over the registers. -/
def TermsOKL (low : Bool) (D : ID → Option Value) (tabs : Tables) (fr : Frame) :
    (ID → Prop) → List ID → Prop
  | _, [] => True
  | V, x :: s => Reg fr x ∧
      (∀ v, D x = some v → termVL tabs v = true → (∀ a ∈ v.args, V a) ∧
        fr.regs[x]? = some (some (rty low (shp low tabs v.type)
          (opValL tabs v.op (shp low tabs v.type) v.auxInt v.aux (v.args.toList.map (rv fr)))))) ∧
      TermsOKL low D tabs fr (fun a => V a ∨ a = x) s

theorem denOKL_terms {fr : Frame} :
    ∀ {L : List ID} {V : ID → Prop}, DenOKL low D tabs fr V → TermsOKL low D tabs fr V L →
      DenOKL low D tabs fr (fun a => V a ∨ a ∈ L)
  | [], V, h, _ => h.iff fun a => ⟨.inl, fun h => h.elim id fun h => absurd h List.not_mem_nil⟩
  | x :: s, V, h, ⟨hreg, hterm, hs⟩ => by
    have h1 : DenOKL low D tabs fr (fun a => V a ∨ a = x) := by
      by_cases hxV : V x
      · exact h.iff fun a => ⟨.inl, fun h => h.elim id fun he => he ▸ hxV⟩
      · by_cases ht : IsTermL tabs D x
        · obtain ⟨v, hv, hop⟩ := ht
          obtain ⟨hargs, hr⟩ := hterm v hv hop
          exact h.term (fun _ _ => rfl) hxV hv hop hargs hr
        · exact h.extend (W := fun a => a = x) (fun _ _ => rfl) fun a ha _ => ha ▸ ⟨ht, hreg⟩
    exact (denOKL_terms h1 hs).iff fun a => by simp only [List.mem_cons, or_assoc]

end

/-! ## Term values of a lowered frame -/

/-- A term value evaluates by `opValL` at its shape, shaped (`evalOpL_termVL`). -/
theorem evalValueL_termL {low : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (ht : termVL ctx.tabs v = true) (h : evalValueL ⟨low, false⟩ env ctx fr v = .ok y) :
    y = rty low (ctx.tys[v.id]?.getD .other) (opValL ctx.tabs v.op (ctx.tys[v.id]?.getD .other)
      v.auxInt v.aux (v.args.toList.map (rv fr))) := by
  rw [evalValueL_of_regs (regsL_of_ok h)] at h
  change ((evalOpL false env ctx fr v _ _).bind _) = _ at h
  rw [evalOpL_termVL ht] at h
  cases h; rfl

theorem evalValueL_termL_eq {low : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (ht : termVL ctx.tabs v = true) (hreg : ∀ a ∈ v.args, Reg fr a) :
    evalValueL ⟨low, false⟩ env ctx fr v = .ok (rty low (ctx.tys[v.id]?.getD .other)
      (opValL ctx.tabs v.op (ctx.tys[v.id]?.getD .other) v.auxInt v.aux
        (v.args.toList.map (rv fr)))) := by
  rw [evalValueL_of_regs hreg]
  change ((evalOpL false env ctx fr v _ _).bind _) = _
  rw [evalOpL_termVL ht]; rfl

/-! ## Applying the term relations to frames -/

section
variable {lowS lowT : Bool} (hl : lowS = true → lowT = true) {D E : ID → Option Value}
  {tabs : Tables} {FS FT : Frame} {VS VT : ID → Prop}
  (hS : DenOKL lowS D tabs FS VS) (hG : DenOKL lowT E tabs FT VT)
  (hrel : ∀ a, VS a → ¬ IsTermL tabs D a → VT a → ¬ IsTermL tabs E a →
    Sem.Refines (rv FS a) (rv FT a))
  (htyS : ∀ a, VS a → ¬ IsTermL tabs D a → rty lowS (shapeL lowS D tabs a) (rv FS a) = rv FS a)
  (htyT : ∀ a, VT a → ¬ IsTermL tabs E a → rty lowT (shapeL lowT E tabs a) (rv FT a) = rv FT a)
  (hsh : ∀ a, VS a → ¬ IsTermL tabs D a → ¬ IsTermL tabs E a → (E a).isSome → ¬ VT a →
    shapeL lowT E tabs a = shapeL lowS D tabs a)
include hl hS hG hrel htyS htyT hsh

/-- The valuations of the frames' atoms, refined and typed. -/
private theorem vals_exist : ∃ ρ ρ' : ID → Val, ValRef ρ ρ' ∧ TypedL lowS D tabs ρ ∧
    TypedL lowT E tabs ρ' ∧ (∀ a, VS a → ¬ IsTermL tabs D a → ρ a = rv FS a) ∧
    (∀ a, VT a → ¬ IsTermL tabs E a → ρ' a = rv FT a) := by
  classical
  let ρ : ID → Val := fun a => if VS a ∧ ¬ IsTermL tabs D a then rv FS a else .poison
  let ρ' : ID → Val := fun a =>
    if VT a ∧ ¬ IsTermL tabs E a then rv FT a
    else if ¬ IsTermL tabs E a ∧ (E a).isSome then rty lowT (shapeL lowT E tabs a) (ρ a)
    else ρ a
  refine ⟨ρ, ρ', fun a => ?_, fun a hat _ => ?_, fun a hat hdef => ?_,
    fun a ha hat => by simp [ρ, ha, hat], fun a ha hat => by simp [ρ', ha, hat]⟩
  · by_cases h1 : VT a ∧ ¬ IsTermL tabs E a
    · by_cases h2 : VS a ∧ ¬ IsTermL tabs D a
      · simp only [ρ', ρ, h1, h2, and_self, ite_true]
        exact hrel a h2.1 h2.2 h1.1 h1.2
      · simp only [ρ', ρ, h1, h2, and_self, ite_true, ite_false]
        exact .poison _
    · by_cases h3 : ¬ IsTermL tabs E a ∧ (E a).isSome
      · show Sem.Refines (ρ a) (if VT a ∧ ¬ IsTermL tabs E a then rv FT a
          else if ¬ IsTermL tabs E a ∧ (E a).isSome then rty lowT (shapeL lowT E tabs a) (ρ a)
          else ρ a)
        rw [if_neg h1, if_pos h3]
        by_cases h2 : VS a ∧ ¬ IsTermL tabs D a
        · have hρa : ρ a = rv FS a := if_pos h2
          rw [hρa]
          have hnv : ¬ VT a := fun hv => h1 ⟨hv, h3.1⟩
          conv => lhs; rw [← htyS a h2.1 h2.2]
          rw [hsh a h2.1 h2.2 h3.1 h3.2 hnv]
          exact rty_le hl _ (Sem.Refines.refl _)
        · have hρa : ρ a = .poison := if_neg h2
          rw [hρa]; exact .poison _
      · simp only [ρ', h1, h3, ite_false]; exact Sem.Refines.refl _
  · by_cases h2 : VS a
    · simp only [ρ, h2, hat, not_false_eq_true, and_self, ite_true]; exact htyS a h2 hat
    · simp only [ρ, h2, false_and, ite_false]; exact rty_poison _ _
  · by_cases h1 : VT a
    · simp only [ρ', h1, hat, not_false_eq_true, and_self, ite_true]; exact htyT a h1 hat
    · have h3 : ¬ IsTermL tabs E a ∧ (E a).isSome := ⟨hat, hdef⟩
      simp only [ρ', h1, h3, false_and, and_self, ite_true, ite_false]
      exact rty_idem _ _ _

/-- **`ArgTermRefL` on registers.** -/
theorem argTermRefL_apply {o : Option Int64} {x y : ID}
    (hT : ArgTermRefL o lowS D tabs x lowT E tabs y) (hxS : VS x) (hyT : VT y) :
    ArgRel o (rv FS x) (rv FT y) := by
  obtain ⟨ρ, ρ', hval, htD, htE, hρ, hρ'⟩ := vals_exist hl hS hG hrel htyS htyT hsh
  obtain ⟨N, hN⟩ := (hS x hxS).2 ρ hρ
  obtain ⟨M, hM⟩ := (hG y hyT).2 ρ' hρ'
  obtain ⟨m, h⟩ := hT N
  have h := h ρ ρ' hval htD htE
  rw [hN N (Nat.le_refl N)] at h
  rw [← hM (max m M) (Nat.le_max_right m M)]
  exact h.trans_right (denL_fuel_mono lowT E tabs ρ' m (max m M) y (Nat.le_max_left m M))

/-- **The terminators on registers**, as functions of their controls' terms. -/
theorem termStepRefL_apply {fb gb : Block}
    (hT : ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → TypedL lowS D tabs ρ → TypedL lowT E tabs ρ' →
      Res.Rel Next.Refines (stepValsL fb (fb.controls.toList.map (denL lowS D tabs ρ n)))
        (stepValsL gb (gb.controls.toList.map (denL lowT E tabs ρ' m))))
    (hxS : ∀ c ∈ fb.controls, VS c) (hyT : ∀ c ∈ gb.controls, VT c) :
    Res.Rel Next.Refines (stepTermL FS fb) (stepTermL FT gb) := by
  obtain ⟨ρ, ρ', hval, htD, htE, hρ, hρ'⟩ := vals_exist hl hS hG hrel htyS htyT hsh
  obtain ⟨N, hN⟩ := hS.list hρ (l := fb.controls.toList)
    fun a ha => hxS a (Array.mem_toList_iff.1 ha)
  obtain ⟨M, hM⟩ := hG.list hρ' (l := gb.controls.toList)
    fun a ha => hyT a (Array.mem_toList_iff.1 ha)
  obtain ⟨m, h⟩ := hT N
  have h := h ρ ρ' hval htD htE
  rw [hN N (Nat.le_refl N)] at h
  have h2 := Res.Rel.trans_next h (stepValsL_mono gb (RefinesList.map _ _
    (fun c => denL_fuel_mono lowT E tabs ρ' m (max m M) c (Nat.le_max_left m M)) gb.controls.toList))
  rw [hM (max m M) (Nat.le_max_right m M)] at h2
  rw [stepTermL_eq_stepValsL (fun c hc => (hS c (hxS c hc)).1),
    stepTermL_eq_stepValsL (fun c hc => (hG c (hyT c hc)).1)]
  exact h2

end

end GoFV.Proof.Low.Sim
