import GoFV.Gen.Check
import GoFV.Proof.Gen.Rel

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G1 accepted (`docs/plans/proofs3.md` §3)

`checkG1 lc ps bstart = .ok tab` unfolded into the facts the soundness proof uses: the function
is lowered, every home is one G1 handles (`homeOK`), the Prog IDs are distinct and below `2^32`,
and for every block of the layout its row of `tab` lists the index in `ps` where each value's
Progs start (`Cx.values_spec`: each value's kind, `VK`, and the Progs between consecutive
indices, `VStep`) and where its terminator's start, whose Progs have the shapes of `TermOK`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-! ## `Except` helpers -/

theorem ex_pure {α : Type} (x : α) : (pure x : Except String α) = .ok x := rfl
theorem ex_throw {α : Type} (s : String) : (throw s : Except String α) = .error s := rfl
theorem ex_bind_error {α β : Type} (e : String) (f : α → Except String β) :
    (Except.error e >>= f) = .error e := rfl

theorem ex_bind_eq_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp only [ex_bind_error, reduceCtorEq] at h
  | ok a => exact ⟨a, rfl, h⟩

theorem ex_guard {α β : Type} {c : Prop} [Decidable c] {A : Except String α} {s : String}
    {f : β → Except String α} {x : α}
    (h : (if c then A else (throw s >>= f)) = .ok x) : c ∧ A = .ok x := by
  split at h
  next hc => exact ⟨hc, h⟩
  next => simp only [ex_throw, ex_bind_error, reduceCtorEq] at h

private theorem forIn_yield {α : Type} {l : List α} {f : α → PUnit → Except String (ForInStep PUnit)}
    {u : PUnit} (h : forIn l PUnit.unit f = .ok u)
    (hf : ∀ a, f a PUnit.unit ≠ .ok (.done PUnit.unit)) :
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

theorem ex_throw_bind {α β : Type} {s : String} {f : α → Except String β} {b : β}
    (h : (throw s >>= f) = .ok b) : False := by
  simp only [ex_throw, ex_bind_error, reduceCtorEq] at h

private theorem arr_one {α : Type} {xs : Array α} {e : α} (hs : xs.size = 1) (h0 : xs[0]? = some e) :
    xs = #[e] := by
  rcases xs with ⟨l⟩
  rcases l with _ | ⟨a, _ | ⟨a', l⟩⟩ <;> simp_all

private theorem arr_two {α : Type} {xs : Array α} {e0 e1 : α} (hs : xs.size = 2)
    (h0 : xs[0]? = some e0) (h1 : xs[1]? = some e1) : xs = #[e0, e1] := by
  rcases xs with ⟨l⟩
  rcases l with _ | ⟨a, _ | ⟨a', _ | ⟨a'', l⟩⟩⟩ <;> simp_all

theorem skipFrom_spec (ps : Array Prog) : ∀ (fuel j : Nat), j ≤ skipFrom ps j fuel ∧
    ∀ l (hl : l < ps.size), j ≤ l → l < skipFrom ps j fuel → noop ps[l] = true
  | 0, j => ⟨Nat.le_refl _, fun l _ h1 h2 => absurd h2 (by simp only [skipFrom]; omega)⟩
  | fuel + 1, j => by
    unfold skipFrom
    cases hp : ps[j]? with
    | none => dsimp only; exact ⟨Nat.le_refl _, fun l _ h1 h2 => absurd h2 (by omega)⟩
    | some p =>
      simp only
      split
      next hn =>
        obtain ⟨h1, h2⟩ := skipFrom_spec ps fuel (j + 1)
        refine ⟨by omega, fun l hl hjl hlk => ?_⟩
        by_cases hlj : l = j
        · subst hlj
          obtain ⟨_, hk'⟩ := Array.getElem?_eq_some_iff.mp hp
          rw [hk']; exact hn
        · exact h2 l hl (by omega) hlk
      next => exact ⟨Nat.le_refl _, fun l _ h1 h2 => absurd h2 (by omega)⟩

/-! ## Operands -/

theorem regHome?_eq {lc : LocCtx} {a r : Nat} : regHome? lc a = some r ↔ lc.home a = some (.reg r) := by
  unfold regHome?
  split <;> simp_all

theorem argObj_spec {lc : LocCtx} {v : Value} {i c : Nat} {o : Int} (h : argObj lc v i = .ok (c, o)) :
    ∃ a r, v.args[i]? = some a ∧ lc.home a = some (.reg r) ∧ objOf? r = some o ∧ cls (lc.ty a) = some c := by
  unfold argObj at h
  cases ha : v.args[i]? with
  | none => simp [ha, ex_throw] at h
  | some a =>
    cases hr : regHome? lc a with
    | none => simp [ha, hr, ex_throw] at h
    | some r =>
      cases ho : objOf? r with
      | none => simp [ha, hr, ho, ex_throw] at h
      | some o' =>
        cases hc : cls (lc.ty a) with
        | none => simp [ha, hr, ho, hc, ex_throw] at h
        | some c' =>
          simp only [ha, hr, ho, hc, ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨a, r, rfl, regHome?_eq.mp hr, ho, hc⟩

theorem resObj_spec {lc : LocCtx} {v : Value} {c : Nat} {o : Int} (h : resObj lc v = .ok (c, o)) :
    ∃ r, lc.home v.id = some (.reg r) ∧ destOK r = true ∧ objOf? r = some o ∧
      cls (lc.ty v.id) = some c := by
  unfold resObj at h
  cases hr : regHome? lc v.id with
  | none => simp [hr, ex_throw] at h
  | some r =>
    cases hd : destOK r with
    | false => simp [hr, hd, ex_throw, ex_bind_error] at h
    | true =>
      cases ho : objOf? r with
      | none => simp [hr, hd, ho, ex_throw] at h
      | some o' =>
        cases hc : cls (lc.ty v.id) with
        | none => simp [hr, hd, ho, hc, ex_throw] at h
        | some c' =>
          simp only [hr, hd, ho, hc, ex_pure, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨r, regHome?_eq.mp hr, hd, ho, rfl⟩

theorem memArg_spec {lc : LocCtx} {v : Value} {i : Nat} (h : memArg lc v i = .ok ()) :
    ∃ a, v.args[i]? = some a ∧ memTy (lc.ty a) = true ∧ lc.home a = none := by
  unfold memArg at h
  cases ha : v.args[i]? with
  | none => simp [ha, ex_throw] at h
  | some a =>
    by_cases hm : memTy (lc.ty a) = true ∧ lc.home a = none
    · exact ⟨a, rfl, hm⟩
    · simp [ha, hm, ex_throw] at h

/-- An obj register of a Go register: `REG_R0 + k` with `k = 31` (`ZR`) for `ZERO`, else the X
register `k < 31` of `objX?`. -/
theorem objOf?_some {r : Nat} {o : Int} (h : objOf? r = some o) :
    ∃ k : Nat, k < 32 ∧ o = ARM64.REG_R0 + k ∧
      ((r = zeroReg ∧ k = 31) ∨ (k < 31 ∧ objX? r = some (BitVec.ofNat 5 k))) := by
  unfold objOf? at h
  have h0 : ARM64.REG_R0 = 8192 := rfl
  by_cases hz : r = zeroReg
  · simp only [hz, ↓reduceIte, Option.some.injEq] at h
    refine ⟨31, by omega, ?_, Or.inl ⟨hz, rfl⟩⟩
    rw [← h, h0]; rfl
  · simp only [hz, ↓reduceIte, Option.map_eq_some_iff] at h
    obtain ⟨kk, hkk, he⟩ := h
    refine ⟨kk.toNat, by omega, he.symm, Or.inr ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := GoFV.Proof.Gen.objX?_some hkk
      split at h2 <;> (try split at h2) <;> omega
    · rw [hkk]; simp

/-! ## Values -/

/-- What `vkind` accepted of a value that is not an entry value, and what it emits. -/
inductive VK (lc : LocCtx) (v : Value) : VKind → Prop
  | phi : v.op = .Phi → v.args.all (lc.home · == lc.home v.id) = true → VK lc v .none
  | zero : v.op = .ARM64ZERO → v.args.size = 0 → lc.home v.id = some (.reg zeroReg) →
      (cls (lc.ty v.id)).isSome = true → VK lc v .none
  | inl : v.op = .InlMark → lc.home v.id = none → inertTy (lc.ty v.id) = true → VK lc v .none
  | copyMem : v.op = .Copy → memTy (lc.ty v.id) = true → v.args.size = 1 → memArg lc v 0 = .ok () →
      lc.home v.id = none → VK lc v .none
  | copySame {c : Nat} {r : Int} : v.op = .Copy → memTy (lc.ty v.id) = false → v.args.size = 1 →
      argObj lc v 0 = .ok (c, r) → resObj lc v = .ok (c, r) → VK lc v .none
  | copyMov {c : Nat} {ra rd : Int} : v.op = .Copy → memTy (lc.ty v.id) = false →
      v.args.size = 1 → argObj lc v 0 = .ok (c, ra) → resObj lc v = .ok (c, rd) → ra ≠ rd →
      VK lc v (.prog { as := .MOVD, from_ := regA ra, to := regA rd })
  | result : v.op = .MakeResult → (lc.home v.id = none ∨ lc.home v.id = some (.results #[])) →
      resultsTy lc v.args (lc.ty v.id) = true →
      (∀ a ∈ v.args.toList, memTy (lc.ty a) = true → lc.home a = none) →
      (∀ a ∈ v.args.toList, memTy (lc.ty a) = false →
        (regHome? lc a).isSome = true ∧ (cls (lc.ty a)).isSome = true) →
      VK lc v .none
  | movConst {c : Nat} {rd : Int} : v.op = .ARM64MOVDconst → v.args.size = 0 →
      resObj lc v = .ok (c, rd) → (c = 1 → v.auxInt = 0 ∨ v.auxInt = 1) →
      VK lc v (.prog { as := .MOVD, from_ := constA v.auxInt.toInt, to := regA rd })
  | alu {c ca cb : Nat} {rn rm rd : Int} {as : As} :
      (v.op = .ARM64ADD ∧ as = .ADD ∨ v.op = .ARM64SUB ∧ as = .SUB) → v.args.size = 2 →
      argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) →
      8 ≤ c → c ≤ ca → c ≤ cb →
      VK lc v (.prog { as, from_ := regA rm, reg := rn, to := regA rd })
  | aluK {c ca : Nat} {rn rd : Int} {as : As} :
      (v.op = .ARM64ADDconst ∧ as = .ADD ∨ v.op = .ARM64SUBconst ∧ as = .SUB) → v.args.size = 1 →
      argObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) → 8 ≤ c → c ≤ ca →
      VK lc v (.prog { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd })
  | cmp {rn rm : Int} : v.op = .ARM64CMP → v.args.size = 2 → (lc.ty v.id).isFlags = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rn) → argObj lc v 1 = .ok (64, rm) →
      VK lc v (.prog { as := .CMP, from_ := regA rm, reg := rn })
  | cmpK {rn : Int} : v.op = .ARM64CMPconst → v.args.size = 1 → (lc.ty v.id).isFlags = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rn) →
      VK lc v (.prog { as := .CMP, from_ := constA v.auxInt.toInt, reg := rn })
  | load {c : Nat} {rn rd : Int} : v.op = .ARM64MOVDload → v.args.size = 2 → v.aux = none →
      argObj lc v 0 = .ok (64, rn) → memArg lc v 1 = .ok () → resObj lc v = .ok (c, rd) → 8 ≤ c →
      VK lc v (.prog { as := .MOVD, from_ := memA rn v.auxInt.toInt, to := regA rd })
  | store {cs : Nat} {rn rs : Int} : v.op = .ARM64MOVDstore → v.args.size = 3 → v.aux = none →
      memTy (lc.ty v.id) = true → lc.home v.id = none → argObj lc v 0 = .ok (64, rn) →
      argObj lc v 1 = .ok (cs, rs) → memArg lc v 2 = .ok () → (cs = 64 ∨ cs = 1) →
      VK lc v (.prog { as := .MOVD, from_ := regA rs, to := memA rn v.auxInt.toInt })

/-- What `vkind` accepted of a value that is not an entry value: no temporary, and `VK`. -/
theorem vkind_spec {lc : LocCtx} {v : Value} {kd : VKind} (h : vkind lc v = .ok kd)
    (hen : entryOp v.op = false) : (lc.temps[v.id]?).join = none ∧ VK lc v kd := by
  have ht : (lc.temps[v.id]?).join = none := by
    by_cases ht : (lc.temps[v.id]?).join = none
    · exact ht
    · unfold vkind at h
      simp [ht, ex_throw, ex_bind_error] at h
  refine ⟨ht, ?_⟩
  unfold vkind at h
  simp only [ht, hen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ex_pure] at h
  split at h
  next _ hop =>
    obtain ⟨hc, h⟩ := ex_guard h
    cases h
    exact VK.phi hop hc
  next _ hop =>
    obtain ⟨hc, h⟩ := ex_guard h
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact VK.zero hop hc.1.1 (regHome?_eq.mp hc.1.2) hc.2
  next _ hop =>
    obtain ⟨hc, h⟩ := ex_guard h
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact VK.inl hop hc.1 hc.2
  next _ hop =>
    split at h
    next hm =>
      obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
      obtain ⟨hc, h⟩ := ex_guard h
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact VK.copyMem hop hm hc.1 hma hc.2
    next hm =>
      obtain ⟨hsz, h⟩ := ex_guard h
      obtain ⟨⟨ca, ra⟩, ha, h⟩ := ex_bind_eq_ok h
      obtain ⟨⟨cd, rd⟩, hr, h⟩ := ex_bind_eq_ok h
      obtain ⟨hcc, h⟩ := ex_guard h
      simp only [beq_iff_eq] at hsz hcc
      subst hcc
      have hm' : memTy (lc.ty v.id) = false := by simpa using hm
      split at h
      next hrr =>
        cases h
        simp only [beq_iff_eq] at hrr
        subst hrr
        exact VK.copySame hop hm' hsz ha hr
      next hrr =>
        cases h
        simp only [beq_iff_eq] at hrr
        exact VK.copyMov hop hm' hsz ha hr hrr
  next _ hop =>
    obtain ⟨hh, h⟩ := ex_guard h
    obtain ⟨hrt, h⟩ := ex_guard h
    obtain ⟨u, hfor, h⟩ := ex_bind_eq_ok h
    cases h
    rw [← Array.forIn_toList] at hfor
    have hall := forIn_yield hfor (by
      intro a
      split
      · split <;> simp [ex_throw, ex_bind_error]
      · split <;> simp [ex_throw, ex_bind_error])
    simp only [Bool.or_eq_true, beq_iff_eq] at hh
    refine VK.result hop hh hrt ?_ ?_
    · intro a ha hm
      have h1 := hall a ha
      simp only [hm, ↓reduceIte] at h1
      have h2 := (ex_guard h1).1
      simpa using h2
    · intro a ha hm
      have h1 := hall a ha
      simp only [hm, Bool.false_eq_true, ↓reduceIte] at h1
      have h2 := (ex_guard h1).1
      simpa only [Bool.and_eq_true] using h2
  next _ hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
    split at h
    next => simp only [ex_throw, ex_bind_error, reduceCtorEq] at h
    next hb =>
      cases h
      simp only [beq_iff_eq] at hsz
      refine VK.movConst hop hsz hr ?_
      intro hc1
      subst hc1
      by_cases h0 : v.auxInt = 0
      · exact Or.inl h0
      · exact Or.inr (by simpa [h0] using hb)
  next _ hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨cb, rm⟩, hb, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    cases h
    simp only [beq_iff_eq] at hsz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [hop, beq_self_eq_true, ↓reduceIte]
    exact VK.alu (Or.inl ⟨hop, rfl⟩) hsz ha hb hr hw.1.1 hw.1.2 hw.2
  next _ hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨cb, rm⟩, hb, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    cases h
    simp only [beq_iff_eq] at hsz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [hop, beq_iff_eq, reduceCtorEq, ↓reduceIte]
    exact VK.alu (Or.inr ⟨hop, rfl⟩) hsz ha hb hr hw.1.1 hw.1.2 hw.2
  next _ hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    cases h
    simp only [beq_iff_eq] at hsz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [hop, beq_self_eq_true, ↓reduceIte]
    exact VK.aluK (Or.inl ⟨hop, rfl⟩) hsz ha hr hw.1 hw.2
  next _ hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    cases h
    simp only [beq_iff_eq] at hsz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [hop, beq_iff_eq, reduceCtorEq, ↓reduceIte]
    exact VK.aluK (Or.inr ⟨hop, rfl⟩) hsz ha hr hw.1 hw.2
  next _ hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨cb, rm⟩, hb, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsz hw
    obtain ⟨rfl, rfl⟩ := hw
    exact VK.cmp hop hsz.1.1 hsz.1.2 hsz.2 ha hb
  next _ hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsz hw
    subst hw
    exact VK.cmpK hop hsz.1.1 hsz.1.2 hsz.2 ha
  next _ hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hm, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨c, rd⟩, hr, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsz hw
    obtain ⟨rfl, hc⟩ := hw
    exact VK.load hop hsz.1 hsz.2 ha hm hr hc
  next _ hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨cs, rs⟩, hb, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hm, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    cases h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hsz hw
    obtain ⟨rfl, hcs⟩ := hw
    exact VK.store hop hsz.1.1.1 hsz.1.1.2 hsz.1.2 hsz.2 ha hb hm hcs
  next => simp only [ex_throw, reduceCtorEq] at h

/-! ## Prog positions -/

/-- From index `j`, after no-ops, the Prog at index `j' - 1` has shape `sh`. -/
def OneAt (ps : Array Prog) (j : Nat) (sh : Shape) (j' : Nat) : Prop :=
  ∃ k, j ≤ k ∧ j' = k + 1 ∧ ∃ hk : k < ps.size, sh.ok ps[k] = true ∧
    ∀ l (hl : l < ps.size), j ≤ l → l < k → noop ps[l] = true

theorem Cx.one_spec {cx : Cx} {j j' : Nat} {sh : Shape} (h : cx.one j sh = .ok j') :
    OneAt cx.ps j sh j' := by
  unfold Cx.one at h
  simp only at h
  cases hp : cx.ps[skipFrom cx.ps j cx.ps.size]? with
  | none => simp [hp, ex_throw] at h
  | some p =>
    simp only [hp] at h
    obtain ⟨hs, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hk, hk'⟩ := Array.getElem?_eq_some_iff.mp hp
    obtain ⟨h1, h2⟩ := skipFrom_spec cx.ps cx.ps.size j
    exact ⟨_, h1, rfl, hk, hk' ▸ hs, h2⟩

theorem Cx.startIdx_spec {cx : Cx} {b : ID} {j : Nat} (h : cx.startIdx b = .ok j) :
    ∃ id, cx.bstart b = some id ∧ ∃ hj : j < cx.ps.size, cx.ps[j].id = id := by
  unfold Cx.startIdx at h
  cases hb : cx.bstart b with
  | none => simp [hb, ex_throw] at h
  | some id =>
    cases hi : cx.idx[id]? with
    | none => simp [hb, hi, ex_throw] at h
    | some j0 =>
      simp only [hb, hi] at h
      obtain ⟨hc, h⟩ := ex_guard h
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      refine ⟨id, rfl, ?_⟩
      cases hp : cx.ps[j0]? with
      | none => simp [hp] at hc
      | some p =>
        obtain ⟨hk, hk'⟩ := Array.getElem?_eq_some_iff.mp hp
        simp only [hp, Option.map_some, beq_iff_eq, Option.some.injEq] at hc
        exact ⟨hk, hk' ▸ hc⟩

/-- The Progs between the start index of a value and the next. -/
def VStep (ps : Array Prog) : VKind → Nat → Nat → Prop
  | .entry, j, j' => j' = j
  | .none, j, j' => j' = j
  | .prog sh, j, j' => OneAt ps j sh j'

theorem Cx.values_spec {cx : Cx} {entry : Bool} :
    ∀ {ids : List ID} {j : Nat} {head : Bool} {js : List Nat} {e : Nat},
      cx.values entry ids j head = .ok (js, e) →
      js.length = ids.length ∧ (js ++ [e]).getD 0 0 = j ∧
      ∀ i (hi : i < ids.length), ∃ v kd, cx.lc.ctx.f.value? ids[i] = some v ∧
        vkind cx.lc v = .ok kd ∧ VStep cx.ps kd ((js ++ [e]).getD i 0) ((js ++ [e]).getD (i + 1) 0) := by
  intro ids
  induction ids with
  | nil =>
    intro j head js e h
    simp only [Cx.values, ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons id ids ih =>
    intro j head js e h
    simp only [Cx.values] at h
    cases hv : cx.lc.ctx.f.value? id with
    | none => simp [hv, ex_throw] at h
    | some v =>
      simp only [hv] at h
      obtain ⟨kd, hk, h⟩ := ex_bind_eq_ok h
      have fin : ∀ k, VStep cx.ps kd j k →
          (cx.values entry ids k (head && entryOp v.op) >>= fun x => pure (j :: x.fst, x.snd)) =
            Except.ok (js, e) →
          js.length = (id :: ids).length ∧ (js ++ [e]).getD 0 0 = j ∧
          ∀ i (hi : i < (id :: ids).length), ∃ v kd, cx.lc.ctx.f.value? (id :: ids)[i] = some v ∧
            vkind cx.lc v = .ok kd ∧
            VStep cx.ps kd ((js ++ [e]).getD i 0) ((js ++ [e]).getD (i + 1) 0) := by
        intro k hstep h
        obtain ⟨⟨js', e'⟩, hrest, h⟩ := ex_bind_eq_ok h
        simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ih1, ih2, ih3⟩ := ih hrest
        refine ⟨by simp [ih1], rfl, ?_⟩
        intro i hi
        cases i with
        | zero =>
          refine ⟨v, kd, hv, hk, ?_⟩
          simp only [List.cons_append, List.getD_cons_zero, List.getD_cons_succ, ih2]
          exact hstep
        | succ i =>
          have := ih3 i (by simpa using hi)
          simpa only [List.cons_append, List.getD_cons_succ, List.getElem_cons_succ] using this

      cases kd with
      | entry =>
        obtain ⟨_, h⟩ := ex_guard h
        exact fin j rfl h
      | none => exact fin j rfl h
      | prog sh =>
        obtain ⟨k, hkk, h⟩ := ex_bind_eq_ok h
        exact fin k (Cx.one_spec hkk) h


/-! ## Terminators -/

/-- A branch of shape `br` to `t`, then the fall-through to `f` (laid out next, `next`) or a `JMP`
to `f`, from index `j`. -/
def TwoAt (cx : Cx) (next : Option (ID × Nat)) (j : Nat) (br : Shape) (t f : ID) : Prop :=
  ∃ tid k, cx.bstart t = some tid ∧ OneAt cx.ps j { br with to := brA tid } k ∧
    (next = some (f, k) ∨
      ∃ fid k', cx.bstart f = some fid ∧ OneAt cx.ps k { as := .JMP, to := brA fid } k')

/-- What `Cx.term` accepted of a terminator from index `j`. -/
structure TermOK (cx : Cx) (b : Block) (j : Nat) (next : Option (ID × Nat)) : Prop where
  succs : ∀ e ∈ b.succs.toList, e.b ∈ cx.lc.ctx.f.blocks.toList
  plain : b.kind = .Plain → ∃ e, b.succs = #[e] ∧
    (next = some (e.b, j) ∨ ∃ id k, cx.bstart e.b = some id ∧ OneAt cx.ps j { as := .JMP, to := brA id } k)
  branch : b.kind ≠ .Plain → b.kind ≠ .Ret → ∃ e0 e1 c, b.succs = #[e0, e1] ∧ b.controls = #[c] ∧
    ((∃ asm inv, condBr b.kind = some (asm, inv) ∧ (cx.lc.ty c).isFlags = true ∧
        cx.lc.home c = none ∧
        (TwoAt cx next j { as := asm } e0.b e1.b ∨ TwoAt cx next j { as := inv } e1.b e0.b)) ∨
     (∃ asm inv r o, condBr b.kind = none ∧ zeroBr b.kind = some (asm, inv) ∧
        cx.lc.home c = some (.reg r) ∧ objOf? r = some o ∧
        (cls (cx.lc.ty c) = some 64 ∨ cls (cx.lc.ty c) = some 1) ∧
        (TwoAt cx next j { as := asm, from_ := regA o } e0.b e1.b ∨
          TwoAt cx next j { as := inv, from_ := regA o } e1.b e0.b)))

theorem Cx.two_spec {cx : Cx} {j : Nat} {next : Option (ID × Nat)} {br : Shape} {t f : ID}
    (h : cx.two j next br t f = .ok ()) : TwoAt cx next j br t f := by
  unfold Cx.two at h
  obtain ⟨a, ha, h⟩ := ex_bind_eq_ok h
  obtain ⟨tid, htid, rfl⟩ : ∃ tid, cx.bstart t = some tid ∧ a = brA tid := by
    simp only at ha
    split at ha
    next tid htid => simp only [ex_pure, Except.ok.injEq] at ha; exact ⟨tid, htid, ha.symm⟩
    next => simp [ex_throw] at ha
  obtain ⟨k, hk, h⟩ := ex_bind_eq_ok h
  refine ⟨tid, k, htid, Cx.one_spec hk, ?_⟩
  split at h
  next hf => left; simpa using hf
  next =>
    right
    obtain ⟨a2, ha2, h⟩ := ex_bind_eq_ok h
    obtain ⟨fid, hfid, rfl⟩ : ∃ fid, cx.bstart f = some fid ∧ a2 = brA fid := by
      simp only at ha2
      split at ha2
      next fid hfid => simp only [ex_pure, Except.ok.injEq] at ha2; exact ⟨fid, hfid, ha2.symm⟩
      next => simp [ex_throw] at ha2
    obtain ⟨k', hk', -⟩ := ex_bind_eq_ok h
    exact ⟨fid, k', hfid, Cx.one_spec hk'⟩

theorem Cx.term_spec {cx : Cx} {b : Block} {j : Nat} {next : Option (ID × Nat)}
    (h : cx.term b j next = .ok ()) : TermOK cx b j next := by
  unfold Cx.term at h
  obtain ⟨hs, h⟩ := ex_guard h
  have hsucc : ∀ e ∈ b.succs.toList, e.b ∈ cx.lc.ctx.f.blocks.toList := by
    intro e he
    simp only [Array.all_eq_true_iff_forall_mem, Array.contains_iff_mem] at hs
    simpa using hs e (by simpa using he)
  split at h
  next hk =>
    refine ⟨hsucc, fun _ => ?_, fun h1 _ => absurd hk h1⟩
    split at h
    next e he =>
      obtain ⟨hc, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      refine ⟨e, arr_one hc.1 he, ?_⟩
      split at h
      next hf => left; simpa using hf
      next =>
        right
        obtain ⟨a, ha, h⟩ := ex_bind_eq_ok h
        obtain ⟨id, hid, rfl⟩ : ∃ id, cx.bstart e.b = some id ∧ a = brA id := by
          simp only at ha
          split at ha
          next id hid => simp only [ex_pure, Except.ok.injEq] at ha; exact ⟨id, hid, ha.symm⟩
          next => simp [ex_throw] at ha
        obtain ⟨k, hk1, -⟩ := ex_bind_eq_ok h
        exact ⟨id, k, hid, Cx.one_spec hk1⟩
    next => simp [ex_throw] at h
  next hk =>
    refine ⟨hsucc, fun h1 => ?_, fun _ h2 => absurd hk h2⟩
    rw [hk] at h1
    cases h1
  next hk1 hk2 =>
    refine ⟨hsucc, fun h1 => absurd h1 hk1, fun _ _ => ?_⟩
    split at h
    next e0 he0 =>
      split at h
      next e1 he1 =>
        obtain ⟨hc, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        split at h
        next c hc0 =>
          refine ⟨e0, e1, c, arr_two hc.1 he0 he1, arr_one hc.2 hc0, ?_⟩
          split at h
          next asm inv hcb =>
            obtain ⟨hcc, h⟩ := ex_guard h
            simp only [Bool.and_eq_true, beq_iff_eq] at hcc
            left
            refine ⟨asm, inv, hcb, hcc.1, hcc.2, ?_⟩
            obtain ⟨x, hx, h⟩ := ex_bind_eq_ok h
            simp only [ex_pure, Except.ok.injEq] at hx
            subst hx
            simp only at h
            split at h
            next heq =>
              exact Or.inl (Cx.two_spec (cx := cx) (j := j) (next := next) (br := { as := asm })
                (t := e0.b) (f := e1.b) heq)
            next =>
              exact Or.inr (Cx.two_spec (cx := cx) (j := j) (next := next) (br := { as := inv })
                (t := e1.b) (f := e0.b) h)
          next asm inv hcb hzb =>
            split at h
            next r hr =>
              split at h
              next o ho =>
                obtain ⟨hw, h⟩ := ex_guard h
                simp only [Bool.or_eq_true, beq_iff_eq] at hw
                right
                refine ⟨asm, inv, r, o, hcb, hzb, regHome?_eq.mp hr, ho, hw, ?_⟩
                obtain ⟨x, hx, h⟩ := ex_bind_eq_ok h
                simp only [ex_pure, Except.ok.injEq] at hx
                subst hx
                simp only at h
                split at h
                next heq =>
                  exact Or.inl (Cx.two_spec (cx := cx) (j := j) (next := next)
                    (br := { as := asm, from_ := regA o }) (t := e0.b) (f := e1.b) heq)
                next =>
                  exact Or.inr (Cx.two_spec (cx := cx) (j := j) (next := next)
                    (br := { as := inv, from_ := regA o }) (t := e1.b) (f := e0.b) h)
              next => exact (ex_throw_bind h).elim
            next => exact (ex_throw_bind h).elim
          next => exact (ex_throw_bind h).elim
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h


/-! ## Blocks and the whole check -/

theorem Cx.blocks_spec {cx : Cx} : ∀ {bids : List ID} {tab : PcTab}, cx.blocks bids = .ok tab →
    ∀ bid ∈ bids, ∃ b j js e next, cx.lc.ctx.f.block? bid = some b ∧ cx.startIdx bid = .ok j ∧
      cx.values (bid == cx.lc.ctx.f.entry) b.values.toList j true = .ok (js, e) ∧
      TermOK cx b e next ∧ (∀ n k, next = some (n, k) → cx.startIdx n = .ok k) ∧
      tab.lookup bid = some (js ++ [e]) := by
  intro bids
  induction bids with
  | nil => intro tab _ bid hb; cases hb
  | cons bid0 rest ih =>
    intro tab h bid hbid
    unfold Cx.blocks at h
    cases hb : cx.lc.ctx.f.block? bid0 with
    | none => simp [hb, ex_throw] at h
    | some b =>
      simp only [hb] at h
      obtain ⟨j, hj, h⟩ := ex_bind_eq_ok h
      obtain ⟨⟨js, e⟩, hv, h⟩ := ex_bind_eq_ok h
      obtain ⟨next, hn, h⟩ : ∃ next, (∀ n k, next = some (n, k) → cx.startIdx n = .ok k) ∧
          (do cx.term b e next; let tab ← cx.blocks rest; pure ((bid0, js ++ [e]) :: tab)) =
            Except.ok tab := by
        split at h
        next n _ =>
          obtain ⟨k, hk, h⟩ := ex_bind_eq_ok h
          refine ⟨some (n, k), fun n' k' he => ?_, h⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact hk
        next => exact ⟨none, (fun _ _ he => nomatch he), h⟩
      obtain ⟨⟨⟩, ht, h⟩ := ex_bind_eq_ok h
      obtain ⟨tab', htab, h⟩ := ex_bind_eq_ok h
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      by_cases hbe : bid = bid0
      · subst hbe
        exact ⟨b, j, js, e, next, hb, hj, hv, Cx.term_spec ht, hn, by simp [List.lookup]⟩
      · have hmem : bid ∈ rest := by
          cases hbid with
          | head => exact absurd rfl hbe
          | tail _ hm => exact hm
        obtain ⟨b', j', js', e', next', h1, h2, h3, h4, h5, h6⟩ := ih htab bid hmem
        refine ⟨b', j', js', e', next', h1, h2, h3, h4, h5, ?_⟩
        have hne : (bid == bid0) = false := by simp [hbe]
        simp only [List.lookup, hne, h6]

theorem checkG1_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab}
    (h : checkG1 lc ps bstart = .ok tab) :
    ∃ cx : Cx, cx.lc = lc ∧ cx.ps = ps ∧ cx.bstart = bstart ∧ lc.ctx.f.lowered = true ∧
      (∀ i, homeOK lc i = true) ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧
      (ps.toList.map (·.id)).Nodup ∧ cx.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG1 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  cases hf : List.find? (fun x => !homeOK lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq] at h
    subst h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, hl, fun i => ?_, fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb⟩
    by_cases hi : i < lc.homes.size
    · have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
      simpa using this
    · have hh : lc.home i = none := by
        simp only [LocCtx.home]
        rw [getElem?_neg lc.homes i hi]
        rfl
      unfold homeOK
      rw [hh]

end GoFV.Gen.Check
