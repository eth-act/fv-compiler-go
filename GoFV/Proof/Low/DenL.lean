import GoFV.Proof.Low.TermL
import GoFV.Proof.Low.ArmMono
import GoFV.Proof.AtomSimDen
import GoFV.Proof.EvalOpLDispatch

/-!
# Basic facts about `denL` (issue #385)

The lowered counterparts of `GoFV.Proof.AtomSim`'s `den` lemmas (`AtomSimDen.lean`): `rty` is
monotone and idempotent, `opValL` monotone; `denL` unfolds at a term node and at an atom, is a
refinement chain in the fuel and reads the valuation only at the atoms it reaches; a term value
of a `runL` frame is `opValL` of its arguments' registers (`evalOpL_termVL`,
`evalValueL_termVL`).
-/

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.LowerTerm GoFV.Opt.LowerCheck GoFV.Proof.Term GoFV.Proof.AtomSim

/-! ## `rty`, `opValL` -/

theorem rty_mono (low : Bool) (t : Ty) {v v' : Val} (h : Sem.Refines v v') :
    Sem.Refines (rty low t v) (rty low t v') := by
  unfold rty; cases low
  · exact retype_mono t h
  · exact retypeL_mono t h

theorem rty_idem (low : Bool) (t : Ty) (v : Val) : rty low t (rty low t v) = rty low t v := by
  unfold rty; cases low
  · exact retype_idem t v
  · exact retypeL_idem t v

theorem rty_poison (low : Bool) (t : Ty) : rty low t .poison = .poison := by
  unfold rty; cases low
  · exact retype_poison t
  · exact retypeL_poison t

theorem rty_hasTy (low : Bool) (t : Ty) (v : Val) : (rty low t v).hasTy t = true := by
  unfold rty; cases low
  · exact Val.retype_hasTy t v
  · exact retypeL_hasTy t v

/-- `rty` is `runL`'s shaping (`Sem.LMode.retype`). -/
theorem LMode.retype_eq (md : LMode) (t : Ty) (v : Val) : md.retype t v = rty md.low t v := rfl

/-- An arm64 load on a refined memory refines. -/
theorem loadN_mono {m m' : Mem} (h : Mem.Refines m m') (ty : Ty) (n : Nat) (s : Bool) (p : Ptr) :
    Sem.Refines (Arm64.loadN ty n s m p) (Arm64.loadN ty n s m' p) := by
  unfold Arm64.loadN
  split
  · have hl := GoFV.SSA.Sem.load_mono h (.int .w64) p
    revert hl
    generalize m.load (.int .w64) p = x
    generalize m'.load (.int .w64) p = y
    intro hl
    cases hl <;> first | exact .poison _ | exact Sem.Refines.refl _ | (constructor; assumption)
  · split
    · rename_i w _
      have hl := GoFV.SSA.Sem.load_mono h (.int w) p
      revert hl
      generalize m.load (.int w) p = x
      generalize m'.load (.int w) p = y
      intro hl
      cases hl <;> first | exact .poison _ | exact Sem.Refines.refl _
    · exact Sem.Refines.refl _

/-- `ldVal` is monotone. -/
theorem ldVal_mono (tabs : Tables) (n : Nat) (s : Bool) (ty : Ty) (ai : Int64)
    (ax : Option AuxRef) {as bs : List Val} (hr : RefinesList as bs) :
    Sem.Refines (ldVal tabs n s ty ai ax as) (ldVal tabs n s ty ai ax bs) := by
  cases hr with
  | nil => exact .poison _
  | @cons a a' _ _ h1 hr =>
  cases hr with
  | nil => exact .poison _
  | @cons b b' _ _ h2 hr =>
  cases hr with
  | @cons c _ l _ _ _ =>
    have : ldVal tabs n s ty ai ax (a :: b :: c :: l) = .poison := by cases b <;> rfl
    rw [this]; exact .poison _
  | nil =>
  cases h2 with
  | mem hm =>
    have hp : movPtr tabs ai ax a = none ∨ movPtr tabs ai ax a = movPtr tabs ai ax a' := by
      cases ax with
      | some _ => exact .inr rfl
      | none => cases h1 <;> first | exact .inr rfl | exact .inl rfl
    rcases hp with he | he
    · simp only [ldVal, he, Option.elim]; exact .poison _
    · simp only [ldVal, he]
      cases movPtr tabs ai ax a' with
      | none => exact .poison _
      | some p => exact loadN_mono hm ty n s p
  | _ => first | exact .poison _ | exact Sem.Refines.refl _

/-- `opValL` of a term value is monotone. -/
theorem opValL_mono_term {tabs : Tables} {v : Value} (ht : termVL tabs v = true) (ty : Ty)
    {as bs : List Val} (h : RefinesList as bs) :
    Sem.Refines (opValL tabs v.op ty v.auxInt v.aux as) (opValL tabs v.op ty v.auxInt v.aux bs) := by
  unfold opValL
  by_cases hg : v.op.generic = true
  · simp only [hg, ite_true]; exact Rules.opVal_mono tabs v.op ty v.auxInt v.aux h
  · simp only [hg, Bool.false_eq_true, ite_false]
    by_cases hm : v.op = .ARM64MOVDaddr
    · simp only [hm, beq_self_eq_true, ite_true]; exact movAddr_mono tabs v.auxInt v.aux h
    · have hm' : (v.op == .ARM64MOVDaddr) = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ite_false]
      cases hl : ldOp? v.op with
      | some p => exact ldVal_mono tabs p.1 p.2 ty v.auxInt v.aux h
      | none =>
        unfold termVL at ht
        simp only [hg, Bool.false_eq_true, ite_false, hm', hl, Option.isSome_none] at ht
        by_cases hd : ldarOp v.op = true
        · rw [armPure_ldar hd, armPure_ldar hd]; exact atomicLoad_mono ty h
        · simp only [hd, Bool.false_eq_true, ite_false, Bool.and_eq_true] at ht
          exact armPure_mono ht.1.1 ty v.auxInt v.aux h

/-! ## `denL` -/

theorem denL_succ_term {low : Bool} {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}
    {n : Nat} {x : ID} {v : Value} (hx : D x = some v) (ht : termVL tabs v = true) :
    denL low D tabs ρ (n + 1) x = rty low (shp low tabs v.type)
      (opValL tabs v.op (shp low tabs v.type) v.auxInt v.aux (v.args.toList.map (denL low D tabs ρ n))) := by
  simp only [denL, hx, ht, ite_true]

theorem denL_succ_atom {low : Bool} {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}
    {n : Nat} {x : ID} (hx : ¬ IsTermL tabs D x) : denL low D tabs ρ (n + 1) x = ρ x := by
  cases h : D x with
  | none => simp only [denL, h]
  | some v =>
    have ht : termVL tabs v = false := by
      cases hv : termVL tabs v
      · rfl
      · exact absurd ⟨v, h, hv⟩ hx
    simp only [denL, h, ht, Bool.false_eq_true, ite_false]

/-- `denL` is a refinement chain in the fuel. -/
theorem denL_fuel_mono (low : Bool) (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) :
    ∀ (n m : Nat) (x : ID), n ≤ m → Sem.Refines (denL low D tabs ρ n x) (denL low D tabs ρ m x)
  | 0, _, _, _ => .poison _
  | n + 1, 0, _, h => absurd h (by omega)
  | n + 1, m + 1, x, h => by
    by_cases ht : IsTermL tabs D x
    · obtain ⟨v, hx, hv⟩ := ht
      rw [denL_succ_term hx hv, denL_succ_term hx hv]
      exact rty_mono _ _ (opValL_mono_term hv _
        (refinesList_map fun a _ => denL_fuel_mono low D tabs ρ n m a (by omega)))
    · rw [denL_succ_atom ht, denL_succ_atom ht]; exact Sem.Refines.refl _

/-- `denL` is monotone in the valuation. -/
theorem denL_val_mono (low : Bool) (D : ID → Option Value) (tabs : Tables) {ρ ρ' : ID → Val}
    (h : ValRef ρ ρ') : ∀ (n : Nat) (x : ID), Sem.Refines (denL low D tabs ρ n x) (denL low D tabs ρ' n x)
  | 0, _ => .poison _
  | n + 1, x => by
    by_cases ht : IsTermL tabs D x
    · obtain ⟨v, hx, hv⟩ := ht
      rw [denL_succ_term hx hv, denL_succ_term hx hv]
      exact rty_mono _ _ (opValL_mono_term hv _
        (refinesList_map fun a _ => denL_val_mono low D tabs h n a))
    · rw [denL_succ_atom ht, denL_succ_atom ht]; exact h x

/-- `V` contains the arguments of its term nodes. -/
def ClosedL (tabs : Tables) (D : ID → Option Value) (V : ID → Prop) : Prop :=
  ∀ x, V x → ∀ v, D x = some v → termVL tabs v = true → ∀ a ∈ v.args, V a

/-- `denL` reads the valuation only at the atoms reached through term nodes. -/
theorem denL_congr {low : Bool} {D : ID → Option Value} {tabs : Tables} {C : ID → Prop}
    (hC : ClosedL tabs D C) {ρ1 ρ2 : ID → Val} (h : ∀ a, C a → ¬ IsTermL tabs D a → ρ1 a = ρ2 a) :
    ∀ (n : Nat) (x : ID), C x → denL low D tabs ρ1 n x = denL low D tabs ρ2 n x
  | 0, _, _ => rfl
  | n + 1, x, hx => by
    by_cases ht : IsTermL tabs D x
    · obtain ⟨v, hv, hop⟩ := ht
      rw [denL_succ_term hv hop, denL_succ_term hv hop]
      rw [List.map_congr_left (fun a ha =>
        denL_congr hC h n a (hC x hx v hv hop a (Array.mem_toList_iff.1 ha)))]
    · rw [denL_succ_atom ht, denL_succ_atom ht]; exact h x hx ht

/-! ## Terms in `runL` frames -/

/-- `Sem.symAddr` without a frame variable aux does not read the frame (`movPtr`). -/
theorem symAddr_eq {ctx : Ctx} {v : Value} {a : Val} (hn : auxIsName ctx.tabs v.aux = false) :
    symAddr ctx v a = movPtr ctx.tabs v.auxInt v.aux a := by
  unfold symAddr movPtr
  cases hax : v.aux with
  | none => rfl
  | some n =>
    unfold auxIsName at hn
    rw [hax] at hn
    simp only [Option.bind_some] at hn
    dsimp only
    cases h : ctx.tabs.aux? n with
    | none => rfl
    | some d =>
      rw [h] at hn
      rcases d with ⟨fmt, kind⟩
      cases kind <;> simp_all

/-- `arm64Op` of `MOVDaddr` without a frame variable aux is `movAddr`. -/
theorem arm64Op_movAddr {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .ARM64MOVDaddr) (hn : auxIsName ctx.tabs v.aux = false) :
    arm64Op false env ctx fr v argv ty = .ok (movAddr ctx.tabs v.auxInt v.aux argv) := by
  have h0 : nilFaults false ctx v argv = none := rfl
  unfold arm64Op
  rw [h0]
  dsimp only
  rw [hop]
  dsimp only
  unfold movAddr
  cases argv with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => dsimp only; rw [symAddr_eq hn]
    | cons => rfl

/-- `Sem.symAddr` with a frame variable aux: the variable's frame block at the offset (the base is
not read). -/
theorem symAddr_name {ctx : Ctx} {v : Value} {a : Val} {n : AuxRef} (hax : v.aux = some n)
    (hn : auxIsName ctx.tabs v.aux = true) :
    symAddr ctx v a = some ⟨frameBlk ctx.tabs ctx.act n, BitVec.ofInt 64 v.auxInt.toInt⟩ := by
  unfold symAddr
  unfold auxIsName at hn
  rw [hax] at hn ⊢
  simp only [Option.bind_some] at hn
  dsimp only
  cases h : ctx.tabs.aux? n with
  | none => rw [h] at hn; cases hn
  | some d =>
    rw [h] at hn
    rcases d with ⟨fmt, kind⟩
    cases kind <;> simp_all

/-- `evalOpL` of a `MOVDaddr` with one argument: the address `symAddr` as a pointer-arithmetic
result. -/
theorem evalOpL_movDaddr {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {a : Val} {ty : Ty}
    (hop : v.op = .ARM64MOVDaddr) :
    evalOpL false env ctx fr v [a] ty = .ok ((symAddr ctx v a).elim .poison PtrOps.ptrRes) := by
  have hg' : Op.ARM64MOVDaddr.generic = false := by decide
  have h1 : evalOpL false env ctx fr v [a] ty = arm64Op false env ctx fr v [a] ty := by
    unfold evalOpL; rw [hop]; simp only [hg', Bool.false_eq_true, ite_false]
  have h0 : nilFaults false ctx v [a] = none := rfl
  rw [h1]
  unfold arm64Op
  rw [h0]
  dsimp only
  rw [hop]

/-- A `MOVDaddr` evaluates (non-faulting mode). -/
theorem evalOpL_movDaddr_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .ARM64MOVDaddr) : ∃ y, evalOpL false env ctx fr v argv ty = .ok y := by
  have hg' : Op.ARM64MOVDaddr.generic = false := by decide
  have h1 : evalOpL false env ctx fr v argv ty = arm64Op false env ctx fr v argv ty := by
    unfold evalOpL; rw [hop]; simp only [hg', Bool.false_eq_true, ite_false]
  have h0 : nilFaults false ctx v argv = none := rfl
  rw [h1]
  unfold arm64Op
  rw [h0]
  dsimp only
  rw [hop]
  dsimp only
  split <;> exact ⟨_, rfl⟩

/-- An integer load without a frame variable aux evaluates to `ldVal`. -/
theorem arm64Op_ld {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    {p : Nat × Bool} (hl : ldOp? v.op = some p) (hn : auxIsName ctx.tabs v.aux = false) :
    evalOpL false env ctx fr v argv ty = .ok (ldVal ctx.tabs p.1 p.2 ty v.auxInt v.aux argv) := by
  have h0 : nilFaults false ctx v argv = none := rfl
  have hs := fun a => symAddr_eq (ctx := ctx) (v := v) (a := a) hn
  rcases ldOp?_mem hl with h | h | h | h | h | h | h <;> rw [h] at hl <;> cases hl <;>
  · unfold evalOpL
    rw [h, if_neg (by decide)]
    dsimp only
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [h]
    dsimp only
    unfold ldVal
    split <;> simp_all

/-- An acquiring load evaluates by `Arm64.evalPure` (non-faulting mode: `arm64Op`'s default). -/
theorem arm64Op_ldar {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hd : ldarOp v.op = true) :
    evalOpL false env ctx fr v argv ty = .ok (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  have h0 : nilFaults false ctx v argv = none := rfl
  rcases ldarOp_cases hd with h | h | h <;>
  · unfold evalOpL
    rw [h, if_neg (by decide)]
    dsimp only
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [h]
    rfl

/-- A term value evaluates by `opValL` (`Sem.evalOpL`: Phase 1's `evalOp` of a generic term
op, `arm64Op` of `MOVDaddr` and of an integer load, `Arm64.evalPure` of an `armTerm` op). -/
theorem evalOpL_termVL {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (ht : termVL ctx.tabs v = true) :
    evalOpL false env ctx fr v argv ty = .ok (opValL ctx.tabs v.op ty v.auxInt v.aux argv) := by
  unfold termVL at ht
  by_cases hg : v.op.generic = true
  · rw [evalOpL_generic _ _ _ _ _ _ hg]
    simp only [hg, ite_true] at ht
    rw [evalOp_term ht]
    simp only [opValL, hg, ite_true]
  · simp only [hg, Bool.false_eq_true, ite_false] at ht
    by_cases hm : v.op = .ARM64MOVDaddr
    · simp only [hm, beq_self_eq_true, ite_true, Bool.not_eq_true'] at ht
      have hg' : Op.ARM64MOVDaddr.generic = false := by rw [← hm]; simpa using hg
      have : evalOpL false env ctx fr v argv ty = arm64Op false env ctx fr v argv ty := by
        unfold evalOpL; rw [hm]; simp only [hg', Bool.false_eq_true, ite_false]
      rw [this, arm64Op_movAddr hm ht]
      simp only [opValL, hm, hg', Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
    · have hm' : (v.op == .ARM64MOVDaddr) = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ite_false] at ht
      cases hl : ldOp? v.op with
      | some p =>
        simp only [hl, Option.isSome_some, ite_true, Bool.not_eq_true'] at ht
        rw [arm64Op_ld hl ht]
        simp only [opValL, hg, Bool.false_eq_true, ite_false, hm', hl]
      | none =>
      simp only [hl, Option.isSome_none, Bool.false_eq_true, ite_false] at ht
      by_cases hd : ldarOp v.op = true
      · rw [arm64Op_ldar hd]
        simp only [opValL, hg, Bool.false_eq_true, ite_false, hm', hl]
      simp only [hd, Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.not_eq_true'] at ht
      obtain ⟨⟨-, ha⟩, hr⟩ := ht
      have : evalOpL false env ctx fr v argv ty = pure (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
        rw [evalOpL_of_not_actOp (by simpa using hg) (by simpa using ha), hr]; rfl
      rw [this]
      simp only [opValL, hg, Bool.false_eq_true, ite_false, hm', hl, pure]

end GoFV.Proof.Low
