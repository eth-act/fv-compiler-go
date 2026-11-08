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
    have hp : symPtr tabs ai ax a = none ∨ symPtr tabs ai ax a = symPtr tabs ai ax a' := by
      cases ax with
      | some _ => exact .inr rfl
      | none => cases h1 <;> first | exact .inr rfl | exact .inl rfl
    rcases hp with he | he
    · simp only [ldVal, he, Option.elim]; exact .poison _
    · simp only [ldVal, he]
      cases symPtr tabs ai ax a' with
      | none => exact .poison _
      | some p => exact Mono.loadN_mono hm ty n s p
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
        by_cases hd : pureActOp v.op = true
        · rcases pureActOp_cases hd with hv | hv | hv | hv <;> rw [hv]
          · exact atomicLoad_mono ty h
          · exact atomicLoad_mono ty h
          · exact atomicLoad_mono ty h
          · exact memEq_mono h
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

/-- `Sem.symAddr` in activation 0 is `symPtr`. -/
theorem symAddr_ld {ctx : Ctx} {v : Value} {a : Val} (hact : ctx.act = 0) :
    symAddr ctx v a = symPtr ctx.tabs v.auxInt v.aux a := by
  unfold symAddr symPtr
  rw [hact]
  rfl

/-- `arm64Op` of `MOVDaddr` in activation 0 is `movAddr`. -/
theorem arm64Op_movAddr {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .ARM64MOVDaddr) (hact : ctx.act = 0) :
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
    | nil => dsimp only; rw [symAddr_ld hact]
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

/-- An integer load evaluates to `ldVal` in activation 0. -/
theorem arm64Op_ld {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    {p : Nat × Bool} (hl : ldOp? v.op = some p) (hact : ctx.act = 0) :
    evalOpL false env ctx fr v argv ty = .ok (ldVal ctx.tabs p.1 p.2 ty v.auxInt v.aux argv) := by
  have h0 : nilFaults false ctx v argv = none := rfl
  have hs := fun a => symAddr_ld (ctx := ctx) (v := v) (a := a) hact
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

/-- An acquiring load or `LoweredMemEq` evaluates by `Arm64.evalPure` (non-faulting mode:
`arm64Op`'s default, `memEq`). -/
theorem arm64Op_pureAct {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hd : pureActOp v.op = true) :
    evalOpL false env ctx fr v argv ty = .ok (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  have h0 : nilFaults false ctx v argv = none := rfl
  rcases pureActOp_cases hd with h | h | h | h <;>
  · unfold evalOpL
    rw [h, if_neg (by decide)]
    dsimp only
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [h]
    rfl

/-- A term value evaluates by `opValL` in activation 0 (`Sem.evalOpL`: Phase 1's `evalOp` of a
generic term op, `arm64Op` of `MOVDaddr` and of an integer load, `Arm64.evalPure` of an `armTerm`
op). -/
theorem evalOpL_termVL {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (ht : termVL ctx.tabs v = true) (hact : ctx.act = 0) :
    evalOpL false env ctx fr v argv ty = .ok (opValL ctx.tabs v.op ty v.auxInt v.aux argv) := by
  unfold termVL at ht
  by_cases hg : v.op.generic = true
  · rw [evalOpL_generic _ _ _ _ _ _ hg]
    simp only [hg, ite_true] at ht
    rw [evalOp_term ht]
    simp only [opValL, hg, ite_true]
  · simp only [hg, Bool.false_eq_true, ite_false] at ht
    by_cases hm : v.op = .ARM64MOVDaddr
    · have hg' : Op.ARM64MOVDaddr.generic = false := by rw [← hm]; simpa using hg
      have : evalOpL false env ctx fr v argv ty = arm64Op false env ctx fr v argv ty := by
        unfold evalOpL; rw [hm]; simp only [hg', Bool.false_eq_true, ite_false]
      rw [this, arm64Op_movAddr hm hact]
      simp only [opValL, hm, hg', Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
    · have hm' : (v.op == .ARM64MOVDaddr) = false := by simpa using hm
      simp only [hm', Bool.false_eq_true, ite_false] at ht
      cases hl : ldOp? v.op with
      | some p =>
        rw [arm64Op_ld hl hact]
        simp only [opValL, hg, Bool.false_eq_true, ite_false, hm', hl]
      | none =>
      simp only [hl, Option.isSome_none, Bool.false_eq_true, ite_false] at ht
      by_cases hd : pureActOp v.op = true
      · rw [arm64Op_pureAct hd]
        simp only [opValL, hg, Bool.false_eq_true, ite_false, hm', hl]
      simp only [hd, Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.not_eq_true'] at ht
      obtain ⟨⟨-, ha⟩, hr⟩ := ht
      have : evalOpL false env ctx fr v argv ty = pure (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
        rw [evalOpL_of_not_actOp (by simpa using hg) (by simpa using ha), hr]; rfl
      rw [this]
      simp only [opValL, hg, Bool.false_eq_true, ite_false, hm', hl, pure]

/-- `idxAddr` is monotone. -/
theorem idxAddr_mono (s : Nat) {a a' i i' : Val} (ha : Sem.Refines a a') (hi : Sem.Refines i i') :
    Sem.Refines (idxAddr s a i) (idxAddr s a' i') := by
  unfold idxAddr
  split
  · exact Mono.add_mono _ (.cons ha (.cons hi .nil))
  · cases hk : Arm64.reg i with
    | none => exact .poison _
    | some k =>
      rw [Mono.reg_of hi hk]
      exact Mono.add_mono _ (.cons ha (.cons (Sem.Refines.refl _) .nil))

theorem termVL_phi {tabs : Tables} {v : Value} (h : v.op = .Phi) : termVL tabs v = false := by
  have hg : Op.Phi.generic = true := by decide
  have ht : GoFV.Opt.RewriteCheck.termOp .Phi = false := by decide
  unfold termVL
  simp only [h, hg, ht, ite_true]

theorem termVL_makeResult {tabs : Tables} {v : Value} (h : v.op = .MakeResult) :
    termVL tabs v = true := by
  have hg : Op.MakeResult.generic = true := by decide
  have ht : GoFV.Opt.RewriteCheck.termOp .MakeResult = true := by decide
  unfold termVL
  simp only [h, hg, ht, ite_true]

/-- An atom other than a `Phi` reads its arguments at most at its `atomFitTy`. -/
theorem argFitTy_atom {tabs : Tables} {v : Value} {i : Nat} (ht : termVL tabs v = false)
    (hp : v.op ≠ .Phi) : argFitTy tabs v i = atomFitTy tabs v i := by
  have hr : v.op ≠ .MakeResult := fun hr => by rw [termVL_makeResult hr] at ht; cases ht
  unfold argFitTy
  simp only [show (v.op == .Phi) = false by simpa using hp,
    show (v.op == .MakeResult) = false by simpa using hr, Bool.false_eq_true, ite_false]

/-- What `stFitTy` says: the value (argument 1) of a narrow integer store, or argument 2 of a
narrow indexed one, at its width. -/
theorem stFitTy_cases {o : Op} {i : Nat} {t : Ty} (h : stFitTy o i = some t) :
    ∃ w, t = .int w ∧ ((i = 1 ∧ stValW o = some w) ∨ (i = 2 ∧ stIdxValW o = some w)) := by
  unfold stFitTy at h
  by_cases hi : i = 1
  · subst hi
    simp only [beq_self_eq_true, ite_true, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    exact ⟨w, rfl, .inl ⟨rfl, hw⟩⟩
  · rw [if_neg (by simpa using hi)] at h
    by_cases hi2 : i = 2
    · subst hi2
      simp only [beq_self_eq_true, ite_true, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      exact ⟨w, rfl, .inr ⟨rfl, hw⟩⟩
    · rw [if_neg (by simpa using hi2)] at h; cases h

/-- The narrow integer stores (`stValW`). -/
theorem stValW_some {o : Op} {w : Width} (h : stValW o = some w) :
    (o = .ARM64MOVBstore ∧ w = .w8) ∨ (o = .ARM64MOVHstore ∧ w = .w16) ∨
      (o = .ARM64MOVWstore ∧ w = .w32) := by
  unfold stValW at h
  split at h <;> simp_all

/-- The narrow indexed integer stores (`stIdxValW`). -/
theorem stIdxValW_some {o : Op} {w : Width} (h : stIdxValW o = some w) :
    (o = .ARM64MOVBstoreidx ∧ w = .w8) ∨ (o = .ARM64MOVHstoreidx ∧ w = .w16) ∨
      (o = .ARM64MOVHstoreidx2 ∧ w = .w16) ∨ (o = .ARM64MOVWstoreidx ∧ w = .w32) ∨
      (o = .ARM64MOVWstoreidx4 ∧ w = .w32) := by
  unfold stIdxValW at h
  split at h <;> simp_all

/-- The ops `stFitTy` fits an argument of: the narrow integer stores, plain or indexed. -/
theorem stFitTy_ops {o : Op} {i : Nat} {t : Ty} (h : stFitTy o i = some t) :
    o = .ARM64MOVBstore ∨ o = .ARM64MOVHstore ∨ o = .ARM64MOVWstore ∨ o = .ARM64MOVBstoreidx ∨
      o = .ARM64MOVHstoreidx ∨ o = .ARM64MOVHstoreidx2 ∨ o = .ARM64MOVWstoreidx ∨
      o = .ARM64MOVWstoreidx4 := by
  obtain ⟨w, -, ⟨-, hw⟩ | ⟨-, hw⟩⟩ := stFitTy_cases h
  · rcases stValW_some hw with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  · rcases stIdxValW_some hw with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

/-- A narrow integer store is no lowered call. -/
theorem callLead_stValW {o : Op} {w : Width} (h : stValW o = some w) : callLead o = none := by
  rcases stValW_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl

/-- A narrow integer store, plain or indexed, is no lowered call. -/
theorem callLead_stFitTy {o : Op} {i : Nat} {t : Ty} (h : stFitTy o i = some t) :
    callLead o = none := by
  rcases stFitTy_ops h with h | h | h | h | h | h | h | h <;> rw [h] <;> rfl

/-- A generic op fits no argument as a narrow store's value. -/
theorem stFitTy_generic {o : Op} (h : o.generic = true) (i : Nat) : stFitTy o i = none := by
  cases hs : stFitTy o i with
  | none => rfl
  | some t =>
    rcases stFitTy_ops hs with h' | h' | h' | h' | h' | h' | h' | h' <;> rw [h'] at h <;> cases h

/-- A renamed atom fits no argument as a narrow store's value. -/
theorem renameOp_stFitTy {o o' : Op} (h : renameOp o o' = true) (i : Nat) :
    stFitTy o' i = none := by
  cases hs : stFitTy o' i with
  | none => rfl
  | some t =>
    exfalso
    have hs' := (renameOp_stSize h).2
    unfold renameOp at h
    simp only [Bool.or_eq_true] at h
    rcases stFitTy_ops hs with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;>
      first
      | exact absurd hs' (by decide)
      | (rcases h with h | h
         · unfold callRename at h; split at h <;> simp_all
         · simp [atomicRen, Arm64.atomicOf] at h)

/-- Where `atomFitTy` comes from: a lowered call (`callFitTy`) or a narrow integer store's value
(`stFitTy`). -/
theorem atomFitTy_cases {tabs : Tables} {v : Value} {i : Nat} {t : Ty}
    (h : atomFitTy tabs v i = some t) :
    ((callLead v.op).isSome ∧ callFitTy tabs v i = some t) ∨
      (callLead v.op = none ∧ stFitTy v.op i = some t) := by
  unfold atomFitTy at h
  cases hk : callLead v.op with
  | some k => rw [hk] at h; exact .inl ⟨rfl, h⟩
  | none => rw [hk] at h; exact .inr ⟨rfl, h⟩

/-- Read at a shape, a piece fitted to it (`fitPiece`) is the piece. -/
theorem retypeL_fitPiece (t : Ty) (x : Val) : (fitPiece t x).retypeL t = x.retypeL t := by
  unfold fitPiece
  split <;> (try split) <;> simp only [retypeL_idem]

/-- Where `argFitTy` comes from: a lowered call (`callFitTy`), a `Phi` (its shape), a
`MakeResult` (its tuple leaf) or a narrow integer store's value (`stFitTy`). -/
theorem argFitTy_cases {tabs : Tables} {v : Value} {i : Nat} {t : Ty}
    (h : argFitTy tabs v i = some t) :
    ((callLead v.op).isSome ∧ callFitTy tabs v i = some t) ∨ (v.op = .Phi ∧ t = shpL tabs v.type) ∨
      (v.op = .MakeResult ∧ ∃ ts, shpL tabs v.type = .tuple ts ∧ ts[i]? = some t) ∨
      (callLead v.op = none ∧ stFitTy v.op i = some t) := by
  unfold argFitTy at h
  by_cases hp : v.op = .Phi
  · rw [if_pos (by simp [hp])] at h
    exact .inr (.inl ⟨hp, (Option.some.inj h).symm⟩)
  · rw [if_neg (by simp [hp])] at h
    by_cases hr : v.op = .MakeResult
    · rw [if_pos (by simp [hr])] at h
      split at h
      · rename_i ts hts
        exact .inr (.inr (.inl ⟨hr, ts, hts, h⟩))
      · cases h
    · rw [if_neg (by simp [hr])] at h
      rcases atomFitTy_cases h with h | h
      · exact .inl h
      · exact .inr (.inr (.inr h))

/-- An integer narrowed to a narrow width `w`: its low `w` bits. -/
theorem int_retypeL_narrow {w : Width} (v : Width) (x : BitVec v.bits) :
    (Val.int v x).retypeL (.int w) = .int w (x.setWidth w.bits) := by
  unfold Val.retypeL Val.widen
  by_cases hlt : v.bits < w.bits
  · rw [if_pos hlt]
    unfold Val.retype
    rw [if_pos (Nat.le_refl _), BitVec.setWidth_eq]
  · rw [if_neg hlt]
    unfold Val.retype
    rw [if_pos (by omega)]

/-- A boolean at a narrow width: 0 or 1. -/
theorem bool_retypeL_narrow (w : Width) (b : Bool) :
    (Val.bool b).retypeL (.int w) = .int w (if b then 1 else 0) := by
  simp [Val.retypeL, Val.widen, Val.retype]

end GoFV.Proof.Low
