import GoFV.Proof.Gen.Loc
import GoFV.SSA.Sem.Arm64.Mem

/-!
# `stepLoc` on each op of slice G1 (`docs/plans/proofs3.md` §3)

What a successful `stepLoc` does for each op the genssa validator accepts, in a lowered function
(`Val.retypeL`) for a value with no temporary register (so `LocState.clobber` changes nothing):
the arguments read from their homes (`LocState.read`), the op's result (`Arm64.evalPure` for the
pure arm64 ops, Phase 1's `Copy`/`MakeResult`, `arm64Op`'s 8-byte load and store), written to the
value's home at its shape.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

theorem stepLoc_ok_eval (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg) (h2 : v.op ≠ .StoreReg)
    (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv r, v.args.toList.mapM (s.read lc) = .ok argv ∧
      evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) = .ok r ∧
      s' = (s.clobber lc v).write lc v.id ((LMode.loc lc.ctx.f).retype (lc.ty v.id) r) := by
  unfold stepLoc at h
  simp only [show (v.op == Op.Phi) = false by simpa using hne, Bool.false_eq_true,
    ↓reduceIte] at h
  cases hm : v.args.toList.mapM (s.read lc) with
  | panic e m => rw [hm] at h; cases h
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    split at h
    · exact (h1 ‹_›).elim
    · exact (h2 ‹_›).elim
    · exact (h1 ‹_›).elim
    · exact (h2 ‹_›).elim
    · exact (h3 ‹_›).elim
    · exact (h4 ‹_›).elim
    · split at h
      · rename_i r hr; cases h; exact ⟨_, r, rfl, hr, rfl⟩
      · cases h
      · cases h

theorem stepLoc_noclobber (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg) (h2 : v.op ≠ .StoreReg)
    (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (hc : v.op.regInfo.clobbers.isEmpty = true) (hc0 : v.op.regInfo.clobbersArg0 = false)
    (hc1 : v.op.regInfo.clobbersArg1 = false) (hf : v.op.clobberFlags = false)
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv r, v.args.toList.mapM (s.read lc) = .ok argv ∧
      evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) = .ok r ∧
      s' = s.write lc v.id (r.retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_ok_eval hne h1 h2 h3 h4 h
  refine ⟨argv, r, hm, hr, ?_⟩
  rw [clobber_none hc hc0 hc1 ht hf, lmode_retype hl]

private theorem mapM_one {a : ID} :
    [a].mapM (s.read lc) = (s.read lc a).bind fun x => .ok [x] := rfl

private theorem mapM_two {a b : ID} :
    [a, b].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => .ok [x, y] := rfl

private theorem mapM_three {a b c : ID} :
    [a, b, c].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        .ok [x, y, z] := rfl

private theorem symAddr_noAux {ctx : Ctx} (haux : v.aux = none) (x : Val) :
    symAddr ctx v x = Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) := by
  unfold symAddr; rw [haux]

/-- A phi whose arguments share its home does nothing. -/
theorem stepLoc_phi (hop : v.op = .Phi) (h : stepLoc env lc s v = .ok s') : s' = s := by
  unfold stepLoc at h
  rw [hop] at h
  simp only [beq_self_eq_true, ite_true] at h
  split at h
  · cases h; rfl
  · cases h

/-- The pure arm64 ops of G1: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_pure (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64ZERO ∨ v.op = .ARM64MOVDconst ∨ v.op = .ARM64ADD ∨ v.op = .ARM64SUB ∨
      v.op = .ARM64ADDconst ∨ v.op = .ARM64SUBconst ∨ v.op = .ARM64CMP ∨ v.op = .ARM64CMPconst)
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL (lc.ty v.id)) := by
  rcases hop with hop | hop | hop | hop | hop | hop | hop | hop <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv) := by
      unfold evalOpL; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨argv, hm, rfl⟩

/-- `Copy` of one argument: the argument at the value's shape. -/
theorem stepLoc_copy (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .Copy) {a : ID} (ha : v.args = #[a]) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a = .ok x ∧ s' = s.write lc v.id (x.retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hm
  change [a].mapM (s.read lc) = _ at hm
  rw [mapM_one] at hm
  cases hx : s.read lc a with
  | ok x =>
    rw [hx] at hm; cases hm
    have he : evalOpL true env lc.ctx s.fr v [x] (lc.ty v.id) = .ok x := by
      unfold evalOpL evalOp frameVal; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨_, rfl, rfl⟩
  | panic e m => rw [hx] at hm; cases hm
  | stuck msg => rw [hx] at hm; cases hm

/-- `MakeResult`: the tuple of its arguments at the value's shape. -/
theorem stepLoc_makeResult (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .MakeResult) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Val.tuple argv).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) = .ok (.tuple argv) := by
    unfold evalOpL evalOp frameVal; rw [hop]; rfl
  rw [he] at hr; cases hr
  exact ⟨argv, hm, rfl⟩

/-- An inline mark with no home and a shape `write` drops changes nothing. -/
theorem stepLoc_inlMark (ht : (lc.temps[v.id]?).join = none) (hop : v.op = .InlMark)
    (hh : lc.home v.id = none) (hi : inertTy (lc.ty v.id) = true)
    (h : stepLoc env lc s v = .ok s') : s' = s := by
  obtain ⟨argv, r, -, -, rfl⟩ := stepLoc_ok_eval (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) h
  rw [clobber_none (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) ht (by rw [hop]; rfl)]
  unfold LocState.write
  rw [hh]
  cases hty : lc.ty v.id <;> simp_all [inertTy]

/-- `MOVDload [off] a mem` without a symbol: the 8-byte load at `a + off` (`poison` if `a` is not
an address). -/
theorem stepLoc_load (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64MOVDload) {a0 a1 : ID} (ha : v.args = #[a0, a1]) (haux : v.aux = none)
    {mm : Mem} (hm : s.read lc a1 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id
        (((Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt)).elim .poison
          (Arm64.loadN (lc.ty v.id) 8 false mm)).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmap
  change [a0, a1].mapM (s.read lc) = _ at hmap
  rw [mapM_two] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
    rw [hx, hm] at hmap; cases hmap
    cases hn : nilFaults true lc.ctx v [x, .mem mm] with
    | some m =>
      have he : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) = .panic .nilDeref m := by
        unfold evalOpL arm64Op; rw [hop, hn]; rfl
      rw [he] at hr; cases hr
    | none =>
      have he : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
          .ok ((symAddr lc.ctx v x).elim .poison (Arm64.loadN (lc.ty v.id) 8 false mm)) := by
        unfold evalOpL arm64Op; rw [hop, hn]; rfl
      rw [he, symAddr_noAux haux] at hr; cases hr
      exact ⟨x, rfl, rfl⟩

/-- `MOVDstore [off] a x mem` without a symbol: the 8-byte store of `x` at `a + off`, which
succeeded. -/
theorem stepLoc_store (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64MOVDstore) {a0 a1 a2 : ID} (ha : v.args = #[a0, a1, a2])
    (haux : v.aux = none) {mm : Mem} (hm : s.read lc a2 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x y p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧
      Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p ∧
      mm.write p (Arm64.storeBytes 8 y) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmap
  change [a0, a1, a2].mapM (s.read lc) = _ at hmap
  rw [mapM_three] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
  cases hy : s.read lc a1 with
  | panic e m => rw [hx, hy] at hmap; cases hmap
  | stuck msg => rw [hx, hy] at hmap; cases hmap
  | ok y =>
    rw [hx, hy, hm] at hmap; cases hmap
    cases hn : nilFaults true lc.ctx v [x, y, .mem mm] with
    | some m =>
      have he : evalOpL true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m := by
        unfold evalOpL arm64Op; rw [hop, hn]; rfl
      rw [he] at hr; cases hr
    | none =>
      obtain ⟨w, m1, m2, he⟩ : ∃ w m1 m2,
          evalOpL true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
            match symAddr lc.ctx v x with
            | some p => writeRes w (Arm64.storeN 8 p y mm)
            | none =>
              if [x, y, Val.mem mm].any (fun | .poison => true | _ => false) then .stuck m1
              else .stuck m2 :=
        ⟨_, _, _, by unfold evalOpL arm64Op; rw [hop, hn]; rfl⟩
      rw [symAddr_noAux haux] at he
      cases hp : Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) with
      | none =>
        rw [hp] at he; rw [he] at hr
        dsimp only at hr
        split at hr <;> cases hr
      | some p =>
        rw [hp] at he; rw [he] at hr
        change writeRes _ (mm.write p (Arm64.storeBytes 8 y)) = _ at hr
        cases hw : mm.write p (Arm64.storeBytes 8 y) with
        | none => rw [hw] at hr; cases hr
        | some mm' =>
          rw [hw] at hr; cases hr
          exact ⟨x, y, p, mm', rfl, rfl, hp, hw, rfl⟩

end GoFV.Proof.Gen
