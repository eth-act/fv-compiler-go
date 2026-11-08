import GoFV.Proof.Gen.Step
import GoFV.Gen.Check3

/-!
# `stepLoc` on each op of slice G3 (`docs/plans/proofs3.md` §4)

What a successful `stepLoc` does for each op slice G3 adds (`vkind3`), in a lowered function for a
value with no temporary register, as `Step.lean` does for G1's: the pure ops (the extensions,
`ANDconst`, `SLLconst`, `SRLconst`, `UBFX`, `CMPW`, `CMPWconst`) are `Arm64.evalPure` on the
arguments read from their homes (`stepLoc_pure3`); the loads and stores of `loadOp?`/`storeOp?`
(narrow, or `MOVD`, with or without a symbol) are `arm64Op`'s `n`-byte load and store at
`symAddr` (`stepLoc_loadN`, `stepLoc_storeN`); `SB` writes its value (`stepLoc_sb`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_two {a b : ID} :
    [a, b].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => .ok [x, y] := rfl

private theorem mapM_three {a b c : ID} :
    [a, b, c].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        .ok [x, y, z] := rfl

/-- The ops of an extension (`extOp?`). -/
theorem extOp?_op {op : Op} {as : GoFV.Asm.As} {w : Nat} {sg : Bool}
    (h : extOp? op = some (as, w, sg)) :
    op = .ARM64MOVBreg ∨ op = .ARM64MOVBUreg ∨ op = .ARM64MOVHreg ∨ op = .ARM64MOVHUreg ∨
      op = .ARM64MOVWreg ∨ op = .ARM64MOVWUreg := by
  unfold extOp? at h
  split at h <;> (try cases h) <;> simp

/-- The ops, bytes and sign extension of a load (`loadOp?`). -/
theorem loadOp?_op {op : Op} {as : GoFV.Asm.As} {n : Nat} {sg : Bool}
    (h : loadOp? op = some (as, n, sg)) :
    (op = .ARM64MOVDload ∧ n = 8 ∧ sg = false) ∨ (op = .ARM64MOVBload ∧ n = 1 ∧ sg = true) ∨
      (op = .ARM64MOVBUload ∧ n = 1 ∧ sg = false) ∨ (op = .ARM64MOVHload ∧ n = 2 ∧ sg = true) ∨
      (op = .ARM64MOVHUload ∧ n = 2 ∧ sg = false) ∨ (op = .ARM64MOVWload ∧ n = 4 ∧ sg = true) ∨
      (op = .ARM64MOVWUload ∧ n = 4 ∧ sg = false) := by
  unfold loadOp? at h
  split at h
  · cases h
    exact .inl ⟨beq_iff_eq.mp ‹_›, rfl, rfl⟩
  · unfold narrowLoad? at h
    split at h <;> (try cases h) <;> simp

/-- The ops and bytes of a store (`storeOp?`). -/
theorem storeOp?_op {op : Op} {as : GoFV.Asm.As} {n : Nat} (h : storeOp? op = some (as, n)) :
    (op = .ARM64MOVDstore ∧ n = 8) ∨ (op = .ARM64MOVBstore ∧ n = 1) ∨
      (op = .ARM64MOVHstore ∧ n = 2) ∨ (op = .ARM64MOVWstore ∧ n = 4) := by
  unfold storeOp? at h
  split at h
  · cases h
    exact .inl ⟨beq_iff_eq.mp ‹_›, rfl⟩
  · unfold narrowStore? at h
    split at h <;> (try cases h) <;> simp

/-- The pure arm64 ops of G3: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_pure3 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64MOVBreg ∨ v.op = .ARM64MOVBUreg ∨ v.op = .ARM64MOVHreg ∨
      v.op = .ARM64MOVHUreg ∨ v.op = .ARM64MOVWreg ∨ v.op = .ARM64MOVWUreg ∨
      v.op = .ARM64ANDconst ∨ v.op = .ARM64SLLconst ∨ v.op = .ARM64SRLconst ∨ v.op = .ARM64UBFX ∨
      v.op = .ARM64CMPW ∨ v.op = .ARM64CMPWconst)
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL (lc.ty v.id)) := by
  rcases hop with hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv) := by
      unfold evalOpL; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨argv, hm, rfl⟩

/-- An extension (`extOp?`): `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_ext (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {as : GoFV.Asm.As} {w : Nat} {sg : Bool} (hop : extOp? v.op = some (as, w, sg))
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL (lc.ty v.id)) := by
  rcases extOp?_op hop with h' | h' | h' | h' | h' | h' <;>
    exact stepLoc_pure3 hl ht (by simp only [h', true_or, or_true]) h

/-- A load whose `arm64Op` is the `n`-byte load (`ld n sg`). -/
private theorem loadN_core {n : Nat} {sg : Bool} (hl : lc.ctx.f.lowered = true)
    (ht : (lc.temps[v.id]?).join = none) (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg)
    (h2 : v.op ≠ .StoreReg) (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (hc : v.op.regInfo.clobbers.isEmpty = true) (hc0 : v.op.regInfo.clobbersArg0 = false)
    (hc1 : v.op.regInfo.clobbersArg1 = false) (hf : v.op.clobberFlags = false)
    (hev : ∀ argv, evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      arm64Op true env lc.ctx s.fr v argv (lc.ty v.id))
    (hld : ∀ x mm, nilFaults true lc.ctx v [x, .mem mm] = none →
      arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
        .ok ((symAddr lc.ctx v x).elim .poison (Arm64.loadN (lc.ty v.id) n sg mm)))
    {a0 a1 : ID} (ha : v.args = #[a0, a1]) {mm : Mem} (hm : s.read lc a1 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id
        (((symAddr lc.ctx v x).elim .poison (Arm64.loadN (lc.ty v.id) n sg mm)).retypeL
          (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht hne h1 h2 h3 h4 hc hc0 hc1 hf h
  rw [ha] at hmap
  change [a0, a1].mapM (s.read lc) = _ at hmap
  rw [mapM_two] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
    rw [hx, hm] at hmap; cases hmap
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) = .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      rw [hld x mm hn] at hr; cases hr
      exact ⟨x, rfl, rfl⟩

/-- A load of `loadOp?` (`MOV{D,B,BU,H,HU,W,WU}load [off] {sym} a mem`, with or without a
symbol): the `n`-byte load at `symAddr` (`poison` if there is none). -/
theorem stepLoc_loadN (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {as : GoFV.Asm.As} {n : Nat} {sg : Bool} (hop : loadOp? v.op = some (as, n, sg))
    {a0 a1 : ID} (ha : v.args = #[a0, a1]) {mm : Mem} (hm : s.read lc a1 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id
        (((symAddr lc.ctx v x).elim .poison (Arm64.loadN (lc.ty v.id) n sg mm)).retypeL
          (lc.ty v.id)) := by
  rcases loadOp?_op hop with ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ |
    ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ <;>
  exact loadN_core hl ht (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
    (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; rfl) (by rw [ho]; rfl)
    (by rw [ho]; rfl) (by rw [ho]; rfl) (fun _ => by unfold evalOpL; rw [ho]; rfl)
    (fun _ _ hn => by unfold arm64Op; rw [hn, ho]) ha hm h

/-- A store whose `arm64Op` is the `n`-byte store (`st n`). -/
private theorem storeN_core {n : Nat} (hl : lc.ctx.f.lowered = true)
    (ht : (lc.temps[v.id]?).join = none) (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg)
    (h2 : v.op ≠ .StoreReg) (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (hc : v.op.regInfo.clobbers.isEmpty = true) (hc0 : v.op.regInfo.clobbersArg0 = false)
    (hc1 : v.op.regInfo.clobbersArg1 = false) (hf : v.op.clobberFlags = false)
    (hev : ∀ argv, evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      arm64Op true env lc.ctx s.fr v argv (lc.ty v.id))
    (hst : ∀ x y mm, nilFaults true lc.ctx v [x, y, .mem mm] = none → ∃ w m1 m2,
      arm64Op true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
        match symAddr lc.ctx v x with
        | some p => writeRes w (Arm64.storeN n p y mm)
        | none =>
          if [x, y, Val.mem mm].any (fun | .poison => true | _ => false) then .stuck m1
          else .stuck m2)
    {a0 a1 a2 : ID} (ha : v.args = #[a0, a1, a2]) {mm : Mem} (hm : s.read lc a2 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x y p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ symAddr lc.ctx v x = some p ∧
      mm.write p (Arm64.storeBytes n y) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht hne h1 h2 h3 h4 hc hc0 hc1 hf h
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
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, y, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      obtain ⟨w, m1, m2, he⟩ := hst x y mm hn
      cases hp : symAddr lc.ctx v x with
      | none =>
        rw [hp] at he; rw [he] at hr
        dsimp only at hr
        split at hr <;> cases hr
      | some p =>
        rw [hp] at he; rw [he] at hr
        change writeRes _ (mm.write p (Arm64.storeBytes n y)) = _ at hr
        cases hw : mm.write p (Arm64.storeBytes n y) with
        | none => rw [hw] at hr; cases hr
        | some mm' =>
          rw [hw] at hr; cases hr
          exact ⟨x, y, p, mm', rfl, rfl, hp, hw, rfl⟩

/-- A store of `storeOp?` (`MOV{D,B,H,W}store [off] {sym} a x mem`, with or without a symbol):
the `n`-byte store of `x` at `symAddr`, which succeeded. -/
theorem stepLoc_storeN (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {as : GoFV.Asm.As} {n : Nat} (hop : storeOp? v.op = some (as, n)) {a0 a1 a2 : ID}
    (ha : v.args = #[a0, a1, a2]) {mm : Mem} (hm : s.read lc a2 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x y p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ symAddr lc.ctx v x = some p ∧
      mm.write p (Arm64.storeBytes n y) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  rcases storeOp?_op hop with ⟨ho, rfl⟩ | ⟨ho, rfl⟩ | ⟨ho, rfl⟩ | ⟨ho, rfl⟩ <;>
  exact storeN_core hl ht (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
    (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; rfl) (by rw [ho]; rfl)
    (by rw [ho]; rfl) (by rw [ho]; rfl) (fun _ => by unfold evalOpL; rw [ho]; rfl)
    (fun _ _ _ hn => ⟨_, _, _, by unfold arm64Op; rw [hn, ho]; rfl⟩) ha hm h

/-- `SB`: whatever it evaluates to, written to its home at its shape. -/
theorem stepLoc_sb (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .SB) (h : stepLoc env lc s v = .ok s') :
    ∃ x : Val, s' = s.write lc v.id (x.retypeL (lc.ty v.id)) := by
  obtain ⟨-, r, -, -, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  exact ⟨r, rfl⟩

end GoFV.Proof.Gen
