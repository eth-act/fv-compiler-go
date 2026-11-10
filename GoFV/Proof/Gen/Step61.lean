import GoFV.Proof.Gen.G38
import GoFV.Proof.Gen.Spec61a

variable [GoFV.SSA.Sem.Addrs]

/-!
# `runLoc` on slice G61's group A (`docs/plans/proofs3.md` §4)

A lowered atomic of group A runs as the generic atomic it lowers (`Arm64.atomicOf`, `arm64Op`'s
last arm, `atomicRoot`) after its clobbers (`LocState.clobber`: the temporary of `andL`/`orL` and,
for a compare-and-swap, the flags become `poison`). `stepLoc_rmw61`: a read-modify-write of family
`f` is `Atomic.rmw` of kind `kindF f` at the location shape `.int (widthN n)`; `stepLoc_cas61`: a
compare-and-swap is `Atomic.cas` at width `widthN n`, which either writes `new` and returns `true`
(the location held `old`) or keeps the memory and returns `false`. `write_atom61` writes the
result tuple to the value's home `(Rd, -)`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

/-- The read-modify-write `Atomic.Kind` of a family of group A (not a compare-and-swap). -/
def kindF (f : AtomF61) : Atomic.Kind :=
  match f with
  | .xchg | .xchgV => .exchange
  | .add | .addV => .add
  | .andL | .andV => .andOld
  | _ => .orOld

/-- The integer width of an `n`-byte location (`n` = 8, 4 or 1). -/
def widthN (n : Nat) : Width := if n = 8 then .w64 else if n = 4 then .w32 else .w8

/-- What an op of group A is: no `Phi`, register move, nil check, bounds check or entry value; it
clobbers no register but (with no temporary) nothing, and the flags exactly when a
compare-and-swap; its bytes; the generic atomic it runs as (`kindF f` at `.int (widthN n)`, or a
compare-and-swap at `widthN n`). -/
theorem atom61?_facts {op : Op} {f : AtomF61} {n : Nat} (h : atom61? op = some (f, n)) :
    op ≠ .Phi ∧ op ≠ .LoadReg ∧ op ≠ .StoreReg ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64MOVDnop ∧
      op.regInfo.clobbers.isEmpty = true ∧ op.regInfo.clobbersArg0 = false ∧
      op.regInfo.clobbersArg1 = false ∧ op.clobberFlags = (f == .cas || f == .casV) ∧
      op ≠ .ARM64LoweredNilCheck ∧ pbOp op = false ∧ entryOp24 op = false ∧
      (n = 8 ∨ n = 4 ∨ n = 1) ∧ (widthN n).bytes = n ∧
      (f = .addV → n ≠ 1) ∧ ((f = .cas ∨ f = .casV ∨ f = .add) → n ≠ 1) ∧
      ∃ g, Arm64.atomicOf op = some g ∧
        ((f ≠ .cas ∧ f ≠ .casV ∧ Atomic.info? g = some (kindF f, .int (widthN n))) ∨
         ((f = .cas ∨ f = .casV) ∧ Atomic.info? g = none ∧ Atomic.casWidth? g = some (widthN n))) := by
  unfold atom61? at h
  split at h
  all_goals first
    | (cases h; exact ⟨nofun, nofun, nofun, nofun, nofun, by decide, by decide, by decide,
        by decide, nofun, rfl, rfl, by decide, by decide, by decide, by decide, _, rfl,
        .inl ⟨nofun, nofun, rfl⟩⟩)
    | (cases h; exact ⟨nofun, nofun, nofun, nofun, nofun, by decide, by decide, by decide,
        by decide, nofun, rfl, rfl, by decide, by decide, by decide, by decide, _, rfl,
        .inr ⟨by decide, rfl, rfl⟩⟩)
    | cases h

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- An op of group A is evaluated by `arm64Op`. -/
theorem evalOpL_atom61 {f : AtomF61} {n : Nat} (hop : atom61? v.op = some (f, n))
    {ctx : Ctx} {fr : Frame} {argv : List Val} {ty : Ty} :
    evalOpL true env ctx fr v argv ty = arm64Op true env ctx fr v argv ty := by
  unfold evalOpL
  generalize v.op = o at hop ⊢
  unfold atom61? at hop
  split at hop
  all_goals first | rfl | cases hop

/-- `arm64Op` of an op of group A without a nil fault: the generic atomic. -/
theorem arm64Op_atom61 {f : AtomF61} {n : Nat} (hop : atom61? v.op = some (f, n)) {g : Op}
    (hg : Arm64.atomicOf v.op = some g) {ctx : Ctx} {fr : Frame} {argv : List Val} {ty : Ty}
    (hn : nilFaults true ctx v argv = none) :
    arm64Op true env ctx fr v argv ty = atomicRoot { v with op := g } (atomicArgs g argv) := by
  unfold arm64Op
  rw [hn]
  generalize v.op = o at hop hg ⊢
  unfold atom61? at hop
  split at hop
  all_goals first | (simp only [Arm64.atomicOf, Option.some.injEq] at hg; subst hg; rfl) | cases hop

private theorem mapM_three61 {a b c : ID} :
    [a, b, c].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        .ok [x, y, z] := rfl

private theorem mapM_four61 {a b c d : ID} :
    [a, b, c, d].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        (s.read lc d).bind fun u => .ok [x, y, z, u] := rfl

/-- A read-modify-write of group A (family `f`, not a compare-and-swap, `n` bytes) that steps: its
clobbers, then `Atomic.rmw` of kind `kindF f` on the `.int (widthN n)` location at the pointer
word of its first argument, the operand fitted to that shape. -/
theorem stepLoc_rmw61 (hl : lc.ctx.f.lowered = true) {f : AtomF61} {n : Nat}
    (hop : atom61? v.op = some (f, n)) (hf1 : f ≠ .cas) (hf2 : f ≠ .casV) {a0 a1 a2 : ID}
    (ha : v.args = #[a0, a1, a2]) {mm : Mem} (hm : s.read lc a2 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x y p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ x.asPtrWord = some p ∧
      Atomic.aligned p (Ty.int (widthN n)).size = true ∧
      mm.write p (encode (.int (widthN n)) (Atomic.step (kindF f) (widthN n)
        (mm.load (.int (widthN n)) p) (fitPiece (.int (widthN n)) y)).1) = some mm' ∧
      s' = (s.clobber lc v).write lc v.id ((Atomic.result (Atomic.step (kindF f) (widthN n)
        (mm.load (.int (widthN n)) p) (fitPiece (.int (widthN n)) y)).2 mm').retypeL
        (lc.ty v.id)) := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -, -, -, -, -, -, -, g, hg, hk⟩ := atom61?_facts hop
  have hinfo : Atomic.info? g = some (kindF f, .int (widthN n)) := by
    rcases hk with ⟨-, -, h⟩ | ⟨hc, -⟩
    · exact h
    · rcases hc with rfl | rfl <;> contradiction
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_ok_eval h1 h2 h3 h4 h5 h
  rw [ha] at hmv
  change [a0, a1, a2].mapM (s.read lc) = _ at hmv
  rw [mapM_three61] at hmv
  cases hx : s.read lc a0 with
  | panic e m0 => rw [hx] at hmv; cases hmv
  | stuck msg => rw [hx] at hmv; cases hmv
  | ok x =>
  cases hy : s.read lc a1 with
  | panic e m0 => rw [hx, hy] at hmv; cases hmv
  | stuck msg => rw [hx, hy] at hmv; cases hmv
  | ok y =>
    rw [hx, hy, hm] at hmv
    cases hmv
    rw [evalOpL_atom61 hop] at hr
    cases hn : nilFaults true lc.ctx v [x, y, .mem mm] with
    | some m0 =>
      have he : arm64Op true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m0 := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      rw [arm64Op_atom61 hop hg hn] at hr
      have hinfo' : Atomic.info? ({ v with op := g } : Value).op =
          some (kindF f, .int (widthN n)) := hinfo
      simp only [atomicArgs, hinfo, atomicRoot] at hr
      cases hp : x.asPtrWord with
      | none => simp [Atomic.rmwRoot, hp, Atomic.unmodelled] at hr
      | some p =>
        simp only [Atomic.rmwRoot, hp, hinfo', Atomic.rmw, Atomic.width] at hr
        split at hr
        · rename_i hal
          cases hw : mm.write p (encode (.int (widthN n)) (Atomic.step (kindF f) (widthN n)
              (mm.load (.int (widthN n)) p) (fitPiece (.int (widthN n)) y)).1) with
          | none => rw [hw] at hr; cases hr
          | some mm' =>
            rw [hw] at hr; cases hr
            exact ⟨x, y, p, mm', rfl, rfl, hp, hal, hw, by rw [lmode_retype hl]⟩
        · cases hr

/-- A compare-and-swap of group A (`n` bytes) that steps: its clobbers, then `Atomic.cas` at
width `widthN n`: the location's integer `cur` and the fitted `old` are integers; when they are
equal, `new` (fitted) is written and the result is `true`, else the memory stays and the result
is `false`. -/
theorem stepLoc_cas61 (hl : lc.ctx.f.lowered = true) {f : AtomF61} {n : Nat}
    (hop : atom61? v.op = some (f, n)) (hf : f = .cas ∨ f = .casV) {a0 a1 a2 a3 : ID}
    (ha : v.args = #[a0, a1, a2, a3]) {mm : Mem} (hm : s.read lc a3 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x yo yn p cur old, s.read lc a0 = .ok x ∧ s.read lc a1 = .ok yo ∧ s.read lc a2 = .ok yn ∧
      x.asPtrWord = some p ∧ Atomic.aligned p (widthN n).bytes = true ∧
      (mm.load (.int (widthN n)) p).asInt (widthN n) = some cur ∧
      (fitPiece (.int (widthN n)) yo).asInt (widthN n) = some old ∧
      ((cur = old ∧ ∃ mm', mm.write p (encode (.int (widthN n)) (fitPiece (.int (widthN n)) yn)) =
          some mm' ∧ s' = (s.clobber lc v).write lc v.id
            ((Val.tuple [.bool true, .mem mm']).retypeL (lc.ty v.id))) ∨
       (cur ≠ old ∧ s' = (s.clobber lc v).write lc v.id
            ((Val.tuple [.bool false, .mem mm]).retypeL (lc.ty v.id)))) := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -, -, -, -, -, -, -, g, hg, hk⟩ := atom61?_facts hop
  have hinfo : Atomic.info? g = none ∧ Atomic.casWidth? g = some (widthN n) := by
    rcases hk with ⟨hc1, hc2, -⟩ | ⟨-, h⟩
    · rcases hf with rfl | rfl <;> contradiction
    · exact h
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_ok_eval h1 h2 h3 h4 h5 h
  rw [ha] at hmv
  change [a0, a1, a2, a3].mapM (s.read lc) = _ at hmv
  rw [mapM_four61] at hmv
  cases hx : s.read lc a0 with
  | panic e m0 => rw [hx] at hmv; cases hmv
  | stuck msg => rw [hx] at hmv; cases hmv
  | ok x =>
  cases hyo : s.read lc a1 with
  | panic e m0 => rw [hx, hyo] at hmv; cases hmv
  | stuck msg => rw [hx, hyo] at hmv; cases hmv
  | ok yo =>
  cases hyn : s.read lc a2 with
  | panic e m0 => rw [hx, hyo, hyn] at hmv; cases hmv
  | stuck msg => rw [hx, hyo, hyn] at hmv; cases hmv
  | ok yn =>
    rw [hx, hyo, hyn, hm] at hmv
    cases hmv
    rw [evalOpL_atom61 hop] at hr
    cases hn : nilFaults true lc.ctx v [x, yo, yn, .mem mm] with
    | some m0 =>
      have he : arm64Op true env lc.ctx s.fr v [x, yo, yn, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m0 := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      rw [arm64Op_atom61 hop hg hn] at hr
      have hcw : Atomic.casWidth? ({ v with op := g } : Value).op = some (widthN n) := hinfo.2
      simp only [atomicArgs, hinfo.1, hinfo.2, atomicRoot] at hr
      cases hp : x.asPtrWord with
      | none => simp [Atomic.casRoot, hp, Atomic.unmodelled] at hr
      | some p =>
        simp only [Atomic.casRoot, hp, hcw, Atomic.cas] at hr
        split at hr
        · rename_i hal
          split at hr
          · rename_i cur old hcur hold
            refine ⟨x, yo, yn, p, cur, old, rfl, rfl, rfl, hp, hal, hcur, hold, ?_⟩
            split at hr
            · rename_i heq
              cases hw : mm.write p (encode (.int (widthN n)) (fitPiece (.int (widthN n)) yn)) with
              | none => rw [hw] at hr; cases hr
              | some mm' =>
                rw [hw] at hr; cases hr
                exact .inl ⟨heq, mm', rfl, by rw [lmode_retype hl]⟩
            · rename_i hne
              cases hr
              exact .inr ⟨hne, by rw [lmode_retype hl]⟩
          · cases hr
        · cases hr

/-- The result tuple of a value of group A written to its home `(r, -)`: the component to `r`, the
memory to the state's. -/
theorem write_atom61 {id r : Nat} {t0 : Ty} {y : Val} {mm' : Mem}
    (hh : lc.home id = some (.pair (some r) none)) (hty : lc.ty id = .tuple [t0, .mem])
    (hc : (cls t0).isSome = true) :
    s.write lc id (.tuple [y, .mem mm']) = { s.setReg r y with mem := .mem mm' } := by
  unfold LocState.write
  simp only [hh, hty, Option.map_some, Option.getD_some, Location.regList, Val.partsOf]
  rw [writeParts_reg hc]
  simp only [LocState.writeParts]

end Steps

end GoFV.Proof.Gen
