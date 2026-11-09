import GoFV.Proof.Gen.Step3
import GoFV.Gen.Check4

variable [GoFV.SSA.Sem.Addrs]

/-!
# `stepLoc` on each op of slice G4 (`docs/plans/proofs3.md` §4)

What a successful `stepLoc` does for each op slice G4 adds (`vkind4`), in a lowered function for a
value with no temporary register, as `Step3.lean` does for G3's: the pair load `LDP` is `arm64Op`'s
`ldPair 8 false`, the two 8-byte loads at `pairAddr` (`stepLoc_ldp`); the pair store `STP` is
`stPair 8`, the two 8-byte writes at `pairAddr`, which succeeded (`stepLoc_stp`); `Select0` and
`Select1` take a component of their argument (`stepLoc_select`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_two' {a b : ID} :
    [a, b].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => .ok [x, y] := rfl

private theorem mapM_four {a b c d : ID} :
    [a, b, c, d].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        (s.read lc d).bind fun w => .ok [x, y, z, w] := rfl

/-- `LDP [off] a mem`: the two 8-byte loads at `pairAddr` (`poison` if there is none). -/
theorem stepLoc_ldp (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64LDP) {a0 a1 : ID} (ha : v.args = #[a0, a1]) {mm : Mem}
    (hm : s.read lc a1 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id
        (((pairAddr lc.ctx v 8 x).elim .poison fun pq =>
          Arm64.loadPair (lc.ty v.id) 8 false mm pq.1 pq.2).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmap
  change [a0, a1].mapM (s.read lc) = _ at hmap
  rw [mapM_two'] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
    rw [hx, hm] at hmap; cases hmap
    have hev : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
        arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) := by
      unfold evalOpL; rw [hop]; rfl
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) = .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
          .ok ((pairAddr lc.ctx v 8 x).elim .poison fun pq =>
            Arm64.loadPair (lc.ty v.id) 8 false mm pq.1 pq.2) := by
        unfold arm64Op; rw [hn, hop]
      rw [he] at hr; cases hr
      exact ⟨x, rfl, rfl⟩

/-- `STP [off] a x y mem`: the 8-byte writes of `x` and `y` at `pairAddr`, in that order, which
succeeded. -/
theorem stepLoc_stp (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64STP) {a0 a1 a2 a3 : ID} (ha : v.args = #[a0, a1, a2, a3]) {mm : Mem}
    (hm : s.read lc a3 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y z p q mm1 mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ s.read lc a2 = .ok z ∧
      pairAddr lc.ctx v 8 x = some (p, q) ∧ mm.write p (Arm64.storeBytes 8 y) = some mm1 ∧
      mm1.write q (Arm64.storeBytes 8 z) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmap
  change [a0, a1, a2, a3].mapM (s.read lc) = _ at hmap
  rw [mapM_four] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
  cases hy : s.read lc a1 with
  | panic e m => rw [hx, hy] at hmap; cases hmap
  | stuck msg => rw [hx, hy] at hmap; cases hmap
  | ok y =>
  cases hz : s.read lc a2 with
  | panic e m => rw [hx, hy, hz] at hmap; cases hmap
  | stuck msg => rw [hx, hy, hz] at hmap; cases hmap
  | ok z =>
    rw [hx, hy, hz, hm] at hmap; cases hmap
    have hev : evalOpL true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
        arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) := by
      unfold evalOpL; rw [hop]; rfl
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, y, z, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      cases hpq : pairAddr lc.ctx v 8 x with
      | none =>
        have he : ∃ m1 m2, arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
            if [x, y, z, Val.mem mm].any (fun | .poison => true | _ => false) then .stuck m1
            else .stuck m2 :=
          ⟨_, _, by unfold arm64Op; rw [hn, hop]; simp only [hpq]; rfl⟩
        obtain ⟨m1, m2, he⟩ := he
        rw [he] at hr
        split at hr <;> cases hr
      | some pq =>
        obtain ⟨p, q⟩ := pq
        have he : ∃ w, arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
            writeRes w (Arm64.storePair 8 p q y z mm) :=
          ⟨_, by unfold arm64Op; rw [hn, hop]; simp only [hpq]; rfl⟩
        obtain ⟨w, he⟩ := he
        rw [he] at hr
        cases hw1 : mm.write p (Arm64.storeBytes 8 y) with
        | none =>
          simp only [Arm64.storePair, hw1, Option.bind_none] at hr
          cases hr
        | some mm1 =>
          cases hw2 : mm1.write q (Arm64.storeBytes 8 z) with
          | none =>
            simp only [Arm64.storePair, hw1, hw2, Option.bind_some] at hr
            cases hr
          | some mm' =>
            simp only [Arm64.storePair, hw1, hw2, Option.bind_some] at hr
            cases hr
            exact ⟨x, y, z, p, q, mm1, mm', rfl, rfl, rfl, hpq, hw1, hw2, rfl⟩

/-- `Select0`/`Select1` of one argument whose evaluation is component `i` of it. -/
private theorem select_core {i : Nat} (hl : lc.ctx.f.lowered = true)
    (ht : (lc.temps[v.id]?).join = none) (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg)
    (h2 : v.op ≠ .StoreReg) (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (hc : v.op.regInfo.clobbers.isEmpty = true) (hc0 : v.op.regInfo.clobbersArg0 = false)
    (hc1 : v.op.regInfo.clobbersArg1 = false) (hf : v.op.clobberFlags = false)
    (hev : ∀ x, evalOpL true env lc.ctx s.fr v [x] (lc.ty v.id) = .ok (Tuple.select i [x]))
    {a : ID} (ha : v.args = #[a]) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a = .ok x ∧
      s' = s.write lc v.id ((Tuple.select i [x]).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht hne h1 h2 h3 h4 hc hc0 hc1 hf h
  rw [ha] at hm
  change ((s.read lc a).bind fun x => Res.ok [x]) = _ at hm
  cases hx : s.read lc a with
  | ok x =>
    rw [hx] at hm; cases hm
    rw [hev] at hr; cases hr
    exact ⟨_, rfl, rfl⟩
  | panic e m => rw [hx] at hm; cases hm
  | stuck msg => rw [hx] at hm; cases hm

/-- `Select0`/`Select1` of one argument: its component `i`. -/
theorem stepLoc_select (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {i : Nat} (hop : v.op = .Select0 ∧ i = 0 ∨ v.op = .Select1 ∧ i = 1) {a : ID}
    (ha : v.args = #[a]) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a = .ok x ∧
      s' = s.write lc v.id ((Tuple.select i [x]).retypeL (lc.ty v.id)) := by
  rcases hop with ⟨hop, rfl⟩ | ⟨hop, rfl⟩
  · exact select_core hl ht (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; rfl) (by rw [hop]; rfl)
      (by rw [hop]; rfl) (by rw [hop]; rfl)
      (fun x => by unfold evalOpL evalOp frameVal; rw [hop]; rfl) ha h
  · exact select_core hl ht (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; rfl) (by rw [hop]; rfl)
      (by rw [hop]; rfl) (by rw [hop]; rfl)
      (fun x => by unfold evalOpL evalOp frameVal; rw [hop]; rfl) ha h

end GoFV.Proof.Gen
