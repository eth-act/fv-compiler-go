import GoFV.Proof.Gen.G1
import GoFV.Proof.Gen.Step4
import GoFV.Gen.Check5

variable [GoFV.SSA.Sem.Addrs]

/-!
# `stepLoc` on the memory markers of slice G5 (`docs/plans/proofs3.md` §4)

The memory markers (`markOp?`: `VarDef`, `VarLive`, `KeepAlive`, `WBend`) are Phase 1's memory
roots (`memRoot`): with the memory argument last, `VarDef {x}` makes a `PAUTO` `x`'s block
poison and keeps the memory for any other `x` (`varDefMem`), `VarLive` and `KeepAlive` keep the
memory, `WBend` frees the write-barrier buffer
(`stepLoc_mark`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

theorem markOp?_op {op : Op} {n : Nat} (h : markOp? op = some n) :
    (op = .VarDef ∧ n = 1) ∨ (op = .VarLive ∧ n = 1) ∨ (op = .WBend ∧ n = 1) ∨
      (op = .KeepAlive ∧ n = 2) := by
  unfold markOp? at h
  split at h <;> (try cases h) <;> simp_all

/-- A memory marker run by `memRoot`: the new memory, written to the value's home. -/
private theorem mark_core (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .VarDef ∨ v.op = .VarLive ∨ v.op = .WBend ∨ v.op = .KeepAlive)
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv r, v.args.toList.mapM (s.read lc) = .ok argv ∧ memRoot lc.ctx v argv = .ok r ∧
      s' = s.write lc v.id (r.retypeL (lc.ty v.id)) := by
  rcases hop with hop | hop | hop | hop <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) = memRoot lc.ctx v argv := by
      unfold evalOpL evalOp; rw [hop]; rfl
    rw [he] at hr
    exact ⟨argv, r, hm, hr, rfl⟩

/-- A memory marker (`markOp?`) with its memory argument last, of the memory shape with no home:
the memory becomes `VarDef`'s poisoned block, stays, or loses the write-barrier buffer. -/
theorem stepLoc_mark (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {n : Nat} (hop : markOp? v.op = some n) (hsz : v.args.size = n)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none) {a : ID} {mm : Mem}
    (ha : v.args[n - 1]? = some a) (hm : s.read lc a = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ mm', s' = { s with mem := .mem mm' } ∧
      (mm' = mm ∨ (∃ b, mm' = mm.poisonBlock b) ∨ mm' = mm.free .wbuf) := by
  have hop' : v.op = .VarDef ∨ v.op = .VarLive ∨ v.op = .WBend ∨ v.op = .KeepAlive := by
    rcases markOp?_op hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  obtain ⟨argv, r, hmap, hr, rfl⟩ := mark_core hl ht hop' h
  rw [write_mem hhn hmt, memTy_eq hmt]
  rcases markOp?_op hop with ⟨hv, rfl⟩ | ⟨hv, rfl⟩ | ⟨hv, rfl⟩ | ⟨hv, rfl⟩
  · rw [arr1 hsz ha] at hmap
    change ((s.read lc a).bind fun x => Res.ok [x]) = _ at hmap
    rw [hm] at hmap; cases hmap
    unfold memRoot at hr; rw [hv] at hr; simp only at hr
    split at hr
    · cases hr
      refine ⟨_, rfl, ?_⟩
      unfold varDefMem
      split
      · exact .inr (.inl ⟨_, rfl⟩)
      · exact .inl rfl
    · cases hr
  · rw [arr1 hsz ha] at hmap
    change ((s.read lc a).bind fun x => Res.ok [x]) = _ at hmap
    rw [hm] at hmap; cases hmap
    unfold memRoot at hr; rw [hv] at hr; simp only at hr
    cases hr; exact ⟨_, rfl, .inl rfl⟩
  · rw [arr1 hsz ha] at hmap
    change ((s.read lc a).bind fun x => Res.ok [x]) = _ at hmap
    rw [hm] at hmap; cases hmap
    unfold memRoot at hr; rw [hv] at hr; simp only at hr
    cases hr; exact ⟨_, rfl, .inr (.inr rfl)⟩
  · obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
      ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
    rw [arr2 hsz ha0 ha] at hmap
    change ((s.read lc a0).bind fun x => (s.read lc a).bind fun y => Res.ok [x, y]) = _ at hmap
    cases hx : s.read lc a0 with
    | ok x =>
      rw [hx, hm] at hmap; cases hmap
      unfold memRoot at hr; rw [hv] at hr; simp only at hr
      cases hr; exact ⟨_, rfl, .inl rfl⟩
    | panic e m => rw [hx] at hmap; cases hmap
    | stuck msg => rw [hx] at hmap; cases hmap

end GoFV.Proof.Gen
