import GoFV.Proof.RoImage
import GoFV.Proof.MemInvL
import GoFV.Proof.EvalOpLDispatch
import GoFV.Gen.MemTyL

variable [GoFV.SSA.Sem.Addrs]

/-!
# The memories `runLoc` holds (`docs/plans/proofs3.md` §10)

A predicate `P` on memories that writes, `set`s of frame blocks and of the write-barrier buffer
keep (`MemInv.MemPred` and `hwb`) and the environment's contracts keep (`MemInv.ContractsOK`)
holds of every memory `runLoc`'s state holds (`LocMems`: its memory, flags, registers, slots,
staged controls and activation), when the function's values whose shape may hold a memory have
ops of `memOpL` (`memTyL`, checked by the driver):

- a read (`LocState.read`) and `Val.retypeL` keep the memories of what they read
  (`MemInv.widen_mems`);
- `stepLoc` writes a copy (`LoadReg`/`StoreReg`), a `MOVDreg` (no memory), or `evalOpL`'s result
  (`evalOpL_mems`): Phase 1's memory ops by `MemInv.evalOp_mems`, the arm64 ops by
  `arm64Op_mems` (stores and the bulk ops write, `LoweredWB` allocates the buffer, calls are
  contracts, nil checks are `memRoot`, atomics are `atomicRoot`), any other value at a shape
  without memories (`WBCheck.memFree`);
- `stepTermLoc` stages controls, which are reads.

`RoMem ro` is such a `P` (`RoImage.roMem_pred`; the buffer is no global; contracts keep it under
`Env.KeepsRo`), so the read-only allocations of `runLoc`'s initial memory are in every memory it
holds: no store writes a read-only symbol (`Mem.write` needs a writable allocation) and no call
removes one (`stepLoc_roMem`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.MemInv GoFV.Opt.WBCheck GoFV.Gen.Check

variable {P : Mem → Prop}

set_option linter.unusedSectionVars false

theorem _root_.GoFV.Proof.MemInv.MemsOK.lretype {v : Val} (h : MemsOK P v) (md : LMode) (t : Ty) :
    MemsOK P (md.retype t v) := by
  unfold LMode.retype
  split
  · exact h.retypeL t
  · exact h.retype t

/-- A value at a shape without memories holds none. -/
theorem lretype_memFree (md : LMode) {t : Ty} (ht : memFree t = true) (v : Val) :
    (md.retype t v).mems = [] := by
  unfold LMode.retype Val.retypeL
  split
  · exact retype_memFree t ht _
  · exact retype_memFree t ht _

theorem res_mems (t : Ty) (r : BitVec 64) : (Arm64.res t r).mems = [] := by
  unfold Arm64.res; split <;> rfl

theorem regVal_mems (t : Ty) (v : Val) : (Arm64.regVal t v).mems = [] := by
  unfold Arm64.regVal
  split
  · rfl
  · split
    · exact res_mems _ _
    · rfl

theorem movdLoc_mems (lc : LocCtx) (v : Value) (argv : List Val) (t : Ty) :
    (movdLoc lc v argv t).mems = [] := by
  unfold movdLoc
  split
  · split
    · exact res_mems _ _
    · exact regVal_mems _ _
  · rfl

/-! ## The state -/

/-- Every memory `runLoc`'s state `s` holds is `P`: its memory, flags, registers, slots, and its
activation's (`MemInv.SInv`: the initial memory and the staged controls). -/
structure LocMems (P : Mem → Prop) (s : LocState) : Prop where
  mem : MemsOK P s.mem
  flags : MemsOK P s.flags
  regs : ∀ (i : Nat) (x : Val), s.regs[i]? = some x → MemsOK P x
  slots : ∀ e ∈ s.slots, MemsOK P e.2
  fr : SInv P s.fr

section State

variable {s : LocState}

theorem LocMems.reg (h : LocMems P s) (t : Ty) (r : Nat) : MemsOK P (s.reg t r) := by
  unfold LocState.reg
  split
  · exact (memsOK_of_mems_nil (res_mems t 0)).retypeL t
  · cases hr : s.regs[r]? with
    | none => exact memsOK_poison
    | some x => exact h.regs r x hr

theorem LocMems.readParts (h : LocMems P s) :
    ∀ (ts : List Ty) (rs : List (Option Nat)), ∀ x ∈ s.readParts ts rs, MemsOK P x
  | [], _ => by simp [LocState.readParts]
  | t :: ts, rs => by
    intro x hx
    unfold LocState.readParts at hx
    split at hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact h.mem
      · exact h.readParts ts rs x hx
    · split at hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact h.flags
        · exact h.readParts ts rs x hx
      · split at hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact h.reg _ _
          · exact h.readParts ts _ x hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact memsOK_poison
          · exact h.readParts ts _ x hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact memsOK_poison
          · exact h.readParts ts _ x hx

theorem lookup_memsOK {l : List (SlotKey × Val)} (hl : ∀ e ∈ l, MemsOK P e.2) (k : SlotKey) :
    MemsOK P ((l.lookup k).getD .poison) := by
  induction l with
  | nil => exact memsOK_poison
  | cons e l ih =>
    obtain ⟨k', x⟩ := e
    simp only [List.lookup]
    split
    · exact hl _ List.mem_cons_self
    · exact ih fun e he => hl e (List.mem_cons_of_mem _ he)

theorem LocMems.raw (h : LocMems P s) {lc : LocCtx} {id : ID} {x : Val}
    (hr : s.raw lc id = .ok x) : MemsOK P x := by
  unfold LocState.raw at hr
  dsimp only at hr
  split at hr
  · cases hr; exact lookup_memsOK h.slots _
  · cases hr; exact memsOK_tuple (h.readParts _ _)
  · cases hr; exact h.reg _ _
  · cases hr; exact memsOK_poison
  · cases hr; exact memsOK_tuple (h.readParts _ _)
  · cases hr; exact h.mem
  · split at hr
    · cases hr; exact h.flags
    · cases hr

theorem LocMems.read (h : LocMems P s) {lc : LocCtx} {id : ID} {x : Val}
    (hr : s.read lc id = .ok x) : MemsOK P x := by
  unfold LocState.read at hr
  cases hraw : s.raw lc id with
  | ok y =>
    rw [hraw] at hr
    cases hr
    exact (h.raw hraw).lretype _ _
  | panic e m => rw [hraw] at hr; cases hr
  | stuck msg => rw [hraw] at hr; cases hr

theorem mapM_memsOK {f : ID → Res Val} (hf : ∀ a x, f a = .ok x → MemsOK P x) :
    ∀ {l : List ID} {L : List Val}, l.mapM f = .ok L → ∀ y ∈ L, MemsOK P y
  | [], L, h => by
    rw [List.mapM_nil] at h; cases h; intro y hy; cases hy
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | panic e m => rw [ha] at h; cases h
    | stuck msg => rw [ha] at h; cases h
    | ok z =>
      rw [ha] at h
      change Res.bind (l.mapM f) _ = _ at h
      cases hl : l.mapM f with
      | ok L' =>
        rw [hl] at h
        cases h
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hf a _ ha
        · exact mapM_memsOK hf hl y hy
      | panic e m => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h

theorem regs_setIfInBounds {r : Array Val} (hr : ∀ (i : Nat) (y : Val), r[i]? = some y → MemsOK P y)
    {k : Nat} {x : Val} (hx : MemsOK P x) :
    ∀ (i : Nat) (y : Val), (r.set! k x)[i]? = some y → MemsOK P y := by
  intro i y hi
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hi
  split at hi
  · split at hi
    · cases hi; exact hx
    · cases hi
  · exact hr i y hi

theorem LocMems.setReg (h : LocMems P s) {r : Nat} {x : Val} (hx : MemsOK P x) :
    LocMems P (s.setReg r x) := by
  refine ⟨h.mem, h.flags, ?_, h.slots, h.fr⟩
  unfold LocState.setReg
  dsimp only
  split
  · exact regs_setIfInBounds h.regs hx
  · exact h.regs

theorem LocMems.writeParts :
    ∀ (ts : List Ty) (xs : List Val) (rs : List (Option Nat)) {s : LocState}, LocMems P s →
      (∀ x ∈ xs, MemsOK P x) → LocMems P (s.writeParts ts xs rs)
  | t :: ts, x :: xs, rs, s, h, hx => by
    have hx0 : MemsOK P x := hx x List.mem_cons_self
    have hxs : ∀ y ∈ xs, MemsOK P y := fun y hy => hx y (List.mem_cons_of_mem _ hy)
    unfold LocState.writeParts
    split
    · exact LocMems.writeParts ts xs rs ⟨hx0, h.flags, h.regs, h.slots, h.fr⟩ hxs
    · split
      · exact LocMems.writeParts ts xs rs ⟨h.mem, hx0, h.regs, h.slots, h.fr⟩ hxs
      · split
        · exact LocMems.writeParts ts xs _ (h.setReg hx0) hxs
        · exact LocMems.writeParts ts xs _ h hxs
        · exact LocMems.writeParts ts xs _ h hxs
  | [], _, _, s, h, _ => by unfold LocState.writeParts; exact h
  | _ :: _, [], _, s, h, _ => by unfold LocState.writeParts; exact h

theorem partsOf_memsOK {x : Val} (hx : MemsOK P x) (n : Nat) : ∀ y ∈ x.partsOf n, MemsOK P y := by
  unfold Val.partsOf
  split
  · exact memsOK_of_tuple hx
  · intro y hy
    rw [List.eq_of_mem_replicate hy]
    exact memsOK_poison

theorem LocMems.write (h : LocMems P s) {lc : LocCtx} {id : ID} {x : Val} (hx : MemsOK P x) :
    LocMems P (s.write lc id x) := by
  unfold LocState.write
  dsimp only
  split
  · refine ⟨h.mem, h.flags, h.regs, ?_, h.fr⟩
    unfold LocState.setSlot
    dsimp only
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hx
    · exact h.slots e (List.mem_filter.1 he).1
  · exact LocMems.writeParts _ _ _ h (partsOf_memsOK hx _)
  · exact h.setReg hx
  · exact ⟨hx, h.flags, h.regs, h.slots, h.fr⟩
  · split
    · exact ⟨h.mem, hx, h.regs, h.slots, h.fr⟩
    · exact h

theorem LocMems.clobber (h : LocMems P s) (lc : LocCtx) (v : Value) :
    LocMems P (s.clobber lc v) := by
  have hm : ∀ {s : LocState} (m : RegMask), LocMems P s → LocMems P (s.clobberMask m) := by
    intro s m h
    unfold LocState.clobberMask
    split
    · exact h
    · refine ⟨h.mem, h.flags, ?_, h.slots, h.fr⟩
      intro i y hi
      rw [Array.getElem?_mapIdx] at hi
      cases hr : s.regs[i]? with
      | none => rw [hr] at hi; cases hi
      | some z =>
        rw [hr] at hi
        simp only [Option.map_some, Option.some.injEq] at hi
        subst hi
        split
        · exact memsOK_poison
        · exact h.regs i z hr
  have ha : ∀ (b : Bool) (i : Nat) {s : LocState}, LocMems P s →
      LocMems P (if !b then s else match v.args[i]?.bind lc.regOf with
        | some r => s.setReg r .poison
        | none => s) := by
    intro b i s h
    split
    · exact h
    · split
      · exact h.setReg memsOK_poison
      · exact h
  have ht : ∀ {s : LocState}, LocMems P s →
      LocMems P (match (lc.temps[v.id]?).join with
        | some r => s.setReg r .poison
        | none => s) := by
    intro s h
    split
    · exact h.setReg memsOK_poison
    · exact h
  have hf : ∀ {s : LocState}, LocMems P s →
      LocMems P (if v.op.clobberFlags then { s with flags := .poison } else s) := by
    intro s h
    split
    · exact ⟨h.mem, memsOK_poison, h.regs, h.slots, h.fr⟩
    · exact h
  exact hf (ht (ha _ 0 (ha _ 1 (hm v.op.regInfo.clobbers h))))

end State

/-! ## Ops -/

theorem memOpOK_generic {o : Op} (h : memOpOK o = true) : o.generic = true := by
  have hl : ∀ o ∈ memOps ++ atomicRootOps, o.generic = true := by decide
  simp only [memOpOK, Bool.or_eq_true, List.contains_iff_mem] at h
  exact hl o (List.mem_append.2 h)

theorem memFreeOps_generic {o : Op} (h : memFreeOps.contains o = true) : o.generic = true := by
  have hl : ∀ o ∈ memFreeOps, o.generic = true := by decide
  exact hl o (List.contains_iff_mem.1 h)

theorem arm64MemOps_generic {o : Op} (h : arm64MemOps.contains o = true) : o.generic = false := by
  have hl : ∀ o ∈ arm64MemOps, o.generic = false := by decide
  exact hl o (List.contains_iff_mem.1 h)

theorem arm64MemOps_wb {o : Op} (h : arm64MemOps.contains o = true)
    (ha : GoFV.Opt.LowerTerm.actOp o = false) : o = .ARM64LoweredWB := by
  have hl : ∀ o ∈ arm64MemOps, GoFV.Opt.LowerTerm.actOp o = true ∨ o = .ARM64LoweredWB := by
    decide
  rcases hl o (List.contains_iff_mem.1 h) with h' | h'
  · rw [ha] at h'; cases h'
  · exact h'

theorem writeRes_mems (hP : MemPred P) {what : String} {m : Mem} {p : Ptr} {bs : Array Byte}
    {r : Val} (hm : P m) (h : writeRes what (m.write p bs) = .ok r) : MemsOK P r := by
  cases hw : m.write p bs with
  | none => rw [hw] at h; cases h
  | some m' => rw [hw] at h; cases h; exact memsOK_mem (hP.write hm hw)

theorem writeRes_pair_mems (hP : MemPred P) {what : String} {m : Mem} {n : Nat} {p q : Ptr}
    {x y : Val} {r : Val} (hm : P m) (h : writeRes what (Arm64.storePair n p q x y m) = .ok r) :
    MemsOK P r := by
  unfold Arm64.storePair at h
  cases hw : m.write p (Arm64.storeBytes n x) with
  | none => rw [hw] at h; cases h
  | some m1 =>
    rw [hw] at h
    exact writeRes_mems hP (hP.write hm hw) h

theorem zero_mems (hP : MemPred P) {n : Int64} {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) :
    MemsOK P (Arm64.zero n argv) := by
  unfold Arm64.zero
  split
  · rename_i a m
    have hm : P m := (ha (.mem m) (by simp)).mem
    split
    · split
      · rename_i m' hw; exact memsOK_mem (hP.write hm hw)
      · exact memsOK_poison
    · exact memsOK_poison
  · exact memsOK_poison

theorem move_mems (hP : MemPred P) {n : Int64} {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) :
    MemsOK P (Arm64.move n argv) := by
  unfold Arm64.move
  split
  · rename_i d s0 m
    have hm : P m := (ha (.mem m) (by simp)).mem
    split
    · split
      · split
        · rename_i m' hw; exact memsOK_mem (hP.write hm hw)
        · exact memsOK_poison
      · exact memsOK_poison
    · exact memsOK_poison
  · exact memsOK_poison

theorem wbOp_mems (hwb : ∀ (m : Mem) (n : Nat), P m → P (m.wbAlloc n)) {n : Int64}
    {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) : MemsOK P (wbOp n argv) := by
  unfold wbOp
  split
  · rename_i m
    refine memsOK_tuple fun y hy => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact memsOK_of_mems_nil rfl
    · exact memsOK_mem (hwb m _ (ha (.mem m) (by simp)).mem)
  · exact memsOK_poison

theorem loadN_mems (t : Ty) (n : Nat) (sg : Bool) (m : Mem) (p : Ptr) :
    (Arm64.loadN t n sg m p).mems = [] := by
  unfold Arm64.loadN
  repeat' split
  all_goals first | rfl | exact res_mems _ _ | exact load_mems _ _ _

theorem loadPair_mems (t : Ty) (n : Nat) (sg : Bool) (m : Mem) (p q : Ptr) :
    (Arm64.loadPair t n sg m p q).mems = [] := by
  unfold Arm64.loadPair Arm64.loadElt Arm64.load16
  simp only [Val.mems, Val.memsL]
  split <;> (try split) <;> (try split) <;>
    simp only [loadN_mems, Val.mems, List.append_nil]

theorem fitPiece_mems (t : Ty) (x : Val) : ∀ m ∈ (fitPiece t x).mems, m ∈ x.mems := by
  intro m hm
  unfold fitPiece at hm
  split at hm
  · split at hm
    · exact hm
    · exact widen_mems _ _ m (retype_mems _ _ m hm)
  · split at hm
    · exact hm
    · exact widen_mems _ _ m (retype_mems _ _ m hm)
  · exact widen_mems _ _ m (retype_mems _ _ m hm)
  · exact widen_mems _ _ m (retype_mems _ _ m hm)
  · exact hm

theorem fitPieces_memsOK (tabs : Tables) :
    ∀ (ps : List ABIParam) {argv : List Val}, (∀ a ∈ argv, MemsOK P a) →
      ∀ a ∈ fitPieces tabs ps argv, MemsOK P a
  | [], _, ha => ha
  | p :: ps, argv, ha => by
    unfold fitPieces
    split
    · exact fitPieces_memsOK tabs ps ha
    · intro a hmem
      rcases List.mem_append.1 hmem with h1 | h1
      · obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 h1
        have hx : MemsOK P ((argv.take p.regs.size)[i]) := ha _ (List.mem_of_mem_take
          (List.getElem_mem hi))
        split
        · exact fun m hm => hx m (fitPiece_mems _ _ m hm)
        · exact hx
      · exact fitPieces_memsOK tabs ps (fun a ha' => ha a (List.mem_of_mem_drop ha')) a h1

theorem atomicArgs_memsOK {g : Op} {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) :
    ∀ a ∈ atomicArgs g argv, MemsOK P a := by
  unfold atomicArgs
  split
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact ha _ (by simp)
    · exact fun m hm => ha _ (by simp) m (fitPiece_mems _ _ m hm)
    · exact ha _ (by simp)
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ha _ (by simp)
    · exact fun m hm => ha _ (by simp) m (fitPiece_mems _ _ m hm)
    · exact fun m hm => ha _ (by simp) m (fitPiece_mems _ _ m hm)
    · exact ha _ (by simp)
  · exact ha

theorem elim_poison_memsOK {α : Type} (o : Option α) {f : α → Val} (hf : ∀ a, (f a).mems = []) :
    MemsOK P (o.elim .poison f) := by
  cases o with
  | none => exact memsOK_poison
  | some a => exact memsOK_of_mems_nil (hf a)

theorem callArgs_memsOK {k : Nat} {tabs : Tables} {ins : List ABIParam} {argv : List Val}
    (ha : ∀ a ∈ argv, MemsOK P a) :
    ∀ a ∈ argv.take k ++ fitPieces tabs ins (argv.drop k), MemsOK P a := by
  intro a hmem
  rcases List.mem_append.1 hmem with h1 | h1
  · exact ha a (List.mem_of_mem_take h1)
  · exact fitPieces_memsOK tabs ins (fun a ha' => ha a (List.mem_of_mem_drop ha')) a h1

theorem writeRes_storeN_mems (hP : MemPred P) {what : String} {n : Nat} {p : Ptr} {x : Val}
    {m : Mem} {r : Val} (hm : P m) (h : writeRes what (Arm64.storeN n p x m) = .ok r) :
    MemsOK P r :=
  writeRes_mems hP hm h

/-- The memory ops of `Arm64.evalPure`: acquire loads, the bulk ops, `LoweredWB`. -/
theorem evalPure_memOps_mems (hP : MemPred P) (hwb : ∀ (m : Mem) (n : Nat), P m → P (m.wbAlloc n))
    {o : Op} (ho : o ∈ [.ARM64LDAR, .ARM64LDARB, .ARM64LDARW, .ARM64LoweredZero,
      .ARM64LoweredZeroLoop, .ARM64LoweredMove, .ARM64LoweredMoveLoop, .ARM64LoweredWB])
    (t : Ty) (k : Int64) (ax : Option AuxRef) {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) :
    MemsOK P (Arm64.evalPure o t k ax argv) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact atomicLoad_mems t ha
  · exact atomicLoad_mems t ha
  · exact atomicLoad_mems t ha
  · exact zero_mems hP ha
  · exact zero_mems hP ha
  · exact move_mems hP ha
  · exact move_mems hP ha
  · exact wbOp_mems hwb ha

set_option maxHeartbeats 800000 in
/-- **An arm64 memory op's result**: from arguments whose memories are `P`. -/
theorem arm64Op_mems (hP : MemPred P) {env : Env} (hE : ContractsOK P env)
    (hwb : ∀ (m : Mem) (n : Nat), P m → P (m.wbAlloc n)) {faulting : Bool} {ctx : Sem.Ctx}
    {fr : Frame} {v : Value} {argv : List Val} {ty : Ty} {r : Val}
    (hop : arm64MemOps.contains v.op = true) (ha : ∀ a ∈ argv, MemsOK P a)
    (h : arm64Op faulting env ctx fr v argv ty = .ok r) : MemsOK P r := by
  unfold arm64Op at h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨id, op, type, auxInt, aux, pos, uses, args, block⟩ := v
  dsimp only at hop h
  cases op
  all_goals first | exact absurd hop (by decide) | skip
  all_goals dsimp only at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | (have hn := ‹Arm64.atomicOf _ = none›; simp only [Arm64.atomicOf, reduceCtorEq] at hn; done)
    | with_reducible exact absurd h panicBounds_not_ok
    | with_reducible exact memRoot_mems hP ha h
    | with_reducible exact callOp_mems hP hE (callArgs_memsOK ha) h
    | with_reducible exact atomicRoot_mems hP (atomicArgs_memsOK ha) h
    | with_reducible exact writeRes_storeN_mems hP (MemsOK.mem (ha _ (by simp))) h
    | with_reducible exact writeRes_pair_mems hP (MemsOK.mem (ha _ (by simp))) h
    | (injection h with h; subst h; first
        | with_reducible exact memsOK_poison
        | with_reducible exact elim_poison_memsOK _ (fun _ => loadPair_mems _ _ _ _ _ _)
        | with_reducible exact evalPure_memOps_mems hP hwb (by simp) _ _ _ ha
        | with_reducible exact ha _ (by simp))


/-- **The result of an op of `memOpL`**, from arguments and an initial memory whose memories are
`P`. -/
theorem evalOpL_mems (hP : MemPred P) {env : Env} (hE : ContractsOK P env)
    (hwb : ∀ (m : Mem) (n : Nat), P m → P (m.wbAlloc n)) {faulting : Bool} {ctx : Sem.Ctx}
    {fr : Frame} {v : Value} {argv : List Val} {ty : Ty} {r : Val} (h0 : P fr.mem0)
    (hop : memOpL v.op = true) (ha : ∀ a ∈ argv, MemsOK P a)
    (h : evalOpL faulting env ctx fr v argv ty = .ok r) : MemsOK P r := by
  have hop' : memOpOK v.op = true ∨ memFreeOps.contains v.op = true ∨
      arm64MemOps.contains v.op = true := by
    simpa only [memOpL, Bool.or_eq_true, or_assoc] using hop
  rw [GoFV.Proof.evalOpL_eq] at h
  cases hg : v.op.generic with
  | true =>
    simp only [hg, ↓reduceIte] at h
    rcases hop' with h1 | h1 | h1
    · exact evalOp_mems hP hE h0 h1 ha h
    · exact memsOK_of_mems_nil (evalOp_memFreeOps_mems h1 h)
    · rw [arm64MemOps_generic h1] at hg; cases hg
  | false =>
    simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
    have h1 : arm64MemOps.contains v.op = true := by
      rcases hop' with h1 | h1 | h1
      · rw [memOpOK_generic h1] at hg; cases hg
      · rw [memFreeOps_generic h1] at hg; cases hg
      · exact h1
    cases hact : GoFV.Opt.LowerTerm.actOp v.op with
    | true =>
      simp only [hact, ↓reduceIte] at h
      exact arm64Op_mems hP hE hwb h1 ha h
    | false =>
      simp only [hact, Bool.false_eq_true, ↓reduceIte] at h
      cases hr : isRoot v.op with
      | true =>
        simp only [hr, ↓reduceIte] at h
        exact atomicRoot_mems hP ha h
      | false =>
        simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
        cases h
        rw [arm64MemOps_wb h1 hact]
        exact evalPure_memOps_mems hP hwb (by simp) _ _ _ ha

/-! ## `stepLoc` and `stepTermLoc` -/

/-- **One value keeps the memories `P`**: a value whose shape may hold a memory has an op of
`memOpL` (`memTyL`). -/
theorem stepLoc_locMems (hP : MemPred P) {env : Env} (hE : ContractsOK P env)
    (hwb : ∀ (m : Mem) (n : Nat), P m → P (m.wbAlloc n)) {lc : LocCtx} {s s' : LocState}
    {v : Value} (hty : memFree (lc.ty v.id) = true ∨ memOpL v.op = true) (hs : LocMems P s)
    (h : stepLoc env lc s v = .ok s') : LocMems P s' := by
  unfold stepLoc at h
  split at h
  · split at h
    · cases h; exact hs
    · cases h
  · cases hm : v.args.toList.mapM (s.read lc) with
    | panic e m => rw [hm] at h; cases h
    | stuck msg => rw [hm] at h; cases h
    | ok argv =>
      have ha : ∀ a ∈ argv, MemsOK P a := mapM_memsOK (fun _ _ hx => hs.read hx) hm
      rw [hm] at h
      simp only [bind, Res.bind] at h
      have hres : ∀ r, MemsOK P ((LMode.loc lc.ctx.f).retype (lc.ty v.id) r) →
          Res.ok ((s.clobber lc v).write lc v.id ((LMode.loc lc.ctx.f).retype (lc.ty v.id) r)) =
            Res.ok s' → LocMems P s' := by
        intro r hr he
        cases he
        exact (hs.clobber lc v).write hr
      repeat' split at h
      all_goals first
        | (cases h; done)
        | skip
      all_goals rename_i hx
      all_goals first
        | (change Res.ok _ = Res.ok _ at hx; cases hx; first
            | exact hres _ ((ha _ (by simp)).lretype _ _) h
            | exact hres _ ((memsOK_of_mems_nil (movdLoc_mems _ _ _ _)).lretype _ _) h)
        | exact hres _ (by
            rcases hty with hf | hop
            · exact memsOK_of_mems_nil (lretype_memFree _ hf _)
            · exact (evalOpL_mems hP hE hwb hs.fr.1 hop ha hx).lretype _ _) h

theorem LocMems.control {s : LocState} (hs : LocMems P s) {lc : LocCtx} {c : ID} {x : Val}
    (h : s.control lc c = .ok x) : MemsOK P x := by
  unfold LocState.control at h
  split at h
  · rename_i v hv
    split at h
    · cases hm : v.args.toList.mapM (s.read lc) with
      | ok xs =>
        rw [hm] at h
        change Res.ok _ = Res.ok _ at h
        cases h
        exact (memsOK_tuple (mapM_memsOK (fun _ _ hx => hs.read hx) hm)).lretype _ _
      | panic e m => rw [hm] at h; cases h
      | stuck msg => rw [hm] at h; cases h
    · exact hs.read h
  · cases h

/-- `stepTermLoc`'s staging of one control. -/
private def stageR (lc : LocCtx) (s : LocState) (c : ID) (regs : Array (Option Val)) :
    Res (ForInStep (Array (Option Val))) := do
  let x ← s.control lc c
  pure (ForInStep.yield (if c < regs.size then regs.set! c (some x) else regs))

private theorem stepTermLoc_eqR (lc : LocCtx) (s : LocState) (b : Block) :
    stepTermLoc lc s b =
      (forIn b.controls.toList s.fr.regs (stageR lc s)) >>= fun regs =>
        (stepTermL ({ s with fr := { s.fr with regs } } : LocState).fr b) >>= fun n =>
          pure (n, ({ s with fr := { s.fr with regs } } : LocState)) := by
  unfold stepTermLoc
  rw [Array.forIn_toList]
  rfl

private theorem forIn_stageR_mems {lc : LocCtx} {s : LocState} (hs : LocMems P s) :
    ∀ (l : List ID) (regs : Array (Option Val)),
      (∀ (x : Nat) (y : Val), regs[x]? = some (some y) → MemsOK P y) → ∀ R,
      forIn l regs (stageR lc s) = .ok R →
      ∀ (x : Nat) (y : Val), R[x]? = some (some y) → MemsOK P y
  | [], regs, hr, R, h => by
    rw [List.forIn_nil] at h; cases h; exact hr
  | c :: cs, regs, hr, R, h => by
    rw [List.forIn_cons] at h
    unfold stageR at h
    cases hc : s.control lc c with
    | ok x =>
      simp only [hc, bind, Res.bind] at h
      refine forIn_stageR_mems hs cs _ ?_ R h
      split
      · exact regs_set_mems hr (hs.control hc)
      · exact hr
    | panic e m => simp only [hc, bind, Res.bind] at h; cases h
    | stuck msg => simp only [hc, bind, Res.bind] at h; cases h

/-- **A terminator keeps the memories `P`**: it stages controls, which are reads. -/
theorem stepTermLoc_locMems {lc : LocCtx} {s s' : LocState} {b : Block} {n : Next}
    (hs : LocMems P s) (h : stepTermLoc lc s b = .ok (n, s')) : LocMems P s' := by
  rw [stepTermLoc_eqR] at h
  cases hf : forIn b.controls.toList s.fr.regs (stageR lc s) with
  | ok R =>
    simp only [hf, bind, Res.bind] at h
    split at h
    · cases h
      exact ⟨hs.mem, hs.flags, hs.regs, hs.slots, ⟨hs.fr.1, forIn_stageR_mems hs _ _ hs.fr.2 R hf⟩⟩
    · cases h
    · cases h
  | panic e m => simp only [hf, bind, Res.bind] at h; cases h
  | stuck msg => simp only [hf, bind, Res.bind] at h; cases h

/-- The entry frame (`entryFrame`) of a run whose memory with the global image is `P`, for a `P`
that every `set` of a block other than a global and the write-barrier buffer keeps (the frame
allocations; `MemInv.sinv_entry` for any context). -/
theorem entryFrame_sinv
    (hset : ∀ {m : Mem} {b : Blk} (a : Alloc), P m → (∀ n, b ≠ .global n) → b ≠ .wbuf →
      P (m.set b a))
    {env : Env} {ctx : Sem.Ctx} {args : List Val} {mem : Mem} (h : P (addGlobals env mem)) :
    SInv P (entryFrame env ctx args mem) := by
  refine ⟨?_, fun x y hx => ?_⟩
  · simp only [entryFrame, frameMem, frameAllocs]
    rw [← Array.foldl_toList]
    refine wb_foldl_inv P _ (fun m a hm => ?_) _ _
      (hset _ h (fun _ h => by cases h) (by simp))
    obtain ⟨n, sz, pi⟩ := a
    exact hset _ hm (frameBlk_ne _ _ _).1 (frameBlk_ne _ _ _).2
  · change (Array.replicate _ none)[x]? = some (some y) at hx
    rw [Array.getElem?_replicate] at hx
    split at hx <;> cases hx

/-! ## The read-only symbols -/

/-- The write-barrier buffer is no global: its allocation keeps the read-only symbols. -/
theorem roMem_wbAlloc (ro : List (String × Alloc)) (m : Mem) (n : Nat) (h : RoMem ro m) :
    RoMem ro (m.wbAlloc n) := by
  unfold Mem.wbAlloc
  exact h.keep (Mem.keepsRo_set (fun _ h => by cases h) _)

/-- **No store writes a read-only symbol and no call drops one**: one value keeps the read-only
allocations `ro` of every memory `runLoc`'s state holds, under contracts that keep them
(`Env.KeepsRo`). -/
theorem stepLoc_roMem {ro : List (String × Alloc)} {env : Env} (hK : env.KeepsRo) {lc : LocCtx}
    {s s' : LocState} {v : Value} (hty : memFree (lc.ty v.id) = true ∨ memOpL v.op = true)
    (hs : LocMems (RoMem ro) s) (h : stepLoc env lc s v = .ok s') : LocMems (RoMem ro) s' :=
  stepLoc_locMems (roMem_pred ro) (hK.contractsOK ro) (roMem_wbAlloc ro) hty hs h

/-- The entry frame of a run whose memory with the global image has the read-only symbols. -/
theorem entryFrame_roMem {ro : List (String × Alloc)} {env : Env} {ctx : Sem.Ctx}
    {args : List Val} {mem : Mem} (h : RoMem ro (addGlobals env mem)) :
    SInv (RoMem ro) (entryFrame env ctx args mem) :=
  entryFrame_sinv (fun a hm hg hw => roMem_set a hm hg hw) h

/-- `memTyL` of a value of the function. -/
theorem memTyL_val {lc : LocCtx} (h : memTyL lc = true) {id : ID} {v : Value}
    (hv : lc.ctx.f.value? id = some v) : memFree (lc.ty v.id) = true ∨ memOpL v.op = true := by
  have hx : lc.ctx.f.valueTab[id]? = some (some v) := by
    unfold Func.value? at hv
    exact Option.join_eq_some_iff.1 hv
  unfold memTyL at h
  rw [Array.all_eq_true'] at h
  have := h (some v) (Array.mem_of_getElem? hx)
  simpa only [Bool.or_eq_true] using this

end GoFV.Proof.Obj
