import GoFV.Proof.Pass.ECRel
import GoFV.Proof.FrameKeep

/-!
# The result slots along the source's run (issue #28)

`SlotsOK ctx m`: the frame slots of the function's stack-assigned results are writable in `m`
(`Mem.canWrite`), which `expand calls`' result stores need. It depends only on the writability
and size of frame allocations, which writes, `poisonBlock`s and freeing the write-barrier buffer
keep (`slotsOK_pred`: a `MemInv.MemPred`), and contracts that keep the caller's frame
(`Env.FrameKeep`, `ecQ_contracts`). So every memory of the source's run is `EcQ` (`MemInv.SInv`):
`ecQ_enter`, `ecQ_prefix`.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.AtomSim

/-- `canWrite` reads the writability and size of the pointer's block. -/
theorem canWrite_attr {m m' : Mem} {p : Ptr}
    (h : (m'.find? p.blk).map Alloc.attr = (m.find? p.blk).map Alloc.attr) (n : Nat) :
    m'.canWrite p n = m.canWrite p n := by
  unfold Mem.canWrite
  cases h1 : m.find? p.blk with
  | none =>
    rw [h1] at h
    cases h2 : m'.find? p.blk with
    | none => rfl
    | some a' => rw [h2] at h; cases h
  | some a =>
    rw [h1] at h
    cases h2 : m'.find? p.blk with
    | none => rw [h2] at h; cases h
    | some a' =>
      rw [h2] at h
      simp only [Option.map_some, Option.some.injEq, Alloc.attr, Prod.mk.injEq] at h
      simp only [h.1, h.2]

/-- Memories with the same frame allocations' writability and sizes have the same slots. -/
theorem slotsOK_congr {ctx : Ctx} {m m' : Mem}
    (h : ∀ b, b.isFrame = true → (m'.find? b).map Alloc.attr = (m.find? b).map Alloc.attr)
    (hs : SlotsOK ctx m) : SlotsOK ctx m' := fun n t ho hp => by
  rw [canWrite_attr (h _ rfl)]; exact hs n t ho hp

/-- `poisonBlock` keeps every allocation's writability and size. -/
theorem find_poisonBlock_attr (m : Mem) (b b' : Blk) :
    ((m.poisonBlock b).find? b').map Alloc.attr = (m.find? b').map Alloc.attr := by
  unfold Mem.poisonBlock
  cases ha : m.find? b with
  | none => rfl
  | some a =>
    simp only
    rw [CSE.Mem.find?_set]
    split
    · next he => subst he; rw [ha]; simp [Alloc.attr]
    · rfl

/-- **The result slots are a memory invariant.** -/
theorem slotsOK_pred (ctx : Ctx) : MemInv.MemPred (SlotsOK ctx) where
  write h hw := slotsOK_congr (fun b _ => Mem.find_write_attr hw b) h
  poison h _ _ := slotsOK_congr (fun b _ => find_poisonBlock_attr _ _ b) h
  free_wbuf h := slotsOK_congr (fun b hb => by
    rw [WB.free_eq_erase, TabsMod.erase_find (by cases b <;> first | rfl | cases hb)]) h

theorem ecQ_pred {tabs : Tables} {f : Func} : MemInv.MemPred (EcQ tabs f) := (slotsOK_pred _).imp

/-- A memory that keeps the frame allocations of one with the slots has them. -/
theorem SlotsOK.keep {ctx : Ctx} {m m' : Mem} (h : SlotsOK ctx m) (hk : m.KeepsFrame m') :
    SlotsOK ctx m' := fun n t ho hp => by
  have hc := h n t ho hp
  have hn : t.size ≠ 0 := by omega
  cases ha : m.find? (.local ctx.act n) with
  | none =>
    unfold Mem.canWrite at hc
    simp only [show (t.size == 0) = false from by simp [hn], Bool.false_or] at hc
    change (match m.find? (.local ctx.act n) with
      | some a => _
      | none => false) = true at hc
    rw [ha] at hc; cases hc
  | some a =>
    have := hk _ a rfl ha
    rw [canWrite_attr (p := ⟨.local ctx.act n, 0⟩) (m := m) (by rw [this, ha]; rfl)]
    exact hc

/-- **Contracts that keep the caller's frame keep `EcQ`.** -/
theorem ecQ_contracts {tabs : Tables} {f : Func} {env : Env} (hK : env.FrameKeep) :
    MemInv.ContractsOK (EcQ tabs f) env := by
  intro name c hc args clo m _ _ hm
  cases hco : c args clo m with
  | returned rs m' =>
    obtain ⟨hk, hrs⟩ := hK name c hc args clo m rs m' hco
    exact ⟨fun ht => (hm ht).keep hk, fun r hr => MemInv.memsOK_of_mems_nil (hrs r hr)⟩
  | panicked e m' => trivial
  | stuck msg => trivial

/-- A block entry keeps the invariant. -/
theorem ecQ_enter {tabs : Tables} {f : Func} {env : Env} (hK : env.FrameKeep) {ce : CheckEnv}
    (hwf : WF ce f) {b : ID} {B : Block} (hb : b ∈ f.blocks) (hB : f.block? b = some B)
    {fr fr' : Frame} {i : Nat} (hs : MemInv.SInv (EcQ tabs f) fr)
    (h : enterBlock env (Ctx.make tabs f) fr B i = .ok fr') : MemInv.SInv (EcQ tabs f) fr' := by
  by_cases hm : GoFV.Opt.WBCheck.memTyOK tabs f = true
  · exact MemInv.sinv_enter ecQ_pred (ecQ_contracts hK) hwf hm hb hB hs h
  · exact ⟨fun h => absurd h hm, fun _ _ _ _ _ h => absurd h hm⟩

/-- The `Phi`s and a part `L` of the schedule of a block keep the invariant. -/
theorem ecQ_prefix {tabs : Tables} {f : Func} {env : Env} (hK : env.FrameKeep) {ce : CheckEnv}
    (hwf : WF ce f) {b : ID} {B : Block} (hb : b ∈ f.blocks) (hB : f.block? b = some B)
    {fr : Frame} {i : Nat} (hs : MemInv.SInv (EcQ tabs f) fr) {ps : List (ID × Val)}
    (hps : B.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps)
    {L : List ID} (hL : ∀ x ∈ L, x ∈ B.values) {G : Frame}
    (hev : evalAll env (Ctx.make tabs f) { fr with regs := setPhis ps fr.regs } L = .ok G) :
    MemInv.SInv (EcQ tabs f) G := by
  by_cases hm : GoFV.Opt.WBCheck.memTyOK tabs f = true
  · refine MemInv.sinv_evalAll ecQ_pred (ecQ_contracts hK) hwf hm (fun x hx => ⟨b, hb, ?_⟩)
      (MemInv.sinv_phis hs hps) hev
    unfold GoFV.Opt.WBCheck.vals; rw [hB]; exact hL x hx
  · exact ⟨fun h => absurd h hm, fun _ _ _ _ _ h => absurd h hm⟩

/-- The memories the registers of a frame with the invariant hold directly are `EcQ`. -/
theorem ecQ_memQ {tabs : Tables} {f : Func} {G : Frame} (h : MemInv.SInv (EcQ tabs f) G) :
    ∀ (a : ID) (m : Mem), G.regs[a]? = some (some (Val.mem m)) → EcQ tabs f m :=
  fun a _ ha => (h.2 a _ ha).mem

/-- The memory a `Ret` reads of a register with the invariant is `EcQ`. -/
theorem ecQ_retQ {tabs : Tables} {f : Func} {G : Frame} (h : MemInv.SInv (EcQ tabs f) G)
    {c : ID} {y : Val} (hy : G.regs[c]? = some (some y)) {rs : List Val} {m : Mem}
    (hr : retOf y = some (rs, m)) : EcQ tabs f m := by
  have hy' := h.2 c y hy
  unfold retOf at hr
  split at hr
  · next vs =>
    split at hr
    · next m0 hl =>
      split at hr
      · cases hr
      · simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hl
        exact (MemInv.memsOK_of_tuple hy' (.mem m0) (by simp)).mem
    · cases hr
  · cases hr

/-- The entry frame has the invariant when its memory has. -/
theorem ecQ_entry {tabs : Tables} {f : Func} {env : Env} {args : List Val} {mem : Mem}
    (h : EcQ tabs f (entryFrame env (Ctx.make tabs f) args mem).mem0) :
    MemInv.SInv (EcQ tabs f) (entryFrame env (Ctx.make tabs f) args mem) := by
  refine ⟨h, fun x y hx => ?_⟩
  change (Array.replicate _ none)[x]? = some (some y) at hx
  rw [Array.getElem?_replicate] at hx
  split at hx <;> cases hx

end GoFV.Proof.EC
