import GoFV.Proof.Obj.RoLoc
import GoFV.Proof.Obj.Whole

variable [GoFV.SSA.Sem.Addrs]

/-!
# The read-only symbols along a run, and in the machine's memory (`docs/plans/proofs3.md` §10)

From `runLoc`'s first state (`locInit`, whose memory is the input's with the global image and the
frame allocations), through the entry values (`enterListLoc`) and every state the body reaches
(`LReach`), every memory `runLoc` holds keeps the read-only allocations `ro` the input memory has
(`lreach_roMem`): `stepLoc_roMem` and `stepTermLoc_locMems` (`RoLoc.lean`), under contracts that
keep them (`Env.KeepsRo`, part of Phase 1's `RoImage` premise) and `memTyL`.

At a state `LocMatch` relates to a machine state, the memory injection (`MemInj`, under
`AddrAgree`) puts each concrete byte of such an allocation at the global's injected address
(`ro_byte`), above the nil page (`ro_addr`); `G2Env.glob` puts the global named by the symbol
`y` at `L.sym y`. So the machine's memory holds a read-only symbol's bytes at its linked address
in every state the composition relates, the calls' included (`CallSpec`'s `MemInj` after the
call): no trusted clause beyond the callee contracts and `Env.KeepsRo`.
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.MemInv GoFV.Opt.WBCheck GoFV.Gen.Check
open GoFV.Proof (enterListLoc)
open GoFV.Proof.Gen (memInj_byteRel)

variable {P : Mem → Prop}

set_option linter.unusedSectionVars false

/-! ## Along a run -/

theorem locInit_locMems {env : Env} {lc : LocCtx} {args : List Val} {mem : Mem}
    (hfr : SInv P (entryFrame env lc.ctx args mem)) : LocMems P (locInit env lc args mem) := by
  refine ⟨memsOK_mem hfr.1, memsOK_poison, fun i x hx => ?_, fun e he => (by cases he), hfr⟩
  change (Array.replicate _ Val.poison)[i]? = some x at hx
  rw [Array.getElem?_replicate] at hx
  split at hx
  · cases hx; exact memsOK_poison
  · cases hx

theorem enterListLoc_locMems (hP : MemPred P) {env : Env} (hE : ContractsOK P env)
    (hwb : ∀ (m : Mem) (n : Nat), P m → P (m.wbAlloc n)) {lc : LocCtx}
    (hmt : memTyL lc = true) :
    ∀ (ids : List ID) {s s' : LocState}, LocMems P s → enterListLoc env lc s ids = .ok s' →
      LocMems P s'
  | [], s, s', hs, h => by cases h; exact hs
  | id :: ids, s, s', hs, h => by
    unfold enterListLoc at h
    split at h
    · cases h
    · rename_i v hv
      split at h
      · rename_i s1 h1
        exact enterListLoc_locMems hP hE hwb hmt ids
          (stepLoc_locMems hP hE hwb (memTyL_val hmt hv) hs h1) h
      · cases h
      · cases h

theorem lreach_locMems (hP : MemPred P) {env : Env} (hE : ContractsOK P env)
    (hwb : ∀ (m : Mem) (n : Nat), P m → P (m.wbAlloc n)) {lc : LocCtx}
    (hmt : memTyL lc = true) {b0 : ID} {i0 : Nat} {s0 : LocState} (h0 : LocMems P s0)
    {b : ID} {i : Nat} {s : LocState} (hr : LReach env lc b0 i0 s0 b i s) : LocMems P s := by
  induction hr with
  | refl => exact h0
  | val _ _ _ hv hs ih => exact stepLoc_locMems hP hE hwb (memTyL_val hmt hv) ih hs
  | term _ _ ht ih => exact stepTermLoc_locMems ih ht

/-- **The read-only symbols along a run**: when the input memory with the global image has the
read-only allocations `ro` and the environment's contracts keep them, every state `runLoc`
reaches from its entry (after the entry values `ids`) holds a memory that has them. -/
theorem lreach_roMem {ro : List (String × Alloc)} {env : Env} {lc : LocCtx} {args : List Val}
    {mem : Mem} (hK : env.KeepsRo) (hmt : memTyL lc = true) (hg : RoMem ro (addGlobals env mem))
    {ids : List ID} {sI : LocState}
    (hpre : enterListLoc env lc (locInit env lc args mem) ids = .ok sI)
    {b0 : ID} {i0 : Nat} {b : ID} {i : Nat} {s : LocState} (hr : LReach env lc b0 i0 sI b i s)
    {mm : Mem} (hm : s.mem = .mem mm) : RoMem ro mm := by
  have h0 := locInit_locMems (entryFrame_roMem (ctx := lc.ctx) (args := args) hg)
  have hI := enterListLoc_locMems (roMem_pred ro) (hK.contractsOK ro) (roMem_wbAlloc ro) hmt _
    h0 hpre
  have := (lreach_locMems (roMem_pred ro) (hK.contractsOK ro) (roMem_wbAlloc ro) hmt hI hr).mem
  rw [hm] at this
  exact this.mem

/-! ## In the machine's memory -/

private theorem find?_mem' {m : Mem} {b : Blk} {al : Alloc} (h : m.find? b = some al) :
    (b, al) ∈ m.blocks := by
  unfold Mem.find? at h
  cases hf : m.blocks.find? (·.1 == b) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have h1 := Array.mem_of_find?_eq_some hf
    have h2 := Array.find?_some hf
    obtain ⟨b', al'⟩ := e
    simp only [beq_iff_eq] at h2
    subst h2
    exact h1

/-- **A read-only symbol's bytes in the machine's memory**: a concrete byte of an allocation of
`ro` lies at the global's injected address plus its offset. -/
theorem ro_byte {ι : Blk → Option (BitVec 64)} {mm : Mem} {M : GoFV.Arm64.Memory}
    (hA : GoFV.Proof.Gen.AddrAgree ι) (h : MemInj ι mm M) {ro : List (String × Alloc)}
    (hro : RoMem ro mm) {name : String} {a : Alloc} (hn : (name, a) ∈ ro) {addr : BitVec 64}
    (hι : ι (.global name) = some addr) {i : Nat} {x : BitVec 8} (hi : a.data[i]? = some (.b x)) :
    M (addr + BitVec.ofNat 64 i) = x := by
  obtain ⟨-, hf⟩ := hro name a hn
  obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.1 hi
  have := memInj_byteRel hA h (find?_mem' hf) hι hlt
  rw [hx] at this
  exact this.symm

/-- A read-only symbol with bytes lies above the nil page and below `2^64`. -/
theorem ro_addr {ι : Blk → Option (BitVec 64)} {mm : Mem} {M : GoFV.Arm64.Memory}
    (h : MemInj ι mm M) {ro : List (String × Alloc)} (hro : RoMem ro mm) {name : String}
    {a : Alloc} (hn : (name, a) ∈ ro) {addr : BitVec 64} (hι : ι (.global name) = some addr)
    (hpos : 0 < a.data.size) : 4096 ≤ addr.toNat ∧ addr.toNat + a.data.size ≤ 2 ^ 64 := by
  obtain ⟨-, hf⟩ := hro name a hn
  obtain ⟨a', ha', hlo, hhi⟩ := h.mapped _ _ (find?_mem' hf)
  rw [hι] at ha'
  cases ha'
  exact ⟨hlo hpos, hhi⟩

end GoFV.Proof.Obj
