import GoFV.Proof.Gen.Mem
import GoFV.Proof.RoImage

variable [GoFV.SSA.Sem.Addrs]

/-!
# The read-only symbols in the machine's memory (`docs/plans/proofs3.md` §10)

At a state `LocMatch` relates to a machine state, the memory injection (`MemInj`, under
`AddrAgree`) puts each concrete byte of a read-only allocation `ro` the memory has (`RoMem`) at
the global's injected address (`ro_byte`), above the nil page (`ro_addr`). `lreach_roMem`
(`GoFV/Proof/Obj/RoReach.lean`) gives `RoMem` along a run; slice G56 (`G56.lean`) reads the float
constant symbols with them.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.MemInv

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
    (hA : AddrAgree ι) (h : MemInj ι mm M) {ro : List (String × Alloc)}
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

end GoFV.Proof.Gen
