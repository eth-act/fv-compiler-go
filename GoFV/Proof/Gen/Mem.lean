import GoFV.Proof.Gen.Value
import GoFV.Arm64.State

/-!
# Loads and stores of slice G1 under `MemInj` (`docs/plans/proofs3.md` §3)

Under `AddrAgree` the pointer words `MemInj` allows (`BytesRel`'s `W`) hold their own Phase 1
address, so every byte of a live block is related to its machine byte by `ByteRel`
(`memInj_byteRel`). An 8-byte load (`Mem.load` at `int64`, `MOVD off(Rn), Rd`) then reads a value
related to the machine word (`lo_load`); an 8-byte store (`Mem.write` of `storeBytes 8`,
`MOVD Rs, off(Rn)`) keeps `MemInj` (`memInj_store`) when the block keys are distinct (otherwise a
second entry of the written block would keep its old bytes while the machine's change).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64

variable {ι : Blk → Option (BitVec 64)}

/-- The block keys of a memory are distinct. -/
def KeysNodup (m : Mem) : Prop := (m.blocks.toList.map (·.1)).Nodup

/-- Under `AddrAgree`, every byte of a live block is related to its machine byte. -/
theorem memInj_byteRel (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm)
    {b : Blk} {al : Alloc} {a : BitVec 64} (hb : (b, al) ∈ m.blocks) (ha : ι b = some a)
    {i : Nat} (hi : i < al.data.size) : ByteRel ι al.data[i] (mm (a + BitVec.ofNat 64 i)) := by
  sorry

/-- The address of an access: a 64-bit base related to `X` (a pointer or a pointer word) moved
by `off`, into a live block, is that block's injected address plus the offset; outside the nil
page when the access of `n > 0` bytes is valid. -/
theorem addr_rel (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm) {base : Val}
    {X off : BitVec 64} {p : Ptr} {n : Nat} (hx : ValRel ι base X) (hf : Fits 64 base)
    (hp : Arm64.addr base off = some p) (hn : 0 < n) (hv : m.canWrite p n = true ∨ (m.read p n).isSome) :
    ∃ a, ι p.blk = some a ∧ X + off = a + p.off ∧ nilPage (a + p.off) = false := by
  sorry

/-- An 8-byte load at a valid address reads a value related to the machine word there. -/
theorem lo_load (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm) {p : Ptr}
    {a : BitVec 64} {bs : Array Byte} (ha : ι p.blk = some a) (hr : m.read p 8 = some bs) :
    Lo ι 64 (m.load (.int .w64) p) ((readMem mm (a + p.off) 8).setWidth 64) := by
  sorry

/-- An 8-byte store of a 64-bit or boolean register content related to `Xs` keeps `MemInj` with
the machine's `writeMem` of `Xs`, and the keys distinct. -/
theorem memInj_store (hA : AddrAgree ι) {m m' : Mem} {mm : Memory} (h : MemInj ι m mm)
    (hk : KeysNodup m) {p : Ptr} {a : BitVec 64} {x : Val} {Xs : BitVec 64}
    (ha : ι p.blk = some a) (hx : ValRel ι x Xs) (hf : Fits 64 x ∨ Fits 1 x)
    (hw : m.write p (Arm64.storeBytes 8 x) = some m') :
    MemInj ι m' (writeMem mm (a + p.off) 8 (BitVec.ofNat (8 * 8) (Xs.toNat % 2 ^ (8 * 8)))) ∧
      KeysNodup m' := by
  sorry

end GoFV.Proof.Gen
