import GoFV.Asm.CheckObj

/-!
# The linked code of one function (`docs/plans/proofs3.md` §2, row D2–D5)

`runMach` runs `Code`, the words at their linked addresses. `linkCode base sym t rs` is the
function's text `t` placed at `base`, with symbol `y<n>` at `sym n` and the relocations `rs`
applied as Go's linker applies them (`cmd/link/internal/arm64/asm.go`, `archreloc`, internal
linking):

* `R_CALLARM64` (and its weak form): the word ORed with `((T − P) >> 2) & 0x3ffffff`, `T` the
  target `sym n + add`, `P` the word's address; the linker rejects `|T − P| ≥ 2^27`.
* `R_ADDRARM64`, `R_ARM64_PCREL_LDST{8,16,32,64}` (two words, `ADRP` then `ADD` or the access):
  with `t = T − (P &^ 0xfff)` (rejected if `|t| ≥ 2^32`), the `ADRP` ORed with
  `((t >> 12) & 3) << 29 | ((t >> 14) & 0x7ffff) << 5` and the second word with
  `(t & 0xfff) >> s << 10`, `s` the access's `log2` size (rejected if `t & (2^s − 1) ≠ 0`).
* Relocations of size 0 (`R_USEIFACE`, `R_CALLIND`, …) patch nothing.

This model is part of the end-to-end statement (the trusted linker, `docs/proofs/STATUS.md`).
It fails, and so excludes, two further cases: a call whose distance is not a multiple of 4
(text symbols are aligned; the linker would truncate it) and relocation types it does not
know.
-/

namespace GoFV.Asm.CheckObj

open GoFV.Arm64

/-- The OR-patch the linker applies to the word at offset `o` for relocation `r`, or `0` if `r`
does not cover `o`. -/
def relocPatch (base : BitVec 64) (sym : Nat → BitVec 64) (r : Reloc) (o : Nat) :
    Except String (BitVec 32) := do
  if r.siz == 0 then return 0
  let some y := r.sym | throw "relocation without symbol"
  let tgt := sym y + BitVec.ofInt 64 r.add
  if isCallReloc r.type then
    if r.off != (o : Int) then return 0
    let d := (tgt - (base + BitVec.ofNat 64 o)).toInt
    if d < -2 ^ 27 || d ≥ 2 ^ 27 || d % 4 != 0 then throw "call relocation distance"
    return BitVec.ofInt 32 (d / 4) &&& 0x3ffffff
  let sc? : Option Nat := if r.type == "R_ADDRARM64" then some 0 else ldstScale r.type
  let some sc := sc? | throw s!"relocation {r.type}"
  if r.off != (o : Int) && r.off + 4 != (o : Int) then return 0
  if r.off < 0 then throw "relocation offset"
  let page := (base + BitVec.ofInt 64 r.off) &&& ~~~(0xFFF : BitVec 64)
  let tt := (tgt - page).toInt
  if tt < -2 ^ 32 || tt ≥ 2 ^ 32 then throw "address relocation distance"
  let lo := (tgt.toNat % 4096)
  if r.off == (o : Int) then
    return BitVec.ofNat 32 ((tt / 4096 % 4).toNat * 2 ^ 29 + (tt / 16384 % 524288).toNat * 32)
  if lo % 2 ^ sc != 0 then throw "misaligned load/store relocation"
  return BitVec.ofNat 32 (lo / 2 ^ sc * 1024)

/-- The linked word at offset `o`. -/
def linkWord (base : BitVec 64) (sym : Nat → BitVec 64) (t : ByteArray) (rs : List Reloc)
    (o : Nat) : Except String (BitVec 32) :=
  rs.foldlM (fun w r => do return w ||| (← relocPatch base sym r o)) (wordAt t o)

/-- The linked code: the words of `t` at `base` (offsets below `t.size`, multiples of 4). Fails
where linking a word fails. -/
def linkCode (base : BitVec 64) (sym : Nat → BitVec 64) (t : ByteArray) (rs : List Reloc) :
    Except String Code := do
  for o in List.range (t.size / 4) do
    let _ ← linkWord base sym t rs (4 * o)
  return fun a =>
    let d := (a - base).toNat
    if d % 4 = 0 ∧ d + 4 ≤ t.size then (linkWord base sym t rs d).toOption else none

end GoFV.Asm.CheckObj
