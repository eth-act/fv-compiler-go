import GoFV.Proof.Obj.Basic

/-!
# The linked words (`GoFV/Asm/CheckObjLink.lean`)

`linkCode` places a word of the text at `base + o`; a word no relocation patches is the text's
word; a relocated word decodes to the instruction the validator read with the relocated field
filled in so that it reaches the target `sym y + add`: `BL`/`B` (`R_CALLARM64`), `ADRP`
(`R_ADDRARM64`, `R_ARM64_PCREL_LDST*`: the target's page), and the `ADD` or load/store after it
(the target's offset in its page).
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj

variable {base : BitVec 64} {sym : Nat → BitVec 64} {t : ByteArray} {rs : List Reloc}
  {code : Code}

/-- The word at a text offset is mapped at `base + o`. -/
theorem linkCode_at (h : linkCode base sym t rs = .ok code) {o : Nat} (ho : o % 4 = 0)
    (hs : o + 4 ≤ t.size) :
    ∃ w, linkWord base sym t rs o = .ok w ∧ code (base + BitVec.ofNat 64 o) = some w := by
  sorry

/-- A word no relocation patches is the text's word. -/
theorem linkWord_plain {o : Nat} {w : BitVec 32} (h : linkWord base sym t rs o = .ok w)
    (hc : covering rs o = []) : w = wordAt t o := by
  sorry

/-- A word one relocation patches is the text's word ORed with that relocation's patch. -/
theorem linkWord_one {o : Nat} {w : BitVec 32} {r : Reloc} (h : linkWord base sym t rs o = .ok w)
    (hc : covering rs o = [r]) : ∃ q, relocPatch base sym r o = .ok q ∧ w = wordAt t o ||| q := by
  sorry

/-- `R_CALLARM64` on `BL`/`B` with a zero offset field: the linked word branches to the target. -/
theorem decode_call {w : BitVec 32} {link : Bool} {r : Reloc} {o y : Nat} {q : BitVec 32}
    (hd : decode w = some (.b link 0)) (hcall : isCallReloc r.type = true) (hoff : r.off = o)
    (hy : r.sym = some y) (hp : relocPatch base sym r o = .ok q) :
    ∃ imm26, decode (w ||| q) = some (.b link imm26) ∧
      (base + BitVec.ofNat 64 o) + (imm26 ++ (0 : BitVec 2)).signExtend 64 =
        sym y + BitVec.ofInt 64 r.add := by
  sorry

/-- The `ADRP` of a two-word relocation: the linked word computes the target's page. -/
theorem decode_adrp {w : BitVec 32} {rd : Reg} {r : Reloc} {o y : Nat} {q : BitVec 32}
    (hd : decode w = some (.adr true 0 rd)) (hcall : isCallReloc r.type = false)
    (hoff : r.off = o) (hy : r.sym = some y) (hp : relocPatch base sym r o = .ok q) :
    ∃ imm, decode (w ||| q) = some (.adr true imm rd) ∧
      ((base + BitVec.ofNat 64 o) &&& ~~~(0xFFF : BitVec 64)) + (imm.signExtend 64 <<< 12) =
        (sym y + BitVec.ofInt 64 r.add) &&& ~~~(0xFFF : BitVec 64) := by
  sorry

/-- The `ADD` of `R_ADDRARM64`: the linked word adds the target's offset in its page. -/
theorem decode_addLo {w : BitVec 32} {rn rd : Reg} {r : Reloc} {o y : Nat} {q : BitVec 32}
    (hd : decode w = some (.addSubImm true false false false 0 rn rd))
    (hty : r.type = "R_ADDRARM64") (hoff : r.off = o) (hy : r.sym = some y)
    (hp : relocPatch base sym r (o + 4) = .ok q) :
    ∃ imm12, decode (w ||| q) = some (.addSubImm true false false false imm12 rn rd) ∧
      ((sym y + BitVec.ofInt 64 r.add) &&& ~~~(0xFFF : BitVec 64)) + imm12.setWidth 64 =
        sym y + BitVec.ofInt 64 r.add := by
  sorry

/-- The load/store of `R_ARM64_PCREL_LDST*`: the linked word's scaled offset is the target's
offset in its page. -/
theorem decode_ldstLo {w : BitVec 32} {size opc : BitVec 2} {rn rt : Reg} {r : Reloc} {o y : Nat}
    {q : BitVec 32} (hd : decode w = some (.ldst size false opc (.uimm 0) rn rt))
    (hsc : ldstScale r.type = some size.toNat) (hoff : r.off = o) (hy : r.sym = some y)
    (hp : relocPatch base sym r (o + 4) = .ok q) :
    ∃ imm12, decode (w ||| q) = some (.ldst size false opc (.uimm imm12) rn rt) ∧
      ((sym y + BitVec.ofInt 64 r.add) &&& ~~~(0xFFF : BitVec 64)) +
          BitVec.ofNat 64 (imm12.toNat * 2 ^ size.toNat) =
        sym y + BitVec.ofInt 64 r.add := by
  sorry

end GoFV.Proof.Obj
