import GoFV.Proof.Gen.Progs2
import GoFV.Gen.Check3

/-!
# The Progs of slice G3 under `runProg` (`docs/plans/proofs3.md` §4)

`progStep` of the Prog shapes slice G3 adds to G2's (`Progs2.lean`, `GoFV.Gen.Check3`), with
symbolic registers `REG_R0 + k` (`k < 32`) as in `Progs.lean`:

* the loads and stores of the `MOV` family (`movMem` opcodes `MOVD`, `MOVB`, `MOVBU`, `MOVH`,
  `MOVHU`, `MOVW`, `MOVWU`) at `off(Rn)` (`progStep_loadN`, `progStep_storeN`) or at a global
  `sym+off(SB)` (`progStep_globLoad`, `progStep_globStore`), the address outside the nil page;
* the extensions `MOVB… Rn, Rd` (`progStep_ext`);
* `AND $k, Rn, Rd`, `LSL $k, Rn, Rd`, `LSR $k, Rn, Rd`, `UBFX $lsb, Rn, $w, Rd`;
* `CMPW from, Rn` (the flags of the 32-bit `SUBS`, `progStep_cmpw`);
* the branches `CBZW`/`CBNZW` and `TBZ`/`TBNZ`.

The `MOV` family shares one reduction of `progEffect` (`movPre`: an opcode name that none of
`progEffect`'s branches before the `movMem` one takes), so each lemma holds for every `movMem`
opcode at once; `loadOp?_movMem`, `storeOp?_movMem` and `extOp?_movMem` give the `movMem` entry
of the opcodes `vkind3` emits, and `testBr_spec` the branch opcodes of `Cx.termG3`.
-/

namespace GoFV.Proof.Gen

open GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64 GoFV.Gen.Check

/-! ## The opcodes `vkind3` and `Cx.termG3` emit -/

/-- A load's opcode reads `n` bytes, sign-extended when `sg`. -/
theorem loadOp?_movMem {op : GoFV.SSA.Op} {as : As} {n : Nat} {sg : Bool}
    (h : loadOp? op = some (as, n, sg)) : ProgOp.movMem as.name = some (n, sg, false) := by
  unfold loadOp? at h
  split at h
  · cases h; rfl
  · unfold narrowLoad? at h
    split at h <;> first | (cases h; rfl) | cases h

/-- A store's opcode writes `n` bytes. -/
theorem storeOp?_movMem {op : GoFV.SSA.Op} {as : As} {n : Nat} (h : storeOp? op = some (as, n)) :
    ∃ sg, ProgOp.movMem as.name = some (n, sg, false) := by
  unfold storeOp? at h
  split at h
  · cases h; exact ⟨false, rfl⟩
  · unfold narrowStore? at h
    split at h <;> first | (cases h; exact ⟨_, rfl⟩) | cases h

/-- An extension's opcode moves `w / 8` bytes, sign-extended when `sg`; `w` is 8, 16 or 32. -/
theorem extOp?_movMem {op : GoFV.SSA.Op} {as : As} {w : Nat} {sg : Bool}
    (h : extOp? op = some (as, w, sg)) :
    ProgOp.movMem as.name = some (w / 8, sg, false) ∧ (w = 8 ∨ w = 16 ∨ w = 32) := by
  unfold extOp? at h
  split at h <;> first | (cases h; exact ⟨rfl, by omega⟩) | cases h

/-- The opcodes of a 32-bit register test or a bit test: `ZW` branches on zero with `CBZW`, `NZW`
with `CBNZW`, `TBZ` on a clear bit with `TBZ`, `TBNZ` with `TBNZ`; the second opcode is the
other one. -/
theorem testBr_spec {k : GoFV.SSA.BlockKind} {asm inv : As} (h : testBr k = some (asm, inv)) :
    (k = .ARM64ZW ∧ asm = .CBZW ∧ inv = .CBNZW) ∨ (k = .ARM64NZW ∧ asm = .CBNZW ∧ inv = .CBZW) ∨
      (k = .ARM64TBZ ∧ asm = .TBZ ∧ inv = .TBNZ) ∨ (k = .ARM64TBNZ ∧ asm = .TBNZ ∧ inv = .TBZ) := by
  unfold testBr at h
  split at h <;> (try cases h)
  · exact .inl ⟨rfl, rfl, rfl⟩
  · exact .inr (.inl ⟨rfl, rfl, rfl⟩)
  · exact .inr (.inr (.inl ⟨rfl, rfl, rfl⟩))
  · exact .inr (.inr (.inr ⟨rfl, rfl, rfl⟩))

/-- The facts a global operand `globA g name abi off a` fixes. -/
theorem globA_eq {g : G2In} {name : GoFV.SSA.GoStr} {abi : Nat} {off : Int} {a : Addr}
    (h : globA g name abi off a = true) :
    a.type = .MEM ∧ a.name = .EXTERN ∧ a.reg = 0 ∧ a.index = 0 ∧ a.offset = off ∧
      ∃ y, a.sym = some y ∧ g.syms[y]? = some (name, abi) := by
  simp only [globA, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  split at h6
  · rename_i y hy
    exact ⟨y, hy, beq_iff_eq.mp h6⟩
  · cases h6

/-! ## Operands -/

/-- A register source at 32 bits (`sf` false): its low word, zero-extended. -/
theorem ctx_src_reg32 {c : ProgCtx} {k : Nat} (hk : k < 32) :
    c.src false { type := .REG, reg := REG_R0 + k } =
      .ok (ProgOp.trunc false (c.s.rX (BitVec.ofNat 5 k))) := by
  simp only [ProgCtx.src, extReg?_r0 hk, ctx_x_r0 hk]
  rfl

/-- A constant source at 32 bits. -/
theorem ctx_src_const32 {c : ProgCtx} {o : Int} :
    c.src false (constA o) = .ok (ProgOp.trunc false (BitVec.ofInt 64 o)) := rfl

/-- The low word of a value truncated to 32 bits. -/
theorem trunc_false_setWidth (x : BitVec 64) : (ProgOp.trunc false x).setWidth 32 = x.setWidth 32 := by
  simp only [ProgOp.trunc, Bool.false_eq_true, ↓reduceIte]
  rw [BitVec.setWidth_setWidth_of_le _ (by omega)]
  simp

/-- The address of `off(Rn)` (no index, no write-back). -/
theorem ctx_mem_reg {c : ProgCtx} {kn : Nat} {off : Int} (hkn : kn < 32) (hsc : c.p.scond = 0) :
    c.mem (memA (REG_R0 + kn) off) = .ok (c.s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off, none) := by
  simp (config := { decide := true }) only [ProgCtx.mem, memA, ctx_x_r0 hkn, hsc]
  rfl

/-- The address of a global operand `sym+off(SB)`. -/
theorem ctx_mem_glob {c : ProgCtx} {a : Addr} {y : Nat} {off : Int} (h1 : a.type = .MEM)
    (h2 : a.name = .EXTERN) (h3 : a.offset = off) (h4 : a.sym = some y) :
    c.mem a = .ok (c.L.sym y + BitVec.ofInt 64 off, none) := by
  simp [ProgCtx.mem, h1, h2, h3, h4]
  rfl

/-! ## The `MOV` family -/

/-- An opcode name none of `progEffect`'s branches before the `movMem` one takes (and no skip). -/
private def movPre (name : String) : Prop :=
  name ∉ ["TEXT", "FUNCDATA", "PCDATA", "NOP"] ∧
  ProgOp.baseOf name ProgOp.binNames = none ∧ ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
  ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
  ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
  ProgOp.baseOf name ["MADD", "MSUB"] = none ∧
  ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] = none ∧
  ProgOp.baseOf name ["EXTR"] = none ∧
  ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] = none ∧
  ProgOp.baseOf name ["CSET", "CSETM"] = none

private theorem movPre_of {name : String} {n : Nat} {sg : Bool}
    (hm : ProgOp.movMem name = some (n, sg, false)) : movPre name := by
  unfold ProgOp.movMem at hm
  split at hm <;> (try cases hm) <;> simp (config := { decide := true }) [movPre]

private theorem isSkip_of {p : Prog} {n : Nat} {sg : Bool}
    (hm : ProgOp.movMem p.as.name = some (n, sg, false)) : p.isSkip = false := by
  have h := (movPre_of hm).1
  unfold Prog.isSkip
  split <;> rename_i has <;> (try rfl) <;> rw [has] at h <;> exact absurd (by decide) h

/-- A load of the `MOV` family from the address `a`. -/
private theorem eff_load {c : ProgCtx} {n kd : Nat} {sg : Bool} {a : BitVec 64} (hkd : kd < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, sg, false)) (hf : c.p.from_.type = .MEM)
    (hma : c.mem c.p.from_ = .ok (a, none)) (ht : c.p.to = regA (REG_R0 + kd)) :
    progEffect c = .ok (effWd { loads := [(a, n)] } kd
      (if sg then ProgOp.sextTo64 n ((readMem c.s.mem a n).setWidth 64)
       else (readMem c.s.mem a n).setWidth 64)) := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := movPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, hma, ht, regA, Eff.ld, ProgCtx.load,
    Bool.false_eq_true, ↓reduceIte]
  simp only [eff_wX_dest hkd]
  rfl

/-- A store of the `MOV` family of `X ks` to the address `a`. -/
private theorem eff_store {c : ProgCtx} {n ks : Nat} {sg : Bool} {a : BitVec 64} (hks : ks < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, sg, false)) (hf : c.p.from_ = regA (REG_R0 + ks))
    (ht : c.p.to.type = .MEM) (hma : c.mem c.p.to = .ok (a, none)) :
    progEffect c = .ok { stores := [(a, n, (c.s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))] } := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := movPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, ht, hma, regA, ctx_x_r0 hks,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A register move of the `MOV` family: the extension of the low `n` bytes. -/
private theorem eff_ext {c : ProgCtx} {n kn kd : Nat} {sg : Bool} (hkn : kn < 32) (hkd : kd < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, sg, false)) (hf : c.p.from_ = regA (REG_R0 + kn))
    (ht : c.p.to = regA (REG_R0 + kd)) :
    progEffect c = .ok (effWd {} kd (if sg then ProgOp.sextTo64 n (c.s.rX (BitVec.ofNat 5 kn))
      else ProgOp.maskN n (c.s.rX (BitVec.ofNat 5 kn)))) := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := movPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, ht, regA, fpIdx?_r0 hkn, fpIdx?_r0 hkd,
    ctx_x_r0 hkn]
  exact eff_wX_dest hkd

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- A load of `n` bytes at `a` outside the nil page into `X kd`. -/
private theorem step_load {n kd : Nat} {sg : Bool} {a : BitVec 64} (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, sg, false))
    (hf : p.from_.type = .MEM) (hma : (ProgCtx.mk L s p).mem p.from_ = .ok (a, none))
    (ht : p.to = regA (REG_R0 + kd)) (hnil : nilPage a = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (if sg then ProgOp.sextTo64 n ((readMem s.mem a n).setWidth 64)
       else (readMem s.mem a n).setWidth 64) with pc := next } := by
  have he := eff_load (c := ⟨L, s, p⟩) hkd hm hf hma ht
  have hnil' : (effWd { loads := [(a, n)] } kd
      (if sg then ProgOp.sextTo64 n ((readMem s.mem a n).setWidth 64)
       else (readMem s.mem a n).setWidth 64)).nilAccess? = none := by
    by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?, List.find?, hnil]
  rw [progStep_eq hn (isSkip_of hm) he hnil']
  by_cases h : kd = 31
  · subst h; rfl
  · simp only [effWd, h, ↓reduceIte, Eff.apply, List.foldr]
    rfl

/-- A store of the low `n` bytes of `X ks` at `a` outside the nil page. -/
private theorem step_store {n ks : Nat} {sg : Bool} {a : BitVec 64} (hks : ks < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, sg, false))
    (hf : p.from_ = regA (REG_R0 + ks)) (ht : p.to.type = .MEM)
    (hma : (ProgCtx.mk L s p).mem p.to = .ok (a, none)) (hnil : nilPage a = false) :
    progStep L p s = .ok { s with
      mem := writeMem s.mem a n (BitVec.ofNat (8 * n) ((s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))),
      pc := next } := by
  have he := eff_store (c := ⟨L, s, p⟩) hks hm hf ht hma
  rw [progStep_eq hn (isSkip_of hm) he (by simp [Eff.nilAccess?, List.find?, hnil])]
  rfl

/-- `MOV{D,B,BU,H,HU,W,WU} off(Rn), Rd` (any `movMem` opcode of the general registers), the
address outside the nil page: the `n` bytes there, sign-extended when `sg`. -/
theorem progStep_loadN {kn kd n : Nat} {sg : Bool} {off : Int} (hkn : kn < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, sg, false))
    (hf : p.from_ = memA (REG_R0 + kn) off) (hsc : p.scond = 0) (ht : p.to = regA (REG_R0 + kd))
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (if sg then ProgOp.sextTo64 n
          ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) n).setWidth 64)
       else (readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) n).setWidth 64) with
        pc := next } := by
  have hma : (ProgCtx.mk L s p).mem p.from_ =
      .ok (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off, none) := by
    rw [hf]; exact ctx_mem_reg hkn hsc
  exact step_load hkd hn hm (by rw [hf]; rfl) hma ht hnil

/-- `MOV{D,B,BU,H,HU,W,WU} sym+off(SB), Rd` (a global operand: `globA_eq`), the address outside
the nil page. -/
theorem progStep_globLoad {kd n y : Nat} {sg : Bool} {off : Int} (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, sg, false))
    (hf1 : p.from_.type = .MEM) (hf2 : p.from_.name = .EXTERN) (hf3 : p.from_.offset = off)
    (hf4 : p.from_.sym = some y) (ht : p.to = regA (REG_R0 + kd))
    (hnil : nilPage (L.sym y + BitVec.ofInt 64 off) = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (if sg then ProgOp.sextTo64 n ((readMem s.mem (L.sym y + BitVec.ofInt 64 off) n).setWidth 64)
       else (readMem s.mem (L.sym y + BitVec.ofInt 64 off) n).setWidth 64) with pc := next } :=
  step_load hkd hn hm hf1 (ctx_mem_glob hf1 hf2 hf3 hf4) ht hnil

/-- `MOV{D,B,H,W} Rs, off(Rn)` (any `movMem` opcode of the general registers), the address
outside the nil page: the low `n` bytes of `X ks`. -/
theorem progStep_storeN {kn ks n : Nat} {sg : Bool} {off : Int} (hkn : kn < 32) (hks : ks < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, sg, false))
    (hf : p.from_ = regA (REG_R0 + ks)) (hsc : p.scond = 0) (ht : p.to = memA (REG_R0 + kn) off)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false) :
    progStep L p s = .ok { s with
      mem := writeMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) n
        (BitVec.ofNat (8 * n) ((s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))),
      pc := next } := by
  have hma : (ProgCtx.mk L s p).mem p.to =
      .ok (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off, none) := by
    rw [ht]; exact ctx_mem_reg hkn hsc
  exact step_store hks hn hm hf (by rw [ht]; rfl) hma hnil

/-- `MOV{D,B,H,W} Rs, sym+off(SB)` (a global operand: `globA_eq`), the address outside the nil
page. -/
theorem progStep_globStore {ks n y : Nat} {sg : Bool} {off : Int} (hks : ks < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, sg, false))
    (hf : p.from_ = regA (REG_R0 + ks)) (ht1 : p.to.type = .MEM) (ht2 : p.to.name = .EXTERN)
    (ht3 : p.to.offset = off) (ht4 : p.to.sym = some y)
    (hnil : nilPage (L.sym y + BitVec.ofInt 64 off) = false) :
    progStep L p s = .ok { s with
      mem := writeMem s.mem (L.sym y + BitVec.ofInt 64 off) n
        (BitVec.ofNat (8 * n) ((s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))),
      pc := next } :=
  step_store hks hn hm hf ht1 (ctx_mem_glob ht1 ht2 ht3 ht4) hnil

/-- The extensions `MOV{B,BU,H,HU,W,WU} Rn, Rd` (any `movMem` opcode of the general registers;
`MOVD` is the move): the low `n` bytes of `X kn`, sign- or zero-extended. -/
theorem progStep_ext {kn kd n : Nat} {sg : Bool} (hkn : kn < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, sg, false))
    (hf : p.from_ = regA (REG_R0 + kn)) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (if sg then ProgOp.sextTo64 n (s.rX (BitVec.ofNat 5 kn))
       else ProgOp.maskN n (s.rX (BitVec.ofNat 5 kn))) with pc := next } := by
  rw [progStep_eq hn (isSkip_of hm) (eff_ext (c := ⟨L, s, p⟩) hkn hkd hm hf ht)
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-! ## Narrow ALU ops -/

theorem logical_and (x y : BitVec 64) : (logical true 0 x y).1 = x &&& y := by
  simp [logical, sizedF]

/-- The amount of a shift by a non-negative constant `k`. -/
theorem ofInt_toNat_mod {k : Int} (hk : 0 ≤ k) : (BitVec.ofInt 64 k).toNat % 64 = k.toNat % 64 := by
  rw [BitVec.toNat_ofInt]
  have : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := rfl
  rw [this]
  omega

theorem dp2Op_lsl (x y : BitVec 64) : dp2Op true 8 x y = x <<< (y.toNat % 64) := by
  simp [dp2Op, sized, GoFV.SSA.Sem.Arm64.Shift.apply]

theorem dp2Op_lsr (x y : BitVec 64) : dp2Op true 9 x y = x >>> (y.toNat % 64) := by
  simp [dp2Op, sized, GoFV.SSA.Sem.Arm64.Shift.apply]

/-- `AND $k, Rn, Rd`. -/
theorem progStep_andK {kn kd : Nat} {k : Int} (hkn : kn < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .AND) (hf : p.from_ = constA k)
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (s.rX (BitVec.ofNat 5 kn) &&& BitVec.ofInt 64 k) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have hname : As.name .AND = "AND" := rfl
  have he : progEffect ⟨L, s, p⟩ =
      .ok (effWd {} kd (s.rX (BitVec.ofNat 5 kn) &&& BitVec.ofInt 64 k)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf, ht, hrn, regA, constA,
      ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ProgOp.binOp,
      logical_and]
    simp only [eff_wX_dest hkd]
    by_cases h : kd = 31 <;> simp [effWd, h] <;> rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-- A shift by a constant (`LSL`/`LSR`/`ASR`/`ROR $k, Rn, Rd`, `op` named `nm`, at 64 bits). -/
private theorem eff_shiftK {c : ProgCtx} {kn kd : Nat} {k : Int} {nm : String} (hkn : kn < 32)
    (hkd : kd < 32) (hb : ProgOp.baseOf c.p.as.name ProgOp.binNames = some (nm, true))
    (hnm : ["LSL", "LSR", "ASR", "ROR"].contains nm = true) (hf : c.p.from_ = constA k)
    (hr : c.p.reg = REG_R0 + kn) (ht : c.p.to = regA (REG_R0 + kd)) :
    progEffect c = .ok (effWd {} kd
      (ProgOp.binOp nm true (c.s.rX (BitVec.ofNat 5 kn)) (BitVec.ofInt 64 k) false).1) := by
  have hrn := rn_reg (c := c) hr
  unfold progEffect
  simp only [hb, hf, constA, hnm, beq_self_eq_true, Bool.true_and, ↓reduceIte, hrn,
    ctx_src_reg hkn, ProgOp.trunc, ht, regA]
  exact eff_wX_dest hkd

/-- `LSL $k, Rn, Rd` (`0 ≤ k`). -/
theorem progStep_lslK {kn kd : Nat} {k : Int} (hkn : kn < 32) (hkd : kd < 32) (hk : 0 ≤ k)
    (hn : L.nextAddr p.id = some next) (has : p.as = .LSL) (hf : p.from_ = constA k)
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (s.rX (BitVec.ofNat 5 kn) <<< (k.toNat % 64)) with pc := next } := by
  have hb : ProgOp.baseOf p.as.name ProgOp.binNames = some ("LSL", true) := by
    rw [has]; simp (config := { decide := true })
  have he := eff_shiftK (c := ⟨L, s, p⟩) hkn hkd hb (by decide) hf hr ht
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]
  simp (config := { decide := true }) only [ProgOp.binOp, dp2Op_lsl, ofInt_toNat_mod hk]

/-- `LSR $k, Rn, Rd` (`0 ≤ k`). -/
theorem progStep_lsrK {kn kd : Nat} {k : Int} (hkn : kn < 32) (hkd : kd < 32) (hk : 0 ≤ k)
    (hn : L.nextAddr p.id = some next) (has : p.as = .LSR) (hf : p.from_ = constA k)
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (s.rX (BitVec.ofNat 5 kn) >>> (k.toNat % 64)) with pc := next } := by
  have hb : ProgOp.baseOf p.as.name ProgOp.binNames = some ("LSR", true) := by
    rw [has]; simp (config := { decide := true })
  have he := eff_shiftK (c := ⟨L, s, p⟩) hkn hkd hb (by decide) hf hr ht
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]
  simp (config := { decide := true }) only [ProgOp.binOp, dp2Op_lsr, ofInt_toNat_mod hk]

/-- The facts `ubfxOK` fixes. -/
theorem ubfxOK_eq {lsb width rn rd : Int} {p : Prog} (h : ubfxOK lsb width rn rd p = true) :
    p.as = .UBFX ∧ p.from_ = constA lsb ∧ p.reg = rn ∧ p.to = regA rd ∧
      ∃ x, p.rest = #[(x, constA width)] := by
  unfold ubfxOK at h
  repeat rw [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩, h7⟩ := h
  refine ⟨beq_iff_eq.mp h1, beq_iff_eq.mp h2, beq_iff_eq.mp h3, beq_iff_eq.mp h4, ?_⟩
  generalize hr : p.rest = r at h7
  obtain ⟨l⟩ := r
  rcases l with _ | ⟨⟨x, a⟩, _ | ⟨_, _⟩⟩
  · exact absurd h7 Bool.false_ne_true
  · have h7' : (a == constA width) = true := h7
    exact ⟨x, by rw [beq_iff_eq.mp h7']⟩
  · exact absurd h7 Bool.false_ne_true

/-- `UBFX` of a bitfield auxint `lsb · 256 + width` (`width < 256`, the auxint below `2 ^ 63`). -/
theorem ubfx_ofNat {lsb width : Nat} (hw : width < 256) (hk : lsb * 256 + width < 2 ^ 63)
    (x : BitVec 64) :
    GoFV.SSA.Sem.Arm64.ubfx (Int64.ofNat (lsb * 256 + width)) x =
      (x >>> lsb) &&& GoFV.SSA.Sem.Arm64.mask width := by
  have h : (Int64.ofNat (lsb * 256 + width)).toInt = ((lsb * 256 + width : Nat) : Int) := by
    rw [Int64.toInt_ofNat_of_lt hk]
  simp only [GoFV.SSA.Sem.Arm64.ubfx, GoFV.SSA.Sem.Arm64.bf, h, Int.toNat_natCast]
  congr 2 <;> omega

/-- `UBFX $lsb, Rn, $width, Rd` (`ubfxOK`; `0 ≤ width < 256`, the auxint
`lsb · 256 + width` below `2 ^ 63`): bits `lsb …` of `X kn`, `width` of them. -/
theorem progStep_ubfx {kn kd : Nat} {lsb width : Int} (hkn : kn < 32) (hkd : kd < 32)
    (hw0 : 0 ≤ width) (hw : width < 256) (hlw : lsb * 256 + width < 2 ^ 63)
    (hn : L.nextAddr p.id = some next) (hu : ubfxOK lsb width (REG_R0 + kn) (REG_R0 + kd) p = true) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      ((s.rX (BitVec.ofNat 5 kn) >>> lsb.toNat) &&& GoFV.SSA.Sem.Arm64.mask width.toNat) with
        pc := next } := by
  obtain ⟨has, hf, hr, ht, x, hrest⟩ := ubfxOK_eq hu
  have hname : As.name .UBFX = "UBFX" := rfl
  have hrest0 : (ProgCtx.mk L s p).rest 0 = .ok (constA width) := by
    simp [ProgCtx.rest, hrest]
    rfl
  have hval : ProgOp.trunc true (GoFV.SSA.Sem.Arm64.ubfx
      (Int64.ofNat (lsb.toNat * 256 + width.toNat)) (ProgOp.trunc true (s.rX (BitVec.ofNat 5 kn)))) =
      (s.rX (BitVec.ofNat 5 kn) >>> lsb.toNat) &&& GoFV.SSA.Sem.Arm64.mask width.toNat := by
    simp only [ProgOp.trunc, ↓reduceIte]
    exact ubfx_ofNat (by omega) (by omega) _
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      ((s.rX (BitVec.ofNat 5 kn) >>> lsb.toNat) &&& GoFV.SSA.Sem.Arm64.mask width.toNat)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames, hrest0, hf, hr, ht, constA, regA, ctx_x_r0 hkn, ctx_x_r0 hkd]
    rw [← hval]
    exact eff_wX_dest hkd
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-! ## 32-bit compares -/

/-- The flags of the 32-bit `SUBS`. -/
theorem addSub_flags32 (x y : BitVec 64) :
    (addSub false true x y).2 = (GoFV.SSA.Sem.Arm64.subFlags (x.setWidth 32) (y.setWidth 32)).2 := by
  simp [addSub, sizedF, GoFV.SSA.Sem.Arm64.subFlags]

/-- `CMPW from, Rn` with `from` a register or a constant whose 32-bit source is `y`
(`ctx_src_reg32`, `ctx_src_const32`): the flags of the 32-bit `SUBS` of the low words. -/
theorem progStep_cmpw {kn : Nat} {y : BitVec 64} (hkn : kn < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .CMPW)
    (hy : ProgCtx.src ⟨L, s, p⟩ false p.from_ = .ok y) (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := (GoFV.SSA.Sem.Arm64.subFlags ((s.rX (BitVec.ofNat 5 kn)).setWidth 32)
        (y.setWidth 32)).2, pc := next } := by
  have hname : As.name .CMPW = "CMPW" := rfl
  have he : progEffect ⟨L, s, p⟩ = .ok { flags := some (GoFV.SSA.Sem.Arm64.subFlags
      ((s.rX (BitVec.ofNat 5 kn)).setWidth 32) (y.setWidth 32)).2 } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hr, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames, ProgOp.endsS, ProgOp.chopS, ctx_src_reg32 hkn, hy, ProgOp.binOp,
      addSub_flags32]
    simp only [bind, Except.bind, pure, Except.pure, trunc_false_setWidth]
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

/-- `CMPW Rm, Rn`. -/
theorem progStep_cmpwReg {kn km : Nat} (hkn : kn < 32) (hkm : km < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .CMPW) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := (GoFV.SSA.Sem.Arm64.subFlags ((s.rX (BitVec.ofNat 5 kn)).setWidth 32)
        ((s.rX (BitVec.ofNat 5 km)).setWidth 32)).2, pc := next } := by
  rw [progStep_cmpw hkn hn has (by rw [hf]; exact ctx_src_reg32 hkm) hr, trunc_false_setWidth]

/-- `CMPW $k, Rn`. -/
theorem progStep_cmpwConst {kn : Nat} {k : Int} (hkn : kn < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .CMPW) (hf : p.from_ = constA k)
    (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := (GoFV.SSA.Sem.Arm64.subFlags ((s.rX (BitVec.ofNat 5 kn)).setWidth 32)
        ((BitVec.ofInt 64 k).setWidth 32)).2, pc := next } := by
  rw [progStep_cmpw hkn hn has (by rw [hf]; exact ctx_src_const32) hr, trunc_false_setWidth]

/-! ## Branches -/

/-- A Prog whose effect is a branch to `t` taken when `b` (as `Branch.lean`'s). -/
private theorem progStep_br {t : BitVec 64} {b : Bool} (hn : L.nextAddr p.id = some next)
    (hs : p.isSkip = false) (he : progEffect ⟨L, s, p⟩ = .ok (if b then { pc := some t } else {})) :
    progStep L p s = .ok { s with pc := if b then t else next } := by
  rw [progStep_eq hn hs he (by cases b <;> rfl)]
  cases b <;> rfl

private theorem trunc_false_eq_zero (x : BitVec 64) :
    ProgOp.trunc false x = 0#64 ↔ x.setWidth 32 = 0#32 := by
  simp only [ProgOp.trunc, Bool.false_eq_true, ↓reduceIte]
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 32) h
    rwa [BitVec.setWidth_setWidth_of_le _ (by omega)] at this
  · intro h
    rw [h]
    rfl

private theorem trunc_false_beq_zero (x : BitVec 64) :
    (ProgOp.trunc false x == 0) = (x.setWidth 32 == 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact trunc_false_eq_zero x

/-- `CBZW Rk, target` / `CBNZW Rk, target`: on the low word of `X k`. -/
theorem progStep_cbzw {k tid : Nat} {t : BitVec 64} (hk : k < 32) (hn : L.nextAddr p.id = some next)
    (has : p.as = .CBZW ∨ p.as = .CBNZW) (hf : p.from_ = regA (REG_R0 + k)) (ht : p.to = brA tid)
    (hL : L.addr tid = some t) :
    progStep L p s = .ok { s with
      pc := if ((s.rX (BitVec.ofNat 5 k)).setWidth 32 == 0) = (p.as == .CBZW) then t else next } := by
  have hT := ctx_target (c := ⟨L, s, p⟩) hL
  simp only [brA] at hT
  rcases has with has | has
  · have hname : As.name .CBZW = "CBZW" := rfl
    have h := progStep_br (b := ((s.rX (BitVec.ofNat 5 k)).setWidth 32 == 0)) (s := s) (t := t) hn
      (by simp [Prog.isSkip, has]) ?_
    · rw [h]
      simp [has]
    · unfold progEffect
      simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
        ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, ht, brA, hT, hf,
        regA, ctx_x_r0 hk, show ProgOp.endsS "CBZW" "W" = true by decide, Bool.not_true]
      simp only [show "CBZ".toList.isPrefixOf "CBZW".toList = true by decide]
      simp only [bind, Except.bind]
      simp only [pure, Except.pure, trunc_false_beq_zero]
      simp
  · have hname : As.name .CBNZW = "CBNZW" := rfl
    have h := progStep_br (b := !((s.rX (BitVec.ofNat 5 k)).setWidth 32 == 0)) (s := s) (t := t) hn
      (by simp [Prog.isSkip, has]) ?_
    · rw [h, has, show (As.CBNZW == As.CBZW) = false by decide]
      simp
    · unfold progEffect
      simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
        ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, ht, brA, hT, hf,
        regA, ctx_x_r0 hk, show ProgOp.endsS "CBNZW" "W" = true by decide, Bool.not_true]
      simp only [show "CBZ".toList.isPrefixOf "CBNZW".toList = false by decide]
      simp only [bind, Except.bind]
      simp only [pure, Except.pure, trunc_false_beq_zero]
      simp

/-- `TBZ $bit, Rk, target` / `TBNZ $bit, Rk, target`: on bit `bit` of `X k`. -/
theorem progStep_tbz {k tid : Nat} {bit : Int} {t : BitVec 64} (hk : k < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .TBZ ∨ p.as = .TBNZ)
    (hf : p.from_ = constA bit) (hr : p.reg = REG_R0 + k) (ht : p.to = brA tid)
    (hL : L.addr tid = some t) :
    progStep L p s = .ok { s with
      pc := if (s.rX (BitVec.ofNat 5 k)).getLsbD bit.toNat = (p.as == .TBNZ) then t else next } := by
  have hT := ctx_target (c := ⟨L, s, p⟩) hL
  simp only [brA] at hT
  rcases has with has | has
  · have hname : As.name .TBZ = "TBZ" := rfl
    have h := progStep_br (b := !(s.rX (BitVec.ofNat 5 k)).getLsbD bit.toNat) (s := s) (t := t) hn
      (by simp [Prog.isSkip, has]) ?_
    · rw [h, has, show (As.TBZ == As.TBNZ) = false by decide]
      simp
    · unfold progEffect
      simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
        ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, ht, brA, hT, hf,
        hr, constA, ctx_x_r0 hk]
      simp
      rfl
  · have hname : As.name .TBNZ = "TBNZ" := rfl
    have h := progStep_br (b := (s.rX (BitVec.ofNat 5 k)).getLsbD bit.toNat) (s := s) (t := t) hn
      (by simp [Prog.isSkip, has]) ?_
    · rw [h, has, show (As.TBNZ == As.TBNZ) = true by decide]
    · unfold progEffect
      simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
        ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, ht, brA, hT, hf,
        hr, constA, ctx_x_r0 hk]
      simp
      rfl

end GoFV.Proof.Gen
