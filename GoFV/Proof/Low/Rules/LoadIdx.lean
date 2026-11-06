import GoFV.Proof.Low.Rules.Fold
import GoFV.Proof.Low.Rules.Peep

/-!
# Lowering rule lemmas: indexed loads (`ARM64.rules:695-746`, `750-753`)

The register-indexed loads (`MOV…loadidx`, `MOV…loadidx{2,4,8}`, `FMOV…loadidx*`) are lowered
terms whose value is `Arm64.loadIdx`: the load at the address of `ADD` of the base and the
(scaled) index (#385).

* `(MOV…load [off] {sym} (ADD ptr idx) mem) && off == 0 && sym == nil => (MOV…loadidx ptr idx
  mem)` (695-701): the validator admits the instance without a symbol (`Pat.addrOKL`), so the
  load's address is the `ADD`'s at offset 0. `ADD` at a shape other than boolean is `ADD` at
  `.other` (`add_other`), and a value read at a shape with a whole register (`armReadW` of a
  load's base: 64 bits) has the same address at offset 0, or none (`addr_retypeL_zero`).
* `(MOV…load [off] {sym} (ADDshiftLL [k] ptr idx) mem) && … => (MOV…loadidx{2,4,8} ptr idx mem)`
  (725-729): `ADDshiftLL` adds `idx << k = idx · 2^k` (`addSh_ll`, `shl_mul`).
* `(MOV…loadidx ptr (SLLconst [k] idx) mem) => (MOV…loadidx{2,4,8} ptr idx mem)` and the swapped
  forms (730-734, 737-739, 750-753), `(MOVH…loadidx ptr (ADD idx idx) mem) => (MOVH…loadidx2 ptr
  idx mem)` (735-736, 740-741): the index register is `idx · 2^k` or `poison` at its shape
  (`retypeL_res_wide`), and `ADD` takes either argument as the base (`add_int_comm`).
* `(MOV…loadidx ptr (MOVDconst [c]) mem) && is32Bit(c) => (MOV…load [int32(c)] ptr mem)` and the
  swapped forms (705-718), `(MOV…loadidx{2,4,8} ptr (MOVDconst [c]) mem) && is32Bit(c<<k) =>
  (MOV…load [int32(c)<<k] ptr mem)` (742-746): the address of `ADD ptr c` at offset 0 is `ptr`'s
  at offset `c`, or none (`addr_add_imm`); `int32(c)<<k` is `c · 2^k` modulo `2^64` when `c<<k`
  is a 32-bit integer (`imm_shl`).

The floating-point loads `FMOV{S,D}load` are atoms, not terms: the rules to or from them (702-703,
719-722, 748-749, 754-755) are not proven.
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- A shape with a whole register is not boolean. -/
theorem ne_bool_of_wide {T : Ty} (h : 64 ≤ argWidth T) : T ≠ .bool := by
  rintro rfl; simp [argWidth] at h

/-- A 64-bit register result at a shape other than boolean is the 64-bit integer. -/
theorem res_of_ne_bool {T : Ty} (h : T ≠ .bool) (r : BitVec 64) : Arm64.res T r = .int .w64 r := by
  cases T <;> first | rfl | exact absurd rfl h

/-- `ADD` at a shape other than boolean is `ADD` at `.other`. -/
theorem add_other {T : Ty} (h : T ≠ .bool) (args : List Val) :
    Arm64.add T args = Arm64.add .other args := by
  unfold Arm64.add Arm64.op2
  simp only [res_of_ne_bool h, res_of_ne_bool (T := .other) (fun h => by cases h)]

/-- `a + d` (`Arm64.addP`) at a shape other than boolean is `ADD` of `a` and the integer `d`. -/
theorem addP_other {T : Ty} (h : T ≠ .bool) (x : Val) (d : BitVec 64) :
    Arm64.addP T x d = Arm64.add .other [x, .int .w64 d] := by
  cases x <;> simp [Arm64.addP, Arm64.add, Arm64.op2, Arm64.reg, Arm64.res]

/-- `ADD` of an integer and `x` is `ADD` of `x` and the integer. -/
theorem add_int_comm (x : Val) (d : BitVec 64) :
    Arm64.add .other [.int .w64 d, x] = Arm64.add .other [x, .int .w64 d] := by
  cases x <;> simp [Arm64.add, Arm64.op2, Arm64.reg, BitVec.add_comm]

/-- `ADD` of `poison` is `poison`. -/
theorem add_poison_right (x : Val) : Arm64.add .other [x, .poison] = .poison := by
  cases x <;> rfl

/-- `ADD` of `poison` is `poison`. -/
theorem add_poison_left (x : Val) : Arm64.add .other [.poison, x] = .poison := by
  cases x <;> rfl

/-- A pointer's word addresses the pointer. -/
theorem addr_word_zero (p : Ptr) : Arm64.addr p.word 0 = some p := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨hc, a, ha, h⟩ <;> rw [h]
  · simp [Arm64.addr, Ptr.add]
  · simp [Arm64.addr, Arm64.reg, Ptr.ofAddr_addr hc ha]

/-- A pointer addresses itself. -/
theorem addr_ptr_zero (p : Ptr) : Arm64.addr (.ptr p) 0 = some p := by
  simp [Arm64.addr, Ptr.add]

/-- A value read at a shape with a whole register addresses what it did, or nothing. -/
theorem addr_retypeL_zero (v : Val) {T : Ty} (hT : 64 ≤ argWidth T) :
    Arm64.addr (v.retypeL T) 0 = none ∨ Arm64.addr (v.retypeL T) 0 = Arm64.addr v 0 := by
  cases T with
  | int w =>
    cases w <;> simp [argWidth, Width.bits] at hT
    right
    cases v with
    | int w x =>
      cases w <;> simp [Val.retypeL, Val.widen, Val.retype, Arm64.addr, Arm64.reg, Width.bits]
    | ptr p => simp only [Val.retypeL, Val.widen, Val.retype, addr_word_zero, addr_ptr_zero]
    | bool b => cases b <;> simp [Val.retypeL, Val.widen, Val.retype, Arm64.addr, Arm64.reg]
    | _ => simp [Val.retypeL, Val.widen, Val.retype, Arm64.addr, Arm64.reg]
  | ptr e =>
    right
    cases v with
    | int w x =>
      cases w <;> simp [Val.retypeL, Val.widen, Val.retype, Arm64.addr, Arm64.reg, Width.bits]
    | ptr p => simp only [Val.retypeL, Val.widen, Val.retype, addr_word_zero, addr_ptr_zero]
    | bool b => cases b <;> simp [Val.retypeL, Val.widen, Val.retype, Arm64.addr, Arm64.reg]
    | _ => simp [Val.retypeL, Val.widen, Val.retype, Arm64.addr, Arm64.reg]
  | agg fs n =>
    left
    cases v with
    | agg vs =>
      simp only [Val.retypeL, Val.widen, Val.retype]
      cases Val.retypeFields fs vs <;> rfl
    | _ => simp [Val.retypeL, Val.widen, Val.retype, Arm64.addr, Arm64.reg]
  | _ => simp [argWidth] at hT

/-- The address of `ADD x d`: undefined, or `x`'s at offset `d`. -/
theorem addr_add_imm (x : Val) (d : BitVec 64) :
    Arm64.addr (Arm64.add .other [x, .int .w64 d]) 0 = none ∨
      Arm64.addr (Arm64.add .other [x, .int .w64 d]) 0 = Arm64.addr x d := by
  cases x with
  | ptr p =>
    simp only [Arm64.add, Arm64.reg, BitVec.setWidth_eq, PtrOps.ptrRes]
    split
    · right; rw [addr_word_zero]; rfl
    · left; rfl
  | _ => right; simp [Arm64.add, Arm64.op2, Arm64.reg, Arm64.res, Arm64.addr]

/-- A left shift by `k < 64` is a multiplication by `2^k`. -/
theorem shl_mul (x : BitVec 64) (k : Nat) (hk : k < 64) :
    x <<< k = x * BitVec.ofNat 64 (2 ^ k) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hk)]

/-- `ADD y y` is the register of `y` doubled. -/
theorem add_self_reg (T : Ty) (y : Val) :
    Arm64.add T [y, y] = match Arm64.reg y with
      | some r => Arm64.res T (r * BitVec.ofNat 64 2)
      | none => .poison := by
  have h2 : ∀ r : BitVec 64, r + r = r * BitVec.ofNat 64 2 := fun r => by
    rw [show BitVec.ofNat 64 2 = BitVec.ofNat 64 (2 ^ 1) from rfl, ← shl_mul r 1 (by decide)]
    bv_omega
  cases y with
  | ptr p =>
    simp only [Arm64.add, Arm64.op2]
    cases Arm64.reg (.ptr p) <;> simp [h2]
  | _ => simp [Arm64.add, Arm64.op2, Arm64.reg, h2]

/-- An unscaled indexed load at a `poison` index is `poison`. -/
theorem loadIdx1_poison_right (T : Ty) (n : Nat) (s : Bool) (x m : Val) :
    Arm64.loadIdx T n 1 s [x, .poison, m] = .poison := by
  cases m <;> simp [Arm64.loadIdx, add_poison_right, Arm64.addr, Arm64.reg]

/-- An unscaled indexed load at a `poison` base is `poison`. -/
theorem loadIdx1_poison_left (T : Ty) (n : Nat) (s : Bool) (x m : Val) :
    Arm64.loadIdx T n 1 s [.poison, x, m] = .poison := by
  cases m <;> simp [Arm64.loadIdx, add_poison_left, Arm64.addr, Arm64.reg]

/-- A scaled indexed load is the unscaled one at the scaled index register. -/
theorem loadIdx_scaled {sc : Nat} (hsc : sc ≠ 1) (T : Ty) (n : Nat) (s : Bool) (x y : Val)
    (m : Mem) :
    Arm64.loadIdx T n sc s [x, y, .mem m] = match Arm64.reg y with
      | some r => Arm64.loadIdx T n 1 s [x, .int .w64 (r * BitVec.ofNat 64 sc), .mem m]
      | none => .poison := by
  simp only [Arm64.loadIdx, hsc, ↓reduceIte]
  cases Arm64.reg y <;> rfl

/-- `ADDshiftLL [k] x y` at a shape other than boolean is `ADD` of `x` and `y · 2^k`. -/
theorem addSh_ll {T : Ty} (h : T ≠ .bool) {j : Int64} {k : Nat} (hj : Arm64.amt j = k)
    (hk : k < 64) (x y : Val) :
    Arm64.addSh T .ll j [x, y] = match Arm64.reg y with
      | some r => Arm64.add .other [x, .int .w64 (r * BitVec.ofNat 64 (2 ^ k))]
      | none => .poison := by
  simp only [Arm64.addSh]
  cases Arm64.reg y with
  | none => rfl
  | some r =>
    simp only [Arm64.shifted, Arm64.Shift.apply, hj, Nat.mod_eq_of_lt hk, shl_mul r k hk,
      addP_other h]

/-- Two loads at related addresses (the source's undefined, or the same). -/
theorem refines_loadAt {a b : Option Ptr} (h : a = none ∨ a = b) (T : Ty) (n : Nat) (s : Bool)
    (m : Mem) :
    Sem.Refines ((a.elim .poison (Arm64.loadN T n s m)).retypeL T)
      ((b.elim .poison (Arm64.loadN T n s m)).retypeL T) := by
  rcases h with rfl | rfl
  · simp only [Option.elim, retypeL_poison]; exact .poison _
  · exact Sem.Refines.refl _

/-- An unscaled indexed load: the load at the address of `ADD` of its arguments. -/
theorem loadIdx1_elim (T : Ty) (n : Nat) (s : Bool) (x y : Val) (m : Mem) :
    Arm64.loadIdx T n 1 s [x, y, .mem m] =
      (Arm64.addr (Arm64.add .other [x, y]) 0).elim .poison (Arm64.loadN T n s m) := by
  simp only [Arm64.loadIdx, ↓reduceIte]
  cases Arm64.addr (Arm64.add .other [x, y]) 0 <;> rfl

/-- An integer load without aux: the load at the base's address moved by the offset. -/
theorem ldVal_none (tabs : Tables) (n : Nat) (s : Bool) (T : Ty) (k : Int64) (x : Val) (m : Mem) :
    ldVal tabs n s T k none [x, .mem m] =
      (Arm64.addr x (BitVec.ofInt 64 k.toInt)).elim .poison (Arm64.loadN T n s m) := rfl

/-- **An `ADD` address folded into an indexed load** (`ARM64.rules:695-701`). -/
theorem refines_ldIdx_add {o : Op} {n : Nat} {s : Bool} (hl : ldOp? o = some (n, s))
    (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false) (tabs : Tables) {T T1 : Ty}
    {k : Int64} (hk : k.toInt = 0) (hT1 : 64 ≤ argWidth T1) (x y m : Val) :
    Sem.Refines
      ((opValL tabs o T k none [(Arm64.add T1 [x, y]).retypeL T1, m]).retypeL T)
      ((Arm64.loadIdx T n 1 s [x, y, m]).retypeL T) := by
  rw [opValL_ld hg hm hl, add_other (ne_bool_of_wide hT1)]
  cases m with
  | mem mm =>
    rw [ldVal_none, loadIdx1_elim, hk, show BitVec.ofInt 64 0 = 0 from rfl]
    exact refines_loadAt (addr_retypeL_zero _ hT1) T n s mm
  | _ => simp only [ldVal, Arm64.loadIdx, retypeL_poison]; exact .poison _

/-- **A shifted `ADD` address folded into a scaled indexed load** (`ARM64.rules:725-729`). -/
theorem refines_ldIdx_shift {o : Op} {n : Nat} {s : Bool} (hl : ldOp? o = some (n, s))
    (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false) (tabs : Tables) {T T1 : Ty}
    {k j : Int64} {sh sc : Nat} (hk : k.toInt = 0) (hj : Arm64.amt j = sh) (hsh : sh < 64)
    (hsc : 2 ^ sh = sc) (hsc1 : sc ≠ 1) (hT1 : 64 ≤ argWidth T1) (x y m : Val) :
    Sem.Refines
      ((opValL tabs o T k none [(Arm64.addSh T1 .ll j [x, y]).retypeL T1, m]).retypeL T)
      ((Arm64.loadIdx T n sc s [x, y, m]).retypeL T) := by
  subst hsc
  rw [opValL_ld hg hm hl, addSh_ll (ne_bool_of_wide hT1) hj hsh]
  cases m with
  | mem mm =>
    rw [ldVal_none, loadIdx_scaled hsc1, hk, show BitVec.ofInt 64 0 = 0 from rfl]
    cases Arm64.reg y with
    | none => simp only [retypeL_poison, Arm64.addr, Arm64.reg, Option.map_none, Option.elim]; exact .poison _
    | some r =>
      dsimp only
      rw [loadIdx1_elim]
      exact refines_loadAt (addr_retypeL_zero _ hT1) T n s mm
  | _ => simp only [ldVal, Arm64.loadIdx, retypeL_poison]; exact .poison _

/-- An index read at a shape with a whole register: `d`, or `poison`. -/
theorem refines_ldIdx_idx {T : Ty} {n : Nat} {s : Bool} {x z : Val} {d : BitVec 64}
    (hz : z = .int .w64 d ∨ z = .poison) (m : Val) :
    Sem.Refines ((Arm64.loadIdx T n 1 s [x, z, m]).retypeL T)
      ((Arm64.loadIdx T n 1 s [x, .int .w64 d, m]).retypeL T) := by
  rcases hz with rfl | rfl
  · exact Sem.Refines.refl _
  · rw [loadIdx1_poison_right, retypeL_poison]; exact .poison _

/-- `refines_ldIdx_idx` with the index first (`ADD` takes either as the base). -/
theorem refines_ldIdx_idx' {T : Ty} {n : Nat} {s : Bool} {x z : Val} {d : BitVec 64}
    (hz : z = .int .w64 d ∨ z = .poison) (m : Val) :
    Sem.Refines ((Arm64.loadIdx T n 1 s [z, x, m]).retypeL T)
      ((Arm64.loadIdx T n 1 s [x, .int .w64 d, m]).retypeL T) := by
  rcases hz with rfl | rfl
  · cases m <;> simp only [Arm64.loadIdx, ↓reduceIte, add_int_comm] <;> exact Sem.Refines.refl _
  · rw [loadIdx1_poison_left, retypeL_poison]; exact .poison _

/-- **A shifted index folded into a scaled indexed load** (`ARM64.rules:730-734`, `737-739`,
`750-753`). -/
theorem refines_ldIdx_sll {T T1 : Ty} {n : Nat} {s : Bool} {j : Int64} {sh sc : Nat}
    (hj : Arm64.amt j = sh) (hsh : sh < 64) (hsc : 2 ^ sh = sc) (hsc1 : sc ≠ 1)
    (hT1 : 64 ≤ argWidth T1) (x y m : Val) (sw : Bool) :
    Sem.Refines
      ((Arm64.loadIdx T n 1 s
        (if sw then [(Arm64.op1 T1 (fun v => Arm64.Shift.ll.apply v (Arm64.amt j)) [y]).retypeL T1, x, m]
          else [x, (Arm64.op1 T1 (fun v => Arm64.Shift.ll.apply v (Arm64.amt j)) [y]).retypeL T1, m])).retypeL T)
      ((Arm64.loadIdx T n sc s [x, y, m]).retypeL T) := by
  subst hsc
  cases m with
  | mem mm =>
    rw [loadIdx_scaled hsc1]
    cases hr : Arm64.reg y with
    | none =>
      cases sw <;> simp only [Arm64.op1, hr, retypeL_poison, loadIdx1_poison_left,
        loadIdx1_poison_right, Bool.false_eq_true, ↓reduceIte] <;> exact .poison _
    | some r =>
      have hz := retypeL_res_wide hT1 (Arm64.Shift.ll.apply r (Arm64.amt j))
      simp only [Arm64.Shift.apply, hj, Nat.mod_eq_of_lt hsh, shl_mul r sh hsh] at hz
      cases sw <;> simp only [Arm64.op1, hr, Arm64.Shift.apply, hj, Nat.mod_eq_of_lt hsh,
        shl_mul r sh hsh, Bool.false_eq_true, ↓reduceIte]
      · exact refines_ldIdx_idx hz _
      · exact refines_ldIdx_idx' hz _
  | _ => cases sw <;> simp only [Arm64.loadIdx, retypeL_poison, Bool.false_eq_true, ↓reduceIte] <;>
    exact .poison _

/-- **A doubled index folded into a scaled indexed load** (`ARM64.rules:735-736`, `740-741`). -/
theorem refines_ldIdx_dbl {T T1 : Ty} {n : Nat} {s : Bool} (hT1 : 64 ≤ argWidth T1)
    (x y m : Val) (sw : Bool) :
    Sem.Refines
      ((Arm64.loadIdx T n 1 s
        (if sw then [(Arm64.add T1 [y, y]).retypeL T1, x, m]
          else [x, (Arm64.add T1 [y, y]).retypeL T1, m])).retypeL T)
      ((Arm64.loadIdx T n 2 s [x, y, m]).retypeL T) := by
  rw [add_self_reg]
  cases m with
  | mem mm =>
    rw [loadIdx_scaled (by decide)]
    cases Arm64.reg y with
    | none =>
      cases sw <;> simp only [retypeL_poison, loadIdx1_poison_left,
        loadIdx1_poison_right, Bool.false_eq_true, ↓reduceIte] <;> exact .poison _
    | some r =>
      have hz := retypeL_res_wide hT1 (r * BitVec.ofNat 64 2)
      cases sw <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact refines_ldIdx_idx hz _
      · exact refines_ldIdx_idx' hz _
  | _ => cases sw <;> simp only [Arm64.loadIdx, retypeL_poison, Bool.false_eq_true, ↓reduceIte] <;>
    exact .poison _

/-- **A constant index folded into a load's offset** (`ARM64.rules:705-718`). -/
theorem refines_ldIdx_const {o : Op} {n : Nat} {s : Bool} (hl : ldOp? o = some (n, s))
    (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false) (tabs : Tables) {T T1 : Ty}
    (hT1 : 64 ≤ argWidth T1) (c : Int64) (x m : Val) (sw : Bool) :
    Sem.Refines
      ((Arm64.loadIdx T n 1 s
        (if sw then [(Arm64.res T1 (BitVec.ofInt 64 c.toInt)).retypeL T1, x, m]
          else [x, (Arm64.res T1 (BitVec.ofInt 64 c.toInt)).retypeL T1, m])).retypeL T)
      ((opValL tabs o T c none [x, m]).retypeL T) := by
  rw [opValL_ld hg hm hl]
  have hz := retypeL_res_wide hT1 (BitVec.ofInt 64 c.toInt)
  refine Sem.Refines.trans (b := (Arm64.loadIdx T n 1 s
    [x, .int .w64 (BitVec.ofInt 64 c.toInt), m]).retypeL T) ?_ ?_
  · cases sw <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact refines_ldIdx_idx hz _
    · exact refines_ldIdx_idx' hz _
  cases m with
  | mem mm =>
    rw [ldVal_none, loadIdx1_elim]
    exact refines_loadAt (addr_add_imm _ _) T n s mm
  | _ => simp only [ldVal, Arm64.loadIdx, retypeL_poison]; exact .poison _

/-- **A constant scaled index folded into a load's offset** (`ARM64.rules:742-746`). -/
theorem refines_ldIdx_constSc {o : Op} {n : Nat} {s : Bool} (hl : ldOp? o = some (n, s))
    (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false) (tabs : Tables) {T T1 : Ty}
    (hT1 : 64 ≤ argWidth T1) {sc : Nat} (hsc1 : sc ≠ 1) (c k : Int64)
    (hk : BitVec.ofInt 64 k.toInt = BitVec.ofInt 64 c.toInt * BitVec.ofNat 64 sc) (x m : Val) :
    Sem.Refines
      ((Arm64.loadIdx T n sc s [x, (Arm64.res T1 (BitVec.ofInt 64 c.toInt)).retypeL T1, m]).retypeL T)
      ((opValL tabs o T k none [x, m]).retypeL T) := by
  rw [opValL_ld hg hm hl]
  cases m with
  | mem mm =>
    rw [ldVal_none, loadIdx_scaled hsc1, hk]
    rcases retypeL_res_wide hT1 (BitVec.ofInt 64 c.toInt) with h | h <;> rw [h]
    · simp only [Arm64.reg, BitVec.setWidth_eq]
      rw [loadIdx1_elim]
      exact refines_loadAt (addr_add_imm _ _) T n s mm
    · simp only [Arm64.reg, retypeL_poison]; exact .poison _
  | _ => simp only [ldVal, Arm64.loadIdx, retypeL_poison]; exact .poison _

/-- `int32(c)<<k` of a `c` whose `c<<k` is a 32-bit integer (`is32Bit(c<<k)`) is `c·2^k`. -/
theorem imm_shl {c sc : Int} (hsc : sc = 2 ∨ sc = 4 ∨ sc = 8)
    (h : wrapInt 64 true (c * sc) = wrapInt 32 true (wrapInt 64 true (c * sc))) :
    BitVec.ofInt 64 (Int64.ofInt (wrapInt 32 true (wrapInt 32 true c * sc))).toInt =
      BitVec.ofInt 64 c * BitVec.ofInt 64 sc := by
  rw [ofInt_int64_ofInt (by decide)]
  have he : wrapInt 32 true (wrapInt 32 true c * sc) = wrapInt 64 true (c * sc) := by
    rw [wrapInt32_omega, wrapInt64_omega] at h
    rw [wrapInt32_omega, wrapInt32_omega, wrapInt64_omega]
    rcases hsc with rfl | rfl | rfl <;> omega
  rw [he, wrapInt_true, ofInt_bmod_of_le (Nat.le_refl _), BitVec.ofInt_mul]

set_option hygiene false in
/-- The obligation of `(MOV…load [off] {sym} (ADD ptr idx) mem) && off == 0 && sym == nil =>
(MOV…loadidx ptr idx mem)` (`refines_ldIdx_add`). -/
macro "arm_ldidx_add" : tactic => `(tactic| (
  left
  arm_unfold
  all_goals (
    simp only [Pat.addrOKL, Pat.addrOKLs, Bool.and_eq_true, Bool.or_eq_true] at hadr
    arm_norm
    obtain ⟨⟨hA | ⟨⟨hax, hk1⟩, -⟩, -⟩, -⟩ := hadr
    · exact absurd hA (by decide)
    rw [show e.aux [] = none from beq_iff_eq.1 hax]
    have hk : (e.auxInt []).toInt = 0 := by
      have h0 := (offOK_toNat hk1).2
      have h1 := hcond.1
      rw [wrapInt32_omega] at h1
      omega
    exact refines_ldIdx_add rfl rfl rfl _ hk (by simpa [armReadW] using harg.1.1) _ _ _)))

set_option hygiene false in
/-- The obligation of `(MOV…load [off] {sym} (ADDshiftLL [sh] ptr idx) mem) && off == 0 &&
sym == nil => (MOV…loadidx{2,4,8} ptr idx mem)` (`refines_ldIdx_shift`). -/
macro "arm_ldidx_shift" sh:term : tactic => `(tactic| (
  left
  arm_unfold
  all_goals (
    simp only [Pat.addrOKL, Pat.addrOKLs, Bool.and_eq_true, Bool.or_eq_true] at hadr
    arm_norm
    obtain ⟨⟨hA | ⟨⟨hax, hk1⟩, -⟩, -⟩, -⟩ := hadr
    · exact absurd hA (by decide)
    rw [show e.aux [] = none from beq_iff_eq.1 hax]
    have hk : (e.auxInt []).toInt = 0 := by
      have h0 := (offOK_toNat hk1).2
      have h1 := hcond.1
      rw [wrapInt32_omega] at h1
      omega
    simp only [DV.int.injEq] at hc
    exact refines_ldIdx_shift (sh := $sh) rfl rfl rfl _ hk (by simp [Arm64.amt, hc]) (by decide)
      (by decide) (by decide) (by simpa [armReadW] using harg.1.1) _ _ _)))

set_option hygiene false in
/-- The obligation of `(MOV…loadidx ptr (SLLconst [sh] idx) mem) => (MOV…loadidx{2,4,8} ptr idx
mem)` and its swapped form (`refines_ldIdx_sll`; `hT` the shape premise of the index). -/
macro "arm_ldidx_sll" sh:term "," sw:term "," hT:term : tactic => `(tactic| (
  left
  arm_unfold
  all_goals (
    arm_norm
    simp only [DV.int.injEq] at hc
    exact refines_ldIdx_sll (sh := $sh) (by simp [Arm64.amt, hc]) (by decide) (by decide)
      (by decide) (by simpa [armReadW] using $hT) _ _ _ $sw)))

set_option hygiene false in
/-- The obligation of `(MOVH…loadidx ptr (ADD idx idx) mem) => (MOVH…loadidx2 ptr idx mem)` and
its swapped form (`refines_ldIdx_dbl`). -/
macro "arm_ldidx_dbl" sw:term "," hT:term : tactic => `(tactic| (
  left
  arm_unfold
  all_goals (
    arm_norm
    rw [hc]
    exact refines_ldIdx_dbl (by simpa [armReadW] using $hT) _ _ _ $sw)))

set_option hygiene false in
/-- The obligation of `(MOV…loadidx ptr (MOVDconst [c]) mem) && is32Bit(c) => (MOV…load
[int32(c)] ptr mem)` and its swapped form (`refines_ldIdx_const`). -/
macro "arm_ldidx_const" sw:term "," hT:term : tactic => `(tactic| (
  left
  arm_unfold
  all_goals (
    arm_norm
    rw [← hcond, Int64.ofInt_toInt]
    exact refines_ldIdx_const rfl rfl rfl _ (by simpa [armReadW] using $hT) _ _ _ $sw)))

set_option hygiene false in
/-- The obligation of `(MOV…loadidx{2,4,8} ptr (MOVDconst [c]) mem) && is32Bit(c<<k) => (MOV…load
[int32(c)<<k] ptr mem)` (`refines_ldIdx_constSc`, `imm_shl`). -/
macro "arm_ldidx_constSc" : tactic => `(tactic| (
  left
  arm_unfold
  all_goals (
    arm_norm
    simp [callH, goShl] at hcond
    simp (config := { decide := true }) only [goShl, ite_false, ↓reduceIte]
    exact refines_ldIdx_constSc rfl rfl rfl _ (by simpa [armReadW] using harg.2.1) (by decide) _ _
      (by simp only [Int.reduceToNat, Int.reducePow]; rw [imm_shl (by decide) hcond]; rfl) _ _)))

/-- `ARM64.rules:695`: `(MOVDload [off] {sym} (ADD ptr idx) mem) && off == 0 && sym == nil => (MOVDloadidx ptr idx mem)` -/
theorem r_ARM64_695_sound : ArmRule.Checked r_ARM64_695 := by
  arm_ldidx_add

/-- `ARM64.rules:696`: `(MOVWUload [off] {sym} (ADD ptr idx) mem) && off == 0 && sym == nil => (MOVWUloadidx ptr idx mem)` -/
theorem r_ARM64_696_sound : ArmRule.Checked r_ARM64_696 := by
  arm_ldidx_add

/-- `ARM64.rules:697`: `(MOVWload [off] {sym} (ADD ptr idx) mem) && off == 0 && sym == nil => (MOVWloadidx ptr idx mem)` -/
theorem r_ARM64_697_sound : ArmRule.Checked r_ARM64_697 := by
  arm_ldidx_add

/-- `ARM64.rules:698`: `(MOVHUload [off] {sym} (ADD ptr idx) mem) && off == 0 && sym == nil => (MOVHUloadidx ptr idx mem)` -/
theorem r_ARM64_698_sound : ArmRule.Checked r_ARM64_698 := by
  arm_ldidx_add

/-- `ARM64.rules:699`: `(MOVHload [off] {sym} (ADD ptr idx) mem) && off == 0 && sym == nil => (MOVHloadidx ptr idx mem)` -/
theorem r_ARM64_699_sound : ArmRule.Checked r_ARM64_699 := by
  arm_ldidx_add

/-- `ARM64.rules:700`: `(MOVBUload [off] {sym} (ADD ptr idx) mem) && off == 0 && sym == nil => (MOVBUloadidx ptr idx mem)` -/
theorem r_ARM64_700_sound : ArmRule.Checked r_ARM64_700 := by
  arm_ldidx_add

/-- `ARM64.rules:701`: `(MOVBload [off] {sym} (ADD ptr idx) mem) && off == 0 && sym == nil => (MOVBloadidx ptr idx mem)` -/
theorem r_ARM64_701_sound : ArmRule.Checked r_ARM64_701 := by
  arm_ldidx_add

/-- `ARM64.rules:705`: `(MOVDloadidx ptr (MOVDconst [c]) mem) && is32Bit(c) => (MOVDload [int32(c)] ptr mem)` -/
theorem r_ARM64_705_sound : ArmRule.Checked r_ARM64_705 := by
  arm_ldidx_const false, harg.2.1

/-- `ARM64.rules:706`: `(MOVDloadidx (MOVDconst [c]) ptr mem) && is32Bit(c) => (MOVDload [int32(c)] ptr mem)` -/
theorem r_ARM64_706_sound : ArmRule.Checked r_ARM64_706 := by
  arm_ldidx_const true, harg.1

/-- `ARM64.rules:707`: `(MOVWUloadidx ptr (MOVDconst [c]) mem) && is32Bit(c) => (MOVWUload [int32(c)] ptr mem)` -/
theorem r_ARM64_707_sound : ArmRule.Checked r_ARM64_707 := by
  arm_ldidx_const false, harg.2.1

/-- `ARM64.rules:708`: `(MOVWUloadidx (MOVDconst [c]) ptr mem) && is32Bit(c) => (MOVWUload [int32(c)] ptr mem)` -/
theorem r_ARM64_708_sound : ArmRule.Checked r_ARM64_708 := by
  arm_ldidx_const true, harg.1

/-- `ARM64.rules:709`: `(MOVWloadidx ptr (MOVDconst [c]) mem) && is32Bit(c) => (MOVWload [int32(c)] ptr mem)` -/
theorem r_ARM64_709_sound : ArmRule.Checked r_ARM64_709 := by
  arm_ldidx_const false, harg.2.1

/-- `ARM64.rules:710`: `(MOVWloadidx (MOVDconst [c]) ptr mem) && is32Bit(c) => (MOVWload [int32(c)] ptr mem)` -/
theorem r_ARM64_710_sound : ArmRule.Checked r_ARM64_710 := by
  arm_ldidx_const true, harg.1

/-- `ARM64.rules:711`: `(MOVHUloadidx ptr (MOVDconst [c]) mem) && is32Bit(c) => (MOVHUload [int32(c)] ptr mem)` -/
theorem r_ARM64_711_sound : ArmRule.Checked r_ARM64_711 := by
  arm_ldidx_const false, harg.2.1

/-- `ARM64.rules:712`: `(MOVHUloadidx (MOVDconst [c]) ptr mem) && is32Bit(c) => (MOVHUload [int32(c)] ptr mem)` -/
theorem r_ARM64_712_sound : ArmRule.Checked r_ARM64_712 := by
  arm_ldidx_const true, harg.1

/-- `ARM64.rules:713`: `(MOVHloadidx ptr (MOVDconst [c]) mem) && is32Bit(c) => (MOVHload [int32(c)] ptr mem)` -/
theorem r_ARM64_713_sound : ArmRule.Checked r_ARM64_713 := by
  arm_ldidx_const false, harg.2.1

/-- `ARM64.rules:714`: `(MOVHloadidx (MOVDconst [c]) ptr mem) && is32Bit(c) => (MOVHload [int32(c)] ptr mem)` -/
theorem r_ARM64_714_sound : ArmRule.Checked r_ARM64_714 := by
  arm_ldidx_const true, harg.1

/-- `ARM64.rules:715`: `(MOVBUloadidx ptr (MOVDconst [c]) mem) && is32Bit(c) => (MOVBUload [int32(c)] ptr mem)` -/
theorem r_ARM64_715_sound : ArmRule.Checked r_ARM64_715 := by
  arm_ldidx_const false, harg.2.1

/-- `ARM64.rules:716`: `(MOVBUloadidx (MOVDconst [c]) ptr mem) && is32Bit(c) => (MOVBUload [int32(c)] ptr mem)` -/
theorem r_ARM64_716_sound : ArmRule.Checked r_ARM64_716 := by
  arm_ldidx_const true, harg.1

/-- `ARM64.rules:717`: `(MOVBloadidx ptr (MOVDconst [c]) mem) && is32Bit(c) => (MOVBload [int32(c)] ptr mem)` -/
theorem r_ARM64_717_sound : ArmRule.Checked r_ARM64_717 := by
  arm_ldidx_const false, harg.2.1

/-- `ARM64.rules:718`: `(MOVBloadidx (MOVDconst [c]) ptr mem) && is32Bit(c) => (MOVBload [int32(c)] ptr mem)` -/
theorem r_ARM64_718_sound : ArmRule.Checked r_ARM64_718 := by
  arm_ldidx_const true, harg.1

/-- `ARM64.rules:725`: `(MOVDload [off] {sym} (ADDshiftLL [3] ptr idx) mem) && off == 0 && sym == nil => (MOVDloadidx8 ptr idx mem)` -/
theorem r_ARM64_725_sound : ArmRule.Checked r_ARM64_725 := by
  arm_ldidx_shift 3

/-- `ARM64.rules:726`: `(MOVWUload [off] {sym} (ADDshiftLL [2] ptr idx) mem) && off == 0 && sym == nil => (MOVWUloadidx4 ptr idx mem)` -/
theorem r_ARM64_726_sound : ArmRule.Checked r_ARM64_726 := by
  arm_ldidx_shift 2

/-- `ARM64.rules:727`: `(MOVWload [off] {sym} (ADDshiftLL [2] ptr idx) mem) && off == 0 && sym == nil => (MOVWloadidx4 ptr idx mem)` -/
theorem r_ARM64_727_sound : ArmRule.Checked r_ARM64_727 := by
  arm_ldidx_shift 2

/-- `ARM64.rules:728`: `(MOVHUload [off] {sym} (ADDshiftLL [1] ptr idx) mem) && off == 0 && sym == nil => (MOVHUloadidx2 ptr idx mem)` -/
theorem r_ARM64_728_sound : ArmRule.Checked r_ARM64_728 := by
  arm_ldidx_shift 1

/-- `ARM64.rules:729`: `(MOVHload [off] {sym} (ADDshiftLL [1] ptr idx) mem) && off == 0 && sym == nil => (MOVHloadidx2 ptr idx mem)` -/
theorem r_ARM64_729_sound : ArmRule.Checked r_ARM64_729 := by
  arm_ldidx_shift 1

/-- `ARM64.rules:730`: `(MOVDloadidx ptr (SLLconst [3] idx) mem) => (MOVDloadidx8 ptr idx mem)` -/
theorem r_ARM64_730_sound : ArmRule.Checked r_ARM64_730 := by
  arm_ldidx_sll 3, false, harg.2.1.1

/-- `ARM64.rules:731`: `(MOVWloadidx ptr (SLLconst [2] idx) mem) => (MOVWloadidx4 ptr idx mem)` -/
theorem r_ARM64_731_sound : ArmRule.Checked r_ARM64_731 := by
  arm_ldidx_sll 2, false, harg.2.1.1

/-- `ARM64.rules:732`: `(MOVWUloadidx ptr (SLLconst [2] idx) mem) => (MOVWUloadidx4 ptr idx mem)` -/
theorem r_ARM64_732_sound : ArmRule.Checked r_ARM64_732 := by
  arm_ldidx_sll 2, false, harg.2.1.1

/-- `ARM64.rules:733`: `(MOVHloadidx ptr (SLLconst [1] idx) mem) => (MOVHloadidx2 ptr idx mem)` -/
theorem r_ARM64_733_sound : ArmRule.Checked r_ARM64_733 := by
  arm_ldidx_sll 1, false, harg.2.1.1

/-- `ARM64.rules:734`: `(MOVHUloadidx ptr (SLLconst [1] idx) mem) => (MOVHUloadidx2 ptr idx mem)` -/
theorem r_ARM64_734_sound : ArmRule.Checked r_ARM64_734 := by
  arm_ldidx_sll 1, false, harg.2.1.1

/-- `ARM64.rules:735`: `(MOVHloadidx ptr (ADD idx idx) mem) => (MOVHloadidx2 ptr idx mem)` -/
theorem r_ARM64_735_sound : ArmRule.Checked r_ARM64_735 := by
  arm_ldidx_dbl false, harg.2.1.1

/-- `ARM64.rules:736`: `(MOVHUloadidx ptr (ADD idx idx) mem) => (MOVHUloadidx2 ptr idx mem)` -/
theorem r_ARM64_736_sound : ArmRule.Checked r_ARM64_736 := by
  arm_ldidx_dbl false, harg.2.1.1

/-- `ARM64.rules:737`: `(MOVDloadidx (SLLconst [3] idx) ptr mem) => (MOVDloadidx8 ptr idx mem)` -/
theorem r_ARM64_737_sound : ArmRule.Checked r_ARM64_737 := by
  arm_ldidx_sll 3, true, harg.1.1

/-- `ARM64.rules:738`: `(MOVWloadidx (SLLconst [2] idx) ptr mem) => (MOVWloadidx4 ptr idx mem)` -/
theorem r_ARM64_738_sound : ArmRule.Checked r_ARM64_738 := by
  arm_ldidx_sll 2, true, harg.1.1

/-- `ARM64.rules:739`: `(MOVWUloadidx (SLLconst [2] idx) ptr mem) => (MOVWUloadidx4 ptr idx mem)` -/
theorem r_ARM64_739_sound : ArmRule.Checked r_ARM64_739 := by
  arm_ldidx_sll 2, true, harg.1.1

/-- `ARM64.rules:740`: `(MOVHloadidx (ADD idx idx) ptr mem) => (MOVHloadidx2 ptr idx mem)` -/
theorem r_ARM64_740_sound : ArmRule.Checked r_ARM64_740 := by
  arm_ldidx_dbl true, harg.1.1

/-- `ARM64.rules:741`: `(MOVHUloadidx (ADD idx idx) ptr mem) => (MOVHUloadidx2 ptr idx mem)` -/
theorem r_ARM64_741_sound : ArmRule.Checked r_ARM64_741 := by
  arm_ldidx_dbl true, harg.1.1

/-- `ARM64.rules:742`: `(MOVDloadidx8 ptr (MOVDconst [c]) mem) && is32Bit(c<<3) => (MOVDload [int32(c)<<3] ptr mem)` -/
theorem r_ARM64_742_sound : ArmRule.Checked r_ARM64_742 := by
  arm_ldidx_constSc

/-- `ARM64.rules:743`: `(MOVWUloadidx4 ptr (MOVDconst [c]) mem) && is32Bit(c<<2) => (MOVWUload [int32(c)<<2] ptr mem)` -/
theorem r_ARM64_743_sound : ArmRule.Checked r_ARM64_743 := by
  arm_ldidx_constSc

/-- `ARM64.rules:744`: `(MOVWloadidx4 ptr (MOVDconst [c]) mem) && is32Bit(c<<2) => (MOVWload [int32(c)<<2] ptr mem)` -/
theorem r_ARM64_744_sound : ArmRule.Checked r_ARM64_744 := by
  arm_ldidx_constSc

/-- `ARM64.rules:745`: `(MOVHUloadidx2 ptr (MOVDconst [c]) mem) && is32Bit(c<<1) => (MOVHUload [int32(c)<<1] ptr mem)` -/
theorem r_ARM64_745_sound : ArmRule.Checked r_ARM64_745 := by
  arm_ldidx_constSc

/-- `ARM64.rules:746`: `(MOVHloadidx2 ptr (MOVDconst [c]) mem) && is32Bit(c<<1) => (MOVHload [int32(c)<<1] ptr mem)` -/
theorem r_ARM64_746_sound : ArmRule.Checked r_ARM64_746 := by
  arm_ldidx_constSc

/-- `ARM64.rules:750`: `(FMOVDloadidx ptr (SLLconst [3] idx) mem) => (FMOVDloadidx8 ptr idx mem)` -/
theorem r_ARM64_750_sound : ArmRule.Checked r_ARM64_750 := by
  arm_ldidx_sll 3, false, harg.2.1.1

/-- `ARM64.rules:751`: `(FMOVSloadidx ptr (SLLconst [2] idx) mem) => (FMOVSloadidx4 ptr idx mem)` -/
theorem r_ARM64_751_sound : ArmRule.Checked r_ARM64_751 := by
  arm_ldidx_sll 2, false, harg.2.1.1

/-- `ARM64.rules:752`: `(FMOVDloadidx (SLLconst [3] idx) ptr mem) => (FMOVDloadidx8 ptr idx mem)` -/
theorem r_ARM64_752_sound : ArmRule.Checked r_ARM64_752 := by
  arm_ldidx_sll 3, true, harg.1.1

/-- `ARM64.rules:753`: `(FMOVSloadidx (SLLconst [2] idx) ptr mem) => (FMOVSloadidx4 ptr idx mem)` -/
theorem r_ARM64_753_sound : ArmRule.Checked r_ARM64_753 := by
  arm_ldidx_sll 2, true, harg.1.1

end GoFV.Proof.Low.Rules
