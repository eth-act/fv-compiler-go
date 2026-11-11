import GoFV.Proof.Gen.G50
import GoFV.Proof.Gen.Spec51c

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G51 group c of the genssa validator: boolean operands of arithmetic and shifted logic
(`docs/plans/proofs3.md` §4)

`vkind51c` (`GoFV/Gen/Check51c.lean`) accepts G1's `ADD`, `SUB`, `ADDconst`, `SUBconst`, G16's
`ADDshiftLL`, G36's shifted adds and subtracts and G27's shifted logic ops with a boolean (class 1)
argument, emitting the Prog the existing slices emit. The existing value lemmas (`lo_add`,
`lo_sub`, `lo_addK`, `lo_addP`, `lo_addSh`, `lo_shOp36`, `lo_logSh`) use only the low `c` bits of
an argument of class at least the result's class `c`. A boolean's register is its machine word on
all 64 bits (`reg_bool51c`: `ValRel` of `.bool b` is `X = if b then 1 else 0`, and so is
`Arm64.reg`), so `reg_info51c` gives an argument of class at least `c` or 1 what `reg_info` gives
one of class at least `c`, and a right shift's operand of class 64 or 1 is its machine word
(`reg_full51c`). The value lemmas follow with `c ≤ ca ∨ ca = 1` (`lo_addP51c`, `lo_add51c`,
`lo_sub51c`, `lo_addK51c`, `lo_addSh51c`, `lo_shOp51c`, `lo_logSh51c`); a subtraction with a boolean
operand has at most one pointer operand, so it needs no `SubOK`.

The machine steps are the existing ones (`progStep_aluReg`, `progStep_aluConst`,
`progStep_addShiftLL`, `progStep_shOp36`, `progStep_logSh`), each writing the X register of the
value's home (`XW`). `ADD`, `SUB`, `ADDconst`, `SUBconst`, `ADDshiftLL` are kept ops of G35's
upper-bit table (`uStep35_keep51c`): the entries of the other registers stay true (`uokl_keep`), so
`vk51c_step` takes the table's `UOKL m L` before the value. After a shifted add or subtract the
table is empty (`uStep35_alu36`); a shifted logic op keeps the entries of the other registers
(`logSh_keep35`, `uokl_keepOps`; slice G59 group U).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem fits_le51c {c : Nat} {x : Val} {r : BitVec 64} (hf : Fits c x)
    (hr : Arm64.reg x = some r) : c ≤ 64 := by
  cases x with
  | int w v => have : w.bits = c := hf; subst this; cases w <;> decide
  | bool b => have : c = 1 := hf; omega
  | ptr p => have : c = 64 := hf; omega
  | _ => cases hr

private theorem low_le51c {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem res_int51c {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

private theorem ptr_or51c (x : Val) : (∃ p, x = .ptr p) ∨ ∀ p, x ≠ .ptr p := by
  cases x <;> simp

private theorem sw_add51c {c : Nat} (hc : c ≤ 64) {x y X Y : BitVec 64}
    (hx : x.setWidth c = X.setWidth c) (hy : y.setWidth c = Y.setWidth c) :
    (x + y).setWidth c = (X + Y).setWidth c := by
  rw [BitVec.setWidth_add _ _ hc, BitVec.setWidth_add _ _ hc, hx, hy]

private theorem sw_neg51c {c : Nat} (hc : c ≤ 64) {y Y : BitVec 64}
    (hy : y.setWidth c = Y.setWidth c) : (-y).setWidth c = (-Y).setWidth c := by
  rw [BitVec.neg_eq_neg_one_mul y, BitVec.neg_eq_neg_one_mul Y, BitVec.setWidth_mul _ _ hc,
    BitVec.setWidth_mul _ _ hc, hy]

private theorem sw_sub51c {c : Nat} (hc : c ≤ 64) {x y X Y : BitVec 64}
    (hx : x.setWidth c = X.setWidth c) (hy : y.setWidth c = Y.setWidth c) :
    (x - y).setWidth c = (X - Y).setWidth c := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]
  exact sw_add51c hc hx (sw_neg51c hc hy)

private theorem add_ptr_l51c {t : Ty} {p : Ptr} {y : Val} (hy : ∀ q, y ≠ .ptr q) :
    Arm64.add t [.ptr p, y] = match Arm64.reg y with
      | some k => PtrOps.ptrRes (p.add k)
      | none => .poison := by
  cases y <;> first | exact absurd rfl (hy _) | rfl

private theorem add_ptr_r51c {t : Ty} {p : Ptr} {x : Val} (hx : ∀ q, x ≠ .ptr q) :
    Arm64.add t [x, .ptr p] = match Arm64.reg x with
      | some k => PtrOps.ptrRes (p.add k)
      | none => .poison := by
  cases x <;> first | exact absurd rfl (hx _) | rfl

private theorem add_nonptr51c {t : Ty} {x y : Val} (hx : ∀ q, x ≠ .ptr q)
    (hy : ∀ q, y ≠ .ptr q) : Arm64.add t [x, y] = Arm64.op2 t (· + ·) [x, y] := by
  cases x <;> first | exact absurd rfl (hx _) | (cases y <;> first | exact absurd rfl (hy _) | rfl)

private theorem sub_ptr_l51c {t : Ty} {p : Ptr} {y : Val} (hy : ∀ q, y ≠ .ptr q) :
    Arm64.sub t [.ptr p, y] = match Arm64.reg y with
      | some k => PtrOps.ptrRes (p.add (-k))
      | none => .poison := by
  cases y <;> first | exact absurd rfl (hy _) | rfl

private theorem sub_nonptr51c {t : Ty} {x y : Val} (hx : ∀ q, x ≠ .ptr q) :
    Arm64.sub t [x, y] = Arm64.op2 t (· - ·) [x, y] := by
  cases x <;> first | exact absurd rfl (hx _) | rfl | (cases y <;> rfl)

/-- A boolean's register is its machine word, on all 64 bits. -/
theorem reg_bool51c {y : Val} {Y k : BitVec 64} (hy : ValRel ι y Y) (hf : Fits 1 y)
    (hr : Arm64.reg y = some k) : k = Y := by
  cases y with
  | bool b =>
    have hr' : (if b then (1 : BitVec 64) else 0) = k := Option.some.inj hr
    have hy' : Y = if b then 1 else 0 := hy
    rw [← hr', hy']
  | int w v =>
    have h : w.bits = 1 := hf
    cases w <;> exact absurd h (by decide)
  | ptr p =>
    have h : (1 : Nat) = 64 := hf
    omega
  | poison => cases hr
  | _ => exact False.elim hf

/-- `reg_info` for an argument of class `cb` at least `c` or a boolean: its register agrees with
its machine word on the low `c` bits, and on all of them at `c = 64`. -/
theorem reg_info51c (hA : AddrAgree ι) {c cb : Nat} {y : Val} {Y k : BitVec 64}
    (hy : ValRel ι y Y) (hf : Fits cb y) (hcb : c ≤ cb ∨ cb = 1) (hr : Arm64.reg y = some k) :
    k.setWidth c = Y.setWidth c ∧ (c < 64 ∨ k = Y) := by
  rcases hcb with hcb | rfl
  · have h1 := reg_low hA hy hf hr
    have h2 := fits_le51c hf hr
    refine ⟨low_le51c h1 hcb, ?_⟩
    rcases Nat.lt_or_ge c 64 with h | h
    · exact .inl h
    · right
      have : cb = 64 := by omega
      subst this
      simpa only [BitVec.setWidth_eq] using h1
  · have := reg_bool51c hy hf hr
    subst this
    exact ⟨rfl, .inr rfl⟩

/-- The register of an argument of class 64 or a boolean is its machine word. -/
theorem reg_full51c (hA : AddrAgree ι) {cb : Nat} {y : Val} {Y k : BitVec 64}
    (hy : ValRel ι y Y) (hf : Fits cb y) (hcb : cb = 64 ∨ cb = 1) (hr : Arm64.reg y = some k) :
    k = Y := by
  rcases hcb with rfl | rfl
  · simpa only [BitVec.setWidth_eq] using reg_low hA hy hf hr
  · exact reg_bool51c hy hf hr

/-- `lo_op2` with arguments of classes at least `c` or booleans. -/
theorem lo_op2_51c (hA : AddrAgree ι) {t : Ty} {f : BitVec 64 → BitVec 64 → BitVec 64}
    {x y : Val} {X Y : BitVec 64} {c ca cb : Nat}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (hca : c ≤ ca ∨ ca = 1) (hcb : c ≤ cb ∨ cb = 1) (ht : t ≠ .bool)
    (hf : ∀ a b, a.setWidth c = X.setWidth c → b.setWidth c = Y.setWidth c →
      (f a b).setWidth c = (f X Y).setWidth c) :
    Lo ι c (Arm64.op2 t f [x, y]) (f X Y) := by
  simp only [Arm64.op2]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      show Lo ι c (Arm64.res t (f a b)) (f X Y)
      rw [res_int51c ht]
      exact hf a b (reg_info51c hA hx hfx hca hrx).1 (reg_info51c hA hy hfy hcb hry).1

/-- `lo_addP` for a register of class at least `c` or a boolean. -/
theorem lo_addP51c (hA : AddrAgree ι) {t : Ty} {x : Val} {X k K : BitVec 64} {c ca : Nat}
    (hx : ValRel ι x X) (hfx : Fits ca x) (hc : c ≤ 64) (hca : c ≤ ca ∨ ca = 1) (ht : t ≠ .bool)
    (hk : k.setWidth c = K.setWidth c) (hK : c < 64 ∨ k = K) :
    Lo ι c (Arm64.addP t x k) (X + K) := by
  rcases ptr_or51c x with ⟨p, rfl⟩ | hxp
  · have h64 : ca = 64 := hfx
    exact lo_addP hA hx hfx hc (by omega) ht hk hK
  · have hx' : Arm64.addP t x k = match Arm64.reg x with
        | some a => Arm64.res t (a + k)
        | none => .poison := by
      cases x <;> first | exact absurd rfl (hxp _) | rfl
    rw [hx']
    cases hr : Arm64.reg x with
    | none => trivial
    | some a =>
      obtain ⟨ha, -⟩ := reg_info51c hA hx hfx hca hr
      show Lo ι c (Arm64.res t (a + k)) (X + K)
      rw [res_int51c ht]
      exact sw_add51c hc ha hk

/-- `ADD` with arguments of classes at least `c` or booleans, one of them a boolean. -/
theorem lo_add51c (hA : AddrAgree ι) {t : Ty} {x y : Val} {X Y : BitVec 64} {c ca cb : Nat}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y) (hc : c ≤ 64)
    (hca : c ≤ ca ∨ ca = 1) (hcb : c ≤ cb ∨ cb = 1) (h1 : ca = 1 ∨ cb = 1) (ht : t ≠ .bool) :
    Lo ι c (Arm64.add t [x, y]) (X + Y) := by
  rcases ptr_or51c x with ⟨p, rfl⟩ | hxp <;> rcases ptr_or51c y with ⟨q, rfl⟩ | hyp
  · have : ca = 64 := hfx
    have : cb = 64 := hfy
    omega
  · rw [add_ptr_l51c hyp]
    cases hr : Arm64.reg y with
    | none => trivial
    | some k =>
      obtain ⟨hk, hK⟩ := reg_info51c hA hy hfy hcb hr
      show Lo ι c (Arm64.addP t (.ptr p) k) (X + Y)
      exact lo_addP51c hA hx hfx hc hca ht hk hK
  · rw [add_ptr_r51c hxp]
    cases hr : Arm64.reg x with
    | none => trivial
    | some k =>
      obtain ⟨hk, hK⟩ := reg_info51c hA hx hfx hca hr
      rw [BitVec.add_comm X Y]
      show Lo ι c (Arm64.addP t (.ptr q) k) (Y + X)
      exact lo_addP51c hA hy hfy hc hcb ht hk hK
  · rw [add_nonptr51c hxp hyp]
    exact lo_op2_51c hA hx hy hfx hfy hca hcb ht fun _ _ ha hb => sw_add51c hc ha hb

/-- `SUB` with arguments of classes at least `c` or booleans, one of them a boolean: at most one
pointer operand. -/
theorem lo_sub51c (hA : AddrAgree ι) {t : Ty} {x y : Val} {X Y : BitVec 64} {c ca cb : Nat}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y) (hc : c ≤ 64)
    (hca : c ≤ ca ∨ ca = 1) (hcb : c ≤ cb ∨ cb = 1) (h1 : ca = 1 ∨ cb = 1) (ht : t ≠ .bool) :
    Lo ι c (Arm64.sub t [x, y]) (X - Y) := by
  rcases ptr_or51c x with ⟨p, rfl⟩ | hxp
  · have hca64 : ca = 64 := hfx
    have hyp : ∀ q, y ≠ .ptr q := by
      rintro q rfl
      have : cb = 64 := hfy
      omega
    rw [sub_ptr_l51c hyp]
    cases hr : Arm64.reg y with
    | none => trivial
    | some k =>
      obtain ⟨hk, hK⟩ := reg_info51c hA hy hfy hcb hr
      rw [BitVec.sub_eq_add_neg]
      show Lo ι c (Arm64.addP t (.ptr p) (-k)) (X + -Y)
      refine lo_addP hA hx hfx hc (by omega) ht (sw_neg51c hc hk) ?_
      rcases hK with h | rfl
      · exact .inl h
      · exact .inr rfl
  · rw [sub_nonptr51c hxp]
    exact lo_op2_51c hA hx hy hfx hfy hca hcb ht fun _ _ ha hb => sw_sub51c hc ha hb

/-- `ADDconst`/`SUBconst` (`addK` with the constant or its negation) of a boolean. -/
theorem lo_addK51c (hA : AddrAgree ι) {t : Ty} {x : Val} {X k : BitVec 64} {c : Nat}
    (hx : ValRel ι x X) (hfx : Fits 1 x) (hc : c ≤ 64) (ht : t ≠ .bool) :
    Lo ι c (Arm64.addK t k [x]) (X + k) :=
  show Lo ι c (Arm64.addP t x k) (X + k) from lo_addP51c hA hx hfx hc (.inr rfl) ht rfl (.inr rfl)

/-- `ADDshiftLL [k]` with arguments of classes at least `c` or booleans. -/
theorem lo_addSh51c (hA : AddrAgree ι) {t : Ty} {x y : Val} {X Y : BitVec 64} {c ca cb : Nat}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y) (hc : c ≤ 64)
    (hca : c ≤ ca ∨ ca = 1) (hcb : c ≤ cb ∨ cb = 1) (ht : t ≠ .bool) {k : Int64}
    (hk : Arm64.amt k < 64) :
    Lo ι c (Arm64.addSh t .ll k [x, y]) (X + Y <<< Arm64.amt k) := by
  have he : Arm64.addSh t .ll k [x, y] = match Arm64.reg y with
      | some b => Arm64.addP t x (Arm64.shifted .ll k b)
      | none => .poison := rfl
  rw [he]
  cases hr : Arm64.reg y with
  | none => trivial
  | some b =>
    obtain ⟨hb, hY⟩ := reg_info51c hA hy hfy hcb hr
    have hs : Arm64.shifted .ll k b = b <<< Arm64.amt k := by
      simp only [Arm64.shifted, Sem.Arm64.Shift.apply, Nat.mod_eq_of_lt hk]
    show Lo ι c (Arm64.addP t x (Arm64.shifted .ll k b)) _
    rw [hs]
    refine lo_addP51c hA hx hfx hc hca ht (shl_low hb) ?_
    rcases hY with h | rfl
    · exact Or.inl h
    · exact Or.inr rfl

/-- `lo_shOp36` with `x` of class at least `c` or a boolean, `y` too for a left shift, else of
64 bits or a boolean. -/
theorem lo_shOp51c (hA : AddrAgree ι) {t : Ty} {as : As} {typ : Nat} {k : Int64} {x y : Val}
    {X Y : BitVec 64} {c ca cb : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x)
    (hfy : Fits cb y) (has : as = .ADD ∨ as = .SUB) (hc : c ≤ 64) (hca : c ≤ ca ∨ ca = 1)
    (hll : typ = 0 → c ≤ cb ∨ cb = 1) (hrr : typ ≠ 0 → cb = 64 ∨ cb = 1) (ht : t ≠ .bool)
    (hk : Arm64.amt k < 64) :
    Lo ι c (shOpV36 as typ t k [x, y])
      (shOpF36 as X (Sem.Arm64.Shift.apply (shK typ) Y (Arm64.amt k))) := by
  -- the shifted register of `y`, agreeing with `Y`'s on the low `c` bits (all of them at `c = 64`)
  have hsh : ∀ b, Arm64.reg y = some b →
      (Arm64.shifted (shK typ) k b).setWidth c =
        (Sem.Arm64.Shift.apply (shK typ) Y (Arm64.amt k)).setWidth c ∧
      (c < 64 ∨ Arm64.shifted (shK typ) k b = Sem.Arm64.Shift.apply (shK typ) Y (Arm64.amt k)) := by
    intro b hry
    unfold Arm64.shifted
    by_cases h0 : typ = 0
    · subst h0
      obtain ⟨hb, hY⟩ := reg_info51c hA hy hfy (hll rfl) hry
      have hs : ∀ z : BitVec 64,
          Sem.Arm64.Shift.apply (shK 0) z (Arm64.amt k) = z <<< Arm64.amt k := by
        intro z
        simp only [shK, Sem.Arm64.Shift.apply, Nat.mod_eq_of_lt hk]
      rw [hs, hs]
      refine ⟨shl_low hb, ?_⟩
      rcases hY with h | rfl
      · exact .inl h
      · exact .inr rfl
    · have := reg_full51c hA hy hfy (hrr h0) hry
      subst this
      exact ⟨rfl, .inr rfl⟩
  rcases has with rfl | rfl
  · show Lo ι c (Arm64.addSh t (shK typ) k [x, y]) _
    simp only [Arm64.addSh]
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      obtain ⟨h1, h2⟩ := hsh b hry
      exact lo_addP51c hA hx hfx hc hca ht h1 h2
  · show Lo ι c (Arm64.subSh t (shK typ) k [x, y]) _
    simp only [Arm64.subSh]
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      obtain ⟨h1, h2⟩ := hsh b hry
      show Lo ι c (Arm64.addP t x (-Arm64.shifted (shK typ) k b)) (X - _)
      rw [BitVec.sub_eq_add_neg]
      refine lo_addP51c hA hx hfx hc hca ht (sw_neg51c hc h1) ?_
      rcases h2 with h | h
      · exact .inl h
      · exact .inr (by rw [h])

/-- `lo_logSh` with `x` of class at least `c` or a boolean, `y` too for a left shift, else of
64 bits or a boolean. -/
theorem lo_logSh51c (hA : AddrAgree ι) {t : Ty} {as : As} {typ : Nat} {k : Int64} {x y : Val}
    {X Y : BitVec 64} {c ca cb : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x)
    (hfy : Fits cb y) (hca : c ≤ ca ∨ ca = 1) (hll : typ = 0 → c ≤ cb ∨ cb = 1)
    (hrr : typ ≠ 0 → cb = 64 ∨ cb = 1) (ht : t ≠ .bool) :
    Lo ι c (Arm64.opSh t (shK typ) k (logF as) [x, y])
      (logF as X (Sem.Arm64.Shift.apply (shK typ) Y (Arm64.amt k))) := by
  simp only [Arm64.opSh, Arm64.op2]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      show Lo ι c (Arm64.res t (logF as a (Arm64.shifted (shK typ) k b))) _
      rw [res_int51c ht]
      show (logF as a (Arm64.shifted (shK typ) k b)).setWidth c = _
      refine logF_low (reg_info51c hA hx hfx hca hrx).1 ?_
      unfold Arm64.shifted
      by_cases h0 : typ = 0
      · subst h0
        exact shl_low (reg_info51c hA hy hfy (hll rfl) hry).1
      · rw [reg_full51c hA hy hfy (hrr h0) hry]

end Vals

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `ADD`/`SUB Rm, Rn, Rd` with a boolean argument. -/
theorem g51c_alu (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca cb c : Nat} {rn rm rd : Int}
    (hop : v.op = .ARM64ADD ∧ as = .ADD ∨ v.op = .ARM64SUB ∧ as = .SUB) (hsz : v.args.size = 2)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca ∨ ca = 1)
    (hcb : c ≤ cb ∨ cb = 1) (h1 : ca = 1 ∨ cb = 1)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  have hKL := knext_set hK hnp hvh hcv
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure hl htemp
    (by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  have hc := cls_le hcv
  rcases hop with ⟨hop, rfl⟩ | ⟨hop, rfl⟩
  · have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x, y] =
        Arm64.add (lc.ty v.id) [x, y] := by rw [hop]; rfl
    rw [he]
    refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
      (valRel_retypeL_lo hA hcv ht (lo_add51c hA hxv hyv hxf hyf hc hca hcb h1 ht))
      (fits_retypeL hcv _) hKL (fun k0 hk0' hok => ?_)).imp
      fun m' ⟨e1, e2, e3, e4⟩ => ⟨e1, e2, e3, hsi, .inr ⟨r, kd, _, hvh, hor, e4⟩⟩
    obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
    rw [progStep_aluReg hkn hkm hkd (nextAddr_pcAt F.nodup hk0') (Or.inl has) hf hr ht', wX_pc]
    simp only [has, ↓reduceIte]
    rfl
  · have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x, y] =
        Arm64.sub (lc.ty v.id) [x, y] := by rw [hop]; rfl
    rw [he]
    refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
      (valRel_retypeL_lo hA hcv ht (lo_sub51c hA hxv hyv hxf hyf hc hca hcb h1 ht))
      (fits_retypeL hcv _) hKL (fun k0 hk0' hok => ?_)).imp
      fun m' ⟨e1, e2, e3, e4⟩ => ⟨e1, e2, e3, hsi, .inr ⟨r, kd, _, hvh, hor, e4⟩⟩
    obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
    rw [progStep_aluReg hkn hkm hkd (nextAddr_pcAt F.nodup hk0') (Or.inr has) hf hr ht', wX_pc]
    simp only [has, reduceCtorEq, ↓reduceIte]
    rfl

/-- `ADD`/`SUB $k, Rn, Rd` of a boolean. -/
theorem g51c_aluK (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {c : Nat} {rn rd : Int}
    (hop : v.op = .ARM64ADDconst ∧ as = .ADD ∨ v.op = .ARM64SUBconst ∧ as = .SUB)
    (hsz : v.args.size = 1) (hao : argObj lc v 0 = .ok (1, rn)) (hro : resObj lc v = .ok (c, rd))
    (h8 : 8 ≤ c)
    (hvs : OneAt2 psA j
      (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  have hKL := knext_set hK hnp hvh hcv
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure hl htemp
    (by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  have hc := cls_le hcv
  rcases hop with ⟨hop, rfl⟩ | ⟨hop, rfl⟩
  · have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x] =
        Arm64.addK (lc.ty v.id) (BitVec.ofInt 64 v.auxInt.toInt) [x] := by rw [hop]; rfl
    rw [he]
    refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
      (valRel_retypeL_lo hA hcv ht (lo_addK51c hA hxv hxf hc ht))
      (fits_retypeL hcv _) hKL (fun k0 hk0' hok => ?_)).imp
      fun m' ⟨e1, e2, e3, e4⟩ => ⟨e1, e2, e3, hsi, .inr ⟨r, kd, _, hvh, hor, e4⟩⟩
    obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
    rw [progStep_aluConst hkn hkd (nextAddr_pcAt F.nodup hk0') (Or.inl has) hf hr ht', wX_pc]
    simp only [has, ↓reduceIte]
    rfl
  · have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x] =
        Arm64.addK (lc.ty v.id) (-BitVec.ofInt 64 v.auxInt.toInt) [x] := by rw [hop]; rfl
    rw [he]
    have hlo := lo_addK51c hA hxv hxf hc ht (k := -BitVec.ofInt 64 v.auxInt.toInt)
      (t := lc.ty v.id)
    rw [← BitVec.sub_eq_add_neg] at hlo
    refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
      (valRel_retypeL_lo hA hcv ht hlo)
      (fits_retypeL hcv _) hKL (fun k0 hk0' hok => ?_)).imp
      fun m' ⟨e1, e2, e3, e4⟩ => ⟨e1, e2, e3, hsi, .inr ⟨r, kd, _, hvh, hor, e4⟩⟩
    obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
    rw [progStep_aluConst hkn hkd (nextAddr_pcAt F.nodup hk0') (Or.inr has) hf hr ht', wX_pc]
    simp only [has, reduceCtorEq, ↓reduceIte]
    rfl

/-- `ADD Rm<<k, Rn, Rd` with a boolean argument. -/
theorem g51c_addSh (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca cb c : Nat} {rn rm rd : Int} (hop : v.op = .ARM64ADDshiftLL) (hsz : v.args.size = 2)
    (hk0 : 0 ≤ v.auxInt.toInt) (hk64 : v.auxInt.toInt < 64)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca ∨ ca = 1)
    (hcb : c ≤ cb ∨ cb = 1)
    (hvs : OneAt2 psA j (.ofShape
      { as := .ADD, from_ := shiftLLA rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_addSh hl htemp hop hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  have hamt : Arm64.amt v.auxInt = v.auxInt.toInt.toNat := rfl
  have hk : v.auxInt.toInt.toNat < 64 := by omega
  have hlo := lo_addSh51c hA hxv hyv hxf hyf (cls_le hcv) hca hcb ht (k := v.auxInt)
    (t := lc.ty v.id) (by rw [hamt]; exact hk)
  rw [hamt] at hlo
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_retypeL_lo hA hcv ht hlo)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨e1, e2, e3, e4⟩ => ⟨e1, e2, e3, hsi, .inr ⟨r, kd, _, hvh, hor, e4⟩⟩
  obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_addShiftLL hkn hkm hkd hk (nextAddr_pcAt F.nodup hk0') has hf hr ht', wX_pc]
  rfl

/-- `ADD`/`SUB Rm SHIFT k, Rn, Rd` with a boolean argument. -/
theorem g51c_shOp (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {typ ca cb c : Nat} {rn rm rd : Int} (hop : shOp36? v.op = some (as, typ))
    (hsz : v.args.size = 2) (hk0 : 0 ≤ v.auxInt.toInt) (hk64 : v.auxInt.toInt < 64)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca ∨ ca = 1)
    (hll : typ = 0 → c ≤ cb ∨ cb = 1) (hrr : typ ≠ 0 → cb = 64 ∨ cb = 1)
    (hvs : OneAt2 psA j (.ofShape
      { as, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp36_shOp hop
  have hnp : v.op ≠ .Phi := (aluOp36_ne halu).1
  have has : as = .ADD ∨ as = .SUB := by
    rcases shOp36?_some hop with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
      simp [h]
  have ht3 : typ < 3 := by
    rcases shOp36?_some hop with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;>
      omega
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu36 hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv, evalPure_shOp36 hop]
  have ht := cls_ne_bool hcv h8
  have hamt : Arm64.amt v.auxInt = v.auxInt.toInt.toNat := rfl
  have hk : v.auxInt.toInt.toNat < 64 := by omega
  have hlo := lo_shOp51c (k := v.auxInt) hA hxv hyv hxf hyf has (cls_le hcv) hca hll hrr ht
    (by rw [hamt]; exact hk)
  rw [hamt] at hlo
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_retypeL_lo hA hcv ht hlo)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨e1, e2, e3⟩ => ⟨e1, e2, e3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_shOp36 has ht3 hkn hkm hkd hk (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `AND`/`ORR`/`EOR`/`BIC Rm SHIFT k, Rn, Rd` with a boolean argument, which writes only its
register (`XW`). -/
theorem g51c_logSh (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {typ ca cb c : Nat} {rn rm rd : Int} (hop : logSh? v.op = some (as, typ))
    (hsz : v.args.size = 2) (hk0 : 0 ≤ v.auxInt.toInt) (hk64 : v.auxInt.toInt < 64)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca ∨ ca = 1)
    (hll : typ = 0 → c ≤ cb ∨ cb = 1) (hrr : typ ≠ 0 → cb = 64 ∨ cb = 1)
    (hvs : OneAt2 psA j (.ofShape
      { as, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := (logSh_noclobber hop).1
  have has : as = .AND ∨ as = .ORR ∨ as = .EOR ∨ as = .BIC := by
    rcases logSh?_some hop with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  have ht3 := logSh?_typ hop
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_logSh hl htemp hop hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  have hamt : Arm64.amt v.auxInt = v.auxInt.toInt.toNat := rfl
  have hk : v.auxInt.toInt.toNat < 64 := by omega
  have hlo := lo_logSh51c (as := as) (typ := typ) (k := v.auxInt) hA hxv hyv hxf hyf hca hll hrr ht
  rw [hamt] at hlo
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_retypeL_lo hA hcv ht hlo)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨e1, e2, e3, e4⟩ => ⟨e1, e2, e3, hsi, .inr ⟨r, kd, _, hvh, hor, e4⟩⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_logSh has ht3 hkn hkm hkd hk (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

end Cases

/-! ## One value -/

/-- `ADD`, `SUB`, `ADDconst`, `SUBconst`, `ADDshiftLL` write only their register: G35's table
drops the entry of the home. -/
theorem uStep35_keep51c {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (h : v.op = .ARM64ADD ∨ v.op = .ARM64SUB ∨ v.op = .ARM64ADDconst ∨ v.op = .ARM64SUBconst ∨
      v.op = .ARM64ADDshiftLL) :
    uStep35 lc L v = L.filter fun e => regHome? lc v.id != some e.1 := by
  have hl : loadOp? v.op = none := by
    rcases h with h | h | h | h | h <;> rw [h] <;> rfl
  rw [uStep35_other (ldEntry35_none hl (by rcases h with h | h | h | h | h <;> rw [h] <;> nofun))
      (by rcases h with h | h | h | h | h <;> simp [pairOp35, h])
      (by rcases h with h | h | h | h | h <;> rw [h] <;> nofun),
    uStep34_keep (by rcases h with h | h | h | h | h <;> simp [keep34, keep31, keepOp31, keepOp34, h])]

/-- A shifted logic op is a kept op of G35's table. -/
theorem logSh_keep35 {op : Op} {as : As} {typ : Nat} (h : logSh? op = some (as, typ)) :
    op ∈ keepOps35 := by
  rcases logSh?_some h with ⟨hop, -⟩ | ⟨hop, -⟩ | ⟨hop, -⟩ | ⟨hop, -⟩ <;>
    rcases hop with rfl | rfl | rfl <;> simp [keepOps35]

/-- One value of G51c's kinds (`VK51c`) emitted at the Progs from `j` to `j'`: the machine runs
from `m` to `m'` matching the state after the value, with the class map `kStep lc K v` and G35's
upper-bit table after the value. `ADD`, `SUB`, `ADDconst`, `SUBconst`, `ADDshiftLL` keep the
table's other entries, so the table before the value must hold (`hL`). -/
theorem vk51c_step {env : Env} {H : Hooks} {lc : LocCtx} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (F : Facts lc sym text az ez ps.toList ret E) (hVK : VK51c lc v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' osp ∧ UOKL m'
      (uStep35 lc L v) := by
  have hR := kread_of_reads hreads
  have hempty : ∀ m', UOKL m' [] := fun _ e he => by cases he
  cases hVK with
  | alu hop hsz hao hbo hro h8 hca hcb h1 =>
    obtain ⟨r, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', e1, e2, e3, e4, e5⟩ := g51c_alu (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo hro h8 hca hcb h1 hvs
      htemp hs
    refine ⟨m', e1, e2, ⟨e3, e4⟩, ?_⟩
    rw [uStep35_keep51c (by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h])]
    exact uokl_keep hL e5
  | aluK hop hsz hao hro h8 =>
    obtain ⟨r, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', e1, e2, e3, e4, e5⟩ := g51c_aluK (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro h8 hvs htemp hs
    refine ⟨m', e1, e2, ⟨e3, e4⟩, ?_⟩
    rw [uStep35_keep51c (by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h])]
    exact uokl_keep hL e5
  | addSh hop hsz hk0 hk64 hao hbo hro h8 hca hcb _ =>
    obtain ⟨r, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', e1, e2, e3, e4, e5⟩ := g51c_addSh (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk64 hao hbo hro h8 hca hcb
      hvs htemp hs
    refine ⟨m', e1, e2, ⟨e3, e4⟩, ?_⟩
    rw [uStep35_keep51c (by simp [hop])]
    exact uokl_keep hL e5
  | sh hop hsz hk0 hk64 hao hbo hro h8 hca hll hrr _ =>
    obtain ⟨r, hvh, -, -, -⟩ := resObj_spec hro
    rcases hop with hop | hop
    · obtain ⟨m', e1, e2, e3, e4, e5⟩ := g51c_logSh (H := H) F hm hinv.core hinv.slots hR
        (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk64 hao hbo hro h8 hca
        hll hrr hvs htemp hs
      exact ⟨m', e1, e2, ⟨e3, e4⟩, uokl_keepOps (logSh_keep35 hop) hL e5⟩
    · obtain ⟨m', e1, e2, e3, e4⟩ := g51c_shOp (H := H) F hm hinv.core hinv.slots hR
        (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk64 hao hbo hro h8 hca
        hll hrr hvs htemp hs
      refine ⟨m', e1, e2, ⟨e3, e4⟩, ?_⟩
      rw [uStep35_alu36 (aluOp36_shOp hop) (shOp36_sh hop)]
      exact hempty m'

end GoFV.Proof.Gen
