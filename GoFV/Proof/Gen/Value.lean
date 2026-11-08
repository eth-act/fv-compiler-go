import GoFV.Proof.Gen.Rel

variable [GoFV.SSA.Sem.Addrs]

/-!
# The values of slice G1's ops against the machine's words (`docs/plans/proofs3.md` §3)

Under `AddrAgree` (`Rel.lean`), each pure op G1 accepts (`Arm64.add`, `Arm64.sub`, `Arm64.addK`,
`Arm64.res` of a constant, `Arm64.cmp`, `Arm64.isZero`) computes, from arguments related to
machine words `X`, `Y` (`ValRel`) and of their register's width class (`Fits`), a value related
to the word the Prog computes (`X + Y`, …).

`Lo ι c z Z`: a 64-bit register result `z` agrees with the machine word `Z` on the low `c` bits
(a pointer: is `Z` under `ι` when `c = 64`). Arithmetic on arguments of classes at least `c`
gives `Lo` at class `c` (only the low bits of a narrow argument's register are known), and `Lo`
at the class of a non-boolean shape gives `ValRel` of the result read at that shape
(`valRel_retypeL_lo`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

variable {ι : Blk → Option (BitVec 64)}

/-- A 64-bit register result and the machine word on the low `c` bits. -/
def Lo (ι : Blk → Option (BitVec 64)) (c : Nat) : Val → BitVec 64 → Prop
  | .int .w64 z, Z => z.setWidth c = Z.setWidth c
  | .ptr p, Z => c < 64 ∨ PtrRel ι p Z
  | .poison, _ => True
  | _, _ => False

/-! ## Helpers -/

private theorem low_of_le {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem sw_add {c : Nat} (hc : c ≤ 64) {x y X Y : BitVec 64}
    (hx : x.setWidth c = X.setWidth c) (hy : y.setWidth c = Y.setWidth c) :
    (x + y).setWidth c = (X + Y).setWidth c := by
  rw [BitVec.setWidth_add _ _ hc, BitVec.setWidth_add _ _ hc, hx, hy]

private theorem sw_neg {c : Nat} (hc : c ≤ 64) {y Y : BitVec 64}
    (hy : y.setWidth c = Y.setWidth c) : (-y).setWidth c = (-Y).setWidth c := by
  rw [BitVec.neg_eq_neg_one_mul y, BitVec.neg_eq_neg_one_mul Y, BitVec.setWidth_mul _ _ hc,
    BitVec.setWidth_mul _ _ hc, hy]

private theorem sw_sub {c : Nat} (hc : c ≤ 64) {x y X Y : BitVec 64}
    (hx : x.setWidth c = X.setWidth c) (hy : y.setWidth c = Y.setWidth c) :
    (x - y).setWidth c = (X - Y).setWidth c := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]
  exact sw_add hc hx (sw_neg hc hy)

private theorem ptrReg_some {p : Ptr} {a : BitVec 64} (h : Arm64.ptrReg p = some a) :
    p.addr? = some a ∧ Ptr.ofAddr a = p := by
  unfold Arm64.ptrReg at h
  split at h
  · rename_i a' ha
    split at h
    · cases h; exact ⟨ha, by assumption⟩
    · cases h
  · cases h

private theorem ptrReg_notTemp {p : Ptr} {a : BitVec 64} (h : Arm64.ptrReg p = some a) :
    NotTemp p.blk := by
  rw [← (ptrReg_some h).2]; exact notTemp_ofAddr a

private theorem ptr_or (x : Val) : (∃ p, x = .ptr p) ∨ ∀ p, x ≠ .ptr p := by
  cases x <;> simp

private theorem res_int {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

/-- A register content of class `c` with a register has `c ≤ 64`. -/
private theorem fits_le {c : Nat} {x : Val} {r : BitVec 64} (hf : Fits c x)
    (hr : Arm64.reg x = some r) : c ≤ 64 := by
  cases x with
  | int w v =>
    have h : w.bits = c := hf
    subst h
    cases w <;> decide
  | bool b => have h : c = 1 := hf; omega
  | ptr p => have h : c = 64 := hf; omega
  | poison => cases hr
  | _ => exact False.elim hf

/-- `Lo` at 64 bits gives `Lo` at any class. -/
theorem Lo.mono {c : Nat} {z : Val} {Z : BitVec 64} (h : Lo ι 64 z Z) (hc : c ≤ 64) : Lo ι c z Z := by
  cases z with
  | int w z =>
    cases w
    case w64 =>
      have h' : z.setWidth 64 = Z.setWidth 64 := h
      exact low_of_le h' hc
    all_goals exact False.elim h
  | ptr p =>
    rcases (h : 64 < 64 ∨ PtrRel ι p Z) with h | h
    · omega
    · exact Or.inr h
  | poison => trivial
  | _ => exact False.elim h

/-- A result agreeing on the low bits of the class of a non-boolean register shape is related
to the machine word when read at that shape. -/
theorem valRel_retypeL_lo (hA : AddrAgree ι) {t : Ty} {c : Nat} {z : Val} {Z : BitVec 64}
    (hc : cls t = some c) (ht : t ≠ .bool) (h : Lo ι c z Z) : ValRel ι (z.retypeL t) Z := by
  cases t with
  | int w =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases z with
    | poison => trivial
    | int v x =>
      cases v
      case w64 =>
        have h' : x.setWidth w.bits = Z.setWidth w.bits := h
        cases w
        case w64 =>
          exact Or.inl (by simpa only [BitVec.setWidth_eq] using h'.symm)
        all_goals exact h'.symm
      all_goals exact False.elim h
    | ptr p =>
      cases w
      case w64 =>
        rcases (h : 64 < 64 ∨ PtrRel ι p Z) with h | h
        · exact absurd h (Nat.lt_irrefl _)
        · exact valRel_word hA h
      all_goals trivial
    | _ => exact False.elim h
  | ptr e =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases z with
    | poison => trivial
    | int v x =>
      cases v
      case w64 =>
        have h' : x.setWidth 64 = Z.setWidth 64 := h
        exact Or.inl (by simpa only [BitVec.setWidth_eq] using h'.symm)
      all_goals exact False.elim h
    | ptr p =>
      rcases (h : 64 < 64 ∨ PtrRel ι p Z) with h | h
      · omega
      · exact valRel_word hA h
    | _ => exact False.elim h
  | bool => exact absurd rfl ht
  | _ => simp [cls] at hc

/-- The register of an argument of class `c` agrees with the machine word on the low `c` bits. -/
theorem reg_low (hA : AddrAgree ι) {c : Nat} {x : Val} {X x' : BitVec 64} (hx : ValRel ι x X)
    (hf : Fits c x) (hr : Arm64.reg x = some x') : x'.setWidth c = X.setWidth c := by
  cases x with
  | poison => cases hr
  | int w v =>
    have hr' : v.setWidth 64 = x' := Option.some.inj hr
    subst hr'
    have hf' : w.bits = c := hf
    subst hf'
    cases w
    case w64 =>
      have := valRel_i64 hA hx
      subst this
      rfl
    all_goals
      have hx' : X.setWidth _ = v := hx
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hx']
  | bool b =>
    have hr' : (if b then (1 : BitVec 64) else 0) = x' := Option.some.inj hr
    have hx' : X = if b then 1 else 0 := hx
    rw [hx', hr']
  | ptr p =>
    have := ptrRel_addr hA hx (ptrReg_some hr).1 (ptrReg_notTemp hr)
    subst this
    rfl
  | _ => cases hr

/-- What the register of an argument of class `cb ≥ c` gives. -/
private theorem reg_info (hA : AddrAgree ι) {c cb : Nat} {y : Val} {Y k : BitVec 64}
    (hy : ValRel ι y Y) (hf : Fits cb y) (hcb : c ≤ cb) (hr : Arm64.reg y = some k) :
    c ≤ 64 ∧ k.setWidth c = Y.setWidth c ∧ (c < 64 ∨ k = Y) := by
  have h1 := reg_low hA hy hf hr
  have h2 := fits_le hf hr
  refine ⟨by omega, low_of_le h1 hcb, ?_⟩
  rcases Nat.lt_or_ge c 64 with h | h
  · exact Or.inl h
  · right
    have : cb = 64 := by omega
    subst this
    simpa only [BitVec.setWidth_eq] using h1

/-- A pointer moved by a register `k` agreeing with `Y` on the low `c` bits. -/
private theorem lo_ptrRes (hA : AddrAgree ι) {c : Nat} {p : Ptr} {k X Y : BitVec 64}
    (hp : PtrRel ι p X) (hc : c ≤ 64) (hk : k.setWidth c = Y.setWidth c) (hY : c < 64 ∨ k = Y) :
    Lo ι c (PtrOps.ptrRes (p.add k)) (X + Y) := by
  unfold PtrOps.ptrRes
  split
  · unfold Ptr.word
    split
    · rename_i a hcv ha
      rw [Ptr.addr?_add] at ha
      cases hpa : p.addr? with
      | none => rw [hpa] at ha; cases ha
      | some a0 =>
        rw [hpa] at ha
        have ha' : a0 + k = a := Option.some.inj ha
        subst ha'
        have := ptrRel_addr hA hp hpa (notTemp_of_convertible (p := p.add k) hcv)
        subst this
        exact sw_add hc rfl hk
    · split
      · show c < 64 ∨ PtrRel ι (p.add k) (X + Y)
        rcases hY with h | rfl
        · exact Or.inl h
        · right
          obtain ⟨b, hb, rfl⟩ := hp
          exact ⟨b, hb, BitVec.add_assoc _ _ _⟩
      · trivial
  · trivial

private theorem add_ptr_ptr {t : Ty} {p q : Ptr} :
    Arm64.add t [.ptr p, .ptr q] = Arm64.op2 t (· + ·) [.ptr p, .ptr q] := rfl

private theorem add_ptr_l {t : Ty} {p : Ptr} {y : Val} (hy : ∀ q, y ≠ .ptr q) :
    Arm64.add t [.ptr p, y] = match Arm64.reg y with
      | some k => PtrOps.ptrRes (p.add k)
      | none => .poison := by
  cases y <;> first | exact absurd rfl (hy _) | rfl

private theorem add_ptr_r {t : Ty} {p : Ptr} {x : Val} (hx : ∀ q, x ≠ .ptr q) :
    Arm64.add t [x, .ptr p] = match Arm64.reg x with
      | some k => PtrOps.ptrRes (p.add k)
      | none => .poison := by
  cases x <;> first | exact absurd rfl (hx _) | rfl

private theorem add_nonptr {t : Ty} {x y : Val} (hx : ∀ q, x ≠ .ptr q) (hy : ∀ q, y ≠ .ptr q) :
    Arm64.add t [x, y] = Arm64.op2 t (· + ·) [x, y] := by
  cases x <;> first | exact absurd rfl (hx _) | (cases y <;> first | exact absurd rfl (hy _) | rfl)

/-- `op2` on registers related to `X`, `Y` on the low `c` bits. -/
private theorem lo_op2 (hA : AddrAgree ι) {t : Ty} {f : BitVec 64 → BitVec 64 → BitVec 64}
    {x y : Val} {X Y : BitVec 64} {c ca cb : Nat}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (hca : c ≤ ca) (hcb : c ≤ cb) (ht : t ≠ .bool)
    (hf : ∀ a b, c ≤ 64 → a.setWidth c = X.setWidth c → b.setWidth c = Y.setWidth c →
      (f a b).setWidth c = (f X Y).setWidth c) :
    Lo ι c (Arm64.op2 t f [x, y]) (f X Y) := by
  simp only [Arm64.op2]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      obtain ⟨hc, ha, -⟩ := reg_info hA hx hfx hca hrx
      obtain ⟨-, hb, -⟩ := reg_info hA hy hfy hcb hry
      show Lo ι c (Arm64.res t (f a b)) (f X Y)
      rw [res_int ht]
      exact hf a b hc ha hb

/-- `ADD`: arguments of classes `ca`, `cb` at least the result's class `c ≥ 8`. -/
theorem lo_add (hA : AddrAgree ι) {t : Ty} {x y : Val} {X Y : BitVec 64} {c ca cb : Nat}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb) (ht : t ≠ .bool) :
    Lo ι c (Arm64.add t [x, y]) (X + Y) := by
  rcases ptr_or x with ⟨p, rfl⟩ | hxp <;> rcases ptr_or y with ⟨q, rfl⟩ | hyp
  · rw [add_ptr_ptr]
    exact lo_op2 hA hx hy hfx hfy hca hcb ht fun _ _ hc ha hb => sw_add hc ha hb
  · rw [add_ptr_l hyp]
    cases hr : Arm64.reg y with
    | none => trivial
    | some k =>
      obtain ⟨hc, hk, hY⟩ := reg_info hA hy hfy hcb hr
      exact lo_ptrRes hA hx hc hk hY
  · rw [add_ptr_r hxp]
    cases hr : Arm64.reg x with
    | none => trivial
    | some k =>
      obtain ⟨hc, hk, hX⟩ := reg_info hA hx hfx hca hr
      rw [BitVec.add_comm X Y]
      exact lo_ptrRes hA hy hc hk hX
  · rw [add_nonptr hxp hyp]
    exact lo_op2 hA hx hy hfx hfy hca hcb ht fun _ _ hc ha hb => sw_add hc ha hb

private theorem sub_ptr_l {t : Ty} {p : Ptr} {y : Val} (hy : ∀ q, y ≠ .ptr q) :
    Arm64.sub t [.ptr p, y] = match Arm64.reg y with
      | some k => PtrOps.ptrRes (p.add (-k))
      | none => .poison := by
  cases y <;> first | exact absurd rfl (hy _) | rfl

private theorem sub_nonptr {t : Ty} {x y : Val} (hx : ∀ q, x ≠ .ptr q) :
    Arm64.sub t [x, y] = Arm64.op2 t (· - ·) [x, y] := by
  cases x <;> first | exact absurd rfl (hx _) | rfl | (cases y <;> rfl)

/-- The operands of a `SUB` that are both pointers point into one block or into no frame
temporaries (whose Phase 1 addresses the machine does not use). -/
def SubOK (x y : Val) : Prop :=
  ∀ p q, x = .ptr p → y = .ptr q → p.blk = q.blk ∨ (NotTemp p.blk ∧ NotTemp q.blk)

/-- `SUB`. -/
theorem lo_sub (hA : AddrAgree ι) {t : Ty} {x y : Val} {X Y : BitVec 64} {c ca cb : Nat}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb) (ht : t ≠ .bool) (hsub : SubOK x y) :
    Lo ι c (Arm64.sub t [x, y]) (X - Y) := by
  rcases ptr_or x with ⟨p, rfl⟩ | hxp
  · have hc : c ≤ 64 := by have : ca = 64 := hfx; omega
    rcases ptr_or y with ⟨q, rfl⟩ | hyp
    · have hxy : Arm64.sub t [.ptr p, .ptr q] = match p.addr?, q.addr? with
          | some x, some y => Arm64.res t (x - y)
          | _, _ => if p.blk == q.blk then Arm64.res t (p.off - q.off) else .poison := rfl
      rw [hxy]
      split
      · rename_i a b hpa hqa
        rcases hsub p q rfl rfl with hb | ⟨hnp, hnq⟩
        · have hab : a - b = X - Y := by
            obtain ⟨a', ha', rfl⟩ := hx
            obtain ⟨a'', ha'', rfl⟩ := hy
            rw [← hb, ha'] at ha''
            cases ha''
            unfold Ptr.addr? at hpa hqa
            rw [← hb] at hqa
            cases hn : p.blk.base? with
            | none => rw [hn] at hpa; cases hpa
            | some n =>
              rw [hn] at hpa hqa
              simp only [Option.map_some, Option.some.injEq] at hpa hqa
              subst hpa; subst hqa
              bv_omega
          rw [res_int ht, hab]
          exact (rfl : (X - Y).setWidth c = (X - Y).setWidth c)
        · have := ptrRel_addr hA hx hpa hnp
          subst this
          have := ptrRel_addr hA hy hqa hnq
          subst this
          rw [res_int ht]
          exact (rfl : (X - Y).setWidth c = (X - Y).setWidth c)
      · split
        · rename_i hb
          have hb' : p.blk = q.blk := beq_iff_eq.mp hb
          obtain ⟨a, ha, rfl⟩ := hx
          obtain ⟨a', ha', rfl⟩ := hy
          rw [← hb', ha] at ha'
          cases ha'
          rw [res_int ht]
          show (p.off - q.off).setWidth c = (a + p.off - (a + q.off)).setWidth c
          congr 1
          bv_omega
        · trivial
    · rw [sub_ptr_l hyp]
      cases hr : Arm64.reg y with
      | none => trivial
      | some k =>
        obtain ⟨-, hk, hY⟩ := reg_info hA hy hfy hcb hr
        rw [BitVec.sub_eq_add_neg]
        refine lo_ptrRes hA hx hc (sw_neg hc hk) ?_
        rcases hY with h | rfl
        · exact Or.inl h
        · exact Or.inr rfl
  · rw [sub_nonptr hxp]
    exact lo_op2 hA hx hy hfx hfy hca hcb ht fun _ _ hc ha hb => sw_sub hc ha hb

/-- `ADDconst`/`SUBconst` (`addK` with the constant or its negation). -/
theorem lo_addK (hA : AddrAgree ι) {t : Ty} {x : Val} {X k : BitVec 64} {c ca : Nat}
    (hx : ValRel ι x X) (hfx : Fits ca x) (h8 : 8 ≤ c) (hca : c ≤ ca) (ht : t ≠ .bool) :
    Lo ι c (Arm64.addK t k [x]) (X + k) := by
  show Lo ι c (Arm64.addP t x k) (X + k)
  rcases ptr_or x with ⟨p, rfl⟩ | hxp
  · have hc : c ≤ 64 := by have : ca = 64 := hfx; omega
    exact lo_ptrRes hA hx hc rfl (Or.inr rfl)
  · have hx' : Arm64.addP t x k = match Arm64.reg x with
        | some a => Arm64.res t (a + k)
        | none => .poison := by
      cases x <;> first | exact absurd rfl (hxp _) | rfl
    rw [hx']
    cases hr : Arm64.reg x with
    | none => trivial
    | some a =>
      obtain ⟨hc, ha, -⟩ := reg_info hA hx hfx hca hr
      show Lo ι c (Arm64.res t (a + k)) (X + k)
      rw [res_int ht]
      exact sw_add hc ha rfl

private theorem sw_shl {c : Nat} (hc : c ≤ 64) {y Y : BitVec 64}
    (hy : y.setWidth c = Y.setWidth c) (n : Nat) : (y <<< n).setWidth c = (Y <<< n).setWidth c := by
  rw [BitVec.shiftLeft_eq_mul_twoPow y, BitVec.shiftLeft_eq_mul_twoPow Y, BitVec.setWidth_mul _ _ hc,
    BitVec.setWidth_mul _ _ hc, hy]

/-- `addP` of a register and an addend `k` agreeing with `K` on the low `c` bits (all of them if
the register holds a pointer of a 64-bit result). -/
theorem lo_addP (hA : AddrAgree ι) {t : Ty} {x : Val} {X k K : BitVec 64} {c ca : Nat}
    (hx : ValRel ι x X) (hfx : Fits ca x) (hc : c ≤ 64) (hca : c ≤ ca) (ht : t ≠ .bool)
    (hk : k.setWidth c = K.setWidth c) (hK : c < 64 ∨ k = K) :
    Lo ι c (Arm64.addP t x k) (X + K) := by
  rcases ptr_or x with ⟨p, rfl⟩ | hxp
  · exact lo_ptrRes hA hx hc hk hK
  · have hx' : Arm64.addP t x k = match Arm64.reg x with
        | some a => Arm64.res t (a + k)
        | none => .poison := by
      cases x <;> first | exact absurd rfl (hxp _) | rfl
    rw [hx']
    cases hr : Arm64.reg x with
    | none => trivial
    | some a =>
      obtain ⟨-, ha, -⟩ := reg_info hA hx hfx hca hr
      show Lo ι c (Arm64.res t (a + k)) (X + K)
      rw [res_int ht]
      exact sw_add hc ha hk

/-- `ADDshiftLL [k]` (`addSh … .ll k`): arguments of classes `ca`, `cb` at least the result's
class `c`, a shift by `amt k < 64`. -/
theorem lo_addSh (hA : AddrAgree ι) {t : Ty} {x y : Val} {X Y : BitVec 64} {c ca cb : Nat}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y) (hc : c ≤ 64)
    (hca : c ≤ ca) (hcb : c ≤ cb) (ht : t ≠ .bool) {k : Int64} (hk : Arm64.amt k < 64) :
    Lo ι c (Arm64.addSh t .ll k [x, y]) (X + Y <<< Arm64.amt k) := by
  have he : Arm64.addSh t .ll k [x, y] = match Arm64.reg y with
      | some b => Arm64.addP t x (Arm64.shifted .ll k b)
      | none => .poison := rfl
  rw [he]
  cases hr : Arm64.reg y with
  | none => trivial
  | some b =>
    obtain ⟨-, hb, hY⟩ := reg_info hA hy hfy hcb hr
    have hs : Arm64.shifted .ll k b = b <<< Arm64.amt k := by
      simp only [Arm64.shifted, Arm64.Shift.apply, Nat.mod_eq_of_lt hk]
    show Lo ι c (Arm64.addP t x (Arm64.shifted .ll k b)) _
    rw [hs]
    refine lo_addP hA hx hfx hc hca ht (sw_shl hc hb _) ?_
    rcases hY with h | rfl
    · exact Or.inl h
    · exact Or.inr rfl

/-- A constant of a register shape (a boolean constant is 0 or 1). -/
theorem valRel_res_const {t : Ty} {c : Nat} {K : BitVec 64} (hc : cls t = some c)
    (hb : c = 1 → K = 0 ∨ K = 1) : ValRel ι ((Arm64.res t K).retypeL t) K := by
  cases t with
  | int w =>
    cases w
    case w64 => exact Or.inl (BitVec.setWidth_eq K).symm
    all_goals exact rfl
  | ptr e => exact Or.inl rfl
  | bool =>
    simp only [cls, Option.some.injEq] at hc
    rcases hb hc.symm with rfl | rfl <;> rfl
  | _ => simp [cls] at hc

/-- `ZERO` read at a register shape is related to `XZR`. -/
theorem valRel_zero {t : Ty} {c : Nat} (hc : cls t = some c) :
    ValRel ι ((Arm64.res t 0).retypeL t) 0 :=
  valRel_res_const hc fun _ => Or.inl rfl

/-- `CMP`'s result is flags-shaped (as `GoFV.Proof.Low.Rules.Cmp.retypeL_cmp`). -/
private theorem retypeL_cmp (a b : Val) : (Arm64.cmp a b).retypeL Ty.flags = Arm64.cmp a b := by
  unfold Arm64.cmp
  split
  · rfl
  · split <;> (try split) <;> rfl

/-- A register content of class 64 that is not a pointer without a register: `poison` or its
register is the machine word. -/
private theorem reg_or_poison (hA : AddrAgree ι) {x : Val} {X : BitVec 64} (hx : ValRel ι x X)
    (hf : Fits 64 x) (hp : ∀ p, x = .ptr p → (Arm64.ptrReg p).isSome) :
    x = .poison ∨ Arm64.reg x = some X := by
  cases x with
  | poison => exact Or.inl rfl
  | int w v =>
    right
    have hr : Arm64.reg (.int w v) = some (v.setWidth 64) := rfl
    have := reg_info hA hx hf (Nat.le_refl 64) hr
    rw [hr]
    rcases this.2.2 with h | h
    · omega
    · rw [h]
  | ptr p =>
    right
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hp p rfl)
    have := ptrRel_addr hA hx (ptrReg_some ha).1 (ptrReg_notTemp ha)
    subst this
    exact ha
  | bool b => exact absurd (show (64 : Nat) = 1 from hf) (by decide)
  | _ => exact False.elim hf

private theorem cmp_poison_l (y : Val) : Arm64.cmp .poison y = .poison := by
  cases y <;> rfl

private theorem cmp_poison_r {x : Val} {X : BitVec 64} (hx : Arm64.reg x = some X) :
    Arm64.cmp x .poison = .poison := by
  cases x with
  | ptr p =>
    unfold Arm64.cmp
    rw [hx]
    rfl
  | _ => rfl

/-- `CMP` of two 64-bit register contents neither of which is a pointer without a register:
the machine's `SUBS` flags, at the flags shape. -/
theorem flagsRel_cmp (hA : AddrAgree ι) {x y : Val} {X Y : BitVec 64}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits 64 x) (hfy : Fits 64 y)
    (hpx : ∀ p, x = .ptr p → (Arm64.ptrReg p).isSome) (hpy : ∀ p, y = .ptr p → (Arm64.ptrReg p).isSome) :
    FlagsRel ((Arm64.cmp x y).retypeL Ty.flags) (Arm64.subFlags X Y).2 := by
  rw [retypeL_cmp]
  rcases reg_or_poison hA hx hfx hpx with rfl | hrx
  · rw [cmp_poison_l]; trivial
  · rcases reg_or_poison hA hy hfy hpy with rfl | hry
    · rw [cmp_poison_r hrx]; trivial
    · have h : Arm64.cmp x y = Arm64.cmpRes (Arm64.subFlags X Y) := by
        unfold Arm64.cmp
        simp only [hrx, hry]
      rw [h]
      exact ⟨rfl, rfl, rfl, rfl⟩

private theorem retype_bit {b : Val} {x : Bool} (h : BitRel b x) : b.retype .bool = b := by
  cases b with
  | bool b => rfl
  | poison => rfl
  | _ => exact False.elim h

/-- Flags related to `NZCV` read back at the flags shape stay related, and every condition
reads them alike (the fifth component `g`, unconstrained by `FlagsRel`, may become `poison`). -/
theorem flags_retypeL {f : Val} {nz : Flags} (h : FlagsRel f nz) :
    FlagsRel (f.retypeL Ty.flags) nz ∧ ∀ c : Cond, c.onVal (f.retypeL Ty.flags) = c.onVal f := by
  cases f with
  | poison => exact ⟨trivial, fun _ => rfl⟩
  | agg vs =>
    rcases vs with _ | ⟨n, _ | ⟨z, _ | ⟨cf, _ | ⟨v, _ | ⟨g, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    all_goals try exact False.elim h
    obtain ⟨hn, hz, hc, hv⟩ := (h : BitRel n nz.n ∧ BitRel z nz.z ∧ BitRel cf nz.c ∧ BitRel v nz.v)
    have he : (Val.agg [n, z, cf, v, g]).retypeL Ty.flags =
        .agg [n.retype .bool, z.retype .bool, cf.retype .bool, v.retype .bool, g.retype .bool] :=
      rfl
    rw [he, retype_bit hn, retype_bit hz, retype_bit hc, retype_bit hv]
    exact ⟨⟨hn, hz, hc, hv⟩, fun _ => rfl⟩
  | _ => exact False.elim h

/-- `CBZ`'s test: a 64-bit or boolean register content that is not a pointer without a register
is zero exactly when its machine word is. -/
theorem isZero_eq (hA : AddrAgree ι) {x : Val} {X : BitVec 64} {z : Bool} (hx : ValRel ι x X)
    (hf : Fits 64 x ∨ Fits 1 x) (hp : ∀ p, x = .ptr p → (Arm64.ptrReg p).isSome)
    (h : Arm64.isZero x = some z) : z = (X == 0) := by
  cases x with
  | poison => cases h
  | int w v =>
    have hw : w = .w64 := by
      clear hx h hp
      revert hf
      cases w <;> simp [Fits, Width.bits]
    subst hw
    rw [valRel_i64 hA hx]
    have h' : (v.setWidth 64 == 0) = z := Option.some.inj h
    rw [← h', BitVec.setWidth_eq]
  | bool b =>
    have hx' : X = if b then 1 else 0 := hx
    subst hx'
    exact (Option.some.inj h).symm
  | ptr p =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hp p rfl)
    obtain ⟨hpa, hpo⟩ := ptrReg_some ha
    have := ptrRel_addr hA hx hpa (ptrReg_notTemp ha)
    subst this
    have h' : p.isNil = z := Option.some.inj h
    subst h'
    cases hn : p.isNil
    · have hX : X ≠ 0 := by
        rintro rfl
        rw [← hpo] at hn
        exact absurd hn (by decide)
      have : (X == 0) = false := beq_eq_false_iff_ne.mpr hX
      rw [this]
    · simp only [Ptr.isNil, Bool.and_eq_true, beq_iff_eq] at hn
      simp only [Ptr.addr?, hn.1, hn.2, Blk.base?_nil, Option.map_some, Option.some.injEq] at hpa
      subst hpa
      decide
  | _ => cases h

end GoFV.Proof.Gen
