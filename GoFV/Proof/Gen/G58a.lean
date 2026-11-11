import GoFV.Proof.Gen.G49
import GoFV.Proof.Gen.G51c
import GoFV.Proof.Gen.G44
import GoFV.Proof.Gen.Spec58a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G58, group A: narrow and boolean operands, wider
store-release sources, `LoweredRound*F` (`docs/plans/proofs3.md` §4)

`vk58a_step`: one value of `VK58a` (`GoFV/Proof/Gen/Spec58a.lean`) steps the machine as `runLoc`
steps it and keeps the activation (`G49Env`), with no run premise; the table of upper bits
(`uStep35`) holds after it given it held before (`hL`: G32's ops keep its other entries).

* `REV16W x` (`lo_rev16w58`): the low halfword of `REV16W`'s word swaps the bytes of the low
  halfword (`rev16_low58`), so an `x` of at least 16 bits gives a result of at most 16;
* `MADDW`, `MSUBW a x y` (`lo_maddw58`): the low `c ≤ 32` bits of the low word's `a ± x · y` read
  only the low `c` bits of the arguments;
* the boolean operands (`bin`, `binK`, `sh`, `ubfiz`, `csinc`): a boolean's register is its
  machine word on all 64 bits (G51c's `reg_bool51c`, `lo_op2_51c`);
* `STLRW`, `STLRB` of a wider source (`g58_stlr`): Phase 1's generic store of the fitted operand
  (`fitPiece` truncates an integer, `retypeL`) writes the bytes of `Arm64.storeBytes` of the
  source, or `poison` bytes for a pointer (`encode_fit58`), which G32's store argument relates;
* `LoweredRound32F`, `LoweredRound64F x` (`g58_round`): `FOps.round` of the float read at its
  width is `x` itself (`round_id58`), in `x`'s `F` register; no code.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## `runLoc` -/

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `LoweredRound32F`, `LoweredRound64F`: `Arm64.evalPure` on the argument read from its home. -/
theorem stepLoc_round58 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64LoweredRound32F ∨ v.op = .ARM64LoweredRound64F)
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  rcases hop with hop | hop <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv) := by
      unfold evalOpL; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨argv, hm, rfl⟩

end Steps

/-! ## Words -/

section Words

private theorem low_le58 {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

/-- The low halfword of `REV16` on a word reads only the low halfword. -/
theorem rev16_low58 {a b : BitVec 32} (h : ∀ j, j < 16 → a.getLsbD j = b.getLsbD j) :
    (GoFV.SSA.Sem.Arm64.rev16 a).setWidth 16 = (GoFV.SSA.Sem.Arm64.rev16 b).setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    GoFV.SSA.Sem.Arm64.rev16, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  have hg : ∀ j (hj : j < 16), a[j]'(by omega) = b[j]'(by omega) := fun j hj => by
    have := h j hj
    simpa [BitVec.getLsbD_eq_getElem, show j < 32 by omega] using this
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp (config := { decide := true }) [hg, Nat.testBit]

private theorem sw_add58 {c : Nat} (hc : c ≤ 32) {x y X Y : BitVec 32}
    (hx : x.setWidth c = X.setWidth c) (hy : y.setWidth c = Y.setWidth c) :
    (x + y).setWidth c = (X + Y).setWidth c := by
  rw [BitVec.setWidth_add _ _ hc, BitVec.setWidth_add _ _ hc, hx, hy]

private theorem sw_mul58 {c : Nat} (hc : c ≤ 32) {x y X Y : BitVec 32}
    (hx : x.setWidth c = X.setWidth c) (hy : y.setWidth c = Y.setWidth c) :
    (x * y).setWidth c = (X * Y).setWidth c := by
  rw [BitVec.setWidth_mul _ _ hc, BitVec.setWidth_mul _ _ hc, hx, hy]

private theorem sw_sub58 {c : Nat} (hc : c ≤ 32) {x y X Y : BitVec 32}
    (hx : x.setWidth c = X.setWidth c) (hy : y.setWidth c = Y.setWidth c) :
    (x - y).setWidth c = (X - Y).setWidth c := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]
  refine sw_add58 hc hx ?_
  rw [BitVec.neg_eq_neg_one_mul y, BitVec.neg_eq_neg_one_mul Y, BitVec.setWidth_mul _ _ hc,
    BitVec.setWidth_mul _ _ hc, hy]

/-- The bytes of the low `n` bytes of a number are its first `n` bytes. -/
theorem intBytes_mod58 (n x : Nat) : intBytes n (x % 2 ^ (8 * n)) = intBytes n x := by
  unfold intBytes
  rw [List.map_toArray, List.map_toArray]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · have : j + 8 * i < 8 * n := by omega
    simp [hj, this]
  · simp [hj]

end Words

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem res_int58 {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

/-- The `W` register of an argument of class at least `c ≤ 32` agrees with the machine word on
the low `c` bits. -/
private theorem reg32_low58 (hA : AddrAgree ι) {x : Val} {X : BitVec 64} {a : BitVec 32}
    {cx c : Nat} (hx : ValRel ι x X) (hfx : Fits cx x) (hc : c ≤ 32) (hcx : c ≤ cx)
    (hr : Arm64.reg32 x = some a) : a.setWidth c = (X.setWidth 32).setWidth c := by
  unfold Arm64.reg32 at hr
  cases hr' : Arm64.reg x with
  | none => rw [hr'] at hr; cases hr
  | some b =>
    rw [hr'] at hr
    cases hr
    rw [BitVec.setWidth_setWidth_of_le _ hc, BitVec.setWidth_setWidth_of_le _ hc]
    exact low_le58 (reg_low hA hx hfx hr') hcx

/-- `REV16W x` of an `x` of at least 16 bits: the machine's word (`unF37`) on the low `c ≤ 16`
bits. -/
theorem lo_rev16w58 (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {cx c : Nat}
    {x : Val} {X : BitVec 64} (hx : ValRel ι x X) (hfx : Fits cx x) (hcx : 16 ≤ cx) (hc : c ≤ 16)
    (ht : t ≠ .bool) :
    Lo ι c (Arm64.evalPure .ARM64REV16W t k aux [x]) (unF37 .REV16W X) := by
  show Lo ι c (Arm64.op1w t _ [x]) _
  simp only [Arm64.op1w]
  cases hrx : Arm64.reg32 x with
  | none => trivial
  | some a =>
    have ha := reg32_low58 hA hx hfx (by omega : 16 ≤ 32) hcx hrx
    show Lo ι c (Arm64.res t _) _
    rw [res_int58 ht]
    show ((GoFV.SSA.Sem.Arm64.rev16 a).setWidth 64).setWidth c =
      ((GoFV.SSA.Sem.Arm64.rev16 (X.setWidth 32)).setWidth 64).setWidth c
    have key := rev16_low58 (a := a) (b := X.setWidth 32) fun j hj => by
      have := congrArg (fun z => z.getLsbD j) ha
      simpa [BitVec.getLsbD_setWidth, hj, show j < 32 by omega] using this
    rw [BitVec.setWidth_setWidth_of_le _ (by omega : c ≤ 64),
      BitVec.setWidth_setWidth_of_le _ (by omega : c ≤ 64)]
    have := congrArg (BitVec.setWidth c) key
    simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

/-- `MADDW`, `MSUBW a x y` of arguments of classes at least the result's `c ≤ 32`: the machine's
word (`maddF37`) on the low `c` bits. -/
theorem lo_maddw58 (hA : AddrAgree ι) {op : Op} {t : Ty} {k : Int64} {aux : Option AuxRef}
    {as : As} {c ca cx cy : Nat} {a x y : Val} {A X Y : BitVec 64}
    (hop : madd37? op = some (as, true)) (ha : ValRel ι a A) (hx : ValRel ι x X)
    (hy : ValRel ι y Y) (hfa : Fits ca a) (hfx : Fits cx x) (hfy : Fits cy y) (hc : c ≤ 32)
    (hca : c ≤ ca) (hcx : c ≤ cx) (hcy : c ≤ cy) (ht : t ≠ .bool) :
    Lo ι c (Arm64.evalPure op t k aux [a, x, y]) (maddF37 as A Y X) := by
  rcases madd37?_some hop with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
  · cases h
  · cases h
  all_goals
    show Lo ι c (Arm64.op3w t _ [a, x, y]) _
    simp only [Arm64.op3w]
    cases hra : Arm64.reg32 a with
    | none => trivial
    | some a' =>
      cases hrx : Arm64.reg32 x with
      | none => trivial
      | some x' =>
        cases hry : Arm64.reg32 y with
        | none => trivial
        | some y' =>
          have h1 := reg32_low58 hA ha hfa hc hca hra
          have h2 := reg32_low58 hA hx hfx hc hcx hrx
          have h3 := reg32_low58 hA hy hfy hc hcy hry
          show Lo ι c (Arm64.res t _) _
          rw [res_int58 ht]
          show (_ : BitVec 64).setWidth c = (maddF37 _ A Y X).setWidth c
          simp only [maddF37]
          rw [BitVec.setWidth_setWidth_of_le _ (by omega : c ≤ 64),
            BitVec.setWidth_setWidth_of_le _ (by omega : c ≤ 64)]
          first
            | exact sw_add58 hc h1 (by rw [BitVec.mul_comm (Y.setWidth 32)]; exact sw_mul58 hc h2 h3)
            | exact sw_sub58 hc h1 (by rw [BitVec.mul_comm (Y.setWidth 32)]; exact sw_mul58 hc h2 h3)

/-- A unary op on the register of a boolean: its word function of the machine word. -/
theorem lo_op1B58 {t : Ty} {f : BitVec 64 → BitVec 64} {x : Val} {X : BitVec 64} {c : Nat}
    (hx : ValRel ι x X) (hfx : Fits 1 x) (ht : t ≠ .bool) : Lo ι c (Arm64.op1 t f [x]) (f X) := by
  simp only [Arm64.op1]
  cases hr : Arm64.reg x with
  | none => trivial
  | some a =>
    rw [reg_bool51c hx hfx hr]
    show Lo ι c (Arm64.res t (f X)) (f X)
    rw [res_int58 ht]
    show (f X).setWidth c = (f X).setWidth c
    rfl

/-- A register shift `x op y` by a boolean `y`: `x` of class `ca` at least the result's class `c`
for `LSL`, of 64 bits otherwise. -/
theorem lo_sh58 (hA : AddrAgree ι) {t : Ty} {as : As} {x y : Val} {X Y : BitVec 64}
    {c ca : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits 1 y)
    (hll : as = .LSL → c ≤ ca) (hr : as ≠ .LSL → ca = 64) (ht : t ≠ .bool) :
    Lo ι c (Arm64.op2 t (shF36 as) [x, y]) (shF36 as X Y) := by
  simp only [Arm64.op2]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      show Lo ι c (Arm64.res t (shF36 as a b)) _
      rw [res_int58 ht, reg_bool51c hy hfy hry]
      show (shF36 as a Y).setWidth c = (shF36 as X Y).setWidth c
      have hxa := reg_low hA hx hfx hrx
      by_cases hl : as = .LSL
      · subst hl
        exact shl_low (low_le58 hxa (hll rfl))
      · have hca := hr hl
        subst hca
        have ha : a = X := by simpa only [BitVec.setWidth_eq] using hxa
        rw [ha]

/-- A register value moved unchanged (`regVal`) of a boolean: the machine word. -/
private theorem lo_regValB58 {t : Ty} {x : Val} {X : BitVec 64} {c : Nat} (hx : ValRel ι x X)
    (hfx : Fits 1 x) (ht : t ≠ .bool) : Lo ι c (Arm64.regVal t x) X := by
  have he : Arm64.regVal t x = match Arm64.reg x with
      | some r => Arm64.res t r
      | none => .poison := by
    cases x with
    | ptr p => have h1 : (1 : Nat) = 64 := hfx; omega
    | _ => rfl
  rw [he]
  cases hr : Arm64.reg x with
  | none => trivial
  | some r =>
    rw [reg_bool51c hx hfx hr]
    show Lo ι c (Arm64.res t X) X
    rw [res_int58 ht]
    show X.setWidth c = X.setWidth c
    rfl

/-- `addP`'s result is `poison`, a pointer or a 64-bit word (G32's). -/
private theorem addP_shape58 {t : Ty} (ht : t ≠ .bool) (y : Val) (k : BitVec 64) :
    Arm64.addP t y k = .poison ∨ (∃ p, Arm64.addP t y k = .ptr p) ∨
      ∃ r, Arm64.addP t y k = .int .w64 r := by
  unfold Arm64.addP
  split
  · unfold PtrOps.ptrRes Ptr.word
    split <;> (try split) <;> (try split) <;> simp
  · split
    · rw [res_int58 ht]; simp
    · simp

/-- A `regVal` of an `addP` result: unchanged (G32's). -/
private theorem regVal_addP58 {t : Ty} (ht : t ≠ .bool) (y : Val) (k : BitVec 64) :
    Arm64.regVal t (Arm64.addP t y k) = Arm64.addP t y k := by
  rcases addP_shape58 ht y k with h | ⟨p, h⟩ | ⟨r, h⟩ <;> rw [h]
  · rfl
  · rfl
  · show Arm64.res t (r.setWidth 64) = _
    rw [res_int58 ht, BitVec.setWidth_eq]

/-- `CSINC [cc] x y f` on flags related to `NZCV`, of arguments of classes at least the result's
`c ≥ 8` or booleans: the machine's `CSINC` word (G32's `valRel_csinc`). -/
theorem valRel_csinc58 (hA : AddrAgree ι) {t : Ty} {k : Int64} {x y f : Val} {X Y : BitVec 64}
    {nz : Flags} {c ca cb : Nat} {cnd : Cond} (hcd : Cond.ofAux k = some cnd) (hf : FlagsRel f nz)
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (hc : cls t = some c) (h8 : 8 ≤ c) (hca : c ≤ ca ∨ ca = 1) (hcb : c ≤ cb ∨ cb = 1) :
    ValRel ι ((Arm64.csinc t k [x, y, f]).retypeL t) (if cnd.holds nz then X else Y + 1) := by
  have ht := cls_ne_bool hc h8
  apply valRel_retypeL_lo hA hc ht
  unfold Arm64.csinc Arm64.condOn
  rw [hcd]
  simp only [Option.bind_some]
  cases ho : cnd.onVal f with
  | none => trivial
  | some b =>
    rw [onVal_holds hf ho]
    cases b
    · rw [regVal_addP58 ht]
      rcases hcb with hcb | rfl
      · exact lo_addK hA hy hfy h8 hcb ht
      · exact lo_addK51c hA hy hfy (cls_le hc) ht
    · rcases hca with hca | rfl
      · exact lo_regVal hA hx hfx hca ht
      · exact lo_regValB58 hx hfx ht

/-- `Round32F`/`Round64F` of a float of its width is the float. -/
theorem round_id58 {w : Width} {x : Val} {q : BitVec 128} (hx : FValRel x q)
    (hf : Fits w.bits x) : Arm64.fop w FOps.round [x] = x := by
  cases x with
  | poison => cases w <;> rfl
  | int w' b =>
    have hw : w'.bits = w.bits := hf
    have he : w' = w := by cases w <;> cases w' <;> first | rfl | exact absurd hw (by decide)
    subst he
    cases w' <;> simp [Arm64.fop, Arm64.fval, FOps.round, int1, Val.asInt]
  | _ => exact hx.elim

end Vals

/-! ## The store-release of a wider source -/

/-- Phase 1's bytes of a store-release of `w` of a source of at least `w`'s bits: those of
`Arm64.storeBytes` of the source, or of `poison` (a pointer stored narrower). -/
theorem encode_fit58 {w : Width} {y : Val} {cs : Nat} (hf : Fits cs y) (hw : w.bits ≤ cs) :
    ∃ y', encode (.int w) (fitPiece (.int w) y) = Arm64.storeBytes w.bytes y' ∧
      (y' = y ∨ y' = .poison) := by
  cases y with
  | poison => exact ⟨.poison, by cases w <;> rfl, .inl rfl⟩
  | int w' x =>
    refine ⟨.int w' x, ?_, .inl rfl⟩
    have hw' : w'.bits = cs := hf
    by_cases he : w' = w
    · subst he
      exact encode_storeBytes (y := .int w' x) rfl
    · have hlt : w.bits < w'.bits := by
        cases w <;> cases w' <;> first | exact absurd rfl he | simp_all [Width.bits] <;> omega
      have hlt64 : x.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le x.isLt
        (Nat.pow_le_pow_right (by omega) (by cases w' <;> decide))
      cases w <;> cases w' <;> first
        | exact absurd rfl he
        | (simp only [Width.bits] at hlt; omega)
        | (simp (config := { decide := true }) only [fitPiece, Val.retypeL, Val.widen, Val.retype,
            encode, Arm64.storeBytes, Arm64.reg, Width.bytes, Width.bits, beq_iff_eq, reduceCtorEq,
            ↓reduceIte, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt64]
           first
            | exact intBytes_mod58 1 x.toNat
            | exact intBytes_mod58 2 x.toNat
            | exact intBytes_mod58 4 x.toNat
            | simp [intBytes_mod58])
  | ptr p =>
    have h64 : cs = 64 := hf
    cases w
    · exact ⟨.poison, rfl, .inr rfl⟩
    · exact ⟨.poison, rfl, .inr rfl⟩
    · exact ⟨.poison, rfl, .inr rfl⟩
    · exact ⟨.ptr p, rfl, .inl rfl⟩
  | bool b =>
    have h1 : cs = 1 := hf
    cases w <;> simp [Width.bits] at hw <;> omega
  | _ => exact False.elim hf

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `REV16W Rm, Rd`. -/
theorem g58_rev16w (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {cx c : Nat} {rm rd : Int} (hop : v.op = .ARM64REV16W) (hsz : v.args.size = 1)
    (hao : argObj lc v 0 = .ok (cx, rm)) (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c)
    (hc : c ≤ 16) (hcx : 16 ≤ cx)
    (hvs : OneAt2 psA j (.ofShape { as := .REV16W, from_ := regA rm, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧ XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp37 v.op := by unfold AluOp37; simp [hop]
  have hnp : v.op ≠ .Phi := (aluOp37_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu37 hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, hop]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht (lo_rev16w58 hA hxv hxf hcx hc ht))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨hpa, hf, -, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_un37 (.inr (.inr rfl)) hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf ht', wX_pc]
  rfl

/-- `MADDW`/`MSUBW Rm, Ra, Rn, Rd`. -/
theorem g58_maddw (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca cx cy c : Nat} {ra rm rn rd : Int}
    (hop : madd37? v.op = some (as, true)) (hsz : v.args.size = 3)
    (hao : argObj lc v 0 = .ok (ca, ra)) (hxo : argObj lc v 1 = .ok (cx, rm))
    (hyo : argObj lc v 2 = .ok (cy, rn)) (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c)
    (hc : c ≤ 32) (hca : c ≤ ca) (hcx : c ≤ cx) (hcy : c ≤ cy)
    (hvs : OneAt2 psA j ⟨maddOK as ra rm rn rd, as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧ XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp37_madd hop
  have hnp : v.op ≠ .Phi := (aluOp37_ne halu).1
  have has : as = .MADD ∨ as = .MSUB ∨ as = .MADDW ∨ as = .MSUBW := by
    rcases madd37?_some hop with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec hyo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨ka, hka, rfl, hkka⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor2
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨a, ha, hav, haf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkka
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu37 hl htemp halu hs
  rw [arr3 hsz ha0 ha1 ha2] at hargv
  obtain rfl := mapM_res_three hargv ha hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht (lo_maddw58 hA hop hav hxv hyv haf hxf hyf hc hca hcx hcy ht))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨hpa, hf, hr, ht', -, -, xr, hrest⟩ := maddOK_spec hok
  rw [progStep_madd37 has hka hkm hkn hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr hrest ht', wX_pc]
  rfl

/-- `op Rm, Rn, Rd` for a register op of G32 with a boolean argument. -/
theorem g58_bin (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca cb c : Nat} {rn rm rd : Int} (hop : bin32? v.op = some as)
    (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (ca, rn))
    (hbo : argObj lc v 1 = .ok (cb, rm)) (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c)
    (hca : c ≤ ca ∨ ca = 1) (hcb : c ≤ cb ∨ cb = 1)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧ XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp32_bin hop
  have hnp : v.op ≠ .Phi := (aluOp32_ne halu).1
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
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu32 hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv, evalPure_bin32 hop]
  have ht := cls_ne_bool hcv h8
  have hc64 := cls_le hcv
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht (lo_op2_51c hA hxv hyv hxf hyf hca hcb ht
      fun _ _ h1 h2 => binF_low as hc64 h1 h2))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_bin32 hop hkn hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `op $k, Rn, Rd` for a constant op of G32 of a boolean. -/
theorem g58_binK (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca c : Nat} {rn rd : Int} (hop : binK32? v.op = some as)
    (hsz : v.args.size = 1) (hao : argObj lc v 0 = .ok (ca, rn)) (hro : resObj lc v = .ok (c, rd))
    (h8 : 8 ≤ c) (hca : ca = 1)
    (hvs : OneAt2 psA j
      (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧ XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp32_binK hop
  have hnp : v.op ≠ .Phi := (aluOp32_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd hca
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu32 hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, evalPure_binK32 hop]
  have ht := cls_ne_bool hcv h8
  have him : Arm64.imm v.auxInt = BitVec.ofInt 64 v.auxInt.toInt := rfl
  rw [him]
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht (lo_op1B58 hxv hxf ht))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_binK32 hop hkn hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `LSL`/`LSR`/`ASR Rm, Rn, Rd` by a boolean. -/
theorem g58_sh (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca cb c : Nat} {rn rm rd : Int} (hop : sh36? v.op = some as)
    (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (ca, rn))
    (hbo : argObj lc v 1 = .ok (cb, rm)) (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c)
    (hcb : cb = 1) (hll : as = .LSL → c ≤ ca) (hrr : as ≠ .LSL → ca = 64)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧ XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp36_sh hop
  have hnp : v.op ≠ .Phi := (aluOp36_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd hcb
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu36 hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv, evalPure_sh36 hop]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht (lo_sh58 hA hxv hyv hxf hyf hll hrr ht))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_sh36 hop hkn hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `UBFIZ $lsb, Rn, $width, Rd` of a boolean. -/
theorem g58_ubfiz (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca c : Nat} {rn rd : Int}
    (hop : v.op = .ARM64UBFIZ) (hsz1 : v.args.size = 1) (hk0 : 0 ≤ v.auxInt.toInt)
    (hk16 : v.auxInt.toInt < 2 ^ 16) (hao : argObj lc v 0 = .ok (ca, rn))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : ca = 1)
    (hvs : OneAt2 psA j
      ⟨ubfizOK (v.auxInt.toInt / 256) (v.auxInt.toInt % 256) rn rd, "UBFIZ"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧ XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp33 v.op := by unfold AluOp33; simp [hop]
  have hnp : v.op ≠ .Phi := (aluOp33_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd hca
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu33 hl htemp halu hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, hop]
  have ht := cls_ne_bool hcv h8
  have hub : ∀ X : BitVec 64, GoFV.SSA.Sem.Arm64.ubfiz v.auxInt X =
      (X &&& Arm64.mask (v.auxInt.toInt % 256).toNat) <<< (v.auxInt.toInt / 256).toNat := by
    intro X
    have h1 : v.auxInt.toInt.toNat / 256 = (v.auxInt.toInt / 256).toNat := by omega
    have h2 : v.auxInt.toInt.toNat % 256 = (v.auxInt.toInt % 256).toNat := by omega
    show (X &&& Arm64.mask (v.auxInt.toInt.toNat % 256)) <<< (v.auxInt.toInt.toNat / 256) = _
    rw [h1, h2]
  have hlo : Lo E.ι c (Arm64.evalPure .ARM64UBFIZ (lc.ty v.id) v.auxInt v.aux [x])
      ((m.rX (BitVec.ofNat 5 kn) &&& Arm64.mask (v.auxInt.toInt % 256).toNat) <<<
        (v.auxInt.toInt / 256).toNat) := by
    rw [← hub]
    exact lo_op1B58 hxv hxf ht
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht hlo)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, hr, ht', -, -, xr, hrest⟩ := ubfizOK_spec hok
  rw [progStep_ubfiz hkn hkd (by omega) (by omega) (by omega) (nextAddr_pcAt F.nodup hk0') has hf
    hr ht' hrest, wX_pc]
  rfl

/-- `CSINC [cc] x y f` with boolean arguments: `CSINC cond, Rx, Ry, Rd`. -/
theorem g58_csinc (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {f : ID} {o : Op} {cc rn rm rd : Int} {ca cb c : Nat}
    (hop : v.op = .ARM64CSINC) (hsz : v.args.size = 3) (hfa : v.args[2]? = some f)
    (hfl : (lc.ty f).isFlags = true) (hhn : lc.home f = none) (ho : ccOp? v.auxInt = some o)
    (hco : (Cond.ofOp o).isSome = true) (hcc : ARM64.condBits o = some cc)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca ∨ ca = 1) (hcb : c ≤ cb ∨ cb = 1)
    (hvs : OneAt2 psA j ⟨csincOK cc rn rm rd, "CSINC"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧ XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨cnd, hcs⟩ := Option.isSome_iff_exists.1 hco
  have hcd := ccOp?_ofAux ho hcs
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, rfl, -⟩ := objOf?_some hor
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  have halu : AluOp32 v.op := by unfold AluOp32; simp [hop]
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu32 hl htemp halu hs
  rw [arr3 hsz ha0 ha1 hfa] at hargv
  obtain rfl := mapM_res_three hargv hx hy (read_flags hl hhn hfl)
  rw [write_reg hvh hcv, hop, isFlags_eq hfl]
  obtain ⟨hfr, -⟩ := flags_retypeL hm.flags
  obtain ⟨hrange, hcond⟩ := cset_cond hcs hcc
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_csinc58 hA hcd hfr hxv hyv hxf hyf hcv h8 hca hcb) (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, hr, ht, -, -, xr, hrest⟩ := csincOK_spec hok
  rw [progStep_csinc hkn hkm hkd (nextAddr_pcAt F.nodup hk) has hf hrange hr hrest ht, wX_pc]
  simp only [MState.holds, hcond]
  rfl

/-- `STLR{,W,B} Rs, (Rn)` of a source of at least the access's bits: G32's store with the
generic atomic store's bytes of the fitted source (`encode_fit58`). -/
theorem g58_stlr (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n ca cs : Nat} {rn rs : Int}
    (hop : stlr? v.op = some (as, n)) (hsz3 : v.args.size = 3) (hmt : memTy (lc.ty v.id) = true)
    (hhn : lc.home v.id = none) (haux : v.aux = none) (hk0 : v.auxInt.toInt = 0)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hso : argObj lc v 1 = .ok (cs, rs))
    (hma : memArg lc v 2 = .ok ()) (hca : ca = 64) (hcs : 8 * n ≤ cs)
    (hvs : OneAt2 psA j ⟨plain as (· == regA rs) (· == memA rn 0), as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, -, -, -, -, -⟩ := stlr_ne (lc := lc) hop
  have hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
    rcases stlr?_some hop with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hso
  obtain ⟨ks, hks, rfl, hkks⟩ := objOf?_some hor1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkks
  obtain ⟨w, x, y', p, mm', hwn, hx, hy', hpw, hw, rfl⟩ := stepLoc_stlr hl htemp hop
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hy] at hy'
  cases hy'
  have hxX : X = x := by rw [hx] at hX; cases hX; rfl
  subst hxX
  subst hca
  have hwc : w.bits ≤ cs := by
    have hb : w.bits = 8 * w.bytes := by cases w <;> rfl
    rw [hb, hwn]; exact hcs
  obtain ⟨z, hz, hzy⟩ := encode_fit58 hyf hwc
  have hzv : ValRel E.ι z (m.rX (BitVec.ofNat 5 ks)) := by
    rcases hzy with rfl | rfl
    · exact hyv
    · trivial
  have hzf : Fits cs z := by
    rcases hzy with rfl | rfl
    · exact hyf
    · trivial
  rw [hz, hwn] at hw
  obtain ⟨mm0, hmm0, hk0', hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  have hcs' : 8 * n ≤ cs ∨ cs = 1 := .inl hcs
  have hbs := (storeBytes_relN hA hn hzv hzf hcs').1
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have haddr : Arm64.addr X 0 = some p := addr_asPtrWord hpw
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < n) (Or.inl hcan)
  have hstep : ∀ k (hk : k < psA.toList.length),
      (Pat.mk (plain as (· == regA (REG_R0 + ks)) (· == memA (REG_R0 + kn) 0)) as.name).ok
        psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m with
          mem := writeMem m.mem (a + p.off) n
            (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))),
          pc := pcAt text psA.toList (k + 1) } := by
    intro k0 hk0 hok
    obtain ⟨has, hf, -, ht', hsc, -, -⟩ := plain_spec hok
    simp only [beq_iff_eq] at hf ht'
    have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
        { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].to =
        .ok (a + p.off, none) := by
      rw [ht', ctx_mem_reg hkn hsc]
      have h0 : BitVec.ofInt 64 0 = (0 : BitVec 64) := by decide
      show Except.ok (m.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0, none) = _
      rw [h0, haeq]
    rw [progStep_stlr hop hks (nextAddr_pcAt F.nodup hk0) has hf hma' hnil]
    rfl
  obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hk0' hn hpa hzv hzf hcs' hw
  have hsep' : SepAt osp E.ι (StkAt E) mm' := hsep0.write hk0' hw
  have hwf := write_wf hw (by rw [hbs]; omega)
  exact (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM' hk' hsep'
    (fun y hy => hout y fun j hj he => hsep0.not_mem hal hpa hy (by omega) (by omega))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) hstep).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩

/-- `LoweredRound32F`/`LoweredRound64F x` in `x`'s `F` register: no code. -/
theorem g58_round (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : Nat} {ra : Int}
    (hop : v.op = .ARM64LoweredRound32F ∧ c = 32 ∨ v.op = .ARM64LoweredRound64F ∧ c = 64)
    (hsz1 : v.args.size = 1) (hao : fargObj lc v 0 = .ok (c, ra)) (hro : fresObj lc v = .ok (c, ra))
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    LocMatch E s' b (i + 1) m ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  obtain ⟨a0, r0, ha0, hah0, hfo0, hft0, hca0⟩ := fargObj_spec hao
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨ka, hka, rfl, hka'⟩ := fobjOf?_some hfo0
  obtain ⟨kd, hkd, hkk, hkd'⟩ := fobjOf?_some hfo
  have hkk' : kd = ka := by omega
  subst hkk'
  have hr0 : r0 ≠ zeroReg := by have := (objV?_some hka').1; unfold zeroReg; omega
  obtain ⟨x, hx, hxv, hxf⟩ := arg_relV hl hm hinv hah0 hft0 hca0
    (kread_arg hR hnp ha0 hah0 hca0 hr0) hka'
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_round58 hl htemp
    (by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  have hev : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x] = x := by
    rcases hop with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · rw [h]; exact round_id58 (w := .w32) hxv hxf
    · rw [h]; exact round_id58 (w := .w64) hxv hxf
  rw [write_reg hvh hcv, hev]
  have hz := fvalRel_retypeL hxv hxf hft hcv
  have hzf := fits_retypeL hcv x
  have hlm := locMatch_setRegV hm hkd' hz (b' := b) (i' := i + 1)
  have hpc : E.pcOf b (i + 1) = m.pc := by rw [hj', hvs, ← hj, hm.pc]
  rw [hpc, wV_self_pc] at hlm
  exact ⟨hlm, (core_setReg hinv hzf).mono (knext_set hK hnp hvh hcv), hsi⟩

end Cases

/-! ## The table -/

/-- The register ops of G58's group A empty G35's table, keep the entries of the other
registers, or (the ops of `keepOps35`) keep the entries of the registers other than the home's. -/
theorem uStep35_58a {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hmem : v.op ∈ ops58a) :
    uStep35 lc L v = [] ∨ uStep35 lc L v = L.filter (fun e => regHome? lc v.id != some e.1) ∨
      uStep35 lc L v = L.filter (!(homeRegs lc v.id).contains ·.1) := by
  by_cases hk : v.op ∈ keepOps35
  · exact .inr (.inr (uStep35_keepOps hk))
  simp only [ops58a, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h <;>
    (try simp [keepOps35, h] at hk) <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

/-! ## One value -/

/-- One value of G58's group A: it runs its Prog (none for `LoweredRound*F`) and keeps the
activation (`G49Env`), the match and `G3Inv`; the upper-bit table after it holds given it held
before (`hL`). No run premise. -/
theorem vk58a_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hcf : checkFrame lc g = .ok ())
    (_hv : lc.ctx.f.value? id = some v) (hVK : VK58a lc v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  have hE2 := hE.env.env.env.env.env
  have hR := kread_of_reads hreads
  have hmem := ops58a_of (vk58a_op hVK)
  have hU : ∀ m', XW lc v m m' → UOKL m' (uStep35 lc L v) := fun m' hx => by
    rcases uStep35_58a (L := L) hmem with h | h | h <;> rw [h]
    · exact fun e he => by cases he
    · exact uokl_keep hL hx
    · exact uokl_xw hL hx
  have fin : ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp →
      SlotInv lc s' → XW lc v m m' →
      ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
        UOKL m' (uStep35 lc L v) := fun m' h1 h2 h3 h4 h5 =>
    ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, hU m' h5⟩
  cases hVK with
  | rev16w hop hsz hao hro h8 hc hcx =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g58_rev16w (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro h8 hc hcx hvs htemp hs
    exact fin m' h1 h2 h3 h4 h5
  | maddw hop hsz hao hxo hyo hro h8 hc hca hcx hcy =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g58_maddw (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hxo hyo hro h8 hc hca hcx hcy
      hvs htemp hs
    exact fin m' h1 h2 h3 h4 h5
  | bin hop hsz hao hbo hro h8 hca hcb =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g58_bin (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo hro h8 hca hcb hvs htemp hs
    exact fin m' h1 h2 h3 h4 h5
  | binK hop hsz hao hro h8 hca =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g58_binK (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro h8 hca hvs htemp hs
    exact fin m' h1 h2 h3 h4 h5
  | sh hop hsz hao hbo hro h8 hcb hll hrr =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g58_sh (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo hro h8 hcb hll hrr hvs
      htemp hs
    exact fin m' h1 h2 h3 h4 h5
  | ubfiz hop hsz hk0 hk16 hao hro h8 hca =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g58_ubfiz (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk16 hao hro h8 hca hvs
      htemp hs
    exact fin m' h1 h2 h3 h4 h5
  | csinc hop hsz hfa hfl hhn ho hco hcc hao hbo hro h8 hca hcb =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g58_csinc (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hfa hfl hhn ho hco hcc hao hbo
      hro h8 hca hcb hvs htemp hs
    exact fin m' h1 h2 h3 h4 h5
  | stlr _ hop hsz3 hmt hhn haux hk0 hao hso hma hca hcs =>
    have hsz := slot_sizes hE2.lcEq hcf hinv.slots
    obtain ⟨m', h1, h2, h3, h4⟩ := g58_stlr (H := H) F hE2.frame hsz hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz3 hmt hhn haux hk0 hao hso hma
      hca hcs hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    have h0 : uStep35 lc L v = [] := by
      rcases stlr?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31,
          keepOp31, keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]
    rw [h0]
    exact fun e he => by cases he
  | round hop hsz1 hao hro =>
    obtain ⟨r2, hvh, -, -, -⟩ := fresObj_spec hro
    have hj0 : j' = j := hvs
    obtain ⟨h2, h3, h4⟩ := g58_round F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz1 hao hro hj0 htemp hs
    exact fin m .refl h2 h3 h4 (.inl rfl)

end GoFV.Proof.Gen
