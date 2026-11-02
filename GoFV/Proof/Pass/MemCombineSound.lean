import GoFV.Proof.Pass.MemCombineDesc

/-!
# memcombine: source descriptions are sound (issue #35)

`symOf_sound`: if the value of `x` (as a term, `den` at fuel `n`) is an integer `X`, the bytes of
its source description (`symOf … false false`) are `X`'s bytes and its loads are valid, at the values of
`den` at the same fuel (`Sound`). `symOf_step_sound`: for a description `symOp` produced (not an
opaque `x`), at the values one fuel lower, which the main induction reads at its hypothesis.

The ops are strict (an integer result has integer arguments of the op's width), and `Load`s
narrower than 8 bytes give an integer only from concrete bytes (`load_sound`).
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.MemCombine.Check GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim

/-- What a description says of the integer `X` at the values `V`: its bytes are `X`'s and its
loads are valid. -/
def Sound (V : ID → Val) (r : Desc) (w : Width) (X : BitVec w.bits) : Prop :=
  semL V r.1 = some (bytesOf w X) ∧ ∀ l ∈ r.2, LoadOK V l

theorem Sound.lift {V V' : ID → Val} (h : ∀ y, Sem.Refines (V y) (V' y)) {r : Desc} {w : Width}
    {X : BitVec w.bits} (hs : Sound V r w X) : Sound V' r w X :=
  ⟨semL_mono' (fun _ _ y _ => h y) hs.1, fun l hl => loadOK_mono h (hs.2 l hl)⟩

/-! ## Values -/

theorem intW_eq {t : Ty} {w : Width} (h : intW t = some w) : t = .int w := by
  unfold intW at h; split at h <;> cases h; rfl

theorem not_term_of' {D : ID → Option Value} {x : ID} {v : Value} (hv : D x = some v)
    (ht : ¬ termOp v.op = true) : ¬ IsTerm D x := fun ⟨w, hw, hw'⟩ => by
  rw [hv] at hw; cases hw; exact ht hw'

theorem poison_hasTy (t : Ty) : Val.poison.hasTy t = true := by
  cases t <;> rfl

/-- The value of a defined node has its type's shape. -/
theorem den_hasTy {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} (hT : Term.Typed D tabs ρ)
    {x : ID} {v : Value} (hD : D x = some v) : ∀ n, (den D tabs ρ n x).hasTy (tabs.ty v.type) = true
  | 0 => poison_hasTy _
  | n + 1 => by
    by_cases ht : termOp v.op = true
    · rw [den_succ_term hD ht]; exact Val.retype_hasTy _ _
    · rw [den_succ_atom (not_term_of' hD ht)]
      have h := hT x (not_term_of' hD ht) (by rw [hD]; rfl)
      simp only [shape, hD, Option.map_some, Option.getD_some] at h
      rw [← h]; exact Val.retype_hasTy _ _

/-- A value of an integer shape that `retype` makes an integer is an integer. -/
theorem int_of_retype {v : Val} {wa wt w : Width} {X : BitVec w.bits} (hv : v.hasTy (.int wa) = true)
    (h : v.retype (.int wt) = .int w X) : ∃ w0 Y, v = .int w0 Y := by
  cases v with
  | int w0 Y => exact ⟨w0, Y, rfl⟩
  | ptr p =>
    cases wa <;> simp [Val.hasTy] at hv
    cases wt <;> simp [Val.retype, hv] at h
  | poison => cases wt <;> cases h
  | _ => cases wt <;> cases h

theorem retype_int_int {w0 wt w : Width} {Y : BitVec w0.bits} {X : BitVec w.bits}
    (h : (Val.int w0 Y).retype (.int wt) = .int w X) :
    wt.bytes ≤ w0.bytes ∧ Val.int w X = .int wt (Y.setWidth wt.bits) := by
  have h' : (Val.int w0 Y).retype (.int wt) =
      if wt.bits ≤ w0.bits then .int wt (Y.setWidth wt.bits) else .poison := rfl
  rw [h'] at h
  split at h
  · rename_i hle
    refine ⟨?_, h.symm⟩
    have := width_bits_eq wt; have := width_bits_eq w0; omega
  · cases h

/-! ## Op inversions -/

theorem int1_cases (w : Width) (F : BitVec w.bits → Val) (a : Val) :
    (∃ A, a = .int w A ∧ Sem.int1 w F [a] = F A) ∨ Sem.int1 w F [a] = .poison := by
  cases h : a.asInt w with
  | none => right; simp only [Sem.int1, h]
  | some A => left; exact ⟨A, asInt_eq h, by simp only [Sem.int1, h]⟩

theorem int2_cases (w : Width) (F : BitVec w.bits → BitVec w.bits → Val) (a b : Val) :
    (∃ A B, a = .int w A ∧ b = .int w B ∧ Sem.int2 w F [a, b] = F A B) ∨
      Sem.int2 w F [a, b] = .poison := by
  cases ha : a.asInt w with
  | none => right; simp only [Sem.int2, ha]
  | some A =>
    cases hb : b.asInt w with
    | none => right; simp only [Sem.int2, ha, hb]
    | some B => left; exact ⟨A, B, asInt_eq ha, asInt_eq hb, by simp only [Sem.int2, ha, hb]⟩

theorem toNat_ofInt_small {c : _root_.Int} (h0 : 0 ≤ c) (h1 : c < 64) :
    (BitVec.ofInt 64 c).toNat = c.toNat := by
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (by omega)]

theorem shift_cases (w : Width) (b : Bool) (F : BitVec w.bits → Nat → BitVec w.bits) (a : Val)
    {S : BitVec 64} (hS : S.toNat < w.bits) :
    (∃ A, a = .int w A ∧ Shift.shift w .w64 b F [a, .int .w64 S] = .int w (F A S.toNat)) ∨
      Shift.shift w .w64 b F [a, .int .w64 S] = .poison := by
  cases ha : a.asInt w with
  | none => right; simp only [Shift.shift, ha]
  | some A =>
    left
    refine ⟨A, asInt_eq ha, ?_⟩
    simp only [Shift.shift, ha, Val.asInt_int]
    rw [if_neg (by simp; omega), Nat.min_eq_left (by omega)]

/-- A load that is not `poison` reads its memory through its pointer word. -/
theorem loadOp_inv {t : Ty} {a b : Val} (h : loadOp t [a, b] ≠ .poison) :
    ∃ Q M, a.asPtrWord = some Q ∧ b = .mem M ∧ loadOp t [a, b] = M.load t Q := by
  cases b <;> try exact (h rfl).elim
  rename_i M
  cases ha : a.asPtrWord with
  | none => exact (h (by simp only [loadOp, ha])).elim
  | some Q => exact ⟨Q, M, rfl, rfl, by simp only [loadOp, ha]⟩

theorem load_int (M : Mem) (wt : Width) (Q : Ptr) :
    M.load (.int wt) Q = match M.read Q wt.bytes with
      | some bs => decodeInt wt (bs.extract 0 (0 + wt.bytes))
      | none => .poison := rfl

theorem bytesNat?_concrete {bs : Array Byte} {k : Nat} (h : bytesNat? bs = some k) :
    ∃ xs : List (BitVec 8), bs.toList = xs.map .b := by
  rw [bytesNat?, ← Array.foldr_toList] at h
  generalize bs.toList = l at h ⊢
  induction l generalizing k with
  | nil => exact ⟨[], rfl⟩
  | cons x l ih =>
    rw [List.foldr_cons] at h
    split at h
    · rename_i y n hacc
      obtain ⟨xs, hxs⟩ := ih hacc
      exact ⟨y :: xs, by rw [hxs]; rfl⟩
    · cases h

/-- **A load narrower than 8 bytes** that is an integer read concrete bytes through its split
pointer, and the description's bytes are the integer's. -/
theorem load_sound {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}
    {n : Nat} {v : Value} {wt : Width} (hb8 : wt.bytes < 8)
    (hpt : ptrTyped tabs D (splitP tabs D 64 v.args[0]! none 0).1 = true) {w : Width}
    {X : BitVec w.bits}
    (hE : (loadOp (.int wt) [den D tabs ρ n v.args[0]!, den D tabs ρ n v.args[1]!]).retype (.int wt) =
      .int w X) :
    ∃ w0 Y, loadOp (.int wt) [den D tabs ρ n v.args[0]!, den D tabs ρ n v.args[1]!] = .int w0 Y ∧
      Sound (den D tabs ρ n)
        ((List.range wt.bytes).map fun (k : Nat) => .mb v.args[1]! (splitP tabs D 64 v.args[0]! none 0).1
          (splitP tabs D 64 v.args[0]! none 0).2.1 ((splitP tabs D 64 v.args[0]! none 0).2.2 + (k : _root_.Int)),
        [⟨v.args[0]!, v.args[1]!, (splitP tabs D 64 v.args[0]! none 0).1,
          (splitP tabs D 64 v.args[0]! none 0).2.1, (splitP tabs D 64 v.args[0]! none 0).2.2, wt.bytes⟩])
        w0 Y := by
  generalize hS : splitP tabs D 64 v.args[0]! none 0 = S at hpt ⊢
  obtain ⟨b, i, o⟩ := S
  dsimp only at hpt ⊢
  have hne : loadOp (.int wt) [den D tabs ρ n v.args[0]!, den D tabs ρ n v.args[1]!] ≠ .poison :=
    fun h => by rw [h, retype_poison] at hE; cases hE
  obtain ⟨Q, M, hpQ, hmM, hL⟩ := loadOp_inv hne
  rw [hL, load_int] at hE ⊢
  cases hr : M.read Q wt.bytes with
  | none => rw [hr] at hE; cases hE
  | some bs =>
    rw [hr] at hE
    dsimp only at hE ⊢
    have hsz := read_size hr
    have hex : bs.extract 0 (0 + wt.bytes) = bs := by
      rw [Nat.zero_add, ← hsz, Array.extract_size]
    rw [hex] at hE ⊢
    cases hn : bytesNat? bs with
    | none =>
      have : decodeInt wt bs = .poison := by
        unfold decodeInt; rw [hn]; dsimp only
        cases wt with
        | w64 => exact absurd hb8 (by decide)
        | _ => rfl
      rw [this, retype_poison] at hE; cases hE
    | some k =>
      obtain ⟨xs, hxs⟩ := bytesNat?_concrete hn
      have hlen : xs.length = wt.bytes := by
        have := congrArg List.length hxs
        simp only [Array.length_toList, List.length_map] at this
        omega
      obtain ⟨Y, hY, hYb⟩ := decodeInt_concrete hxs hlen
      refine ⟨wt, Y, hY, ?_, ?_⟩
      · obtain ⟨P, I, hbP, hI, hpq⟩ := splitP_sound (m := n) 64 n v.args[0]! none 0 (Nat.le_refl _)
          hS hpt hpQ rfl
        have hQ : ptrAt Q 0 0 = Q := by simp [ptrAt]
        rw [hQ] at hpq
        unfold bytesOf
        refine semL_map_range _ _ fun j hj => mb_sem hmM hbP hI (hpq ▸ hr) (by omega) (by omega) ?_
        rw [show (o + (j : _root_.Int) - o).toNat = j by omega, ← Array.getElem?_toList, hxs,
          List.getElem?_map, List.getElem?_eq_getElem (by omega), hYb j hj]
        rfl
      · intro l hl
        rw [List.mem_singleton] at hl
        subst hl
        obtain ⟨P, I, hbP, hI, hpq⟩ := splitP_sound (m := n) 64 n v.args[0]! none 0 (Nat.le_refl _)
          hS hpt hpQ rfl
        have hQ : ptrAt Q 0 0 = Q := by simp [ptrAt]
        rw [hQ] at hpq
        refine ⟨M, P, I, bs, hmM, hbP, hI, by rw [hpQ, hpq], hpq ▸ hr, fun x hx => ?_⟩
        rw [hxs] at hx
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        exact ⟨y, rfl⟩

/-! ## `symOf` by cases -/

theorem symOf_succ_spec {tabs : Tables} {D : ID → Option Value} {tgt wide : Bool} {N : Nat} {x : ID}
    {r : Desc} (h : symOf tabs D tgt wide (N + 1) x = some r) :
    ∃ v wt, D x = some v ∧ tabs.ty v.type = .int wt ∧
      ((∃ r', symOp tabs D tgt wide (symOf tabs D tgt wide N) v wt = some r' ∧ wt.bytes ≤ r'.1.length ∧
          keepB tgt (r'.1.take wt.bytes) (r'.1.drop wt.bytes) r'.2 = some r) ∨
        r = ((List.range wt.bytes).map (.vb x), [])) := by
  rw [symOf] at h
  cases hD : D x with
  | none => rw [hD] at h; cases h
  | some v =>
    rw [hD] at h
    dsimp only at h
    cases hw : intW (tabs.ty v.type) with
    | none => rw [hw] at h; cases h
    | some wt =>
      rw [hw] at h
      dsimp only at h
      refine ⟨v, wt, rfl, intW_eq hw, ?_⟩
      split at h
      · rename_i r' hr'
        cases h
        left
        cases ho : symOp tabs D tgt wide (symOf tabs D tgt wide N) v wt with
        | none => rw [ho] at hr'; cases hr'
        | some r'' =>
          rw [ho] at hr'
          simp only [Option.bind_some] at hr'
          split at hr'
          · exact ⟨r'', rfl, ‹_›, hr'⟩
          · cases hr'
      · cases h; exact .inr rfl

/-- A description has its value's type's bytes. -/
theorem symOf_shape {tabs : Tables} {D : ID → Option Value} {tgt wide : Bool} :
    ∀ {N : Nat} {x : ID} {r : Desc}, symOf tabs D tgt wide N x = some r →
      ∃ v wt, D x = some v ∧ tabs.ty v.type = .int wt ∧ r.1.length = wt.bytes
  | 0, _, _, h => by cases h
  | N + 1, x, r, h => by
    obtain ⟨v, wt, hD, hty, h | rfl⟩ := symOf_succ_spec h
    · obtain ⟨r', -, hle, hk⟩ := h
      obtain ⟨rfl, -⟩ := keepB_spec hk
      exact ⟨v, wt, hD, hty, by simp; omega⟩
    · exact ⟨v, wt, hD, hty, by simp⟩

/-! ## Soundness -/

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}

/-- **One op**: the description `symOp` gives of an integer result, from sound descriptions of
the arguments (`hrec`), at the arguments' values. -/
theorem symOp_sound (hT : Term.Typed D tabs ρ) {n : Nat} {rec : ID → Option Desc}
    (hrec : ∀ a r (w : Width) (X : BitVec w.bits), rec a = some r → den D tabs ρ n a = .int w X →
      Sound (den D tabs ρ n) r w X)
    (hsh : ∀ a r, rec a = some r → ∃ va wa, D a = some va ∧ tabs.ty va.type = .int wa)
    {v : Value} {wt : Width} {r : Desc} (h : symOp tabs D false false rec v wt = some r)
    {w : Width} {X : BitVec w.bits}
    (hE : (evalPure v.op (.int wt) v.auxInt v.aux (v.args.toList.map (den D tabs ρ n))).retype
      (.int wt) = .int w X) :
    ∃ w0 Y, evalPure v.op (.int wt) v.auxInt v.aux (v.args.toList.map (den D tabs ρ n)) =
      .int w0 Y ∧ Sound (den D tabs ρ n) r w0 Y := by
  have hpo : ∀ {e : Val}, e = .poison → e.retype (.int wt) = .int w X → False := fun he h => by
    rw [he, retype_poison] at h; cases h
  rcases symOp_cases h with ⟨w', hw, hsz, rfl⟩ | ⟨ho, hsz, hr⟩ | ⟨ho, hl⟩ |
    ⟨w1, w2, a, hw, hsz, ha, rfl⟩ | ⟨w1, w2, a, hw, hsz, ha, hk⟩ | ⟨w1, hw, hl⟩ | ⟨w1, hw, hl⟩ |
    ⟨w1, a, hw, hsz, ha, rfl⟩ | ⟨w1, hw, ho⟩
  · -- a constant
    rw [(constW_spec hw).2.2]
    exact ⟨w', _, rfl, semL_lits _ _ _, fun _ h => by cases h⟩
  · -- `Copy`
    rw [ho, args_one hsz] at hE ⊢
    change (den D tabs ρ n v.args[0]!).retype _ = _ at hE
    change ∃ w0 Y, den D tabs ρ n v.args[0]! = _ ∧ _
    obtain ⟨va, wa, hDa, htya⟩ := hsh _ _ hr
    have hty := den_hasTy hT hDa n
    rw [htya] at hty
    obtain ⟨w0, Y, hY⟩ := int_of_retype hty hE
    exact ⟨w0, Y, hY, hrec _ _ _ _ hr hY⟩
  · -- `Load`
    obtain ⟨hsz, hb8, hpt, rfl⟩ := symLoad_spec hl
    rw [ho, args_two hsz] at hE ⊢
    exact load_sound (hb8 rfl) hpt hE
  · -- `ZeroExt`
    obtain ⟨-, -, hle, hev⟩ := zextW_spec hw
    obtain ⟨hra, hla⟩ := symArg_spec ha
    rw [hev, args_one hsz] at hE ⊢
    rcases int1_cases w1 (fun x => .int w2 (x.setWidth w2.bits)) (den D tabs ρ n v.args[0]!) with
      ⟨A, hA, he⟩ | he
    · refine ⟨w2, _, he, ?_⟩
      obtain ⟨h1, h2⟩ := hrec _ _ _ _ hra hA
      exact ⟨by rw [bytesOf_zext A hle]; exact semL_append.2 ⟨_, _, h1, semL_zeros _ _, rfl⟩, h2⟩
    · exact (hpo he hE).elim
  · -- `Trunc`
    obtain ⟨-, -, hle, hev⟩ := truncW_spec hw
    obtain ⟨hra, hla⟩ := symArg_spec ha
    obtain ⟨rfl, -⟩ := keepB_spec hk
    rw [hev, args_one hsz] at hE ⊢
    rcases int1_cases w1 (fun x => .int w2 (x.setWidth w2.bits)) (den D tabs ρ n v.args[0]!) with
      ⟨A, hA, he⟩ | he
    · refine ⟨w2, _, he, ?_⟩
      obtain ⟨h1, h2⟩ := hrec _ _ _ _ hra hA
      exact ⟨by rw [bytesOf_trunc A hle]; exact (semL_take_drop _ h1).1, h2⟩
    · exact (hpo he hE).elim
  · -- `Lsh`
    obtain ⟨-, -, hev⟩ := lshW_spec hw
    obtain ⟨k, a, hsz, hk, ha, hkp⟩ := symLsh_spec hl
    obtain ⟨hra, hla⟩ := symArg_spec ha
    obtain ⟨rfl, -⟩ := keepB_spec hkp
    obtain ⟨c, hc, hc0, hck, hkw⟩ := shiftBytes_spec hk
    rw [hev, args_two hsz] at hE ⊢
    cases n with
    | zero => exact (hpo rfl hE).elim
    | succ n =>
    rw [den_const64 hc] at hE ⊢
    have hS : (BitVec.ofInt 64 c).toNat = 8 * k := by
      rw [toNat_ofInt_small hc0 (by have := bytes_le_eight w1; have := width_bits_eq w1; omega)]; omega
    rcases shift_cases w1 (v.auxInt == 1) (fun x n => x <<< n) (den D tabs ρ (n + 1) v.args[0]!)
      (S := BitVec.ofInt 64 c) (by omega) with ⟨A, hA, he⟩ | he
    · rw [hS] at he
      refine ⟨w1, _, he, ?_⟩
      obtain ⟨h1, h2⟩ := hrec _ _ _ _ hra hA
      have hkb : k ≤ w1.bytes := by have := width_bits_eq w1; omega
      exact ⟨by
        rw [bytesOf_shl A hkb]
        exact semL_append.2 ⟨_, _, semL_zeros _ _, (semL_take_drop _ h1).1, rfl⟩, h2⟩
    · exact (hpo he hE).elim
  · -- `Rsh…U`
    obtain ⟨-, -, hev⟩ := rshuW_spec hw
    obtain ⟨k, a, hsz, hk, ha, hkp⟩ := symRsh_spec hl
    obtain ⟨hra, hla⟩ := symArg_spec ha
    obtain ⟨rfl, -⟩ := keepB_spec hkp
    obtain ⟨c, hc, hc0, hck, hkw⟩ := shiftBytes_spec hk
    rw [hev, args_two hsz] at hE ⊢
    cases n with
    | zero => exact (hpo rfl hE).elim
    | succ n =>
    rw [den_const64 hc] at hE ⊢
    have hS : (BitVec.ofInt 64 c).toNat = 8 * k := by
      rw [toNat_ofInt_small hc0 (by have := bytes_le_eight w1; have := width_bits_eq w1; omega)]; omega
    rcases shift_cases w1 (v.auxInt == 1) (fun x n => x >>> n) (den D tabs ρ (n + 1) v.args[0]!)
      (S := BitVec.ofInt 64 c) (by omega) with ⟨A, hA, he⟩ | he
    · rw [hS] at he
      refine ⟨w1, _, he, ?_⟩
      obtain ⟨h1, h2⟩ := hrec _ _ _ _ hra hA
      have hkb : k ≤ w1.bytes := by have := width_bits_eq w1; omega
      exact ⟨by
        rw [bytesOf_ushr A hkb]
        exact semL_append.2 ⟨_, _, (semL_take_drop _ h1).2, semL_zeros _ _, rfl⟩, h2⟩
    · exact (hpo he hE).elim
  · -- `Bswap`
    obtain ⟨-, -, hev⟩ := bswapW_spec hw
    obtain ⟨hra, hla⟩ := symArg_spec ha
    rw [hev, args_one hsz] at hE ⊢
    rcases int1_cases w1 (fun x => .int w1 (BitVec.ofNat w1.bits (Int.bswapNat (w1.bits / 8) x.toNat)))
      (den D tabs ρ n v.args[0]!) with ⟨A, hA, he⟩ | he
    · refine ⟨w1, _, he, ?_⟩
      obtain ⟨h1, h2⟩ := hrec _ _ _ _ hra hA
      exact ⟨by rw [bytesOf_bswap A]; exact semL_reverse h1, h2⟩
    · exact (hpo he hE).elim
  · -- `Or`
    obtain ⟨-, -, hev⟩ := orW_spec hw
    obtain ⟨a, b, c, hsz, ha, hb, hc, rfl⟩ := symOr_spec ho
    obtain ⟨hra, -⟩ := symArg_spec ha
    obtain ⟨hrb, -⟩ := symArg_spec hb
    rw [hev, args_two hsz] at hE ⊢
    rcases int2_cases w1 (fun x y => .int w1 (x ||| y)) (den D tabs ρ n v.args[0]!)
      (den D tabs ρ n v.args[1]!) with ⟨A, B, hA, hB, he⟩ | he
    · refine ⟨w1, _, he, ?_⟩
      obtain ⟨h1, h2⟩ := hrec _ _ _ _ hra hA
      obtain ⟨h3, h4⟩ := hrec _ _ _ _ hrb hB
      refine ⟨by rw [bytesOf_or]; exact orBytes_sem hc h1 h3, fun l hl => ?_⟩
      rcases List.mem_append.1 hl with hl | hl
      · exact h2 l hl
      · exact h4 l hl
    · exact (hpo he hE).elim

/-- The values at a lower fuel refine those at a higher one. -/
theorem den_lift (n m : Nat) (h : n ≤ m) : ∀ y, Sem.Refines (den D tabs ρ n y) (den D tabs ρ m y) :=
  fun y => den_fuel_mono D tabs ρ n m y h

/-- **Soundness of the source's descriptions**: an integer value has the bytes of its
description, whose loads are valid, at the values of the same fuel. -/
theorem symOf_sound (hT : Term.Typed D tabs ρ) : ∀ (N n : Nat) (x : ID) (r : Desc) (w : Width)
    (X : BitVec w.bits), symOf tabs D false false N x = some r → den D tabs ρ n x = .int w X →
    Sound (den D tabs ρ n) r w X
  | 0, _, _, _, _, _, h, _ => by cases h
  | N + 1, n, x, r, w, X, h, hx => by
    obtain ⟨v, wt, hD, hty, hc | rfl⟩ := symOf_succ_spec h
    · obtain ⟨r', ho, hle, hk⟩ := hc
      obtain ⟨rfl, -⟩ := keepB_spec hk
      obtain ⟨ht, hfr⟩ := symOp_term ho
      cases n with
      | zero => cases hx
      | succ n =>
      rw [den_term hD ht hfr, hty] at hx
      obtain ⟨w0, Y, hY, hs⟩ := symOp_sound hT (n := n)
        (fun a r w X hr hv => symOf_sound hT N n a r w X hr hv)
        (fun a r hr => by obtain ⟨va, wa, h1, h2, -⟩ := symOf_shape hr; exact ⟨va, wa, h1, h2⟩)
        ho hx
      rw [hY] at hx
      obtain ⟨hle', heq⟩ := retype_int_int hx
      cases heq
      have hs' := hs.lift (den_lift n (n + 1) (Nat.le_succ n))
      exact ⟨by rw [bytesOf_trunc Y hle']; exact (semL_take_drop _ hs'.1).1, hs'.2⟩
    · have hty' := den_hasTy hT hD n
      rw [hty, hx] at hty'
      simp only [Val.hasTy, beq_iff_eq] at hty'
      subst hty'
      refine ⟨?_, fun _ h => by cases h⟩
      unfold bytesOf
      exact semL_map_range _ _ fun k hk => by
        simp only [SB.sem, hx, byte?, hk, ite_true]

/-- **One step of soundness**: a description that `symOp` produced, without bytes of `x` itself,
has, for an integer value of `x`, its bytes and valid loads at the values one fuel lower. -/
theorem symOf_step_sound (hT : Term.Typed D tabs ρ) {N n : Nat} {x : ID} {r : Desc}
    (h : symOf tabs D false false (N + 1) x = some r) (hnx : ∀ s ∈ r.1, s.vbId? ≠ some x)
    {w : Width} {X : BitVec w.bits} (hx : den D tabs ρ (n + 1) x = .int w X) :
    Sound (den D tabs ρ n) r w X := by
  obtain ⟨v, wt, hD, hty, hc | rfl⟩ := symOf_succ_spec h
  · obtain ⟨r', ho, hle, hk⟩ := hc
    obtain ⟨rfl, -⟩ := keepB_spec hk
    obtain ⟨ht, hfr⟩ := symOp_term ho
    rw [den_term hD ht hfr, hty] at hx
    obtain ⟨w0, Y, hY, hs⟩ := symOp_sound hT (n := n)
      (fun a r w X hr hv => symOf_sound hT N n a r w X hr hv)
      (fun a r hr => by obtain ⟨va, wa, h1, h2, -⟩ := symOf_shape hr; exact ⟨va, wa, h1, h2⟩)
      ho hx
    rw [hY] at hx
    obtain ⟨hle', heq⟩ := retype_int_int hx
    cases heq
    exact ⟨by rw [bytesOf_trunc Y hle']; exact (semL_take_drop _ hs.1).1, hs.2⟩
  · exact (hnx (.vb x 0) (by simp [bytes_pos]) rfl).elim

end

end GoFV.Proof.MemCombine
