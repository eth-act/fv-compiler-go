import GoFV.Proof.Low.SimAtom

/-!
# Lowered loads and stores refine the generic ones (issue #385)

`ARM64.rules` lowers `(Load <t> ptr mem)` to `MOV{B,BU,H,HU,W,WU,D}load ptr mem` by the width and
signedness of `t`, and `(Store {t} ptr val mem)` to `MOV{B,H,W,D}store`/`FMOV{S,D}store ptr val
mem` by `t`'s size (offset 0, no aux). Here, for a value shape `ty` with a scalar layout
(`LoadFits`/`StoreFits`: a boolean of 1 byte, an integer of `w.bytes`, a pointer of 8 bytes):

* `ld_ref`: Phase 1's `Load` (`loadOp`, the memory decoded at `ty`) shaped by `retypeL` is
  refined by the arm64 load (`ldRes`, `Arm64.loadN`) shaped by `retypeL`. A narrow load's
  extension is cut by `retypeL`; a boolean byte other than 0/1 is `poison` in Phase 1 and its low
  bit in the load; a pointer-typed 8-byte load reads the same word (`decodeInt .w64 =
  decodePtr`). Loads are terms on both sides (`termVL`, `opValL`'s `ldVal`), so the load rules are
  `ArmRule.Sound` (`Rules/LoadStore.lean`; the size fit is the validator's `resFitsL`).
* `store_lower_eval`: Phase 1's `Store` (`memRoot`: the write of `encode ty val`) is refined by
  the arm64 store (`arm64Op`'s `st n`: the write of `Arm64.storeBytes n val`) whose address
  (`Sem.symAddr` at its offset and aux) is the `Store`'s (`AddrRef`; an `ADDconst` offset folded
  into it, `ARM64.rules:758-776`, or a global symbol's or frame variable's address, `881-905`):
  the stored bytes agree, or the generic ones are `poison` (`encode_le_storeBytes`).

A `Store {t}` of an aggregate shape (`StoreFits` excludes it: a size-1/2/4/8 struct, `[1]T` or
`complex64`) would not refine: `encode` writes the fields' bytes, `storeBytes` `poison`
(`Arm64.reg` of an aggregate is `none`).

Stores are atoms: the validator pairs them by `memLower` (`LowerCheck.atomPair`;
`memLower_cases`), and `GoFV.Proof.Low.atomPair_eval` relates every corresponding pair of atoms:
the same op, a renamed op (`SimAtom.lean`), or a lowered store (`store_lower_eval`).
-/

namespace GoFV.Proof.Low.Sim

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Proof.Low GoFV.Proof.AtomSim

/-! ## The lowered memory ops -/

/-- The plain arm64 stores `Store` lowers to, with their size. -/
inductive StOp : Op → Nat → Prop
  | b : StOp .ARM64MOVBstore 1
  | h : StOp .ARM64MOVHstore 2
  | w : StOp .ARM64MOVWstore 4
  | d : StOp .ARM64MOVDstore 8
  | fs : StOp .ARM64FMOVSstore 4
  | fd : StOp .ARM64FMOVDstore 8

/-- A scalar shape of `n` bytes a lowered load reads: a boolean (1), an integer or float
(`w.bytes`), a pointer (8). -/
def LoadFits (ty : Ty) (n : Nat) : Prop :=
  (ty = .bool ∧ n = 1) ∨ (∃ w, ty = .int w ∧ n = w.bytes) ∨ (∃ e, ty = .ptr e ∧ n = 8)

/-- A scalar shape of `n` bytes a lowered store writes. -/
def StoreFits (ty : Ty) (n : Nat) : Prop :=
  (ty = .bool ∧ n = 1) ∨ (∃ w, ty = .int w ∧ n = w.bytes) ∨ (∃ e, ty = .ptr e ∧ n = 8)

/-- What a lowered load at offset 0 without aux evaluates to. -/
def ldRes (ty : Ty) (n : Nat) (s : Bool) : List Val → Val
  | [a, .mem m] => (Arm64.addr a 0).elim .poison (Arm64.loadN ty n s m)
  | _ => .poison

theorem symAddr_none {ctx : Ctx} {w : Value} (hax : w.aux = none) (a : Val) :
    symAddr ctx w a = Arm64.addr a (BitVec.ofInt 64 w.auxInt.toInt) := by
  unfold symAddr; rw [hax]

/-- `Sem.symAddr` is the store address `addrAt` at the value's aux and offset. -/
theorem symAddr_eq_addrAt (ctx : Ctx) (w : Value) (a : Val) :
    symAddr ctx w a = addrAt ctx.tabs ctx.act w.aux w.auxInt a := by
  unfold symAddr addrAt; rfl

/-- A lowered store on an address, a value and a memory writes `storeBytes`. -/
theorem evalOpL_st {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} {ty : Ty} {n : Nat}
    (hst : StOp w.op n) {a x : Val} {m : Mem} {p : Ptr} (hp : symAddr ctx w a = some p) :
    ∃ what, evalOpL false env ctx fr w [a, x, .mem m] ty = writeRes what (Arm64.storeN n p x m) := by
  have h0 : nilFaults false ctx w [a, x, .mem m] = none := rfl
  generalize hop : w.op = o at hst
  cases hst <;>
  · refine ⟨s!"v{w.id}: {w.op.name}", ?_⟩
    unfold evalOpL
    rw [hop, if_neg (by decide)]
    dsimp only
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hop]
    dsimp only
    rw [hp]

/-! ## Loads -/

theorem width_ofSize_bytes (w : Width) : Width.ofSize? w.bytes = some w := by
  cases w <;> rfl

private theorem bytesNat?_frag {bs : Array Byte} {p : Ptr} (h : bs[0]? = some (.frag p 0)) :
    bytesNat? bs = none := by
  unfold bytesNat?
  rcases bs with ⟨l⟩
  cases l with
  | nil => simp at h
  | cons b l =>
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp

/-- An 8-byte load reads a word alike at an integer and at a pointer shape. -/
theorem decodeInt_w64_eq (bs : Array Byte) : decodeInt .w64 bs = decodePtr bs := by
  unfold decodeInt decodePtr
  cases hp : bytesPtr? bs with
  | none =>
    cases bytesNat? bs <;> rfl
  | some p =>
    have h0 : bs[0]? = some (.frag p 0) := by
      unfold bytesPtr? at hp
      split at hp
      · rename_i q hq
        split at hp
        · cases hp; exact hq
        · cases hp
      · cases hp
    rw [bytesNat?_frag h0]

private theorem zext_low {k : Nat} (hk : k ≤ 64) (x : BitVec k) : (x.setWidth 64).setWidth k = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, show i < 64 by omega, hi, decide_true, Bool.true_and]

private theorem sext_low_gen {k : Nat} (hk0 : 0 < k) (hk : k ≤ 64) (x : BitVec k) :
    (Arm64.sext k (x.setWidth 64)).setWidth k = x := by
  unfold Arm64.sext Arm64.mask
  rw [if_neg (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight]
  have h1 : 64 - k + i < 64 := by omega
  have h2 : 64 - k + i - (64 - k) = i := by omega
  simp only [h1, ite_true, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, BitVec.getLsbD_setWidth, h2, hi, show i < 64 by omega,
    show ¬ (64 ≤ i) by omega, show ¬ (64 - k + i < 64 - k) by omega, decide_true, decide_false,
    Bool.true_and, Bool.and_true, Bool.not_false, Bool.not_true]

private theorem low_bits_gen {k : Nat} (hk0 : 0 < k) (hk : k ≤ 64) (s : Bool) (x : BitVec k) :
    (if s then Arm64.sext k (x.setWidth 64) else x.setWidth 64).setWidth k = x := by
  cases s
  · exact zext_low hk x
  · exact sext_low_gen hk0 hk x

private theorem bool_bit (s : Bool) (x : BitVec 8) (hx : x.toNat ≤ 1) :
    (if s then Arm64.sext 8 (x.setWidth 64) else x.setWidth 64).getLsbD 0 = (x == 1) := by
  have h0 : (if s then Arm64.sext 8 (x.setWidth 64) else x.setWidth 64).getLsbD 0 = x.getLsbD 0 := by
    have := congrArg (fun y : BitVec 8 => y.getLsbD 0) (low_bits_gen (by decide) (by decide) s x)
    simpa [BitVec.getLsbD_setWidth] using this
  rw [h0]
  have : x = 0#8 ∨ x = 1#8 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with h | h
    · left; exact BitVec.eq_of_toNat_eq (by simp [h])
    · right; exact BitVec.eq_of_toNat_eq (by simp [h])
  rcases this with rfl | rfl <;> decide

theorem load_int_cases (m : Mem) (p : Ptr) {w : Width} (hw : w ≠ .w64) :
    m.load (.int w) p = .poison ∨ ∃ x, m.load (.int w) p = .int w x := by
  simp only [Mem.load]
  cases m.read p (Ty.int w).size with
  | none => exact .inl rfl
  | some bs =>
    simp only [decodeLoad, decode, decodeInt]
    cases bytesNat? (bs.extract 0 (0 + w.bytes)) with
    | some k => exact .inr ⟨_, rfl⟩
    | none => cases w <;> first | exact absurd rfl hw | exact .inl rfl

/-- The 8-byte arm64 load at a non-boolean shape is the 64-bit integer load. -/
theorem loadN_8 {ty : Ty} (hty : ty ≠ .bool) (s : Bool) (m : Mem) (p : Ptr) :
    Arm64.loadN ty 8 s m p = m.load (.int .w64) p := by
  simp only [Arm64.loadN]
  split
  · next x hx =>
    rw [hx]
    cases ty <;> first | exact absurd rfl hty | rfl
  · rfl

/-- A narrow arm64 load: the loaded bits extended to the register. -/
theorem loadN_narrow {w : Width} (hw : w ≠ .w64) (ty : Ty) (s : Bool) (m : Mem) (p : Ptr) :
    Arm64.loadN ty w.bytes s m p = match m.load (.int w) p with
      | .int _ x => Arm64.res ty (if s then Arm64.sext (8 * w.bytes) (x.setWidth 64) else x.setWidth 64)
      | _ => .poison := by
  cases w <;> first | exact absurd rfl hw | rfl

private theorem low_bits (w : Width) (hw : w ≠ .w64) (s : Bool) (x : BitVec w.bits) :
    (if s then Arm64.sext (8 * w.bytes) (x.setWidth 64) else x.setWidth 64).setWidth w.bits = x := by
  have hk : 8 * w.bytes = w.bits := by cases w <;> rfl
  rw [hk]
  exact low_bits_gen (by cases w <;> decide) (by cases w <;> decide) s x

/-- **The lowered load** at a fitting shape reads (`retypeL`) a refinement of the generic one. -/
theorem loadN_ref {ty : Ty} {n : Nat} (hfit : LoadFits ty n) (s : Bool) (m : Mem) (p : Ptr) :
    Sem.Refines ((m.load ty p).retypeL ty) ((Arm64.loadN ty n s m p).retypeL ty) := by
  rcases hfit with ⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
  · -- a boolean byte
    rw [show (1 : Nat) = Width.w8.bytes from rfl, loadN_narrow (w := .w8) (by decide)]
    have hb : m.load .bool p = (match m.read p 1 with
        | some bs => decode bs 0 .bool
        | none => .poison) := rfl
    have hi : m.load (.int .w8) p = (match m.read p 1 with
        | some bs => decodeInt .w8 (bs.extract 0 1)
        | none => .poison) := rfl
    rw [hb, hi]
    cases m.read p 1 with
    | none => exact .poison _
    | some bs =>
      dsimp only
      rcases bs with ⟨l⟩
      cases l with
      | nil => exact .poison _
      | cons b l =>
        cases b with
        | b x =>
          by_cases hx : x.toNat ≤ 1
          · have hd : decode (List.toArray (Byte.b x :: l)) 0 .bool = .bool (x == 1) := by
              simp [decode, hx]
            have he : (List.toArray (Byte.b x :: l)).extract 0 1 = #[.b x] := by simp
            have hn : decodeInt .w8 #[.b x] = .int .w8 x := by
              simp [decodeInt, bytesNat?]
            rw [hd, he, hn]
            show Sem.Refines (Val.bool (x == 1)) (Val.bool _)
            rw [show 8 * Width.w8.bytes = 8 from rfl, bool_bit s x hx]
            exact Sem.Refines.refl _
          · have hd : decode (List.toArray (Byte.b x :: l)) 0 .bool = .poison := by
              simp [decode, hx]
            rw [hd]; exact .poison _
        | _ => exact .poison _
  · by_cases hw : w = .w64
    · subst hw
      rw [show Width.w64.bytes = 8 from rfl, loadN_8 (ty := .int .w64) (by simp) s m p]
      exact Sem.Refines.refl _
    · rcases load_int_cases m p hw with h | ⟨x, h⟩
      · rw [h, retypeL_poison]; exact .poison _
      · rw [loadN_narrow hw, h]
        have h1 : (Val.int w x).retypeL (.int w) = .int w x := by
          have hw1 : Val.widen (.int w) (.int w x) = .int w x := by
            show (if w.bits < w.bits then Val.int w (x.setWidth w.bits) else Val.int w x) = _
            rw [if_neg (Nat.lt_irrefl _)]
          show (Val.widen (.int w) (.int w x)).retype (.int w) = _
          rw [hw1]
          show (if w.bits ≤ w.bits then Val.int w (x.setWidth w.bits) else .poison) = _
          rw [if_pos (Nat.le_refl _), BitVec.setWidth_eq]
        have h2 : (Arm64.res (.int w) (if s then Arm64.sext (8 * w.bytes) (x.setWidth 64)
            else x.setWidth 64)).retypeL (.int w) = .int w x := by
          have hle : w.bits ≤ 64 := by cases w <;> decide
          have hlt : ¬ (64 < w.bits) := by omega
          generalize hy : (if s then Arm64.sext (8 * w.bytes) (x.setWidth 64) else x.setWidth 64) = y
          have hw1 : Val.widen (.int w) (.int .w64 y) = .int .w64 y := by
            show (if Width.w64.bits < w.bits then Val.int w (y.setWidth w.bits)
              else Val.int .w64 y) = _
            rw [if_neg hlt]
          show (Val.widen (.int w) (.int .w64 y)).retype (.int w) = _
          rw [hw1]
          show (if w.bits ≤ Width.w64.bits then Val.int w (y.setWidth w.bits) else .poison) = _
          rw [if_pos hle, ← hy, low_bits w hw s x]
        dsimp only
        rw [h1, h2]
        exact Sem.Refines.refl _
  · rw [loadN_8 (ty := .ptr e) (by simp) s m p]
    have : m.load (.int .w64) p = m.load (.ptr e) p := by
      have h1 : m.load (.int .w64) p = (match m.read p 8 with
          | some bs => decodeInt .w64 (bs.extract 0 8)
          | none => .poison) := rfl
      have h2 : m.load (.ptr e) p = (match m.read p 8 with
          | some bs => decodePtr (bs.extract 0 8)
          | none => .poison) := rfl
      rw [h1, h2]
      cases m.read p 8 with
      | none => rfl
      | some bs => exact decodeInt_w64_eq _
    rw [this]
    exact Sem.Refines.refl _

/-- The lowered load on the same arguments reads a refinement of `loadOp`, both `retypeL`. -/
theorem ld_ref {ty : Ty} {n : Nat} (hfit : LoadFits ty n) (s : Bool) (argv : List Val) :
    Sem.Refines ((loadOp ty argv).retypeL ty) ((ldRes ty n s argv).retypeL ty) := by
  have hp0 : ∀ v, Sem.Refines (Val.poison.retypeL ty) v := fun v => by
    rw [retypeL_poison]; exact .poison _
  rcases argv with _ | ⟨a, _ | ⟨x, _ | ⟨y, l⟩⟩⟩
  · exact hp0 _
  · exact hp0 _
  · cases x with
    | mem m =>
      show Sem.Refines ((match a.asPtrWord with
        | some p => m.load ty p
        | none => .poison).retypeL ty) (((Arm64.addr a 0).elim .poison (Arm64.loadN ty n s m)).retypeL ty)
      cases hp : a.asPtrWord with
      | none => exact hp0 _
      | some p =>
        rw [addr_of_asPtrWord hp]
        exact loadN_ref hfit s m p
    | _ => exact hp0 _
  · cases x <;> exact hp0 _

/-! ## Stores -/

private theorem resRefines_trans {a b c : Res Val} (h1 : Res.Refines a b) (h2 : Res.Refines b c) :
    Res.Refines a c := by
  cases h1 with
  | ok h => cases h2 with | ok h' => exact .ok (h.trans h')
  | panic e hm => cases h2 with | panic e hm' => exact .panic e (hm.trans hm')
  | stuck msg => exact .stuck msg _

theorem storeBytes_size {n : Nat} (hn : n ≤ 8) (v : Val) : (Arm64.storeBytes n v).size = n := by
  unfold Arm64.storeBytes
  split
  · simp [ptrBytes]
  · split
    · next h => simpa using h
    · simp
  · split
    · rw [if_pos hn]; simp [intBytes]
    · simp

private theorem storeBytes_reg {n : Nat} {v : Val} (hp : ∀ p, v ≠ .ptr p) (hb : ∀ bs, v ≠ .blob bs) :
    Arm64.storeBytes n v = match Arm64.reg v with
      | some x => if n ≤ 8 then intBytes n x.toNat else Array.replicate n .poison
      | none => Array.replicate n .poison := by
  unfold Arm64.storeBytes
  split
  · exact absurd rfl (hp _)
  · exact absurd rfl (hb _)
  · rfl

/-- **The bytes a lowered store writes refine those a generic `Store {t}` writes**, at a scalar
shape of the store's size. -/
theorem encode_le_storeBytes {ty : Ty} {n : Nat} (hfit : StoreFits ty n) (x : Val) :
    BytesRefineA (encode ty x) (Arm64.storeBytes n x) := by
  have hn : n ≤ 8 := by
    rcases hfit with ⟨-, rfl⟩ | ⟨w, -, rfl⟩ | ⟨-, -, rfl⟩
    · decide
    · cases w <;> decide
    · decide
  have hsz : ty.size = n := by
    rcases hfit with ⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩ | ⟨e, rfl, rfl⟩ <;> rfl
  have hpois : encode ty x = Array.replicate ty.size .poison →
      BytesRefineA (encode ty x) (Arm64.storeBytes n x) := fun h => by
    rw [h]; exact BytesRefineA.replicate_poison _ (by rw [storeBytes_size hn, hsz])
  -- a blob is stored as its bytes in both
  by_cases hblob : ∃ bs, x = .blob bs
  · obtain ⟨bs, rfl⟩ := hblob
    have he : encode ty (.blob bs) = if bs.length == ty.size then bs.toArray
        else Array.replicate ty.size .poison := by
      rcases hfit with ⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      · rfl
      · cases w <;> rfl
      · rfl
    have hs : Arm64.storeBytes n (.blob bs) = if bs.length == n then bs.toArray
        else Array.replicate n .poison := by
      unfold Arm64.storeBytes; split <;> simp_all
    rw [he, hs, hsz]; exact BytesRefineA.refl _
  have hb : ∀ bs, x ≠ .blob bs := fun bs h => hblob ⟨bs, h⟩
  rcases hfit with ⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
  · -- a boolean
    cases x with
    | bool b =>
      rw [storeBytes_reg (fun _ h => by cases h) hb]
      rw [show Arm64.reg (.bool b) = some (if b then 1 else 0) from rfl]
      dsimp only
      rw [if_pos (by decide : 1 ≤ 8)]
      have he : intBytes 1 ((if b then 1 else 0 : BitVec 64).toNat) = encode .bool (.bool b) := by
        cases b <;> simp [intBytes, encode]
      rw [he]; exact BytesRefineA.refl _
    | blob bs => exact absurd rfl (hb bs)
    | int w y => exact hpois (by cases w <;> rfl)
    | _ => exact hpois rfl
  · -- an integer or float of its width
    cases x with
    | int w' y =>
      by_cases hww : w' = w
      · subst hww
        rw [storeBytes_reg (fun _ h => by cases h) hb]
        have he : encode (.int w') (.int w' y) = intBytes w'.bytes y.toNat := by
          simp [encode]
        rw [he]
        simp only [Arm64.reg, if_pos hn]
        have hlt : y.toNat < 2 ^ 64 := by
          have := y.isLt; cases w' <;> simp_all [Width.bits] <;> omega
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt]
        exact BytesRefineA.refl _
      · apply hpois
        have hne : (w' == w) = false := by simpa using hww
        simp [encode, hne, Ty.size]
    | ptr q =>
      by_cases hww : w = .w64
      · subst hww
        have he : encode (.int .w64) (.ptr q) = ptrBytes q := rfl
        rw [he]; exact BytesRefineA.refl _
      · exact hpois (by cases w <;> first | exact absurd rfl hww | rfl)
    | blob bs => exact absurd rfl (hb bs)
    | bool b => exact hpois (by cases w <;> rfl)
    | _ => exact hpois (by cases w <;> rfl)
  · -- a pointer word
    cases x with
    | ptr q => exact BytesRefineA.refl _
    | int w' y =>
      by_cases hww : w' = .w64
      · subst hww
        rw [storeBytes_reg (fun _ h => by cases h) hb]
        have he : encode (.ptr e) (.int .w64 y) = intBytes 8 y.toNat := rfl
        rw [he]
        simp only [Arm64.reg, if_pos hn]
        rw [BitVec.setWidth_eq]
        exact BytesRefineA.refl _
      · exact hpois (by cases w' <;> first | exact absurd rfl hww | rfl)
    | blob bs => exact absurd rfl (hb bs)
    | _ => exact hpois rfl

private theorem stuck_ite {c : Bool} {m1 m2 : String} (r : Res Val) :
    Res.Refines (if c then .stuck m1 else .stuck m2) r := by
  split <;> exact .stuck _ _

/-- The lowered store refines the generic `Store` on the same value and memory, its address
(`Sem.symAddr` at its offset and aux) holding the `Store`'s (`AddrRef`). -/
theorem st_ref {env : Env} {ctx ctx' : Ctx} {fr : Frame} {u w : Value} (hu : u.op = .Store)
    {n : Nat} (hst : StOp w.op n)
    (hfit : StoreFits (auxTy ctx.tabs u.aux) n) {ty : Ty} {a a' : Val}
    (ha : AddrRef ctx'.tabs ctx'.act w.aux w.auxInt a a') (rest : List Val) :
    Res.Refines (memRoot ctx u (a :: rest)) (evalOpL false env ctx' fr w (a' :: rest) ty) := by
  rcases rest with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · unfold memRoot; rw [hu]; exact stuck_ite _
  · unfold memRoot; rw [hu]; exact stuck_ite _
  · cases y with
    | mem m =>
      have hm : memRoot ctx u [a, x, .mem m] = match a.asPtrWord with
          | some p => writeRes s!"v{u.id}: {u.op.name}" (m.write p (encode (auxTy ctx.tabs u.aux) x))
          | none => .stuck s!"v{u.id}: {u.op.name}: undefined or ill-typed address" := by
        unfold memRoot; rw [hu]; rfl
      rw [hm]
      cases hp : a.asPtrWord with
      | none => exact .stuck _ _
      | some p =>
        obtain ⟨what, he⟩ := evalOpL_st (env := env) (ctx := ctx') (fr := fr) (ty := ty) (x := x)
          (m := m) hst (by rw [symAddr_eq_addrAt]; exact ha p hp)
        rw [he]
        dsimp only
        cases hw : m.write p (encode (auxTy ctx.tabs u.aux) x) with
        | none => exact .stuck _ _
        | some m1 =>
          obtain ⟨m2, hw', hm2⟩ := (Mem.Refines.refl m).write (encode_le_storeBytes hfit x) hw
          simp only [writeRes, Arm64.storeN, hw']
          exact .ok (.mem hm2)
    | _ => unfold memRoot; rw [hu]; exact stuck_ite _
  · cases x <;> cases y <;> (unfold memRoot; rw [hu]; exact stuck_ite _)

/-- **`Store` lowered to an arm64 store** (`ARM64.rules` `(Store {t} ptr val mem)`, its offset
folded, `758-776`, or a global symbol's or frame variable's address, `881-905`): on arguments
whose address holds the `Store`'s at the store's offset and aux (`AddrRef`) and whose value and
memory are refined, the arm64 store refines the generic one (both shaped), at a scalar shape of
the store's size. -/
theorem store_lower_eval {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame}
    {u w : Value} (hu : u.op = .Store) {n : Nat} (hst : StOp w.op n)
    (hfit : StoreFits (auxTy ctx.tabs u.aux) n) {ty : Ty} (lS : Bool) {argv argv' : List Val}
    (h : (argv = [] ∧ argv' = []) ∨ ∃ a a' r r', argv = a :: r ∧ argv' = a' :: r' ∧
      AddrRef ctx'.tabs ctx'.act w.aux w.auxInt a a' ∧ RefinesList r r') :
    Res.Refines ((evalOp env ctx fr u argv ty).bind fun r => .ok (rty lS ty r))
      ((evalOpL false env ctx' fr' w argv' ty).bind fun r => .ok (rty true ty r)) := by
  have hS : evalOp env ctx fr u argv ty = memRoot ctx u argv := by
    unfold evalOp; rw [hu]
  rw [hS]
  rcases h with ⟨rfl, rfl⟩ | ⟨a, a', r, r', rfl, rfl, ha, hr⟩
  · exact Res.Rel.bind (by unfold memRoot; rw [hu]; exact stuck_ite _)
      fun x y hxy => .ok (rty_le (fun _ => rfl) ty hxy)
  · exact Res.Rel.bind (resRefines_trans (memRoot_mono ctx u (.cons (Sem.Refines.refl a) hr))
      (st_ref hu hst hfit ha r')) fun x y hxy => .ok (rty_le (fun _ => rfl) ty hxy)

/-- `LoweredZero [n]` (and `LoweredZeroLoop`) zeroes `n` bytes at its address (`Arm64.zero`). -/
theorem evalOpL_zero {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} {argv : List Val} {ty : Ty}
    (hw : w.op = .ARM64LoweredZero ∨ w.op = .ARM64LoweredZeroLoop) :
    evalOpL false env ctx fr w argv ty = .ok (Arm64.zero w.auxInt argv) := by
  have h0 : nilFaults false ctx w argv = none := rfl
  rcases hw with hw | hw <;>
  · unfold evalOpL
    rw [hw, if_neg (by decide)]
    dsimp only
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hw]
    rfl

/-- **`Zero` lowered to `LoweredZero`** (`ARM64.rules:376-377`): on refined arguments, the
lowered zeroing refines the generic one (`memRoot`: `stuck` on an undefined address or an invalid
write, where `Arm64.zero` is `poison`). -/
theorem zero_lower_eval {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame} {u w : Value}
    (hu : u.op = .Zero) (hw : w.op = .ARM64LoweredZero ∨ w.op = .ARM64LoweredZeroLoop)
    (hai : u.auxInt = w.auxInt) {ty : Ty} {argv argv' : List Val} (h : RefinesList argv argv') :
    Res.Refines (evalOp env ctx fr u argv ty) (evalOpL false env ctx' fr' w argv' ty) := by
  have hS : evalOp env ctx fr u argv ty = memRoot ctx u argv := by
    unfold evalOp; rw [hu]
  rw [hS, evalOpL_zero hw]
  refine resRefines_trans (memRoot_mono ctx u h) ?_
  rcases argv' with _ | ⟨a, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · unfold memRoot; rw [hu]; exact stuck_ite _
  · unfold memRoot; rw [hu]; exact stuck_ite _
  · cases y with
    | mem m =>
      have hm : memRoot ctx u [a, .mem m] = match a.asPtrWord with
          | some p => writeRes s!"v{u.id}: {u.op.name}"
              (m.write p (Array.replicate u.auxInt.toInt.toNat (.b 0)))
          | none => .stuck s!"v{u.id}: {u.op.name}: undefined or ill-typed address" := by
        unfold memRoot; rw [hu]; rfl
      rw [hm]
      cases hp : a.asPtrWord with
      | none => exact .stuck _ _
      | some p =>
        dsimp only
        cases hwr : m.write p (Array.replicate u.auxInt.toInt.toNat (.b 0)) with
        | none => exact .stuck _ _
        | some m1 =>
          simp only [writeRes, Arm64.zero, addr_of_asPtrWord hp, ← hai, hwr]
          exact .ok (Sem.Refines.refl _)
    | _ => unfold memRoot; rw [hu]; exact stuck_ite _
  · cases a <;> cases y <;> (unfold memRoot; rw [hu]; exact stuck_ite _)

/-! ## `memLower` and `atomPair` -/

open GoFV.Opt.LowerCheck

theorem stSize_stOp {o : Op} {n : Nat} (h : stSize o = some n) : StOp o n := by
  unfold stSize at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first | exact .b | exact .h | exact .w | exact .d | exact .fs | exact .fd

theorem fitsB_store {ty : Ty} {n : Nat} (h : fitsB ty n = true) : StoreFits ty n := by
  unfold fitsB at h
  split at h <;> simp only [beq_iff_eq, reduceCtorEq] at h
  · exact .inl ⟨rfl, h⟩
  · exact .inr (.inl ⟨_, rfl, h⟩)
  · exact .inr (.inr ⟨_, rfl, h⟩)

/-- What `memLower` says. -/
theorem memLower_cases {tabs : Tables} {u w : Value} (h : memLower tabs u w = true) :
    offOK w.auxInt = true ∧ stAux tabs w.aux = true ∧ u.op = .Store ∧
      ∃ n, StOp w.op n ∧ StoreFits (auxTy tabs u.aux) n := by
  unfold memLower at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] at h
  obtain ⟨⟨⟨hai, hax⟩, hu⟩, n, hn, hf⟩ := h
  exact ⟨hai, hax, hu, n, stSize_stOp hn, fitsB_store hf⟩

theorem atomPair_spec {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true) :
    (((((u.op = w.op ∨ renameOp u.op w.op = true) ∧ u.auxInt = w.auxInt ∧ u.aux = w.aux) ∨
        memLower tabs u w = true ∨ zeroLower u w = true) ∧ u.args.size = w.args.size) ∨
        addrLower tabs u w = true ∨ pbLower u w = true) ∧
      u.type = w.type ∧ u.block = w.block ∧ u.id = w.id := by
  unfold atomPair at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, h2, h3, h4⟩
  rcases h1 with (⟨(⟨⟨h1, h6⟩, h7⟩ | h1) | h1, hs⟩ | h1) | h1
  · exact .inl ⟨.inl ⟨h1, h6, h7⟩, hs⟩
  · exact .inl ⟨.inr (.inl h1), hs⟩
  · exact .inl ⟨.inr (.inr h1), hs⟩
  · exact .inr (.inl h1)
  · exact .inr (.inr h1)

/-- A bounds panic with constant operands and the `PanicBounds` it lowers: no `Phi`s, both
roots. -/
theorem pbLower_ops {u w : Value} (h : pbLower u w = true) :
    u.op ≠ .Phi ∧ w.op ≠ .Phi ∧ isRoot w.op = isRoot u.op := by
  obtain ⟨hu, -, -, ks, hk, -⟩ := pbLower_cases h
  rcases pbKeep_cases hk with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩ <;> rw [hu, hw] <;> decide

/-- Corresponding atoms other than a lowered frame address or a bounds panic with constant
operands have as many arguments. -/
theorem atomPair_size {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true)
    (hn : addrLower tabs u w = false) (hb : pbLower u w = false) : u.args.size = w.args.size := by
  rcases (atomPair_spec h).1 with ⟨-, hs⟩ | ha | ha
  · exact hs
  · rw [hn] at ha; cases ha
  · rw [hb] at ha; cases ha

/-- A lowered store and the `Store` it lowers: no `Phi`s, both roots. -/
theorem memLower_ops {tabs : Tables} {u w : Value} (h : memLower tabs u w = true) :
    u.op ≠ .Phi ∧ w.op ≠ .Phi ∧ isRoot w.op = isRoot u.op := by
  obtain ⟨-, -, hu, n, hs, -⟩ := memLower_cases h
  generalize w.op = o at hs
  rw [hu]; cases hs <;> decide

/-- A lowered frame address and the `LocalAddr` it lowers: no `Phi`s, no roots. -/
theorem addrLower_ops {tabs : Tables} {u w : Value} (h : addrLower tabs u w = true) :
    u.op ≠ .Phi ∧ w.op ≠ .Phi ∧ isRoot w.op = isRoot u.op := by
  obtain ⟨hu, hw, -⟩ := addrLower_cases h
  rw [hu, hw]; decide

/-- A lowered `Zero` and the `Zero` it lowers: no `Phi`s; the `Zero` is a root, the lowered one
is not (`LoweredZero` has no memory type in the op table). -/
theorem zeroLower_ops {u w : Value} (h : zeroLower u w = true) :
    u.op ≠ .Phi ∧ w.op ≠ .Phi ∧ isRoot u.op = true ∧ isRoot w.op = false := by
  obtain ⟨hu, hw, -⟩ := zeroLower_cases h
  rw [hu]; rcases hw with hw | hw <;> rw [hw] <;> decide

/-- Corresponding atoms are both `Phi`s or neither. -/
theorem atomPair_phi {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true) :
    w.op = .Phi ↔ u.op = .Phi := by
  rcases (atomPair_spec h).1 with ⟨⟨h | h, -⟩ | h | h, -⟩ | h | h
  · rw [h]
  · rcases renameOp_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] <;> decide
  · obtain ⟨h1, h2, -⟩ := memLower_ops h
    exact ⟨fun h' => absurd h' h2, fun h' => absurd h' h1⟩
  · obtain ⟨h1, h2, -⟩ := zeroLower_ops h
    exact ⟨fun h' => absurd h' h2, fun h' => absurd h' h1⟩
  · obtain ⟨h1, h2, -⟩ := addrLower_ops h
    exact ⟨fun h' => absurd h' h2, fun h' => absurd h' h1⟩
  · obtain ⟨h1, h2, -⟩ := pbLower_ops h
    exact ⟨fun h' => absurd h' h2, fun h' => absurd h' h1⟩

/-- Corresponding atoms are both roots or neither, except a lowered `Zero` (`zeroLower`), which is
not a root where the `Zero` is. -/
theorem atomPair_isRoot {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true) :
    isRoot w.op = isRoot u.op ∨ zeroLower u w = true := by
  rcases (atomPair_spec h).1 with ⟨⟨h | h, -⟩ | h | h, -⟩ | h | h
  · exact .inl (by rw [h])
  · left
    rcases renameOp_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] <;> decide
  · exact .inl (memLower_ops h).2.2
  · exact .inr h
  · exact .inl (addrLower_ops h).2.2
  · exact .inl (pbLower_ops h).2.2

/-- An atom of `g` that is a root corresponds to a root of `f`. -/
theorem atomPair_root {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true)
    (hr : isRoot w.op = true) : isRoot u.op = true := by
  rcases atomPair_isRoot h with h' | h'
  · rw [← h']; exact hr
  · exact (zeroLower_ops h').2.2.1

theorem makeL_tabs (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).tabs = tabs := by
  unfold Ctx.makeL; split <;> rfl


end GoFV.Proof.Low.Sim

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Proof.AtomSim GoFV.Opt.LowerCheck Sim

/-- A pointer shaped in any mode is refined by its word shaped in lowered mode: at the word shapes
both are the word (`Val.retype`), at every other shape the pointer is `poison`. -/
theorem ptr_rty_word (P : Ptr) (lS : Bool) (t : Ty) :
    Sem.Refines (rty lS t (.ptr P)) (rty true t P.word) := by
  refine (rty_le (fun _ => rfl) t (Sem.Refines.refl _)).trans ?_
  show Sem.Refines (((Val.ptr P).widen t).retype t) ((P.word.widen t).retype t)
  cases t with
  | int w =>
    cases w
    · exact Sem.Refines.poison _
    · exact Sem.Refines.poison _
    · exact Sem.Refines.poison _
    · rw [GoFV.Proof.Low.Mono.widen_of_hasTy _ _ (Ptr.word_hasTy_i64 P), Ptr.word_retype_i64]
      exact Sem.Refines.refl _
  | ptr e =>
    rw [GoFV.Proof.Low.Mono.widen_of_hasTy _ _ (Ptr.word_hasTy_ptr P e), Ptr.word_retype_ptr]
    exact Sem.Refines.refl _
  | _ => exact Sem.Refines.poison _

/-- **A lowered frame address refines the `LocalAddr` it lowers** (`addrLower`): `LocalAddr {n}`
is the pointer to `n`'s frame block (`Sem.frameVal`); `MOVDaddr {n}` at offset 0 is that pointer's
word (`Sem.symAddr`, `ptrRes`: a frame block's offset 0 is in its window), whatever its argument. -/
theorem addr_lower_eval {tabs : Tables} {f g : Func} {env : Env} (hown : f.ownAux = g.ownAux)
    (hgl : g.lowered = true) {GS GT : Frame} {u w : Value} (ha : addrLower tabs u w = true)
    (hty : (Ctx.makeL tabs g).tys[w.id]?.getD .other = (Ctx.makeL tabs f).tys[u.id]?.getD .other)
    (hregS : ∀ a ∈ u.args, Reg GS a) (hregT : ∀ a ∈ w.args, Reg GT a) :
    Res.Refines (evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) GS u)
      (evalValueL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) GT w) := by
  obtain ⟨hu, hw, hai, hax, hn, hsz⟩ := addrLower_cases ha
  rw [evalValueL_of_regs hregS, evalValueL_of_regs hregT, hty]
  generalize (Ctx.makeL tabs f).tys[u.id]?.getD .other = ty
  cases hux : u.aux with
  | none => rw [hux] at hn; cases hn
  | some n =>
  have hgen : u.op.generic = true := by rw [hu]; decide
  rw [evalOpL_generic _ _ _ _ _ _ hgen, evalOp_localAddr hu, hux]
  obtain ⟨a, hwa⟩ : ∃ a, w.args = #[a] := by
    rcases hw' : w.args with ⟨l⟩
    rw [hw'] at hsz
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 (by simpa using hsz)
    exact ⟨a, rfl⟩
  rw [hwa]
  change Res.Refines (Res.bind (.ok _) _)
    (Res.bind (evalOpL false env (Ctx.makeL tabs g) GT w [rv GT a] ty) _)
  have hact : (Ctx.makeL tabs g).act = (Ctx.makeL tabs f).act := by rw [ctxL_eq hown]
  rw [evalOpL_movDaddr hw, symAddr_name (by rw [hax, hux]) (by rw [makeL_tabs, hax]; exact hn),
    hai, hact, makeL_tabs, makeL_tabs]
  have hoff : BitVec.ofInt 64 (0 : Int64).toInt = 0 := by decide
  rw [hoff]
  have hwin : ∀ act, (⟨frameBlk tabs act n, 0⟩ : Ptr).inWindow = true := fun act => by
    unfold frameBlk; split <;> rfl
  simp only [Option.elim, PtrOps.ptrRes, hwin, ite_true, Option.map_some, Option.getD_some]
  refine .ok ?_
  rw [hgl]
  exact ptr_rty_word _ _ _

/-- A plain arm64 store's size. -/
theorem stOp_stSize {o : Op} {n : Nat} (h : StOp o n) : (stSize o).isSome = true := by
  cases h <;> rfl

/-- The registers of a store's arguments: none, or the address related at the offset and aux
(`AddrRef`) and the others refined. -/
theorem stArgs_split {tabs : Tables} {act : Nat} {F G : ID → Val} {k : Int64}
    {ax : Option AuxRef} : ∀ {l l' : List ID}, l.length = l'.length →
    (∀ (i : Nat) a a', l[i]? = some a → l'[i]? = some a' →
      ArgRel tabs act (if i = 0 then some (k, ax) else none) (F a) (G a')) →
    (l.map F = [] ∧ l'.map G = []) ∨ ∃ a a' r r', l.map F = a :: r ∧ l'.map G = a' :: r' ∧
      AddrRef tabs act ax k a a' ∧ RefinesList r r'
  | [], [], _, _ => .inl ⟨rfl, rfl⟩
  | b :: l, b' :: l', hl, h => .inr ⟨F b, G b', l.map F, l'.map G, rfl, rfl,
      by simpa [ArgRel] using h 0 b b' rfl rfl,
      refinesList_idx (by simpa using hl) fun i a a' ha ha' => by
        simpa [ArgRel] using h (i + 1) a a' ha ha'⟩
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

/-- **Corresponding atoms evaluate to refinements.** An atom `w` of `g` (lowered) corresponding to
the atom `u` of `f` (`atomPair`, `u` generic, not a lowered frame address), in frames of one
activation whose argument registers are related (`ArgRel` of `stArg`: refined, or a lowered
store's address at its offset), at the same shape, evaluates in `g`'s mode to a refinement of `u`
in `f`'s mode. -/
theorem atomPair_eval {tabs : Tables} {f g : Func} {env : Env} (hE : env.Mono)
    (hown : f.ownAux = g.ownAux) (hl : f.lowered = true → g.lowered = true) (hgl : g.lowered = true)
    {GS GT : Frame} (hfr : GT = { GS with regs := GT.regs }) {u w : Value}
    (hp : atomPair tabs u w = true) (hn : addrLower tabs u w = false) (hb : pbLower u w = false)
    (hgen : u.op.generic = true)
    (hty : (Ctx.makeL tabs g).tys[w.id]?.getD .other = (Ctx.makeL tabs f).tys[u.id]?.getD .other)
    (hregS : ∀ a ∈ u.args, Reg GS a) (hregT : ∀ a ∈ w.args, Reg GT a)
    (hargs : ∀ i < u.args.size, ArgRel tabs (Ctx.makeL tabs g).act (stArg u w i)
      (rv GS u.args[i]!) (rv GT w.args[i]!)) :
    Res.Refines (evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) GS u)
      (evalValueL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) GT w) := by
  obtain ⟨hk', -, -, hid⟩ := atomPair_spec hp
  obtain ⟨hk, hsz⟩ := hk'.resolve_right (by rw [hn, hb]; decide)
  rw [evalValueL_of_regs hregS, evalValueL_of_regs hregT, hty]
  have hrel : ∀ (i : Nat) a a', u.args.toList[i]? = some a → w.args.toList[i]? = some a' →
      ArgRel tabs (Ctx.makeL tabs g).act (stArg u w i) (rv GS a) (rv GT a') :=
    fun i a a' ha ha' => by
    rw [Array.getElem?_toList] at ha ha'
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.1 ha
    obtain ⟨hi', rfl⟩ := Array.getElem?_eq_some_iff.1 ha'
    have := hargs i hi
    rwa [getElem!_pos u.args i hi, getElem!_pos w.args i hi'] at this
  generalize hty' : (Ctx.makeL tabs f).tys[u.id]?.getD .other = ty
  rcases hk with ⟨hop, hai, hax⟩ | hm | hz
  case inr.inr =>
    -- a lowered `Zero`
    obtain ⟨hu, hw, hai⟩ := zeroLower_cases hz
    have hwst : stSize w.op = none := by rcases hw with h | h <;> rw [h] <;> rfl
    have hlist : RefinesList (u.args.toList.map (rv GS)) (w.args.toList.map (rv GT)) :=
      refinesList_idx (by simp [hsz]) fun i a a' ha ha' => by
        have := hrel i a a' ha ha'
        rwa [stArg_none hwst] at this
    rw [evalOpL_generic _ _ _ _ _ _ hgen]
    exact Res.Rel.bind (zero_lower_eval hu hw hai hlist) fun x y hxy => .ok (rty_le hl ty hxy)
  case inr.inl =>
    -- a lowered store
    obtain ⟨-, -, hu, n, hst, hfit⟩ := memLower_cases hm
    rw [hgl, evalOpL_generic _ _ _ _ _ _ hgen]
    have hsp := stArgs_split (tabs := tabs) (act := (Ctx.makeL tabs g).act) (F := rv GS)
      (G := rv GT) (k := w.auxInt) (ax := w.aux) (l := u.args.toList) (l' := w.args.toList)
      (by simp [hsz]) fun i a a' ha ha' => by
        have := hrel i a a' ha ha'
        rwa [stArg_store hu (stOp_stSize hst)] at this
    refine store_lower_eval hu hst (by rw [makeL_tabs]; exact hfit) f.lowered ?_
    rw [makeL_tabs]; exact hsp
  have hwst : stSize w.op = none := by
    rcases hop with hop | hop
    · rw [← hop]; exact stSize_generic hgen
    · exact (renameOp_stSize hop).2
  have hlist : RefinesList (u.args.toList.map (rv GS)) (w.args.toList.map (rv GT)) :=
    refinesList_idx (by simp [hsz]) fun i a a' ha ha' => by
      have := hrel i a a' ha ha'
      rwa [stArg_none hwst] at this
  generalize u.args.toList.map (rv GS) = AS at hlist
  generalize w.args.toList.map (rv GT) = AT at hlist
  -- the source's op on the target's arguments, in the target's activation
  have hctx : Ctx.makeL tabs g =
      { (Ctx.makeL tabs f) with f := (Ctx.makeL tabs g).f, sched := (Ctx.makeL tabs g).sched, tys := (Ctx.makeL tabs g).tys } := by
    rw [makeL_f]; exact ctxL_eq (tabs := tabs) hown
  have hmono : Res.Refines (evalOp env (Ctx.makeL tabs f) GS u AS ty)
      (evalOp env (Ctx.makeL tabs g) GT { w with op := u.op } AT ty) := by
    have h1 := evalOp_mono env hE (Ctx.makeL tabs f) (Ctx.makeL tabs g) hctx GS GT (by rw [hfr])
      (by rw [hfr]) (by rw [hfr]) (by rw [hfr]) u ty hlist
    rwa [← evalOp_congr (ctx := Ctx.makeL tabs g) (ctx' := Ctx.makeL tabs g) (fr := GT) (v := u)
      (v' := { w with op := u.op }) rfl hax.symm hai.symm hid.symm rfl rfl rfl] at h1
  have hsrc : evalOpL false env (Ctx.makeL tabs f) GS u AS ty = evalOp env (Ctx.makeL tabs f) GS u AS ty :=
    evalOpL_generic _ _ _ _ _ _ hgen
  have hev : Res.Refines (evalOpL false env (Ctx.makeL tabs f) GS u AS ty)
      (evalOpL false env (Ctx.makeL tabs g) GT w AT ty) := by
    rw [hsrc]
    rcases hop with hop | hop
    · have hw : { w with op := u.op } = w := by rw [hop]
      rw [hw] at hmono
      rw [evalOpL_generic _ _ _ _ _ _ (hop ▸ hgen)]
      exact hmono
    · rcases evalOpL_rename (env := env) (ctx := Ctx.makeL tabs g) (fr := GT) (argv := AT) (ty := ty)
          hop with ⟨k, hk, he⟩ | ⟨-, he⟩ | ⟨-, msg, he⟩
      · rw [he]
        have ht : evalOp env (Ctx.makeL tabs g) GT { w with op := u.op } AT ty =
            callOp env (Ctx.makeL tabs g) { w with op := u.op } AT := evalOp_postCall hk
        rw [ht] at hmono
        have hfit := callOp_fit hE (Ctx.makeL tabs g) { w with op := u.op } (k := k) hk AT
        exact resRefines_trans hmono hfit
      · rw [he]; exact hmono
      · rw [he] at hmono; exact resRefines_trans hmono (.stuck msg _)
  exact Res.Rel.bind hev fun x y hxy => .ok (rty_le hl ty hxy)


/-! ### Bounds panics with constant operands (`pbLower`) -/

section
variable {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} {ty : Ty} {a : AuxDef}

/-- `LoweredPanicBoundsRC [kind] {c} x mem` panics as `PanicBounds [kind] x c mem`. -/
theorem evalOpL_pbRC (hw : w.op = .ARM64LoweredPanicBoundsRC)
    (ha : w.aux.bind ctx.tabs.aux? = some a) {c : Int} (hk : a.kind = .pbc c) (x m : Val) :
    evalOpL false env ctx fr w [x, m] ty = panicBounds w.auxInt [x, .i64 (BitVec.ofInt 64 c), m] := by
  have h0 : nilFaults false ctx w [x, m] = none := rfl
  have hg : Op.ARM64LoweredPanicBoundsRC.generic = false := by decide
  cases a; cases hk
  unfold evalOpL
  rw [hw]
  simp only [hg, Bool.false_eq_true, ite_false]
  unfold arm64Op
  rw [h0]
  dsimp only
  rw [hw, ha]

/-- `LoweredPanicBoundsCR [kind] {c} y mem` panics as `PanicBounds [kind] c y mem`. -/
theorem evalOpL_pbCR (hw : w.op = .ARM64LoweredPanicBoundsCR)
    (ha : w.aux.bind ctx.tabs.aux? = some a) {c : Int} (hk : a.kind = .pbc c) (y m : Val) :
    evalOpL false env ctx fr w [y, m] ty = panicBounds w.auxInt [.i64 (BitVec.ofInt 64 c), y, m] := by
  have h0 : nilFaults false ctx w [y, m] = none := rfl
  have hg : Op.ARM64LoweredPanicBoundsCR.generic = false := by decide
  cases a; cases hk
  unfold evalOpL
  rw [hw]
  simp only [hg, Bool.false_eq_true, ite_false]
  unfold arm64Op
  rw [h0]
  dsimp only
  rw [hw, ha]

/-- `LoweredPanicBoundsCC [kind] {cx cy} mem` panics as `PanicBounds [kind] cx cy mem`. -/
theorem evalOpL_pbCC (hw : w.op = .ARM64LoweredPanicBoundsCC)
    (ha : w.aux.bind ctx.tabs.aux? = some a) {cx cy : Int} (hk : a.kind = .pbcc cx cy) (m : Val) :
    evalOpL false env ctx fr w [m] ty =
      panicBounds w.auxInt [.i64 (BitVec.ofInt 64 cx), .i64 (BitVec.ofInt 64 cy), m] := by
  have h0 : nilFaults false ctx w [m] = none := rfl
  have hg : Op.ARM64LoweredPanicBoundsCC.generic = false := by decide
  cases a; cases hk
  unfold evalOpL
  rw [hw]
  simp only [hg, Bool.false_eq_true, ite_false]
  unfold arm64Op
  rw [h0]
  dsimp only
  rw [hw, ha]

end

/-- What `pbConsts` says. -/
theorem pbConsts_cases {tabs : Tables} {w : Value} {l : List (Nat × Int)} (h : pbConsts tabs w = some l) :
    ∃ a, w.aux.bind tabs.aux? = some a ∧
      ((w.op = .ARM64LoweredPanicBoundsRC ∧ ∃ k, a.kind = .pbc k ∧ l = [(1, k)]) ∨
       (w.op = .ARM64LoweredPanicBoundsCR ∧ ∃ k, a.kind = .pbc k ∧ l = [(0, k)]) ∨
       (w.op = .ARM64LoweredPanicBoundsCC ∧ ∃ kx ky, a.kind = .pbcc kx ky ∧ l = [(0, kx), (1, ky)])) := by
  unfold pbConsts at h
  split at h <;> simp_all
  exact ⟨_, _, ⟨rfl, rfl⟩, h.symm⟩

private theorem args3 {xs : Array ID} (h : xs.size = 3) : ∃ a0 a1 a2, xs = #[a0, a1, a2] := by
  rcases xs with ⟨l⟩
  match l, h with | [a0, a1, a2], _ => exact ⟨a0, a1, a2, rfl⟩

private theorem args2 {xs : Array ID} (h : xs.size = 2) : ∃ a0 a1, xs = #[a0, a1] := by
  rcases xs with ⟨l⟩
  match l, h with | [a0, a1], _ => exact ⟨a0, a1, rfl⟩

private theorem args1 {xs : Array ID} (h : xs.size = 1) : ∃ a0, xs = #[a0] := by
  rcases xs with ⟨l⟩
  match l, h with | [a0], _ => exact ⟨a0, rfl⟩

/-- **A bounds panic with constant operands refines the `PanicBounds` it lowers** (`pbLower`):
both panic with `panicBounds` at the same kind, the kept arguments refined (`argIx`) and the
dropped ones refined by the aux constants (`pbConsts`). -/
theorem pb_lower_eval {tabs : Tables} {f g : Func} {env : Env}
    (hl : f.lowered = true → g.lowered = true) (hgl : g.lowered = true)
    {GS GT : Frame} {u w : Value} (hb : pbLower u w = true)
    (hty : (Ctx.makeL tabs g).tys[w.id]?.getD .other = (Ctx.makeL tabs f).tys[u.id]?.getD .other)
    (hregS : ∀ a ∈ u.args, Reg GS a) (hregT : ∀ a ∈ w.args, Reg GT a)
    (hargs : ∀ i < w.args.size, Sem.Refines (rv GS u.args[argIx u w i]!) (rv GT w.args[i]!))
    {l : List (Nat × Int)} (hcs : pbConsts tabs w = some l)
    (hc : ∀ p ∈ l, Sem.Refines (rv GS u.args[p.1]!) (.i64 (BitVec.ofInt 64 p.2))) :
    Res.Refines (evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) GS u)
      (evalValueL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) GT w) := by
  obtain ⟨hu, h3, hai, ks, hks, hsz⟩ := pbLower_cases hb
  rw [evalValueL_of_regs hregS, evalValueL_of_regs hregT, hty]
  generalize (Ctx.makeL tabs f).tys[u.id]?.getD .other = ty
  have hsrc : evalOpL false env (Ctx.makeL tabs f) GS u (u.args.toList.map (rv GS)) ty =
      panicBounds w.auxInt (u.args.toList.map (rv GS)) := by
    rw [evalOpL_generic _ _ _ _ _ _ (by rw [hu]; decide), ← hai]
    simp only [evalOp, hu]
  have hix : ∀ i (hi : i < ks.length), argIx u w i = ks[i] := fun i hi => argIx_of_pb hb hks hi
  have htabs : (Ctx.makeL tabs g).tabs = tabs := makeL_tabs tabs g
  obtain ⟨a0, a1, a2, hua⟩ := args3 h3
  have hev : Res.Refines (evalOpL false env (Ctx.makeL tabs f) GS u (u.args.toList.map (rv GS)) ty)
      (evalOpL false env (Ctx.makeL tabs g) GT w (w.args.toList.map (rv GT)) ty) := by
    rw [hsrc]
    obtain ⟨a, hax, hcase⟩ := pbConsts_cases hcs
    rw [← htabs] at hax
    rcases hcase with ⟨hw, k, hk, rfl⟩ | ⟨hw, k, hk, rfl⟩ | ⟨hw, kx, ky, hk, rfl⟩
    · obtain rfl : ks = [0, 2] := by rw [hw] at hks; exact (Option.some.inj hks).symm
      obtain ⟨b0, b1, hwa⟩ := args2 hsz
      have e0 := hargs 0 (by rw [hwa]; simp)
      have e1 := hargs 1 (by rw [hwa]; simp)
      rw [hix 0 (by decide), hua, hwa] at e0
      rw [hix 1 (by decide), hua, hwa] at e1
      have e2 := hc (1, k) (by simp)
      rw [hua] at e2
      simp at e0 e1 e2
      rw [hwa, hua]
      simp only [List.toList_toArray, List.map_cons, List.map_nil]
      rw [evalOpL_pbRC hw hax hk]
      exact panicBounds_mono _ (.cons e0 (.cons e2 (.cons e1 .nil)))
    · obtain rfl : ks = [1, 2] := by rw [hw] at hks; exact (Option.some.inj hks).symm
      obtain ⟨b0, b1, hwa⟩ := args2 hsz
      have e0 := hargs 0 (by rw [hwa]; simp)
      have e1 := hargs 1 (by rw [hwa]; simp)
      rw [hix 0 (by decide), hua, hwa] at e0
      rw [hix 1 (by decide), hua, hwa] at e1
      have e2 := hc (0, k) (by simp)
      rw [hua] at e2
      simp at e0 e1 e2
      rw [hwa, hua]
      simp only [List.toList_toArray, List.map_cons, List.map_nil]
      rw [evalOpL_pbCR hw hax hk]
      exact panicBounds_mono _ (.cons e2 (.cons e0 (.cons e1 .nil)))
    · obtain rfl : ks = [2] := by rw [hw] at hks; exact (Option.some.inj hks).symm
      obtain ⟨b0, hwa⟩ := args1 hsz
      have e0 := hargs 0 (by rw [hwa]; simp)
      rw [hix 0 (by decide), hua, hwa] at e0
      have ex := hc (0, kx) (by simp)
      have ey := hc (1, ky) (by simp)
      rw [hua] at ex ey
      simp at e0 ex ey
      rw [hwa, hua]
      simp only [List.toList_toArray, List.map_cons, List.map_nil]
      rw [evalOpL_pbCC hw hax hk]
      exact panicBounds_mono _ (.cons ex (.cons ey (.cons e0 .nil)))
  exact Res.Rel.bind hev fun x y hxy => .ok (rty_le hl ty hxy)

end GoFV.Proof.Low
