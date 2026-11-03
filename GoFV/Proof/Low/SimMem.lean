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
  the arm64 store (`arm64Op`'s `st n`: the write of `Arm64.storeBytes n val`): the stored bytes
  agree, or the generic ones are `poison` (`encode_le_storeBytes`).

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

theorem symAddr_zero {ctx : Ctx} {w : Value} (hax : w.aux = none) (hai : w.auxInt = 0) (a : Val) :
    symAddr ctx w a = Arm64.addr a 0 := by
  unfold symAddr; rw [hax, hai]; rfl

/-- A lowered store on an address, a value and a memory writes `storeBytes`. -/
theorem evalOpL_st {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} {ty : Ty} {n : Nat}
    (hst : StOp w.op n) (hax : w.aux = none) (hai : w.auxInt = 0) {a x : Val} {m : Mem} {p : Ptr}
    (hp : Arm64.addr a 0 = some p) :
    ∃ what, evalOpL false env ctx fr w [a, x, .mem m] ty = writeRes what (Arm64.storeN n p x m) := by
  have h0 : nilFaults false ctx w [a, x, .mem m] = none := rfl
  have hs := symAddr_zero (ctx := ctx) hax hai a
  rw [hp] at hs
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
    rw [hs]

/-! ## Addresses -/

theorem addr_of_asPtrWord {a : Val} {p : Ptr} (h : a.asPtrWord = some p) : Arm64.addr a 0 = some p := by
  cases a with
  | ptr q =>
    simp only [Val.asPtrWord, Option.some.injEq] at h
    subst h
    simp [Arm64.addr, Ptr.add]
  | int w x =>
    cases w <;> simp only [Val.asPtrWord, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    simp [Arm64.addr, Arm64.reg]
  | _ => simp [Val.asPtrWord] at h

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

/-- The lowered store on the same arguments refines the generic `Store`. -/
private theorem stuck_ite {c : Bool} {m1 m2 : String} (r : Res Val) :
    Res.Refines (if c then .stuck m1 else .stuck m2) r := by
  split <;> exact .stuck _ _

theorem st_ref {env : Env} {ctx ctx' : Ctx} {fr : Frame} {u w : Value} (hu : u.op = .Store)
    {n : Nat} (hst : StOp w.op n) (hax : w.aux = none) (hai : w.auxInt = 0)
    (hfit : StoreFits (auxTy ctx.tabs u.aux) n) {ty : Ty} (argv : List Val) :
    Res.Refines (memRoot ctx u argv) (evalOpL false env ctx' fr w argv ty) := by
  rcases argv with _ | ⟨a, _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩⟩
  · unfold memRoot; rw [hu]; exact stuck_ite _
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
          (m := m) hst hax hai (addr_of_asPtrWord hp)
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

/-- **`Store` lowered to an arm64 store** (`ARM64.rules` `(Store {t} ptr val mem)`, offset 0, no
aux): on refined arguments, the arm64 store refines the generic one (both shaped), at a scalar
shape of the store's size. -/
theorem store_lower_eval {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame}
    {u w : Value} (hu : u.op = .Store) {n : Nat} (hst : StOp w.op n) (hax : w.aux = none)
    (hai : w.auxInt = 0) (hfit : StoreFits (auxTy ctx.tabs u.aux) n) {ty : Ty} (lS : Bool)
    {argv argv' : List Val} (h : RefinesList argv argv') :
    Res.Refines ((evalOp env ctx fr u argv ty).bind fun r => .ok (rty lS ty r))
      ((evalOpL false env ctx' fr' w argv' ty).bind fun r => .ok (rty true ty r)) := by
  have hS : evalOp env ctx fr u argv ty = memRoot ctx u argv := by
    unfold evalOp; rw [hu]
  rw [hS]
  refine Res.Rel.bind (resRefines_trans (memRoot_mono ctx u h) (st_ref hu hst hax hai hfit argv'))
    fun x y hxy => .ok (rty_le (fun _ => rfl) ty hxy)

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
    w.auxInt = 0 ∧ w.aux = none ∧ u.op = .Store ∧ ∃ n, StOp w.op n ∧ StoreFits (auxTy tabs u.aux) n := by
  unfold memLower at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] at h
  obtain ⟨⟨⟨hai, hax⟩, hu⟩, n, hn, hf⟩ := h
  exact ⟨hai, hax, hu, n, stSize_stOp hn, fitsB_store hf⟩

theorem atomPair_spec {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true) :
    (((u.op = w.op ∨ renameOp u.op w.op = true) ∧ u.auxInt = w.auxInt ∧ u.aux = w.aux) ∨
        memLower tabs u w = true) ∧
      u.type = w.type ∧ u.args.size = w.args.size ∧ u.block = w.block ∧ u.id = w.id := by
  unfold atomPair at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, h2, h3, h4, h5⟩
  rcases h1 with ⟨⟨h1, h6⟩, h7⟩ | h1
  · exact .inl ⟨h1, h6, h7⟩
  · exact .inr h1

/-- A lowered store and the `Store` it lowers: no `Phi`s, both roots. -/
theorem memLower_ops {tabs : Tables} {u w : Value} (h : memLower tabs u w = true) :
    u.op ≠ .Phi ∧ w.op ≠ .Phi ∧ isRoot w.op = isRoot u.op := by
  obtain ⟨-, -, hu, n, hs, -⟩ := memLower_cases h
  generalize w.op = o at hs
  rw [hu]; cases hs <;> decide

/-- Corresponding atoms are both `Phi`s or neither. -/
theorem atomPair_phi {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true) :
    w.op = .Phi ↔ u.op = .Phi := by
  rcases (atomPair_spec h).1 with ⟨h | h, -⟩ | h
  · rw [h]
  · rcases renameOp_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] <;> decide
  · obtain ⟨h1, h2, -⟩ := memLower_ops h
    exact ⟨fun h' => absurd h' h2, fun h' => absurd h' h1⟩

/-- Corresponding atoms are both roots or neither. -/
theorem atomPair_isRoot {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true) :
    isRoot w.op = isRoot u.op := by
  rcases (atomPair_spec h).1 with ⟨h | h, -⟩ | h
  · rw [h]
  · rcases renameOp_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] <;> decide
  · exact (memLower_ops h).2.2

theorem makeL_tabs (tabs : Tables) (f : Func) : (Ctx.makeL tabs f).tabs = tabs := by
  unfold Ctx.makeL; split <;> rfl


end GoFV.Proof.Low.Sim

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Proof.AtomSim GoFV.Opt.LowerCheck Sim

/-- **Corresponding atoms evaluate to refinements.** An atom `w` of `g` (lowered) corresponding to
the atom `u` of `f` (`atomPair`, `u` generic), in frames of one activation whose argument registers
are refined, at the same shape, evaluates in `g`'s mode to a refinement of `u` in `f`'s mode. -/
theorem atomPair_eval {tabs : Tables} {f g : Func} {env : Env} (hE : env.Mono)
    (hown : f.ownAux = g.ownAux) (hl : f.lowered = true → g.lowered = true) (hgl : g.lowered = true)
    {GS GT : Frame} (hfr : GT = { GS with regs := GT.regs }) {u w : Value}
    (hp : atomPair tabs u w = true) (hgen : u.op.generic = true)
    (hty : (Ctx.makeL tabs g).tys[w.id]?.getD .other = (Ctx.makeL tabs f).tys[u.id]?.getD .other)
    (hregS : ∀ a ∈ u.args, Reg GS a) (hregT : ∀ a ∈ w.args, Reg GT a)
    (hargs : ∀ i < u.args.size, Sem.Refines (rv GS u.args[i]!) (rv GT w.args[i]!)) :
    Res.Refines (evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) GS u)
      (evalValueL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) GT w) := by
  obtain ⟨hk, -, hsz, -, hid⟩ := atomPair_spec hp
  rw [evalValueL_of_regs hregS, evalValueL_of_regs hregT, hty]
  have hlist : RefinesList (u.args.toList.map (rv GS)) (w.args.toList.map (rv GT)) := by
    refine refinesList_idx (by simp [hsz]) fun i a a' ha ha' => ?_
    rw [Array.getElem?_toList] at ha ha'
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.1 ha
    obtain ⟨hi', rfl⟩ := Array.getElem?_eq_some_iff.1 ha'
    have := hargs i hi
    rwa [getElem!_pos u.args i hi, getElem!_pos w.args i hi'] at this
  generalize hty' : (Ctx.makeL tabs f).tys[u.id]?.getD .other = ty
  rcases hk with ⟨hop, hai, hax⟩ | hm
  case inr =>
    -- a lowered store
    obtain ⟨hwai, hwax, hu, n, hst, hfit⟩ := memLower_cases hm
    rw [hgl, evalOpL_generic _ _ _ _ _ _ hgen]
    exact store_lower_eval hu hst hwax hwai (by rw [makeL_tabs]; exact hfit) f.lowered hlist
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
          hop with ⟨k, hk, he⟩ | ⟨-, he⟩
      · rw [he]
        have ht : evalOp env (Ctx.makeL tabs g) GT { w with op := u.op } AT ty =
            callOp env (Ctx.makeL tabs g) { w with op := u.op } AT := evalOp_postCall hk
        rw [ht] at hmono
        have hfit := callOp_fit hE (Ctx.makeL tabs g) { w with op := u.op } (k := k) hk AT
        exact resRefines_trans hmono hfit
      · rw [he]; exact hmono
  exact Res.Rel.bind hev fun x y hxy => .ok (rty_le hl ty hxy)

end GoFV.Proof.Low
