import GoFV.Proof.Gen.Spec66
import GoFV.Proof.Gen.G65

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G66: spills and reloads at slots of 1, 2 and 4 bytes (`docs/plans/slot-size.md`)

`stackalloc` homes a narrow value in a slot of its own type (`checkFrame`'s `homeFits`), so the
slot has the value's `n ∈ {1, 2, 4}` bytes (`narrowBytes`). `LocMatch` relates a slot's value to
those `n` bytes zero-extended as a register (`SlotRel` at the slot's shape), and `StkAt` holds each
slot's own bytes; nothing here changes the relation.

* A narrow spill (`VK66.nspill`) runs as G2's spill: `StoreReg` writes its argument, read at the
  value's shape, to its slot `k` (`stepLoc_move`). `MOVB`/`MOVH`/`MOVW Rs, off(RSP)` stores the
  register's low `n` bytes (`progStep_slotStoreN`); the value relates to them as a register
  (`valRel_lowN`: its low `8n` bits, or a boolean's 0/1). The other slots, the live blocks and
  the saved frame words lie outside the `n` written bytes (`g66_nspill`).
* A narrow reload (`VK66.nreload`): `loadByType`'s load (`MOV{B,H,W}` for a signed type, else
  `MOV{B,H,W}U`, `progStep_slotLoadN`) writes the slot's `n` bytes, sign- or zero-extended, to the
  `X` register; a value of class `8n` (or a boolean) is related to either extension as to the
  zero extension (`valRel_extN`) (`g66_nreload`).
* A `float32` spill or reload (`VK66.fspill`, `VK66.freload`): `FMOVS` stores or loads 4 bytes of
  the `V` register (`progStep_fstoreAt`, `progStep_floadAt`); a 32-bit value has no pointer form,
  so the reload needs no premise (`g66_fspill`, `g66_freload`).
* A narrow incoming stack argument (`VK66.narg`) is G62's `g62_arg`, at any class.

As `g2_spillW`/`g63_fspillW`, `g66_nspillW` and `g66_fspillW` take the relation on the machine
state with its memory replaced by one that agrees with it outside some bytes `W` (the entry
stores' pending windows, `GoFV/Proof/Obj/EntrySkip.lean`): both memories get the same write.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## Values and bytes -/

/-- Reading back the `k ≤ 8` bytes just written. -/
theorem readMem_writeMem_selfN (mm : Memory) (A : BitVec 64) {k : Nat} (hk : k ≤ 8)
    (V : BitVec (8 * k)) : readMem (writeMem mm A k V) A k = V := by
  apply BitVec.eq_of_toNat_eq
  have h256 : (2 : Nat) ^ (8 * k) = 256 ^ k := by rw [Nat.pow_mul]
  apply readMem_of_bytes _ k A V.toNat (by have := V.isLt; rwa [h256] at this)
  intro j hj
  rw [writeMem_at k mm A V j hj hk]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (8 * j) = 256 ^ j by rw [Nat.pow_mul], show 2 ^ 8 = 256 from rfl]

/-- The class of a shape is `8 ×` its bytes, or a boolean's 1 at one byte. -/
theorem cls_size {t : Ty} {c : Nat} (h : cls t = some c) : c = 8 * t.size ∨ (c = 1 ∧ t.size = 1) := by
  cases t with
  | int w =>
    simp only [GoFV.Gen.Check.cls, Option.some.injEq] at h
    subst h; left; cases w <;> rfl
  | bool => simp only [GoFV.Gen.Check.cls, Option.some.injEq] at h; subst h; right; exact ⟨rfl, rfl⟩
  | ptr _ => simp only [GoFV.Gen.Check.cls, Option.some.injEq] at h; subst h; left; rfl
  | _ => simp [GoFV.Gen.Check.cls] at h

/-- `narrowBytes` gives 1, 2 or 4 bytes, the type's size. -/
theorem narrowBytes_spec {lc : LocCtx} {t : TypeRef} {n : Nat} (h : narrowBytes lc t = some n) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  unfold narrowBytes at h
  split at h
  · split at h
    · cases h
    · split at h
      · split at h
        · cases h; simp_all <;> omega
        · cases h
      · cases h
  · cases h

/-- The low `k` bits of `V` written as `k` bits and zero-extended. -/
theorem low_setWidth (V : BitVec 64) {k : Nat} (hk : k ≤ 64) :
    ((BitVec.ofNat k (V.toNat % 2 ^ k)).setWidth 64).setWidth k = V.setWidth k := by
  apply BitVec.eq_of_toNat_eq
  have h1 : V.toNat % 2 ^ k < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.pow_le_pow_right (by omega) hk)
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt h1]

/-- A value of class `c` related to a register is related to the register's low `n` bytes
(`8n = c`, or a boolean's one byte), zero-extended. -/
theorem valRel_lowN {ι : Blk → Option (BitVec 64)} {n c : Nat} {y : Val} {V : BitVec 64}
    (hn : n = 1 ∨ n = 2 ∨ n = 4) (hc : c = 8 * n ∨ (c = 1 ∧ n = 1)) (hf : Fits c y)
    (h : ValRel ι y V) :
    ValRel ι y ((BitVec.ofNat (8 * n) (V.toNat % 2 ^ (8 * n))).setWidth 64) := by
  cases y with
  | poison => trivial
  | int w x =>
    simp only [Fits] at hf
    rcases hn with rfl | rfl | rfl <;> cases w <;> simp only [Width.bits] at hf <;>
      first
      | (exfalso; omega)
      | (simp only [ValRel] at h ⊢; rw [← h]; exact low_setWidth V (by decide))
  | bool b =>
    simp only [Fits] at hf
    obtain rfl : n = 1 := by omega
    simp only [ValRel] at h ⊢
    subst h
    cases b <;> first | rfl | decide
  | ptr p => simp only [Fits] at hf; omega
  | _ => exact absurd hf (by simp [Fits])

/-- The sign extension of the low `w` bits keeps them. -/
theorem sext_low {w : Nat} (hw : 0 < w ∧ w ≤ 64) (r : BitVec 64) :
    (Arm64.sext w r).setWidth w = r.setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  rw [sext_bit w hw r i (by omega)]
  simp [hi]

/-- A value of class `c` (`8n`, or a boolean at one byte) related to the zero extension of the
`n` bytes `Y` is related to their sign extension too. -/
theorem valRel_extN {ι : Blk → Option (BitVec 64)} {n c : Nat} {y : Val} {Y : BitVec (8 * n)}
    (hn : n = 1 ∨ n = 2 ∨ n = 4) (hc : c = 8 * n ∨ (c = 1 ∧ n = 1)) (hf : Fits c y)
    (h : ValRel ι y (Y.setWidth 64)) (sg : Bool) :
    ValRel ι y (if sg then ProgOp.sextTo64 n (Y.setWidth 64) else Y.setWidth 64) := by
  cases sg with
  | false => exact h
  | true =>
  simp only [↓reduceIte, ProgOp.sextTo64]
  cases y with
  | poison => trivial
  | int w x =>
    simp only [Fits] at hf
    rcases hn with rfl | rfl | rfl <;> cases w <;> simp only [Width.bits] at hf <;>
      first
      | (exfalso; omega)
      | (simp only [ValRel] at h ⊢; rw [← h]; exact sext_low ⟨by decide, by decide⟩ _)
  | bool b =>
    simp only [Fits] at hf
    obtain rfl : n = 1 := by omega
    simp only [ValRel] at h ⊢
    rw [h]
    cases b <;> first | rfl | decide
  | ptr p => simp only [Fits] at hf; omega
  | _ => exact absurd hf (by simp [Fits])

/-! ## A write of a slot's bytes -/

/-- **A store of a home slot's `n` bytes** (the slot's size): `LocMatch` holds of the state with
the slot set to `y` and the machine memory with `W` written at the slot, when `y` relates to `W`
zero-extended. The other slots, the live blocks (`SepFrom (StkAt E)`) and the saved frame words
lie outside the written bytes. -/
theorem slot_write_match {E : MatchEnv} {lc : LocCtx} {g : G2In} {L : Link} {s : LocState}
    {b : ID} {i : Nat} {m : MState} {K : Nat → Option Nat} {osp : Bool}
    (hF : FrameOK E) (hlc : E.lc = lc) (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k ∈ homeSlots lc, ∀ nc off, g.slotOp k = some (nc, off) →
      E.slot k = some (frameOff L nc off))
    (hext : 0 ≤ L.extrasize)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    {id : ID} {k : SlotKey} {o : Int} {n : Nat} {W : BitVec (8 * n)} {y : Val} {pc' : BitVec 64}
    (hh : lc.home id = some (.slot k)) (hsl : E.slot k = some o) (hkn : (lc.slotTy k).size = n)
    (hy : ValRel E.ι y (W.setWidth 64)) (hpc : pc' = E.pcOf b (i + 1)) :
    LocMatch E (s.setSlot lc.ctx.tabs k y) b (i + 1)
      { m with mem := writeMem m.mem (E.sp + BitVec.ofInt 64 o) n W, pc := pc' } := by
  have h8 : n ≤ 8 := hkn ▸ (home_slot_gen hcf hh).1
  obtain ⟨ho8, hohi⟩ := hF.slot k o hsl
  have hMout : ∀ y : BitVec 64, (∀ j, j < n → y ≠ E.sp + BitVec.ofInt 64 o + BitVec.ofNat 64 j) →
      writeMem m.mem (E.sp + BitVec.ofInt 64 o) n W y = m.mem y :=
    fun y hy => writeMem_other n _ _ _ y hy
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, -, hsep⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  refine ⟨hm.regs, hm.flags, ?_, ⟨mm, hmm, ?_⟩, ?_, hpc⟩
  · intro k' v' hk'
    rcases lookup_setSlot hk' with ⟨rfl, rfl⟩ | ⟨hne, hold⟩
    · refine ⟨o, hsl, ?_⟩
      unfold SlotRel
      rw [hlc, hkn, readMem_writeMem_selfN _ _ h8]
      exact hy
    · obtain ⟨o', ho', hsr⟩ := hm.slots k' v' hold
      refine ⟨o', ho', ?_⟩
      obtain ⟨-, i', hi'⟩ := hsi k' v' hold
      have hap := slot_apart hcf hslot hext (mem_homeSlots hh) (mem_homeSlots hi') (Ne.symm hne)
        hsl ho'
      rw [hkn] at hap
      unfold SlotRel at hsr ⊢
      rw [hlc] at hsr ⊢
      have h8' : (lc.slotTy k').size ≤ 8 := (home_slot_gen hcf hi').1
      rw [readMem_congr _ (E.sp + BitVec.ofInt 64 o')
        (fun j hj => hMout _ (fun j' hj' => slot_windows_apart hF hsl ho' hap (by omega) (by omega)
          hj' hj))]
      exact hsr
  · exact memInj_of_sepW hMI hsep.sepW fun y hy =>
      hMout y fun j hj he => hy (he ▸ stk_slot hF hsl (by omega) (by rw [hlc, hkn]; exact hj))
  · refine frameRel_mem hF hm.frame (fun _ j hj => ⟨hMout _ (fun j' hj' he => ?_),
      hMout _ (fun j' hj' he => ?_)⟩)
    · have := congrArg BitVec.toNat he
      rw [sp_toNat hF hj, win_toNat (by omega) hohi (by omega : j' < 8)] at this
      omega
    · have := congrArg BitVec.toNat he
      rw [spm8_toNat hF hj, win_toNat (by omega) hohi (by omega : j' < 8)] at this
      have := hF.lo
      omega

/-- The slot invariant after a store of `y` of the slot's class. -/
theorem slotInv_setSlot {lc : LocCtx} {g : G2In} {s : LocState} (hcf : checkFrame lc g = .ok ())
    (hsi : SlotInv lc s) {id : ID} {k : SlotKey} {y : Val} {c : Nat}
    (hh : lc.home id = some (.slot k)) (hc : cls (lc.ty id) = some c) (hy : Fits c y) :
    SlotInv lc (s.setSlot lc.ctx.tabs k y) := by
  intro k' v' hk'
  rcases lookup_setSlot hk' with ⟨rfl, rfl⟩ | ⟨-, hold⟩
  · exact ⟨by rw [slotCls_home hcf hh hc]; exact hy, id, hh⟩
  · exact hsi k' v' hold

/-- `movMem` of `storeByType`'s narrow stores. -/
theorem nstoreAs_movMem {n : Nat} (hn : n = 1 ∨ n = 2 ∨ n = 4) :
    ProgOp.movMem (nstoreAs n).name = some (n, true, false) := by
  rcases hn with rfl | rfl | rfl <;> rfl

/-- `movMem` of `loadByType`'s narrow loads. -/
theorem nloadAs_movMem {n : Nat} (hn : n = 1 ∨ n = 2 ∨ n = 4) (sg : Bool) :
    ProgOp.movMem (nloadAs n sg).name = some (n, sg, false) := by
  rcases hn with rfl | rfl | rfl <;> cases sg <;> rfl

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- **A narrow spill**: `MOVB`/`MOVH`/`MOVW Rs, off(RSP)` of the register's low `n` bytes, from a
relation on `m` with its memory replaced by `M0` (agreeing with `m.mem` outside `W`), as
`g2_spillW`: both memories get the same write. `g66_nspill` is the case `M0 = m.mem`. -/
theorem g66_nspillW (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hlc : E.lc = lc) (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k ∈ homeSlots lc, ∀ nc off, g.slotOp k = some (nc, off) →
      E.slot k = some (frameOff (Link.byId sym text az ez psA.toList) nc off))
    (hext : 0 ≤ (Link.byId sym text az ez psA.toList).extrasize) {M0 : Memory}
    (hm : LocMatch E s b i { m with mem := M0 }) (hinv : CoreInv E.ι (StkAt E) K s osp)
    (hsi : SlotInv lc s) (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {k : SlotKey} {nc : AddrName} {off : Int} {rs : Int} {n c : Nat}
    (hop : v.op = .StoreReg) (hn : narrowBytes lc v.type = some n)
    (hh : lc.home v.id = some (.slot k)) (hso : g.slotOp k = some (nc, off))
    (hsz1 : v.args.size = 1) (hts : (lc.ty v.id).size = n) (hao : argObj lc v 0 = .ok (c, rs))
    (hcv : cls (lc.ty v.id) = some c)
    (hvs : OneAt2 psA j ⟨plain (nstoreAs n) (· == regA rs) (slotA · nc off), "narrow spill"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s')
    {W : BitVec 64 → Prop} (hW : ∀ y, ¬ W y → M0 y = m.mem y) :
    ∃ m' M', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) { m' with mem := M' } ∧ CoreInv E.ι (StkAt E) K' s' osp ∧
      SlotInv lc s' ∧ m'.x = m.x ∧ ∀ y, ¬ W y → M' y = m'.mem y := by
  have hl := F.lowered
  have hA := F.addr
  have hn3 := narrowBytes_spec hn
  obtain ⟨a, r1, ha0, hah, hor1, hca⟩ := argObj_spec hao
  obtain ⟨ks, hks, rfl, hkk⟩ := objOf?_some hor1
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨x, hx, hxv, hxf⟩ := arg_rel hA hl hm hinv hah hca (kread_arg hR hnp ha0 hah hca) hkk
  obtain ⟨x', hx', rfl⟩ := stepLoc_move hl htemp (Or.inl hop) (arr1 hsz1 ha0) hs
  rw [hx] at hx'
  cases hx'
  rw [write_slot hh]
  obtain ⟨-, hsize, -, nc', off', hso', hnc⟩ := home_slot_gen hcf hh
  rw [hso] at hso'
  cases hso'
  have hkn : (lc.slotTy k).size = n := hsize.trans hts
  have hcn : c = 8 * n ∨ (c = 1 ∧ n = 1) := by have := cls_size hcv; rw [hts] at this; exact this
  have hsl := hslot k (mem_homeSlots hh) nc off hso
  generalize ho : frameOff (Link.byId sym text az ez psA.toList) nc off = o at hsl
  obtain ⟨ho8, hohi⟩ := hF.slot k o hsl
  have hsp : m.sp = E.sp := hm.frame.1
  obtain ⟨k0, rfl, hk0, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  have hpc : ({ m with pc := pcAt text psA.toList j } : MState) = m := by
    rw [← hj, ← show ({ m with mem := M0 } : MState).pc = E.pcOf b i from hm.pc]
  rw [hpc] at hstar
  simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
  obtain ⟨has, hf, -, ht, -, -, -⟩ := hok
  obtain ⟨V, hVe⟩ : ∃ V : BitVec 64,
      V = ({ m with pc := pcAt text psA.toList k0 } : MState).rX (BitVec.ofNat 5 ks) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : BitVec (8 * n), Y = BitVec.ofNat (8 * n) (V.toNat % 2 ^ (8 * n)) :=
    ⟨_, rfl⟩
  have hstep : progStep (Link.byId sym text az ez psA.toList) psA.toList[k0]
      { m with pc := pcAt text psA.toList k0 } =
      .ok { m with mem := (writeMem m.mem (E.sp + BitVec.ofInt 64 o) n Y),
                   pc := pcAt text psA.toList (k0 + 1) } := by
    rw [progStep_slotStoreN hks (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact nstoreAs_movMem hn3)
      hf ht hnc]
    · rw [← hVe, ← hY, hsp, ho]
    · simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
      show 4096 ≤ (m.sp + BitVec.ofInt 64 _).toNat
      rw [hsp, ho, win0_toNat (by omega) hohi]
      have := hF.lo; omega
  have hxV : ValRel E.ι (x.retypeL (lc.ty v.id)) V := by
    rw [hVe]; exact valRel_retypeL hA hcv hxf hxv
  have hyW : ValRel E.ι (x.retypeL (lc.ty v.id)) (Y.setWidth 64) := by
    rw [hY]; exact valRel_lowN hn3 hcn (fits_retypeL hcv _) hxV
  refine ⟨_, writeMem M0 (E.sp + BitVec.ofInt 64 o) n Y,
    hstar.tail (pstep_at F.nodup F.lt F.ret hk0 rfl hstep),
    slot_write_match (m := { m with mem := M0 }) hF hlc hcf hslot hext hm hinv hsi hh hsl hkn hyW
      hj'.symm, ?_, slotInv_setSlot hcf hsi hh hcv (fits_retypeL hcv _), rfl,
    fun y hy => writeMem_pt n _ _ _ _ y (hW y hy)⟩
  exact CoreInv.mono ⟨hinv.regs, hinv.mem⟩ (knext_same hK (Or.inr fun r _ => by rw [hh]; nofun))

/-- **A narrow spill**: `g66_nspillW` with the relation on `m` itself. -/
theorem g66_nspill (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hlc : E.lc = lc) (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k ∈ homeSlots lc, ∀ nc off, g.slotOp k = some (nc, off) →
      E.slot k = some (frameOff (Link.byId sym text az ez psA.toList) nc off))
    (hext : 0 ≤ (Link.byId sym text az ez psA.toList).extrasize)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {k : SlotKey} {nc : AddrName} {off : Int} {rs : Int} {n c : Nat}
    (hop : v.op = .StoreReg) (hn : narrowBytes lc v.type = some n)
    (hh : lc.home v.id = some (.slot k)) (hso : g.slotOp k = some (nc, off))
    (hsz1 : v.args.size = 1) (hts : (lc.ty v.id).size = n) (hao : argObj lc v 0 = .ok (c, rs))
    (hcv : cls (lc.ty v.id) = some c)
    (hvs : OneAt2 psA j ⟨plain (nstoreAs n) (· == regA rs) (slotA · nc off), "narrow spill"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  obtain ⟨m', M', h1, h2, h3, h4, h5, h6⟩ := g66_nspillW (H := H) F hF hlc hcf hslot hext
    (M0 := m.mem) hm hinv hsi hR hK hj hj' hop hn hh hso hsz1 hts hao hcv hvs htemp hs
    (W := fun _ => False) fun _ _ => rfl
  have hM : M' = m'.mem := funext fun y => h6 y id
  subst hM
  exact ⟨m', h1, h2, h3, h4, h5⟩


/-- **A narrow reload**: `loadByType`'s `MOV{B,H,W}` (signed type) or `MOV{B,H,W}U off(RSP), Rd`
of the slot's `n` bytes, sign- or zero-extended into `X kd` (the machine's registers in
`g49_load`'s form, for G35's upper-bit table). -/
theorem g66_nreload (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hlc : E.lc = lc) (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k ∈ homeSlots lc, ∀ nc off, g.slotOp k = some (nc, off) →
      E.slot k = some (frameOff (Link.byId sym text az ez psA.toList) nc off))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {a : ID} {k : SlotKey} {nc : AddrName} {off : Int} {rd : Int} {n c : Nat}
    (hop : v.op = .LoadReg) (hn : narrowBytes lc v.type = some n) (hsz1 : v.args.size = 1)
    (ha0 : v.args[0]? = some a) (hah : lc.home a = some (.slot k))
    (hso : g.slotOp k = some (nc, off)) (hta : (lc.ty a).size = n)
    (hca : cls (lc.ty a) = cls (lc.ty v.id)) (hro : resObj lc v = .ok (c, rd))
    (hvs : OneAt2 psA j ⟨plain (nloadAs n (typeSigned lc.ctx.tabs v.type)) (slotA · nc off)
      (· == regA rd), "narrow reload"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' ∧
      ∃ (kd : Nat) (Y : BitVec (8 * n)), rd = REG_R0 + kd ∧
        m'.x = (m.wX (BitVec.ofNat 5 kd) (if typeSigned lc.ctx.tabs v.type then
          ProgOp.sextTo64 n (Y.setWidth 64) else Y.setWidth 64)).x := by
  have hl := F.lowered
  have hA := F.addr
  have hn3 := narrowBytes_spec hn
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  have hca' : cls (lc.ty a) = some c := hca.trans hcv
  have hcn : c = 8 * n ∨ (c = 1 ∧ n = 1) := by have := cls_size hca'; rw [hta] at this; exact this
  obtain ⟨x, hx, rfl⟩ := stepLoc_move hl htemp (Or.inr hop) (arr1 hsz1 ha0) hs
  rw [read_slot hl hah] at hx
  cases hx
  rw [write_reg hvh hcv]
  obtain ⟨-, hsize, -, nc', off', hso', hnc⟩ := home_slot_gen hcf hah
  rw [hso] at hso'
  cases hso'
  have hkn : (lc.slotTy k).size = n := hsize.trans hta
  have hsl := hslot k (mem_homeSlots hah) nc off hso
  obtain ⟨ho8, hohi⟩ := hF.slot k _ hsl
  have hsp : m.sp = E.sp := hm.frame.1
  obtain ⟨Y, hY⟩ : ∃ Y : BitVec (8 * n), Y = readMem m.mem
      (m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off)) n :=
    ⟨_, rfl⟩
  have hrel : ValRel E.ι (((s.slots.lookup k).getD .poison).retypeL (lc.ty a))
      (if typeSigned lc.ctx.tabs v.type then ProgOp.sextTo64 n (Y.setWidth 64)
        else Y.setWidth 64) := by
    cases hk : s.slots.lookup k with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some v0 =>
      simp only [Option.getD_some]
      obtain ⟨o', ho', hsr⟩ := hm.slots k v0 hk
      rw [hsl] at ho'; cases ho'
      unfold SlotRel at hsr
      rw [hlc, hkn, ← hsp, ← hY] at hsr
      have hfk : Fits c v0 := by rw [← slotCls_home hcf hah hca']; exact (hsi k v0 hk).1
      exact valRel_retypeL hA hca' hfk (valRel_extN hn3 hcn hfk hsr _)
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL hA hcv (fits_retypeL hca' _) hrel) (fits_retypeL hcv _)
    (knext_set hK (by rw [hop]; nofun) hvh hcv)
    (fun k0 hk0 hok => ?_)).imp fun m' ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩, kd, Y, rfl, h4⟩
  simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
  obtain ⟨has, hf, -, ht, -, -, -⟩ := hok
  rw [progStep_slotLoadN hkd (nextAddr_pcAt F.nodup hk0)
    (by rw [has]; exact nloadAs_movMem hn3 _) hf hnc ht ?_, wX_pc, ← hY]
  simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
  show 4096 ≤ (m.sp + BitVec.ofInt 64 _).toNat
  rw [hsp, win0_toNat (by omega) hohi]
  have := hF.lo; omega

/-- **A `float32` spill**: `FMOVS Fs, off(RSP)` of the low 4 bytes of the argument's V register,
from a relation on `m` with its memory replaced by `M0` (agreeing with `m.mem` outside `W`), as
`g63_fspillW`. `g66_fspill` is the case `M0 = m.mem`. -/
theorem g66_fspillW (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hlc : E.lc = lc) (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k ∈ homeSlots lc, ∀ nc off, g.slotOp k = some (nc, off) →
      E.slot k = some (frameOff (Link.byId sym text az ez psA.toList) nc off))
    (hext : 0 ≤ (Link.byId sym text az ez psA.toList).extrasize) {M0 : Memory}
    (hm : LocMatch E s b i { m with mem := M0 }) (hinv : CoreInv E.ι (StkAt E) K s osp)
    (hsi : SlotInv lc s) (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {k : SlotKey} {nc : AddrName} {off : Int} {rs : Int}
    (hop : v.op = .StoreReg) (hh : lc.home v.id = some (.slot k))
    (hso : g.slotOp k = some (nc, off)) (hsz1 : v.args.size = 1) (hft : fTy (lc.ty v.id) = true)
    (hcv : cls (lc.ty v.id) = some 32) (hao : fargObj lc v 0 = .ok (32, rs))
    (hvs : OneAt2 psA j ⟨plain .FMOVS (· == regA rs) (slotA · nc off), "FMOVS spill"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s')
    {W : BitVec 64 → Prop} (hW : ∀ y, ¬ W y → M0 y = m.mem y) :
    ∃ m' M', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) { m' with mem := M' } ∧ CoreInv E.ι (StkAt E) K' s' osp ∧
      SlotInv lc s' ∧ m'.x = m.x ∧ ∀ y, ¬ W y → M' y = m'.mem y := by
  have hl := F.lowered
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a, r1, ha0, hah, hfo1, hft1, hca⟩ := fargObj_spec hao
  obtain ⟨ks, hks, rfl, hkk⟩ := fobjOf?_some hfo1
  have hr0 : r1 ≠ zeroReg := by have := (objV?_some hkk).1; unfold zeroReg; omega
  obtain ⟨x, hx, hxv, hxf⟩ := arg_relV hl hm hinv hah hft1 hca
    (kread_arg hR hnp ha0 hah hca hr0) hkk
  obtain ⟨x', hx', rfl⟩ := stepLoc_move hl htemp (Or.inl hop) (arr1 hsz1 ha0) hs
  rw [hx] at hx'
  cases hx'
  rw [write_slot hh]
  obtain ⟨-, hsize, -, nc', off', hso', hnc⟩ := home_slot_gen hcf hh
  rw [hso] at hso'
  cases hso'
  have hkn : (lc.slotTy k).size = 4 := by
    rw [hsize]; have := cls_size hcv; omega
  have hsl := hslot k (mem_homeSlots hh) nc off hso
  generalize ho : frameOff (Link.byId sym text az ez psA.toList) nc off = o at hsl
  obtain ⟨ho8, hohi⟩ := hF.slot k o hsl
  have hsp : m.sp = E.sp := hm.frame.1
  obtain ⟨k0, rfl, hk0, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  have hpc : ({ m with pc := pcAt text psA.toList j } : MState) = m := by
    rw [← hj, ← show ({ m with mem := M0 } : MState).pc = E.pcOf b i from hm.pc]
  rw [hpc] at hstar
  simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
  obtain ⟨has, hf, -, ht, -, -, -⟩ := hok
  obtain ⟨q, hq⟩ : ∃ q : BitVec 128,
      q = ({ m with pc := pcAt text psA.toList k0 } : MState).v (BitVec.ofNat 5 ks) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : BitVec (8 * 4), Y = BitVec.ofNat (8 * 4) (q.toNat % 2 ^ (8 * 4)) :=
    ⟨_, rfl⟩
  have hstep : progStep (Link.byId sym text az ez psA.toList) psA.toList[k0]
      { m with pc := pcAt text psA.toList k0 } =
      .ok { m with mem := (writeMem m.mem (E.sp + BitVec.ofInt 64 o) 4 Y),
                   pc := pcAt text psA.toList (k0 + 1) } := by
    rw [progStep_fstoreAt hks (nextAddr_pcAt F.nodup hk0) (by rw [has]; rfl) hf (slotA_eq ht).1
      (ctx_mem_slot ht hnc)]
    · rw [← hq, ← hY, hsp, ho]
    · simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
      show 4096 ≤ (m.sp + BitVec.ofInt 64 _).toNat
      rw [hsp, ho, win0_toNat (by omega) hohi]
      have := hF.lo; omega
  have hxV : ValRel E.ι (x.retypeL (lc.ty v.id)) (q.setWidth 64) := by
    rw [hq]; exact valRel_of_fvalRel (fvalRel_retypeL hxv hxf hft hcv)
  have hyW : ValRel E.ι (x.retypeL (lc.ty v.id)) (Y.setWidth 64) := by
    have h := valRel_lowN (n := 4) (by omega) (by omega) (fits_retypeL hcv _) hxV
    have hqY : (BitVec.ofNat (8 * 4) ((q.setWidth 64).toNat % 2 ^ (8 * 4)) : BitVec (8 * 4)) = Y := by
      rw [hY]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
      rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ (8 * 4) ∣ 2 ^ 64)]
    rwa [hqY] at h
  refine ⟨_, writeMem M0 (E.sp + BitVec.ofInt 64 o) 4 Y,
    hstar.tail (pstep_at F.nodup F.lt F.ret hk0 rfl hstep),
    slot_write_match (m := { m with mem := M0 }) hF hlc hcf hslot hext hm hinv hsi hh hsl hkn hyW
      hj'.symm, ?_, slotInv_setSlot hcf hsi hh hcv (fits_retypeL hcv _), rfl,
    fun y hy => writeMem_pt 4 _ _ _ _ y (hW y hy)⟩
  exact CoreInv.mono ⟨hinv.regs, hinv.mem⟩ (knext_same hK (Or.inr fun r _ => by rw [hh]; nofun))

/-- **A `float32` spill**: `g66_fspillW` with the relation on `m` itself. -/
theorem g66_fspill (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hlc : E.lc = lc) (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k ∈ homeSlots lc, ∀ nc off, g.slotOp k = some (nc, off) →
      E.slot k = some (frameOff (Link.byId sym text az ez psA.toList) nc off))
    (hext : 0 ≤ (Link.byId sym text az ez psA.toList).extrasize)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {k : SlotKey} {nc : AddrName} {off : Int} {rs : Int}
    (hop : v.op = .StoreReg) (hh : lc.home v.id = some (.slot k))
    (hso : g.slotOp k = some (nc, off)) (hsz1 : v.args.size = 1) (hft : fTy (lc.ty v.id) = true)
    (hcv : cls (lc.ty v.id) = some 32) (hao : fargObj lc v 0 = .ok (32, rs))
    (hvs : OneAt2 psA j ⟨plain .FMOVS (· == regA rs) (slotA · nc off), "FMOVS spill"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  obtain ⟨m', M', h1, h2, h3, h4, h5, h6⟩ := g66_fspillW (H := H) F hF hlc hcf hslot hext
    (M0 := m.mem) hm hinv hsi hR hK hj hj' hop hh hso hsz1 hft hcv hao hvs htemp hs
    (W := fun _ => False) fun _ _ => rfl
  have hM : M' = m'.mem := funext fun y => h6 y id
  subst hM
  exact ⟨m', h1, h2, h3, h4, h5⟩

/-- A value of class 32 related to the zero extension of 4 bytes `Y` as a register is related to
them in the low bits of a V register. -/
theorem fvalRel_of_valRel32 {ι : Blk → Option (BitVec 64)} {y : Val} {Y : BitVec (8 * 4)}
    (hf : Fits 32 y) (h : ValRel ι y (Y.setWidth 64)) : FValRel y (Y.setWidth 128) := by
  cases y with
  | poison => trivial
  | int w x =>
    simp only [Fits] at hf
    cases w <;> simp only [Width.bits] at hf <;> first | omega | skip
    simp only [ValRel] at h
    simp only [FValRel, ← h]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  | bool _ => simp [Fits] at hf
  | ptr _ => simp [Fits] at hf
  | _ => exact absurd hf (by simp [Fits])

/-- **A `float32` reload**: `FMOVS off(RSP), Fd` of the slot's 4 bytes into the V register's low
32 bits; a 32-bit value has no pointer form, so no premise. -/
theorem g66_freload (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hlc : E.lc = lc) (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k ∈ homeSlots lc, ∀ nc off, g.slotOp k = some (nc, off) →
      E.slot k = some (frameOff (Link.byId sym text az ez psA.toList) nc off))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {a : ID} {k : SlotKey} {nc : AddrName} {off : Int} {rd : Int}
    (hop : v.op = .LoadReg) (hsz1 : v.args.size = 1) (ha0 : v.args[0]? = some a)
    (hah : lc.home a = some (.slot k)) (hso : g.slotOp k = some (nc, off))
    (hca : cls (lc.ty a) = some 32) (hro : fresObj lc v = .ok (32, rd))
    (hvs : OneAt2 psA j ⟨plain .FMOVS (slotA · nc off) (· == regA rd), "FMOVS reload"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨x, hx, rfl⟩ := stepLoc_move hl htemp (Or.inr hop) (arr1 hsz1 ha0) hs
  rw [read_slot hl hah] at hx
  cases hx
  rw [write_reg hvh hcv]
  obtain ⟨-, hsize, -, nc', off', hso', hnc⟩ := home_slot_gen hcf hah
  rw [hso] at hso'
  cases hso'
  have hkn : (lc.slotTy k).size = 4 := by
    rw [hsize]; have := cls_size hca; omega
  have hsl := hslot k (mem_homeSlots hah) nc off hso
  obtain ⟨ho8, hohi⟩ := hF.slot k _ hsl
  have hsp : m.sp = E.sp := hm.frame.1
  obtain ⟨Y, hY⟩ : ∃ Y : BitVec (8 * 4), Y = readMem m.mem
      (m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off)) 4 :=
    ⟨_, rfl⟩
  have hrel : ValRel E.ι (((s.slots.lookup k).getD .poison).retypeL (lc.ty a)) (Y.setWidth 64) := by
    cases hk : s.slots.lookup k with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some v0 =>
      simp only [Option.getD_some]
      obtain ⟨o', ho', hsr⟩ := hm.slots k v0 hk
      rw [hsl] at ho'; cases ho'
      unfold SlotRel at hsr
      rw [hlc, hkn, ← hsp, ← hY] at hsr
      have hfk : Fits 32 v0 := by rw [← slotCls_home hcf hah hca]; exact (hsi k v0 hk).1
      exact valRel_retypeL hA hca hfk hsr
  have hz := valRel_retypeL hA hcv (fits_retypeL hca _) hrel
  have hfz := fvalRel_of_valRel32 (fits_retypeL hcv _) hz
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hfz (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
  obtain ⟨has, hf, -, ht, -, -, -⟩ := hok
  rw [progStep_floadAt hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; rfl) (slotA_eq hf).1
    (ctx_mem_slot hf hnc) ht]
  · subst hY; rfl
  · simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
    show 4096 ≤ (m.sp + BitVec.ofInt 64 _).toNat
    rw [hsp, win0_toNat (by omega) hohi]
    have := hF.lo; omega

end Cases

end GoFV.Proof.Gen
