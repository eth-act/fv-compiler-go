import GoFV.Proof.Gen.Spec63
import GoFV.Proof.Gen.G62

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G63: float spills and reloads (`docs/plans/proofs3.md` §4)

A float spill (`VK63.fspill`) runs as G2's spill: `StoreReg` writes its argument, read at its
float shape, to its slot `k` (`stepLoc_move`). The argument's V register holds its bit pattern in
its low 64 bits (`arg_relV`, `FValRel`), and `FMOVD Fs, off(RSP)` stores those 8 bytes at `k`'s frame
address (`progStep_fstoreAt`, `ctx_mem_slot`), so the slot relates as a 64-bit register does
(`SlotRel`, `valRel_of_fvalRel`); the other slots, the blocks and the frame words lie outside the
written window, as for G2's spill (`g63_fspill`). As `g2_spillW`, `g63_fspillW` takes the relation
on the machine state with its memory replaced by one that agrees with it outside some bytes `W`
(the entry stores' pending windows, `GoFV/Proof/Obj/EntrySkip.lean`): both memories get the same
write.

A float reload (`VK63.freload`) runs as G2's reload: `LoadReg` writes the slot's value, read at its
argument's shape and then at the value's float shape, to its V register. `FMOVD off(RSP), Fd` loads
the slot's 8 bytes into the V register's low 64 bits (`progStep_floadAt`). The slot relates the
value to those bytes as a register (`SlotRel`); a V register relates only integers and `poison`
(`FValRel`: a pointer has no V register form), so the reload needs the value it reads at the float
shape to be no pointer without an integer form: the run premise `FReloadPre`, as G44's `FLoadPre`
for a float load. Then `fvalRel_of_valRel` relates it to the V register (`g63_freload`).

Neither writes an X register (`m'.x = m.x`), so G35's upper-bit table keeps the entries of the
other registers (`uokl_f63`); the class table follows `kStep`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-- **A float reload reads no pointer** (the run premise of slice G63, as G44's `FLoadPre`): a
`LoadReg` homed in a V register reads, at its float shape, no pointer without an integer form (a
pointer has no V register form). -/
def FReloadPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  v.op = .LoadReg → ∀ r k, lc.home v.id = some (.reg r) → objV? r = some k →
    ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → ∀ q, x.retypeL (lc.ty v.id) ≠ .ptr q

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- A float spill: `FMOVD Fs, off(RSP)` of the low 64 bits of the argument's V register, from a
relation on `m` with its memory replaced by `M0` (agreeing with `m.mem` outside `W`), as
`g2_spillW`. `g63_fspill` is the case `M0 = m.mem`. -/
theorem g63_fspillW (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
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
    (hcv : cls (lc.ty v.id) = some 64) (hao : fargObj lc v 0 = .ok (64, rs))
    (hvs : OneAt2 psA j ⟨plain .FMOVD (· == regA rs) (slotA · nc off), "FMOVD spill"⟩ j')
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
  obtain ⟨h8, nc', off', hso', hnc⟩ := home_slot hcf hh hcv
  rw [hso] at hso'
  cases hso'
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
  obtain ⟨A, hAe⟩ : ∃ A, A = E.sp + BitVec.ofInt 64 o := ⟨_, rfl⟩
  obtain ⟨V, hVe⟩ : ∃ V : BitVec 64,
      V = (({ m with pc := pcAt text psA.toList k0 } : MState).v (BitVec.ofNat 5 ks)).setWidth 64 :=
    ⟨_, rfl⟩
  have hVeq : (BitVec.ofNat (8 * 8) ((({ m with pc := pcAt text psA.toList k0 } : MState).v
      (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * 8)) : BitVec 64) = V := by
    rw [hVe]
    apply BitVec.eq_of_toNat_eq
    simp
  have hstep : progStep (Link.byId sym text az ez psA.toList) psA.toList[k0]
      { m with pc := pcAt text psA.toList k0 } =
      .ok { m with mem := writeMem m.mem A 8 V, pc := pcAt text psA.toList (k0 + 1) } := by
    rw [progStep_fstoreAt hks (nextAddr_pcAt F.nodup hk0) (by rw [has]; rfl) hf (slotA_eq ht).1
      (ctx_mem_slot ht hnc)]
    · rw [hVeq, hsp, ho, ← hAe]
    · simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
      show 4096 ≤ (m.sp + BitVec.ofInt 64 _).toNat
      rw [hsp, ho, win0_toNat (by omega) hohi]
      have := hF.lo; omega
  subst hAe
  have hxV : ValRel E.ι (x.retypeL (lc.ty v.id)) V := by
    rw [hVe]
    exact valRel_of_fvalRel (fvalRel_retypeL hxv hxf hft hcv)
  have hMout : ∀ y : BitVec 64, (∀ j, j < 8 → y ≠ E.sp + BitVec.ofInt 64 o + BitVec.ofNat 64 j) →
      writeMem M0 (E.sp + BitVec.ofInt 64 o) 8 V y = M0 y :=
    fun y hy => writeMem_other 8 _ _ _ y hy
  refine ⟨_, writeMem M0 (E.sp + BitVec.ofInt 64 o) 8 V,
    hstar.tail (pstep_at F.nodup F.lt F.ret hk0 rfl hstep), ?_, ?_, ?_, rfl,
    fun y hy => writeMem_pt 8 _ _ _ _ y (hW y hy)⟩
  · obtain ⟨mm, hmm, hMI⟩ := hm.mem
    obtain ⟨mm0, hmm0, -, hsep⟩ := hinv.mem
    rw [hmm] at hmm0
    cases hmm0
    refine ⟨hm.regs, hm.flags, ?_, ⟨mm, hmm, ?_⟩, ?_, by rw [hj']⟩
    · intro k' v' hk'
      rcases lookup_setSlot hk' with ⟨rfl, rfl⟩ | ⟨hne, hold⟩
      · refine ⟨o, hsl, ?_⟩
        unfold SlotRel
        rw [hlc, h8, readMem_writeMem_self]
        simpa using hxV
      · obtain ⟨o', ho', hsr⟩ := hm.slots k' v' hold
        refine ⟨o', ho', ?_⟩
        obtain ⟨-, i', hi'⟩ := hsi k' v' hold
        have hap := slot_apart hcf hslot hext (mem_homeSlots hh) (mem_homeSlots hi') (Ne.symm hne)
          hsl ho'
        unfold SlotRel at hsr ⊢
        rw [hlc] at hsr ⊢
        have h8' : (lc.slotTy k').size ≤ 8 := hlc ▸ slot_sizes hlc hcf hsi k' v' hold
        rw [readMem_congr _ (E.sp + BitVec.ofInt 64 o')
          (fun j hj => hMout _ (fun j' hj' => slot_windows_apart hF hsl ho' hap hj' (by omega)
            (by rw [h8]; exact hj') hj))]
        exact hsr
    · exact memInj_of_sepW hMI hsep.sepW fun y hy =>
        hMout y fun j hj he => hy (he ▸ stk_slot hF hsl hj (by rw [hlc, h8]; exact hj))
    · refine frameRel_mem (m := { m with mem := M0 }) hF hm.frame
        (fun _ j hj => ⟨hMout _ (fun j' hj' he => ?_), hMout _ (fun j' hj' he => ?_)⟩)
      · have := congrArg BitVec.toNat he
        rw [sp_toNat hF hj, win_toNat (by omega) hohi hj'] at this
        omega
      · have := congrArg BitVec.toNat he
        rw [spm8_toNat hF hj, win_toNat (by omega) hohi hj'] at this
        have := hF.lo
        omega
  · exact CoreInv.mono ⟨hinv.regs, hinv.mem⟩
      (knext_same hK (Or.inr fun r _ => by rw [hh]; nofun))
  · intro k' v' hk'
    rcases lookup_setSlot hk' with ⟨rfl, rfl⟩ | ⟨-, hold⟩
    · exact ⟨by rw [slotCls_home hcf hh hcv]; exact fits_retypeL hcv _, v.id, hh⟩
    · exact hsi k' v' hold

/-- A float spill: `g63_fspillW` with the relation on `m` itself. -/
theorem g63_fspill (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
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
    (hcv : cls (lc.ty v.id) = some 64) (hao : fargObj lc v 0 = .ok (64, rs))
    (hvs : OneAt2 psA j ⟨plain .FMOVD (· == regA rs) (slotA · nc off), "FMOVD spill"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  obtain ⟨m', M', h1, h2, h3, h4, h5, h6⟩ := g63_fspillW (H := H) F hF hlc hcf hslot hext
    (M0 := m.mem) hm hinv hsi hR hK hj hj' hop hh hso hsz1 hft hcv hao hvs htemp hs
    (W := fun _ => False) fun _ _ => rfl
  have hM : M' = m'.mem := funext fun y => h6 y id
  subst hM
  exact ⟨m', h1, h2, h3, h4, h5⟩

/-- A float reload: `FMOVD off(RSP), Fd` of the slot's 8 bytes, under `FReloadPre`. -/
theorem g63_freload (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hlc : E.lc = lc) (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k ∈ homeSlots lc, ∀ nc off, g.slotOp k = some (nc, off) →
      E.slot k = some (frameOff (Link.byId sym text az ez psA.toList) nc off))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {a : ID} {k : SlotKey} {nc : AddrName} {off : Int} {rd : Int}
    (hop : v.op = .LoadReg) (hsz1 : v.args.size = 1) (ha0 : v.args[0]? = some a)
    (hah : lc.home a = some (.slot k)) (hso : g.slotOp k = some (nc, off))
    (hca : cls (lc.ty a) = some 64) (hro : fresObj lc v = .ok (64, rd))
    (hvs : OneAt2 psA j ⟨plain .FMOVD (slotA · nc off) (· == regA rd), "FMOVD reload"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hpre : FReloadPre lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨x, hx, rfl⟩ := stepLoc_move hl htemp (Or.inr hop) (arr1 hsz1 ha0) hs
  have hnptr := hpre hop r _ hvh hkd' a x ha0 hx
  rw [read_slot hl hah] at hx
  cases hx
  rw [write_reg hvh hcv]
  obtain ⟨h8, nc', off', hso', hnc⟩ := home_slot hcf hah hca
  rw [hso] at hso'
  cases hso'
  have hsl := hslot k (mem_homeSlots hah) nc off hso
  obtain ⟨ho8, hohi⟩ := hF.slot k _ hsl
  have hsp : m.sp = E.sp := hm.frame.1
  have hrel : ValRel E.ι (((s.slots.lookup k).getD .poison).retypeL (lc.ty a))
      ((readMem m.mem (m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off))
        8).setWidth 64) := by
    cases hk : s.slots.lookup k with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some v0 =>
      simp only [Option.getD_some]
      obtain ⟨o', ho', hsr⟩ := hm.slots k v0 hk
      rw [hsl] at ho'; cases ho'
      unfold SlotRel at hsr
      rw [hlc, h8] at hsr
      rw [hsp]
      have hfk : Fits 64 v0 := by rw [← slotCls_home hcf hah hca]; exact (hsi k v0 hk).1
      exact valRel_retypeL hA hca hfk hsr
  obtain ⟨hw, -⟩ := fTy_eq (n := 8) hft hcv
  have hz := valRel_retypeL hA hcv (fits_retypeL hca _) hrel
  have hfz := fvalRel_of_valRel hA hz hnptr
    (fun b' => by rw [hw]; exact retypeL_int_ne_bool _ b')
    (q := (readMem m.mem (m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList)
      nc off)) 8).setWidth 128)
    (by rw [BitVec.setWidth_setWidth_of_le _ (by omega)])
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hfz (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
  obtain ⟨has, hf, -, ht, -, -, -⟩ := hok
  rw [progStep_floadAt hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; rfl) (slotA_eq hf).1
    (ctx_mem_slot hf hnc) ht]
  · rfl
  · simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
    show 4096 ≤ (m.sp + BitVec.ofInt 64 _).toNat
    rw [hsp, win0_toNat (by omega) hohi]
    have := hF.lo; omega

end Cases

/-! ## The tables -/

/-- G35's upper-bit table across a float spill or reload (a reload homed in no X register, so with
no entry, `reloadEntry35`): the entries of the other registers. -/
theorem uokl_f63 {lc : LocCtx} {v : Value} {m m' : MState} {L : List (Nat × Nat × Bool)}
    (hop : v.op = .StoreReg ∨ v.op = .LoadReg)
    (hf : v.op = .LoadReg → ∀ r, regHome? lc v.id = some r → objX? r = none)
    (hx : m'.x = m.x) (hL : UOKL m L) :
    UOKL m' (uStep35 lc L v) := by
  have h0 : ldEntry35 lc v = none := by
    rcases hop with h | h
    · exact ldEntry35_none (by rw [h]; rfl) (by rw [h]; nofun)
    · exact ldEntry35_reload_none h fun r _ hr _ hx' _ => by
        rw [hf h r hr] at hx'; cases hx'
  have hp : pairOp35 lc v = false := by rcases hop with h | h <;> simp [pairOp35, h]
  have hk : keep34 v = true := by
    rcases hop with h | h <;> simp [keep34, keep31, keepOp31, keepOp34, h]
  rw [uStep35_other h0 hp (by rcases hop with h | h <;> rw [h] <;> nofun), uStep34_keep hk]
  exact uokl_keep hL (.inl hx)

end GoFV.Proof.Gen
