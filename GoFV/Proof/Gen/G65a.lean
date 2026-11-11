import GoFV.Proof.Gen.Spec65
import GoFV.Proof.Gen.G64

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G65: the cases (`docs/plans/proofs3.md` §4)

* A float load of a frame variable (`g65_fvload`): G44's float load (`stepLoc_fload`, the run
  premise `FLoadPre`, `fvalRel_of_valRel`) at the variable's block (`VarAt57`, as G57's float
  stores): the block is at `SP + frameOff` under the injection, and the machine loads the frame
  operand (`ctx_mem_slot`, `progStep_floadAt`).
* A float pair store through a register (`g65_fstpReg`, as G57's `STPW`, `g57_stpw`) or to a
  global (`g65_fstpGlob`, as G22's `STP`, `g22_stp`): `runLoc` writes the floats' raw bits at
  `pairAddr` (`stepLoc_fstp57`), the machine the low bytes of the V registers at the operand's
  address and `n` bytes above (`progStep_fstpAt`), related as G57's frame-variable pair stores
  (`g57_fstp`). No run premise.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The machine -/

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- The opcode of a float pair store of 4- or 8-byte elements. -/
private theorem fstpAs_cases65 {n : Nat} (hn : n = 4 ∨ n = 8) :
    (n = 4 ∧ fstpAs n = .FSTPS) ∨ (n = 8 ∧ fstpAs n = .FSTPD) := by
  rcases hn with rfl | rfl
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-- `FSTPS`/`FSTPD (Fa, Fb)` at the address `A` of its operand: the low `n` bytes of `V ka` at
`A`, then those of `V kb` `n` bytes above. -/
private theorem eff_fstp65 {c : ProgCtx} {n ka kb : Nat} {A : BitVec 64} (hka : ka < 32)
    (hkb : kb < 32) (hn : n = 4 ∨ n = 8) (has : c.p.as = fstpAs n)
    (hf : c.p.from_ = pairA (REG_F0 + ka) (REG_F0 + kb)) (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, n, (c.s.v (BitVec.ofNat 5 ka)).toNat % 2 ^ (8 * n)),
        (A + BitVec.ofNat 64 n, n, (c.s.v (BitVec.ofNat 5 kb)).toNat % 2 ^ (8 * n))] } := by
  rcases fstpAs_cases65 hn with ⟨rfl, hfa⟩ | ⟨rfl, hfa⟩
  · have hname : As.name .FSTPS = "FSTPS" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hfa, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_v_f0 hka, ctx_v_f0 hkb]
    rfl
  · have hname : As.name .FSTPD = "FSTPD" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hfa, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_v_f0 hka, ctx_v_f0 hkb]
    rfl

/-- `FSTPS`/`FSTPD (Fa, Fb)` at an operand of address `A`, both addresses outside the nil page: the
low `n` bytes of `V ka` at `A`, then those of `V kb` `n` bytes above. -/
theorem progStep_fstpAt {n ka kb : Nat} {A : BitVec 64} (hka : ka < 32) (hkb : kb < 32)
    (hn4 : n = 4 ∨ n = 8) (hn : L.nextAddr p.id = some next) (has : p.as = fstpAs n)
    (hf : p.from_ = pairA (REG_F0 + ka) (REG_F0 + kb))
    (hma : (ProgCtx.mk L s p).mem p.to = .ok (A, none))
    (hnil : nilPage A = false) (hnil' : nilPage (A + BitVec.ofNat 64 n) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem A n
          (BitVec.ofNat (8 * n) ((s.v (BitVec.ofNat 5 ka)).toNat % 2 ^ (8 * n))))
        (A + BitVec.ofNat 64 n) n
          (BitVec.ofNat (8 * n) ((s.v (BitVec.ofNat 5 kb)).toNat % 2 ^ (8 * n))),
      pc := next } := by
  have hsk : p.isSkip = false := by
    rcases fstpAs_cases65 hn4 with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [Prog.isSkip, has, h]
  have he := eff_fstp65 (c := ⟨L, s, p⟩) hka hkb hn4 has hf hma
  rw [progStep_eq hn hsk he (by simp [Eff.nilAccess?, List.find?, hnil, hnil'])]
  rfl

end Progs

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `FMOVS`/`FMOVD off(<nc>), Fd`: the float load of a frame variable, G44's `n`-byte load into a
V register (`g44_fload`) at the variable's block (`VarAt57`). -/
theorem g65_fvload (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K') (hpre : FLoadPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {nc : AddrName} {off : Int} {bk : Blk}
    (hB : VarAt57 lc E (Link.byId sym text az ez psA.toList) v nc off bk) {rd : Int}
    (hop : v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload) (hsz2 : v.args.size = 2)
    (hma : memArg lc v 1 = .ok ()) (hro : fresObj lc v = .ok (8 * fBytes v.op, rd))
    (hvs : OneAt2 psA j ⟨plain (fmovAs (8 * fBytes v.op)) (slotA · nc off) (· == regA rd),
      (fmovAs (8 * fBytes v.op)).name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> nofun
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨x, hx, rfl⟩ := stepLoc_fload hl htemp hop (arr2 hsz2 ha0 ha1)
    (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, mm2, bs, hsym, hmm2, hrd, hnpp⟩ := hpre hop a0 x ha0 hx
  rw [hmm] at hmm2
  cases hmm2
  rw [hB.sym v x rfl] at hsym
  cases hsym
  rw [write_reg hvh hcv, hB.sym v x rfl]
  simp only [Option.elim]
  have hn := fBytes_cases v.op
  have hn' : fBytes v.op = 1 ∨ fBytes v.op = 2 ∨ fBytes v.op = 4 ∨ fBytes v.op = 8 := by omega
  obtain ⟨hty, -⟩ := fTy_eq hft hcv
  have ht : lc.ty v.id ≠ .bool := by rw [hty]; nofun
  have hmov := fmovAs_movMem hn
  obtain ⟨a, hpa, haeq⟩ := hB.addr
  have hval : FValRel ((Arm64.loadN (lc.ty v.id) (fBytes v.op) false mm
        ⟨bk, BitVec.ofInt 64 v.auxInt.toInt⟩).retypeL (lc.ty v.id))
      ((readMem m.mem (a + BitVec.ofInt 64 v.auxInt.toInt) (fBytes v.op)).setWidth 128) := by
    have hv := valRel_retypeL_lo hA hcv ht
      ((lo_loadN hA hMI hn' (fun _ => rfl) ht hpa hrd).mono (cls_le hcv))
    refine fvalRel_of_valRel hA hv hnpp (fun b' => by rw [hty]; exact retypeL_int_ne_bool _ b') ?_
    exact BitVec.setWidth_setWidth_of_le _ (by omega)
  have hzf := fits_retypeL hcv
    (Arm64.loadN (lc.ty v.id) (fBytes v.op) false mm ⟨bk, BitVec.ofInt 64 v.auxInt.toInt⟩)
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < fBytes v.op) (Or.inr (by rw [hrd]; rfl))
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hval hzf
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  obtain ⟨has, hf, -, ht', -⟩ := plain_spec hok
  simp only [beq_iff_eq] at ht'
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].from_ =
      .ok (a + BitVec.ofInt 64 v.auxInt.toInt, none) := by
    rw [ctx_mem_slot hf hB.cls]
    exact congrArg (fun z => Except.ok (z, none)) hA'
  rw [progStep_floadAt hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov) (slotA_eq hf).1
    hma' ht' hnil]
  rfl

/-- `FSTPS`/`FSTPD (Fa, Fb), off(Rn)`: the low `n` bytes of `Fa` at the address and of `Fb` `n`
bytes above (`g57_stpw` with V registers), outside the frame. -/
theorem g65_fstpReg (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {rn rx ry : Int} {dst : Addr → Bool} (hop : fstpOf v.op = some n)
    (hsz4 : v.args.size = 4) (hax : v.aux = none) (hmt : memTy (lc.ty v.id) = true)
    (hhn : lc.home v.id = none) (hao : argObj lc v 0 = .ok (64, rn))
    (hxo : fargObj lc v 1 = .ok (8 * n, rx)) (hyo : fargObj lc v 2 = .ok (8 * n, ry))
    (hma : memArg lc v 3 = .ok ()) (hdst : ∀ A, dst A = true → A = memA rn v.auxInt.toInt)
    (hvs : OneAt2 psA j ⟨plain (fstpAs n) (· == pairA rx ry) dst, (fstpAs n).name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hn48 : n = 4 ∨ n = 8 := by rcases fstpOf_some hop with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hn' : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by omega
  have hnp : v.op ≠ .Phi := by rcases fstpOf_some hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨a1, r1, ha1, hah1, hfo1, hft1, hca1⟩ := fargObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hfo2, hft2, hca2⟩ := fargObj_spec hyo
  obtain ⟨kx, hkx, rfl, hkx'⟩ := fobjOf?_some hfo1
  obtain ⟨ky, hky, rfl, hky'⟩ := fobjOf?_some hfo2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  have hr1 : r1 ≠ zeroReg := by have := (objV?_some hkx').1; unfold zeroReg; omega
  have hr2 : r2 ≠ zeroReg := by have := (objV?_some hky').1; unfold zeroReg; omega
  obtain ⟨Y, hY, hyv, hyf⟩ := arg_relV hl hm hinv hah1 hft1 hca1
    (kread_arg hR hnp ha1 hah1 hca1 hr1) hkx'
  obtain ⟨Z, hZ, hzv, hzf⟩ := arg_relV hl hm hinv hah2 hft2 hca2
    (kread_arg hR hnp ha2 hah2 hca2 hr2) hky'
  obtain ⟨x, y, z, p, q, mm1, mm', hx, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_fstp57 hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hX] at hx; cases hx
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨hap, haq⟩ := pairAddr_noAuxN hax hpq
  have hyv' : ValRel E.ι Y ((m.v (BitVec.ofNat 5 kx)).setWidth 64) := valRel_of_fvalRel hyv
  have hzv' : ValRel E.ι Z ((m.v (BitVec.ofNat 5 ky)).setWidth 64) := valRel_of_fvalRel hzv
  have hcs : 8 * n ≤ 8 * n ∨ 8 * n = 1 := .inl (Nat.le_refl _)
  have hby := (storeBytes_relN hA hn' hyv' hyf hcs).1
  have hbz := (storeBytes_relN hA hn' hzv' hzf hcs).1
  have hcan1 : mm.canWrite p n = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf hap (by omega : 0 < n) (Or.inl hcan1)
  obtain ⟨hM1, hk1, hback1, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hk0 hn' hpa hyv' hyf hcs hw1
  have hcan2 : mm1.canWrite q n = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨a', hqa, haeq', hnil'⟩ := addr_rel hA hM1 hxv hxf haq (by omega : 0 < n) (Or.inl hcan2)
  obtain ⟨hM2, hk2, hback2, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 hn' hqa hzv' hzf hcs hw2
  have hsep1 : SepAt osp E.ι (StkAt E) mm1 := hsep0.write hk0 hw1
  have hsep2 : SepAt osp E.ι (StkAt E) mm' := hsep1.write hk1 hw2
  have hwf1 := write_wf hw1 (by rw [hby]; omega)
  have hwf2 := write_wf hw2 (by rw [hbz]; omega)
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have haeqn : a + p.off + BitVec.ofNat 64 n = a' + q.off := by
    rw [← haeq, BitVec.add_assoc]; exact haeq'
  have hword : ∀ k : Nat, k < 32 →
      ((m.v (BitVec.ofNat 5 k)).setWidth 64).toNat % 2 ^ (8 * n) =
        (m.v (BitVec.ofNat 5 k)).toNat % 2 ^ (8 * n) := by
    intro k _
    rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM2 hk2 hsep2
    (fun w hw => (hout2 w fun j hj he => hsep1.not_mem hal2 hqa hw (by omega) (by omega)).trans
      (hout1 w fun j hj he => hsep0.not_mem hal1 hpa hw (by omega) (by omega)))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf1, -, ht1, hsc, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf1
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
      .ok (a + p.off, none) := by
    rw [hdst _ ht1, ctx_mem_reg hkn hsc]
    exact congrArg (fun z => Except.ok (z, none)) haeq
  rw [progStep_fstpAt hkx hky hn48 (nextAddr_pcAt F.nodup hk) has hf1 hma' hnil
    (by rw [haeqn]; exact hnil'), haeqn, hword kx hkx, hword ky hky]

/-- `FSTPS`/`FSTPD (Fa, Fb), sym+off(SB)`: the two `n`-byte stores into the global's block, at its
injected address (`g22_stp` with V registers). -/
theorem g65_fstpGlob (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {x : AuxRef} {name : GoStr} {abi : Nat} {rx ry : Int} {dst : Addr → Bool}
    (hop : fstpOf v.op = some n) (hx : v.aux = some x)
    (hsy : symOf? lc.ctx.tabs x = some (name, abi)) (hsz4 : v.args.size = 4)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hxo : fargObj lc v 1 = .ok (8 * n, rx)) (hyo : fargObj lc v 2 = .ok (8 * n, ry))
    (hma : memArg lc v 3 = .ok ())
    (hdst : ∀ A, dst A = true → A.type = .MEM ∧ A.name = .EXTERN ∧ A.reg = 0 ∧ A.index = 0 ∧
      A.offset = v.auxInt.toInt ∧ ∃ y, A.sym = some y ∧ g.syms[y]? = some (name, abi))
    (hvs : OneAt2 psA j ⟨plain (fstpAs n) (· == pairA rx ry) dst, (fstpAs n).name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hn48 : n = 4 ∨ n = 8 := by rcases fstpOf_some hop with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hn' : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by omega
  have hnp : v.op ≠ .Phi := by rcases fstpOf_some hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨a1, r1, ha1, hah1, hfo1, hft1, hca1⟩ := fargObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hfo2, hft2, hca2⟩ := fargObj_spec hyo
  obtain ⟨kx, hkx, rfl, hkx'⟩ := fobjOf?_some hfo1
  obtain ⟨ky, hky, rfl, hky'⟩ := fobjOf?_some hfo2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  have hr1 : r1 ≠ zeroReg := by have := (objV?_some hkx').1; unfold zeroReg; omega
  have hr2 : r2 ≠ zeroReg := by have := (objV?_some hky').1; unfold zeroReg; omega
  obtain ⟨Y, hY, hyv, hyf⟩ := arg_relV hl hm hinv hah1 hft1 hca1
    (kread_arg hR hnp ha1 hah1 hca1 hr1) hkx'
  obtain ⟨Z, hZ, hzv, hzf⟩ := arg_relV hl hm hinv hah2 hft2 hca2
    (kread_arg hR hnp ha2 hah2 hca2 hr2) hky'
  obtain ⟨x', y, z, p, q, mm1, mm', -, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_fstp57 hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  rw [pairAddr_globN hx hsy] at hpq
  cases hpq
  obtain ⟨k0, -, hlt0, hok0, -⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  obtain ⟨-, -, -, ht0, -⟩ := plain_spec hok0
  obtain ⟨-, -, -, -, -, yy, -, hyy⟩ := hdst _ ht0
  have hpa := hglob yy name abi hyy
  have hyv' : ValRel E.ι Y ((m.v (BitVec.ofNat 5 kx)).setWidth 64) := valRel_of_fvalRel hyv
  have hzv' : ValRel E.ι Z ((m.v (BitVec.ofNat 5 ky)).setWidth 64) := valRel_of_fvalRel hzv
  have hcs : 8 * n ≤ 8 * n ∨ 8 * n = 1 := .inl (Nat.le_refl _)
  have hby := (storeBytes_relN hA hn' hyv' hyf hcs).1
  have hbz := (storeBytes_relN hA hn' hzv' hzf hcs).1
  have hcan1 :
      mm.canWrite ⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt⟩ n = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inl hcan1)
  obtain ⟨hM1, hk1, hback1, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hk0 hn' hpa hyv' hyf hcs hw1
  have hcan2 : mm1.canWrite ⟨.global name.toStringLossy,
      BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n⟩ n = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨hnil', -⟩ := access_nil hM1 hpa (by omega : 0 < n) (Or.inl hcan2)
  obtain ⟨hM2, hk2, hback2, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 hn' hpa hzv' hzf hcs hw2
  have hsep1 : SepAt osp E.ι (StkAt E) mm1 := hsep0.write hk0 hw1
  have hsep2 : SepAt osp E.ι (StkAt E) mm' := hsep1.write hk1 hw2
  have hwf1 := write_wf hw1 (by rw [hby]; omega)
  have hwf2 := write_wf hw2 (by rw [hbz]; omega)
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have hword : ∀ k : Nat, k < 32 →
      ((m.v (BitVec.ofNat 5 k)).setWidth 64).toNat % 2 ^ (8 * n) =
        (m.v (BitVec.ofNat 5 k)).toNat % 2 ^ (8 * n) := by
    intro k _
    rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM2 hk2 hsep2
    (fun w hw => (hout2 w fun j hj he =>
        hsep1.not_mem hal2 hpa hw (by simp only [Blk.writableFrom]; omega) (by omega)).trans
      (hout1 w fun j hj he =>
        hsep0.not_mem hal1 hpa hw (by simp only [Blk.writableFrom]; omega) (by omega)))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, -, ht', -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf
  obtain ⟨g1, g2, -, -, g5, y', hy1, hy'⟩ := hdst _ ht'
  have hL : (Link.byId sym text az ez psA.toList).sym y' = sym yy :=
    Option.some.inj ((hglob y' name abi hy').symm.trans hpa)
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
      .ok (sym yy + BitVec.ofInt 64 v.auxInt.toInt, none) := by
    rw [ctx_mem_glob g1 g2 g5 hy1]
    exact congrArg (fun z => Except.ok (z + BitVec.ofInt 64 v.auxInt.toInt, none)) hL
  have hAn : sym yy + BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n =
      sym yy + (BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n) := BitVec.add_assoc _ _ _
  rw [progStep_fstpAt hkx hky hn48 (nextAddr_pcAt F.nodup hk) has hf hma' hnil
    (by rw [hAn]; exact hnil'), hAn, hword kx hkx, hword ky hky]

end Cases

end GoFV.Proof.Gen
