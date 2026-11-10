import GoFV.Proof.Gen.G57a
import GoFV.Proof.Gen.Spec59p

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G59, group P: float pair loads of a global or a frame variable (`docs/plans/proofs3.md` §4)

`vkind59p` (`GoFV/Gen/Check59p.lean`) accepts the `FLDPD`/`FLDPS` with an aux; `VK59p`
(`Spec59p.lean`) says what it accepted.

* `FLDPD`/`FLDPS` of a global (`g59_fldpGlob`) is G50's `FLDPD` (`stepLoc_ldPair`, `lo_loadN` at
  `n = 8` or `4`, `fvalRel_of_valRel`) at G22's address of the global's block (`pairAddr_globN`,
  `G2Env.glob`); of a frame variable in a `Blk.temp` block (`g59_fldpVar`), at G6's address
  (`pairAddr_varN`, `var_addr`). The machine (`step_fldp59`) loads the two `n`-byte elements at
  the operand's address (`ctx_mem_glob`, `ctx_mem_slot`) into the V registers.

The pair loads read valid bytes at both addresses, and no pointer at their component shapes, by
G50's run premise `PairPre50`, which states it for every `pairOp50` op with or without an aux (it
is part of `G54Pre`). The upper-bit table is empty after each (`uStep35_ldpF`). `vk59p_step` is
one value, in `vk57a_step`'s form (the frame variables' places and the globals' addresses come
from `G49Env`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The machine -/

section Progs

/-- `FLDPD`/`FLDPS` at the address `A` of its operand: two `n`-byte loads at `A` and `n` bytes
above, into V registers (`Progs50.lean`'s `eff_fldp`). -/
private theorem eff_fldp59 {c : ProgCtx} {ka kb n : Nat} {A : BitVec 64} (hka : ka < 32)
    (hkb : kb < 32) (has : c.p.as = .FLDPD ∧ n = 8 ∨ c.p.as = .FLDPS ∧ n = 4)
    (hma : c.mem c.p.from_ = .ok (A, none))
    (ht : c.p.to = pairA (REG_F0 + ka) (REG_F0 + kb)) :
    progEffect c = .ok
      { v := [(kb, (readMem c.s.mem (A + BitVec.ofNat 64 n) n).setWidth 128),
              (ka, (readMem c.s.mem A n).setWidth 128)],
        loads := [(A + BitVec.ofNat 64 n, n), (A, n)] } := by
  rcases has with ⟨has, rfl⟩ | ⟨has, rfl⟩
  · have hname : As.name .FLDPD = "FLDPD" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wV_f0 hka, eff_wV_f0 hkb]
    rfl
  · have hname : As.name .FLDPS = "FLDPS" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wV_f0 hka, eff_wV_f0 hkb]
    rfl

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `FLDPD`/`FLDPS` (`n = 8`, `4`) at an operand of address `A`, both addresses outside the nil
page: `V ka` from the `n` bytes at `A`, then `V kb` from the `n` bytes above. -/
theorem step_fldp59 {ka kb n : Nat} {A : BitVec 64} (hka : ka < 32) (hkb : kb < 32)
    (hn : L.nextAddr p.id = some next)
    (has : p.as = .FLDPD ∧ n = 8 ∨ p.as = .FLDPS ∧ n = 4)
    (hma : (ProgCtx.mk L s p).mem p.from_ = .ok (A, none))
    (ht : p.to = pairA (REG_F0 + ka) (REG_F0 + kb))
    (hnil : nilPage A = false) (hniln : nilPage (A + BitVec.ofNat 64 n) = false) :
    progStep L p s = .ok { (s.wV (BitVec.ofNat 5 ka) ((readMem s.mem A n).setWidth 128)).wV
        (BitVec.ofNat 5 kb) ((readMem s.mem (A + BitVec.ofNat 64 n) n).setWidth 128) with
      pc := next } := by
  have he := eff_fldp59 (c := ⟨L, s, p⟩) hka hkb has hma ht
  have hsk : p.isSkip = false := by
    rcases has with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [Prog.isSkip, h]
  rw [progStep_eq hn hsk he (by simp [Eff.nilAccess?, List.find?, hnil, hniln])]
  simp only [Eff.apply, List.foldr]
  rfl

end Progs

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `FLDPD`/`FLDPS sym+off(SB), (Fa, Fb)`: the two `n`-byte elements of the global at the offset,
at the global's injected address, into `V ka` and `V kb`. -/
theorem g59_fldpGlob (F : Facts lc sym text az ez psA.toList ret E)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    {ra rb : Nat} {t0 t1 : Ty} {as : As} {n : Nat}
    (hK : KLe K' (kSet (kSet K ra (some (8 * n))) rb (some (8 * n)))) (hpre : PairPre50 lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {x : AuxRef} {name : GoStr} {abi : Nat} (hop : FldpOp v.op as n)
    (hsz2 : v.args.size = 2) (hx : v.aux = some x)
    (hsy : symOf? lc.ctx.tabs x = some (name, abi))
    {oa ob : Int} (hty : lc.ty v.id = .tuple [t0, t1]) (hf0 : fTy t0 = true)
    (hf1 : fTy t1 = true) (h0 : cls t0 = some (8 * n)) (h1 : cls t1 = some (8 * n))
    (hma : memArg lc v 1 = .ok ()) (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hoa : fobjOf? ra = some oa) (hob : fobjOf? rb = some ob)
    (hvs : OneAt2 psA j
      ⟨plain as (globA g name abi v.auxInt.toInt) (· == pairA oa ob), "FLDP sym(SB)"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hpo := hop.pairOp
  have has' := hop.asN
  have hn48 : n = 4 ∨ n = 8 := by rcases has' with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ka, hka, rfl, hkka⟩ := fobjOf?_some hoa
  obtain ⟨kb, hkb, rfl, hkkb⟩ := fobjOf?_some hob
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨y, hy, rfl⟩ :=
    stepLoc_ldPair hl htemp hpo (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, q, mm2, bs, bs', hpq, hmm2, hrp, hrq, hnpp⟩ := hpre as n false true hpo a0 y ha0 hy
  rw [hmm] at hmm2
  cases hmm2
  obtain ⟨hnp0, hnp1⟩ := hnpp rfl t0 t1 hty
  rw [pairAddr_globN hx hsy] at hpq
  cases hpq
  rw [pairAddr_globN hx hsy]
  simp only [Option.elim]
  rw [hty, loadPair_tupleN (by omega), retypeL_pair,
    write_pair hh hty (by rw [h0]; rfl) (by rw [h1]; rfl)]
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, hfr, -, ht', -⟩ := plain_spec hok
  simp only [beq_iff_eq] at ht'
  obtain ⟨g1, g2, -, -, g5, yy, hy1, hyy⟩ := globA_eq hfr
  have hpa := hglob yy name abi hyy
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨hnil', -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inr (by rw [hrq]; rfl))
  obtain ⟨hty0, -⟩ := fTy_eq hf0 h0
  obtain ⟨hty1, -⟩ := fTy_eq hf1 h1
  have ht0 : t0 ≠ .bool := by rw [hty0]; nofun
  have ht1 : t1 ≠ .bool := by rw [hty1]; nofun
  have hn' : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by omega
  have hrel0 := fvalRel_of_valRel hA (valRel_retypeL_lo hA h0 ht0
      ((lo_loadN hA hMI hn' (fun _ => rfl) ht0 hpa hrp).mono (cls_le h0))) hnp0
    (fun b' => by rw [hty0]; exact retypeL_int_ne_bool _ b')
    (BitVec.setWidth_setWidth_of_le _ (by omega))
  have hrel1 := fvalRel_of_valRel hA (valRel_retypeL_lo hA h1 ht1
      ((lo_loadN hA hMI hn' (fun _ => rfl) ht1 hpa hrq).mono (cls_le h1))) hnp1
    (fun b' => by rw [hty1]; exact retypeL_int_ne_bool _ b')
    (BitVec.setWidth_setWidth_of_le _ (by omega))
  have hlm1 := locMatch_setRegV hm hkka hrel0 (b' := b) (i' := i + 1)
  have hlm2 := locMatch_setRegV hlm1 hkkb hrel1 (b' := b) (i' := i + 1)
  rw [hj'] at hlm2
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm2,
    (core_setReg (core_setReg hinv (fits_retypeL h0 _)) (fits_retypeL h1 _)).mono hK, hsi⟩
  have has'' : psA.toList[k].as = .FLDPD ∧ n = 8 ∨ psA.toList[k].as = .FLDPS ∧ n = 4 := by
    rw [has]; exact has'
  have hAn : sym yy + BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n =
      sym yy + (BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n) := BitVec.add_assoc _ _ _
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].from_ =
      .ok (sym yy + BitVec.ofInt 64 v.auxInt.toInt, none) := ctx_mem_glob g1 g2 g5 hy1
  rw [step_fldp59 hka hkb (nextAddr_pcAt F.nodup hk) has'' hma' ht' hnil
    (by rw [hAn]; exact hnil'), hAn]
  rfl

/-- `FLDPD`/`FLDPS off'(RSP), (Fa, Fb)`: the two `n`-byte elements of a frame variable in a
`Blk.temp` block at the offset, at its injected address `SP + frameOff off`, into `V ka` and
`V kb`. -/
theorem g59_fldpVar (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    {ra rb : Nat} {t0 t1 : Ty} {as : As} {n : Nat}
    (hK : KLe K' (kSet (kSet K ra (some (8 * n))) rb (some (8 * n)))) (hpre : PairPre50 lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {x : AuxRef} {off : Int} (hop : FldpOp v.op as n)
    (hsz2 : v.args.size = 2) (hx : v.aux = some x) (hvar : isVar lc x = true)
    (hf : lc.ctx.tabs.forgeable x = false)
    (hι : ∃ a, E.ι (.temp lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off))
    {oa ob : Int} (hty : lc.ty v.id = .tuple [t0, t1]) (hf0 : fTy t0 = true)
    (hf1 : fTy t1 = true) (h0 : cls t0 = some (8 * n)) (h1 : cls t1 = some (8 * n))
    (hma : memArg lc v 1 = .ok ()) (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hoa : fobjOf? ra = some oa) (hob : fobjOf? rb = some ob)
    (hvs : OneAt2 psA j ⟨plain as (slotA · .AUTO off) (· == pairA oa ob), "FLDP var"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hpo := hop.pairOp
  have has' := hop.asN
  have hn48 : n = 4 ∨ n = 8 := by rcases has' with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ka, hka, rfl, hkka⟩ := fobjOf?_some hoa
  obtain ⟨kb, hkb, rfl, hkkb⟩ := fobjOf?_some hob
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨y, hy, rfl⟩ :=
    stepLoc_ldPair hl htemp hpo (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, q, mm2, bs, bs', hpq, hmm2, hrp, hrq, hnpp⟩ := hpre as n false true hpo a0 y ha0 hy
  rw [hmm] at hmm2
  cases hmm2
  obtain ⟨hnp0, hnp1⟩ := hnpp rfl t0 t1 hty
  rw [pairAddr_varN hx hvar hf] at hpq
  cases hpq
  rw [pairAddr_varN hx hvar hf]
  simp only [Option.elim]
  rw [hty, loadPair_tupleN (by omega), retypeL_pair,
    write_pair hh hty (by rw [h0]; rfl) (by rw [h1]; rfl)]
  obtain ⟨a, hpa, haeq⟩ := hι
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨hnil', -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inr (by rw [hrq]; rfl))
  obtain ⟨hty0, -⟩ := fTy_eq hf0 h0
  obtain ⟨hty1, -⟩ := fTy_eq hf1 h1
  have ht0 : t0 ≠ .bool := by rw [hty0]; nofun
  have ht1 : t1 ≠ .bool := by rw [hty1]; nofun
  have hn' : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by omega
  have hrel0 := fvalRel_of_valRel hA (valRel_retypeL_lo hA h0 ht0
      ((lo_loadN hA hMI hn' (fun _ => rfl) ht0 hpa hrp).mono (cls_le h0))) hnp0
    (fun b' => by rw [hty0]; exact retypeL_int_ne_bool _ b')
    (BitVec.setWidth_setWidth_of_le _ (by omega))
  have hrel1 := fvalRel_of_valRel hA (valRel_retypeL_lo hA h1 ht1
      ((lo_loadN hA hMI hn' (fun _ => rfl) ht1 hpa hrq).mono (cls_le h1))) hnp1
    (fun b' => by rw [hty1]; exact retypeL_int_ne_bool _ b')
    (BitVec.setWidth_setWidth_of_le _ (by omega))
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  have hlm1 := locMatch_setRegV hm hkka hrel0 (b' := b) (i' := i + 1)
  have hlm2 := locMatch_setRegV hlm1 hkkb hrel1 (b' := b) (i' := i + 1)
  rw [hj'] at hlm2
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm2,
    (core_setReg (core_setReg hinv (fits_retypeL h0 _)) (fits_retypeL h1 _)).mono hK, hsi⟩
  obtain ⟨has, hfr, -, ht', -⟩ := plain_spec hok
  simp only [beq_iff_eq] at ht'
  have has'' : psA.toList[k].as = .FLDPD ∧ n = 8 ∨ psA.toList[k].as = .FLDPS ∧ n = 4 := by
    rw [has]; exact has'
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  have hAn : a + BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n =
      a + (BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n) := BitVec.add_assoc _ _ _
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].from_ =
      .ok (a + BitVec.ofInt 64 v.auxInt.toInt, none) := by
    rw [← hA']; exact ctx_mem_slot hfr (.inl rfl)
  rw [step_fldp59 hka hkb (nextAddr_pcAt F.nodup hk) has'' hma' ht' hnil
    (by rw [hAn]; exact hnil'), hAn]
  rfl

end Cases

/-! ## The theorem -/

/-- One value of G59's group P: it runs its one Prog and keeps the activation (`G49Env`), the
match and `G3Inv`, and empties the upper-bit table. The pair loads take G50's `PairPre50`. -/
theorem vk59p_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (_hcf : checkFrame lc g = .ok ())
    (hv : lc.ctx.f.value? id = some v) (hVK : VK59p lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (_hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (_hL : UOKL m L)
    (hpre : PairPre50 lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  have hE2 := hE.env.env.env.env.env
  have hvars := hE.env.env.env.env.vars
  have same : ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp ∧
      SlotInv lc s' → UOKL m' (uStep35 lc L v) →
      ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
        UOKL m' (uStep35 lc L v) :=
    fun m' ⟨h1, h2, h3, h4⟩ hu => ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, hu⟩
  cases hVK with
  | glob hop hsz2 hx hsy hty hf0 hf1 h0 h1 hma hh hne hoa hob =>
    have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
    obtain ⟨m', h⟩ := g59_fldpGlob (H := H) F hE2.glob hm hinv.core hinv.slots
      (kpair_kStep hnp hh hty h0 h1 hne) hpre hj hj' hop hsz2 hx hsy hty hf0 hf1 h0 h1 hma hh
      hoa hob hvs htemp hs
    refine same m' h ?_
    rw [uStep35_ldpF hop.pairOp]
    exact fun e he => by cases he
  | var hop hsz2 hfv hty hf0 hf1 h0 h1 hma hh hne hoa hob =>
    have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
    obtain ⟨m', h⟩ := g59_fldpVar (H := H) F hm hinv.core hinv.slots
      (kpair_kStep hnp hh hty h0 h1 hne) hpre hj hj' hop hsz2 hfv.aux hfv.var hfv.temp
      (var_addr hfv hv hvars) hty hf0 hf1 h0 h1 hma hh hoa hob hvs htemp hs
    refine same m' h ?_
    rw [uStep35_ldpF hop.pairOp]
    exact fun e he => by cases he

end GoFV.Proof.Gen
