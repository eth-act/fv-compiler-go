import GoFV.Proof.Gen.G21
import GoFV.Proof.Gen.Spec22

/-!
# Soundness of the genssa validator's slice G22: pair loads and stores of globals
(`docs/plans/proofs3.md` §4)

`g22_value`, `g22_term`, `g22_nilPanic`, `g22_boundsPanic`: `g21_value`'s, `g21_term`'s,
`g21_nilPanic`'s and `g21_boundsPanic`'s statements over `checkG22`.

`LDP sym+off(SB), (Ra, Rb)` and `STP (Rx, Ry), sym+off(SB)` access the global's block at the
offset and 8 bytes above (`pairAddr_glob`); the machine accesses the global's linked symbol address
plus the offset and 8 bytes above (`progStep_globLdp`, `progStep_globStp`), which the activation
injects the block at (`G2Env.glob`). The rest is G4's pair load and store (`g4_ldp`, `g4_stp`) at
that address: `g22_ldp`, `g22_stp`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The machine's pair accesses of a global -/

section Progs

/-- `LDP` at the address `A` of its operand: two 8-byte loads at `A` and 8 bytes above. -/
private theorem eff_ldp {c : ProgCtx} {ka kb : Nat} {A : BitVec 64} (hka : ka < 31)
    (hkb : kb < 31) (has : c.p.as = .LDP) (hma : c.mem c.p.from_ = .ok (A, none))
    (ht : c.p.to = pairA (REG_R0 + ka) (REG_R0 + kb)) :
    progEffect c = .ok
      { x := [(kb, c.load (A + BitVec.ofNat 64 8) 8), (ka, c.load A 8)],
        loads := [(A + BitVec.ofNat 64 8, 8), (A, 8)] } := by
  have hname : As.name .LDP = "LDP" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wX_r0 hka, eff_wX_r0 hkb]
  rfl

/-- `STP (Rx, Ry)` at the address `A` of its operand. -/
private theorem eff_stp {c : ProgCtx} {kx ky : Nat} {A : BitVec 64} (hkx : kx < 32)
    (hky : ky < 32) (has : c.p.as = .STP) (hf : c.p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky))
    (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, 8, (c.s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8)),
        (A + BitVec.ofNat 64 8, 8, (c.s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))] } := by
  have hname : As.name .STP = "STP" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_x_r0 hkx, ctx_x_r0 hky]
  rfl

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `LDP sym+off(SB), (Ra, Rb)` (a global operand: `globA_eq`; `Ra`, `Rb` not `ZR`), both
addresses outside the nil page: `Ra` from the 8 bytes at the symbol's address plus `off`, then `Rb`
from the 8 bytes above. -/
theorem progStep_globLdp {ka kb y : Nat} {off : Int} (hka : ka < 31) (hkb : kb < 31)
    (hn : L.nextAddr p.id = some next) (has : p.as = .LDP)
    (hf1 : p.from_.type = .MEM) (hf2 : p.from_.name = .EXTERN) (hf3 : p.from_.offset = off)
    (hf4 : p.from_.sym = some y) (ht : p.to = pairA (REG_R0 + ka) (REG_R0 + kb))
    (hnil : nilPage (L.sym y + BitVec.ofInt 64 off) = false)
    (hnil8 : nilPage (L.sym y + BitVec.ofInt 64 off + 8) = false) :
    progStep L p s = .ok { (s.wX (BitVec.ofNat 5 ka)
        ((readMem s.mem (L.sym y + BitVec.ofInt 64 off) 8).setWidth 64)).wX
        (BitVec.ofNat 5 kb)
        ((readMem s.mem (L.sym y + BitVec.ofInt 64 off + 8) 8).setWidth 64) with
      pc := next } := by
  have he := eff_ldp (c := ⟨L, s, p⟩) hka hkb has (ctx_mem_glob hf1 hf2 hf3 hf4) ht
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by
      have h8 : nilPage (L.sym y + BitVec.ofInt 64 off + 8#64) = false := hnil8
      simp [Eff.nilAccess?, List.find?, hnil, h8])]
  rfl

/-- `STP (Rx, Ry), sym+off(SB)` (a global operand: `globA_eq`), both addresses outside the nil
page: the 8 bytes of `X kx` at the symbol's address plus `off`, then those of `X ky` 8 bytes
above. -/
theorem progStep_globStp {kx ky y : Nat} {off : Int} (hkx : kx < 32) (hky : ky < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .STP)
    (hf : p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky))
    (ht1 : p.to.type = .MEM) (ht2 : p.to.name = .EXTERN) (ht3 : p.to.offset = off)
    (ht4 : p.to.sym = some y)
    (hnil : nilPage (L.sym y + BitVec.ofInt 64 off) = false)
    (hnil8 : nilPage (L.sym y + BitVec.ofInt 64 off + 8) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem (L.sym y + BitVec.ofInt 64 off) 8
          (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8))))
        (L.sym y + BitVec.ofInt 64 off + 8) 8
          (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))),
      pc := next } := by
  have he := eff_stp (c := ⟨L, s, p⟩) hkx hky has hf (ctx_mem_glob ht1 ht2 ht3 ht4)
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by
      have h8 : nilPage (L.sym y + BitVec.ofInt 64 off + 8#64) = false := hnil8
      simp [Eff.nilAccess?, List.find?, hnil, h8])]
  rfl

end Progs

/-- The element addresses of a pair access of a global: its block at the offset and 8 bytes
above. -/
theorem pairAddr_glob {ctx : Ctx} {v : Value} {x : AuxRef} {name : GoStr} {abi : Nat} {a : Val}
    (hx : v.aux = some x) (hs : symOf? ctx.tabs x = some (name, abi)) :
    pairAddr ctx v 8 a = some (⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt⟩,
      ⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt + 8⟩) := by
  unfold pairAddr
  rw [symAddr_global hs hx,
    symAddr_global (v := { v with auxInt := v.auxInt + Int64.ofNat 8 }) hs hx]
  simp only [Option.bind_some, Option.map_some, ofInt_add8]

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `LDP sym+off(SB), (Ra, Rb)`: the two 8-byte words of the global at the offset, at the global's
injected address. -/
theorem g22_ldp (F : Facts lc sym text az ez psA.toList ret E)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    {ra rb : Nat} {t0 t1 : Ty} {c0 c1 : Nat}
    (hK : KLe K' (kSet (kSet K ra (some c0)) rb (some c1))) (hpre : G4Pre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {x : AuxRef} {name : GoStr} {abi : Nat} (hx : v.aux = some x)
    (hsy : symOf? lc.ctx.tabs x = some (name, abi))
    {oa ob : Int} (hop : v.op = .ARM64LDP) (hsz2 : v.args.size = 2)
    (hty : lc.ty v.id = .tuple [t0, t1]) (h0 : cls t0 = some c0) (h1 : cls t1 = some c1)
    (h80 : 8 ≤ c0) (h81 : 8 ≤ c1) (hma : memArg lc v 1 = .ok ())
    (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hza : ra ≠ zeroReg) (hzb : rb ≠ zeroReg) (hda : destOK ra = true) (hdb : destOK rb = true)
    (hoa : objOf? ra = some oa) (hob : objOf? rb = some ob)
    (hvs : OneAt2 psA j
      ⟨plain .LDP (globA g name abi v.auxInt.toInt) (· == pairA oa ob), "LDP sym(SB)"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧
      PairW ra rb m m' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ka, hka, rfl, hkka⟩ := objOf?_some hoa
  obtain ⟨kb, hkb, rfl, hkkb⟩ := objOf?_some hob
  have hka' : ka < 31 := by
    rcases hkka with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hza
    · exact h
  have hkb' : kb < 31 := by
    rcases hkkb with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hzb
    · exact h
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨y, hy, rfl⟩ :=
    stepLoc_ldp hl htemp hop (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, q, mm2, bs, bs', hpq, hmm2, hrp, hrq⟩ := hpre.2 hop a0 y ha0 hy
  rw [hmm] at hmm2
  cases hmm2
  rw [pairAddr_glob hx hsy] at hpq
  cases hpq
  rw [pairAddr_glob hx hsy]
  simp only [Option.elim]
  rw [hty, loadPair_tuple, retypeL_pair, write_pair hh hty (by rw [h0]; rfl) (by rw [h1]; rfl)]
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, hf1, -, ht', -⟩ := plain_spec hok
  simp only [beq_iff_eq] at ht'
  obtain ⟨g1, g2, -, -, g5, yy, hy1, hyy⟩ := globA_eq hf1
  have hpa := hglob yy name abi hyy
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < 8) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨hnil', -⟩ := access_nil hMI hpa (by omega : 0 < 8) (Or.inr (by rw [hrq]; rfl))
  have ht0 := cls_ne_bool h0 h80
  have ht1 := cls_ne_bool h1 h81
  have hrel0 : ValRel E.ι ((Arm64.loadN t0 8 false mm
        ⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt⟩).retypeL t0)
      ((readMem m.mem (sym yy + BitVec.ofInt 64 v.auxInt.toInt) 8).setWidth 64) :=
    valRel_retypeL_lo hA h0 ht0 ((lo_loadN hA hMI (by simp) (fun _ => rfl) ht0 hpa hrp).mono
      (cls_le h0))
  have hrel1 : ValRel E.ι ((Arm64.loadN t1 8 false mm
        ⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt + 8⟩).retypeL t1)
      ((readMem m.mem (sym yy + (BitVec.ofInt 64 v.auxInt.toInt + 8)) 8).setWidth 64) :=
    valRel_retypeL_lo hA h1 ht1 ((lo_loadN hA hMI (by simp) (fun _ => rfl) ht1 hpa hrq).mono
      (cls_le h1))
  obtain ⟨hlm1, hinv1⟩ := finish_reg hm hinv hda (by omega : ka < 32) hoa hrel0
    (fits_retypeL h0 _) (b' := b) (i' := i + 1)
  obtain ⟨hlm2, hinv2⟩ := finish_reg hlm1 hinv1 hdb (by omega : kb < 32) hob hrel1
    (fits_retypeL h1 _) (b' := b) (i' := i + 1)
  rw [hj'] at hlm2
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm2, hinv2.mono hK, hsi, ka, kb,
    (readMem m.mem (sym yy + BitVec.ofInt 64 v.auxInt.toInt) 8).setWidth 64,
    (readMem m.mem (sym yy + (BitVec.ofInt 64 v.auxInt.toInt + 8)) 8).setWidth 64, hoa, hob,
    by simp only [wX_pc]⟩
  have hL : (Link.byId sym text az ez psA.toList).sym yy = sym yy := rfl
  have hA8 : sym yy + BitVec.ofInt 64 v.auxInt.toInt + 8 =
      sym yy + (BitVec.ofInt 64 v.auxInt.toInt + 8) := BitVec.add_assoc _ _ _
  rw [progStep_globLdp hka' hkb' (nextAddr_pcAt F.nodup hk) has g1 g2 g5 hy1 ht'
    (by rw [hL]; exact hnil) (by rw [hL, hA8]; exact hnil'), hL, hA8]
  simp only [wX_pc]

/-- `STP (Rx, Ry), sym+off(SB)` of two 64-bit registers: the two 8-byte stores into the global's
block, at its injected address. -/
theorem g22_stp (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {x : AuxRef} {name : GoStr} {abi : Nat} {rx ry : Int} (hop : v.op = .ARM64STP)
    (hx : v.aux = some x) (hsy : symOf? lc.ctx.tabs x = some (name, abi))
    (hsz4 : v.args.size = 4) (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hxo : argObj lc v 1 = .ok (64, rx)) (hyo : argObj lc v 2 = .ok (64, ry))
    (hma : memArg lc v 3 = .ok ())
    (hvs : OneAt2 psA j
      ⟨plain .STP (· == pairA rx ry) (globA g name abi v.auxInt.toInt), "STP sym(SB)"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec hyo
  obtain ⟨kx, hkx, rfl, hkkx⟩ := objOf?_some hor1
  obtain ⟨ky, hky, rfl, hkky⟩ := objOf?_some hor2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkx
  obtain ⟨Z, hZ, hzv, hzf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkky
  obtain ⟨x', y, z, p, q, mm1, mm', -, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_stp hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  rw [pairAddr_glob hx hsy] at hpq
  cases hpq
  obtain ⟨k0, -, hlt0, hok0, -⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  obtain ⟨-, -, -, ht0, -⟩ := plain_spec hok0
  obtain ⟨-, -, -, -, -, yy, -, hyy⟩ := globA_eq ht0
  have hpa := hglob yy name abi hyy
  have hby := (storeBytes_relN hA (n := 8) (by simp) hyv hyf (Or.inl (Nat.le_refl _))).1
  have hbz := (storeBytes_relN hA (n := 8) (by simp) hzv hzf (Or.inl (Nat.le_refl _))).1
  have hcan1 : mm.canWrite ⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt⟩ 8 = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < 8) (Or.inl hcan1)
  obtain ⟨hM1, hk1, hback1, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hk0 (by simp) hpa hyv hyf (Or.inl (Nat.le_refl _)) hw1
  have hcan2 :
      mm1.canWrite ⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt + 8⟩ 8 = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨hnil', -⟩ := access_nil hM1 hpa (by omega : 0 < 8) (Or.inl hcan2)
  obtain ⟨hM2, hk2, hback2, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 (by simp) hpa hzv hzf (Or.inl (Nat.le_refl _)) hw2
  have hsep1 : SepFrom E.ι (StkAt E) mm1 := by
    intro b2 al a2 hb hι w hw
    obtain ⟨al0, hb0, hs0⟩ := hback1 b2 al hb
    rw [← hs0]; exact hsep0 b2 al0 a2 hb0 hι w hw
  have hsep2 : SepFrom E.ι (StkAt E) mm' := by
    intro b2 al a2 hb hι w hw
    obtain ⟨al0, hb0, hs0⟩ := hback2 b2 al hb
    rw [← hs0]; exact hsep1 b2 al0 a2 hb0 hι w hw
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM2 hk2 hsep2
    (fun w hw => (hout2 w fun j hj he => hsep1 _ _ _ hal2 hpa w hw ⟨by omega, by omega⟩).trans
      (hout1 w fun j hj he => hsep0 _ _ _ hal1 hpa w hw ⟨by omega, by omega⟩))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, -, ht', -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf
  obtain ⟨g1, g2, -, -, g5, y', hy1, hy'⟩ := globA_eq ht'
  have hL : (Link.byId sym text az ez psA.toList).sym y' = sym yy :=
    Option.some.inj ((hglob y' name abi hy').symm.trans hpa)
  have hA8 : sym yy + BitVec.ofInt 64 v.auxInt.toInt + 8 =
      sym yy + (BitVec.ofInt 64 v.auxInt.toInt + 8) := BitVec.add_assoc _ _ _
  rw [progStep_globStp hkx hky (nextAddr_pcAt F.nodup hk) has hf g1 g2 g5 hy1
    (by rw [hL]; exact hnil) (by rw [hL, hA8]; exact hnil'), hL, hA8]
  rfl

end Cases

/-! ## The theorems -/

/-- One value of G22's kinds: `vk21_step`'s statement. -/
theorem vk22_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK22 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s)
    (hu : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        UOK m (some (r, c, lc.signOf lc.ctx.f.valueTab.size x)))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZ H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOK H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧ UOK m' (uEntry lc v) := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨hlcE, -, -, -, -, hglob, -, -, -, -, hF⟩, -⟩, -⟩, -⟩ := hE
  cases hVK with
  | g21 _ hVK21 =>
    exact vk21_step hE0 F hhome hcf hv hVK21 hvs htemp hj hj' hreads hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hs
  | ldp hop hx _ _ hsy hsz2 hty h0 h1 h80 h81 hma hh hne hza hzb hda hdb hoa hob =>
    have hue : uEntry lc v = none := by
      have : narrowLd? lc v = none := by unfold narrowLd?; rw [hop]; rfl
      simp only [uEntry, this]
    rw [hue]
    obtain ⟨m', h1', h2', h3', h4', -⟩ := g22_ldp (H := H) F hglob hm hinv.core hinv.slots
      (kpair_kStep (by rw [hop]; nofun) hh hty h0 h1 hne) hpre.1.1.1 hj hj' hx hsy hop hsz2 hty
      h0 h1 h80 h81 hma hh hza hzb hda hdb hoa hob hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1', h2', ⟨h3', h4'⟩, trivial⟩
  | stp hop hx _ _ hsy hsz4 hmt hhn hxo hyo hma =>
    have hue : uEntry lc v = none := by
      have : narrowLd? lc v = none := by unfold narrowLd?; rw [hop]; rfl
      simp only [uEntry, this]
    rw [hue]
    have hsz := slot_sizes hlcE hcf hinv.slots
    obtain ⟨m', h1', h2', h3', h4'⟩ := g22_stp (H := H) F hF hsz hglob hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hx hsy hsz4
      hmt hhn hxo hyo hma hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1', h2', ⟨h3', h4'⟩, trivial⟩

/-- **G22, values.** `g21_value`'s statement over `checkG22`. -/
theorem g22_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG22 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOK m (uAt lc blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOK m' (uAt lc blk (i + 1)) := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd⟩ :=
    checkG22_spec hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨htemp, hVK⟩ := vkind22_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hu1 : uAt c.cx.lc blk (i + 1) = uEntry c.cx.lc v := by simp [uAt, hi, hv]
  rw [kAt_succ hi hv, hu1]
  exact vk22_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv
    (fun x hop hx => by
      obtain ⟨r, c', hr, hc', hu0⟩ := movdOK_spec hmovd hbid hb hi hv hop hx
      exact ⟨r, c', hr, hc', hu0 ▸ hu⟩)
    hpre hcall hcallz hicall hwb hclo hgetg hs

/-- A nil check of G22's kinds is G7's. -/
theorem vk22_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK22 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g21 _ h => exact vk21_nil h hop
  | ldp hop' => rw [hop] at hop'; cases hop'
  | stp hop' => rw [hop] at hop'; cases hop'

/-- **G22, nil panics.** `g21_nilPanic`'s statement over `checkG22`. -/
theorem g22_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG22 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG22_spec hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨-, hVK⟩ := vkind22_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk22_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G22, bounds panics.** `g21_boundsPanic`'s statement over `checkG22`, under `BoundsOK`. -/
theorem g22_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG22 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -⟩ :=
    checkG22_spec hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  have hen : entryOp3 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  obtain ⟨-, hVK⟩ := vkind22_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | ldp hop' => rw [hop'] at hop; cases hop
  | stp hop' => rw [hop'] at hop; cases hop
  | g21 _ hVK21 =>
    cases hVK21 with
    | regSame hop' => rw [hop'] at hop; cases hop
    | regMov hop' => rw [hop'] at hop; cases hop
    | g20 _ hVK20 =>
      cases hVK20 with
      | nop hop' => rw [hop'] at hop; cases hop
      | g19 _ hVK19 =>
        exact vk19_boundsPanic F hsyms hpb hrow hb hi hv hVK19 hvs hj hreads hop hm hinv hbok hs

/-- **G22, terminators.** `g21_term`'s statement over `checkG22`. -/
theorem g22_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG22 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG22_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
