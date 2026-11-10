import GoFV.Proof.Gen.G5
import GoFV.Proof.Gen.Spec6

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G6: frame variables (`docs/plans/proofs3.md` §4)

`g6_value`: when `checkG6` accepts a function with the class table `kt`, every value of a block
(other than the entry values) run by `runLoc` from a state related by `LocMatch` to a machine
state, whose registers hold values of the classes the table gives before that value (`G3Inv` at
`kAt lc kt b blk i`), is matched by `runProg` steps of genssa's P0 Progs to a state related before
the next value, with the registers at the classes before the next value. `g6_term`: a terminator
that goes to a successor is matched by steps to a state related before the successor's first
value, with the registers at the classes of the successor's start (`kt.at`).

The activation is `G6Env`: G2's (`G2Env`), and each frame variable the function accesses
(`accessedVars`, of a `NAME_AUTO` operand, not converted to an integer: its block is `Blk.temp`)
at its frame operand `SP + frameOff` under the injection (`VarsAt`). `AddrAgree` leaves frame
temporaries free (`Rel.lean`), so this placement is consistent with it. The invariant and the
per-value premises are G4's (`G3Inv`, `G4Pre`). G5's values go through `vk5_step`; G6's own are the
address of a variable (`g6_addr`: `MOVD $off(RSP), Rd`, the pointer to the variable's block, a
`PtrRel` to `SP + frameOff`), its loads and stores (`g6_load`, `g6_store`) and pair loads and
stores (`g6_ldp`, `g6_stp`), each at the variable's injected address (`var_addr`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## The activation -/

/-- The current activation's accessed frame variables (`accessedVars`) at their `NAME_AUTO`
operands: the block `Blk.temp act x` of each one whose address the function does not convert to
an integer at `SP + frameOff`. -/
def VarsAt (lc : LocCtx) (g : G2In) (L : Link) (E : MatchEnv) : Prop :=
  ∀ x ∈ accessedVars lc, ∀ o, varOp g x = some (.AUTO, o) → lc.ctx.tabs.forgeable x = false →
    E.ι (.temp lc.ctx.act x) = some (E.sp + BitVec.ofInt 64 (frameOff L .AUTO o))

/-- The activation of a function `checkG6` accepted with table `tab`: G2's, and the frame
variables at their frame operands. -/
structure G6Env (lc : LocCtx) (g : G2In) (L : Link) (ps : Array Prog) (ret : BitVec 64)
    (tab : PcTab) (E : MatchEnv) : Prop where
  env : G2Env lc g L ps ret tab E
  vars : VarsAt lc g L E

/-- An activation whose injection extends `E`'s keeps the frame variables' places. -/
theorem VarsAt.extend {lc : LocCtx} {g : G2In} {L : Link} {E E' : MatchEnv}
    (h : VarsAt lc g L E) (hx : E.Extends E') : VarsAt lc g L E' := by
  intro x hx' o ho hf
  have hsp : E'.sp = E.sp := by rw [hx.1]
  rw [hsp]
  exact hx.2 _ _ (h x hx' o ho hf)

/-- A variable a value of the function accesses is an accessed variable. -/
theorem mem_accessedVars {lc : LocCtx} {id : ID} {v : Value} {x : AuxRef}
    (hv : lc.ctx.f.value? id = some v) (hx : v.aux = some x) (hvar : isVar lc x = true)
    (hsp : spArg lc v = true) : x ∈ accessedVars lc := by
  unfold accessedVars
  rw [List.mem_eraseDups]
  have h1 : lc.ctx.f.valueTab[id]? = some (some v) := by
    have hv' : (lc.ctx.f.valueTab[id]?).join = some v := hv
    cases h : lc.ctx.f.valueTab[id]? with
    | none => rw [h] at hv'; cases hv'
    | some o => rw [h] at hv'; cases o <;> simp_all
  refine List.mem_filterMap.2 ⟨some v, Array.mem_toList_iff.2 (Array.mem_of_getElem? h1), ?_⟩
  simp [hx, hvar, hsp]

/-- The address of an access of a frame variable not converted to an integer: its `temp` block at
the access's offset (the base argument is ignored). -/
theorem symAddr_var {lc : LocCtx} {v : Value} {x : AuxRef} {a : Val} (hx : v.aux = some x)
    (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = false) :
    symAddr lc.ctx v a = some ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩ := by
  unfold isVar at hvar
  unfold symAddr
  rw [hx]
  split at hvar
  · rename_i heq
    simp only [heq, frameBlk_temp hf]
  · cases hvar

/-- The element addresses of a pair access of a frame variable: its `temp` block at the offset and
8 bytes above. -/
theorem pairAddr_var {lc : LocCtx} {v : Value} {x : AuxRef} {a : Val} (hx : v.aux = some x)
    (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = false) :
    pairAddr lc.ctx v 8 a = some (⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩,
      ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt + 8⟩) := by
  unfold pairAddr
  rw [symAddr_var hx hvar hf,
    symAddr_var (v := { v with auxInt := v.auxInt + Int64.ofNat 8 }) hx hvar hf]
  simp only [Option.bind_some, Option.map_some, ofInt_add8]

/-- A `NAME_AUTO` frame offset moved by `k`. -/
theorem frameOff_add (L : Link) (o k : Int) :
    BitVec.ofInt 64 (frameOff L .AUTO (o + k)) =
      BitVec.ofInt 64 (frameOff L .AUTO o) + BitVec.ofInt 64 k := by
  rw [show frameOff L .AUTO (o + k) = frameOff L .AUTO o + k by simp only [frameOff]; omega,
    BitVec.ofInt_add]

/-- An access of an accessed frame variable at the operand offset `off`: its block's injected
address plus the access's offset is `SP + frameOff off`. -/
theorem var_addr {lc : LocCtx} {g : G2In} {L : Link} {E : MatchEnv} {id : ID} {v : Value}
    {x : AuxRef} {off : Int} (hfv : FrameVarOK lc g v x off) (hv : lc.ctx.f.value? id = some v)
    (hvars : VarsAt lc g L E) :
    ∃ a, E.ι (.temp lc.ctx.act x) = some a ∧
      a + BitVec.ofInt 64 v.auxInt.toInt = E.sp + BitVec.ofInt 64 (frameOff L .AUTO off) := by
  obtain ⟨o, ho, rfl⟩ := hfv.op
  refine ⟨_, hvars x (mem_accessedVars hv hfv.aux hfv.var hfv.sp) o ho hfv.temp, ?_⟩
  rw [frameOff_add, BitVec.add_assoc]

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `MOVDaddr` of a frame variable not converted to an integer: the pointer to its `temp` block at
the offset, at the value's shape. -/
theorem stepLoc_addrVar (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64MOVDaddr) {a : ID} {x : AuxRef} (ha : v.args = #[a]) (hx : v.aux = some x)
    (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = false)
    (h : stepLoc env lc s v = .ok s') :
    s' = s.write lc v.id ((PtrOps.ptrRes ⟨.temp lc.ctx.act x,
      BitVec.ofInt 64 v.auxInt.toInt⟩).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hm
  change ((s.read lc a).bind fun x => Res.ok [x]) = _ at hm
  cases hy : s.read lc a with
  | ok y =>
    rw [hy] at hm; cases hm
    have he : evalOpL true env lc.ctx s.fr v [y] (lc.ty v.id) =
        match nilFaults true lc.ctx v [y] with
        | some m => .panic .nilDeref m
        | none => .ok ((symAddr lc.ctx v y).elim .poison PtrOps.ptrRes) := by
      unfold evalOpL arm64Op; rw [hop]; rfl
    rw [he] at hr
    split at hr
    · cases hr
    · cases hr
      rw [symAddr_var hx hvar hf]
      rfl
  | panic e m => rw [hy] at hm; cases hm
  | stuck msg => rw [hy] at hm; cases hm

end Step

/-! ## One access of a frame variable -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}
  {x : AuxRef} {off : Int}

/-- `MOVD $off(RSP), Rd`: the address of a frame variable. -/
theorem g6_addr (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = false)
    (hι : ∃ a, E.ι (.temp lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off))
    {a0 : ID} {rd : Int} (hop : v.op = .ARM64MOVDaddr) (hsz1 : v.args.size = 1)
    (ha0 : v.args[0]? = some a0) (hro : resObj lc v = .ok (64, rd))
    (hvs : OneAt2 psA j ⟨plain .MOVD (addrA · off) (· == regA rd), "MOVD $var"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨a, hpa, haeq⟩ := hι
  rw [stepLoc_addrVar hl htemp hop (arr1 hsz1 ha0) hx hvar hf hs, write_reg hvh hcv]
  have hrel : ValRel E.ι (PtrOps.ptrRes ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩)
      (E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off)) := by
    unfold PtrOps.ptrRes
    split
    · exact valRel_word hA ⟨a, hpa, haeq.symm⟩
    · trivial
  have hfit : Fits 64 (PtrOps.ptrRes ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩) := by
    unfold PtrOps.ptrRes; split
    · exact fits_word _
    · trivial
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL hA hcv hfit hrel) (fits_retypeL hcv _)
    (knext_set hK (by rw [hop]; nofun) hvh hcv)
    (fun k0 hk0 hok => ?_)).imp fun m' ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf1, -, ht, -⟩ := plain_spec hok
  simp only [addrA, Bool.and_eq_true, beq_iff_eq] at hf1
  simp only [beq_iff_eq] at ht
  have hsp : m.sp = E.sp := hm.frame.1
  rw [← hsp, progStep_slotAddr hkd (nextAddr_pcAt F.nodup hk0) has hf1.1 hf1.2 (.inl rfl) ht, wX_pc]

/-- A load of `n` bytes of a frame variable at `off(RSP)`, with the registers of the machine after
the load: the zero or sign extension of the `n` loaded bytes written to `X[kd]`, `rd = R0 + kd`. -/
theorem g6_load (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K') (hpre : G3Pre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = false)
    (hι : ∃ a, E.ι (.temp lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off))
    {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int}
    (hop : loadOp? v.op = some (as, n, sg)) (hsz2 : v.args.size = 2)
    (hma : memArg lc v 1 = .ok ()) (hro : resObj lc v = .ok (c, rd))
    (hc : 8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false)
    (hvs : OneAt2 psA j ⟨plain as (slotA · .AUTO off) (· == regA rd), as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      ∃ (kd : Nat) (Y : BitVec (8 * n)), rd = GoFV.Asm.ARM64.REG_R0 + kd ∧
        m'.x = (m.wX (BitVec.ofNat 5 kd)
          (if sg then ProgOp.sextTo64 n (Y.setWidth 64) else Y.setWidth 64)).x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp := loadOp?_ne_phi hop
  obtain ⟨hn, hsg⟩ := loadOp?_bytes hop
  have hmov := loadOp?_movMem hop
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨y, hy, rfl⟩ := stepLoc_loadN hl htemp hop (arr2 hsz2 ha0 ha1)
    (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, mm2, bs, hsym, hmm2, hrd, h01⟩ := hpre.2.1 _ _ _ hop a0 y ha0 hy
  rw [hmm] at hmm2
  cases hmm2
  rw [symAddr_var hx hvar hf] at hsym
  cases hsym
  rw [write_reg hvh hcv, symAddr_var hx hvar hf]
  simp only [Option.elim]
  obtain ⟨a, hpa, haeq⟩ := hι
  have hval : ValRel E.ι ((Arm64.loadN (lc.ty v.id) n sg mm
        ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩).retypeL (lc.ty v.id))
      (if sg then ProgOp.sextTo64 n
          ((readMem m.mem (a + BitVec.ofInt 64 v.auxInt.toInt) n).setWidth 64)
       else (readMem m.mem (a + BitVec.ofInt 64 v.auxInt.toInt) n).setWidth 64) := by
    rcases hc with h8 | ⟨rfl, rfl, rfl⟩
    · have ht := cls_ne_bool hcv h8
      exact valRel_retypeL_lo hA hcv ht ((lo_loadN hA hMI hn hsg ht hpa hrd).mono (cls_le hcv))
    · have ht := cls_bool hcv
      rw [ht]
      exact valRel_loadBool hA hMI hpa hrd (h01 ht)
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inr (by rw [hrd]; rfl))
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor hval (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k1 hk1 hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, kd, _, rfl, h4⟩
  obtain ⟨has, hf1, -, ht', -⟩ := plain_spec hok
  simp only [beq_iff_eq] at ht'
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  rw [progStep_slotLoadN hkd (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf1 (.inl rfl)
    ht' (by rw [hA']; exact hnil), hA', wX_pc]

/-- A store of `n` bytes to a frame variable at `off(RSP)`, outside the frame's saved words and
slots. -/
theorem g6_store (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = false)
    (hι : ∃ a, E.ι (.temp lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off))
    {as : As} {n cs : Nat} {rs : Int}
    (hop : storeOp? v.op = some (as, n)) (hsz3 : v.args.size = 3)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hso : argObj lc v 1 = .ok (cs, rs)) (hma : memArg lc v 2 = .ok ())
    (hc : 8 * n ≤ cs ∨ cs = 1 ∧ n = 1)
    (hvs : OneAt2 psA j ⟨plain as (· == regA rs) (slotA · .AUTO off), as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp := storeOp?_ne_phi hop
  have hn := storeOp?_bytes hop
  obtain ⟨sg, hmov⟩ := storeOp?_movMem hop
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hso
  obtain ⟨ks, hks, rfl, hkks⟩ := objOf?_some hor1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkks
  obtain ⟨x', y', p, mm', hx', hy', hsym, hw, rfl⟩ := stepLoc_storeN hl htemp hop
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hy] at hy'
  cases hy'
  rw [symAddr_var hx hvar hf] at hsym
  cases hsym
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  have hcs : 8 * n ≤ cs ∨ cs = 1 := hc.imp_right And.left
  have hbs := (storeBytes_relN hA hn hyv hyf hcs).1
  have hcan : mm.canWrite ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩ n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨a, hpa, haeq⟩ := hι
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inl hcan)
  obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hk0 hn hpa hyv hyf hcs hw
  have hsep' : SepAt osp E.ι (StkAt E) mm' := hsep0.write hk0 hw
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM' hk' hsep'
    (fun y hy => hout y fun j hj he =>
      hsep0.not_mem hal hpa hy (by simp only [Blk.writableFrom]; omega) (by omega))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k1 hk1 hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf1, -, ht1, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf1
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  rw [progStep_slotStoreN hks (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf1 ht1
    (.inl rfl) (by rw [hA']; exact hnil), hA']
  rfl

/-- `LDP off(RSP), (Ra, Rb)`: the 8 bytes of a frame variable at the offset into `Ra`, the 8 bytes
above into `Rb`. -/
theorem g6_ldp (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    {ra rb : Nat} {t0 t1 : Ty} {c0 c1 : Nat}
    (hK : KLe K' (kSet (kSet K ra (some c0)) rb (some c1))) (hpre : G4Pre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = false)
    (hι : ∃ a, E.ι (.temp lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off))
    {oa ob : Int} (hop : v.op = .ARM64LDP) (hsz2 : v.args.size = 2)
    (hty : lc.ty v.id = .tuple [t0, t1]) (h0 : cls t0 = some c0) (h1 : cls t1 = some c1)
    (h80 : 8 ≤ c0) (h81 : 8 ≤ c1) (hma : memArg lc v 1 = .ok ())
    (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hza : ra ≠ zeroReg) (hzb : rb ≠ zeroReg) (hda : destOK ra = true) (hdb : destOK rb = true)
    (hoa : objOf? ra = some oa) (hob : objOf? rb = some ob)
    (hvs : OneAt2 psA j ⟨plain .LDP (slotA · .AUTO off) (· == pairA oa ob), "LDP"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
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
  rw [pairAddr_var hx hvar hf] at hpq
  cases hpq
  rw [pairAddr_var hx hvar hf]
  simp only [Option.elim]
  rw [hty, loadPair_tuple, retypeL_pair, write_pair hh hty (by rw [h0]; rfl) (by rw [h1]; rfl)]
  obtain ⟨a, hpa, haeq⟩ := hι
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < 8) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨hnil', -⟩ := access_nil hMI hpa (by omega : 0 < 8) (Or.inr (by rw [hrq]; rfl))
  have ht0 := cls_ne_bool h0 h80
  have ht1 := cls_ne_bool h1 h81
  have hrel0 : ValRel E.ι ((Arm64.loadN t0 8 false mm
        ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩).retypeL t0)
      ((readMem m.mem (a + BitVec.ofInt 64 v.auxInt.toInt) 8).setWidth 64) :=
    valRel_retypeL_lo hA h0 ht0 ((lo_loadN hA hMI (by simp) (fun _ => rfl) ht0 hpa hrp).mono
      (cls_le h0))
  have hrel1 : ValRel E.ι ((Arm64.loadN t1 8 false mm
        ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt + 8⟩).retypeL t1)
      ((readMem m.mem (a + (BitVec.ofInt 64 v.auxInt.toInt + 8)) 8).setWidth 64) :=
    valRel_retypeL_lo hA h1 ht1 ((lo_loadN hA hMI (by simp) (fun _ => rfl) ht1 hpa hrq).mono
      (cls_le h1))
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨hlm1, hinv1⟩ := finish_reg hm hinv hda (by omega : ka < 32) hoa hrel0
    (fits_retypeL h0 _) (b' := b) (i' := i + 1)
  obtain ⟨hlm2, hinv2⟩ := finish_reg hlm1 hinv1 hdb (by omega : kb < 32) hob hrel1
    (fits_retypeL h1 _) (b' := b) (i' := i + 1)
  rw [hj'] at hlm2
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm2, hinv2.mono hK, hsi, ka, kb,
    (readMem m.mem (a + BitVec.ofInt 64 v.auxInt.toInt) 8).setWidth 64,
    (readMem m.mem (a + (BitVec.ofInt 64 v.auxInt.toInt + 8)) 8).setWidth 64, hoa, hob,
    by simp only [wX_pc]⟩
  obtain ⟨has, hf1, -, ht', -⟩ := plain_spec hok
  simp only [beq_iff_eq] at ht'
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  have hA8 : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off) + 8 =
      a + (BitVec.ofInt 64 v.auxInt.toInt + 8) := by rw [hA', BitVec.add_assoc]
  rw [progStep_slotLdp hka' hkb' (nextAddr_pcAt F.nodup hk) has hf1 (.inl rfl) ht'
    (by rw [hA']; exact hnil) (by rw [hA8]; exact hnil'), hA8, hA']
  simp only [wX_pc]

/-- `STP (Rx, Ry), off(RSP)`: the 8 bytes of `Rx` at a frame variable's offset, those of `Ry` 8
bytes above, outside the frame's saved words and slots. -/
theorem g6_stp (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = false)
    (hι : ∃ a, E.ι (.temp lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off))
    {rx ry : Int} (hop : v.op = .ARM64STP) (hsz4 : v.args.size = 4)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hxo : argObj lc v 1 = .ok (64, rx)) (hyo : argObj lc v 2 = .ok (64, ry))
    (hma : memArg lc v 3 = .ok ())
    (hvs : OneAt2 psA j ⟨plain .STP (· == pairA rx ry) (slotA · .AUTO off), "STP"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
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
  rw [pairAddr_var hx hvar hf] at hpq
  cases hpq
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨a, hpa, haeq⟩ := hι
  have hby := (storeBytes_relN hA (n := 8) (by simp) hyv hyf (Or.inl (Nat.le_refl _))).1
  have hbz := (storeBytes_relN hA (n := 8) (by simp) hzv hzf (Or.inl (Nat.le_refl _))).1
  have hcan1 : mm.canWrite ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩ 8 = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < 8) (Or.inl hcan1)
  obtain ⟨hM1, hk1, hback1, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hk0 (by simp) hpa hyv hyf (Or.inl (Nat.le_refl _)) hw1
  have hcan2 : mm1.canWrite ⟨.temp lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt + 8⟩ 8 = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨hnil', -⟩ := access_nil hM1 hpa (by omega : 0 < 8) (Or.inl hcan2)
  obtain ⟨hM2, hk2, hback2, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 (by simp) hpa hzv hzf (Or.inl (Nat.le_refl _)) hw2
  have hsep1 : SepAt osp E.ι (StkAt E) mm1 := hsep0.write hk0 hw1
  have hsep2 : SepAt osp E.ι (StkAt E) mm' := hsep1.write hk1 hw2
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  have hA8 : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) .AUTO off) + 8 =
      a + (BitVec.ofInt 64 v.auxInt.toInt + 8) := by rw [hA', BitVec.add_assoc]
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM2 hk2 hsep2
    (fun w hw => (hout2 w fun j hj he =>
        hsep1.not_mem hal2 hpa hw (by simp only [Blk.writableFrom]; omega) (by omega)).trans
      (hout1 w fun j hj he =>
        hsep0.not_mem hal1 hpa hw (by simp only [Blk.writableFrom]; omega) (by omega)))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf1, -, ht1, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf1
  rw [progStep_slotStp hkx hky (nextAddr_pcAt F.nodup hk) has hf1 ht1 (.inl rfl)
    (by rw [hA']; exact hnil) (by rw [hA8]; exact hnil'), hA8, hA']
  rfl

end Cases

/-! ## The theorems -/

/-- One value of G6's kinds (`VK6`) emitted at the Progs from `j` to `j'`: `vk5_step`'s statement
for G6's values under `G6Env`. -/
theorem vk6_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G6Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hns : CallsNotSlot lc)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK6 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hpre : G4Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G6Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp := by
  obtain ⟨hE2, hvars⟩ := hE
  have hE0 := hE2
  obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE2
  have hR := kread_of_reads hreads
  have hsz := slot_sizes hlcE hcf hinv.slots
  have same : ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp ∧
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G6Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp :=
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨E, m', ⟨rfl, fun _ _ h => h⟩, ⟨hE0, hvars⟩, h1, h2, ⟨h3, h4⟩⟩
  cases hVK with
  | g5 hVK5 =>
    obtain ⟨E', m', hx, hE', h⟩ :=
      vk5_step hE0 F hns hcf hv hVK5 hvs htemp hj hj' hreads hm hinv hpre hcall hs
    exact ⟨E', m', hx, ⟨hE', hvars.extend hx⟩, h⟩
  | var hfv hVar =>
    have hι := var_addr hfv hv hvars
    have hx := hfv.aux
    have hvar := hfv.var
    have hf := hfv.temp
    cases hVar with
    | addr hop hsz1 hro =>
      obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
        ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
      obtain ⟨m', h1, h2, h3, h4, -⟩ := g6_addr (H := H) F hm hinv.core hinv.slots
        (knext_kStep fun _ => (hs_res hro).noRegs) hj hj' hx hvar hf hι hop hsz1 ha0 hro hvs
        htemp hs
      exact same m' ⟨h1, h2, h3, h4⟩
    | load hop hsz2 hma hro hc =>
      obtain ⟨m', h1', h2', h3', h4', -⟩ := g6_load (H := H) F hm hinv.core hinv.slots
        (knext_kStep fun _ => (hs_res hro).noRegs) hpre.1 hj hj' hx hvar hf hι hop hsz2 hma hro
        hc hvs htemp hs
      exact same m' ⟨h1', h2', h3', h4'⟩
    | store hop hsz3 hmt hhn hso hma hc =>
      obtain ⟨m', h⟩ := g6_store (H := H) F hF hsz hm hinv.core hinv.slots hR
        (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hx hvar hf hι hop hsz3 hmt hhn hso
        hma hc hvs htemp hs
      exact same m' h
    | ldp hop hsz2 hty h0 h1 h80 h81 hma hh hne hza hzb hda hdb hoa hob =>
      obtain ⟨m', h1', h2', h3', h4', -⟩ := g6_ldp (H := H) F hm hinv.core hinv.slots
        (kpair_kStep (by rw [hop]; nofun) hh hty h0 h1 hne) hpre hj hj' hx hvar hf hι hop hsz2
        hty h0 h1 h80 h81 hma hh hza hzb hda hdb hoa hob hvs htemp hs
      exact same m' ⟨h1', h2', h3', h4'⟩
    | stp hop hsz4 hmt hhn hxo hyo hma =>
      obtain ⟨m', h⟩ := g6_stp (H := H) F hF hsz hm hinv.core hinv.slots hR
        (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hx hvar hf hι hop hsz4 hmt hhn hxo
        hyo hma hvs htemp hs
      exact same m' h

/-- **G6, values.** A value (not an entry value) of a function `checkG6` accepted with the class
table `kt`, run by `runLoc` from a state related by `LocMatch` to a machine state whose registers
hold values of the classes the table gives before the value (`G3Inv` at `kAt … i`), under an
activation `G6Env` (G2's, with the accessed frame variables at their frame operands), is matched
by `runProg` steps of genssa's P0 Progs to a state related before the next value, with the
registers at the classes before the next value, under an activation `E'` that extends `E`'s
injection (by the callee's, at a call) and is again a `G6Env`. At a static call the callee's
behaviour is the trusted contract `CallOK`. -/
theorem g6_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG6 lc ps bstart g = .ok (tab, kt)) (hE : G6Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G4Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G6Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome4, hcf, hk, hlt, hnd, hblocks⟩ := checkG6_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind6_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk6_step hE0 F (call_not_slot4 hhome4) hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre
    hcall hs

/-- **G6, terminators.** A terminator of a function `checkG6` accepted with the class table `kt`
that goes to a successor, from a state whose registers hold the classes of the block's end, is
matched by `runProg` steps to a state related before the successor's first value, with the
registers at the classes of the successor's start (`kt.at`); an `Exit` block never goes to one. -/
theorem g6_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG6 lc ps bstart g = .ok (tab, kt)) (hE : G6Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome4, -, hk, hlt, hnd, hblocks⟩ := checkG6_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
