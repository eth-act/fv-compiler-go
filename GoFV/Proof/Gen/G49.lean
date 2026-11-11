import GoFV.Proof.Gen.G51
import GoFV.Proof.Gen.Spec49

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G49 of the genssa validator: frame variables in `Blk.local` blocks
(`docs/plans/proofs3.md` §8, item 8)

`checkG49 lc` (`GoFV/Gen/Check49.lean`) is G51 with G6's accesses (`MOVDaddr`, the loads and
stores of G3, `LDP`, `STP`) of a frame variable whose block is `Blk.local` (`Tables.forgeable`: a
parameter or result, at its `NAME_PARAM` operand, or a `PAUTO` whose address the function converts
to an integer, at its `NAME_AUTO` operand).

**The activation** (`G49Env`): G28's (`G28Env`), and each such variable the function accesses at its
frame operand `SP + frameOff` under the injection (`VarsAt49`). `AddrAgree` pins a `Blk.local` block
that has an address to that address, so `VarsAt49` with `AddrAgree` says the address assignment
places the block at `SP + frameOff` or leaves it without an address: the machine instance of
`docs/plans/proofs3.md` §8 item 4 does the first for the running activation's parameters.

**The values** are G6's case lemmas on the `local` block at an operand of class `NAME_AUTO` or
`NAME_PARAM` (`g49_addr`, `g49_load`, `g49_store`, `g49_ldp`, `g49_stp`, each at the variable's
injected address, `var49_addr`). An address is a `Ptr.word` related to `SP + frameOff` by
`valRel_word` under `AddrAgree`, whatever the assignment. The upper-bit table (G35) takes a narrow
load's entry, or keeps the other entries across a load with none (`ld_uokl`), a pair load's other
entries (`uokl_pair`), the entries an address keeps (`uokl_keep`), and is empty after a store of
a frame variable (`st_uokl`).

`g49_value` takes G51's premise `G51Pre`; `g49_initMem`, `g49_term`, `g49_nilPanic`,
`g49_boundsPanic` are G51's statements over `checkG49`, under `G49Env`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The activation -/

/-- The current activation's accessed frame variables (`accessedVars`) in `Blk.local` blocks at
their operands: the block `Blk.local act x` of each one with a `NAME_AUTO` or `NAME_PARAM` operand
at `SP + frameOff`. -/
def VarsAt49 (lc : LocCtx) (g : G2In) (L : Link) (E : MatchEnv) : Prop :=
  ∀ x ∈ accessedVars lc, ∀ nc o, varOp g x = some (nc, o) → (nc = .AUTO ∨ nc = .PARAM) →
    lc.ctx.tabs.forgeable x = true →
    E.ι (.local lc.ctx.act x) = some (E.sp + BitVec.ofInt 64 (frameOff L nc o))

/-- The activation of a function `checkG49` accepted with table `tab`: G28's, and the frame
variables in `Blk.local` blocks at their frame operands. -/
structure G49Env (lc : LocCtx) (g : G2In) (L : Link) (ps : Array Prog) (ret : BitVec 64)
    (tab : PcTab) (E : MatchEnv) : Prop where
  env : G28Env lc g L ps ret tab E
  vars : VarsAt49 lc g L E

/-- An activation whose injection extends `E`'s keeps the frame variables' places. -/
theorem VarsAt49.extend {lc : LocCtx} {g : G2In} {L : Link} {E E' : MatchEnv}
    (h : VarsAt49 lc g L E) (hx : E.Extends E') : VarsAt49 lc g L E' := by
  intro x hx' nc o ho hnc hf
  have hsp : E'.sp = E.sp := by rw [hx.1]
  rw [hsp]
  exact hx.2 _ _ (h x hx' nc o ho hnc hf)

/-- The address of an access of a frame variable converted to an integer, a parameter or a
result: its `local` block at the access's offset (the base argument is ignored). -/
theorem symAddr_local {lc : LocCtx} {v : Value} {x : AuxRef} {a : Val} (hx : v.aux = some x)
    (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = true) :
    symAddr lc.ctx v a = some ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩ := by
  unfold isVar at hvar
  unfold symAddr
  rw [hx]
  split at hvar
  · rename_i heq
    simp only [heq, frameBlk_local hf]
  · cases hvar

/-- The element addresses of a pair access of such a frame variable: its `local` block at the
offset and 8 bytes above. -/
theorem pairAddr_local {lc : LocCtx} {v : Value} {x : AuxRef} {a : Val} (hx : v.aux = some x)
    (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = true) :
    pairAddr lc.ctx v 8 a = some (⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩,
      ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt + 8⟩) := by
  unfold pairAddr
  rw [symAddr_local hx hvar hf,
    symAddr_local (v := { v with auxInt := v.auxInt + Int64.ofNat 8 }) hx hvar hf]
  simp only [Option.bind_some, Option.map_some, ofInt_add8]

/-- A `NAME_AUTO` or `NAME_PARAM` frame offset moved by `k`. -/
theorem frameOffN_add (L : Link) {nc : AddrName} (hnc : nc = .AUTO ∨ nc = .PARAM) (o k : Int) :
    BitVec.ofInt 64 (frameOff L nc (o + k)) =
      BitVec.ofInt 64 (frameOff L nc o) + BitVec.ofInt 64 k := by
  have : frameOff L nc (o + k) = frameOff L nc o + k := by
    rcases hnc with rfl | rfl <;> simp only [frameOff] <;> omega
  rw [this, BitVec.ofInt_add]

/-- A variable a value of the function accesses is an accessed variable (`FrameVar49OK`). -/
theorem var49_addr {lc : LocCtx} {g : G2In} {L : Link} {E : MatchEnv} {id : ID} {v : Value}
    {x : AuxRef} {nc : AddrName} {off : Int} (hfv : FrameVar49OK lc g v x nc off)
    (hv : lc.ctx.f.value? id = some v) (hvars : VarsAt49 lc g L E) :
    ∃ a, E.ι (.local lc.ctx.act x) = some a ∧
      a + BitVec.ofInt 64 v.auxInt.toInt = E.sp + BitVec.ofInt 64 (frameOff L nc off) := by
  obtain ⟨o, ho, rfl⟩ := hfv.op
  refine ⟨_, hvars x (mem_accessedVars hv hfv.aux hfv.var hfv.sp) nc o ho hfv.cls hfv.loc, ?_⟩
  rw [frameOffN_add L hfv.cls, BitVec.add_assoc]

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `MOVDaddr` of a frame variable in a `local` block: the pointer to its block at the offset, at
the value's shape. -/
theorem stepLoc_addrLocal (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64MOVDaddr) {a : ID} {x : AuxRef} (ha : v.args = #[a]) (hx : v.aux = some x)
    (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = true)
    (h : stepLoc env lc s v = .ok s') :
    s' = s.write lc v.id ((PtrOps.ptrRes ⟨.local lc.ctx.act x,
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
      rw [symAddr_local hx hvar hf]
      rfl
  | panic e m => rw [hy] at hm; cases hm
  | stuck msg => rw [hy] at hm; cases hm

end Step

/-! ## One access of a frame variable in a `local` block -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}
  {x : AuxRef} {nc : AddrName} {off : Int}

/-- `MOVD $off(<nc>), Rd`: the address of a frame variable (`g6_addr` on its `local` block). -/
theorem g49_addr (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hι : ∃ a, E.ι (.local lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off))
    {a0 : ID} {rd : Int} (hop : v.op = .ARM64MOVDaddr) (hsz1 : v.args.size = 1)
    (ha0 : v.args[0]? = some a0) (hro : resObj lc v = .ok (64, rd))
    (hvs : OneAt2 psA j ⟨plain .MOVD (addrN · nc off) (· == regA rd), "MOVD $var"⟩ j')
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
  rw [stepLoc_addrLocal hl htemp hop (arr1 hsz1 ha0) hx hvar hf hs, write_reg hvh hcv]
  have hrel : ValRel E.ι (PtrOps.ptrRes ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩)
      (E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off)) := by
    unfold PtrOps.ptrRes
    split
    · exact valRel_word hA ⟨a, hpa, haeq.symm⟩
    · trivial
  have hfit : Fits 64 (PtrOps.ptrRes ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩) := by
    unfold PtrOps.ptrRes; split
    · exact fits_word _
    · trivial
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL hA hcv hfit hrel) (fits_retypeL hcv _)
    (knext_set hK (by rw [hop]; nofun) hvh hcv)
    (fun k0 hk0 hok => ?_)).imp fun m' ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf1, -, ht, -⟩ := plain_spec hok
  simp only [addrN, Bool.and_eq_true, beq_iff_eq] at hf1
  simp only [beq_iff_eq] at ht
  have hsp : m.sp = E.sp := hm.frame.1
  rw [← hsp, progStep_slotAddr hkd (nextAddr_pcAt F.nodup hk0) has hf1.1 hf1.2 hnc ht, wX_pc]

/-- A load of `n` bytes of a frame variable at `off(<nc>)` (`g6_load` on its `local` block), with
the registers of the machine after the load. -/
theorem g49_load (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K') (hpre : G3Pre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hι : ∃ a, E.ι (.local lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off))
    {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int}
    (hop : loadOp? v.op = some (as, n, sg)) (hsz2 : v.args.size = 2)
    (hma : memArg lc v 1 = .ok ()) (hro : resObj lc v = .ok (c, rd))
    (hc : 8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false)
    (hvs : OneAt2 psA j ⟨plain as (slotA · nc off) (· == regA rd), as.name⟩ j')
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
  rw [symAddr_local hx hvar hf] at hsym
  cases hsym
  rw [write_reg hvh hcv, symAddr_local hx hvar hf]
  simp only [Option.elim]
  obtain ⟨a, hpa, haeq⟩ := hι
  have hval : ValRel E.ι ((Arm64.loadN (lc.ty v.id) n sg mm
        ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩).retypeL (lc.ty v.id))
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
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  rw [progStep_slotLoadN hkd (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf1 hnc
    ht' (by rw [hA']; exact hnil), hA', wX_pc]

/-- A store of `n` bytes to a frame variable at `off(<nc>)` (`g6_store` on its `local` block),
outside the frame's saved words and slots; it writes no X register (`XW`). -/
theorem g49_store (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hι : ∃ a, E.ι (.local lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off))
    {as : As} {n cs : Nat} {rs : Int}
    (hop : storeOp? v.op = some (as, n)) (hsz3 : v.args.size = 3)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hso : argObj lc v 1 = .ok (cs, rs)) (hma : memArg lc v 2 = .ok ())
    (hc : 8 * n ≤ cs ∨ cs = 1 ∧ n = 1)
    (hvs : OneAt2 psA j ⟨plain as (· == regA rs) (slotA · nc off), as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
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
  rw [symAddr_local hx hvar hf] at hsym
  cases hsym
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  have hcs : 8 * n ≤ cs ∨ cs = 1 := hc.imp_right And.left
  have hbs := (storeBytes_relN hA hn hyv hyf hcs).1
  have hcan : mm.canWrite ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩ n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨a, hpa, haeq⟩ := hι
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inl hcan)
  obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hk0 hn hpa hyv hyf hcs hw
  have hsep' : SepAt osp E.ι (StkAt E) mm' := hsep0.write hk0 hw
  refine (op_mem2X (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM' hk' hsep'
    (fun y hy => hout y fun j hj he =>
      hsep0.not_mem hal hpa hy (by simp only [Blk.writableFrom]; omega) (by omega))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k1 hk1 hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inl h4⟩
  obtain ⟨has, hf1, -, ht1, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf1
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  rw [progStep_slotStoreN hks (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf1 ht1
    hnc (by rw [hA']; exact hnil), hA']
  rfl

/-- `LDP off(<nc>), (Ra, Rb)` (`g6_ldp` on the variable's `local` block). -/
theorem g49_ldp (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    {ra rb : Nat} {t0 t1 : Ty} {c0 c1 : Nat}
    (hK : KLe K' (kSet (kSet K ra (some c0)) rb (some c1))) (hpre : G4Pre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hι : ∃ a, E.ι (.local lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off))
    {oa ob : Int} (hop : v.op = .ARM64LDP) (hsz2 : v.args.size = 2)
    (hty : lc.ty v.id = .tuple [t0, t1]) (h0 : cls t0 = some c0) (h1 : cls t1 = some c1)
    (h80 : 8 ≤ c0) (h81 : 8 ≤ c1) (hma : memArg lc v 1 = .ok ())
    (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hza : ra ≠ zeroReg) (hzb : rb ≠ zeroReg) (hda : destOK ra = true) (hdb : destOK rb = true)
    (hoa : objOf? ra = some oa) (hob : objOf? rb = some ob)
    (hvs : OneAt2 psA j ⟨plain .LDP (slotA · nc off) (· == pairA oa ob), "LDP"⟩ j')
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
  rw [pairAddr_local hx hvar hf] at hpq
  cases hpq
  rw [pairAddr_local hx hvar hf]
  simp only [Option.elim]
  rw [hty, loadPair_tuple, retypeL_pair, write_pair hh hty (by rw [h0]; rfl) (by rw [h1]; rfl)]
  obtain ⟨a, hpa, haeq⟩ := hι
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < 8) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨hnil', -⟩ := access_nil hMI hpa (by omega : 0 < 8) (Or.inr (by rw [hrq]; rfl))
  have ht0 := cls_ne_bool h0 h80
  have ht1 := cls_ne_bool h1 h81
  have hrel0 : ValRel E.ι ((Arm64.loadN t0 8 false mm
        ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩).retypeL t0)
      ((readMem m.mem (a + BitVec.ofInt 64 v.auxInt.toInt) 8).setWidth 64) :=
    valRel_retypeL_lo hA h0 ht0 ((lo_loadN hA hMI (by simp) (fun _ => rfl) ht0 hpa hrp).mono
      (cls_le h0))
  have hrel1 : ValRel E.ι ((Arm64.loadN t1 8 false mm
        ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt + 8⟩).retypeL t1)
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
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  have hA8 : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) + 8 =
      a + (BitVec.ofInt 64 v.auxInt.toInt + 8) := by rw [hA', BitVec.add_assoc]
  rw [progStep_slotLdp hka' hkb' (nextAddr_pcAt F.nodup hk) has hf1 hnc ht'
    (by rw [hA']; exact hnil) (by rw [hA8]; exact hnil'), hA8, hA']
  simp only [wX_pc]

/-- `STP (Rx, Ry), off(<nc>)` (`g6_stp` on the variable's `local` block), outside the frame's
saved words and slots. -/
theorem g49_stp (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hx : v.aux = some x) (hvar : isVar lc x = true) (hf : lc.ctx.tabs.forgeable x = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hι : ∃ a, E.ι (.local lc.ctx.act x) = some a ∧ a + BitVec.ofInt 64 v.auxInt.toInt =
      E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off))
    {rx ry : Int} (hop : v.op = .ARM64STP) (hsz4 : v.args.size = 4)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hxo : argObj lc v 1 = .ok (64, rx)) (hyo : argObj lc v 2 = .ok (64, ry))
    (hma : memArg lc v 3 = .ok ())
    (hvs : OneAt2 psA j ⟨plain .STP (· == pairA rx ry) (slotA · nc off), "STP"⟩ j')
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
  rw [pairAddr_local hx hvar hf] at hpq
  cases hpq
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨a, hpa, haeq⟩ := hι
  have hby := (storeBytes_relN hA (n := 8) (by simp) hyv hyf (Or.inl (Nat.le_refl _))).1
  have hbz := (storeBytes_relN hA (n := 8) (by simp) hzv hzf (Or.inl (Nat.le_refl _))).1
  have hcan1 : mm.canWrite ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt⟩ 8 = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < 8) (Or.inl hcan1)
  obtain ⟨hM1, hk1, hback1, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hk0 (by simp) hpa hyv hyf (Or.inl (Nat.le_refl _)) hw1
  have hcan2 : mm1.canWrite ⟨.local lc.ctx.act x, BitVec.ofInt 64 v.auxInt.toInt + 8⟩ 8 = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨hnil', -⟩ := access_nil hM1 hpa (by omega : 0 < 8) (Or.inl hcan2)
  obtain ⟨hM2, hk2, hback2, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 (by simp) hpa hzv hzf (Or.inl (Nat.le_refl _)) hw2
  have hsep1 : SepAt osp E.ι (StkAt E) mm1 := hsep0.write hk0 hw1
  have hsep2 : SepAt osp E.ι (StkAt E) mm' := hsep1.write hk1 hw2
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  have hA8 : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) + 8 =
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
  rw [progStep_slotStp hkx hky (nextAddr_pcAt F.nodup hk) has hf1 ht1 hnc
    (by rw [hA']; exact hnil) (by rw [hA8]; exact hnil'), hA8, hA']
  rfl

end Cases

/-! ## The upper-bit table across G49's values -/

/-- A value no narrow load (`uEntry`), `MOVDnop` or `MOVDreg`, outside `keep34` and no pair load:
G35's table is empty after it. -/
theorem uStep35_nil {lc : LocCtx} {v : Value} {L : List (Nat × Nat × Bool)}
    (hue : uEntry lc v = none) (h0 : ldEntry35 lc v = none) (hp : pairOp35 lc v = false)
    (hk : keep34 v = false) (h1 : v.op ≠ .ARM64MOVDnop) (h2 : v.op ≠ .ARM64MOVDreg) :
    uStep35 lc L v = [] := by
  have hc : v.op ≠ .Copy := fun h => by simp [keep34, keep31, keepOp31, h] at hk
  rw [uStep35_other h0 hp hc, uStep34, hk]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact uStepL_other hue h1 h2

/-! ## One value -/

/-- What a value of G49's kinds is: G51's, or an access of a frame variable in a `local` block. -/
theorem vk49_ops {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK49 lc g v kd) :
    VK51 lc g v kd ∨ ∃ x nc off, FrameVar49OK lc g v x nc off ∧ VKVar49 lc v nc off kd := by
  cases h with
  | g51 h => exact .inl h
  | var hfv hv => exact .inr ⟨_, _, _, hfv, hv⟩

/-- One value of G49's kinds: `vk51_step`'s statement under `G49Env`. -/
theorem vk49_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK49 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G51Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  obtain ⟨hE28, hvars⟩ := hE
  cases hVK with
  | g51 hVK51 =>
    obtain ⟨E', m', hx, hE', h⟩ := vk51_step hE28 F hhome hcf hv hVK51 hvs htemp hj hj' hreads
      hm hinv hL hmem hpre hcall hcallz hicall hwb hclo hgetg hmeq hs
    exact ⟨E', m', hx, ⟨hE', hvars.extend hx⟩, h⟩
  | var hfv hVar =>
    obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE28.env.env.env.env
    have hR := kread_of_reads hreads
    have hsz := slot_sizes hlcE hcf hinv.slots
    have h14 : G14Pre lc s v := hpre.1.1.1.1.1.1.1
    have hι := var49_addr hfv hv hvars
    have hx := hfv.aux
    have hvar := hfv.var
    have hf := hfv.loc
    have hnc := hfv.cls
    have same : ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
        LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp →
        SlotInv lc s' → UOKL m' (uStep35 lc L v) →
        ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
          PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
          LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
          UOKL m' (uStep35 lc L v) :=
      fun m' h1 h2 h3 h4 h5 => ⟨E, m', ⟨rfl, fun _ _ h => h⟩, ⟨hE28, hvars⟩, h1, h2, ⟨h3, h4⟩, h5⟩
    cases hVar with
    | addr hop hsz1 hro =>
      obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
        ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
      obtain ⟨m', h1, h2, h3, h4, hxw⟩ := g49_addr (H := H) F hm hinv.core hinv.slots
        (knext_kStep fun _ => (hs_res hro).noRegs) hj hj' hx hvar hf hnc hι hop hsz1 ha0 hro hvs
        htemp hs
      refine same m' h1 h2 h3 h4 ?_
      have hl0 : loadOp? v.op = none := by rw [hop]; rfl
      rw [uStep35_other (ldEntry35_none hl0 (by rw [hop]; nofun)) (by simp [pairOp35, hop])
          (by rw [hop]; nofun),
        uStep34_keep (by simp [keep34, keepOp34, hop])]
      exact uokl_keep hL hxw
    | load hop hsz2 hma hro hc =>
      obtain ⟨m', h1, h2, h3, h4, kd', Y, hrd, hx'⟩ := g49_load (H := H) F hm hinv.core
        hinv.slots (knext_kStep fun _ => (hs_res hro).noRegs) h14.1.1.1.1 hj hj' hx hvar hf hnc
        hι hop hsz2 hma hro hc hvs htemp hs
      refine same m' h1 h2 h3 h4 ?_
      exact ld_uokl hop hro hrd hx' hL
    | store hop hsz3 hmt hhn hso hma hc =>
      obtain ⟨m', h1, h2, h3, h4, h5⟩ := g49_store (H := H) F hF hsz hm hinv.core hinv.slots hR
        (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hx hvar hf hnc hι hop hsz3 hmt hhn hso
        hma hc hvs htemp hs
      exact same m' h1 h2 h3 h4 (st_uokl hop hL h5)
    | @ldp ra rb _ _ _ _ _ _ hop hsz2 hty h0 h1 h80 h81 hma hh hne hza hzb hda hdb hoa hob =>
      obtain ⟨m', h1', h2', h3', h4', h5'⟩ := g49_ldp (H := H) F hm hinv.core hinv.slots
        (kpair_kStep (by rw [hop]; nofun) hh hty h0 h1 hne) h14.1.1.1 hj hj' hx hvar hf hnc hι
        hop hsz2 hty h0 h1 h80 h81 hma hh hza hzb hda hdb hoa hob hvs htemp hs
      refine same m' h1' h2' h3' h4' ?_
      rw [uStep35_ldp hop]
      have hr : homeRegs lc v.id = [ra, rb] := by simp [homeRegs, hh]
      rw [hr]
      exact uokl_pair hL h5'
    | stp hop hsz4 hmt hhn hxo hyo hma =>
      obtain ⟨m', h1, h2, h3, h4⟩ := g49_stp (H := H) F hF hsz hm hinv.core hinv.slots hR
        (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hx hvar hf hnc hι hop hsz4 hmt hhn hxo
        hyo hma hvs htemp hs
      refine same m' h1 h2 h3 h4 ?_
      have hue : uEntry lc v = none := by
        have : narrowLd? lc v = none := by unfold narrowLd?; rw [hop]; rfl
        unfold uEntry; rw [this]
      rw [uStep35_nil hue (ldEntry35_none (by rw [hop]; rfl) (by rw [hop]; nofun))
        (by simp [pairOp35, hop])
        (by simp [keep34, keep31, keepOp31, keepOp34, hop]) (by rw [hop]; nofun)
        (by rw [hop]; nofun)]
      intro e he'
      cases he'

/-- A nil check of G49's kinds is G7's. -/
theorem vk49_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK49 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g51 h => exact vk51_nil h hop
  | var _ hv =>
    cases hv with
    | addr h' => rw [hop] at h'; cases h'
    | load h' => rw [hop] at h'; cases h'
    | store h' => rw [hop] at h'; cases h'
    | ldp h' => rw [hop] at h'; cases h'
    | stp h' => rw [hop] at h'; cases h'

/-- A bounds check of G49's kinds is G28's. -/
theorem vk49_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK49 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  cases h with
  | g51 h => exact vk51_pb h hop
  | var _ hv =>
    cases hv with
    | addr h' => rw [h'] at hop; cases hop
    | load h' =>
      rcases loadOp?_op h' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        rw [h] at hop <;> cases hop
    | store h' =>
      rcases storeOp?_op h' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hop <;> cases hop
    | ldp h' => rw [h'] at hop; cases hop
    | stp h' => rw [h'] at hop; cases hop

/-! ## The theorems on G49's check -/

/-- G51's values and G49's accesses of frame variables under G49's check, under `G51Pre`. -/
theorem g49L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG49L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G51Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_49L hl hc) hE.env hbid hb
      hi hv hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre.1.1.1.1.1.1.1 hcall hcallz
      hicall hwb hclo hgetg hmeq hs
    refine ⟨E', m', hx, ⟨hE', hE.vars.extend hx⟩, h1, h2, h3, ?_⟩
    rw [uL35_nl hl]
    intro e he
    cases he
  | true =>
  rw [uL35_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -⟩ :=
    checkG49L_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind49_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk49_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- `InitMem` under G49's check: `g51L_initMem`'s statement. -/
theorem g49L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG49L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, -, -, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -⟩ := checkG49L_spec hl hc
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
  have hkd := vkind49_initMem hop hkd
  rw [vkind51_initMem hop, vkind50_initMem hop, vkind47_initMem hop, vkind46_initMem hop,
    vkind45_initMem hop, vkind44_initMem hop] at hkd
  obtain ⟨-, -, ht, -, hh, hmt, rfl⟩ := vkind43_initMem hkd hop
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hpc : E.pcOf bid (i + 1) = E.pcOf bid i := by rw [hj', hj, hvs]
  have hss : s' = s := by
    rw [stepLoc_initMem hl ht hop hh hmt hs]
    exact congrArg (fun x => { s with mem := x }) hpre.symm
  subst hss
  have hK : kAt c.cx.lc kt bid blk (i + 1) = kAt c.cx.lc kt bid blk i := by
    rw [kAt_succ hi hv, kStep_none (by rw [hh]; nofun) (by rw [hh]; nofun) (by rw [hh]; nofun)]
  refine ⟨E, m, ⟨rfl, fun _ _ h => h⟩, hE0, .refl, locMatch_pc hm (hpc.trans hm.pc.symm),
    hK ▸ hinv, ?_⟩
  rw [uL35_succ hl hi hv, uStep35_initMem hop]
  intro e he
  cases he

/-- G38's nil panics under G49's check. -/
theorem g49L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG49L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_49L hl hc) hE.env hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG49L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind49_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk49_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G49's check. -/
theorem g49L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG49L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_49L hl hc) hE.env hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG49L_spec hl hc
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
  have hen : entryOp24 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  obtain ⟨-, hVK⟩ := vkind49_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk49_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G49's check. -/
theorem g49L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG49L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_49L hl hc) hE.env hbid hb hm hinv hpre
      (by rw [uL31_nl hl]; intro e he; cases he) ht
    refine ⟨m', h1, h2, h3, h4, ?_⟩
    rw [uIn35_nl hl]
    intro e he
    cases he
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges⟩ :=
    checkG49L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG49 lc`, on `liveCtx lc` -/

/-- **G49, values.** `g51_value`'s statement over `checkG49` under `G49Env` (G28's activation with
the accessed frame variables in `Blk.local` blocks at their operands, `VarsAt49`), under G51's
premise `G51Pre`. -/
theorem g49_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG49 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G51Pre (liveCtx lc) s v)
    (hcall : CallOK H E g L (liveCtx lc) s s' v m) (hcallz : CallOKZ H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOK H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOK H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L (liveCtx lc) s v m) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g49L_value (checkG49_spec hc).2 hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz hicall hwb hclo
    hgetg hmeq hs

/-- **G49, `InitMem`.** `g51_initMem`'s statement over `checkG49`. -/
theorem g49_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG49 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g49L_initMem (checkG49_spec hc).2 hE hl hbid hb hi hv hop hm hinv hpre hs

/-- **G49, nil panics.** `g51_nilPanic`'s statement over `checkG49`. -/
theorem g49_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG49 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g49L_nilPanic (checkG49_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G49, bounds panics.** `g51_boundsPanic`'s statement over `checkG49`. -/
theorem g49_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG49 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g49L_boundsPanic (checkG49_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G49, terminators.** `g51_term`'s statement over `checkG49`. -/
theorem g49_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG49 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s)
    (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g49L_term (checkG49_spec hc).2 hE hbid hb hm hinv hpre hu ht

end GoFV.Proof.Gen
