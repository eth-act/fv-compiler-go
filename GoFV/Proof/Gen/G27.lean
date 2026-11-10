import GoFV.Proof.Gen.G26
import GoFV.Proof.Gen.Spec27

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G27: shifted logic ops (`docs/plans/proofs3.md` §4)

`g27_value`, `g27_term`, `g27_nilPanic`, `g27_boundsPanic`: `g26_value`'s, `g26_term`'s,
`g26_nilPanic`'s and `g26_boundsPanic`'s statements over `checkG27`.

`ANDshiftXX`, `ORshiftXX`, `XORshiftXX`, `BICshiftXX [k] x y` run under `runLoc` as `Arm64.opSh`
of the shift kind (`shK`) and the bitwise op (`logF`) on the arguments read from their homes
(`stepLoc_logSh`): `x op (y SHIFT k)` on their registers. genssa's `op Rm SHIFT k, Rn, Rd` has the
shifted source operand `shiftA`, which reads `X[m]` shifted by the same `Shift.apply`
(`ctx_src_shift`), so the machine writes `X[n] op (X[m] SHIFT k)` (`progStep_logSh`). A bitwise
op's low bits depend only on its operands' low bits. A left shift's low bits depend only on the
shifted register's low bits; a right shift reads all of a class-64 register, which equals its
machine word. So the result is related on the low bits of its class (`lo_logSh`, `g27_logSh`).
On a function with no arm64 op, `checkG27` is `checkG26` (`checkG26_of_27`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The ops -/

/-- The shift of a `makeshift` kind (0 `LSL`, 1 `LSR`, 2 `ASR`). -/
def shK : Nat → Sem.Arm64.Shift
  | 0 => .ll
  | 1 => .rl
  | _ => .ra

/-- The bitwise op of a shifted logic opcode. -/
def logF : As → BitVec 64 → BitVec 64 → BitVec 64
  | .AND => (· &&& ·)
  | .ORR => (· ||| ·)
  | .EOR => (· ^^^ ·)
  | _ => fun x y => x &&& ~~~y

theorem logSh?_some {op : Op} {as : As} {typ : Nat} (h : logSh? op = some (as, typ)) :
    (op = .ARM64ANDshiftLL ∨ op = .ARM64ANDshiftRL ∨ op = .ARM64ANDshiftRA) ∧ as = .AND ∨
    (op = .ARM64ORshiftLL ∨ op = .ARM64ORshiftRL ∨ op = .ARM64ORshiftRA) ∧ as = .ORR ∨
    (op = .ARM64XORshiftLL ∨ op = .ARM64XORshiftRL ∨ op = .ARM64XORshiftRA) ∧ as = .EOR ∨
    (op = .ARM64BICshiftLL ∨ op = .ARM64BICshiftRL ∨ op = .ARM64BICshiftRA) ∧ as = .BIC := by
  unfold logSh? at h
  split at h <;> (try cases h) <;> simp

theorem logSh?_typ {op : Op} {as : As} {typ : Nat} (h : logSh? op = some (as, typ)) : typ < 3 := by
  unfold logSh? at h
  split at h <;> (try cases h) <;> decide

/-- `runLoc`'s value of a shifted logic op: `opSh` of its shift kind and bitwise op. -/
theorem evalOpL_logSh {env : Env} {ctx : Ctx} {fr : GoFV.SSA.Sem.Frame} {v : Value}
    {argv : List Val} {t : Ty} {as : As} {typ : Nat} (h : logSh? v.op = some (as, typ)) :
    evalOpL true env ctx fr v argv t = .ok (Arm64.opSh t (shK typ) v.auxInt (logF as) argv) := by
  have hop := h
  unfold logSh? at hop
  split at hop <;> (try cases hop) <;>
  · rename_i heq
    unfold evalOpL; rw [heq]; rfl

theorem logSh_noclobber {op : Op} {as : As} {typ : Nat} (h : logSh? op = some (as, typ)) :
    op ≠ .Phi ∧ op ≠ .LoadReg ∧ op ≠ .StoreReg ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64MOVDnop ∧
      op.regInfo.clobbers.isEmpty = true ∧ op.regInfo.clobbersArg0 = false ∧
      op.regInfo.clobbersArg1 = false ∧ op.clobberFlags = false := by
  unfold logSh? at h
  split at h <;> (try cases h) <;> exact ⟨nofun, nofun, nofun, nofun, nofun, rfl, rfl, rfl, rfl⟩

theorem narrowLd?_logSh {lc : LocCtx} {v : Value} {as : As} {typ : Nat}
    (h : logSh? v.op = some (as, typ)) : narrowLd? lc v = none := by
  have hop := h
  unfold logSh? at hop
  split at hop <;> (try cases hop) <;>
  · rename_i heq
    unfold narrowLd?; rw [heq]; rfl

/-- `stepLoc` of a shifted logic op: `opSh` of the arguments read from their homes. -/
theorem stepLoc_logSh {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value} {as : As}
    {typ : Nat} (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : logSh? v.op = some (as, typ)) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id
        ((Arm64.opSh (lc.ty v.id) (shK typ) v.auxInt (logF as) argv).retypeL (lc.ty v.id)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := logSh_noclobber hop
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht h1 h2 h3 h4 h5 h6 h7 h8 h9 h
  rw [evalOpL_logSh hop] at hr
  cases hr
  exact ⟨argv, hm, rfl⟩

/-! ## The machine's `op Rm SHIFT k, Rn, Rd` -/

theorem shiftOf_shK {typ : Nat} (ht : typ < 3) : shiftOf (BitVec.ofNat 2 typ) = shK typ := by
  rcases (by omega : typ = 0 ∨ typ = 1 ∨ typ = 2) with rfl | rfl | rfl <;> rfl

/-- The shifted register operand `shiftA typ (R0 + km) k`: `X[km]` shifted by `k`. -/
theorem ctx_src_shift {c : ProgCtx} {typ km k : Nat} (ht : typ < 3) (hkm : km < 32) (hk : k < 64) :
    c.src true (shiftA typ (REG_R0 + km) k) =
      .ok (Sem.Arm64.Shift.apply (shK typ) (c.s.rX (BitVec.ofNat 5 km)) k) := by
  have ho : ((REG_R0 + (km : Int) - REG_R0) * 65536 + (typ : Int) * 4194304 + (k : Int) * 1024).toNat =
      km * 65536 + typ * 4194304 + k * 1024 := by omega
  have h1 : (km * 65536 + typ * 4194304 + k * 1024) / 65536 % 32 = km := by omega
  have h2 : (km * 65536 + typ * 4194304 + k * 1024) / 4194304 % 4 = typ := by omega
  have h3 : (km * 65536 + typ * 4194304 + k * 1024) / 1024 % 64 = k := by omega
  simp only [ProgCtx.src, shiftA, ho, h1, h2, h3, shiftOf_shK ht]
  simp [sized]
  rfl

theorem logical_orr (x y : BitVec 64) : (logical true 1 x y).1 = x ||| y := by
  simp [logical, sizedF]

theorem logical_eor (x y : BitVec 64) : (logical true 2 x y).1 = x ^^^ y := by
  simp [logical, sizedF]

/-- The result of `op` (`ProgOp.binOp`) for a shifted logic opcode at 64 bits. -/
theorem binOp_logF {as : As} (has : as = .AND ∨ as = .ORR ∨ as = .EOR ∨ as = .BIC)
    (x y : BitVec 64) (cin : Bool) : (ProgOp.binOp as.name true x y cin).1 = logF as x y := by
  rcases has with rfl | rfl | rfl | rfl
  · exact logical_and x y
  · exact logical_orr x y
  · exact logical_eor x y
  · show (logical true 0 x (ProgOp.trunc true (~~~y))).1 = x &&& ~~~y
    simp [logical, sizedF, ProgOp.trunc]

/-- `op Rm SHIFT k, Rn, Rd` for a shifted logic opcode. -/
theorem progStep_logSh {L : Link} {p : Prog} {s : MState} {next : BitVec 64} {as : As}
    {typ kn km kd k : Nat} (has : as = .AND ∨ as = .ORR ∨ as = .EOR ∨ as = .BIC) (ht3 : typ < 3)
    (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32) (hk : k < 64)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as)
    (hf : p.from_ = shiftA typ (REG_R0 + km) k) (hr : p.reg = REG_R0 + kn)
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (logF as (s.rX (BitVec.ofNat 5 kn))
        (Sem.Arm64.Shift.apply (shK typ) (s.rX (BitVec.ofNat 5 km)) k)) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (logF as (s.rX (BitVec.ofNat 5 kn))
      (Sem.Arm64.Shift.apply (shK typ) (s.rX (BitVec.ofNat 5 km)) k))) := by
    rcases has with rfl | rfl | rfl | rfl <;>
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, hf, ht, hrn, regA, shiftA,
        ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn]
      rw [← shiftA, ctx_src_shift ht3 hkm hk]
      simp only [ProgOp.binOp, logical_and, logical_orr, logical_eor, eff_wX_dest hkd, logF]
      by_cases h : kd = 31 <;> simp [effWd, h, logical, sizedF, ProgOp.trunc] <;> rfl
  have hsk : p.isSkip = false := by
    rcases has with rfl | rfl | rfl | rfl <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-! ## The value -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem bits_sw {c : Nat} {a b : BitVec 64} (h : a.setWidth c = b.setWidth c) :
    ∀ i, i < c → a.getLsbD i = b.getLsbD i := by
  intro i hi
  have := congrArg (fun y : BitVec c => y.getLsbD i) h
  simpa [BitVec.getLsbD_setWidth, hi] using this

private theorem sw_of_bits {c : Nat} {a b : BitVec 64} (h : ∀ i, i < c → a.getLsbD i = b.getLsbD i) :
    a.setWidth c = b.setWidth c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  exact h i hi

/-- A bitwise op's low bits depend only on its operands' low bits. -/
theorem logF_low {as : As} {c : Nat} {a b a' b' : BitVec 64} (ha : a.setWidth c = a'.setWidth c)
    (hb : b.setWidth c = b'.setWidth c) : (logF as a b).setWidth c = (logF as a' b').setWidth c := by
  have ha' := bits_sw ha
  have hb' := bits_sw hb
  apply sw_of_bits
  intro i hi
  unfold logF
  split <;> simp [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
    ha' i hi, hb' i hi]

/-- A left shift's low bits depend only on the shifted register's low bits. -/
theorem shl_low {c s : Nat} {b b' : BitVec 64} (hb : b.setWidth c = b'.setWidth c) :
    (b <<< s).setWidth c = (b' <<< s).setWidth c := by
  have hb' := bits_sw hb
  apply sw_of_bits
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft]
  by_cases h : i < s
  · simp [h]
  · simp only [h, decide_false, Bool.not_false, Bool.true_and, Bool.and_true]
    rw [hb' (i - s) (by omega)]

private theorem res_int27 {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | exact absurd rfl ht | rfl

private theorem fits_le27 {c : Nat} {x : Val} {r : BitVec 64} (hf : Fits c x)
    (hr : Arm64.reg x = some r) : c ≤ 64 := by
  cases x with
  | int w v => have : w.bits = c := hf; subst this; cases w <;> decide
  | bool b => have : c = 1 := hf; omega
  | ptr p => have : c = 64 := hf; omega
  | _ => cases hr

/-- A shifted logic op `x op (y SHIFT k)`: `x` of class `ca` at least the result's class `c`;
`y` of class `cb ≥ c` for a left shift, of class 64 for a right shift. -/
theorem lo_logSh (hA : AddrAgree ι) {t : Ty} {as : As} {typ : Nat} {k : Int64} {x y : Val}
    {X Y : BitVec 64} {c ca cb : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x)
    (hfy : Fits cb y) (hca : c ≤ ca) (hll : typ = 0 → c ≤ cb) (hr : typ ≠ 0 → cb = 64)
    (ht : t ≠ .bool) :
    Lo ι c (Arm64.opSh t (shK typ) k (logF as) [x, y])
      (logF as X (Sem.Arm64.Shift.apply (shK typ) Y (Arm64.amt k))) := by
  simp only [Arm64.opSh, Arm64.op2]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      show Lo ι c (Arm64.res t (logF as a (Arm64.shifted (shK typ) k b))) _
      rw [res_int27 ht]
      show (logF as a (Arm64.shifted (shK typ) k b)).setWidth c = _
      have ha : a.setWidth c = X.setWidth c := by
        have := congrArg (BitVec.setWidth c) (reg_low hA hx hfx hrx)
        rwa [BitVec.setWidth_setWidth_of_le _ hca, BitVec.setWidth_setWidth_of_le _ hca] at this
      refine logF_low ha ?_
      unfold Arm64.shifted
      by_cases h0 : typ = 0
      · subst h0
        have hb : b.setWidth c = Y.setWidth c := by
          have := congrArg (BitVec.setWidth c) (reg_low hA hy hfy hry)
          rwa [BitVec.setWidth_setWidth_of_le _ (hll rfl),
            BitVec.setWidth_setWidth_of_le _ (hll rfl)] at this
        exact shl_low hb
      · have hcb := hr h0
        subst hcb
        have hb : b = Y := by simpa only [BitVec.setWidth_eq] using reg_low hA hy hfy hry
        rw [hb]

end Vals

/-! ## The case -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `op Rm SHIFT k, Rn, Rd`, which writes only its register (`XW`). -/
theorem g27_logSh (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {typ ca cb c : Nat} {rn rm rd : Int} (hop : logSh? v.op = some (as, typ))
    (hsz : v.args.size = 2) (hk0 : 0 ≤ v.auxInt.toInt) (hk64 : v.auxInt.toInt < 64)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca) (hll : typ = 0 → c ≤ cb)
    (hrr : typ ≠ 0 → cb = 64)
    (hvs : OneAt2 psA j (.ofShape
      { as, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := (logSh_noclobber hop).1
  have has : as = .AND ∨ as = .ORR ∨ as = .EOR ∨ as = .BIC := by
    rcases logSh?_some hop with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  have ht3 := logSh?_typ hop
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_logSh hl htemp hop hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  have hamt : Arm64.amt v.auxInt = v.auxInt.toInt.toNat := rfl
  have hk : v.auxInt.toInt.toNat < 64 := by omega
  have hlo := lo_logSh (as := as) (typ := typ) (k := v.auxInt) hA hxv hyv hxf hyf hca hll hrr ht
  rw [hamt] at hlo
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_retypeL_lo hA hcv ht hlo)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_logSh has ht3 hkn hkm hkd hk (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

end Cases

/-! ## The theorems -/

/-- One value of G27's kinds: `vk25_step`'s statement. -/
theorem vk27_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK27 lc g v kd)
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
  cases hVK with
  | g25 _ hVK25 =>
    exact vk25_step hE F hhome hcf hv hVK25 hvs htemp hj hj' hreads hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hs
  | logSh hop hsz hk0 hk64 hao hbo hro h8 hca hll hrr =>
    have hue : uEntry lc v = none := by simp only [uEntry, narrowLd?_logSh hop]
    rw [hue]
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g27_logSh (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk64
      hao hbo hro h8 hca hll hrr hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, trivial⟩

/-- **G27, values.** `g26_value`'s statement over `checkG27`. -/
theorem g27_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG27 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOK m (uAt lc blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOK m' (uAt lc blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g26_value (checkG26_of_27 hl hc) hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hs
  | true =>
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd⟩ :=
    checkG27_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind27_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hu1 : uAt c.cx.lc blk (i + 1) = uEntry c.cx.lc v := by simp [uAt, hi, hv]
  rw [kAt_succ hi hv, hu1]
  exact vk27_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv
    (fun x hop hx => by
      obtain ⟨r, c', hr, hc', hu0⟩ := movdOK_spec hmovd hbid hb hi hv hop hx
      exact ⟨r, c', hr, hc', hu0 ▸ hu⟩)
    hpre hcall hcallz hicall hwb hclo hgetg hs

/-- A nil check of G27's kinds is G7's. -/
theorem vk27_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK27 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g25 _ h => exact vk25_nil h hop
  | logSh h => rw [hop] at h; cases h

/-- **G27, nil panics.** `g26_nilPanic`'s statement over `checkG27`. -/
theorem g27_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG27 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g26_nilPanic (checkG26_of_27 hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG27_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind27_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk27_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G27, bounds panics.** `g26_boundsPanic`'s statement over `checkG27`, under `BoundsOK`. -/
theorem g27_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG27 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g26_boundsPanic (checkG26_of_27 hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -⟩ :=
    checkG27_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind27_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | logSh h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | g25 _ hVK25 =>
  cases hVK25 with
  | csel h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | csel0 h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | tst h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | tstw h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | g24 _ _ hVK24 =>
    cases hVK24 with
    | sp hsp => rcases pbOp_cases hop with h | h | h | h <;> rw [h] at hsp <;> cases hsp
    | g23 _ hVK23 =>
      cases hVK23 with
      | cset hc =>
        rcases pbOp_cases hop with h | h | h | h <;> rw [h] at hc <;> simp [Cond.ofOp] at hc
      | g22 _ hVK22 =>
        cases hVK22 with
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
              exact vk19_boundsPanic F hsyms hpb hrow hb hi hv hVK19 hvs hj hreads hop hm hinv
                hbok hs

/-- **G27, terminators.** `g26_term`'s statement over `checkG27`. -/
theorem g27_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG27 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g26_term (checkG26_of_27 hl hc) hE hbid hb hm hinv hpre ht
  | true =>
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG27_spec hl hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
