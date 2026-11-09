import GoFV.Proof.Gen.G40
import GoFV.Proof.Gen.Spec41

/-!
# Slice G41 of the genssa validator: `CMNconst`, `CMPshiftLL`, `CMPshiftRL` (`docs/plans/proofs3.md` §4)

`checkG41 lc` (`GoFV/Gen/Check41.lean`) is G40 with the compares `CMNconst [k] x` (`CMN $k, Rn`) and
`CMPshiftLL`, `CMPshiftRL [k] x y` (`CMP Rm SHIFT k, Rn`) of 64-bit arguments. `runLoc` runs them as
Phase 1's `cmp1P`/`cmpSh` (`stepLoc_alu41`): on registers, the flags of the 64-bit `ADDS`/`SUBS`,
which the machine computes (`progStep_cmnConst`, G1's `progStep_cmp` with G27's shifted operand);
on a pointer without an integer form as first argument, `Z` clear (`Arm64.zClear`), which the
machine does not compute. The run premise `CmpPre` (their first argument is no such pointer,
G1's `NoBarePtr`, as G1's premise for `CMP`/`CMPconst`) excludes that case: a property of the run,
checkable on the state, not a trusted hook. `g41_value`'s per-value premise is `G41Pre`: `G38Pre`
and `CmpPre`. `g41_initMem`, `g41_term`, `g41_nilPanic`, `g41_boundsPanic` are G40's statements over
`checkG41`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- The first argument of a G41 compare is no pointer without an integer form (`NoBarePtr`). -/
def CmpPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  (v.op = .ARM64CMNconst ∨ v.op = .ARM64CMPshiftLL ∨ v.op = .ARM64CMPshiftRL) →
    ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → NoBarePtr x

/-- The per-value premises of G41: G38's (`G38Pre`), and `CmpPre`. -/
def G41Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop := G38Pre lc s v ∧ CmpPre lc s v

/-! ## Ops -/

/-- The ops of G41. -/
def AluOp41 (op : Op) : Prop :=
  op = .ARM64CMNconst ∨ op = .ARM64CMPshiftLL ∨ op = .ARM64CMPshiftRL

theorem aluOp41_cmpSh {op : Op} {typ : Nat} (h : cmpSh41? op = some typ) : AluOp41 op := by
  unfold AluOp41
  rcases cmpSh41?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp41_ne {op : Op} (h : AluOp41 op) :
    op ≠ .Phi ∧ op ≠ .ARM64MOVDnop ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false := by
  unfold AluOp41 at h
  rcases h with h | h | h <;> subst h <;> exact ⟨nofun, nofun, nofun, nofun, rfl⟩

/-- The G41 ops empty G35's table. -/
theorem uStep35_alu41 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : AluOp41 v.op) : uStep35 lc L v = [] := by
  obtain ⟨-, hn1, hn2, -, -⟩ := aluOp41_ne hop
  unfold AluOp41 at hop
  have hl : loadOp? v.op = none := by rcases hop with h | h | h <;> rw [h] <;> rfl
  have hi : loadIdxOp? v.op = none := by rcases hop with h | h | h <;> rw [h] <;> rfl
  have hp : pairOp35 lc v = false := by
    rcases hop with h | h | h <;> simp [pairOp35, h]
  have hk : keep34 v = false := by
    rcases hop with h | h | h <;> simp [keep34, keep31, keepOp31, keepOp34, h]
  have hk31 : keep31 v = false := by
    rcases hop with h | h | h <;> simp [keep31, keepOp31, h]
  have hue : uEntry lc v = none := by
    have : narrowLd? lc v = none := by
      unfold narrowLd?
      rw [hl, hi]
    simp only [uEntry, this]
  rw [uStep35_other (ldEntry35_none hl) hp, uStep34_other hk, uStep31_other hk31,
    uStepL_other hue hn1 hn2]

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The ops of G41: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_alu41 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : AluOp41 v.op) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  unfold AluOp41 at hop
  rcases hop with hop | hop | hop <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv) := by
      unfold evalOpL; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨argv, hm, rfl⟩

end Steps

/-! ## The machine -/

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- The flags of the 64-bit `ADDS`. -/
theorem addSub_addFlags (x y : BitVec 64) :
    (addSub true false x y).2 = (GoFV.SSA.Sem.addWithCarry x y false).2 := by
  simp [addSub, sizedF]

/-- `CMN $k, Rn`: the flags of the 64-bit `ADDS` of `X[n]` and `k`. -/
theorem progStep_cmnConst {kn : Nat} {k : Int} (hkn : kn < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .CMN) (hf : p.from_ = constA k)
    (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := (GoFV.SSA.Sem.addWithCarry (s.rX (BitVec.ofNat 5 kn)) (BitVec.ofInt 64 k)
        false).2, pc := next } := by
  have hname : As.name .CMN = "CMN" := rfl
  have he : progEffect ⟨L, s, p⟩ = .ok { flags := some (GoFV.SSA.Sem.addWithCarry
      (s.rX (BitVec.ofNat 5 kn)) (BitVec.ofInt 64 k) false).2 } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hr, hf, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames, ctx_src_reg hkn, ctx_src_const, ProgOp.binOp, addSub_addFlags]
    rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

/-- `CMP Rm SHIFT k, Rn`: the flags of the `SUBS` of `X[n]` and `X[m]` shifted by `k`. -/
theorem progStep_cmpShift {kn km typ k : Nat} (hkn : kn < 32) (hkm : km < 32) (ht : typ < 3)
    (hk : k < 64) (hn : L.nextAddr p.id = some next) (has : p.as = .CMP)
    (hf : p.from_ = shiftA typ (REG_R0 + km) k) (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := (GoFV.SSA.Sem.Arm64.subFlags (s.rX (BitVec.ofNat 5 kn))
        (Sem.Arm64.Shift.apply (shK typ) (s.rX (BitVec.ofNat 5 km)) k)).2, pc := next } := by
  refine progStep_cmp hkn hn has ?_ hr
  rw [hf]
  exact ctx_src_shift ht hkm hk

end Progs

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

/-- A 64-bit register content that is no pointer without an integer form: none at all
(`poison`, or a value without a register), or the machine word. -/
theorem reg_cases41 (hA : AddrAgree ι) {x : Val} {X : BitVec 64} (hx : ValRel ι x X)
    (hf : Fits 64 x) :
    Arm64.reg x = some X ∨ Arm64.reg x = none := by
  cases hr : Arm64.reg x with
  | none => exact .inr rfl
  | some a =>
    have h := reg_low hA hx hf hr
    simp only [BitVec.setWidth_eq] at h
    exact .inl (congrArg some h)

/-- `CMNconst [k]` of a 64-bit argument that is no pointer without an integer form: the flags of
the machine's `CMN $k, Rn` (`progStep_cmnConst`). -/
theorem flagsRel_cmnK (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} (hx : ValRel ι x X) (hfx : Fits 64 x) (hp : NoBarePtr x) :
    FlagsRel (Arm64.evalPure .ARM64CMNconst t k aux [x])
      (GoFV.SSA.Sem.addWithCarry X (BitVec.ofInt 64 k.toInt) false).2 := by
  show FlagsRel (Arm64.cmp1P (fun a => GoFV.SSA.Sem.addWithCarry a (Arm64.imm k) false) [x]) _
  rcases reg_cases41 hA hx hfx with h | h
  · simp only [Arm64.cmp1P, h]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [Arm64.cmp1P, h]
    cases x with
    | ptr q =>
      have := hp q rfl
      simp only [Arm64.reg] at h
      rw [h] at this
      cases this
    | _ => trivial

/-- `CMPshiftLL`/`CMPshiftRL [k]` (`cmpSh41? = some typ`) of a first argument that is no pointer
without an integer form: the flags of the machine's `CMP Rm SHIFT k, Rn` (`progStep_cmpShift`). -/
theorem flagsRel_cmpSh41 (hA : AddrAgree ι) {op : Op} {typ : Nat} (hop : cmpSh41? op = some typ)
    {t : Ty} {k : Int64} {aux : Option AuxRef} {x y : Val} {X Y : BitVec 64}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits 64 x) (hfy : Fits 64 y)
    (hp : NoBarePtr x) :
    FlagsRel (Arm64.evalPure op t k aux [x, y])
      (GoFV.SSA.Sem.Arm64.subFlags X (Sem.Arm64.Shift.apply (shK typ) Y k.toInt.toNat)).2 := by
  have hev : Arm64.evalPure op t k aux [x, y] =
      Arm64.cmpSh (fun a b => Arm64.subFlags a (Arm64.shifted (shK typ) k b)) [x, y] := by
    rcases cmpSh41?_some hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rw [hev]
  rcases reg_cases41 hA hy hfy with hry | hry
  · rcases reg_cases41 hA hx hfx with hrx | hrx
    · simp only [Arm64.cmpSh, hrx, hry]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [Arm64.cmpSh, hrx, hry]
      cases x with
      | ptr q =>
        have := hp q rfl
        simp only [Arm64.reg] at hrx
        rw [hrx] at this
        cases this
      | _ => trivial
  · simp only [Arm64.cmpSh, hry]
    trivial

end Vals

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `CMN $k, Rn`. -/
theorem g41_cmn (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : CmpPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rn : Int}
    (hop : v.op = .ARM64CMNconst) (hsz1 : v.args.size = 1) (hfl : (lc.ty v.id).isFlags = true)
    (hhn : lc.home v.id = none) (hao : argObj lc v 0 = .ok (64, rn))
    (hvs : OneAt2 psA j (.ofShape { as := .CMN, from_ := constA v.auxInt.toInt, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧ m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp41 v.op := .inl hop
  have hnp : v.op ≠ .Phi := (aluOp41_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  have hpx := hpre (.inl hop) a0 x ha0 hx
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu41 hl htemp halu hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_flags hhn hfl, hop, isFlags_eq hfl]
  exact (op_flags F hm hinv hj hj' hvs (flags_retypeL (flagsRel_cmnK hA hxv hxf hpx)).1
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_cmnConst hkn (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
    fun m' ⟨h1, h2, h3, _, h5⟩ => ⟨h1, h2, h3, hsi, h5⟩

/-- `CMP Rm SHIFT k, Rn`. -/
theorem g41_cmpSh (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : CmpPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {typ : Nat} {rn rm : Int}
    (hop : cmpSh41? v.op = some typ) (hsz2 : v.args.size = 2) (hfl : (lc.ty v.id).isFlags = true)
    (hhn : lc.home v.id = none) (hk0 : 0 ≤ v.auxInt.toInt) (hk64 : v.auxInt.toInt < 64)
    (hao : argObj lc v 0 = .ok (64, rn)) (hbo : argObj lc v 1 = .ok (64, rm))
    (hvs : OneAt2 psA j (.ofShape
      { as := .CMP, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧ m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp41 v.op := aluOp41_cmpSh hop
  have hnp : v.op ≠ .Phi := (aluOp41_ne halu).1
  have hop' : v.op = .ARM64CMNconst ∨ v.op = .ARM64CMPshiftLL ∨ v.op = .ARM64CMPshiftRL := by
    rcases cmpSh41?_some hop with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  have ht3 : typ < 3 := by rcases cmpSh41?_some hop with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  have hpx := hpre hop' a0 x ha0 hx
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu41 hl htemp halu hs
  rw [arr2 hsz2 ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_flags hhn hfl, isFlags_eq hfl]
  have hkk : v.auxInt.toInt.toNat < 64 := by omega
  exact (op_flags F hm hinv hj hj' hvs
    (flags_retypeL (flagsRel_cmpSh41 hA hop hxv hyv hxf hyf hpx)).1
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_cmpShift hkn hkm ht3 hkk (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
    fun m' ⟨h1, h2, h3, _, h5⟩ => ⟨h1, h2, h3, hsi, h5⟩

end Cases

/-! ## One value -/

/-- One value of G41's kinds: `vk38_step`'s statement, under `G41Pre`. -/
theorem vk41_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK41 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G41Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZ H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOK H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOK H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
      UOKL m' (uStep35 lc L v) := by
  have fin : AluOp41 v.op → ∀ m',
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' →
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
        UOKL m' (uStep35 lc L v) := fun halu m' h1 h2 h3 h4 => by
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_alu41 halu]
    intro e he
    cases he
  cases hVK with
  | g38 _ _ hVK38 =>
    exact vk38_step hE F hhome hcf hv hVK38 hvs htemp hj hj' hreads hm hinv hL hmem hpre.1 hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | cmn hop hsz hfl hhn hao =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g41_cmn (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_none hhn).noRegs) hpre.2 hj hj' hop hsz
      hfl hhn hao hvs htemp hs
    exact fin (.inl hop) m' h1 h2 h3 h4
  | cmpSh hop hsz hfl hhn hk0 hk64 hao hbo =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g41_cmpSh (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_none hhn).noRegs) hpre.2 hj hj' hop hsz
      hfl hhn hk0 hk64 hao hbo hvs htemp hs
    exact fin (aluOp41_cmpSh hop) m' h1 h2 h3 h4

/-- A nil check of G41's kinds is G7's. -/
theorem vk41_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK41 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g38 _ _ h => exact vk38_nil h hop
  | cmn h => rw [hop] at h; cases h
  | cmpSh h => exact absurd hop (aluOp41_ne (aluOp41_cmpSh h)).2.2.2.1

/-- A bounds check of G38's kinds is G28's. -/
theorem vk38_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK38 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  cases h with
  | ldar h => rw [(ldar_ne h).2.2.2.2.1] at hop; cases hop
  | sel0 h => rw [h] at hop; cases hop
  | sel1 h => rw [h] at hop; cases hop
  | g37 _ _ hVK37 =>
  cases hVK37 with
  | bin h => rw [(aluOp37_ne (aluOp37_bin h)).2.2.2.2] at hop; cases hop
  | un h => rw [(aluOp37_ne (aluOp37_un h)).2.2.2.2] at hop; cases hop
  | madd h => rw [(aluOp37_ne (aluOp37_madd h)).2.2.2.2] at hop; cases hop
  | sbfx h => rw [h] at hop; cases hop
  | g36 _ _ _ _ _ hVK36 =>
  cases hVK36 with
  | g33 _ _ _ hVK33 =>
    cases hVK33 with
    | g32 _ _ _ _ hVK32 =>
      cases hVK32 with
      | g28 _ _ _ _ _ hVK28 => exact hVK28
      | bin h =>
        rw [(aluOp32_ne (aluOp32_bin h)).2.2.2.2] at hop; cases hop
      | binK h =>
        rw [(aluOp32_ne (aluOp32_binK h)).2.2.2.2] at hop; cases hop
      | un h =>
        rw [(aluOp32_ne (aluOp32_un h)).2.2.2.2] at hop; cases hop
      | csinc h => rw [h] at hop; cases hop
      | stlr h => rw [(stlr_ne (lc := lc) h).2.2.2.2.1] at hop; cases hop
    | un h => rw [(aluOp33_ne (aluOp33_un h)).2.2.2.2] at hop; cases hop
    | ubfiz h => rw [h] at hop; cases hop
    | sra h => rw [h] at hop; cases hop
    | cmnw h => rw [h] at hop; cases hop
  | sh h => rw [(aluOp36_ne (aluOp36_sh h)).2.2.2.2] at hop; cases hop
  | shOp h => rw [(aluOp36_ne (aluOp36_shOp h)).2.2.2.2] at hop; cases hop
  | tst h => rw [h] at hop; cases hop

/-- A bounds check of G41's kinds is G28's. -/
theorem vk41_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK41 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  cases h with
  | g38 _ _ h => exact vk38_pb h hop
  | cmn h => rw [h] at hop; cases hop
  | cmpSh h => rw [(aluOp41_ne (aluOp41_cmpSh h)).2.2.2.2] at hop; cases hop

/-! ## The theorems on G41's check -/

/-- G38's values and G41's compares under G41's check, under `G41Pre`. -/
theorem g41L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG41L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G41Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_41L hl hc) hE hbid hb hi hv
      hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre.1.1 hcall hcallz hicall hwb
      hclo hgetg hmeq hs
    refine ⟨E', m', hx, hE', h1, h2, h3, ?_⟩
    rw [uL35_nl hl]
    intro e he
    cases he
  | true =>
  rw [uL35_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -⟩ :=
    checkG41L_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind41_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk41_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- `InitMem` under G41's check: `g40L_initMem`'s statement. -/
theorem g41L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG41L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true) (hp : memPure lc = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, -, -, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -⟩ := checkG41L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind41_initMem hop] at hkd
  obtain ⟨ht, -, hh, hmt, rfl⟩ := vkind40_initMem hkd hop hp
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

/-- G38's nil panics under G41's check. -/
theorem g41L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG41L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_41L hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG41L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind41_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk41_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G41's check. -/
theorem g41L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG41L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_41L hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG41L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind41_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk41_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G41's check. -/
theorem g41L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG41L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_41L hl hc) hE hbid hb hm hinv hpre
      (by rw [uL31_nl hl]; intro e he; cases he) ht
    refine ⟨m', h1, h2, h3, h4, ?_⟩
    rw [uIn35_nl hl]
    intro e he
    cases he
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges⟩ :=
    checkG41L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG41 lc`, on `liveCtx lc` -/

/-- **G41, values.** `g40_value`'s statement over `checkG41`, under the per-value premise
`G41Pre` (`G38Pre`, and the first argument of a G41 compare is no pointer without an integer form,
`CmpPre`). -/
theorem g41_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG41 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G41Pre (liveCtx lc) s v)
    (hcall : CallOK H E g L (liveCtx lc) s s' v m) (hcallz : CallOKZ H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOK H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOK H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L (liveCtx lc) s v m) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g41L_value (checkG41_spec hc).2 hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz hicall hwb hclo
    hgetg hmeq hs

/-- **G41, `InitMem`.** `g40_initMem`'s statement over `checkG41`. -/
theorem g41_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG41 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true) (hp : memPure (liveCtx lc) = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g41L_initMem (checkG41_spec hc).2 hE hl hp hbid hb hi hv hop hm hinv hpre hs

/-- **G41, nil panics.** `g40_nilPanic`'s statement over `checkG41`. -/
theorem g41_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG41 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g41L_nilPanic (checkG41_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G41, bounds panics.** `g40_boundsPanic`'s statement over `checkG41`. -/
theorem g41_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG41 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g41L_boundsPanic (checkG41_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G41, terminators.** `g40_term`'s statement over `checkG41`. -/
theorem g41_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG41 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s)
    (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g41L_term (checkG41_spec hc).2 hE hbid hb hm hinv hpre hu ht

end GoFV.Proof.Gen
