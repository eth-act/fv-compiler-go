import GoFV.Proof.Gen.G46
import GoFV.Proof.Gen.Spec55a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G55, group A: `VCNT`, `VUADDLV`, `FRINT*` (`docs/plans/proofs3.md` §4)

`vkind55a` (`GoFV/Gen/Check55a.lean`) accepts `VCNT`, `VUADDLV` and the `FRINT` rounds; `VK55a`
(`Spec55a.lean`) says what it accepted. `runLoc` runs each as `Arm64.evalPure` on its argument
(`stepLoc_pure55`): `VCNT`/`VUADDLV` are `op1` of `Arm64.vcnt`/`Arm64.vuaddlv` on the 64-bit
register, the rounds `FOps.roundInt` of the float at its width. The machine (`progStep_simd55`,
`progStep_frint55`) runs `VCNT Va.B8, Vd.B8` and `VUADDLV Va.B8, Vd` (`fpIdx?` reads the `ARNG`
and `V` operands as the V register's number, `fpIdx?_arng`, `fpIdx?_vOfF`) on the low 64 bits of
the source V register, zero-extended into the destination, and the rounds as `fp1Op` with the
`opc` of `frintOf`. An argument related to its V register (`FValRel`) of 64 bits is `poison` or
those bits (`fval_rel`), so the results are related (`fvalRel_simd55`, `fvalRel_frint55`), with no
run premise: a round of a NaN gives the NaN's processed quiet NaN on both sides (`IEEE.roundInt`).
None of these ops is in an upper-bit keep or entry table: after each the table is empty
(`uStep35_55a`). `vk55a_step` is one value.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64
open GoFV.IEEE (Fmt)

/-! ## The ops -/

/-- G55's group A: `VCNT`, `VUADDLV` and the rows of `frintOf`. -/
def ops55a : List Op :=
  [.ARM64VCNT, .ARM64VUADDLV, .ARM64FRINTND, .ARM64FRINTNS, .ARM64FRINTPD, .ARM64FRINTPS,
    .ARM64FRINTMD, .ARM64FRINTMS, .ARM64FRINTZD, .ARM64FRINTZS, .ARM64FRINTAD, .ARM64FRINTAS]

theorem ops55a_frint {op : Op} {n : Nat} {ft : BitVec 2} {opc : BitVec 6}
    (h : frintOf op = some (n, ft, opc)) : op ∈ ops55a := by
  rcases frintOf_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [ops55a]

theorem ops55a_simd {op : Op} {cnt : Bool} (h : op = cond cnt .ARM64VCNT .ARM64VUADDLV) :
    op ∈ ops55a := by
  cases cnt <;> subst h <;> simp [ops55a]

theorem ops55a_of {op : Op} (h : op55a op = true) : op ∈ ops55a := by
  simp only [op55a, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | h
  · simp [ops55a]
  · simp [ops55a]
  · cases hf : frintOf op with
    | none => rw [hf] at h; cases h
    | some p => obtain ⟨n, ft, opc⟩ := p; exact ops55a_frint hf

set_option hygiene false in
/-- The 12 rows of `ops55a` as hypotheses `h : op = …`. -/
local macro "ops55a_cases" : tactic => `(tactic| (
  simp only [ops55a, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h))

/-- G55's group A are pure arm64 ops that clobber nothing, no `Phi`, nil check, bounds check or
entry value. -/
theorem ops55a_facts {op : Op} (hmem : op ∈ ops55a) :
    op ≠ .Phi ∧ op ≠ .LoadReg ∧ op ≠ .StoreReg ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64MOVDnop ∧
      op.regInfo.clobbers.isEmpty = true ∧ op.regInfo.clobbersArg0 = false ∧
      op.regInfo.clobbersArg1 = false ∧ op.clobberFlags = false ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false ∧ entryOp24 op = false := by
  ops55a_cases <;> subst h <;>
    exact ⟨nofun, nofun, nofun, nofun, nofun, rfl, rfl, rfl, rfl, nofun, rfl, rfl⟩

/-- G55's group A runs as `Arm64.evalPure`. -/
theorem ops55a_eval {env : Env} {ctx : Ctx} {fr : GoFV.SSA.Sem.Frame} {v : Value} {ty : Ty}
    (hmem : v.op ∈ ops55a) (argv : List Val) :
    evalOpL true env ctx fr v argv ty = .ok (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  ops55a_cases <;> (unfold evalOpL; rw [h]; rfl)

/-- G35's table is empty after G55's group A. -/
theorem uStep35_55a {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hmem : v.op ∈ ops55a) : uStep35 lc L v = [] := by
  ops55a_cases <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- G55's group A: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_pure55 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hmem : v.op ∈ ops55a) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id
        ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL (lc.ty v.id)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := ops55a_facts hmem
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht h1 h2 h3 h4 h5 h6 h7 h8 h9 h
  rw [ops55a_eval hmem] at hr
  cases hr
  exact ⟨argv, hm, rfl⟩

end Step

/-! ## The machine -/

/-- The 64-bit function of `VCNT` (`cnt`) or `VUADDLV`. -/
def simdF55 (cnt : Bool) : BitVec 64 → BitVec 64 :=
  cond cnt GoFV.SSA.Sem.Arm64.vcnt GoFV.SSA.Sem.Arm64.vuaddlv

/-- The `8B` arrangement of `V k` is read as `V k`. -/
theorem fpIdx?_arng {k : Nat} (hk : k < 32) : ProgOp.fpIdx? (arng8B (REG_F0 + k)) = some k := by
  have h1 : ¬ ((REG_F0 ≤ arng8B (REG_F0 + k) && arng8B (REG_F0 + k) < REG_V0 + 32) = true) := by
    show ¬ ((decide ((8224 : Int) ≤ 9216 + (8224 + k - 8224)) &&
      decide ((9216 : Int) + (8224 + k - 8224) < 8256 + 32)) = true)
    simp; omega
  have h2 : (REG_ARNG ≤ arng8B (REG_F0 + k) && arng8B (REG_F0 + k) < REG_ARNG + 1024) = true := by
    show (decide ((9216 : Int) ≤ 9216 + (8224 + k - 8224)) &&
      decide ((9216 : Int) + (8224 + k - 8224) < 9216 + 1024)) = true
    simp; omega
  simp only [ProgOp.fpIdx?, h1, h2, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
  show (9216 + (8224 + (k : Int) - 8224) - 8192).toNat % 32 = k
  have h : (9216 + (8224 + (k : Int) - 8224) - 8192) = ((1024 + k : Nat) : Int) := by omega
  rw [h, Int.toNat_natCast]
  omega

/-- The scalar `V` operand of `F k` is read as `V k`. -/
theorem fpIdx?_vOfF {k : Nat} (hk : k < 32) : ProgOp.fpIdx? (vOfF (REG_F0 + k)) = some k := by
  have h1 : (REG_F0 ≤ vOfF (REG_F0 + k) && vOfF (REG_F0 + k) < REG_V0 + 32) = true := by
    show (decide ((8224 : Int) ≤ 8224 + k - 8224 + 8256) &&
      decide ((8224 : Int) + k - 8224 + 8256 < 8256 + 32)) = true
    simp; omega
  simp only [ProgOp.fpIdx?, h1, ↓reduceIte, Option.some.injEq]
  show (8224 + (k : Int) - 8224 + 8256 - 8224).toNat % 32 = k
  have h : (8224 + (k : Int) - 8224 + 8256 - 8224) = ((32 + k : Nat) : Int) := by omega
  rw [h, Int.toNat_natCast]
  omega

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

set_option hygiene false in
/-- `progEffect` of a Prog of opcode name `nm`, its string tests decided (as `FArith.lean`). -/
local macro "name_eff55 " nm:str : tactic => `(tactic| (
  have hname : p.as.name = $nm := by rw [has]; rfl
  unfold progEffect
  dsimp only
  rw [hname]
  dsimp (config := { decide := true }) only [ProgOp.baseOf, ↓reduceIte, ProgOp.movMem,
    ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS]))

/-- `VCNT Va.B8, Vd.B8` (`cnt`) or `VUADDLV Va.B8, Vd`: `simdF55` of the low 64 bits of `V ka`,
zero-extended into `V kd`. -/
theorem progStep_simd55 {cnt : Bool} {ka kd : Nat} (hka : ka < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = cond cnt .VCNT .VUADDLV)
    (hf : p.from_ = regA (arng8B (REG_F0 + ka)))
    (ht : p.to = regA (cond cnt (arng8B (REG_F0 + kd)) (vOfF (REG_F0 + kd)))) :
    progStep L p s = .ok { s.wV (BitVec.ofNat 5 kd)
      ((simdF55 cnt ((s.v (BitVec.ofNat 5 ka)).setWidth 64)).setWidth 128) with pc := next } := by
  have hv : ProgCtx.v ⟨L, s, p⟩ (arng8B (REG_F0 + ka)) = .ok (s.v (BitVec.ofNat 5 ka)) := by
    simp only [ProgCtx.v, fpIdx?_arng hka]
    rfl
  have hsk : p.isSkip = false := by cases cnt <;> simp [Prog.isSkip, has]
  have he : progEffect ⟨L, s, p⟩ = .ok { v := [(kd,
      (simdF55 cnt ((s.v (BitVec.ofNat 5 ka)).setWidth 64)).setWidth 128)] } := by
    cases cnt
    · have hw : ∀ (e : Eff) (q : BitVec 128), e.wV (vOfF (REG_F0 + kd)) q =
          .ok { e with v := (kd, q) :: e.v } := fun e q => by
        simp only [Eff.wV, fpIdx?_vOfF hkd]
        rfl
      name_eff55 "VUADDLV"
      simp only [hf, ht, regA, Bool.cond_false, hv, hw]
      rfl
    · have hw : ∀ (e : Eff) (q : BitVec 128), e.wV (arng8B (REG_F0 + kd)) q =
          .ok { e with v := (kd, q) :: e.v } := fun e q => by
        simp only [Eff.wV, fpIdx?_arng hkd]
        rfl
      name_eff55 "VCNT"
      simp only [hf, ht, regA, Bool.cond_true, hv, hw]
      rfl
  rw [progStep_eq hn hsk he rfl, effV_apply]

/-- `FRINTN`/`FRINTP`/`FRINTM`/`FRINTZ`/`FRINTA` `Fa, Fd` (`frintOf`): `fp1Op` of `V ka`. -/
theorem progStep_frint55 {op : Op} {n : Nat} {ft : BitVec 2} {opc : BitVec 6} {ka kd : Nat}
    (hka : ka < 32) (hkd : kd < 32) (hop : frintOf op = some (n, ft, opc))
    (hn : L.nextAddr p.id = some next) (has : p.as = opAsm op)
    (hf : p.from_ = regA (REG_F0 + ka)) (ht : p.to = regA (REG_F0 + kd)) :
    progStep L p s = .ok { s.wV (BitVec.ofNat 5 kd) (fp1Op ft opc (s.v (BitVec.ofNat 5 ka))) with
      pc := next } := by
  have hsk : p.isSkip = false := by
    rcases frintOf_some hop with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> (unfold Prog.isSkip; rw [has]; rfl)
  have he : progEffect ⟨L, s, p⟩ = .ok { v := [(kd, fp1Op ft opc (s.v (BitVec.ofNat 5 ka)))] } := by
    rcases frintOf_some hop with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    · first
        | name_eff55 "FRINTND" | name_eff55 "FRINTNS" | name_eff55 "FRINTPD"
        | name_eff55 "FRINTPS" | name_eff55 "FRINTMD" | name_eff55 "FRINTMS"
        | name_eff55 "FRINTZD" | name_eff55 "FRINTZS" | name_eff55 "FRINTAD"
        | name_eff55 "FRINTAS"
      simp only [hf, ht, regA, ctx_v_f0 hka, eff_wV_f0 hkd]
      rfl
  rw [progStep_eq hn hsk he rfl, effV_apply]

end Progs

/-! ## Values -/

private theorem int1_fval55 {w : Width} (g : BitVec w.bits → BitVec w.bits) (z : BitVec w.bits) :
    int1 w (fun a => .int w (g a)) [Arm64.fval w (.int w z)] = .int w (g z) := by
  simp [int1, Arm64.fval, Val.asInt]

/-- A unary float op of `Arm64.fop` shape on an operand related to `q` (`FArith.lean`'s
`fvalRel_int1` at one width). -/
private theorem fvalRel_un55 {w : Width} {g : BitVec w.bits → BitVec w.bits} {x : Val}
    {q q' : BitVec 128} (hx : FValRel x q) (hf : Fits w.bits x)
    (hg : FValRel (.int w (g (q.setWidth w.bits))) q') :
    FValRel ((int1 w (fun a => .int w (g a)) [Arm64.fval w x]).retypeL (.int w)) q' := by
  rcases fval_rel hx hf with rfl | rfl
  · show FValRel (Val.poison.retypeL _) _
    rw [retypeL_poison]; trivial
  · rw [int1_fval55, retypeL_int_self]; exact hg

/-- `VCNT`/`VUADDLV` of an argument of 64 bits related to the V register `q`: the machine's
`simdF55` of its low 64 bits, zero-extended. -/
theorem fvalRel_simd55 {op : Op} {cnt : Bool} (hop : op = cond cnt .ARM64VCNT .ARM64VUADDLV)
    {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val} {q : BitVec 128} (hx : FValRel x q)
    (hf : Fits 64 x) (hft : fTy t = true) (hct : cls t = some 64) :
    FValRel ((Arm64.evalPure op t k aux [x]).retypeL t)
      ((simdF55 cnt (q.setWidth 64)).setWidth 128) := by
  obtain ⟨rfl, -⟩ := fTy_eq (n := 8) hft hct
  subst hop
  rcases fval_rel (w := .w64) hx hf with rfl | rfl
  · cases cnt
    · show FValRel ((Arm64.op1 (.int .w64) GoFV.SSA.Sem.Arm64.vuaddlv [.poison]).retypeL _) _
      simp only [Arm64.op1, Arm64.reg]
      rw [retypeL_poison]; trivial
    · show FValRel ((Arm64.op1 (.int .w64) GoFV.SSA.Sem.Arm64.vcnt [.poison]).retypeL _) _
      simp only [Arm64.op1, Arm64.reg]
      rw [retypeL_poison]; trivial
  · cases cnt
    · show FValRel ((Arm64.op1 (.int .w64) GoFV.SSA.Sem.Arm64.vuaddlv
        [.int .w64 (q.setWidth 64)]).retypeL (.int .w64)) _
      simp only [Arm64.op1, Arm64.reg, Arm64.res, BitVec.setWidth_eq]
      rw [retypeL_int_self]
      exact fvalRel_setWidth (w := .w64) _
    · show FValRel ((Arm64.op1 (.int .w64) GoFV.SSA.Sem.Arm64.vcnt
        [.int .w64 (q.setWidth 64)]).retypeL (.int .w64)) _
      simp only [Arm64.op1, Arm64.reg, Arm64.res, BitVec.setWidth_eq]
      rw [retypeL_int_self]
      exact fvalRel_setWidth (w := .w64) _

/-- The `FRINT` rounds (`frintOf`) of an argument related to the V register `q`: the machine's
`fp1Op`. -/
theorem fvalRel_frint55 {op : Op} {n : Nat} {ft : BitVec 2} {opc : BitVec 6}
    (hop : frintOf op = some (n, ft, opc)) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {q : BitVec 128} (hx : FValRel x q) (hf : Fits (8 * n) x) (hft : fTy t = true)
    (hct : cls t = some (8 * n)) :
    FValRel ((Arm64.evalPure op t k aux [x]).retypeL t) (fp1Op ft opc q) := by
  obtain ⟨rfl, -⟩ := fTy_eq hft hct
  rcases frintOf_some hop with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact fvalRel_un55 (w := .w64) (g := GoFV.IEEE.roundInt Fmt.b64 .rne) hx hf (fvalRel_setWidth _)
  · exact fvalRel_un55 (w := .w32) (g := GoFV.IEEE.roundInt Fmt.b32 .rne) hx hf (fvalRel_setWidth _)
  · exact fvalRel_un55 (w := .w64) (g := GoFV.IEEE.roundInt Fmt.b64 .rpi) hx hf (fvalRel_setWidth _)
  · exact fvalRel_un55 (w := .w32) (g := GoFV.IEEE.roundInt Fmt.b32 .rpi) hx hf (fvalRel_setWidth _)
  · exact fvalRel_un55 (w := .w64) (g := GoFV.IEEE.roundInt Fmt.b64 .rmi) hx hf (fvalRel_setWidth _)
  · exact fvalRel_un55 (w := .w32) (g := GoFV.IEEE.roundInt Fmt.b32 .rmi) hx hf (fvalRel_setWidth _)
  · exact fvalRel_un55 (w := .w64) (g := GoFV.IEEE.roundInt Fmt.b64 .rz) hx hf (fvalRel_setWidth _)
  · exact fvalRel_un55 (w := .w32) (g := GoFV.IEEE.roundInt Fmt.b32 .rz) hx hf (fvalRel_setWidth _)
  · exact fvalRel_un55 (w := .w64) (g := GoFV.IEEE.roundInt Fmt.b64 .rna) hx hf (fvalRel_setWidth _)
  · exact fvalRel_un55 (w := .w32) (g := GoFV.IEEE.roundInt Fmt.b32 .rna) hx hf (fvalRel_setWidth _)

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- A float argument in a V register, read at its shape: `arg_relV` from `fargObj` (`G46.lean`). -/
private theorem farg_rel55 (F : Facts lc sym text az ez psA.toList ret E) (hm : LocMatch E s b i m)
    (hinv : CoreInv E.ι (StkAt E) K s) (hR : KRead lc v K) (hnp : v.op ≠ .Phi) {n c : Nat}
    {ra : Int} (hao : fargObj lc v n = .ok (c, ra)) :
    ∃ (a : ID) (k : Nat), v.args[n]? = some a ∧ ra = REG_F0 + k ∧ k < 32 ∧
      ∃ x, s.read lc a = .ok x ∧ FValRel x (m.v (BitVec.ofNat 5 k)) ∧ Fits c x := by
  obtain ⟨a0, r0, ha0, hah0, hfo0, hft0, hca0⟩ := fargObj_spec hao
  obtain ⟨ka, hka, rfl, hka'⟩ := fobjOf?_some hfo0
  have hr0 : r0 ≠ zeroReg := by have := (objV?_some hka').1; unfold zeroReg; omega
  exact ⟨a0, ka, ha0, rfl, hka,
    arg_relV F.lowered hm hinv hah0 hft0 hca0 (kread_arg hR hnp ha0 hah0 hca0 hr0) hka'⟩

/-- `VCNT Va.B8, Vd.B8` (`cnt`) or `VUADDLV Va.B8, Vd`. -/
theorem g55_simd (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {cnt : Bool} {ra rd : Int} (hop : v.op = cond cnt .ARM64VCNT .ARM64VUADDLV)
    (hsz1 : v.args.size = 1) (hao : fargObj lc v 0 = .ok (64, ra))
    (hro : fresObj lc v = .ok (64, rd)) (hvs : OneAt2 psA j (.ofShape (simdShape cnt ra rd)) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hmem := ops55a_simd hop
  have hnp := (ops55a_facts hmem).1
  obtain ⟨a0, ka, ha0, rfl, hka, x, hx, hxv, hxf⟩ := farg_rel55 F hm hinv hR hnp hao
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure55 hl htemp hmem hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have hz := fvalRel_simd55 (k := v.auxInt) (aux := v.aux) hop hxv hxf hft hcv
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hz (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi⟩
  obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
  rw [progStep_simd55 hka hkd (nextAddr_pcAt F.nodup hk0) has hf ht]
  rfl

/-- `FRINTN`/`FRINTP`/`FRINTM`/`FRINTZ`/`FRINTA` `Fa, Fd`. -/
theorem g55_frint (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {ft : BitVec 2} {opc : BitVec 6} {ra rd : Int}
    (hop : frintOf v.op = some (n, ft, opc)) (hsz1 : v.args.size = 1)
    (hao : fargObj lc v 0 = .ok (8 * n, ra)) (hro : fresObj lc v = .ok (8 * n, rd))
    (hvs : OneAt2 psA j (.ofShape { as := opAsm v.op, from_ := regA ra, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hmem := ops55a_frint hop
  have hnp := (ops55a_facts hmem).1
  obtain ⟨a0, ka, ha0, rfl, hka, x, hx, hxv, hxf⟩ := farg_rel55 F hm hinv hR hnp hao
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure55 hl htemp hmem hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have hz := fvalRel_frint55 (k := v.auxInt) (aux := v.aux) hop hxv hxf hft hcv
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hz (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi⟩
  obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
  rw [progStep_frint55 hka hkd hop (nextAddr_pcAt F.nodup hk0) has hf ht]
  rfl

end Cases

/-! ## The theorem -/

/-- One value of G55's group A: it runs its one Prog, keeps the match and `G3Inv`, and empties the
upper-bit table. -/
theorem vk55a_step {env : Env} {H : Hooks} {lc : LocCtx} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (F : Facts lc sym text az ez ps.toList ret E) (hVK : VK55a lc v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' ∧ UOKL m' (uStep35 lc L v) := by
  have hR := kread_of_reads hreads
  cases hVK with
  | simd hop hsz hao hro =>
    obtain ⟨r, hvh, -⟩ := fresObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g55_simd (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro hvs htemp hs
    refine ⟨m', h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_55a (ops55a_simd hop)]
    exact fun e he => by cases he
  | frint hop hsz hao hro =>
    obtain ⟨r, hvh, -⟩ := fresObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g55_frint (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro hvs htemp hs
    refine ⟨m', h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_55a (ops55a_frint hop)]
    exact fun e he => by cases he

end GoFV.Proof.Gen
