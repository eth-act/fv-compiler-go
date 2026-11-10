import GoFV.Proof.Gen.G45
import GoFV.Proof.Gen.FArith
import GoFV.Proof.Gen.Spec46

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G46 of the genssa validator: float arithmetic, conversions and compares
(`docs/plans/proofs3.md` §4, float stage (b))

`checkG46 lc` (`GoFV/Gen/Check46.lean`) is G45 with the float values that compute: `FADD`,
`FSUB`, `FMUL`, `FDIV`, `FNEG`, `FABS`, `FSQRT`, `FCVTSD`, `FCVTDS`, `SCVTF`/`UCVTF`,
`FCVTZS`/`FCVTZU`, `FCMP` (register and zero forms) and the fused `FMADD`/`FNMSUB`, each one
Prog. Phase 1 runs them as `Arm64.evalPure` (`stepLoc_pure46`); the machine as `fp2Op`, `fp1Op`,
`fcmpOp`, `fp3Op` or the conversions of `Exec.lean` (`FArith.lean`'s `progStep_*`), and the
value relations are `FArith.lean`'s: `fvalRel_fp2`, `fvalRel_fp1`, `fvalRel_cvtf`, `lo_fcvtz`,
`flagsRel_fcmp`, `flagsRel_fcmp0`, `fvalRel_fma`. Each case writes its V register (`op_regV`), its
X register (`op_reg2W`, the conversions to an integer) or the flags (`op_flags`).

Phase 1 and the machine disagree on NaN operands in two places (`FArith.lean`): `FADD`/`FMUL`
when both operands are NaNs of one kind and Phase 1's `FOps.ordered` swaps them (`FNaNSwap`), and
`FMADD`/`FNMSUB` when both multiplicands are NaNs of one kind (`FSameNaN`; genssa's operand order
swaps Phase 1's multiplicands). The run premise `FArithPre` excludes exactly these:
`g46_value` takes `G46Pre := G45Pre ∧ FArithPre`. The float blocks `FLT`/`FLE`/`FGT`/`FGE` are
`condBr` kinds (G1's terminators). `g46_initMem`, `g46_term`, `g46_nilPanic`, `g46_boundsPanic`
are G45's statements over `checkG46`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- The NaN operands on which Phase 1's result is not the machine's (`FArith.lean`): no
`FADD`/`FMUL` reads a `FNaNSwap` pair (arguments 0 and 1), no `FMADD`/`FNMSUB` multiplies an
`FSameNaN` pair (arguments 1 and 2). -/
def FArithPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  (∀ n ft opc, fp2Of v.op = some (n, ft, opc) → (opc = 0 ∨ opc = 2) → ∀ a0 a1 x y,
    v.args[0]? = some a0 → v.args[1]? = some a1 → s.read lc a0 = .ok x → s.read lc a1 = .ok y →
    ¬ FNaNSwap x y) ∧
  (∀ n ft o1 o0, fp3Of v.op = some (n, ft, o1, o0) → ∀ a1 a2 y z,
    v.args[1]? = some a1 → v.args[2]? = some a2 → s.read lc a1 = .ok y → s.read lc a2 = .ok z →
    ¬ FSameNaN y z)

/-- The per-value premises of G46: G45's (`G45Pre`), and `FArithPre`. -/
def G46Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop := G45Pre lc s v ∧ FArithPre lc s v

/-! ## The ops -/

/-- G46's ops: the rows of `fp2Of`, `fp1Of`, `cvtfOf`, `fcvtzOf`, `fcmpOf`, `fp3Of`. -/
def fops46 : List Op :=
  [.ARM64FADDD, .ARM64FADDS, .ARM64FSUBD, .ARM64FSUBS, .ARM64FMULD, .ARM64FMULS, .ARM64FDIVD,
    .ARM64FDIVS, .ARM64FNEGD, .ARM64FNEGS, .ARM64FABSD, .ARM64FABSS, .ARM64FSQRTD, .ARM64FSQRTS,
    .ARM64FCVTSD, .ARM64FCVTDS, .ARM64SCVTFWS, .ARM64SCVTFWD, .ARM64UCVTFWS, .ARM64UCVTFWD,
    .ARM64SCVTFS, .ARM64SCVTFD, .ARM64UCVTFS, .ARM64UCVTFD, .ARM64FCVTZSSW, .ARM64FCVTZSDW,
    .ARM64FCVTZUSW, .ARM64FCVTZUDW, .ARM64FCVTZSS, .ARM64FCVTZSD, .ARM64FCVTZUS, .ARM64FCVTZUD,
    .ARM64FCMPS, .ARM64FCMPD, .ARM64FCMPS0, .ARM64FCMPD0, .ARM64FMADDD, .ARM64FMADDS,
    .ARM64FMSUBD, .ARM64FMSUBS, .ARM64FNMADDD, .ARM64FNMADDS, .ARM64FNMSUBD, .ARM64FNMSUBS]

theorem fops46_fp2 {op : Op} {n : Nat} {ft : BitVec 2} {opc : BitVec 4}
    (h : fp2Of op = some (n, ft, opc)) : op ∈ fops46 := by
  rcases fp2Of_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [fops46]

theorem fops46_fp1 {op : Op} {ns nd : Nat} {ft : BitVec 2} {opc : BitVec 6}
    (h : fp1Of op = some (ns, nd, ft, opc)) : op ∈ fops46 := by
  rcases fp1Of_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [fops46]

theorem fops46_cvtf {op : Op} {u : Bool} {ns nd : Nat} (h : cvtfOf op = some (u, ns, nd)) :
    op ∈ fops46 := by
  rcases cvtfOf_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [fops46]

theorem fops46_fcvtz {op : Op} {u : Bool} {ns nd : Nat} (h : fcvtzOf op = some (u, ns, nd)) :
    op ∈ fops46 := by
  rcases fcvtzOf_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [fops46]

theorem fops46_fcmp {op : Op} {n : Nat} {ft : BitVec 2} {z : Bool}
    (h : fcmpOf op = some (n, ft, z)) : op ∈ fops46 := by
  rcases fcmpOf_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [fops46]

theorem fops46_fp3 {op : Op} {n : Nat} {ft : BitVec 2} {o1 o0 : Bool}
    (h : fp3Of op = some (n, ft, o1, o0)) : op ∈ fops46 := by
  rcases fp3Of_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [fops46]

/-- On an op outside G46's (`fops46`), `vkind46` is `vkind45`. -/
theorem vkind46_eq45 {lc : LocCtx} {g : G2In} {v : Value} (h : v.op ∉ fops46) :
    vkind46 lc g v = vkind45 lc g v := by
  unfold vkind46
  cases vkind45 lc g v with
  | ok _ => rfl
  | error e =>
    have h2 : fp2Of v.op = none := by
      cases hx : fp2Of v.op with
      | none => rfl
      | some x => obtain ⟨_, _, _⟩ := x; exact absurd (fops46_fp2 hx) h
    have h1 : fp1Of v.op = none := by
      cases hx : fp1Of v.op with
      | none => rfl
      | some x => obtain ⟨_, _, _, _⟩ := x; exact absurd (fops46_fp1 hx) h
    have hc : cvtfOf v.op = none := by
      cases hx : cvtfOf v.op with
      | none => rfl
      | some x => obtain ⟨_, _, _⟩ := x; exact absurd (fops46_cvtf hx) h
    have hz : fcvtzOf v.op = none := by
      cases hx : fcvtzOf v.op with
      | none => rfl
      | some x => obtain ⟨_, _, _⟩ := x; exact absurd (fops46_fcvtz hx) h
    have hm : fcmpOf v.op = none := by
      cases hx : fcmpOf v.op with
      | none => rfl
      | some x => obtain ⟨_, _, _⟩ := x; exact absurd (fops46_fcmp hx) h
    have h3 : fp3Of v.op = none := by
      cases hx : fp3Of v.op with
      | none => rfl
      | some x => obtain ⟨_, _, _, _⟩ := x; exact absurd (fops46_fp3 hx) h
    simp [fkind46, h2, h1, hc, hz, hm, h3]

set_option hygiene false in
/-- The 44 rows of `fops46` as hypotheses `h : op = …`. -/
local macro "fops46_cases" : tactic => `(tactic| (
  simp only [fops46, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h))

/-- G46's ops are pure arm64 ops that clobber nothing, no `Phi`, nil check, bounds check or entry
value. -/
theorem fops46_facts {op : Op} (hmem : op ∈ fops46) :
    op ≠ .Phi ∧ op ≠ .LoadReg ∧ op ≠ .StoreReg ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64MOVDnop ∧
      op.regInfo.clobbers.isEmpty = true ∧ op.regInfo.clobbersArg0 = false ∧
      op.regInfo.clobbersArg1 = false ∧ op.clobberFlags = false ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false ∧ entryOp24 op = false := by
  fops46_cases <;> subst h <;>
    exact ⟨nofun, nofun, nofun, nofun, nofun, rfl, rfl, rfl, rfl, nofun, rfl, rfl⟩

/-- G46's ops run as `Arm64.evalPure`. -/
theorem fops46_eval {env : Env} {ctx : Ctx} {fr : GoFV.SSA.Sem.Frame} {v : Value} {ty : Ty}
    (hmem : v.op ∈ fops46) (argv : List Val) :
    evalOpL true env ctx fr v argv ty = .ok (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  fops46_cases <;> (unfold evalOpL; rw [h]; rfl)

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- G46's values: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_pure46 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hmem : v.op ∈ fops46) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id
        ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL (lc.ty v.id)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := fops46_facts hmem
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht h1 h2 h3 h4 h5 h6 h7 h8 h9 h
  rw [fops46_eval hmem] at hr
  cases hr
  exact ⟨argv, hm, rfl⟩

end Step

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- A float argument in a V register, read at its shape: `arg_relV` from `fargObj`. -/
private theorem farg_rel (F : Facts lc sym text az ez psA.toList ret E) (hm : LocMatch E s b i m)
    (hinv : CoreInv E.ι (StkAt E) K s osp) (hR : KRead lc v K) (hnp : v.op ≠ .Phi) {n c : Nat}
    {ra : Int} (hao : fargObj lc v n = .ok (c, ra)) :
    ∃ (a : ID) (k : Nat), v.args[n]? = some a ∧ ra = REG_F0 + k ∧ k < 32 ∧
      ∃ x, s.read lc a = .ok x ∧ FValRel x (m.v (BitVec.ofNat 5 k)) ∧ Fits c x := by
  obtain ⟨a0, r0, ha0, hah0, hfo0, hft0, hca0⟩ := fargObj_spec hao
  obtain ⟨ka, hka, rfl, hka'⟩ := fobjOf?_some hfo0
  have hr0 : r0 ≠ zeroReg := by have := (objV?_some hka').1; unfold zeroReg; omega
  exact ⟨a0, ka, ha0, rfl, hka,
    arg_relV F.lowered hm hinv hah0 hft0 hca0 (kread_arg hR hnp ha0 hah0 hca0 hr0) hka'⟩

/-- `FADD`/`FSUB`/`FMUL`/`FDIV`: `op Fm, Fn, Fd`. -/
theorem g46_fbin (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : FArithPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {ft : BitVec 2} {opc : BitVec 4} {rn rm rd : Int}
    (hop : fp2Of v.op = some (n, ft, opc)) (hsz2 : v.args.size = 2)
    (hao : fargObj lc v 0 = .ok (8 * n, rn)) (hbo : fargObj lc v 1 = .ok (8 * n, rm))
    (hro : fresObj lc v = .ok (8 * n, rd))
    (hvs : OneAt2 psA j (.ofShape { as := opAsm v.op, from_ := regA rm, reg := rn, to := regA rd })
      j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hmem := fops46_fp2 hop
  have hnp := (fops46_facts hmem).1
  obtain ⟨a0, kn, ha0, rfl, hkn, x, hx, hxv, hxf⟩ := farg_rel F hm hinv hR hnp hao
  obtain ⟨a1, km, ha1, rfl, hkm, y, hy, hyv, hyf⟩ := farg_rel F hm hinv hR hnp hbo
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure46 hl htemp hmem hs
  rw [arr2 hsz2 ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have hz := fvalRel_fp2 (k := v.auxInt) (aux := v.aux) hop hxv hyv hxf hyf hft hcv
    (fun ho => hpre.1 _ _ _ hop ho a0 a1 x y ha0 ha1 hx hy)
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hz (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  obtain ⟨has, hf, hr, ht, -⟩ := Shape.ok_eq hok
  rw [progStep_fp2 hkn hkm hkd hop (nextAddr_pcAt F.nodup hk0) has hf hr ht]
  rfl

/-- `FNEG`/`FABS`/`FSQRT`/`FCVTSD`/`FCVTDS`: `op Fa, Fd`. -/
theorem g46_fun (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ns nd : Nat} {ft : BitVec 2} {opc : BitVec 6} {ra rd : Int}
    (hop : fp1Of v.op = some (ns, nd, ft, opc)) (hsz1 : v.args.size = 1)
    (hao : fargObj lc v 0 = .ok (8 * ns, ra)) (hro : fresObj lc v = .ok (8 * nd, rd))
    (hvs : OneAt2 psA j (.ofShape { as := opAsm v.op, from_ := regA ra, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hmem := fops46_fp1 hop
  have hnp := (fops46_facts hmem).1
  obtain ⟨a0, ka, ha0, rfl, hka, x, hx, hxv, hxf⟩ := farg_rel F hm hinv hR hnp hao
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure46 hl htemp hmem hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have hz := fvalRel_fp1 (k := v.auxInt) (aux := v.aux) hop hxv hxf hft hcv
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hz (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
  rw [progStep_fp1 hka hkd hop (nextAddr_pcAt F.nodup hk0) has hf ht]
  rfl

/-- `SCVTF`/`UCVTF`: `op Rn, Fd`. -/
theorem g46_cvtf (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {u : Bool} {ns nd ca : Nat} {rn rd : Int}
    (hop : cvtfOf v.op = some (u, ns, nd)) (hsz1 : v.args.size = 1)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hca : 8 * ns ≤ ca) (hro : fresObj lc v = .ok (8 * nd, rd))
    (hvs : OneAt2 psA j (.ofShape { as := opAsm v.op, from_ := regA rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hmem := fops46_cvtf hop
  have hnp := (fops46_facts hmem).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure46 hl htemp hmem hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have hz := fvalRel_cvtf (k := v.auxInt) (aux := v.aux) hA hop hxv hxf hca hft hcv
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hz (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
  rw [progStep_cvtf hkn hkd hop (nextAddr_pcAt F.nodup hk0) has hf ht]
  rfl

/-- `FCVTZS`/`FCVTZU`: `op Fn, Rd`. -/
theorem g46_fcvtz (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {u : Bool} {ns nd : Nat} {rn rd : Int}
    (hop : fcvtzOf v.op = some (u, ns, nd)) (hsz1 : v.args.size = 1)
    (hao : fargObj lc v 0 = .ok (8 * ns, rn)) (hro : resObj lc v = .ok (8 * nd, rd))
    (hvs : OneAt2 psA j (.ofShape { as := opAsm v.op, from_ := regA rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hmem := fops46_fcvtz hop
  have hnp := (fops46_facts hmem).1
  have hnd : nd = 4 ∨ nd = 8 := by
    rcases fcvtzOf_some hop with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ |
      ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> simp [h]
  obtain ⟨a0, ka, ha0, rfl, hka, x, hx, hxv, hxf⟩ := farg_rel F hm hinv hR hnp hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure46 hl htemp hmem hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv (by omega)
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_fcvtz (k := v.auxInt) (aux := v.aux) hop hxv hxf ht).mono
      (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, -, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_fcvtz hka hkd hop (nextAddr_pcAt F.nodup hk0) has hf ht', wX_pc]

/-- `FCMPS`/`FCMPD`: `FCMP Fm, Fn`. -/
theorem g46_fcmp (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {ft : BitVec 2} {rn rm : Int}
    (hop : fcmpOf v.op = some (n, ft, false)) (hfl : (lc.ty v.id).isFlags = true)
    (hhn : lc.home v.id = none) (hsz2 : v.args.size = 2)
    (hao : fargObj lc v 0 = .ok (8 * n, rn)) (hbo : fargObj lc v 1 = .ok (8 * n, rm))
    (hvs : OneAt2 psA j (.ofShape { as := opAsm v.op, from_ := regA rm, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hmem := fops46_fcmp hop
  have hnp := (fops46_facts hmem).1
  obtain ⟨a0, kn, ha0, rfl, hkn, x, hx, hxv, hxf⟩ := farg_rel F hm hinv hR hnp hao
  obtain ⟨a1, km, ha1, rfl, hkm, y, hy, hyv, hyf⟩ := farg_rel F hm hinv hR hnp hbo
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure46 hl htemp hmem hs
  rw [arr2 hsz2 ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_flags hhn hfl, isFlags_eq hfl]
  exact (op_flags F hm hinv hj hj' hvs
    (flagsRel_fcmp (k := v.auxInt) (aux := v.aux) hop hxv hyv hxf hyf)
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_fcmp hkn hkm hop (nextAddr_pcAt F.nodup hk) has hf hr])).imp
    fun m' ⟨h1, h2, h3, _, h5⟩ => ⟨h1, h2, h3, hsi, h5⟩

/-- `FCMPS0`/`FCMPD0`: `FCMP $(0.0), Fn`. -/
theorem g46_fcmp0 (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {ft : BitVec 2} {rn : Int}
    (hop : fcmpOf v.op = some (n, ft, true)) (hfl : (lc.ty v.id).isFlags = true)
    (hhn : lc.home v.id = none) (hsz1 : v.args.size = 1)
    (hao : fargObj lc v 0 = .ok (8 * n, rn))
    (hvs : OneAt2 psA j (.ofShape { as := opAsm v.op, from_ := fzeroA, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hmem := fops46_fcmp hop
  have hnp := (fops46_facts hmem).1
  obtain ⟨a0, kn, ha0, rfl, hkn, x, hx, hxv, hxf⟩ := farg_rel F hm hinv hR hnp hao
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure46 hl htemp hmem hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_flags hhn hfl, isFlags_eq hfl]
  exact (op_flags F hm hinv hj hj' hvs
    (flagsRel_fcmp0 (k := v.auxInt) (aux := v.aux) hop hxv hxf)
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_fcmp0 hkn hop (nextAddr_pcAt F.nodup hk) has (by rw [hf]; rfl) hr])).imp
    fun m' ⟨h1, h2, h3, _, h5⟩ => ⟨h1, h2, h3, hsi, h5⟩

/-- What `fmaPat` accepts. -/
theorem fmaPat_ok {op : Op} {ra rm rn rd : Int} {p : Prog} (h : (fmaPat op ra rm rn rd).ok p = true) :
    p.as = opAsm op ∧ p.from_ = regA rm ∧ p.reg = ra ∧ p.to = regA rd ∧
      p.rest = #[(0, regA rn)] := by
  simp only [fmaPat, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.2⟩

/-- `FMADD`/`FNMSUB`: `op Fm, Fa, Fn, Fd`. -/
theorem g46_fma (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : FArithPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {ft : BitVec 2} {o : Bool} {ra rm rn rd : Int}
    (hop : fp3Of v.op = some (n, ft, o, o)) (hsz3 : v.args.size = 3)
    (hao : fargObj lc v 0 = .ok (8 * n, ra)) (hmo : fargObj lc v 1 = .ok (8 * n, rm))
    (hno : fargObj lc v 2 = .ok (8 * n, rn)) (hro : fresObj lc v = .ok (8 * n, rd))
    (hvs : OneAt2 psA j (fmaPat v.op ra rm rn rd) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hmem := fops46_fp3 hop
  have hnp := (fops46_facts hmem).1
  obtain ⟨a0, ka, ha0, rfl, hka, x, hx, hxv, hxf⟩ := farg_rel F hm hinv hR hnp hao
  obtain ⟨a1, km, ha1, rfl, hkm, y, hy, hyv, hyf⟩ := farg_rel F hm hinv hR hnp hmo
  obtain ⟨a2, kn, ha2, rfl, hkn, z, hz, hzv, hzf⟩ := farg_rel F hm hinv hR hnp hno
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure46 hl htemp hmem hs
  rw [arr3 hsz3 ha0 ha1 ha2] at hargv
  obtain rfl := mapM_res_three hargv hx hy hz
  rw [write_reg hvh hcv]
  have hr := fvalRel_fma (k := v.auxInt) (aux := v.aux) hop hxv hyv hzv hxf hyf hzf hft hcv
    (hpre.2 _ _ _ _ hop a1 a2 y z ha1 ha2 hy hz)
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hr (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  obtain ⟨has, hf, hreg, ht, hrest⟩ := fmaPat_ok hok
  rw [progStep_fp3 hka hkn hkm hkd hop (nextAddr_pcAt F.nodup hk0) has hreg hf hrest ht]
  rfl

end Cases

/-! ## One value -/

/-- G35's table is empty after G46's values. -/
theorem uStep35_f46 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hmem : v.op ∈ fops46) : uStep35 lc L v = [] := by
  fops46_cases <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

/-- One value of G46's kinds: `vk45_step`'s statement, under `G46Pre`. -/
theorem vk46_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK46 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G46Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  have hR := kread_of_reads hreads
  have fin : v.op ∈ fops46 → ∀ m',
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp →
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
        UOKL m' (uStep35 lc L v) := fun hmem m' h1 h2 h3 h4 => by
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_f46 hmem]
    intro e he
    cases he
  cases hVK with
  | g45 hVK45 =>
    exact vk45_step hE F hhome hcf hv hVK45 hvs htemp hj hj' hreads hm hinv hL hmem hpre.1 hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | fbin hop hsz hao hbo hro =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g46_fbin (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hpre.2 hj hj' hop hsz hao hbo hro hvs htemp hs
    exact fin (fops46_fp2 hop) m' h1 h2 h3 h4
  | fun1 hop hsz hao hro =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g46_fun (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro hvs htemp hs
    exact fin (fops46_fp1 hop) m' h1 h2 h3 h4
  | cvtf hop hsz hao hca hro =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g46_cvtf (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hca hro hvs htemp hs
    exact fin (fops46_cvtf hop) m' h1 h2 h3 h4
  | fcvtz hop hsz hao hro =>
    obtain ⟨r, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g46_fcvtz (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro hvs htemp hs
    exact fin (fops46_fcvtz hop) m' h1 h2 h3 h4
  | fcmp hop hfl hhn hsz hao hbo =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g46_fcmp (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hfl hhn hsz hao hbo hvs htemp hs
    exact fin (fops46_fcmp hop) m' h1 h2 h3 h4
  | fcmp0 hop hfl hhn hsz hao =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g46_fcmp0 (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hfl hhn hsz hao hvs htemp hs
    exact fin (fops46_fcmp hop) m' h1 h2 h3 h4
  | fma hop hsz hao hmo hno hro =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g46_fma (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hpre.2 hj hj' hop hsz hao hmo hno hro hvs htemp
      hs
    exact fin (fops46_fp3 hop) m' h1 h2 h3 h4

/-- G46's values are no nil check. -/
theorem vk46_ops {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK46 lc g v kd) :
    VK45 lc g v kd ∨ v.op ∈ fops46 := by
  cases h with
  | g45 h => exact .inl h
  | fbin hop => exact .inr (fops46_fp2 hop)
  | fun1 hop => exact .inr (fops46_fp1 hop)
  | cvtf hop => exact .inr (fops46_cvtf hop)
  | fcvtz hop => exact .inr (fops46_fcvtz hop)
  | fcmp hop => exact .inr (fops46_fcmp hop)
  | fcmp0 hop => exact .inr (fops46_fcmp hop)
  | fma hop => exact .inr (fops46_fp3 hop)

/-- A nil check of G46's kinds is G7's. -/
theorem vk46_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK46 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  rcases vk46_ops h with h | h
  · exact vk45_nil h hop
  · exact absurd hop (fops46_facts h).2.2.2.2.2.2.2.2.2.1

/-- A bounds check of G46's kinds is G28's. -/
theorem vk46_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK46 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  rcases vk46_ops h with h | h
  · exact vk45_pb h hop
  · rw [(fops46_facts h).2.2.2.2.2.2.2.2.2.2.1] at hop
    cases hop

/-! ## The theorems on G46's check -/

/-- G45's values and G46's float values under G46's check, under `G46Pre`. -/
theorem g46L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG46L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G46Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_46L hl hc) hE hbid hb hi hv
      hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre.1.1.1.1.1 hcall hcallz hicall
      hwb hclo hgetg hmeq hs
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
    checkG46L_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind46_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk46_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- `InitMem` under G46's check: `g45L_initMem`'s statement. -/
theorem g46L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG46L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -⟩ := checkG46L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind46_initMem hop, vkind45_initMem hop, vkind44_initMem hop] at hkd
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

/-- G38's nil panics under G46's check. -/
theorem g46L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG46L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_46L hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG46L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind46_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk46_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G46's check. -/
theorem g46L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG46L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_46L hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG46L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind46_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk46_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G46's check (with the float blocks of `condBr`). -/
theorem g46L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG46L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_46L hl hc) hE hbid hb hm hinv hpre
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
    checkG46L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG46 lc`, on `liveCtx lc` -/

/-- **G46, values.** `g45_value`'s statement over `checkG46`, under `G46Pre` (G45's premise and
`FArithPre`: no `FADD`/`FMUL` of a `FNaNSwap` pair, no `FMADD`/`FNMSUB` of `FSameNaN`
multiplicands, where Phase 1's NaN is not the machine's). -/
theorem g46_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG46 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G46Pre (liveCtx lc) s v)
    (hcall : CallOK H E g L (liveCtx lc) s s' v m) (hcallz : CallOKZ H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOK H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOK H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L (liveCtx lc) s v m) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g46L_value (checkG46_spec hc).2 hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz hicall hwb hclo
    hgetg hmeq hs

/-- **G46, `InitMem`.** `g45_initMem`'s statement over `checkG46`. -/
theorem g46_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG46 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g46L_initMem (checkG46_spec hc).2 hE hl hbid hb hi hv hop hm hinv hpre hs

/-- **G46, nil panics.** `g45_nilPanic`'s statement over `checkG46`. -/
theorem g46_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG46 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g46L_nilPanic (checkG46_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G46, bounds panics.** `g45_boundsPanic`'s statement over `checkG46`. -/
theorem g46_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG46 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g46L_boundsPanic (checkG46_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G46, terminators.** `g45_term`'s statement over `checkG46` (the float blocks
`FLT`/`FLE`/`FGT`/`FGE` included through `condBr`). -/
theorem g46_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG46 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s)
    (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g46L_term (checkG46_spec hc).2 hE hbid hb hm hinv hpre hu ht

end GoFV.Proof.Gen
