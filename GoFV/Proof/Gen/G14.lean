import GoFV.Proof.Gen.G13
import GoFV.Proof.Gen.Spec14

/-!
# Soundness of the genssa validator's slice G14: register-index loads (`docs/plans/proofs3.md` §4)

`g14_value`, `g14_term`, `g14_nilPanic`: `g13_value`'s, `g13_term`'s and `g13_nilPanic`'s
statements over `checkG14`; `g14_value`'s per-value premise `G14Pre` adds to `G13Pre` that a
register-index load reads valid bytes (`IdxPre`, as `G3Pre` asks of a plain load).

`MOV…loadidx{,2,4,8} ptr idx mem` runs under `runLoc` as `Arm64.loadIdx` (`stepLoc_loadIdx`): the
`n` bytes at the address of `idxSum` (`ADD` of `ptr` and `idx · 2^sh`, with `ADD`'s pointer
cases), `poison` when there is none (`loadIdx_eq`). Genssa emits one load from `(Rp)(Ri<<sh)`,
whose address is `X[p] + (X[i] <<< sh)` (`ctx_mem_idx`). Both registers are related to the
arguments at class 64, so the sum is related to that word (`lo_idxSum`: `lo_add`, the index
register is the integer itself, `reg_low`); a valid access's address is then the injected address
of the bytes (`addr_rel`), outside the nil page, and the loaded register is G3's (`lo_loadN`,
`valRel_loadBool`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The opcodes -/

theorem loadIdxOp?_op {op : Op} {as : As} {n sh : Nat} {sg : Bool}
    (h : loadIdxOp? op = some (as, n, sh, sg)) :
    (op = .ARM64MOVDloadidx ∧ as = .MOVD ∧ n = 8 ∧ sh = 0 ∧ sg = false) ∨
    (op = .ARM64MOVWloadidx ∧ as = .MOVW ∧ n = 4 ∧ sh = 0 ∧ sg = true) ∨
    (op = .ARM64MOVWUloadidx ∧ as = .MOVWU ∧ n = 4 ∧ sh = 0 ∧ sg = false) ∨
    (op = .ARM64MOVHloadidx ∧ as = .MOVH ∧ n = 2 ∧ sh = 0 ∧ sg = true) ∨
    (op = .ARM64MOVHUloadidx ∧ as = .MOVHU ∧ n = 2 ∧ sh = 0 ∧ sg = false) ∨
    (op = .ARM64MOVBloadidx ∧ as = .MOVB ∧ n = 1 ∧ sh = 0 ∧ sg = true) ∨
    (op = .ARM64MOVBUloadidx ∧ as = .MOVBU ∧ n = 1 ∧ sh = 0 ∧ sg = false) ∨
    (op = .ARM64MOVHloadidx2 ∧ as = .MOVH ∧ n = 2 ∧ sh = 1 ∧ sg = true) ∨
    (op = .ARM64MOVHUloadidx2 ∧ as = .MOVHU ∧ n = 2 ∧ sh = 1 ∧ sg = false) ∨
    (op = .ARM64MOVWloadidx4 ∧ as = .MOVW ∧ n = 4 ∧ sh = 2 ∧ sg = true) ∨
    (op = .ARM64MOVWUloadidx4 ∧ as = .MOVWU ∧ n = 4 ∧ sh = 2 ∧ sg = false) ∨
    (op = .ARM64MOVDloadidx8 ∧ as = .MOVD ∧ n = 8 ∧ sh = 3 ∧ sg = false) := by
  unfold loadIdxOp? at h
  split at h <;> first | (cases h; simp) | cases h

/-- A register-index load is no `Phi`, reads `n ∈ {1, 2, 4, 8}` bytes (unsigned at 8) with a
shift below 4, and its opcode is a `movMem` load of `n` bytes. -/
theorem loadIdxOp?_facts {op : Op} {as : As} {n sh : Nat} {sg : Bool}
    (h : loadIdxOp? op = some (as, n, sh, sg)) :
    op ≠ .Phi ∧ (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) ∧ (n = 8 → sg = false) ∧ sh < 4 ∧
      ProgOp.movMem as.name = some (n, sg, false) := by
  rcases loadIdxOp?_op h with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
  exact ⟨nofun, by decide, by decide, by decide, rfl⟩

/-! ## `stepLoc` of a register-index load -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem loadIdx_core {n scale : Nat} {sg : Bool} (hl : lc.ctx.f.lowered = true)
    (ht : (lc.temps[v.id]?).join = none) (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg)
    (h2 : v.op ≠ .StoreReg) (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (hc : v.op.regInfo.clobbers.isEmpty = true) (hc0 : v.op.regInfo.clobbersArg0 = false)
    (hc1 : v.op.regInfo.clobbersArg1 = false) (hf : v.op.clobberFlags = false)
    (hev : ∀ argv, evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      .ok (Arm64.loadIdx (lc.ty v.id) n scale sg argv))
    {a0 a1 a2 : ID} (ha : v.args = #[a0, a1, a2]) {mm : Mem}
    (hm : s.read lc a2 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y, s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧
      s' = s.write lc v.id ((Arm64.loadIdx (lc.ty v.id) n scale sg [x, y, .mem mm]).retypeL
        (lc.ty v.id)) := by
  obtain ⟨argv, r, hmv, hr, rfl⟩ :=
    stepLoc_noclobber hl ht hne h1 h2 h3 h4 hc hc0 hc1 hf h
  rw [ha] at hmv
  change ((s.read lc a0).bind fun x => (s.read lc a1).bind fun y => (s.read lc a2).bind
    fun z => .ok [x, y, z]) = .ok argv at hmv
  rw [hev] at hr
  cases hr
  cases hx : s.read lc a0 with
  | panic e m0 => rw [hx] at hmv; cases hmv
  | stuck msg => rw [hx] at hmv; cases hmv
  | ok x =>
    cases hy : s.read lc a1 with
    | panic e m0 => rw [hx, hy] at hmv; cases hmv
    | stuck msg => rw [hx, hy] at hmv; cases hmv
    | ok y =>
      rw [hx, hy, hm] at hmv
      cases hmv
      exact ⟨x, y, rfl, rfl, rfl⟩

/-- A register-index load: `Arm64.loadIdx` of the arguments read from their homes, at scale
`2^sh`. -/
theorem stepLoc_loadIdx (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {as : As} {n sh : Nat} {sg : Bool} (hop : loadIdxOp? v.op = some (as, n, sh, sg))
    {a0 a1 a2 : ID} (ha : v.args = #[a0, a1, a2]) {mm : Mem}
    (hm : s.read lc a2 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y, s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧
      s' = s.write lc v.id ((Arm64.loadIdx (lc.ty v.id) n (2 ^ sh) sg [x, y, .mem mm]).retypeL
        (lc.ty v.id)) := by
  rcases loadIdxOp?_op hop with ⟨ho, rfl, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl, rfl⟩ |
    ⟨ho, rfl, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl, rfl⟩ |
    ⟨ho, rfl, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl, rfl⟩ |
    ⟨ho, rfl, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl, rfl⟩ | ⟨ho, rfl, rfl, rfl, rfl⟩ |
    ⟨ho, rfl, rfl, rfl, rfl⟩ <;>
  exact loadIdx_core hl ht (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
    (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl)
    (by rw [ho]; rfl) (fun _ => by unfold evalOpL; rw [ho]; rfl) ha hm h

end Step

/-! ## The address -/

/-- The register `Arm64.loadIdx` takes the address of: `ADD` of the base and the index scaled by
`scale` (`poison` when a scaled index has no register form). -/
def idxSum (scale : Nat) (x y : Val) : Val :=
  if scale = 1 then Arm64.add .other [x, y] else
    match Arm64.reg y with
    | some k => Arm64.add .other [x, .int .w64 (k * BitVec.ofNat 64 scale)]
    | none => .poison

/-- `Arm64.loadIdx` is the load at the address of `idxSum` (`poison` if it has none). -/
theorem loadIdx_eq (ty : Ty) (n scale : Nat) (sg : Bool) (x y : Val) (mm : Mem) :
    Arm64.loadIdx ty n scale sg [x, y, .mem mm] =
      (Arm64.addr (idxSum scale x y) 0).elim .poison (Arm64.loadN ty n sg mm) := by
  show (match Arm64.addr (idxSum scale x y) 0 with
    | some p => Arm64.loadN ty n sg mm p
    | none => .poison) = _
  cases Arm64.addr (idxSum scale x y) 0 <;> rfl

variable {ι : Blk → Option (BitVec 64)}

/-- `x · 2^sh` is `x <<< sh`. -/
theorem mul_twoPow_eq_shl (x : BitVec 64) (sh : Nat) : x * BitVec.ofNat 64 (2 ^ sh) = x <<< sh := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- The base and index registers related at class 64: `idxSum` and the machine's `X[p] + (X[i] <<<
sh)`, as an `ADD`'s result (`Lo` at 64 bits). -/
theorem lo_idxSum (hA : AddrAgree ι) {x y : Val} {X Y : BitVec 64} (hx : ValRel ι x X)
    (hy : ValRel ι y Y) (hfx : Fits 64 x) (hfy : Fits 64 y) (sh : Nat) :
    Lo ι 64 (idxSum (2 ^ sh) x y) (X + Y <<< sh) := by
  unfold idxSum
  by_cases h0 : sh = 0
  · subst h0
    simp only [Nat.pow_zero, ↓reduceIte, BitVec.shiftLeft_zero]
    exact lo_add hA hx hy hfx hfy (by decide) (Nat.le_refl _) (Nat.le_refl _) nofun
  · have h1 : 2 ^ sh ≠ 1 := by
      have := Nat.one_lt_two_pow h0
      omega
    simp only [h1, ↓reduceIte]
    cases hr : Arm64.reg y with
    | none => trivial
    | some k =>
      have hk : k = Y := by
        have := reg_low hA hy hfy hr
        simpa only [BitVec.setWidth_eq] using this
      subst hk
      have hy' : ValRel ι (.int .w64 (k * BitVec.ofNat 64 (2 ^ sh))) (k <<< sh) :=
        Or.inl (mul_twoPow_eq_shl k sh).symm
      exact lo_add hA hx hy' hfx rfl (by decide) (Nat.le_refl _) (Nat.le_refl _) nofun

/-- A 64-bit `ADD` result with an address is related to the machine word, at class 64. -/
theorem lo64_rel {z : Val} {Z : BitVec 64} (h : Lo ι 64 z Z) {p : Ptr}
    (hp : Arm64.addr z 0 = some p) : ValRel ι z Z ∧ Fits 64 z := by
  cases z with
  | int w x =>
    cases w with
    | w64 =>
      have hx : x = Z := by simpa only [Lo, BitVec.setWidth_eq] using h
      exact ⟨Or.inl hx.symm, rfl⟩
    | _ => exact (h : False).elim
  | ptr q =>
    rcases (h : 64 < 64 ∨ PtrRel ι q Z) with h | h
    · omega
    · exact ⟨h, rfl⟩
  | poison => cases hp
  | _ => exact (h : False).elim

/-! ## The per-value premise -/

/-- The per-value premise of a register-index load: it reads valid bytes (and a boolean is 0 or
1), as `G3Pre` asks of a plain load. -/
def IdxPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  ∀ as n sh sg, loadIdxOp? v.op = some (as, n, sh, sg) → ∀ a0 a1 x y, v.args[0]? = some a0 →
    v.args[1]? = some a1 → s.read lc a0 = .ok x → s.read lc a1 = .ok y →
    ∃ p mm bs, Arm64.addr (idxSum (2 ^ sh) x y) 0 = some p ∧ s.mem = .mem mm ∧
      mm.read p n = some bs ∧
      (lc.ty v.id = .bool → ∀ z, mm.load (.int .w8) p = .int .w8 z → z.toNat < 2)

/-- The per-value premises of G14: G13's, and `IdxPre`. -/
def G14Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop := G13Pre lc s v ∧ IdxPre lc s v

/-! ## The machine's load -/

/-- The address of `(Rn)(Ri)` or `(Rn)(Ri<<sh)` (`idxA`): `X[n] + (X[i] <<< sh)`. -/
theorem ctx_mem_idx {c : ProgCtx} {kn ki sh : Nat} (hkn : kn < 32) (hki : ki < 32) (hsh : sh < 8) :
    c.mem (idxA (REG_R0 + kn) (REG_R0 + ki) sh) =
      .ok (c.s.rX (BitVec.ofNat 5 kn) + c.s.rX (BitVec.ofNat 5 ki) <<< sh, none) := by
  have e0 : REG_R0 = 8192 := rfl
  have e1 : REG_LSL = 8704 := rfl
  have e2 : REG_EXT = 12288 := rfl
  by_cases h0 : sh = 0
  · subst h0
    have h1 : ((REG_R0 + (ki : Int)) != 0) = true := by rw [e0]; simp; omega
    have h2 : (decide (REG_EXT ≤ REG_R0 + (ki : Int)) &&
        decide (REG_R0 + (ki : Int) < REG_EXT + 4096)) = false := by
      rw [e0, e2]; simp; omega
    have h3 : (decide (REG_LSL ≤ REG_R0 + (ki : Int)) &&
        decide (REG_R0 + (ki : Int) < REG_LSL + 512)) = false := by
      rw [e0, e1]; simp; omega
    simp only [ProgCtx.mem, idxA, ↓reduceIte, h1, h2, h3, ctx_x_r0 hkn, ctx_x_r0 hki]
    simp only [BitVec.shiftLeft_zero]
    rfl
  · have hi : REG_LSL + 32 * (sh : Int) + (REG_R0 + ki - REG_R0) = 8704 + 32 * sh + ki := by
      rw [e1]; omega
    have h1 : (((8704 : Int) + 32 * sh + ki) != 0) = true := by simp; omega
    have h2 : (decide (REG_EXT ≤ (8704 : Int) + 32 * sh + ki) &&
        decide ((8704 : Int) + 32 * sh + ki < REG_EXT + 4096)) = false := by
      rw [e2]; simp; omega
    have h3 : (decide (REG_LSL ≤ (8704 : Int) + 32 * sh + ki) &&
        decide ((8704 : Int) + 32 * sh + ki < REG_LSL + 512)) = true := by
      rw [e1]; simp; omega
    have hd : ((8704 : Int) + 32 * sh + ki - REG_R0).toNat = 512 + 32 * sh + ki := by
      rw [e0]; omega
    have hm : (512 + 32 * sh + ki) % 32 = ki := by omega
    have hq : (512 + 32 * sh + ki) / 32 % 8 = sh := by omega
    simp only [ProgCtx.mem, idxA, h0, ↓reduceIte, hi, h1, h2, h3, hd, hm, hq, ctx_x_r0 hkn]
    rfl

/-! ## The value -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `g14_idx` with the registers of the machine after the load: the zero or sign extension of the
`n` loaded bytes written to `X[kd]`, `rd = R0 + kd`. -/
theorem g14_idxW (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : IdxPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n sh : Nat} {sg : Bool} {c : Nat} {rn ri rd : Int}
    (hop : loadIdxOp? v.op = some (as, n, sh, sg)) (hsz3 : v.args.size = 3)
    (hao : argObj lc v 0 = .ok (64, rn)) (hio : argObj lc v 1 = .ok (64, ri))
    (hma : memArg lc v 2 = .ok ()) (hro : resObj lc v = .ok (c, rd))
    (hc : 8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false)
    (hvs : OneAt2 psA j ⟨plain as (· == idxA rn ri sh) (· == regA rd), as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧
      ∃ (kd : Nat) (Y : BitVec (8 * n)), rd = GoFV.Asm.ARM64.REG_R0 + kd ∧
        m'.x = (m.wX (BitVec.ofNat 5 kd)
          (if sg then ProgOp.sextTo64 n (Y.setWidth 64) else Y.setWidth 64)).x := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, hn, hsg, hsh, hmov⟩ := loadIdxOp?_facts hop
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hio
  obtain ⟨ki, hki, rfl, hkki⟩ := objOf?_some hor1
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨x, y, hx, hy, rfl⟩ := stepLoc_loadIdx hl htemp hop (arr3 hsz3 ha0 ha1 ha2)
    (read_mem hl hah2 hamt hmm) hs
  obtain ⟨p, mm2, bs, hpa, hmm2, hrd, h01⟩ := hpre _ _ _ _ hop a0 a1 x y ha0 ha1 hx hy
  rw [hmm] at hmm2
  cases hmm2
  rw [write_reg hvh hcv, loadIdx_eq, hpa]
  simp only [Option.elim]
  -- the loaded register at the access's address
  have hval : ∀ a, E.ι p.blk = some a →
      ValRel E.ι ((Arm64.loadN (lc.ty v.id) n sg mm p).retypeL (lc.ty v.id))
        (if sg then ProgOp.sextTo64 n ((readMem m.mem (a + p.off) n).setWidth 64)
         else (readMem m.mem (a + p.off) n).setWidth 64) := by
    intro a ha
    rcases hc with h8 | ⟨rfl, rfl, rfl⟩
    · have ht := cls_ne_bool hcv h8
      exact valRel_retypeL_lo hA hcv ht ((lo_loadN hA hMI hn hsg ht ha hrd).mono (cls_le hcv))
    · have ht := cls_bool hcv
      rw [ht]
      exact valRel_loadBool hA hMI ha hrd (h01 ht)
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  rw [hx] at hX
  cases hX
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkki
  rw [hy] at hY
  cases hY
  obtain ⟨hzv, hzf⟩ := lo64_rel (lo_idxSum hA hxv hyv hxf hyf sh) hpa
  obtain ⟨a, hpa', haeq, hnil⟩ := addr_rel hA hMI hzv hzf hpa (by omega : 0 < n)
    (Or.inr (by rw [hrd]; rfl))
  have haeq' : m.rX (BitVec.ofNat 5 kn) + m.rX (BitVec.ofNat 5 ki) <<< sh = a + p.off := by
    simpa using haeq
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (hval a hpa') (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, kd, _, rfl, h4⟩
  obtain ⟨has, hf, -, ht', -, -, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf ht'
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].from_ =
      .ok (a + p.off, none) := by
    rw [hf, ctx_mem_idx hkn hki (by omega)]
    exact congrArg (fun z => Except.ok (z, none)) haeq'
  rw [progStep_loadAt hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov)
    (by rw [hf]; rfl) hma' ht' hnil, wX_pc]

/-- A register-index load `MOV… (Rp)(Ri<<sh), Rd` of `n` valid bytes. -/
theorem g14_idx (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : IdxPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n sh : Nat} {sg : Bool} {c : Nat} {rn ri rd : Int}
    (hop : loadIdxOp? v.op = some (as, n, sh, sg)) (hsz3 : v.args.size = 3)
    (hao : argObj lc v 0 = .ok (64, rn)) (hio : argObj lc v 1 = .ok (64, ri))
    (hma : memArg lc v 2 = .ok ()) (hro : resObj lc v = .ok (c, rd))
    (hc : 8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false)
    (hvs : OneAt2 psA j ⟨plain as (· == idxA rn ri sh) (· == regA rd), as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' :=
  (g14_idxW (H := H) F hm hinv hsi hR hK hpre hj hj' hop hsz3 hao hio hma hro hc hvs htemp
    hs).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end Cases

/-! ## The theorems -/

/-- One value of G14's kinds (`VK14`) emitted at the Progs from `j` to `j'`: `vk13_step`'s
statement for G14's values, under G14's per-value premises. -/
theorem vk14_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK14 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : G14Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOK H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' := by
  cases hVK with
  | g13 hVK13 =>
    exact vk13_step hE F hhome hcf hv hVK13 hvs htemp hj hj' hreads hm hinv hpre.1 hcall hicall
      hwb hclo hs
  | idx hop hsz3 hao hio hma hro hc =>
    obtain ⟨r, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g14_idx (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hpre.2 hj hj' hop hsz3
      hao hio hma hro hc hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩⟩

/-- **G14, values.** `g13_value`'s statement over `checkG14`, under G14's per-value premises
(`G14Pre`: G13's, and a register-index load reads valid bytes). -/
theorem g14_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG14 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks⟩ := checkG14_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind14_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk14_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre hcall hicall hwb hclo
    hs

/-- **G14, nil panics.** `g13_nilPanic`'s statement over `checkG14`. -/
theorem g14_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG14 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG14_spec hc
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
  obtain ⟨-, hVK⟩ := vkind14_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | g13 hVK13 =>
    cases hVK13 with
    | g12 hVK12 =>
      cases hVK12 with
      | g11 hVK11 =>
        cases hVK11 with
        | g10 hVK10 =>
          cases hVK10 with
          | g9 hVK9 =>
            cases hVK9 with
            | g8 _ hVK8 =>
              cases hVK8 with
              | g7 hVK7 =>
                cases hVK7 with
                | g6 hne _ => exact absurd hop hne
                | nil _ hsz2 _ _ hao hma =>
                  exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2
                    hao hma hvs hs
              | wb hop' => rw [hop] at hop'; cases hop'
              | sel0 hop' => rw [hop] at hop'; cases hop'
              | sel1 hop' => rw [hop] at hop'; cases hop'
            | call hop' => rw [hop] at hop'; cases hop'
          | icall hn => rw [hop] at hn; cases hn
          | selMem hop' => rw [hop] at hop'; cases hop'
          | selReg hop' => rw [hop] at hop'; cases hop'
        | clo hop' => rw [hop] at hop'; cases hop'
      | conv hop' => rw [hop] at hop'; cases hop'
    | zero hop' => rw [hop] at hop'; cases hop'
  | idx hop' => rw [hop] at hop'; cases hop'

/-- **G14, terminators.** `g13_term`'s statement over `checkG14`. -/
theorem g14_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG14 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG14_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
