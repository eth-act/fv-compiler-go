import GoFV.Proof.Gen.FMove
import GoFV.Proof.Gen.Spec44

/-!
# Slice G44 of the genssa validator: floating-point moves, loads and stores
(`docs/plans/proofs3.md` §4)

`checkG44 lc` (`GoFV/Gen/Check44.lean`) is G43 with the values that move a float's bit pattern
(`.int .w32`/`.int .w64`) through the V registers: `Copy` between `F` registers
(`FMOVS`/`FMOVD Fs, Fd`, or nothing), `FMOVSload`/`FMOVDload`, `FMOVSstore`/`FMOVDstore`,
`FMOVSgpfp`/`FMOVDgpfp` (`Rn → Fd`), `FMOVSfpgp`/`FMOVDfpgp` (`Fn → Rd`) and
`FMOVSconst`/`FMOVDconst` (`$c, Fd`). `LocMatch` relates a V register to its value's low bits
(`FValRel`); each case writes its register (`op_regV` for a V register, `op_reg2W` for `fpgp`'s X
register) or its memory (`memInj_storeN`), with the value relation from `FMove.lean`:

* a copy and a float store read the argument's V register at its float shape (`arg_relV`) and
  move its low `8n` bits (`maskN_v_low`); the store writes the bytes of the value as G3's does,
  its word the V register's low 64 bits (`valRel_of_fvalRel`);
* a float load is G3's `n`-byte load (`lo_loadN`), related to the V register by
  `fvalRel_of_valRel`; that needs the loaded value at its shape to be no pointer without an integer
  form (a pointer has no V register form), the run premise `FLoadPre` (with G3's: the bytes are
  valid);
* `FMOVgpfp` moves the low `8n` bits of an X register of a class of at least `8n` (`reg_low`);
  `FMOVfpgp` moves the low `8n` bits of a float, zero-extended (`lo_fmovVX`);
* `FMOVconst` writes `fconstBits n` of `auxInt`'s bits, Phase 1's `Const64F`/`Const32F`
  (`fvalRel_fconst`: `FMOVS` rounds the `float64` to single precision as `Const32F` does).

None of these writes an X register but `fpgp`, so G35's upper-bit table drops the entry of the
home (`Copy`, `uokl_keep`) or is empty after them (`uStep35_f44`). `g44_value` takes
`G44Pre := G41Pre ∧ FLoadPre`; `g44_initMem`, `g44_term`, `g44_nilPanic`, `g44_boundsPanic` are
G43's statements over `checkG44`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- A float load reads `n` valid bytes at its address (`symAddr`), and what it reads at its shape
is no pointer without an integer form (a pointer has no V register form). -/
def FLoadPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  (v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload) → ∀ a x, v.args[0]? = some a →
    s.read lc a = .ok x → ∃ p mm bs, symAddr lc.ctx v x = some p ∧ s.mem = .mem mm ∧
      mm.read p (fBytes v.op) = some bs ∧
      ∀ q, (Arm64.loadN (lc.ty v.id) (fBytes v.op) false mm p).retypeL (lc.ty v.id) ≠ .ptr q

/-- The per-value premises of G44: G41's (`G41Pre`), and `FLoadPre`. -/
def G44Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop := G41Pre lc s v ∧ FLoadPre lc s v

/-! ## `stepLoc` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_two' {a b : ID} :
    [a, b].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => .ok [x, y] := rfl

private theorem mapM_three' {a b c : ID} :
    [a, b, c].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        .ok [x, y, z] := rfl

/-- G44's pure ops: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_pureF (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64FMOVSgpfp ∨ v.op = .ARM64FMOVDgpfp ∨ v.op = .ARM64FMOVSfpgp ∨
      v.op = .ARM64FMOVDfpgp ∨ v.op = .ARM64FMOVSconst ∨ v.op = .ARM64FMOVDconst)
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id
        ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL (lc.ty v.id)) := by
  rcases hop with hop | hop | hop | hop | hop | hop <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv) := by
      unfold evalOpL; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨argv, hm, rfl⟩

/-- A float load (`FMOVSload`/`FMOVDload [off] {sym} a mem`): the `fBytes`-byte load at `symAddr`
(`poison` if there is none). -/
theorem stepLoc_fload (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload)
    {a0 a1 : ID} (ha : v.args = #[a0, a1]) {mm : Mem} (hm : s.read lc a1 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id
        (((symAddr lc.ctx v x).elim .poison (Arm64.loadN (lc.ty v.id) (fBytes v.op) false mm)).retypeL
          (lc.ty v.id)) := by
  rcases hop with ho | ho <;>
  · obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [ho]; nofun)
      (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
      (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) h
    rw [ha] at hmap
    change [a0, a1].mapM (s.read lc) = _ at hmap
    rw [mapM_two'] at hmap
    cases hx : s.read lc a0 with
    | panic e m => rw [hx] at hmap; cases hmap
    | stuck msg => rw [hx] at hmap; cases hmap
    | ok x =>
      rw [hx, hm] at hmap; cases hmap
      have hev : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
          arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) := by
        unfold evalOpL; rw [ho]; rfl
      rw [hev] at hr
      cases hn : nilFaults true lc.ctx v [x, .mem mm] with
      | some m =>
        have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) = .panic .nilDeref m := by
          unfold arm64Op; rw [hn]
        rw [he] at hr; cases hr
      | none =>
        have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
            .ok ((symAddr lc.ctx v x).elim .poison
              (Arm64.loadN (lc.ty v.id) (fBytes v.op) false mm)) := by
          unfold arm64Op; rw [hn, ho]; rfl
        rw [he] at hr; cases hr
        exact ⟨x, rfl, rfl⟩

/-- A float store (`FMOVSstore`/`FMOVDstore [off] {sym} a x mem`): the `fBytes`-byte store of `x`
at `symAddr`, which succeeded. -/
theorem stepLoc_fstore (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore) {a0 a1 a2 : ID}
    (ha : v.args = #[a0, a1, a2]) {mm : Mem} (hm : s.read lc a2 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x y p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ symAddr lc.ctx v x = some p ∧
      mm.write p (Arm64.storeBytes (fBytes v.op) y) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  rcases hop with ho | ho <;>
  · obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [ho]; nofun)
      (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
      (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) h
    rw [ha] at hmap
    change [a0, a1, a2].mapM (s.read lc) = _ at hmap
    rw [mapM_three'] at hmap
    cases hx : s.read lc a0 with
    | panic e m => rw [hx] at hmap; cases hmap
    | stuck msg => rw [hx] at hmap; cases hmap
    | ok x =>
    cases hy : s.read lc a1 with
    | panic e m => rw [hx, hy] at hmap; cases hmap
    | stuck msg => rw [hx, hy] at hmap; cases hmap
    | ok y =>
      rw [hx, hy, hm] at hmap; cases hmap
      have hev : evalOpL true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
          arm64Op true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) := by
        unfold evalOpL; rw [ho]; rfl
      rw [hev] at hr
      cases hn : nilFaults true lc.ctx v [x, y, .mem mm] with
      | some m =>
        have he : arm64Op true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
            .panic .nilDeref m := by
          unfold arm64Op; rw [hn]
        rw [he] at hr; cases hr
      | none =>
        have he : ∃ w m1 m2, arm64Op true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
            match symAddr lc.ctx v x with
            | some p => writeRes w (Arm64.storeN (fBytes v.op) p y mm)
            | none =>
              if [x, y, Val.mem mm].any (fun | .poison => true | _ => false) then .stuck m1
              else .stuck m2 := ⟨_, _, _, by unfold arm64Op; rw [hn, ho]; rfl⟩
        obtain ⟨w, m1, m2, he⟩ := he
        cases hp : symAddr lc.ctx v x with
        | none =>
          rw [hp] at he; rw [he] at hr
          dsimp only at hr
          split at hr <;> cases hr
        | some p =>
          rw [hp] at he; rw [he] at hr
          change writeRes _ (mm.write p (Arm64.storeBytes (fBytes v.op) y)) = _ at hr
          cases hw : mm.write p (Arm64.storeBytes (fBytes v.op) y) with
          | none => rw [hw] at hr; cases hr
          | some mm' =>
            rw [hw] at hr; cases hr
            exact ⟨x, y, p, mm', rfl, rfl, hp, hw, rfl⟩

end Step

/-! ## Values -/

/-- The `float64` bits of an `Int64` constant as an `FCONST` operand holds them. -/
theorem int64_bits (k : Int64) : BitVec.ofNat 64 k.toUInt64.toNat = BitVec.ofInt 64 k.toInt := by
  have h1 : k.toUInt64.toNat = k.toBitVec.toNat := rfl
  have h2 : k.toInt = k.toBitVec.toInt := rfl
  rw [h1, h2, BitVec.ofInt_toInt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A value at an integer shape is no boolean. -/
theorem retypeL_int_ne_bool {w : Width} (x : Val) (b : Bool) : x.retypeL (.int w) ≠ .bool b := by
  intro h
  cases w <;> cases x
  all_goals first
    | (rename_i w' y; cases w' <;> simp [Val.retypeL, Val.widen, Val.retype, Width.bits] at h <;>
        split at h <;> cases h)
    | (simp [Val.retypeL, Val.widen, Val.retype] at h; done)
    | (simp only [Val.retypeL, Val.widen, Val.retype, Ptr.word] at h
       split at h
       · cases h
       · split at h <;> cases h)

/-- The width of a float of `n` bytes. -/
def fW (n : Nat) : Width := if n = 4 then .w32 else .w64

/-- The `FMOV` opcode of a float of `8n` bits moves `n` bytes between the register files. -/
theorem fmovAs_movMem {n : Nat} (hn : n = 4 ∨ n = 8) :
    ProgOp.movMem (fmovAs (8 * n)).name = some (n, false, true) := by
  rcases hn with rfl | rfl <;> rfl

/-- `fBytes` is 4 or 8. -/
theorem fBytes_cases (op : Op) : fBytes op = 4 ∨ fBytes op = 8 := by
  unfold fBytes; split <;> simp

/-- A float shape of class `8n`. -/
theorem fTy_eq {t : Ty} {n : Nat} (h : fTy t = true) (hc : cls t = some (8 * n)) :
    t = .int (fW n) ∧ (n = 4 ∨ n = 8) := by
  rcases fTy_spec h with ⟨rfl, h'⟩ | ⟨rfl, h'⟩
  · have : 8 * n = 32 := Option.some.inj (hc.symm.trans h')
    have hn : n = 4 := by omega
    subst hn
    exact ⟨rfl, .inl rfl⟩
  · have : 8 * n = 64 := Option.some.inj (hc.symm.trans h')
    have hn : n = 8 := by omega
    subst hn
    exact ⟨rfl, .inr rfl⟩

theorem rt_64_32 (z : BitVec 64) : (Val.int .w64 z).retypeL (.int .w32) = .int .w32 (z.setWidth 32) :=
  rfl

theorem rt_64_64 (z : BitVec 64) : (Val.int .w64 z).retypeL (.int .w64) = .int .w64 z := by
  show Val.int .w64 (z.setWidth 64) = _
  rw [BitVec.setWidth_eq]

theorem rt_32_32 (z : BitVec 32) : (Val.int .w32 z).retypeL (.int .w32) = .int .w32 z := by
  show Val.int .w32 (z.setWidth 32) = _
  rw [BitVec.setWidth_eq]

/-- `maskN n` of a V register's low word keeps its low `8n` bits. -/
theorem maskN_v_low {n : Nat} (hn : n = 4 ∨ n = 8) (q : BitVec 128) :
    ((ProgOp.maskN n (q.setWidth 64)).setWidth 128).setWidth (8 * n) = q.setWidth (8 * n) := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), maskN_low hn,
    BitVec.setWidth_setWidth_of_le _ (by omega)]

/-- `maskN n` of an X register keeps its low `8n` bits. -/
theorem maskN_x_low {n : Nat} (hn : n = 4 ∨ n = 8) (X : BitVec 64) :
    ((ProgOp.maskN n X).setWidth 128).setWidth (8 * n) = X.setWidth (8 * n) := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), maskN_low hn]

/-- `FMOVgpfp` of an X register of class `ca ≥ 8n` at a float shape of `8n` bits. -/
theorem fvalRel_gpfp {ι : Blk → Option (BitVec 64)} (hA : AddrAgree ι) {x : Val} {X : BitVec 64}
    {ca n : Nat} (hx : ValRel ι x X) (hf : Fits ca x) (hn : n = 4 ∨ n = 8) (hca : 8 * n ≤ ca) :
    FValRel ((Arm64.fmov (fW n) (.int (fW n)) [x]).retypeL (.int (fW n)))
      ((ProgOp.maskN n X).setWidth 128) := by
  cases hr : Arm64.reg x with
  | none =>
    simp only [Arm64.fmov, hr, retypeL_poison]
    trivial
  | some X' =>
    have hlow := reg_low hA hx hf hr
    have h8 : X'.setWidth (8 * n) = X.setWidth (8 * n) := by
      have := congrArg (BitVec.setWidth (8 * n)) hlow
      simpa only [BitVec.setWidth_setWidth_of_le _ hca] using this
    rcases hn with rfl | rfl
    · have he : Arm64.fmov (fW 4) (.int (fW 4)) [x] =
          .int .w64 ((X'.setWidth 32).setWidth 64) := by
        simp only [Arm64.fmov, hr]; rfl
      rw [he]
      show FValRel ((Val.int .w64 ((X'.setWidth 32).setWidth 64)).retypeL (.int .w32)) _
      rw [rt_64_32]
      show ((ProgOp.maskN 4 X).setWidth 128).setWidth 32 =
        ((X'.setWidth 32).setWidth 64).setWidth 32
      rw [maskN_x_low (Or.inl rfl), BitVec.setWidth_setWidth_of_le _ (by omega)]
      exact h8.symm
    · have he : Arm64.fmov (fW 8) (.int (fW 8)) [x] = .int .w64 X' := by
        simp only [Arm64.fmov, hr]; rfl
      rw [he]
      show FValRel ((Val.int .w64 X').retypeL (.int .w64)) _
      rw [rt_64_64]
      show ((ProgOp.maskN 8 X).setWidth 128).setWidth 64 = X'
      rw [maskN_x_low (Or.inr rfl)]
      have : X'.setWidth 64 = X.setWidth 64 := h8
      simpa only [BitVec.setWidth_eq] using this.symm

/-- The zero extension of the low 32 bits of a V register's low word. -/
theorem low32_v (q : BitVec 128) :
    ((q.setWidth 32).setWidth 64 : BitVec 64) = ProgOp.maskN 4 (q.setWidth 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show _ = ((q.setWidth 64) &&& BitVec.ofNat 64 (2 ^ 32 - 1)).getLsbD i
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases h32 : i < 32
  · simp [h32, hi, show i < 128 by omega]
  · simp [h32]

/-- `FMOVfpgp` of a float of `8n` bits: the register's low word, the low `8n` bits zero-extended. -/
theorem lo_fmovVX {ι : Blk → Option (BitVec 64)} {x : Val} {q : BitVec 128} {n : Nat}
    (hn : n = 4 ∨ n = 8) (hx : FValRel x q) (hf : Fits (8 * n) x) {t : Ty} (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.fmov (fW n) t [x]) (ProgOp.maskN n (q.setWidth 64)) := by
  rcases fval_cases hx hf with rfl | ⟨w, y, rfl, hw⟩
  · trivial
  · have hres : ∀ r : BitVec 64, Arm64.res t r = .int .w64 r := by
      intro r; cases t <;> first | rfl | exact absurd rfl ht
    have hy : q.setWidth w.bits = y := hx
    subst hy
    rcases hn with rfl | rfl
    · have hw' : w = .w32 := by cases w <;> simp_all [Width.bits]
      subst hw'
      have he : Arm64.fmov (fW 4) t [.int .w32 (q.setWidth 32)] =
          .int .w64 ((q.setWidth 32).setWidth 64) := by
        show Arm64.fmov .w32 t [.int .w32 (q.setWidth 32)] = _
        simp only [Arm64.fmov, Arm64.reg, hres]
        rw [BitVec.setWidth_setWidth_of_le (q.setWidth 32) (show 32 ≤ 64 by omega),
          BitVec.setWidth_eq]
      rw [he]
      show ((q.setWidth 32).setWidth 64).setWidth 64 = (ProgOp.maskN 4 (q.setWidth 64)).setWidth 64
      rw [BitVec.setWidth_eq, BitVec.setWidth_eq, ← low32_v]
    · have hw' : w = .w64 := by cases w <;> simp_all [Width.bits]
      subst hw'
      have he : Arm64.fmov (fW 8) t [.int .w64 (q.setWidth 64)] = .int .w64 (q.setWidth 64) := by
        show Arm64.fmov .w64 t [.int .w64 (q.setWidth 64)] = _
        simp only [Arm64.fmov, Arm64.reg, hres, BitVec.setWidth_eq]
      rw [he]
      rfl

/-- `FMOVconst` of `8n` bits: Phase 1's `Const32F`/`Const64F` and the bits `fconstBits n` of the
`FCONST` operand. -/
theorem fvalRel_fconst {n : Nat} (hn : n = 4 ∨ n = 8) (k : Int64) :
    FValRel ((if n = 4 then FOps.const32 k else FOps.const64 k).retypeL (.int (fW n)))
      (fconstBits n k.toUInt64) := by
  rcases hn with rfl | rfl
  · show FValRel ((FOps.const32 k).retypeL (.int .w32)) (fconstBits 4 k.toUInt64)
    unfold FOps.const32
    rw [rt_32_32]
    show ((GoFV.IEEE.convert GoFV.IEEE.Fmt.b64 GoFV.IEEE.Fmt.b32 .rne
        (BitVec.ofNat 64 k.toUInt64.toNat)).setWidth 128).setWidth 32 = _
    rw [BitVec.setWidth_setWidth_of_le _ (by omega), int64_bits]
    exact BitVec.setWidth_eq _
  · show FValRel ((FOps.const64 k).retypeL (.int .w64)) (fconstBits 8 k.toUInt64)
    unfold FOps.const64
    rw [rt_64_64]
    show ((BitVec.ofNat 64 k.toUInt64.toNat).setWidth 128).setWidth 64 = _
    rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, int64_bits]

/-- `m` with its own V register written back, at its PC. -/
theorem wV_self_pc (m : MState) (k : GoFV.Arm64.Reg) :
    ({ m.wV k (m.v k) with pc := m.pc } : MState) = m := by
  cases m
  simp only [MState.wV, MState.mk.injEq, and_true, true_and]
  funext i
  split <;> simp_all

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat} {g : G2In}

/-- A `Copy` of a float register to another: `FMOVS`/`FMOVD Fs, Fd`. -/
theorem g44_fcopy (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : Nat} {ra rd : Int} (hop : v.op = .Copy) (hsz1 : v.args.size = 1)
    (hao : fargObj lc v 0 = .ok (c, ra)) (hro : fresObj lc v = .ok (c, rd))
    (hvs : OneAt2 psA j (.ofShape { as := fmovAs c, from_ := regA ra, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧ m'.x = m.x := by
  have hl := F.lowered
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hfo0, hft0, hca0⟩ := fargObj_spec hao
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨ka, hka, rfl, hka'⟩ := fobjOf?_some hfo0
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  have hr0 : r0 ≠ zeroReg := by have := (objV?_some hka').1; unfold zeroReg; omega
  obtain ⟨x, hx, hxv, hxf⟩ := arg_relV hl hm hinv hah0 hft0 hca0
    (kread_arg hR hnp ha0 hah0 hca0 hr0) hka'
  obtain ⟨y, hy, rfl⟩ := stepLoc_copy hl htemp hop (arr1 hsz1 ha0) hs
  rw [hx] at hy
  cases hy
  rw [write_reg hvh hcv]
  obtain ⟨n, rfl, hn⟩ : ∃ n, c = 8 * n ∧ (n = 4 ∨ n = 8) := by
    rcases fTy_spec hft with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [hcv] at h <;> cases h
    · exact ⟨4, rfl, .inl rfl⟩
    · exact ⟨8, rfl, .inr rfl⟩
  have hz := fvalRel_retypeL hxv hxf hft hcv
  have hzf := fits_retypeL hcv x
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd'
    (fvalRel_low hz hzf (maskN_v_low hn (m.v (BitVec.ofNat 5 ka)))) hzf
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
  rw [progStep_fmovVV hka hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact fmovAs_movMem hn)
    hf ht]
  rfl

/-- A `Copy` of a float register to itself: no code. -/
theorem g44_fcopyNone (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : Nat} {ra : Int} (hop : v.op = .Copy) (hsz1 : v.args.size = 1)
    (hao : fargObj lc v 0 = .ok (c, ra)) (hro : fresObj lc v = .ok (c, ra)) (hvs : j' = j)
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧ m'.x = m.x := by
  have hl := F.lowered
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hfo0, hft0, hca0⟩ := fargObj_spec hao
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨ka, hka, rfl, hka'⟩ := fobjOf?_some hfo0
  obtain ⟨kd, hkd, hkk, hkd'⟩ := fobjOf?_some hfo
  have hkk' : kd = ka := by omega
  subst hkk'
  have hr0 : r0 ≠ zeroReg := by have := (objV?_some hka').1; unfold zeroReg; omega
  obtain ⟨x, hx, hxv, hxf⟩ := arg_relV hl hm hinv hah0 hft0 hca0
    (kread_arg hR hnp ha0 hah0 hca0 hr0) hka'
  obtain ⟨y, hy, rfl⟩ := stepLoc_copy hl htemp hop (arr1 hsz1 ha0) hs
  rw [hx] at hy
  cases hy
  rw [write_reg hvh hcv]
  have hz := fvalRel_retypeL hxv hxf hft hcv
  have hzf := fits_retypeL hcv x
  have hlm := locMatch_setRegV hm hkd' hz (b' := b) (i' := i + 1)
  have hpc : E.pcOf b (i + 1) = m.pc := by rw [hj', hvs, ← hj, hm.pc]
  rw [hpc, wV_self_pc] at hlm
  exact ⟨m, .refl, hlm, (core_setReg hinv hzf).mono (knext_set hK hnp hvh hcv), hsi, rfl⟩

/-- `FMOVSgpfp`/`FMOVDgpfp`: `FMOVS`/`FMOVD Rn, Fd`. -/
theorem g44_gpfp (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca c : Nat} {rn rd : Int} (hop : v.op = .ARM64FMOVSgpfp ∨ v.op = .ARM64FMOVDgpfp)
    (hsz1 : v.args.size = 1) (hao : argObj lc v 0 = .ok (ca, rn))
    (hro : fresObj lc v = .ok (c, rd)) (hc : c = 8 * fBytes v.op) (hca : c ≤ ca)
    (hvs : OneAt2 psA j (.ofShape { as := fmovAs c, from_ := regA rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧ m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pureF hl htemp
    (by rcases hop with h | h <;> simp [h]) hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  subst hc
  have hn := fBytes_cases v.op
  obtain ⟨hty, -⟩ := fTy_eq hft hcv
  have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x] =
      Arm64.fmov (fW (fBytes v.op)) (lc.ty v.id) [x] := by
    rcases hop with h | h <;> rw [h] <;> rfl
  rw [he, hty]
  have hz := fvalRel_gpfp hA hxv hxf hn hca
  have hzf := fits_retypeL (hty ▸ hcv) (Arm64.fmov (fW (fBytes v.op)) (.int (fW (fBytes v.op))) [x])
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hz hzf
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
  rw [progStep_fmovXV hkn hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact fmovAs_movMem hn)
    hf ht]
  rfl

/-- `FMOVSfpgp`/`FMOVDfpgp`: `FMOVS`/`FMOVD Fn, Rd`. -/
theorem g44_fpgp (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca c : Nat} {rn rd : Int} (hop : v.op = .ARM64FMOVSfpgp ∨ v.op = .ARM64FMOVDfpgp)
    (hsz1 : v.args.size = 1) (hao : fargObj lc v 0 = .ok (ca, rn))
    (hro : resObj lc v = .ok (c, rd)) (hca : ca = 8 * fBytes v.op) (hc : c = 8 * fBytes v.op)
    (hvs : OneAt2 psA j (.ofShape { as := fmovAs c, from_ := regA rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧ XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> nofun
  obtain ⟨a0, r0, ha0, hah0, hfo0, hft0, hca0⟩ := fargObj_spec hao
  obtain ⟨ka, hka, rfl, hka'⟩ := fobjOf?_some hfo0
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  have hr0 : r0 ≠ zeroReg := by have := (objV?_some hka').1; unfold zeroReg; omega
  obtain ⟨x, hx, hxv, hxf⟩ := arg_relV hl hm hinv hah0 hft0 hca0
    (kread_arg hR hnp ha0 hah0 hca0 hr0) hka'
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pureF hl htemp
    (by rcases hop with h | h <;> simp [h]) hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  subst hc hca
  have hn := fBytes_cases v.op
  have ht := cls_ne_bool hcv (by omega)
  have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [x] =
      Arm64.fmov (fW (fBytes v.op)) (lc.ty v.id) [x] := by
    rcases hop with h | h <;> rw [h] <;> rfl
  rw [he]
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_fmovVX hn hxv hxf ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, -, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_fmovVX hka hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact fmovAs_movMem hn)
    hf ht', wX_pc]

/-- `FMOVSconst`/`FMOVDconst`: `FMOVS`/`FMOVD $c, Fd`. -/
theorem g44_fconst (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : Nat} {rd : Int} (hop : v.op = .ARM64FMOVSconst ∨ v.op = .ARM64FMOVDconst)
    (hsz0 : v.args.size = 0) (hro : fresObj lc v = .ok (c, rd)) (hc : c = 8 * fBytes v.op)
    (hvs : OneAt2 psA j (.ofShape { as := fmovAs c, from_ := fconstA v, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧ m'.x = m.x := by
  have hl := F.lowered
  have hnp : v.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> nofun
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pureF hl htemp
    (by rcases hop with h | h <;> simp [h]) hs
  have hnil : v.args.toList = [] := by rw [Array.size_eq_zero_iff.mp hsz0]
  rw [hnil] at hargv
  cases hargv
  simp only [List.reverse_nil]
  rw [write_reg hvh hcv]
  subst hc
  have hn := fBytes_cases v.op
  obtain ⟨hty, -⟩ := fTy_eq hft hcv
  have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [] =
      if fBytes v.op = 4 then FOps.const32 v.auxInt else FOps.const64 v.auxInt := by
    rcases hop with h | h <;> rw [h] <;> rfl
  rw [he, hty]
  have hz := fvalRel_fconst hn v.auxInt
  have hzf := fits_retypeL (hty ▸ hcv)
    (if fBytes v.op = 4 then FOps.const32 v.auxInt else FOps.const64 v.auxInt)
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hz hzf
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
  rw [progStep_fconst hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact fmovAs_movMem hn)
    hf ht]
  rfl

/-- A float load of `n` bytes, through a 64-bit register (`off(Rn)`) or of a global
(`sym+off(SB)`): G3's load into a V register. -/
theorem g44_fload (F : Facts lc sym text az ez psA.toList ret E)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : FLoadPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : Nat} {rd : Int} {src : Addr → Bool}
    (hop : v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload) (hsz2 : v.args.size = 2)
    (hacc : accessA lc g v = .ok src) (hma : memArg lc v 1 = .ok ())
    (hro : fresObj lc v = .ok (c, rd)) (hc : c = 8 * fBytes v.op)
    (hvs : OneAt2 psA j ⟨plain (fmovAs c) src (· == regA rd), (fmovAs c).name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧ m'.x = m.x := by
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
  rw [write_reg hvh hcv, hsym]
  simp only [Option.elim]
  subst hc
  have hn := fBytes_cases v.op
  have hn' : fBytes v.op = 1 ∨ fBytes v.op = 2 ∨ fBytes v.op = 4 ∨ fBytes v.op = 8 := by omega
  obtain ⟨hty, -⟩ := fTy_eq hft hcv
  have ht : lc.ty v.id ≠ .bool := by rw [hty]; nofun
  have hmov := fmovAs_movMem hn
  -- the loaded value at the access's address
  have hval : ∀ a, E.ι p.blk = some a →
      FValRel ((Arm64.loadN (lc.ty v.id) (fBytes v.op) false mm p).retypeL (lc.ty v.id))
        ((readMem m.mem (a + p.off) (fBytes v.op)).setWidth 128) := by
    intro a ha
    have hv := valRel_retypeL_lo hA hcv ht
      ((lo_loadN hA hMI hn' (fun _ => rfl) ht ha hrd).mono (cls_le hcv))
    refine fvalRel_of_valRel hA hv hnpp (fun b' => by rw [hty]; exact retypeL_int_ne_bool _ b') ?_
    exact BitVec.setWidth_setWidth_of_le _ (by omega)
  have hzf := fits_retypeL hcv (Arm64.loadN (lc.ty v.id) (fBytes v.op) false mm p)
  obtain ⟨P, hP, hPs⟩ := accessA_spec hacc
  have hpat : ∀ q : Prog,
      (⟨plain (fmovAs (8 * fBytes v.op)) src (· == regA (REG_F0 + kd)),
        (fmovAs (8 * fBytes v.op)).name⟩ : Pat).ok q = true →
      q.as = fmovAs (8 * fBytes v.op) ∧ P q.from_ ∧ q.to = regA (REG_F0 + kd) := by
    intro q hq
    obtain ⟨h1, h2, -, h4, -⟩ := plain_spec hq
    exact ⟨h1, hPs _ h2, beq_iff_eq.mp h4⟩
  cases hP with
  | reg haux hao =>
    obtain ⟨a0', r0, ha0', hah0, hor0, hca0⟩ := argObj_spec hao
    rw [ha0] at ha0'
    cases ha0'
    obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
    obtain ⟨X, hX, hxv, hxf⟩ :=
      arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
    rw [hx] at hX
    cases hX
    have haddr : Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p := by
      rw [← hsym]; unfold symAddr; rw [haux]
    obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < fBytes v.op)
      (Or.inr (by rw [hrd]; rfl))
    refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' (hval a hpa) hzf
      (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
      fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
    obtain ⟨has, hf, ht'⟩ := hpat _ hok
    have hsc : psA.toList[k0].scond = 0 := (plain_spec hok).2.2.2.2.1
    have haeq' : ({ m with pc := pcAt text psA.toList k0 } : MState).rX (BitVec.ofNat 5 kn) +
        BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
    have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
        { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].from_ =
        .ok (a + p.off, none) := by
      rw [hf, ctx_mem_reg hkn hsc, haeq']
    rw [progStep_floadAt hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov)
      (by rw [hf]; rfl) hma' ht' hnil]
    rfl
  | glob hx' ha0' hsb hsy =>
    rename_i xa a0'' name abi
    rw [ha0] at ha0'
    cases ha0'
    have hp := symAddr_global (ctx := lc.ctx) (a := x) hsy hx'
    rw [hsym] at hp
    cases hp
    obtain ⟨k0, -, hk0, hok0, -⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
    obtain ⟨-, ⟨-, -, -, -, -, y, -, hy⟩, -⟩ := hpat _ hok0
    have hpa := hglob y name abi hy
    obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < fBytes v.op)
      (Or.inr (by rw [hrd]; rfl))
    refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' (hval _ hpa) hzf
      (knext_set hK hnp hvh hcv) (fun k1 hk1 hok => ?_)).imp
      fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
    obtain ⟨has, ⟨hf1, hf2, -, -, hf5, y', hy1, hy'⟩, ht'⟩ := hpat _ hok
    have hyy : sym y' = sym y :=
      Option.some.inj ((hglob y' name abi hy').symm.trans hpa)
    have hL : (Link.byId sym text az ez psA.toList).sym y' = sym y := hyy
    have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
        { m with pc := pcAt text psA.toList k1 } psA.toList[k1]).mem psA.toList[k1].from_ =
        .ok (sym y + BitVec.ofInt 64 v.auxInt.toInt, none) := by
      rw [ctx_mem_glob hf1 hf2 hf5 hy1]
      exact congrArg (fun z => Except.ok (z + BitVec.ofInt 64 v.auxInt.toInt, none)) hL
    rw [progStep_floadAt hkd (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf1 hma' ht'
      hnil]
    rfl

/-- A float store of `n` bytes, through a 64-bit register (`off(Rn)`) or to a global
(`sym+off(SB)`): G3's store of a V register's low bytes. -/
theorem g44_fstore (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {cs : Nat} {rs : Int} {dst : Addr → Bool}
    (hop : v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore) (hsz3 : v.args.size = 3)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none) (hacc : accessA lc g v = .ok dst)
    (hso : fargObj lc v 1 = .ok (cs, rs)) (hma : memArg lc v 2 = .ok ())
    (hc : cs = 8 * fBytes v.op)
    (hvs : OneAt2 psA j ⟨plain (fmovAs cs) (· == regA rs) dst, (fmovAs cs).name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> nofun
  obtain ⟨a1, r1, ha1, hah1, hfo1, hft1, hca1⟩ := fargObj_spec hso
  obtain ⟨ks, hks, rfl, hks'⟩ := fobjOf?_some hfo1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  have hr1 : r1 ≠ zeroReg := by have := (objV?_some hks').1; unfold zeroReg; omega
  obtain ⟨y, hy, hyv, hyf⟩ := arg_relV hl hm hinv hah1 hft1 hca1
    (kread_arg hR hnp ha1 hah1 hca1 hr1) hks'
  obtain ⟨x, y', p, mm', hx, hy', hsym, hw, rfl⟩ := stepLoc_fstore hl htemp hop
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hy] at hy'
  cases hy'
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  subst hc
  have hn := fBytes_cases v.op
  have hn' : fBytes v.op = 1 ∨ fBytes v.op = 2 ∨ fBytes v.op = 4 ∨ fBytes v.op = 8 := by omega
  have hmov := fmovAs_movMem hn
  have hyv' : ValRel E.ι y ((m.v (BitVec.ofNat 5 ks)).setWidth 64) := valRel_of_fvalRel hyv
  have hcs : 8 * fBytes v.op ≤ 8 * fBytes v.op ∨ 8 * fBytes v.op = 1 := .inl (Nat.le_refl _)
  have hbs := (storeBytes_relN hA hn' hyv' hyf hcs).1
  have hcan : mm.canWrite p (fBytes v.op) = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have hword : ∀ k : Nat, k < 32 →
      ((m.v (BitVec.ofNat 5 k)).setWidth 64).toNat % 2 ^ (8 * fBytes v.op) =
        (m.v (BitVec.ofNat 5 k)).toNat % 2 ^ (8 * fBytes v.op) := by
    intro k _
    rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  obtain ⟨P, hP, hPs⟩ := accessA_spec hacc
  have hpat : ∀ q : Prog,
      (⟨plain (fmovAs (8 * fBytes v.op)) (· == regA (REG_F0 + ks)) dst,
        (fmovAs (8 * fBytes v.op)).name⟩ : Pat).ok q = true →
      q.as = fmovAs (8 * fBytes v.op) ∧ q.from_ = regA (REG_F0 + ks) ∧ P q.to ∧ q.scond = 0 := by
    intro q hq
    obtain ⟨h1, h2, -, h4, h5, -⟩ := plain_spec hq
    exact ⟨h1, beq_iff_eq.mp h2, hPs _ h4, h5⟩
  -- the store at the injected address of its block
  suffices hfin : ∀ a, E.ι p.blk = some a →
      (∀ k (hk : k < psA.toList.length),
        (⟨plain (fmovAs (8 * fBytes v.op)) (· == regA (REG_F0 + ks)) dst,
          (fmovAs (8 * fBytes v.op)).name⟩ : Pat).ok psA.toList[k] = true →
        progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
            { m with pc := pcAt text psA.toList k } =
          .ok { m with
            mem := writeMem m.mem (a + p.off) (fBytes v.op)
              (BitVec.ofNat (8 * fBytes v.op)
                (((m.v (BitVec.ofNat 5 ks)).setWidth 64).toNat % 2 ^ (8 * fBytes v.op))),
            pc := pcAt text psA.toList (k + 1) }) →
      ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
        LocMatch E { s with mem := .mem mm' } b (i + 1) m' ∧
        CoreInv E.ι (StkAt E) K' { s with mem := .mem mm' } ∧ SlotInv lc { s with mem := .mem mm' } by
    cases hP with
    | reg haux hao =>
      obtain ⟨a0', r0, ha0', hah0, hor0, hca0⟩ := argObj_spec hao
      rw [ha0] at ha0'
      cases ha0'
      obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
      obtain ⟨X, hX, hxv, hxf⟩ :=
        arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
      rw [hx] at hX
      cases hX
      have haddr : Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p := by
        rw [← hsym]; unfold symAddr; rw [haux]
      obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < fBytes v.op)
        (Or.inl hcan)
      refine hfin a hpa fun k0 hk0 hok => ?_
      obtain ⟨has, hf, ht', hsc⟩ := hpat _ hok
      have haeq' : ({ m with pc := pcAt text psA.toList k0 } : MState).rX (BitVec.ofNat 5 kn) +
          BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
      have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].to =
          .ok (a + p.off, none) := by
        rw [ht', ctx_mem_reg hkn hsc, haeq']
      rw [progStep_fstoreAt hks (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov) hf
        (by rw [ht']; rfl) hma' hnil, hword ks hks]
    | glob hx' ha0' hsb hsy =>
      rename_i xa a0'' name abi
      rw [ha0] at ha0'
      cases ha0'
      have hp := symAddr_global (ctx := lc.ctx) (a := x) hsy hx'
      rw [hsym] at hp
      cases hp
      obtain ⟨k0, -, hk0, hok0, -⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
      obtain ⟨-, -, ⟨-, -, -, -, -, y0, -, hy0⟩, -⟩ := hpat _ hok0
      have hpa := hglob y0 name abi hy0
      obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < fBytes v.op) (Or.inl hcan)
      refine hfin _ hpa fun k1 hk1 hok => ?_
      obtain ⟨has, hf, ⟨ht1, ht2, -, -, ht5, y', hy1, hy'⟩, -⟩ := hpat _ hok
      have hyy : sym y' = sym y0 := Option.some.inj ((hglob y' name abi hy').symm.trans hpa)
      have hL : (Link.byId sym text az ez psA.toList).sym y' = sym y0 := hyy
      have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m with pc := pcAt text psA.toList k1 } psA.toList[k1]).mem psA.toList[k1].to =
          .ok (sym y0 + BitVec.ofInt 64 v.auxInt.toInt, none) := by
        rw [ctx_mem_glob ht1 ht2 ht5 hy1]
        exact congrArg (fun z => Except.ok (z + BitVec.ofInt 64 v.auxInt.toInt, none)) hL
      rw [progStep_fstoreAt hks (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf ht1 hma'
        hnil, hword ks hks]
  intro a hpa hstep
  obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ :=
    memInj_storeN hA hMI hk0 hn' hpa hyv' hyf hcs hw
  have hsep' : SepFrom E.ι (StkAt E) mm' := by
    intro b2 al2 a2 hb hι y hy
    obtain ⟨al1, hb1, hs1⟩ := hback b2 al2 hb
    rw [← hs1]; exact hsep0 b2 al1 a2 hb1 hι y hy
  exact (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM' hk'
    hsep' (fun y hy => hout y fun j hj he => hsep0 _ _ _ hal hpa y hy ⟨by omega, by omega⟩)
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) hstep).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2, hsi⟩

end Cases

/-! ## One value -/

/-- A float `Copy` writes only its register: G35's table drops the entry of its home. -/
theorem uStep35_fcopy {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : v.op = .Copy) : uStep35 lc L v = L.filter fun e => regHome? lc v.id != some e.1 := by
  rw [uStep35_other (ldEntry35_none (by rw [hop]; rfl)) (by simp [pairOp35, hop]),
    uStep34_keep (by simp [keep34, keep31, keepOp31, hop])]

/-- G44's ops other than `Copy`. -/
def FOp44 (op : Op) : Prop :=
  op = .ARM64FMOVSload ∨ op = .ARM64FMOVDload ∨ op = .ARM64FMOVSstore ∨ op = .ARM64FMOVDstore ∨
    op = .ARM64FMOVSgpfp ∨ op = .ARM64FMOVDgpfp ∨ op = .ARM64FMOVSfpgp ∨ op = .ARM64FMOVDfpgp ∨
    op = .ARM64FMOVSconst ∨ op = .ARM64FMOVDconst

/-- G35's table is empty after G44's values other than `Copy`. -/
theorem uStep35_f44 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} (hop : FOp44 v.op) :
    uStep35 lc L v = [] := by
  rcases hop with h | h | h | h | h | h | h | h | h | h <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

/-- One value of G44's kinds: `vk42_step`'s statement, under `G44Pre`. -/
theorem vk44_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK44 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G44Pre lc s v)
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
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨hlcE, -, -, -, -, hglob, -, -, -, -, hF⟩, -⟩, -⟩, -⟩, -⟩ := hE
  have hR := kread_of_reads hreads
  have hempty : ∀ m', UOKL m' [] := fun _ e he => by cases he
  cases hVK with
  | g42 hVK42 =>
    exact vk42_step hE0 F hhome hcf hv hVK42 hvs htemp hj hj' hreads hm hinv hL hmem hpre.1 hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | fcopyNone hop hsz ha hr =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hr
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g44_fcopyNone (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz ha hr hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_fcopy hop]
    exact uokl_keep hL (.inl h5)
  | fcopy hop hsz ha hr =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hr
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g44_fcopy (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz ha hr hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_fcopy hop]
    exact uokl_keep hL (.inl h5)
  | fload hop hsz hacc hma hr hc =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hr
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g44_fload (H := H) F (fun y name abi h => hglob y name abi h)
      hm hinv.core hinv.slots hR (knext_kStep fun _ => (hs_reg hvh).noRegs) hpre.2 hj hj' hop hsz
      hacc hma hr hc hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_f44 (by rcases hop with h | h <;> simp [FOp44, h])]
    exact hempty m'
  | fstore hop hsz hmt hhn hacc hso hma hc =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g44_fstore (H := H) F hF (slot_sizes hlcE hcf hinv.slots)
      (fun y name abi h => hglob y name abi h) hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz hmt hhn hacc hso hma hc hvs
      htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_f44 (by rcases hop with h | h <;> simp [FOp44, h])]
    exact hempty m'
  | gpfp hop hsz hao hr hc hca =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hr
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g44_gpfp (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hr hc hca hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_f44 (by rcases hop with h | h <;> simp [FOp44, h])]
    exact hempty m'
  | fpgp hop hsz hao hro hca hc =>
    obtain ⟨r, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g44_fpgp (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro hca hc hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_f44 (by rcases hop with h | h <;> simp [FOp44, h])]
    exact hempty m'
  | fconst hop hsz hro hc =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g44_fconst (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hro hc hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_f44 (by rcases hop with h | h <;> simp [FOp44, h])]
    exact hempty m'

/-- A nil check of G44's kinds is G7's. -/
theorem vk44_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK44 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g42 h => exact vk42_nil h hop
  | fcopyNone h => rw [hop] at h; cases h
  | fcopy h => rw [hop] at h; cases h
  | fload h => rcases h with h | h <;> rw [hop] at h <;> cases h
  | fstore h => rcases h with h | h <;> rw [hop] at h <;> cases h
  | gpfp h => rcases h with h | h <;> rw [hop] at h <;> cases h
  | fpgp h => rcases h with h | h <;> rw [hop] at h <;> cases h
  | fconst h => rcases h with h | h <;> rw [hop] at h <;> cases h

/-- A bounds check of G44's kinds is G28's. -/
theorem vk44_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK44 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  cases h with
  | g42 h => exact vk42_pb h hop
  | fcopyNone h => rw [h] at hop; cases hop
  | fcopy h => rw [h] at hop; cases hop
  | fload h => rcases h with h | h <;> rw [h] at hop <;> cases hop
  | fstore h => rcases h with h | h <;> rw [h] at hop <;> cases hop
  | gpfp h => rcases h with h | h <;> rw [h] at hop <;> cases hop
  | fpgp h => rcases h with h | h <;> rw [h] at hop <;> cases hop
  | fconst h => rcases h with h | h <;> rw [h] at hop <;> cases hop

/-! ## The theorems on G44's check -/

/-- G43's values and G44's float moves under G44's check, under `G44Pre`. -/
theorem g44L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG44L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G44Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_44L hl hc) hE hbid hb hi hv
      hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre.1.1.1 hcall hcallz hicall hwb
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
    checkG44L_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind44_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk44_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- `InitMem` under G44's check: `g43L_initMem`'s statement. -/
theorem g44L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG44L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -⟩ := checkG44L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind44_initMem hop] at hkd
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

/-- G38's nil panics under G44's check. -/
theorem g44L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG44L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_44L hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG44L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind44_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk44_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G44's check. -/
theorem g44L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG44L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_44L hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG44L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind44_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk44_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G44's check. -/
theorem g44L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG44L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_44L hl hc) hE hbid hb hm hinv hpre
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
    checkG44L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG44 lc`, on `liveCtx lc` -/

/-- **G44, values.** `g43_value`'s statement over `checkG44`, under `G44Pre` (G41's premise and
`FLoadPre`: a float load reads valid bytes that are no pointer without an integer form). -/
theorem g44_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG44 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G44Pre (liveCtx lc) s v)
    (hcall : CallOK H E g L (liveCtx lc) s s' v m) (hcallz : CallOKZ H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOK H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOK H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L (liveCtx lc) s v m) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g44L_value (checkG44_spec hc).2 hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz hicall hwb hclo
    hgetg hmeq hs

/-- **G44, `InitMem`.** `g43_initMem`'s statement over `checkG44`. -/
theorem g44_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG44 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g44L_initMem (checkG44_spec hc).2 hE hl hbid hb hi hv hop hm hinv hpre hs

/-- **G44, nil panics.** `g43_nilPanic`'s statement over `checkG44`. -/
theorem g44_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG44 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g44L_nilPanic (checkG44_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G44, bounds panics.** `g43_boundsPanic`'s statement over `checkG44`. -/
theorem g44_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG44 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g44L_boundsPanic (checkG44_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G44, terminators.** `g43_term`'s statement over `checkG44`. -/
theorem g44_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG44 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s)
    (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g44L_term (checkG44_spec hc).2 hE hbid hb hm hinv hpre hu ht

end GoFV.Proof.Gen
