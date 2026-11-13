import GoFV.Proof.Gen.G44
import GoFV.Proof.Gen.Spec45

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G45 of the genssa validator: register-index float loads and stores
(`docs/plans/proofs3.md` §4)

`checkG45 lc` (`GoFV/Gen/Check45.lean`) is G44 with the float register-index loads
`FMOV{S,D}loadidx{,4,8} ptr idx mem` and stores `FMOV{S,D}storeidx{,4,8} ptr idx val mem`. Phase 1
runs them as the integer ones (`Arm64.loadIdx`, `stIdx`, `stepLoc_fLoadIdx`,
`stepLoc_fStoreIdx`): the `n` bytes at the address of `idxSum (2^sh)`. Genssa emits one
`FMOVS`/`FMOVD` from or to `(Rp)(Ri<<sh)` (`idxA`), whose address is `X[p] + (X[i] <<< sh)`
(`ctx_mem_idx`); the address is G14's (`lo_idxSum`, `addr_rel`) and the value G44's:

* a load is G3's `n`-byte load (`lo_loadN`) related to the V register by `fvalRel_of_valRel`, which
  needs the loaded value at its shape to be no pointer; with G14's premise that the bytes are
  valid, that is the run premise `FIdxPre`;
* a store writes the low `8n` bits of the value's V register (`arg_relV`, `valRel_of_fvalRel`,
  `memInj_storeN`), as G44's float store; it needs no premise.

Neither writes an X register, so G35's upper-bit table is empty after them (`uStep35_f45`).
`g45_value` takes `G45Pre := G44Pre ∧ FIdxPre`; `g45_initMem`, `g45_term`, `g45_nilPanic`,
`g45_boundsPanic` are G44's statements over `checkG45`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The opcodes -/

theorem fLoadIdxOp?_op {op : Op} {n sh : Nat} (h : fLoadIdxOp? op = some (n, sh)) :
    (op = .ARM64FMOVSloadidx ∧ n = 4 ∧ sh = 0) ∨ (op = .ARM64FMOVDloadidx ∧ n = 8 ∧ sh = 0) ∨
    (op = .ARM64FMOVSloadidx4 ∧ n = 4 ∧ sh = 2) ∨ (op = .ARM64FMOVDloadidx8 ∧ n = 8 ∧ sh = 3) := by
  unfold fLoadIdxOp? at h
  split at h <;> first | (cases h; simp) | cases h

theorem fStoreIdxOp?_op {op : Op} {n sh : Nat} (h : fStoreIdxOp? op = some (n, sh)) :
    (op = .ARM64FMOVSstoreidx ∧ n = 4 ∧ sh = 0) ∨ (op = .ARM64FMOVDstoreidx ∧ n = 8 ∧ sh = 0) ∨
    (op = .ARM64FMOVSstoreidx4 ∧ n = 4 ∧ sh = 2) ∨ (op = .ARM64FMOVDstoreidx8 ∧ n = 8 ∧ sh = 3) := by
  unfold fStoreIdxOp? at h
  split at h <;> first | (cases h; simp) | cases h

/-- A float register-index load is no `Phi`, of 4 or 8 bytes, with a shift below 4. -/
theorem fLoadIdxOp?_facts {op : Op} {n sh : Nat} (h : fLoadIdxOp? op = some (n, sh)) :
    op ≠ .Phi ∧ (n = 4 ∨ n = 8) ∧ sh < 4 := by
  rcases fLoadIdxOp?_op h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ <;> exact ⟨nofun, by decide, by decide⟩

/-- A float register-index store is no `Phi`, of 4 or 8 bytes, with a shift below 4. -/
theorem fStoreIdxOp?_facts {op : Op} {n sh : Nat} (h : fStoreIdxOp? op = some (n, sh)) :
    op ≠ .Phi ∧ (n = 4 ∨ n = 8) ∧ sh < 4 := by
  rcases fStoreIdxOp?_op h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ <;> exact ⟨nofun, by decide, by decide⟩

/-! ## The premise -/

/-- A float register-index load reads `n` valid bytes at its address (`idxSum`, as `IdxPre`), and
what it reads at its shape is no pointer without an integer form (a pointer has no V register
form, as `FLoadPre`). -/
def FIdxPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  ∀ n sh, fLoadIdxOp? v.op = some (n, sh) → ∀ a0 a1 x y, v.args[0]? = some a0 →
    v.args[1]? = some a1 → s.read lc a0 = .ok x → s.read lc a1 = .ok y →
    ∃ p mm bs, Arm64.addr (idxSum (2 ^ sh) x y) 0 = some p ∧ s.mem = .mem mm ∧
      mm.read p n = some bs ∧
      ∀ q, (Arm64.loadN (lc.ty v.id) n false mm p).retypeL (lc.ty v.id) ≠ .ptr q

/-- The per-value premises of G45: G44's (`G44Pre`), and `FIdxPre`. -/
def G45Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop := G44Pre lc s v ∧ FIdxPre lc s v

/-! ## `stepLoc` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_four' {a b c d : ID} :
    [a, b, c, d].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        (s.read lc d).bind fun w => .ok [x, y, z, w] := rfl

/-- A float register-index load: `Arm64.loadIdx` of the arguments read from their homes, at scale
`2^sh`. -/
theorem stepLoc_fLoadIdx (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {n sh : Nat} (hop : fLoadIdxOp? v.op = some (n, sh))
    {a0 a1 a2 : ID} (ha : v.args = #[a0, a1, a2]) {mm : Mem}
    (hm : s.read lc a2 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y, s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧
      s' = s.write lc v.id ((Arm64.loadIdx (lc.ty v.id) n (2 ^ sh) false [x, y, .mem mm]).retypeL
        (lc.ty v.id)) := by
  rcases fLoadIdxOp?_op hop with ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ |
    ⟨ho, rfl, rfl⟩ <;>
  · obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [ho]; nofun)
      (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
      (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) h
    rw [ha] at hmv
    change ((s.read lc a0).bind fun x => (s.read lc a1).bind fun y => (s.read lc a2).bind
      fun z => .ok [x, y, z]) = .ok argv at hmv
    have hev : ∀ argv, evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.loadIdx (lc.ty v.id) _ _ false argv) := fun _ => by
      unfold evalOpL; rw [ho]; rfl
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

/-- A store whose `arm64Op` is `stIdx n scale`: the `n`-byte store at `idxSum scale` (G18's
`storeIdx_core`). -/
private theorem fstoreIdx_core {n scale : Nat} (hl : lc.ctx.f.lowered = true)
    (ht : (lc.temps[v.id]?).join = none) (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg)
    (h2 : v.op ≠ .StoreReg) (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (hc : v.op.regInfo.clobbers.isEmpty = true) (hc0 : v.op.regInfo.clobbersArg0 = false)
    (hc1 : v.op.regInfo.clobbersArg1 = false) (hf : v.op.clobberFlags = false)
    (hev : ∀ argv, evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      arm64Op true env lc.ctx s.fr v argv (lc.ty v.id))
    (hst : ∀ x y z mm, nilFaults true lc.ctx v [x, y, z, .mem mm] = none → ∃ w m1 m2,
      arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
        match Arm64.addr (idxSum scale x y) 0 with
        | some p => writeRes w (Arm64.storeN n p z mm)
        | none =>
          if [x, y, z, Val.mem mm].any (fun | .poison => true | _ => false) then .stuck m1
          else .stuck m2)
    {a0 a1 a2 a3 : ID} (ha : v.args = #[a0, a1, a2, a3]) {mm : Mem}
    (hm : s.read lc a3 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y z p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ s.read lc a2 = .ok z ∧
      Arm64.addr (idxSum scale x y) 0 = some p ∧ mm.write p (Arm64.storeBytes n z) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht hne h1 h2 h3 h4 hc hc0 hc1 hf h
  rw [ha] at hmap
  change [a0, a1, a2, a3].mapM (s.read lc) = _ at hmap
  rw [mapM_four'] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
  cases hy : s.read lc a1 with
  | panic e m => rw [hx, hy] at hmap; cases hmap
  | stuck msg => rw [hx, hy] at hmap; cases hmap
  | ok y =>
  cases hz : s.read lc a2 with
  | panic e m => rw [hx, hy, hz] at hmap; cases hmap
  | stuck msg => rw [hx, hy, hz] at hmap; cases hmap
  | ok z =>
    rw [hx, hy, hz, hm] at hmap; cases hmap
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, y, z, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      obtain ⟨w, m1, m2, he⟩ := hst x y z mm hn
      cases hp : Arm64.addr (idxSum scale x y) 0 with
      | none =>
        rw [hp] at he; rw [he] at hr
        dsimp only at hr
        split at hr <;> cases hr
      | some p =>
        rw [hp] at he; rw [he] at hr
        change writeRes _ (mm.write p (Arm64.storeBytes n z)) = _ at hr
        cases hw : mm.write p (Arm64.storeBytes n z) with
        | none => rw [hw] at hr; cases hr
        | some mm' =>
          rw [hw] at hr; cases hr
          exact ⟨x, y, z, p, mm', rfl, rfl, rfl, hp, hw, rfl⟩

/-- A float register-index store: the `n`-byte store of `val` at the address of `idxSum (2^sh)`,
which succeeded. -/
theorem stepLoc_fStoreIdx (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {n sh : Nat} (hop : fStoreIdxOp? v.op = some (n, sh))
    {a0 a1 a2 a3 : ID} (ha : v.args = #[a0, a1, a2, a3]) {mm : Mem}
    (hm : s.read lc a3 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y z p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ s.read lc a2 = .ok z ∧
      Arm64.addr (idxSum (2 ^ sh) x y) 0 = some p ∧ mm.write p (Arm64.storeBytes n z) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  rcases fStoreIdxOp?_op hop with ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ |
    ⟨ho, rfl, rfl⟩ <;>
  exact fstoreIdx_core hl ht (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
    (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl)
    (by rw [ho]; rfl) (fun _ => by unfold evalOpL; rw [ho]; rfl)
    (fun _ _ _ _ hn => ⟨_, _, _, by unfold arm64Op; rw [hn, ho]; rfl⟩) ha hm h

end Step

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- A float register-index load `FMOVS`/`FMOVD (Rp)(Ri<<sh), Fd` of `n` valid bytes: G14's address,
G44's load into a V register. -/
theorem g45_fldIdx (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : FIdxPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n sh c : Nat} {rn ri rd : Int}
    (hop : fLoadIdxOp? v.op = some (n, sh)) (hsz3 : v.args.size = 3)
    (hao : argObj lc v 0 = .ok (64, rn)) (hio : argObj lc v 1 = .ok (64, ri))
    (hma : memArg lc v 2 = .ok ()) (hro : fresObj lc v = .ok (c, rd)) (hc : c = 8 * n)
    (hvs : OneAt2 psA j ⟨plain (fmovAs c) (· == idxA rn ri sh) (· == regA rd), (fmovAs c).name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, hn, hsh⟩ := fLoadIdxOp?_facts hop
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hio
  obtain ⟨ki, hki, rfl, hkki⟩ := objOf?_some hor1
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨x, y, hx, hy, rfl⟩ := stepLoc_fLoadIdx hl htemp hop (arr3 hsz3 ha0 ha1 ha2)
    (read_mem hl hah2 hamt hmm) hs
  obtain ⟨p, mm2, bs, hpa, hmm2, hrd, hnpp⟩ := hpre _ _ hop a0 a1 x y ha0 ha1 hx hy
  rw [hmm] at hmm2
  cases hmm2
  rw [write_reg hvh hcv, loadIdx_eq, hpa]
  simp only [Option.elim]
  subst hc
  have hn' : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by omega
  obtain ⟨hty, -⟩ := fTy_eq hft hcv
  have ht : lc.ty v.id ≠ .bool := by rw [hty]; nofun
  have hmov := fmovAs_movMem hn
  -- the loaded value at the access's address
  have hval : ∀ a, E.ι p.blk = some a →
      FValRel ((Arm64.loadN (lc.ty v.id) n false mm p).retypeL (lc.ty v.id))
        ((readMem m.mem (a + p.off) n).setWidth 128) := by
    intro a ha
    have hv := valRel_retypeL_lo hA hcv ht
      ((lo_loadN hA hMI hn' (fun _ => rfl) ht ha hrd).mono (cls_le hcv))
    refine fvalRel_of_valRel hA hv hnpp (fun b' => by rw [hty]; exact retypeL_int_ne_bool _ b') ?_
    exact BitVec.setWidth_setWidth_of_le _ (by omega)
  have hzf := fits_retypeL hcv (Arm64.loadN (lc.ty v.id) n false mm p)
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  rw [hx] at hX
  cases hX
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkki
  rw [hy] at hY
  cases hY
  obtain ⟨hzv, hzf'⟩ := lo64_rel (lo_idxSum hA hxv hyv hxf hyf sh) hpa
  obtain ⟨a, hpa', haeq, hnil⟩ := addr_rel hA hMI hzv hzf' hpa (by omega : 0 < n)
    (Or.inr (by rw [hrd]; rfl))
  have haeq' : m.rX (BitVec.ofNat 5 kn) + m.rX (BitVec.ofNat 5 ki) <<< sh = a + p.off := by
    simpa using haeq
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' (hval a hpa') hzf
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  obtain ⟨has, hf, -, ht', -, -, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf ht'
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].from_ =
      .ok (a + p.off, none) := by
    rw [hf, ctx_mem_idx hkn hki (by omega)]
    exact congrArg (fun z => Except.ok (z, none)) haeq'
  rw [progStep_floadAt hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov)
    (by rw [hf]; rfl) hma' ht' hnil]
  rfl

/-- A float register-index store `FMOVS`/`FMOVD Fs, (Rp)(Ri<<sh)` of `n` bytes: G18's address,
G44's store of a V register's low bytes. -/
theorem g45_fstIdx (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n sh cs : Nat} {rn ri rs : Int}
    (hop : fStoreIdxOp? v.op = some (n, sh)) (hsz4 : v.args.size = 4)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hao : argObj lc v 0 = .ok (64, rn)) (hio : argObj lc v 1 = .ok (64, ri))
    (hso : fargObj lc v 2 = .ok (cs, rs)) (hc : cs = 8 * n) (hma : memArg lc v 3 = .ok ())
    (hvs : OneAt2 psA j ⟨plain (fmovAs cs) (· == regA rs) (· == idxA rn ri sh), (fmovAs cs).name⟩
      j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, hn, hsh⟩ := fStoreIdxOp?_facts hop
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hio
  obtain ⟨ki, hki, rfl, hkki⟩ := objOf?_some hor1
  obtain ⟨a2, r2, ha2, hah2, hfo2, hft2, hca2⟩ := fargObj_spec hso
  obtain ⟨ks, hks, rfl, hks'⟩ := fobjOf?_some hfo2
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  have hr2 : r2 ≠ zeroReg := by have := (objV?_some hks').1; unfold zeroReg; omega
  obtain ⟨z, hz, hzv, hzf⟩ := arg_relV hl hm hinv hah2 hft2 hca2
    (kread_arg hR hnp ha2 hah2 hca2 hr2) hks'
  obtain ⟨x, y, z', p, mm', hx, hy, hz', hpa, hw, rfl⟩ := stepLoc_fStoreIdx hl htemp hop
    (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hz] at hz'
  cases hz'
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  rw [hx] at hX
  cases hX
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkki
  rw [hy] at hY
  cases hY
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  subst hc
  have hn' : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by omega
  have hmov := fmovAs_movMem hn
  have hzv' : ValRel E.ι z ((m.v (BitVec.ofNat 5 ks)).setWidth 64) := valRel_of_fvalRel hzv
  have hcs : 8 * n ≤ 8 * n ∨ 8 * n = 1 := .inl (Nat.le_refl _)
  have hbs := (storeBytes_relN hA hn' hzv' hzf hcs).1
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨hsv, hsf⟩ := lo64_rel (lo_idxSum hA hxv hyv hxf hyf sh) hpa
  obtain ⟨a, hpa', haeq, hnil⟩ := addr_rel hA hMI hsv hsf hpa (by omega : 0 < n) (Or.inl hcan)
  have haeq' : m.rX (BitVec.ofNat 5 kn) + m.rX (BitVec.ofNat 5 ki) <<< sh = a + p.off := by
    simpa using haeq
  have hword : ((m.v (BitVec.ofNat 5 ks)).setWidth 64).toNat % 2 ^ (8 * n) =
      (m.v (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n) := by
    rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ :=
    memInj_storeN hA hMI hk0 hn' hpa' hzv' hzf hcs hw
  have hsep' : SepAt osp E.ι (StkAt E) mm' := hsep0.write hk0 hw
  have hwf := write_wf hw (by rw [hbs]; omega)
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM' hk' hsep'
    (fun y hy => hout y fun j hj he => hsep0.not_mem hal hpa' hy (by omega) (by omega))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k0 hk0 hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, -, ht', -, -, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf ht'
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].to =
      .ok (a + p.off, none) := by
    rw [ht', ctx_mem_idx hkn hki (by omega)]
    exact congrArg (fun z => Except.ok (z, none)) haeq'
  rw [progStep_fstoreAt hks (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov) hf
    (by rw [ht']; rfl) hma' hnil, hword]

end Cases

/-! ## One value -/

/-- G45's ops. -/
def FOp45 (op : Op) : Prop :=
  op = .ARM64FMOVSloadidx ∨ op = .ARM64FMOVDloadidx ∨ op = .ARM64FMOVSloadidx4 ∨
    op = .ARM64FMOVDloadidx8 ∨ op = .ARM64FMOVSstoreidx ∨ op = .ARM64FMOVDstoreidx ∨
    op = .ARM64FMOVSstoreidx4 ∨ op = .ARM64FMOVDstoreidx8

/-- G35's table is empty after G45's values. -/
theorem uStep35_f45 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} (hop : FOp45 v.op) :
    uStep35 lc L v = [] := by
  rcases hop with h | h | h | h | h | h | h | h <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

theorem fop45_load {op : Op} {n sh : Nat} (h : fLoadIdxOp? op = some (n, sh)) : FOp45 op := by
  rcases fLoadIdxOp?_op h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [FOp45, h]

theorem fop45_store {op : Op} {n sh : Nat} (h : fStoreIdxOp? op = some (n, sh)) : FOp45 op := by
  rcases fStoreIdxOp?_op h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [FOp45, h]

/-- One value of G45's kinds: `vk44_step`'s statement, under `G45Pre`. -/
theorem vk45_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK45 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G45Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hmp : MemEqPre lc s v) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩, -⟩, -⟩, -⟩, -⟩ := hE
  have hR := kread_of_reads hreads
  have hempty : ∀ m', UOKL m' [] := fun _ e he => by cases he
  cases hVK with
  | g44 hVK44 =>
    exact vk44_step hE0 F hhome hcf hv hVK44 hvs htemp hj hj' hreads hm hinv hL hmem hpre.1 hcall
      hcallz hicall hwb hclo hgetg hmeq hmp hs
  | fldIdx hop hsz hao hio hma hr hc =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hr
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g45_fldIdx (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hpre.2 hj hj' hop hsz hao hio hma hr hc hvs
      htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_f45 (fop45_load hop)]
    exact hempty m'
  | fstIdx hop hsz hmt hhn hao hio hso hc hma =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g45_fstIdx (H := H) F hF (slot_sizes hlcE hcf hinv.slots)
      hm hinv.core hinv.slots hR (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz hmt
      hhn hao hio hso hc hma hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_f45 (fop45_store hop)]
    exact hempty m'

/-- A nil check of G45's kinds is G7's. -/
theorem vk45_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK45 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g44 h => exact vk44_nil h hop
  | fldIdx h => rw [hop] at h; simp [fLoadIdxOp?] at h
  | fstIdx h => rw [hop] at h; simp [fStoreIdxOp?] at h

/-- A bounds check of G45's kinds is G28's. -/
theorem vk45_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK45 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  cases h with
  | g44 h => exact vk44_pb h hop
  | fldIdx h =>
    rcases fLoadIdxOp?_op h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hop <;> cases hop
  | fstIdx h =>
    rcases fStoreIdxOp?_op h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hop <;>
      cases hop

/-! ## The theorems on G45's check -/

/-- G44's values and G45's float register-index accesses under G45's check, under `G45Pre`. -/
theorem g45L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG45L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G45Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hmp : MemEqPre lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_45L hl hc) hE hbid hb hi hv
      hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre.1.1.1.1 hcall hcallz hicall
      hwb hclo hgetg hmeq hmp hs
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
    checkG45L_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind45_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk45_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hmp hs

/-- `InitMem` under G45's check: `g44L_initMem`'s statement. -/
theorem g45L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG45L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -⟩ := checkG45L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind45_initMem hop, vkind44_initMem hop] at hkd
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

/-- G38's nil panics under G45's check. -/
theorem g45L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG45L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_45L hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG45L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind45_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk45_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G45's check. -/
theorem g45L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG45L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_45L hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG45L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind45_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk45_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G45's check. -/
theorem g45L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG45L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_45L hl hc) hE hbid hb hm hinv hpre
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
    checkG45L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG45 lc`, on `liveCtx lc` -/

/-- **G45, values.** `g44_value`'s statement over `checkG45`, under `G45Pre` (G44's premise and
`FIdxPre`: a float register-index load reads valid bytes that are no pointer without an integer
form). -/
theorem g45_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG45 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G45Pre (liveCtx lc) s v)
    (hcall : CallOK H E g L (liveCtx lc) s s' v m) (hcallz : CallOKZ H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOK H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOK H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L (liveCtx lc) s v m) (hmp : MemEqPre (liveCtx lc) s v)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g45L_value (checkG45_spec hc).2 hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz hicall hwb hclo
    hgetg hmeq hmp hs

/-- **G45, `InitMem`.** `g44_initMem`'s statement over `checkG45`. -/
theorem g45_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG45 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g45L_initMem (checkG45_spec hc).2 hE hl hbid hb hi hv hop hm hinv hpre hs

/-- **G45, nil panics.** `g44_nilPanic`'s statement over `checkG45`. -/
theorem g45_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG45 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g45L_nilPanic (checkG45_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G45, bounds panics.** `g44_boundsPanic`'s statement over `checkG45`. -/
theorem g45_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG45 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g45L_boundsPanic (checkG45_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G45, terminators.** `g44_term`'s statement over `checkG45`. -/
theorem g45_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG45 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s)
    (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g45L_term (checkG45_spec hc).2 hE hbid hb hm hinv hpre hu ht

end GoFV.Proof.Gen
