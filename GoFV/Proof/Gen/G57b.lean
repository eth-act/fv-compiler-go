import GoFV.Proof.Gen.G49
import GoFV.Proof.Gen.Spec57b

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G57, group B: `DMB`, `PRFM`, float stores to frame variables (`docs/plans/proofs3.md` §4)

`vkind57b` (`GoFV/Gen/Check57b.lean`) accepts `DMB`, `PRFM` and the float stores `FMOVSstore`,
`FMOVDstore`, `FSTPS`, `FSTPD` of a frame variable; `VK57b` (`Spec57b.lean`) says what it accepted.

* `DMB [k] mem` and `PRFM [k] addr mem`: `runLoc` returns the memory unchanged (`arm64Op`, the
  address of `PRFM` ignored), so the state stays (`stepLoc_dmb57`, `stepLoc_prfm57`); the machine
  runs `DMB $k` and `PRFM 0(Rn), $k` with no effect (`progEffect`'s `DMB`/`PRFM` arm,
  `progStep_barrier57`), and the PC moves on (`g57_barrier`).
* The float stores to a frame variable: the variable's block (`VarAt57`), G49's `local` block
  (`symAddr_local`, `var49_addr`) or G6's `temp` block (`symAddr_var`, `var_addr`), is at
  `SP + frameOff` under the injection; `runLoc` writes the float's raw bits (`stepLoc_fstore`,
  `stPair` for the pairs, `stepLoc_fstp57`), the machine the low bytes of the V registers at the
  frame operand (`progStep_fstoreAt`, `progStep_fstp57`), related as G44's float stores
  (`g57_fstore`, `g57_fstp`, after `g49_store`/`g49_stp`). No run premise: a `poison` float
  stores `poison` bytes.

None of these ops is in an upper-bit keep or entry table: after each the table is empty
(`uStep35_57b`). `vk57b_step` is one value, in `vk55_step`'s form (under `G49Env`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The ops -/

/-- G57's group B. -/
def ops57b : List Op :=
  [.ARM64DMB, .ARM64PRFM, .ARM64FMOVSstore, .ARM64FMOVDstore, .ARM64FSTPD, .ARM64FSTPS]

theorem ops57b_of {op : Op} (h : op57b op = true) : op ∈ ops57b := by
  simp only [op57b, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((rfl | rfl) | rfl) | rfl) | h
  · simp [ops57b]
  · simp [ops57b]
  · simp [ops57b]
  · simp [ops57b]
  · cases hf : fstpOf op with
    | none => rw [hf] at h; cases h
    | some n =>
      rcases fstpOf_some hf with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [ops57b]

set_option hygiene false in
/-- The 6 rows of `ops57b` as hypotheses `h : op = …`. -/
local macro "ops57b_cases" : tactic => `(tactic| (
  simp only [ops57b, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h))

/-- G57's group B are arm64 ops that clobber nothing, no `Phi`, nil check, bounds check or entry
value. -/
theorem ops57b_facts {op : Op} (hmem : op ∈ ops57b) :
    op ≠ .Phi ∧ op ≠ .LoadReg ∧ op ≠ .StoreReg ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64MOVDnop ∧
      op.regInfo.clobbers.isEmpty = true ∧ op.regInfo.clobbersArg0 = false ∧
      op.regInfo.clobbersArg1 = false ∧ op.clobberFlags = false ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false ∧ entryOp24 op = false := by
  ops57b_cases <;> subst h <;>
    exact ⟨nofun, nofun, nofun, nofun, nofun, rfl, rfl, rfl, rfl, nofun, rfl, rfl⟩

/-- G35's table is empty after G57's group B. -/
theorem uStep35_57b {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hmem : v.op ∈ ops57b) : uStep35 lc L v = [] := by
  ops57b_cases <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

theorem fstpOf_mem {op : Op} {n : Nat} (h : fstpOf op = some n) : op ∈ ops57b := by
  rcases fstpOf_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [ops57b]

/-! ## `stepLoc` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem noclob57 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hmem : v.op ∈ ops57b) (h : stepLoc env lc s v = .ok s') :
    ∃ argv r, v.args.toList.mapM (s.read lc) = .ok argv ∧
      evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) = .ok r ∧
      s' = s.write lc v.id (r.retypeL (lc.ty v.id)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := ops57b_facts hmem
  exact stepLoc_noclobber hl ht h1 h2 h3 h4 h5 h6 h7 h8 h9 h

/-- `DMB [k] mem` returns the memory: the state stays. -/
theorem stepLoc_dmb57 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64DMB) {a0 : ID} (ha : v.args = #[a0]) {mm : Mem}
    (hsm : s.mem = .mem mm) (hm : s.read lc a0 = .ok (.mem mm)) (hh : lc.home v.id = none)
    (hmt : memTy (lc.ty v.id) = true) (h : stepLoc env lc s v = .ok s') : s' = s := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := noclob57 hl ht (by rw [hop]; simp [ops57b]) h
  rw [ha] at hmap
  change ((s.read lc a0).bind fun x => Res.ok [x]) = _ at hmap
  rw [hm] at hmap
  cases hmap
  have hev : evalOpL true env lc.ctx s.fr v [.mem mm] (lc.ty v.id) =
      arm64Op true env lc.ctx s.fr v [.mem mm] (lc.ty v.id) := by
    unfold evalOpL; rw [hop]; rfl
  rw [hev] at hr
  cases hn : nilFaults true lc.ctx v [.mem mm] with
  | some m =>
    have he : arm64Op true env lc.ctx s.fr v [.mem mm] (lc.ty v.id) = .panic .nilDeref m := by
      unfold arm64Op; rw [hn]
    rw [he] at hr; cases hr
  | none =>
    have he : arm64Op true env lc.ctx s.fr v [.mem mm] (lc.ty v.id) = .ok (.mem mm) := by
      unfold arm64Op; rw [hn, hop]
    rw [he] at hr; cases hr
    rw [write_mem hh hmt, memTy_eq hmt, retypeL_mem, ← hsm]

/-- `PRFM [k] addr mem` returns the memory: the state stays. -/
theorem stepLoc_prfm57 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64PRFM) {a0 a1 : ID} (ha : v.args = #[a0, a1]) {mm : Mem}
    (hsm : s.mem = .mem mm) (hm : s.read lc a1 = .ok (.mem mm)) (hh : lc.home v.id = none)
    (hmt : memTy (lc.ty v.id) = true) (h : stepLoc env lc s v = .ok s') : s' = s := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := noclob57 hl ht (by rw [hop]; simp [ops57b]) h
  rw [ha] at hmap
  change ((s.read lc a0).bind fun x => (s.read lc a1).bind fun y => Res.ok [x, y]) = _ at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
    rw [hx, hm] at hmap
    cases hmap
    have hev : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
        arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) := by
      unfold evalOpL; rw [hop]; rfl
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) = .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) = .ok (.mem mm) := by
        unfold arm64Op; rw [hn, hop]
      rw [he] at hr; cases hr
      rw [write_mem hh hmt, memTy_eq hmt, retypeL_mem, ← hsm]

private theorem mapM_four57 {a b c d : ID} :
    [a, b, c, d].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        (s.read lc d).bind fun w => .ok [x, y, z, w] := rfl

/-- `FSTPS`/`FSTPD [off] a x y mem` (`fstpOf`: `n`-byte elements): the `n`-byte writes of `x` and
`y` at `pairAddr`, in that order, which succeeded (`stepLoc_stp` at `n`). -/
theorem stepLoc_fstp57 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {n : Nat} (hop : fstpOf v.op = some n) {a0 a1 a2 a3 : ID} (ha : v.args = #[a0, a1, a2, a3])
    {mm : Mem} (hm : s.read lc a3 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y z p q mm1 mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ s.read lc a2 = .ok z ∧
      pairAddr lc.ctx v n x = some (p, q) ∧ mm.write p (Arm64.storeBytes n y) = some mm1 ∧
      mm1.write q (Arm64.storeBytes n z) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := noclob57 hl ht (fstpOf_mem hop) h
  rw [ha] at hmap
  change [a0, a1, a2, a3].mapM (s.read lc) = _ at hmap
  rw [mapM_four57] at hmap
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
    have hev : evalOpL true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
        arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) := by
      rcases fstpOf_some hop with ⟨ho, -⟩ | ⟨ho, -⟩ <;> (unfold evalOpL; rw [ho]; rfl)
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, y, z, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      cases hpq : pairAddr lc.ctx v n x with
      | none =>
        have he : ∃ m1 m2, arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
            if [x, y, z, Val.mem mm].any (fun | .poison => true | _ => false) then .stuck m1
            else .stuck m2 := by
          rcases fstpOf_some hop with ⟨ho, rfl⟩ | ⟨ho, rfl⟩ <;>
            exact ⟨_, _, by unfold arm64Op; rw [hn, ho]; simp only [hpq]; rfl⟩
        obtain ⟨m1, m2, he⟩ := he
        rw [he] at hr
        split at hr <;> cases hr
      | some pq =>
        obtain ⟨p, q⟩ := pq
        have he : ∃ w, arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
            writeRes w (Arm64.storePair n p q y z mm) := by
          rcases fstpOf_some hop with ⟨ho, rfl⟩ | ⟨ho, rfl⟩ <;>
            exact ⟨_, by unfold arm64Op; rw [hn, ho]; simp only [hpq]; rfl⟩
        obtain ⟨w, he⟩ := he
        rw [he] at hr
        cases hw1 : mm.write p (Arm64.storeBytes n y) with
        | none =>
          simp only [Arm64.storePair, hw1, Option.bind_none] at hr
          cases hr
        | some mm1 =>
          cases hw2 : mm1.write q (Arm64.storeBytes n z) with
          | none =>
            simp only [Arm64.storePair, hw1, hw2, Option.bind_some] at hr
            cases hr
          | some mm' =>
            simp only [Arm64.storePair, hw1, hw2, Option.bind_some] at hr
            cases hr
            exact ⟨x, y, z, p, q, mm1, mm', rfl, rfl, rfl, hpq, hw1, hw2, rfl⟩

end Step

/-! ## The machine -/

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `DMB $k` and `PRFM 0(Rn), $k` have no effect (`progEffect`'s `DMB`/`PRFM` arm): the PC moves
to the fall-through. -/
theorem progStep_barrier57 (hn : L.nextAddr p.id = some next) (has : p.as = .DMB ∨ p.as = .PRFM) :
    progStep L p s = .ok { s with pc := next } := by
  have hsk : p.isSkip = false := by rcases has with h | h <;> simp [Prog.isSkip, h]
  have he : progEffect ⟨L, s, p⟩ = .ok {} := by
    rcases has with h | h
    · have hname : As.name .DMB = "DMB" := rfl
      unfold progEffect
      simp (config := { decide := true }) only [h, hname, ProgOp.baseOf, ↓reduceIte,
        ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS]
      rfl
    · have hname : As.name .PRFM = "PRFM" := rfl
      unfold progEffect
      simp (config := { decide := true }) only [h, hname, ProgOp.baseOf, ↓reduceIte,
        ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS]
      rfl
  rw [progStep_eq hn hsk he rfl]
  rfl

/-- The opcode of a float pair store of 4- or 8-byte elements. -/
private theorem fstpAs_cases {n : Nat} (hn : n = 4 ∨ n = 8) :
    (n = 4 ∧ fstpAs n = .FSTPS) ∨ (n = 8 ∧ fstpAs n = .FSTPD) := by
  rcases hn with rfl | rfl
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-- `FSTPS`/`FSTPD (Fa, Fb)` at the address `A` of its operand: the low `n` bytes of `V ka` at
`A`, then those of `V kb` `n` bytes above. -/
private theorem eff_fstp57 {c : ProgCtx} {n ka kb : Nat} {A : BitVec 64} (hka : ka < 32)
    (hkb : kb < 32) (hn : n = 4 ∨ n = 8) (has : c.p.as = fstpAs n)
    (hf : c.p.from_ = pairA (REG_F0 + ka) (REG_F0 + kb)) (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, n, (c.s.v (BitVec.ofNat 5 ka)).toNat % 2 ^ (8 * n)),
        (A + BitVec.ofNat 64 n, n, (c.s.v (BitVec.ofNat 5 kb)).toNat % 2 ^ (8 * n))] } := by
  rcases fstpAs_cases hn with ⟨rfl, hfa⟩ | ⟨rfl, hfa⟩
  · have hname : As.name .FSTPS = "FSTPS" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hfa, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_v_f0 hka, ctx_v_f0 hkb]
    rfl
  · have hname : As.name .FSTPD = "FSTPD" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hfa, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_v_f0 hka, ctx_v_f0 hkb]
    rfl

/-- `FSTPS`/`FSTPD (Fa, Fb), off(<nc>)` at a frame operand, both addresses outside the nil page. -/
theorem progStep_fstp57 {n ka kb : Nat} {nc : AddrName} {off : Int} (hka : ka < 32)
    (hkb : kb < 32) (hn4 : n = 4 ∨ n = 8)
    (hn : L.nextAddr p.id = some next) (has : p.as = fstpAs n)
    (hf : p.from_ = pairA (REG_F0 + ka) (REG_F0 + kb)) (ht : slotA p.to nc off = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hnil : nilPage (s.sp + BitVec.ofInt 64 (frameOff L nc off)) = false)
    (hnil' : nilPage (s.sp + BitVec.ofInt 64 (frameOff L nc off) + BitVec.ofNat 64 n) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem (s.sp + BitVec.ofInt 64 (frameOff L nc off)) n
          (BitVec.ofNat (8 * n) ((s.v (BitVec.ofNat 5 ka)).toNat % 2 ^ (8 * n))))
        (s.sp + BitVec.ofInt 64 (frameOff L nc off) + BitVec.ofNat 64 n) n
          (BitVec.ofNat (8 * n) ((s.v (BitVec.ofNat 5 kb)).toNat % 2 ^ (8 * n))),
      pc := next } := by
  have hsk : p.isSkip = false := by
    rcases fstpAs_cases hn4 with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [Prog.isSkip, has, h]
  have he := eff_fstp57 (c := ⟨L, s, p⟩) hka hkb hn4 has hf (ctx_mem_slot ht hnc)
  rw [progStep_eq hn hsk he (by simp [Eff.nilAccess?, List.find?, hnil, hnil'])]
  rfl

end Progs

/-! ## The frame variable's block -/

/-- The block `bk` an access `v` of a frame variable at the operand `nc`, `off` reaches: every
access with `v`'s aux addresses `bk` at its offset, and `bk` is at `SP + frameOff` under the
injection. -/
structure VarAt57 (lc : LocCtx) (E : MatchEnv) (L : Link) (v : Value) (nc : AddrName) (off : Int)
    (bk : Blk) : Prop where
  sym : ∀ (v' : Value) (a : Val), v'.aux = v.aux →
    symAddr lc.ctx v' a = some ⟨bk, BitVec.ofInt 64 v'.auxInt.toInt⟩
  cls : nc = .AUTO ∨ nc = .PARAM
  addr : ∃ a, E.ι bk = some a ∧
    a + BitVec.ofInt 64 v.auxInt.toInt = E.sp + BitVec.ofInt 64 (frameOff L nc off)

/-- An access of `FVar57` reaches its variable's `local` (G49) or `temp` (G6) block. -/
theorem varAt57 {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E : MatchEnv} {id : ID} {v : Value} {nc : AddrName} {off : Int}
    (hE : G49Env lc g L ps ret tab E) (hv : lc.ctx.f.value? id = some v)
    (hfv : FVar57 lc g v nc off) : ∃ bk, VarAt57 lc E L v nc off bk := by
  cases hfv with
  | loc h =>
    exact ⟨_, fun v' a hx => symAddr_local (hx.trans h.aux) h.var h.loc, h.cls,
      var49_addr h hv hE.vars⟩
  | temp h =>
    exact ⟨_, fun v' a hx => symAddr_var (hx.trans h.aux) h.var h.temp, .inl rfl,
      var_addr h hv hE.env.env.env.env.vars⟩

/-- An `Int64` offset moved by `n`, as a machine word. -/
private theorem ofInt_addN57 (k : Int64) {n : Nat} (hn : n = 4 ∨ n = 8) :
    BitVec.ofInt 64 (k + Int64.ofNat n).toInt = BitVec.ofInt 64 k.toInt + BitVec.ofNat 64 n := by
  show BitVec.ofInt 64 (k + Int64.ofNat n).toBitVec.toInt =
    BitVec.ofInt 64 k.toBitVec.toInt + BitVec.ofNat 64 n
  rw [BitVec.ofInt_toInt, BitVec.ofInt_toInt, Int64.toBitVec_add]
  rcases hn with rfl | rfl <;> rfl

/-- The element addresses of a pair access of the variable: its block at the offset and `n` bytes
above. -/
theorem VarAt57.pair {lc : LocCtx} {E : MatchEnv} {L : Link} {v : Value} {nc : AddrName}
    {off : Int} {bk : Blk} (h : VarAt57 lc E L v nc off bk) {n : Nat} (hn : n = 4 ∨ n = 8)
    (a : Val) :
    pairAddr lc.ctx v n a = some (⟨bk, BitVec.ofInt 64 v.auxInt.toInt⟩,
      ⟨bk, BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n⟩) := by
  unfold pairAddr
  rw [h.sym v a rfl, h.sym { v with auxInt := v.auxInt + Int64.ofNat n } a rfl]
  simp only [Option.bind_some, Option.map_some, ofInt_addN57 _ hn]

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- A value with no home whose one Prog only moves the PC: the state stays. -/
private theorem op_skip57 (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hK : KNext lc v K K') (hhn : lc.home v.id = none)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {pat : Pat} (hvs : OneAt2 psA j pat j')
    (hstep : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m with pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s ∧ SlotInv lc s := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl (hstep k hk hok)),
    { hm with pc := hj'.symm }, hinv.mono (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)),
    hsi⟩

/-- `DMB $k`: the PC moves on. -/
theorem g57_dmb (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hop : v.op = .ARM64DMB) (hsz1 : v.args.size = 1) (hmt : memTy (lc.ty v.id) = true)
    (hhn : lc.home v.id = none) (hma : memArg lc v 0 = .ok ())
    (hvs : OneAt2 psA j (.ofShape (dmbShape v.auxInt.toInt)) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  obtain ⟨a0, ha0, hamt, hah0⟩ := memArg_spec hma
  obtain ⟨mm, hmm, -⟩ := hm.mem
  obtain rfl := stepLoc_dmb57 hl htemp hop (arr1 hsz1 ha0) hmm (read_mem hl hah0 hamt hmm) hhn
    hmt hs
  refine op_skip57 F hm hinv hsi hK hhn hj hj' hvs fun k hk hok => ?_
  obtain ⟨has, -⟩ := Shape.ok_eq hok
  exact progStep_barrier57 (nextAddr_pcAt F.nodup hk) (.inl has)

/-- `PRFM 0(Rn), $k`: the PC moves on. -/
theorem g57_prfm (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rn : Int} (hop : v.op = .ARM64PRFM) (hsz2 : v.args.size = 2)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none) (hma : memArg lc v 1 = .ok ())
    (hvs : OneAt2 psA j (.ofShape (prfmShape rn v.auxInt.toInt)) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm, hmm, -⟩ := hm.mem
  obtain rfl := stepLoc_prfm57 hl htemp hop (arr2 hsz2 ha0 ha1) hmm (read_mem hl hah1 hamt hmm)
    hhn hmt hs
  refine op_skip57 F hm hinv hsi hK hhn hj hj' hvs fun k hk hok => ?_
  obtain ⟨has, -⟩ := Shape.ok_eq hok
  exact progStep_barrier57 (nextAddr_pcAt F.nodup hk) (.inr has)

/-- `FMOVS`/`FMOVD Fs, off(<nc>)`: the store of the float's bytes to the frame variable's block
(`g44_fstore` at a frame operand, `g49_store`), outside the frame's saved words and slots. -/
theorem g57_fstore (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {nc : AddrName} {off : Int} {bk : Blk}
    (hB : VarAt57 lc E (Link.byId sym text az ez psA.toList) v nc off bk) {rs : Int}
    (hop : v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore) (hsz3 : v.args.size = 3)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hso : fargObj lc v 1 = .ok (8 * fBytes v.op, rs)) (hma : memArg lc v 2 = .ok ())
    (hvs : OneAt2 psA j ⟨plain (fmovAs (8 * fBytes v.op)) (· == regA rs) (slotA · nc off),
      (fmovAs (8 * fBytes v.op)).name⟩ j')
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
  rw [hB.sym v x rfl] at hsym
  cases hsym
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  have hn := fBytes_cases v.op
  have hn' : fBytes v.op = 1 ∨ fBytes v.op = 2 ∨ fBytes v.op = 4 ∨ fBytes v.op = 8 := by omega
  have hmov := fmovAs_movMem hn
  have hyv' : ValRel E.ι y ((m.v (BitVec.ofNat 5 ks)).setWidth 64) := valRel_of_fvalRel hyv
  have hcs : 8 * fBytes v.op ≤ 8 * fBytes v.op ∨ 8 * fBytes v.op = 1 := .inl (Nat.le_refl _)
  have hbs := (storeBytes_relN hA hn' hyv' hyf hcs).1
  have hcan : mm.canWrite ⟨bk, BitVec.ofInt 64 v.auxInt.toInt⟩ (fBytes v.op) = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨a, hpa, haeq⟩ := hB.addr
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < fBytes v.op) (Or.inl hcan)
  obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hk0 hn' hpa hyv' hyf hcs hw
  have hsep' : SepFrom E.ι (StkAt E) mm' := by
    intro b2 al2 a2 hb hι' y hy
    obtain ⟨al1, hb1, hs1⟩ := hback b2 al2 hb
    rw [← hs1]; exact hsep0 b2 al1 a2 hb1 hι' y hy
  have hword : ∀ k : Nat, k < 32 →
      ((m.v (BitVec.ofNat 5 k)).setWidth 64).toNat % 2 ^ (8 * fBytes v.op) =
        (m.v (BitVec.ofNat 5 k)).toNat % 2 ^ (8 * fBytes v.op) := by
    intro k _
    rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM' hk' hsep'
    (fun y hy => hout y fun j hj he => hsep0 _ _ _ hal hpa y hy ⟨by omega, by omega⟩)
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k1 hk1 hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf1, -, ht1, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf1
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k1 } psA.toList[k1]).mem psA.toList[k1].to =
      .ok (a + BitVec.ofInt 64 v.auxInt.toInt, none) := by
    rw [ctx_mem_slot ht1 hB.cls]
    exact congrArg (fun z => Except.ok (z, none)) hA'
  rw [progStep_fstoreAt hks (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf1
    (slotA_eq ht1).1 hma' hnil, hword ks hks]

/-- `FSTPS`/`FSTPD (Fa, Fb), off(<nc>)`: the two stores of the floats' bytes to the frame
variable's block (`g49_stp` with V registers), outside the frame's saved words and slots. -/
theorem g57_fstp (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {nc : AddrName} {off : Int} {bk : Blk}
    (hB : VarAt57 lc E (Link.byId sym text az ez psA.toList) v nc off bk) {n : Nat} {rx ry : Int}
    (hop : fstpOf v.op = some n) (hsz4 : v.args.size = 4)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hxo : fargObj lc v 1 = .ok (8 * n, rx)) (hyo : fargObj lc v 2 = .ok (8 * n, ry))
    (hma : memArg lc v 3 = .ok ())
    (hvs : OneAt2 psA j ⟨plain (fstpAs n) (· == pairA rx ry) (slotA · nc off), (fstpAs n).name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hn48 : n = 4 ∨ n = 8 := by rcases fstpOf_some hop with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  have hn' : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by omega
  have hnp : v.op ≠ .Phi := by rcases fstpOf_some hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨a1, r1, ha1, hah1, hfo1, hft1, hca1⟩ := fargObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hfo2, hft2, hca2⟩ := fargObj_spec hyo
  obtain ⟨kx, hkx, rfl, hkx'⟩ := fobjOf?_some hfo1
  obtain ⟨ky, hky, rfl, hky'⟩ := fobjOf?_some hfo2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  have hr1 : r1 ≠ zeroReg := by have := (objV?_some hkx').1; unfold zeroReg; omega
  have hr2 : r2 ≠ zeroReg := by have := (objV?_some hky').1; unfold zeroReg; omega
  obtain ⟨Y, hY, hyv, hyf⟩ := arg_relV hl hm hinv hah1 hft1 hca1
    (kread_arg hR hnp ha1 hah1 hca1 hr1) hkx'
  obtain ⟨Z, hZ, hzv, hzf⟩ := arg_relV hl hm hinv hah2 hft2 hca2
    (kread_arg hR hnp ha2 hah2 hca2 hr2) hky'
  obtain ⟨x', y, z, p, q, mm1, mm', -, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_fstp57 hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  rw [hB.pair hn48] at hpq
  cases hpq
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨a, hpa, haeq⟩ := hB.addr
  have hyv' : ValRel E.ι Y ((m.v (BitVec.ofNat 5 kx)).setWidth 64) := valRel_of_fvalRel hyv
  have hzv' : ValRel E.ι Z ((m.v (BitVec.ofNat 5 ky)).setWidth 64) := valRel_of_fvalRel hzv
  have hcs : 8 * n ≤ 8 * n ∨ 8 * n = 1 := .inl (Nat.le_refl _)
  have hby := (storeBytes_relN hA hn' hyv' hyf hcs).1
  have hbz := (storeBytes_relN hA hn' hzv' hzf hcs).1
  have hcan1 : mm.canWrite ⟨bk, BitVec.ofInt 64 v.auxInt.toInt⟩ n = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inl hcan1)
  obtain ⟨hM1, hk1, hback1, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hk0 hn' hpa hyv' hyf hcs hw1
  have hcan2 : mm1.canWrite ⟨bk, BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n⟩ n = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨hnil', -⟩ := access_nil hM1 hpa (by omega : 0 < n) (Or.inl hcan2)
  obtain ⟨hM2, hk2, hback2, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 hn' hpa hzv' hzf hcs hw2
  have hsep1 : SepFrom E.ι (StkAt E) mm1 := by
    intro b2 al a2 hb hι' w hw
    obtain ⟨al0, hb0, hs0⟩ := hback1 b2 al hb
    rw [← hs0]; exact hsep0 b2 al0 a2 hb0 hι' w hw
  have hsep2 : SepFrom E.ι (StkAt E) mm' := by
    intro b2 al a2 hb hι' w hw
    obtain ⟨al0, hb0, hs0⟩ := hback2 b2 al hb
    rw [← hs0]; exact hsep1 b2 al0 a2 hb0 hι' w hw
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have hA' : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) =
      a + BitVec.ofInt 64 v.auxInt.toInt := by rw [hm.frame.1, haeq]
  have hAn : m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off) +
      BitVec.ofNat 64 n = a + (BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n) := by
    rw [hA', BitVec.add_assoc]
  have hword : ∀ k : Nat, k < 32 →
      ((m.v (BitVec.ofNat 5 k)).setWidth 64).toNat % 2 ^ (8 * n) =
        (m.v (BitVec.ofNat 5 k)).toNat % 2 ^ (8 * n) := by
    intro k _
    rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM2 hk2 hsep2
    (fun w hw => (hout2 w fun j hj he => hsep1 _ _ _ hal2 hpa w hw ⟨by omega, by omega⟩).trans
      (hout1 w fun j hj he => hsep0 _ _ _ hal1 hpa w hw ⟨by omega, by omega⟩))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf1, -, ht1, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf1
  rw [progStep_fstp57 hkx hky hn48 (nextAddr_pcAt F.nodup hk) has hf1 ht1 hB.cls
    (by rw [hA']; exact hnil) (by rw [hAn]; exact hnil'), hAn, hA', hword kx hkx, hword ky hky]

end Cases

/-! ## The theorem -/

/-- One value of G57's group B, in `vk55_step`'s form under `G49Env`: it runs its one Prog, keeps
the match and `G3Inv` under the same activation, and empties the upper-bit table. -/
theorem vk57b_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hcf : checkFrame lc g = .ok ())
    (hv : lc.ctx.f.value? id = some v) (hVK : VK57b lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
      UOKL m' (uStep35 lc L v) := by
  obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE.env.env.env.env.env
  have hR := kread_of_reads hreads
  have hsz := slot_sizes hlcE hcf hinv.slots
  have fin : ∀ m', v.op ∈ ops57b →
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' →
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
        UOKL m' (uStep35 lc L v) := fun m' hmem h1 h2 h3 h4 => by
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_57b hmem]
    exact fun e he => by cases he
  cases hVK with
  | dmb hop hsz1 hmt hhn hma =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g57_dmb (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz1 hmt hhn hma hvs htemp hs
    exact fin m' (by rw [hop]; simp [ops57b]) h1 h2 h3 h4
  | prfm hop hsz2 hmt hhn _ hma =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g57_prfm (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz2 hmt hhn hma hvs htemp hs
    exact fin m' (by rw [hop]; simp [ops57b]) h1 h2 h3 h4
  | store hfv hop hsz3 hmt hhn hso hma =>
    obtain ⟨bk, hB⟩ := varAt57 hE hv hfv
    obtain ⟨m', h1, h2, h3, h4⟩ := g57_fstore (H := H) F hF hsz hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hB hop hsz3 hmt hhn hso hma hvs htemp hs
    exact fin m' (by rcases hop with h | h <;> rw [h] <;> simp [ops57b]) h1 h2 h3 h4
  | stp hfv hop hsz4 hmt hhn hxo hyo hma =>
    obtain ⟨bk, hB⟩ := varAt57 hE hv hfv
    obtain ⟨m', h1, h2, h3, h4⟩ := g57_fstp (H := H) F hF hsz hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hB hop hsz4 hmt hhn hxo hyo hma hvs
      htemp hs
    exact fin m' (fstpOf_mem hop) h1 h2 h3 h4

end GoFV.Proof.Gen
