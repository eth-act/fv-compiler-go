import GoFV.Gen.Check48
import GoFV.Proof.Gen.G3
import GoFV.Proof.Gen.G4
import GoFV.Proof.Gen.G44
import GoFV.Proof.Gen.G50
import GoFV.Proof.Gen.G57a
import GoFV.Proof.Gen.Stack

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G48: the accesses off `SP` (`docs/plans/proofs3.md` §8, item 7)

The steps of the values G48 adds besides calls (`Gen/Check48.lean`, `spKind48`): a store or a
load of `n` bytes at `o(RSP)` (`memA regSP o`), whose Phase 1 address is `SP`'s pointer
`⟨outargs act, 0⟩` moved by `o`. Their base is the Go register `SP`, which `LocMatch` does not
relate; the lemmas take its relation to the machine's `SP` as a premise on the base's read
(`hsp`: `ValRel E.ι x E.sp`, which `SPInv` gives once `outargs act` sits at `SP`).

The memory facts are stated in the separation of any mode `w` (`SepAt`, `Proof/Gen/G1.lean`), of
which they use `SepFromW` (`SepAt.sepW`): the outgoing area at `SP` overlaps the saved `LR` word
(`StkAt`) in its first 8 bytes, which no Phase 1 write reaches (`Blk.writableFrom`), so a store's
machine bytes stay away from the frame words and the spill slots (`sepW_out`) and the store keeps
the separation (`SepAt.write`).

* `g48_spStore`: `MOV{D,W,H,B} Rs, o(RSP)`;
* `g48_spLoad`: `MOV{D,W,WU,H,HU,B,BU} o(RSP), Rd`;
* `g48_spStp`, `g48_spStpw`, `g48_spFstpd`: `STP`, `STPW`, `FSTPD (Rx, Ry), o(RSP)`;
* `g48_spFStore`, `g48_spFLoad`: `FMOV{S,D}` to and from `o(RSP)`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The machine's `o(RSP)` -/

/-- The address of `o(RSP)` (`memA regSP o`, no index, no pre- or post-increment). -/
theorem ctx_mem_sp {c : ProgCtx} {off : Int} (hsc : c.p.scond = 0) :
    c.mem (memA regSP off) = .ok (c.s.sp + BitVec.ofInt 64 off, none) := by
  simp (config := { decide := true }) only [ProgCtx.mem, memA, ProgCtx.x, regSP, hsc]
  rfl

/-- `STP (Rx, Ry)` at the address `A` of its operand (`Progs4.lean`'s private `eff_stp`). -/
private theorem eff_stp48 {c : ProgCtx} {kx ky : Nat} {A : BitVec 64} (hkx : kx < 32)
    (hky : ky < 32) (has : c.p.as = .STP)
    (hf : c.p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky)) (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, 8, (c.s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8)),
        (A + BitVec.ofNat 64 8, 8, (c.s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))] } := by
  have hname : As.name .STP = "STP" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_x_r0 hkx, ctx_x_r0 hky]
  rfl

/-- `STP (Rx, Ry)` at the address `A` of its memory operand, whatever the operand (`o(RSP)`),
both addresses outside the nil page (`Progs4.lean`'s private `step_stp`). -/
theorem progStep_stpAt {L : Link} {p : Prog} {s : MState} {next : BitVec 64} {kx ky : Nat}
    {A : BitVec 64} (hkx : kx < 32) (hky : ky < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .STP)
    (hf : p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky))
    (hma : (ProgCtx.mk L s p).mem p.to = .ok (A, none))
    (hnil : nilPage A = false) (hnil8 : nilPage (A + 8) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem A 8
          (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8))))
        (A + 8) 8 (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))),
      pc := next } := by
  have he := eff_stp48 (c := ⟨L, s, p⟩) hkx hky has hf hma
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by
      have h8 : nilPage (A + 8#64) = false := hnil8
      simp [Eff.nilAccess?, List.find?, hnil, h8])]
  rfl

/-! ## `STPW` -/

section Stpw

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_four48 {a b c d : ID} :
    [a, b, c, d].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        (s.read lc d).bind fun w => .ok [x, y, z, w] := rfl

/-- `FSTPD [off] a x y mem`: the 8-byte writes of `x` and `y` at `pairAddr` (`stPair 8`), in that
order, which succeeded (`stepLoc_stp` on V registers' values). -/
theorem stepLoc_fstpd (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64FSTPD) {a0 a1 a2 a3 : ID} (ha : v.args = #[a0, a1, a2, a3]) {mm : Mem}
    (hm : s.read lc a3 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y z p q mm1 mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ s.read lc a2 = .ok z ∧
      pairAddr lc.ctx v 8 x = some (p, q) ∧ mm.write p (Arm64.storeBytes 8 y) = some mm1 ∧
      mm1.write q (Arm64.storeBytes 8 z) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmap
  change [a0, a1, a2, a3].mapM (s.read lc) = _ at hmap
  rw [mapM_four48] at hmap
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
      unfold evalOpL; rw [hop]; rfl
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, y, z, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      cases hpq : pairAddr lc.ctx v 8 x with
      | none =>
        have he : ∃ m1 m2, arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
            if [x, y, z, Val.mem mm].any (fun | .poison => true | _ => false) then .stuck m1
            else .stuck m2 :=
          ⟨_, _, by unfold arm64Op; rw [hn, hop]; simp only [hpq]; rfl⟩
        obtain ⟨m1, m2, he⟩ := he
        rw [he] at hr
        split at hr <;> cases hr
      | some pq =>
        obtain ⟨p, q⟩ := pq
        have he : ∃ w, arm64Op true env lc.ctx s.fr v [x, y, z, .mem mm] (lc.ty v.id) =
            writeRes w (Arm64.storePair 8 p q y z mm) :=
          ⟨_, by unfold arm64Op; rw [hn, hop]; simp only [hpq]; rfl⟩
        obtain ⟨w, he⟩ := he
        rw [he] at hr
        cases hw1 : mm.write p (Arm64.storeBytes 8 y) with
        | none =>
          simp only [Arm64.storePair, hw1, Option.bind_none] at hr
          cases hr
        | some mm1 =>
          cases hw2 : mm1.write q (Arm64.storeBytes 8 z) with
          | none =>
            simp only [Arm64.storePair, hw1, hw2, Option.bind_some] at hr
            cases hr
          | some mm' =>
            simp only [Arm64.storePair, hw1, hw2, Option.bind_some] at hr
            cases hr
            exact ⟨x, y, z, p, q, mm1, mm', rfl, rfl, rfl, hpq, hw1, hw2, rfl⟩

end Stpw

/-- `STPW (Rx, Ry)` at the address `A` of its operand: the low 4 bytes of `X kx` at `A`, then those
of `X ky` 4 bytes above. -/
private theorem eff_stpw48 {c : ProgCtx} {kx ky : Nat} {A : BitVec 64} (hkx : kx < 32)
    (hky : ky < 32) (has : c.p.as = .STPW)
    (hf : c.p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky)) (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, 4, (c.s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 4)),
        (A + BitVec.ofNat 64 4, 4, (c.s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 4))] } := by
  have hname : As.name .STPW = "STPW" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_x_r0 hkx, ctx_x_r0 hky]
  rfl

/-- `STPW (Rx, Ry)` at the address `A` of its memory operand (`o(RSP)`), both addresses outside
the nil page: the low 4 bytes of `X kx` at `A`, then those of `X ky` 4 bytes above. -/
theorem progStep_stpwAt {L : Link} {p : Prog} {s : MState} {next : BitVec 64} {kx ky : Nat}
    {A : BitVec 64} (hkx : kx < 32) (hky : ky < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .STPW)
    (hf : p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky))
    (hma : (ProgCtx.mk L s p).mem p.to = .ok (A, none))
    (hnil : nilPage A = false) (hnil4 : nilPage (A + 4) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem A 4
          (BitVec.ofNat (8 * 4) ((s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 4))))
        (A + 4) 4 (BitVec.ofNat (8 * 4) ((s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 4))),
      pc := next } := by
  have he := eff_stpw48 (c := ⟨L, s, p⟩) hkx hky has hf hma
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by
      have h4 : nilPage (A + 4#64) = false := hnil4
      simp [Eff.nilAccess?, List.find?, hnil, h4])]
  rfl

/-- `FSTPD (Fx, Fy)` at the address `A` of its operand: the low 8 bytes of `V kx` at `A`, then those
of `V ky` 8 bytes above. -/
private theorem eff_fstpd48 {c : ProgCtx} {kx ky : Nat} {A : BitVec 64} (hkx : kx < 32)
    (hky : ky < 32) (has : c.p.as = .FSTPD)
    (hf : c.p.from_ = pairA (REG_F0 + kx) (REG_F0 + ky)) (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, 8, (c.s.v (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8)),
        (A + BitVec.ofNat 64 8, 8, (c.s.v (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))] } := by
  have hname : As.name .FSTPD = "FSTPD" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_v_f0 hkx, ctx_v_f0 hky]
  rfl

/-- `FSTPD (Fx, Fy)` at the address `A` of its memory operand (`o(RSP)`), both addresses outside
the nil page: the low 8 bytes of `V kx` at `A`, then those of `V ky` 8 bytes above. -/
theorem progStep_fstpdAt {L : Link} {p : Prog} {s : MState} {next : BitVec 64} {kx ky : Nat}
    {A : BitVec 64} (hkx : kx < 32) (hky : ky < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .FSTPD)
    (hf : p.from_ = pairA (REG_F0 + kx) (REG_F0 + ky))
    (hma : (ProgCtx.mk L s p).mem p.to = .ok (A, none))
    (hnil : nilPage A = false) (hnil8 : nilPage (A + 8) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem A 8
          (BitVec.ofNat (8 * 8) ((s.v (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8))))
        (A + 8) 8 (BitVec.ofNat (8 * 8) ((s.v (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))),
      pc := next } := by
  have he := eff_fstpd48 (c := ⟨L, s, p⟩) hkx hky has hf hma
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by
      have h8 : nilPage (A + 8#64) = false := hnil8
      simp [Eff.nilAccess?, List.find?, hnil, h8])]
  rfl

/-! ## Separation -/

variable {ι : Blk → Option (BitVec 64)}

/-- A successful write of `n > 0` bytes starts at or above `Blk.writableFrom`. -/
theorem wf_of_canWrite {mm : Mem} {p : Ptr} {n : Nat} (h : mm.canWrite p n = true) (hn : 0 < n) :
    p.blk.writableFrom ≤ p.off.toNat := by
  unfold Mem.canWrite at h
  cases hf : mm.find? p.blk with
  | none => simp [hf] at h; omega
  | some a =>
    simp only [hf, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · omega
    · exact h.1.1.1.2

/-- Under `SepFromW`, the bytes `[o, o + n)` of a live block at or above its `Blk.writableFrom`
lie outside `P`. -/
theorem sepW_out {P : BitVec 64 → Prop} {mm : Mem} (hsep : SepFromW ι P mm) {bk : Blk} {al : Alloc}
    {a : BitVec 64} (hb : (bk, al) ∈ mm.blocks) (ha : ι bk = some a) {o n : Nat}
    (hwf : bk.writableFrom ≤ o) (hon : o + n ≤ al.data.size) {y : BitVec 64} (hy : P y) :
    ∀ j, j < n → y.toNat ≠ a.toNat + o + j := by
  intro j hj he
  have := (hsep bk al a hb ha y hy (o + j) (by omega) (by omega)).1
  omega

/-! ## The steps -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- **A store off `SP`**: `MOV{D,W,H,B} Rs, o(RSP)` stores `n` bytes at `⟨outargs act, o⟩` (the
base `SP`'s read related to the machine's `SP`, `hsp`). The machine store lies outside the frame
words and the spill slots (`SepFromW`, the write at or above `Blk.writableFrom`), so `LocMatch`
holds after it; the memory keeps distinct keys and its separation, the X registers are kept. -/
theorem g48_spStore (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) {mm : Mem} (hmm : s.mem = .mem mm) (hkn : KeysNodup mm)
    {w : Bool} (hsep : SepAt w E.ι (StkAt E) mm)
    (hregs : ∀ r v c, r ≠ zeroReg → s.regs[r]? = some v → K r = some c → Fits c v)
    (hR : KRead lc v K)
    (hsp : ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → ValRel E.ι x E.sp ∧ Fits 64 x)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n cs : Nat} {rs : Int} {pat : Pat}
    (hop : storeOp? v.op = some (as, n)) (hsz3 : v.args.size = 3) (haux : v.aux = none)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hso : argObj lc v 1 = .ok (cs, rs)) (hma : memArg lc v 2 = .ok ())
    (hc : 8 * n ≤ cs ∨ cs = 1 ∧ n = 1)
    (hpat : ∀ p, pat.ok p = true → p.as = as ∧ p.from_ = regA rs ∧ p.reg = 0 ∧
      p.to = memA regSP v.auxInt.toInt ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0)
    (hvs : OneAt2 psA j pat j') (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m' mm', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ s' = { s with mem := .mem mm' } ∧ KeysNodup mm' ∧
      SepAt w E.ι (StkAt E) mm' ∧ m'.x = m.x := by
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
  obtain ⟨mm0, hmm0, hMI⟩ := hm.mem
  rw [hmm] at hmm0
  cases hmm0
  have hinv : CoreInv E.ι (fun _ => False) K s :=
    ⟨hregs, mm, hmm, hkn, fun _ _ _ _ _ _ h => h.elim⟩
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkks
  obtain ⟨x, y', p, mm', hx, hy', hsym, hw, rfl⟩ := stepLoc_storeN hl htemp hop
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hy] at hy'
  cases hy'
  have hcs : 8 * n ≤ cs ∨ cs = 1 := hc.imp_right And.left
  have hbs := (storeBytes_relN hA hn hyv hyf hcs).1
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  obtain ⟨hxv, hxf⟩ := hsp a0 x ha0 hx
  have haddr : Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p := by
    rw [← hsym]; unfold symAddr; rw [haux]
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < n) (Or.inl hcan)
  obtain ⟨hM', hk', -, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hkn hn hpa hyv hyf hcs hw
  have hwf := wf_of_canWrite hcan (by omega)
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have hP : ∀ y, StkAt E y →
      writeMem m.mem (a + p.off) n
        (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))) y = m.mem y :=
    fun y hy => hout y fun j hj he => sepW_out hsep.sepW hal hpa hwf hoff hy j hj (by omega)
  obtain ⟨hsl, hfr⟩ := stk_keeps hm hF hsz _ hP
  have hlm := locMatch_setMem hm hsl hfr hM' (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, hf, -, ht', hsc, -, -⟩ := hpat _ hok
  have hspm : m.sp = E.sp := hm.frame.1
  refine ⟨_, mm', hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm, rfl, hk',
    SepAt.write hkn hsep hw, rfl⟩
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
      .ok (a + p.off, none) := by
    rw [ht', ctx_mem_sp hsc]
    exact congrArg (fun z => Except.ok (z, none)) (by simpa [hspm] using haeq)
  rw [progStep_storeAt hks (nextAddr_pcAt F.nodup hk) (by rw [has]; exact hmov) hf
    (by rw [ht']; rfl) hma' hnil]
  rfl

/-- **A load off `SP`**: `MOV{D,W,WU,H,HU,B,BU} o(RSP), Rd` loads `n` valid bytes (`hrd`) at
`⟨outargs act, o⟩` (the base `SP`'s read related to the machine's `SP`, `hsp`) into the result's
register: the registers keep their classes under the next class map `K'`, the memory is
unchanged. -/
theorem g48_spLoad (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) {mm : Mem} (hmm : s.mem = .mem mm) (hkn : KeysNodup mm)
    (hregs : ∀ r v c, r ≠ zeroReg → s.regs[r]? = some v → K r = some c → Fits c v)
    (hK : KNext lc v K K')
    (hsp : ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → ValRel E.ι x E.sp ∧ Fits 64 x)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int} {pat : Pat}
    (hrd : ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
      ∃ p bs, Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p ∧ mm.read p n = some bs ∧
        (lc.ty v.id = .bool → ∀ z, mm.load (.int .w8) p = .int .w8 z → z.toNat < 2))
    (hop : loadOp? v.op = some (as, n, sg)) (hsz2 : v.args.size = 2) (haux : v.aux = none)
    (hma : memArg lc v 1 = .ok ()) (hro : resObj lc v = .ok (c, rd))
    (hc : 8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false)
    (hpat : ∀ p, pat.ok p = true → p.as = as ∧ p.from_ = memA regSP v.auxInt.toInt ∧ p.reg = 0 ∧
      p.to = regA rd ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0)
    (hvs : OneAt2 psA j pat j') (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ s'.mem = s.mem ∧ s'.slots = s.slots ∧
      (∀ r v c, r ≠ zeroReg → s'.regs[r]? = some v → K' r = some c → Fits c v) ∧
      ∃ (kd : Nat) (Y : BitVec (8 * n)), rd = GoFV.Asm.ARM64.REG_R0 + kd ∧
        m'.x = (m.wX (BitVec.ofNat 5 kd)
          (if sg then ProgOp.sextTo64 n (Y.setWidth 64) else Y.setWidth 64)).x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp := loadOp?_ne_phi hop
  obtain ⟨hn, hsg⟩ := loadOp?_bytes hop
  have hmov := loadOp?_movMem hop
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd', -⟩ := objOf?_some hor
  subst hrd'
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm0, hmm0, hMI⟩ := hm.mem
  rw [hmm] at hmm0
  cases hmm0
  have hinv : CoreInv E.ι (fun _ => False) K s :=
    ⟨hregs, mm, hmm, hkn, fun _ _ _ _ _ _ h => h.elim⟩
  obtain ⟨x, hx, rfl⟩ := stepLoc_loadN hl htemp hop (arr2 hsz2 ha0 ha1)
    (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, bs, haddr, hrdp, h01⟩ := hrd a0 x ha0 hx
  have hsym : symAddr lc.ctx v x = some p := by unfold symAddr; rw [haux]; exact haddr
  rw [write_reg hvh hcv, hsym]
  simp only [Option.elim]
  obtain ⟨hxv, hxf⟩ := hsp a0 x ha0 hx
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < n)
    (Or.inr (by rw [hrdp]; rfl))
  have hval : ValRel E.ι ((Arm64.loadN (lc.ty v.id) n sg mm p).retypeL (lc.ty v.id))
      (if sg then ProgOp.sextTo64 n ((readMem m.mem (a + p.off) n).setWidth 64)
       else (readMem m.mem (a + p.off) n).setWidth 64) := by
    rcases hc with h8 | ⟨rfl, rfl, rfl⟩
    · have ht := cls_ne_bool hcv h8
      exact valRel_retypeL_lo hA hcv ht ((lo_loadN hA hMI hn hsg ht hpa hrdp).mono (cls_le hcv))
    · have ht := cls_bool hcv
      rw [ht]
      exact valRel_loadBool hA hMI hpa hrdp (h01 ht)
  have hspm : m.sp = E.sp := hm.frame.1
  obtain ⟨m', h1, h2, h3, h4⟩ := op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor hval
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => by
      obtain ⟨has, hf, -, ht', hsc, -, -⟩ := hpat _ hok
      have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].from_ =
          .ok (a + p.off, none) := by
        rw [hf, ctx_mem_sp hsc]
        exact congrArg (fun z => Except.ok (z, none)) (by simpa [hspm] using haeq)
      rw [progStep_loadAt hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov)
        (by rw [hf]; rfl) hma' ht' hnil, wX_pc])
  exact ⟨m', h1, h2, rfl, rfl, h3.regs, kd, _, rfl, h4⟩

/-- **A pair store off `SP`**: `STP (Rx, Ry), o(RSP)` stores two 64-bit registers at
`⟨outargs act, o⟩` and 8 bytes above (`g4_stp` with the base `SP`, `hsp`, in the separation of
mode `w`). -/
theorem g48_spStp (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) {mm : Mem} (hmm : s.mem = .mem mm) (hkn : KeysNodup mm)
    {w : Bool} (hsep : SepAt w E.ι (StkAt E) mm)
    (hregs : ∀ r v c, r ≠ zeroReg → s.regs[r]? = some v → K r = some c → Fits c v)
    (hR : KRead lc v K)
    (hsp : ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → ValRel E.ι x E.sp ∧ Fits 64 x)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rx ry : Int} (hop : v.op = .ARM64STP) (hsz4 : v.args.size = 4) (hax : v.aux = none)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hxo : argObj lc v 1 = .ok (64, rx)) (hyo : argObj lc v 2 = .ok (64, ry))
    (hma : memArg lc v 3 = .ok ())
    (hvs : OneAt2 psA j
      (.ofShape { as := .STP, from_ := pairA rx ry, to := memA regSP v.auxInt.toInt }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m' mm', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ s' = { s with mem := .mem mm' } ∧ KeysNodup mm' ∧
      SepAt w E.ι (StkAt E) mm' ∧ m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec hyo
  obtain ⟨kx, hkx, rfl, hkkx⟩ := objOf?_some hor1
  obtain ⟨ky, hky, rfl, hkky⟩ := objOf?_some hor2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm0, hmm0, hMI⟩ := hm.mem
  rw [hmm] at hmm0
  cases hmm0
  have hinv : CoreInv E.ι (fun _ => False) K s :=
    ⟨hregs, mm, hmm, hkn, fun _ _ _ _ _ _ h => h.elim⟩
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkx
  obtain ⟨Z, hZ, hzv, hzf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkky
  obtain ⟨x, y, z, p, q, mm1, mm', hx, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_stp hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  obtain ⟨hxv, hxf⟩ := hsp a0 x ha0 hx
  obtain ⟨hap, haq⟩ := pairAddr_noAux hax hpq
  have hby := (storeBytes_relN hA (n := 8) (by simp) hyv hyf (Or.inl (Nat.le_refl _))).1
  have hbz := (storeBytes_relN hA (n := 8) (by simp) hzv hzf (Or.inl (Nat.le_refl _))).1
  have hcan1 : mm.canWrite p 8 = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf hap (by omega : 0 < 8) (Or.inl hcan1)
  obtain ⟨hM1, hk1, -, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hkn (by simp) hpa hyv hyf (Or.inl (Nat.le_refl _)) hw1
  have hcan2 : mm1.canWrite q 8 = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨a', hqa, haeq', hnil'⟩ := addr_rel hA hM1 hxv hxf haq (by omega : 0 < 8) (Or.inl hcan2)
  obtain ⟨hM2, hk2, -, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 (by simp) hqa hzv hzf (Or.inl (Nat.le_refl _)) hw2
  have hsep1 := SepAt.write hkn hsep hw1
  have hwf1 := wf_of_canWrite hcan1 (by omega)
  have hwf2 := wf_of_canWrite hcan2 (by omega)
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have haeq8 : a + p.off + 8 = a' + q.off := by rw [← haeq, BitVec.add_assoc]; exact haeq'
  obtain ⟨hsl, hfr⟩ := stk_keeps hm hF hsz _ fun w hw =>
    (hout2 w fun j hj he => sepW_out hsep1.sepW hal2 hqa hwf2 hoff2 hw j hj (by omega)).trans
      (hout1 w fun j hj he => sepW_out hsep.sepW hal1 hpa hwf1 hoff1 hw j hj (by omega))
  have hlm := locMatch_setMem hm hsl hfr hM2 (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  have hspm : m.sp = E.sp := hm.frame.1
  refine ⟨_, mm', hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm, rfl, hk2,
    SepAt.write hk1 hsep1 hw2, rfl⟩
  obtain ⟨has, hf, -, ht', hsc⟩ := Shape.ok_eq hok
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
      .ok (a + p.off, none) := by
    rw [ht', ctx_mem_sp hsc]
    exact congrArg (fun z => Except.ok (z, none)) (by simpa [hspm] using haeq)
  rw [progStep_stpAt hkx hky (nextAddr_pcAt F.nodup hk) has hf hma' hnil
    (by rw [haeq8]; exact hnil'), haeq8]
  rfl

/-- **A narrow pair store off `SP`**: `STPW (Rx, Ry), o(RSP)` stores the low 4 bytes of two
registers of at least 32 bits at `⟨outargs act, o⟩` and 4 bytes above (`g48_spStp` at 4
bytes). -/
theorem g48_spStpw (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) {mm : Mem} (hmm : s.mem = .mem mm) (hkn : KeysNodup mm)
    {w : Bool} (hsep : SepAt w E.ι (StkAt E) mm)
    (hregs : ∀ r v c, r ≠ zeroReg → s.regs[r]? = some v → K r = some c → Fits c v)
    (hR : KRead lc v K)
    (hsp : ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → ValRel E.ι x E.sp ∧ Fits 64 x)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {cx cy : Nat} {rx ry : Int} (hop : v.op = .ARM64STPW) (hsz4 : v.args.size = 4)
    (hax : v.aux = none) (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hxo : argObj lc v 1 = .ok (cx, rx)) (hyo : argObj lc v 2 = .ok (cy, ry))
    (hcx : 32 ≤ cx) (hcy : 32 ≤ cy) (hma : memArg lc v 3 = .ok ())
    (hvs : OneAt2 psA j (.ofShape (stpwSP48 rx ry v.auxInt.toInt)) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m' mm', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ s' = { s with mem := .mem mm' } ∧ KeysNodup mm' ∧
      SepAt w E.ι (StkAt E) mm' ∧ m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec hyo
  obtain ⟨kx, hkx, rfl, hkkx⟩ := objOf?_some hor1
  obtain ⟨ky, hky, rfl, hkky⟩ := objOf?_some hor2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm0, hmm0, hMI⟩ := hm.mem
  rw [hmm] at hmm0
  cases hmm0
  have hinv : CoreInv E.ι (fun _ => False) K s :=
    ⟨hregs, mm, hmm, hkn, fun _ _ _ _ _ _ h => h.elim⟩
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkx
  obtain ⟨Z, hZ, hzv, hzf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkky
  obtain ⟨x, y, z, p, q, mm1, mm', hx, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_stpw hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  obtain ⟨hxv, hxf⟩ := hsp a0 x ha0 hx
  obtain ⟨hap, haq⟩ := pairAddr_noAuxN hax hpq
  have hcy4 : 8 * 4 ≤ cx ∨ cx = 1 := .inl hcx
  have hcz4 : 8 * 4 ≤ cy ∨ cy = 1 := .inl hcy
  have hby := (storeBytes_relN hA (n := 4) (by simp) hyv hyf hcy4).1
  have hbz := (storeBytes_relN hA (n := 4) (by simp) hzv hzf hcz4).1
  have hcan1 : mm.canWrite p 4 = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf hap (by omega : 0 < 4) (Or.inl hcan1)
  obtain ⟨hM1, hk1, -, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hkn (by simp) hpa hyv hyf hcy4 hw1
  have hcan2 : mm1.canWrite q 4 = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨a', hqa, haeq', hnil'⟩ := addr_rel hA hM1 hxv hxf haq (by omega : 0 < 4) (Or.inl hcan2)
  obtain ⟨hM2, hk2, -, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 (by simp) hqa hzv hzf hcz4 hw2
  have hsep1 := SepAt.write hkn hsep hw1
  have hwf1 := wf_of_canWrite hcan1 (by omega)
  have hwf2 := wf_of_canWrite hcan2 (by omega)
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have haeq4 : a + p.off + 4 = a' + q.off := by rw [← haeq, BitVec.add_assoc]; exact haeq'
  obtain ⟨hsl, hfr⟩ := stk_keeps hm hF hsz _ fun w hw =>
    (hout2 w fun j hj he => sepW_out hsep1.sepW hal2 hqa hwf2 hoff2 hw j hj (by omega)).trans
      (hout1 w fun j hj he => sepW_out hsep.sepW hal1 hpa hwf1 hoff1 hw j hj (by omega))
  have hlm := locMatch_setMem hm hsl hfr hM2 (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  have hspm : m.sp = E.sp := hm.frame.1
  refine ⟨_, mm', hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm, rfl, hk2,
    SepAt.write hk1 hsep1 hw2, rfl⟩
  obtain ⟨has, hf, -, ht', hsc⟩ := Shape.ok_eq hok
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
      .ok (a + p.off, none) := by
    rw [ht']
    simp only [stpwSP48]
    rw [ctx_mem_sp hsc]
    exact congrArg (fun z => Except.ok (z, none)) (by simpa [hspm] using haeq)
  rw [progStep_stpwAt hkx hky (nextAddr_pcAt F.nodup hk) has hf hma' hnil
    (by rw [haeq4]; exact hnil'), haeq4]
  rfl

/-- **A float pair store off `SP`**: `FSTPD (Fx, Fy), o(RSP)` stores the low 8 bytes of two V
registers at `⟨outargs act, o⟩` and 8 bytes above (`g48_spStp` on V registers). -/
theorem g48_spFstpd (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) {mm : Mem} (hmm : s.mem = .mem mm) (hkn : KeysNodup mm)
    {w : Bool} (hsep : SepAt w E.ι (StkAt E) mm)
    (hregs : ∀ r v c, r ≠ zeroReg → s.regs[r]? = some v → K r = some c → Fits c v)
    (hR : KRead lc v K)
    (hsp : ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → ValRel E.ι x E.sp ∧ Fits 64 x)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rx ry : Int} (hop : v.op = .ARM64FSTPD) (hsz4 : v.args.size = 4)
    (hax : v.aux = none) (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hxo : fargObj lc v 1 = .ok (64, rx)) (hyo : fargObj lc v 2 = .ok (64, ry))
    (hma : memArg lc v 3 = .ok ())
    (hvs : OneAt2 psA j (.ofShape (fstpdSP48 rx ry v.auxInt.toInt)) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m' mm', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ s' = { s with mem := .mem mm' } ∧ KeysNodup mm' ∧
      SepAt w E.ι (StkAt E) mm' ∧ m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a1, r1, ha1, hah1, hfo1, hft1, hca1⟩ := fargObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hfo2, hft2, hca2⟩ := fargObj_spec hyo
  obtain ⟨kx, hkx, rfl, hkx'⟩ := fobjOf?_some hfo1
  obtain ⟨ky, hky, rfl, hky'⟩ := fobjOf?_some hfo2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm0, hmm0, hMI⟩ := hm.mem
  rw [hmm] at hmm0
  cases hmm0
  have hinv : CoreInv E.ι (fun _ => False) K s :=
    ⟨hregs, mm, hmm, hkn, fun _ _ _ _ _ _ h => h.elim⟩
  have hr1 : r1 ≠ zeroReg := by have := (objV?_some hkx').1; unfold zeroReg; omega
  have hr2 : r2 ≠ zeroReg := by have := (objV?_some hky').1; unfold zeroReg; omega
  obtain ⟨Y, hY, hyv, hyf⟩ := arg_relV hl hm hinv hah1 hft1 hca1
    (kread_arg hR hnp ha1 hah1 hca1 hr1) hkx'
  obtain ⟨Z, hZ, hzv, hzf⟩ := arg_relV hl hm hinv hah2 hft2 hca2
    (kread_arg hR hnp ha2 hah2 hca2 hr2) hky'
  obtain ⟨x, y, z, p, q, mm1, mm', hx, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_fstpd hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  obtain ⟨hxv, hxf⟩ := hsp a0 x ha0 hx
  obtain ⟨hap, haq⟩ := pairAddr_noAux hax hpq
  have hyv' : ValRel E.ι Y ((m.v (BitVec.ofNat 5 kx)).setWidth 64) := valRel_of_fvalRel hyv
  have hzv' : ValRel E.ι Z ((m.v (BitVec.ofNat 5 ky)).setWidth 64) := valRel_of_fvalRel hzv
  have hc8 : 8 * 8 ≤ 64 ∨ (64 : Nat) = 1 := .inl (Nat.le_refl _)
  have hby := (storeBytes_relN hA (n := 8) (by simp) hyv' hyf hc8).1
  have hbz := (storeBytes_relN hA (n := 8) (by simp) hzv' hzf hc8).1
  have hcan1 : mm.canWrite p 8 = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf hap (by omega : 0 < 8) (Or.inl hcan1)
  obtain ⟨hM1, hk1, -, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hkn (by simp) hpa hyv' hyf hc8 hw1
  have hcan2 : mm1.canWrite q 8 = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨a', hqa, haeq', hnil'⟩ := addr_rel hA hM1 hxv hxf haq (by omega : 0 < 8) (Or.inl hcan2)
  obtain ⟨hM2, hk2, -, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 (by simp) hqa hzv' hzf hc8 hw2
  have hsep1 := SepAt.write hkn hsep hw1
  have hwf1 := wf_of_canWrite hcan1 (by omega)
  have hwf2 := wf_of_canWrite hcan2 (by omega)
  have hword : ∀ k : Nat, ((m.v (BitVec.ofNat 5 k)).setWidth 64).toNat % 2 ^ (8 * 8) =
      (m.v (BitVec.ofNat 5 k)).toNat % 2 ^ (8 * 8) := by
    intro k
    rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have haeq8 : a + p.off + 8 = a' + q.off := by rw [← haeq, BitVec.add_assoc]; exact haeq'
  obtain ⟨hsl, hfr⟩ := stk_keeps hm hF hsz _ fun w hw =>
    (hout2 w fun j hj he => sepW_out hsep1.sepW hal2 hqa hwf2 hoff2 hw j hj (by omega)).trans
      (hout1 w fun j hj he => sepW_out hsep.sepW hal1 hpa hwf1 hoff1 hw j hj (by omega))
  have hlm := locMatch_setMem hm hsl hfr hM2 (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  have hspm : m.sp = E.sp := hm.frame.1
  refine ⟨_, mm', hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm, rfl, hk2,
    SepAt.write hk1 hsep1 hw2, rfl⟩
  obtain ⟨has, hf, -, ht', hsc⟩ := Shape.ok_eq hok
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
      .ok (a + p.off, none) := by
    rw [ht']
    simp only [fstpdSP48]
    rw [ctx_mem_sp hsc]
    exact congrArg (fun z => Except.ok (z, none)) (by simpa [hspm] using haeq)
  rw [progStep_fstpdAt hkx hky (nextAddr_pcAt F.nodup hk) has hf hma' hnil
    (by rw [haeq8]; exact hnil'), haeq8, hword kx, hword ky]

/-- **A float store off `SP`**: `FMOV{S,D} Fs, o(RSP)` stores the low bytes of a V register at
`⟨outargs act, o⟩` (`g44_fstore` with the base `SP`, `hsp`, in the separation of mode `w`). -/
theorem g48_spFStore (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) {mm : Mem} (hmm : s.mem = .mem mm) (hkn : KeysNodup mm)
    {w : Bool} (hsep : SepAt w E.ι (StkAt E) mm)
    (hregs : ∀ r v c, r ≠ zeroReg → s.regs[r]? = some v → K r = some c → Fits c v)
    (hR : KRead lc v K)
    (hsp : ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → ValRel E.ι x E.sp ∧ Fits 64 x)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {cs : Nat} {rs : Int} (hop : v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore)
    (hsz3 : v.args.size = 3) (haux : v.aux = none)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hso : fargObj lc v 1 = .ok (cs, rs)) (hma : memArg lc v 2 = .ok ())
    (hc : cs = 8 * fBytes v.op)
    (hvs : OneAt2 psA j
      ⟨plain (fmovAs cs) (· == regA rs) (spDst48 v), (fmovAs cs).name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m' mm', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ s' = { s with mem := .mem mm' } ∧ KeysNodup mm' ∧
      SepAt w E.ι (StkAt E) mm' ∧ m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> nofun
  obtain ⟨a1, r1, ha1, hah1, hfo1, hft1, hca1⟩ := fargObj_spec hso
  obtain ⟨ks, hks, rfl, hks'⟩ := fobjOf?_some hfo1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm0, hmm0, hMI⟩ := hm.mem
  rw [hmm] at hmm0
  cases hmm0
  have hinv : CoreInv E.ι (fun _ => False) K s :=
    ⟨hregs, mm, hmm, hkn, fun _ _ _ _ _ _ h => h.elim⟩
  have hr1 : r1 ≠ zeroReg := by have := (objV?_some hks').1; unfold zeroReg; omega
  obtain ⟨y, hy, hyv, hyf⟩ := arg_relV hl hm hinv hah1 hft1 hca1
    (kread_arg hR hnp ha1 hah1 hca1 hr1) hks'
  obtain ⟨x, y', p, mm', hx, hy', hsym, hw, rfl⟩ := stepLoc_fstore hl htemp hop
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hy] at hy'
  cases hy'
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
  have hword : ((m.v (BitVec.ofNat 5 ks)).setWidth 64).toNat % 2 ^ (8 * fBytes v.op) =
      (m.v (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * fBytes v.op) := by
    rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  obtain ⟨hxv, hxf⟩ := hsp a0 x ha0 hx
  have haddr : Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p := by
    rw [← hsym]; unfold symAddr; rw [haux]
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < fBytes v.op)
    (Or.inl hcan)
  obtain ⟨hM', hk', -, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hkn hn' hpa hyv' hyf hcs hw
  have hwf := wf_of_canWrite hcan (by omega)
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨hsl, hfr⟩ := stk_keeps hm hF hsz _ fun w hw =>
    hout w fun j hj he => sepW_out hsep.sepW hal hpa hwf hoff hw j hj (by omega)
  have hlm := locMatch_setMem hm hsl hfr hM' (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  have hspm : m.sp = E.sp := hm.frame.1
  refine ⟨_, mm', hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm, rfl, hk',
    SepAt.write hkn hsep hw, rfl⟩
  obtain ⟨has, hf, -, ht', hsc, -⟩ := plain_spec hok
  have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
      .ok (a + p.off, none) := by
    rw [beq_iff_eq.mp ht', ctx_mem_sp hsc]
    exact congrArg (fun z => Except.ok (z, none)) (by simpa [hspm] using haeq)
  rw [progStep_fstoreAt hks (nextAddr_pcAt F.nodup hk) (by rw [has]; exact hmov)
    (beq_iff_eq.mp hf) (by rw [beq_iff_eq.mp ht']; rfl) hma' hnil, hword]

/-- **A float load off `SP`**: `FMOV{S,D} o(RSP), Fd` loads `n` valid bytes (`hrd`, no pointer)
at `⟨outargs act, o⟩` into the result's V register (`g44_fload` with the base `SP`, `hsp`). -/
theorem g48_spFLoad (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) {mm : Mem} (hmm : s.mem = .mem mm) (hkn : KeysNodup mm)
    (hregs : ∀ r v c, r ≠ zeroReg → s.regs[r]? = some v → K r = some c → Fits c v)
    (hK : KNext lc v K K')
    (hsp : ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → ValRel E.ι x E.sp ∧ Fits 64 x)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : Nat} {rd : Int} (hop : v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload)
    (hrd : ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
      ∃ p bs, Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p ∧
        mm.read p (fBytes v.op) = some bs ∧
        ∀ q, (Arm64.loadN (lc.ty v.id) (fBytes v.op) false mm p).retypeL (lc.ty v.id) ≠ .ptr q)
    (hsz2 : v.args.size = 2) (haux : v.aux = none)
    (hma : memArg lc v 1 = .ok ()) (hro : fresObj lc v = .ok (c, rd)) (hc : c = 8 * fBytes v.op)
    (hvs : OneAt2 psA j
      ⟨plain (fmovAs c) (spDst48 v) (· == regA rd), (fmovAs c).name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ s'.mem = s.mem ∧ s'.slots = s.slots ∧
      (∀ r v c, r ≠ zeroReg → s'.regs[r]? = some v → K' r = some c → Fits c v) ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> nofun
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm0, hmm0, hMI⟩ := hm.mem
  rw [hmm] at hmm0
  cases hmm0
  have hinv : CoreInv E.ι (fun _ => False) K s :=
    ⟨hregs, mm, hmm, hkn, fun _ _ _ _ _ _ h => h.elim⟩
  obtain ⟨x, hx, rfl⟩ := stepLoc_fload hl htemp hop (arr2 hsz2 ha0 ha1)
    (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, bs, haddr, hrdp, hnpp⟩ := hrd a0 x ha0 hx
  have hsym : symAddr lc.ctx v x = some p := by unfold symAddr; rw [haux]; exact haddr
  rw [write_reg hvh hcv, hsym]
  simp only [Option.elim]
  subst hc
  have hn := fBytes_cases v.op
  have hn' : fBytes v.op = 1 ∨ fBytes v.op = 2 ∨ fBytes v.op = 4 ∨ fBytes v.op = 8 := by omega
  obtain ⟨hty, -⟩ := fTy_eq hft hcv
  have ht : lc.ty v.id ≠ .bool := by rw [hty]; nofun
  have hmov := fmovAs_movMem hn
  obtain ⟨hxv, hxf⟩ := hsp a0 x ha0 hx
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < fBytes v.op)
    (Or.inr (by rw [hrdp]; rfl))
  have hval : FValRel ((Arm64.loadN (lc.ty v.id) (fBytes v.op) false mm p).retypeL (lc.ty v.id))
      ((readMem m.mem (a + p.off) (fBytes v.op)).setWidth 128) := by
    have hv := valRel_retypeL_lo hA hcv ht
      ((lo_loadN hA hMI hn' (fun _ => rfl) ht hpa hrdp).mono (cls_le hcv))
    refine fvalRel_of_valRel hA hv hnpp (fun b' => by rw [hty]; exact retypeL_int_ne_bool _ b') ?_
    exact BitVec.setWidth_setWidth_of_le _ (by omega)
  have hzf := fits_retypeL hcv (Arm64.loadN (lc.ty v.id) (fBytes v.op) false mm p)
  have hspm : m.sp = E.sp := hm.frame.1
  obtain ⟨m', h1, h2, h3, h4⟩ := op_regV (H := H) F hm hinv hj hj' hvs hkd' hval hzf
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => by
      obtain ⟨has, hf, -, ht', hsc, -⟩ := plain_spec hok
      have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].from_ =
          .ok (a + p.off, none) := by
        rw [beq_iff_eq.mp hf, ctx_mem_sp hsc]
        exact congrArg (fun z => Except.ok (z, none)) (by simpa [hspm] using haeq)
      rw [progStep_floadAt hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov)
        (by rw [beq_iff_eq.mp hf]; rfl) hma' (beq_iff_eq.mp ht') hnil]
      rfl)
  exact ⟨m', h1, h2, rfl, rfl, h3.regs, h4⟩

end Cases

end GoFV.Proof.Gen
