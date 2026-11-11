import GoFV.Proof.Gen.Spec64
import GoFV.Proof.Gen.G63

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G64: 128-bit moves of blobs (`docs/plans/proofs3.md` §4)

`runLoc` runs `FMOVQload` as `Arm64.load16` (the 16 raw bytes at `symAddr`, a `blob`), `FLDPQ` as
two of them at `pairAddr` (`stepLoc_qload`, `stepLoc_qldp`), `FMOVQstore`/`FSTPQ` as the writes of
the blobs' bytes (`Arm64.storeBytes 16`; `stepLoc_qstore`, `stepLoc_qstp`). A V register holds a
blob bytewise (`VRel`'s `BlobRel`, as memory bytes are related, `ByteRel`):

* a load reads 16 valid bytes of a live block (the run premise `QLoadPre`, as G3's loads), each
  related to the machine byte at the injected address (`memInj_byteRel`), so the blob is related
  to the 128 bits `LDR Q`/`LDP Q` load there (`blobRel_load`, `progStep_floadAt`,
  `progStep_fldpqAt`);
* a store writes the bytes of the register's content read at the blob shape (`poison` or a
  16-byte blob, `retypeB_cases`), each related to the register's byte (`store16_rel`), which keeps
  `MemInj` with the machine's 16-byte write (`memInj_write16`, `progStep_fstoreAt`,
  `progStep_fstpqAt`), away from the frame's saved words and slots (`SepAt`);
* a select of an `FLDPQ` component reads its register at the blob shape: no code (`g64_qsel`).

The machine address of the operand (`OpAt`) and its relation to the Phase 1 address (`QBase`) come
from the operand's form (`qbase64`): G3's `off(Rn)` (`addr_rel`), a global's `sym+off(SB)`
(`symAddr_global`, `G2Env.glob`) or a frame variable's `off(<nc>)` (`varAt57`). None of these
writes an X register; the class table has no class for a blob (`kSet … none`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- **A 128-bit load reads valid bytes** (the run premise of slice G64, as G3's loads): an
`FMOVQload` reads 16 valid bytes at its address (`symAddr`), an `FLDPQ` 16 at each of its two
(`pairAddr`). -/
def QLoadPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  (v.op = .ARM64FMOVQload → ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
    ∃ p mm bs, symAddr lc.ctx v x = some p ∧ s.mem = .mem mm ∧ mm.read p 16 = some bs) ∧
  (v.op = .ARM64FLDPQ → ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
    ∃ p q mm bs bs', pairAddr lc.ctx v 16 x = some (p, q) ∧ s.mem = .mem mm ∧
      mm.read p 16 = some bs ∧ mm.read q 16 = some bs')

/-! ## `stepLoc` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_two64 {a b : ID} :
    [a, b].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => .ok [x, y] := rfl

private theorem mapM_three64 {a b c : ID} :
    [a, b, c].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        .ok [x, y, z] := rfl

private theorem mapM_four64 {a b c d : ID} :
    [a, b, c, d].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        (s.read lc d).bind fun w => .ok [x, y, z, w] := rfl

/-- `FMOVQload [off] {sym} a mem`: the 16 bytes at `symAddr` (`poison` if there is none). -/
theorem stepLoc_qload (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64FMOVQload) {a0 a1 : ID} (ha : v.args = #[a0, a1]) {mm : Mem}
    (hm : s.read lc a1 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id
        (((symAddr lc.ctx v x).elim .poison (Arm64.load16 mm)).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmap
  change [a0, a1].mapM (s.read lc) = _ at hmap
  rw [mapM_two64] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
    rw [hx, hm] at hmap; cases hmap
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
      have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
          .ok ((symAddr lc.ctx v x).elim .poison (Arm64.load16 mm)) := by
        unfold arm64Op; rw [hn, hop] <;> rfl
      rw [he] at hr; cases hr
      exact ⟨x, rfl, rfl⟩

/-- `FMOVQstore [off] {sym} a x mem`: the store of `x`'s 16 bytes at `symAddr`, which succeeded. -/
theorem stepLoc_qstore (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64FMOVQstore) {a0 a1 a2 : ID} (ha : v.args = #[a0, a1, a2]) {mm : Mem}
    (hm : s.read lc a2 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ symAddr lc.ctx v x = some p ∧
      mm.write p (Arm64.storeBytes 16 y) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmap
  change [a0, a1, a2].mapM (s.read lc) = _ at hmap
  rw [mapM_three64] at hmap
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
      unfold evalOpL; rw [hop]; rfl
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
          | some p => writeRes w (Arm64.storeN 16 p y mm)
          | none =>
            if [x, y, Val.mem mm].any (fun | .poison => true | _ => false) then .stuck m1
            else .stuck m2 := ⟨_, _, _, by unfold arm64Op; rw [hn, hop]; rfl⟩
      obtain ⟨w, m1, m2, he⟩ := he
      cases hp : symAddr lc.ctx v x with
      | none =>
        rw [hp] at he; rw [he] at hr
        dsimp only at hr
        split at hr <;> cases hr
      | some p =>
        rw [hp] at he; rw [he] at hr
        change writeRes _ (mm.write p (Arm64.storeBytes 16 y)) = _ at hr
        cases hw : mm.write p (Arm64.storeBytes 16 y) with
        | none => rw [hw] at hr; cases hr
        | some mm' =>
          rw [hw] at hr; cases hr
          exact ⟨x, y, p, mm', rfl, rfl, hp, hw, rfl⟩

/-- `FLDPQ [off] {sym} a mem`: the two 16-byte loads at `pairAddr` (`poison` if there is none). -/
theorem stepLoc_qldp (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64FLDPQ) {a0 a1 : ID} (ha : v.args = #[a0, a1]) {mm : Mem}
    (hm : s.read lc a1 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id
        (((pairAddr lc.ctx v 16 x).elim .poison fun pq =>
          Arm64.loadPair (lc.ty v.id) 16 false mm pq.1 pq.2).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmap
  change [a0, a1].mapM (s.read lc) = _ at hmap
  rw [mapM_two64] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
    rw [hx, hm] at hmap; cases hmap
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
      have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
          .ok ((pairAddr lc.ctx v 16 x).elim .poison fun pq =>
            Arm64.loadPair (lc.ty v.id) 16 false mm pq.1 pq.2) := by
        unfold arm64Op; rw [hn, hop] <;> rfl
      rw [he] at hr; cases hr
      exact ⟨x, rfl, rfl⟩

/-- `FSTPQ [off] {sym} a x y mem`: the 16-byte writes of `x` and `y` at `pairAddr`, in that
order, which succeeded. -/
theorem stepLoc_qstp (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64FSTPQ) {a0 a1 a2 a3 : ID} (ha : v.args = #[a0, a1, a2, a3])
    {mm : Mem} (hm : s.read lc a3 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y z p q mm1 mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ s.read lc a2 = .ok z ∧
      pairAddr lc.ctx v 16 x = some (p, q) ∧ mm.write p (Arm64.storeBytes 16 y) = some mm1 ∧
      mm1.write q (Arm64.storeBytes 16 z) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmap
  change [a0, a1, a2, a3].mapM (s.read lc) = _ at hmap
  rw [mapM_four64] at hmap
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
      cases hpq : pairAddr lc.ctx v 16 x with
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
            writeRes w (Arm64.storePair 16 p q y z mm) :=
          ⟨_, by unfold arm64Op; rw [hn, hop]; simp only [hpq]; rfl⟩
        obtain ⟨w, he⟩ := he
        rw [he] at hr
        cases hw1 : mm.write p (Arm64.storeBytes 16 y) with
        | none =>
          simp only [Arm64.storePair, hw1, Option.bind_none] at hr
          cases hr
        | some mm1 =>
          cases hw2 : mm1.write q (Arm64.storeBytes 16 z) with
          | none =>
            simp only [Arm64.storePair, hw1, hw2, Option.bind_some] at hr
            cases hr
          | some mm' =>
            simp only [Arm64.storePair, hw1, hw2, Option.bind_some] at hr
            cases hr
            exact ⟨x, y, z, p, q, mm1, mm', rfl, rfl, rfl, hpq, hw1, hw2, rfl⟩

end Step

/-! ## Blobs in registers -/

section Regs

variable {lc : LocCtx} {s : LocState}

/-- A blob homed in a register, read at its shape. -/
theorem read_regB {a r : Nat} (hl : lc.ctx.f.lowered = true) (hh : lc.home a = some (.reg r))
    (hty : lc.ty a = .blob 16) :
    s.read lc a = .ok ((s.reg (.blob 16) r).retypeL (.blob 16)) := by
  have hraw : s.raw lc a = .ok (s.reg (.blob 16) r) := by
    simp [LocState.raw, hh, hty]
  unfold LocState.read
  rw [hraw]; simp only [lmode_retype hl, hty]
  rfl

/-- Writing a blob with a register home: `setReg`. -/
theorem write_regB {r : Nat} {id : ID} {x : Val} (hh : lc.home id = some (.reg r))
    (hty : lc.ty id = .blob 16) : s.write lc id x = s.setReg r x := by
  simp [LocState.write, hh, hty]

/-- A pair of blobs written to a register pair home. -/
theorem write_pairB {id ra rb : Nat} {y0 y1 : Val}
    (hh : lc.home id = some (.pair (some ra) (some rb)))
    (hty : lc.ty id = .tuple [.blob 16, .blob 16]) :
    s.write lc id (.tuple [y0, y1]) = (s.setReg ra y0).setReg rb y1 := by
  simp [LocState.write, hh, hty, Location.regList, Val.partsOf, LocState.writeParts, Ty.isFlags]

/-- A pair of blobs homed in a register pair, read at its shape. -/
theorem read_pairB {c ra rb : Nat} (hl : lc.ctx.f.lowered = true)
    (hh : lc.home c = some (.pair (some ra) (some rb)))
    (hty : lc.ty c = .tuple [.blob 16, .blob 16]) :
    s.read lc c = .ok (.tuple [(s.reg (.blob 16) ra).retypeL (.blob 16),
      (s.reg (.blob 16) rb).retypeL (.blob 16)]) := by
  have hraw : s.raw lc c = .ok (.tuple [s.reg (.blob 16) ra, s.reg (.blob 16) rb]) := by
    simp [LocState.raw, hh, hty, Location.regList, LocState.readParts, Ty.isFlags]
  unfold LocState.read
  rw [hraw]; simp only [lmode_retype hl, hty]
  show Res.ok ((Val.tuple _).retypeL (.tuple _)) = _
  rw [retypeL_pair]

/-- A value read at the blob shape is `poison` or a 16-byte blob it already was. -/
theorem retypeB_cases (x : Val) : x.retypeL (.blob 16) = .poison ∨
    ∃ bs, x = .blob bs ∧ bs.length = 16 ∧ x.retypeL (.blob 16) = x := by
  cases x with
  | blob bs =>
    by_cases h : bs.length = 16
    · exact .inr ⟨bs, rfl, h, by simp [Val.retypeL, Val.widen, Val.retype, h]⟩
    · exact .inl (by simp [Val.retypeL, Val.widen, Val.retype, h])
  | _ => exact .inl (by first | rfl | simp [Val.retypeL, Val.widen, Val.retype])

/-- A 16-byte blob read at the blob shape. -/
theorem retypeB_blob {l : List Byte} (hl : l.length = 16) : (Val.blob l).retypeL (.blob 16) = .blob l := by
  simp [Val.retypeL, Val.widen, Val.retype, hl]

/-- Reading at the blob shape keeps `VRel`. -/
theorem vrel_retypeB {ι : Blk → Option (BitVec 64)} {x : Val} {q : BitVec 128}
    (h : VRel ι x q) : VRel ι (x.retypeL (.blob 16)) q := by
  rcases retypeB_cases x with h' | ⟨bs, rfl, -, h'⟩
  · rw [h']; trivial
  · rw [h']; exact h

/-- The 16 bytes a store writes of a register content read at the blob shape are related to the
register's bytes. -/
theorem store16_rel {ι : Blk → Option (BitVec 64)} {x : Val} {q : BitVec 128} (h : VRel ι x q)
    (hx : x = .poison ∨ ∃ bs, x = .blob bs ∧ bs.length = 16) :
    (Arm64.storeBytes 16 x).size = 16 ∧
      ∀ j, j < 16 → ByteRel ι (Arm64.storeBytes 16 x)[j]! (q.extractLsb' (8 * j) 8) := by
  rcases hx with rfl | ⟨bs, rfl, hl⟩
  · refine ⟨by simp [Arm64.storeBytes, Arm64.reg], fun j hj => ?_⟩
    simp [Arm64.storeBytes, Arm64.reg, hj, ByteRel]
  · have h' : BlobRel ι bs q := h
    unfold BlobRel at h'
    have hsb : Arm64.storeBytes 16 (.blob bs) = bs.toArray := by simp [Arm64.storeBytes, hl]
    refine ⟨by rw [hsb]; simp [hl], fun j hj => ?_⟩
    have hj' : j < bs.length := by omega
    rw [hsb, show bs.toArray[j]! = bs[j] by simp [hj']]
    exact h'.2 j hj'

/-- An argument homed in a V register at the blob shape: its read is related to the register and
is `poison` or a 16-byte blob. -/
theorem arg_relB {E : MatchEnv} {b : ID} {i : Nat} {m : MState} (hl : lc.ctx.f.lowered = true)
    (hm : LocMatch E s b i m) {a r : Nat} {k : GoFV.Arm64.Reg} (hh : lc.home a = some (.reg r))
    (hty : lc.ty a = .blob 16) (hk : objV? r = some k) :
    ∃ y, s.read lc a = .ok y ∧ VRel E.ι y (m.v k) ∧
      (y = .poison ∨ ∃ bs, y = .blob bs ∧ bs.length = 16) := by
  refine ⟨_, read_regB hl hh hty, ?_, ?_⟩
  · have hrz : r ≠ zeroReg := by have := (objV?_some hk).1; unfold zeroReg; omega
    apply vrel_retypeB
    simp only [LocState.reg, beq_iff_eq, hrz, ↓reduceIte]
    cases hv : s.regs[r]? with
    | none => simp only [Option.getD_none]; trivial
    | some c => simp only [Option.getD_some]; exact (hm.regs r c hv).2 k hk
  · rcases retypeB_cases (s.reg (.blob 16) r) with h | ⟨bs, h1, h2, h3⟩
    · exact .inl h
    · exact .inr ⟨bs, by rw [h3, h1], h2⟩

/-- A 16-byte load at the blob shape of valid bytes: the blob of the bytes. -/
theorem load16_blob {mm : Mem} {p : Ptr} {bs : Array Byte} (hr : mm.read p 16 = some bs)
    (hl : bs.toList.length = 16) : (Arm64.load16 mm p).retypeL (.blob 16) = .blob bs.toList := by
  unfold Arm64.load16
  rw [hr]
  exact retypeB_blob hl

/-- `FLDPQ` at the pair of blobs: the two 16-byte loads. -/
theorem loadPair16 {mm : Mem} {p q : Ptr} :
    Arm64.loadPair (.tuple [.blob 16, .blob 16]) 16 false mm p q =
      .tuple [Arm64.load16 mm p, Arm64.load16 mm q] := by
  simp [Arm64.loadPair, Arm64.loadElt, Arm64.tupleTy]

end Regs

/-! ## The class table -/

/-- Setting a register with no class keeps the invariant at the table without its class. -/
theorem core_setRegN {ι : Blk → Option (BitVec 64)} {P : BitVec 64 → Prop}
    {K : Nat → Option Nat} {s : LocState} {osp : Bool} (hinv : CoreInv ι P K s osp) {r : Nat}
    {x : Val} : CoreInv ι P (kSet K r none) (s.setReg r x) osp where
  mem := hinv.mem
  regs := by
    intro r' v c' hr' hv hcls
    simp only [LocState.setReg] at hv
    by_cases hrr : r' = r
    · subst hrr
      simp [kSet] at hcls
    · simp only [kSet, hrr, ↓reduceIte] at hcls
      split at hv
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hrr)] at hv
        exact hinv.regs r' v c' hr' hv hcls
      · exact hinv.regs r' v c' hr' hv hcls

/-- `KNext` across a value that writes its register home `r` with no class. -/
theorem knext_setN {lc : LocCtx} {v : Value} {K K' : Nat → Option Nat} (hK : KNext lc v K K')
    (hop : v.op ≠ .Phi) {r : Nat} (hh : lc.home v.id = some (.reg r))
    (hc : cls (lc.ty v.id) = none) : KLe K' (kSet K r none) := by
  intro r' c' hr' hc'
  have := hK r' c' hr' hc'
  by_cases hrr : r' = r
  · subst hrr
    simp [hop, hh, hc] at this
  · have hne : lc.home v.id ≠ some (.reg r') := by rw [hh]; simpa using Ne.symm hrr
    simp only [hne, and_false, ↓reduceIte] at this
    simp [kSet, hrr, this]

/-- The class table follows an `FLDPQ` into a register pair: no class for either register. -/
theorem kpairB_kStep {lc : LocCtx} {K : KMap} {v : Value} {ra rb : Nat} (hop : v.op ≠ .Phi)
    (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hty : lc.ty v.id = .tuple [.blob 16, .blob 16]) (hne : ra ≠ rb) :
    KLe (kStep lc K v).get (kSet (kSet K.get ra none) rb none) := by
  intro r c _ hc
  rw [kStep_get] at hc
  simp only [hop, ↓reduceIte, hh, hty, tupleTys, List.zip_cons_cons, List.zip_nil_right] at hc
  have hnd : ([(Ty.blob 16, some ra), (Ty.blob 16, some rb)].filterMap (·.2)).Nodup := by
    simp [hne]
  unfold kSet
  by_cases hrb : r = rb
  · subst hrb
    by_cases hsz : r < K.size
    · rw [kResults_get_of_mem (t := .blob 16) hnd (by simp) hsz] at hc; simp [GoFV.Gen.Check.cls] at hc
    · rw [KMap.get_ge (by rw [kResults_size]; omega)] at hc; cases hc
  · simp only [hrb, ↓reduceIte]
    by_cases hra : r = ra
    · subst hra
      by_cases hsz : r < K.size
      · rw [kResults_get_of_mem (t := .blob 16) hnd (by simp) hsz] at hc; simp [GoFV.Gen.Check.cls] at hc
      · rw [KMap.get_ge (by rw [kResults_size]; omega)] at hc; cases hc
    · simp only [hra, ↓reduceIte]
      rw [kResults_get_of_not_mem (by simp [hra, hrb])] at hc
      exact hc

/-! ## Memory -/

section Memory

variable {ι : Blk → Option (BitVec 64)}

theorem extract_setWidth128 (X : BitVec (8 * 16)) {i : Nat} (hi : i < 16) :
    (X.setWidth 128).extractLsb' (8 * i) 8 = X.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have : 8 * i + j < 128 := by omega
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hj, this]

theorem ofNat128 (q : BitVec 128) : BitVec.ofNat (8 * 16) (q.toNat % 2 ^ (8 * 16)) = q := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_mod, Nat.mod_eq_of_lt q.isLt]

/-- The 16 valid bytes of a live block at `p`, as a blob, are related to the 128 bits the machine
loads at the injected address. -/
theorem blobRel_load (hA : AddrAgree ι) {mm : Mem} {M : Memory} (h : MemInj ι mm M) {p : Ptr}
    {a : BitVec 64} {bs : Array Byte} (ha : ι p.blk = some a) (hr : mm.read p 16 = some bs) :
    VRel ι (.blob bs.toList) ((readMem M (a + p.off) 16).setWidth 128) := by
  obtain ⟨al, hfa, hsz, rfl⟩ := read_some53 (by decide) hr
  show BlobRel ι _ _
  unfold BlobRel
  refine ⟨by simp; omega, fun i hi => ?_⟩
  simp only [Array.length_toList, Array.size_extract] at hi
  have hi16 : i < 16 := by omega
  rw [extract_setWidth128 _ hi16, readMem_get M _ hi16, Array.getElem_toList,
    Array.getElem_extract, ← addr_off]
  exact memInj_byteRel hA h (find?_mem53 hfa) ha (by omega)

/-- A 16-byte write of bytes related to the bytes of `V` keeps `MemInj` with the machine's
`writeMem` of `V` (`memInj_storeN` at 16 bytes). -/
theorem memInj_write16 (hA : AddrAgree ι) {m m' : Mem} {mm : Memory} (h : MemInj ι m mm)
    (hk : KeysNodup m) {p : Ptr} {a : BitVec 64} {bsW : Array Byte} {V : BitVec (8 * 16)}
    (ha : ι p.blk = some a) (hsz : bsW.size = 16)
    (hbyte : ∀ j, j < 16 → ByteRel ι bsW[j]! (V.extractLsb' (8 * j) 8))
    (hw : m.write p bsW = some m') :
    MemInj ι m' (writeMem mm (a + p.off) 16 V) ∧ KeysNodup m' ∧
      (∀ b al2, (b, al2) ∈ m'.blocks → ∃ al1, (b, al1) ∈ m.blocks ∧ al1.data.size = al2.data.size) ∧
      ∃ al, (p.blk, al) ∈ m.blocks ∧ p.off.toNat + 16 ≤ al.data.size ∧
        ∀ y : BitVec 64, (∀ j, j < 16 → y.toNat ≠ a.toNat + p.off.toNat + j) →
          writeMem mm (a + p.off) 16 V y = mm y := by
  have hout : ∀ al, (p.blk, al) ∈ m.blocks → p.off.toNat + 16 ≤ al.data.size →
      ∀ y : BitVec 64, (∀ j, j < 16 → y.toNat ≠ a.toNat + p.off.toNat + j) →
        writeMem mm (a + p.off) 16 V y = mm y := by
    intro al hmem hoff y hy
    obtain ⟨a0, ha0, -, hhi⟩ := h.mapped _ _ hmem
    obtain rfl : a = a0 := Option.some.inj (ha.symm.trans ha0)
    apply writeMem_other
    intro j hj he
    apply hy j hj
    rw [he]; simp [BitVec.toNat_add]; omega
  obtain ⟨al, hmem, hoff⟩ := write_inside hw (by rw [hsz]; decide)
  rw [hsz] at hoff
  obtain ⟨h1, h2, h3, -⟩ := memInj_writeAny hA h hk (by decide : 0 < 16) ha hsz
    (fun j hj => by
      have he : (a + p.off + BitVec.ofNat 64 j - (a + p.off)).toNat = j := by
        bv_omega
      rw [writeMem_get 16 mm _ V _ (by decide), he, if_pos hj]
      exact hbyte j hj)
    (hout al hmem hoff) hw
  exact ⟨h1, h2, h3, al, hmem, hoff, hout al hmem hoff⟩

end Memory

/-! ## The machine -/

section Progs

private theorem eff_fldpq64 {c : ProgCtx} {ka kb : Nat} {A : BitVec 64} (hka : ka < 32)
    (hkb : kb < 32) (has : c.p.as = .FLDPQ) (hma : c.mem c.p.from_ = .ok (A, none))
    (ht : c.p.to = pairA (REG_F0 + ka) (REG_F0 + kb)) :
    progEffect c = .ok
      { v := [(kb, (readMem c.s.mem (A + BitVec.ofNat 64 16) 16).setWidth 128),
              (ka, (readMem c.s.mem A 16).setWidth 128)],
        loads := [(A + BitVec.ofNat 64 16, 16), (A, 16)] } := by
  have hname : As.name .FLDPQ = "FLDPQ" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wV_f0 hka, eff_wV_f0 hkb]
  rfl

private theorem eff_fstpq64 {c : ProgCtx} {ka kb : Nat} {A : BitVec 64} (hka : ka < 32)
    (hkb : kb < 32) (has : c.p.as = .FSTPQ)
    (hf : c.p.from_ = pairA (REG_F0 + ka) (REG_F0 + kb)) (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, 16, (c.s.v (BitVec.ofNat 5 ka)).toNat % 2 ^ (8 * 16)),
        (A + BitVec.ofNat 64 16, 16, (c.s.v (BitVec.ofNat 5 kb)).toNat % 2 ^ (8 * 16))] } := by
  have hname : As.name .FSTPQ = "FSTPQ" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_v_f0 hka, ctx_v_f0 hkb]
  rfl

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `FLDPQ` at the address `A` of its operand, both addresses outside the nil page: `V ka` from the
16 bytes at `A`, then `V kb` from the 16 bytes above. -/
theorem progStep_fldpqAt {ka kb : Nat} {A : BitVec 64} (hka : ka < 32) (hkb : kb < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .FLDPQ)
    (hma : (ProgCtx.mk L s p).mem p.from_ = .ok (A, none))
    (ht : p.to = pairA (REG_F0 + ka) (REG_F0 + kb)) (hnil : nilPage A = false)
    (hnil' : nilPage (A + BitVec.ofNat 64 16) = false) :
    progStep L p s = .ok { (s.wV (BitVec.ofNat 5 ka) ((readMem s.mem A 16).setWidth 128)).wV
        (BitVec.ofNat 5 kb) ((readMem s.mem (A + BitVec.ofNat 64 16) 16).setWidth 128) with
      pc := next } := by
  have he := eff_fldpq64 (c := ⟨L, s, p⟩) hka hkb has hma ht
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by simp [Eff.nilAccess?, List.find?, hnil, hnil'])]
  simp only [Eff.apply, List.foldr]
  rfl

/-- `FSTPQ (Fa, Fb)` at the address `A` of its operand, both addresses outside the nil page: the
16 bytes of `V ka` at `A`, then those of `V kb` 16 bytes above. -/
theorem progStep_fstpqAt {ka kb : Nat} {A : BitVec 64} (hka : ka < 32) (hkb : kb < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .FSTPQ)
    (hf : p.from_ = pairA (REG_F0 + ka) (REG_F0 + kb))
    (hma : (ProgCtx.mk L s p).mem p.to = .ok (A, none)) (hnil : nilPage A = false)
    (hnil' : nilPage (A + BitVec.ofNat 64 16) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem A 16
          (BitVec.ofNat (8 * 16) ((s.v (BitVec.ofNat 5 ka)).toNat % 2 ^ (8 * 16))))
        (A + BitVec.ofNat 64 16) 16
          (BitVec.ofNat (8 * 16) ((s.v (BitVec.ofNat 5 kb)).toNat % 2 ^ (8 * 16))),
      pc := next } := by
  have he := eff_fstpq64 (c := ⟨L, s, p⟩) hka hkb has hf hma
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by simp [Eff.nilAccess?, List.find?, hnil, hnil'])]
  rfl

end Progs

/-! ## The addresses -/

/-- The machine address `B` of every memory operand `P` accepts, in a state with `m`'s registers
(at any PC, no writeback). -/
def OpAt (L : Link) (m : MState) (P : Addr → Bool) (B : BitVec 64) : Prop :=
  ∀ (p : Prog) (pc : BitVec 64) (a : Addr), P a = true → p.scond = 0 →
    a.type = .MEM ∧ (ProgCtx.mk L { m with pc := pc } p).mem a = .ok (B, none)

/-- The machine address `B` of an access of `v` at the base value `x`: its Phase 1 address (and
the one 16 bytes above, `pairAddr`'s second), when valid, is in a block injected at `B` minus its
offset (and `B + 16`). -/
structure QBase (E : MatchEnv) (lc : LocCtx) (v : Value) (x : Val) (B : BitVec 64) : Prop where
  at0 : ∀ p (mm : Mem) (M : Memory), MemInj E.ι mm M → symAddr lc.ctx v x = some p →
    (mm.canWrite p 16 = true ∨ (mm.read p 16).isSome) → ∃ a, E.ι p.blk = some a ∧ B = a + p.off
  at16 : ∀ q (mm : Mem) (M : Memory), MemInj E.ι mm M →
    symAddr lc.ctx { v with auxInt := v.auxInt + Int64.ofNat 16 } x = some q →
    (mm.canWrite q 16 = true ∨ (mm.read q 16).isSome) →
    ∃ a, E.ι q.blk = some a ∧ B + BitVec.ofNat 64 16 = a + q.off

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- The operand forms of a 128-bit access (`qaccessA`): the machine address of the operand and its
relation to the Phase 1 address. -/
theorem qbase64 (F : Facts lc sym text az ez psA.toList ret E)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hvar : ∀ nc off, FVar57 lc g v nc off →
      ∃ bk, VarAt57 lc E (Link.byId sym text az ez psA.toList) v nc off bk)
    (hm : LocMatch E s b i m) {P : BitVec 64 → Prop} (hinv : CoreInv E.ι P K s osp)
    (hR : KRead lc v K) (hnp : v.op ≠ .Phi) {src : Addr → Bool}
    (hacc : qaccessA lc g v = .ok src) (hsrc : ∃ a', src a' = true) {a0 : ID}
    (ha0 : v.args[0]? = some a0) {x : Val} (hx : s.read lc a0 = .ok x) :
    ∃ B, QBase E lc v x B ∧ OpAt (Link.byId sym text az ez psA.toList) m src B := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨P', hP, hPs⟩ := qaccessA_spec hacc
  cases hP with
  | frame hfv =>
    rename_i nc off
    obtain ⟨bk, hB⟩ := hvar nc off hfv
    obtain ⟨a, hpa, haeq⟩ := hB.addr
    refine ⟨E.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off),
      ⟨fun p mm M _ hsym _ => ?_, fun q mm M _ hsym _ => ?_⟩, fun p pc a hPa hsc => ?_⟩
    · rw [hB.sym v x rfl] at hsym
      cases hsym
      exact ⟨a, hpa, haeq.symm⟩
    · rw [hB.sym { v with auxInt := v.auxInt + Int64.ofNat 16 } x rfl] at hsym
      cases hsym
      refine ⟨a, hpa, ?_⟩
      show _ = a + BitVec.ofInt 64 (v.auxInt + Int64.ofNat 16).toInt
      rw [ofInt_addN, ← haeq, BitVec.add_assoc]
    · have hs := hPs a hPa
      refine ⟨(slotA_eq hs).1, ?_⟩
      rw [ctx_mem_slot hs hB.cls]
      have hsp : m.sp = E.sp := hm.frame.1
      show Except.ok (m.sp + _, none) = _
      rw [hsp]
  | acc hP' =>
    cases hP' with
    | reg haux hao =>
      rename_i rn
      obtain ⟨a0', r0, ha0', hah0, hor0, hca0⟩ := argObj_spec hao
      rw [ha0] at ha0'
      cases ha0'
      obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
      obtain ⟨X, hX, hxv, hxf⟩ :=
        arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
      rw [hx] at hX
      cases hX
      refine ⟨m.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 v.auxInt.toInt,
        ⟨fun p mm M hMI hsym hval => ?_, fun q mm M hMI hsym hval => ?_⟩,
        fun p pc a hPa hsc => ?_⟩
      · have haddr : Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p := by
          rw [← hsym]; unfold symAddr; rw [haux]
        obtain ⟨a, hpa, haeq, -⟩ := addr_rel hA hMI hxv hxf haddr (by decide : 0 < 16) hval
        exact ⟨a, hpa, haeq⟩
      · have haddr : Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 16) =
            some q := by
          rw [← hsym, ← ofInt_addN]; unfold symAddr; simp only [haux]
        obtain ⟨a, hpa, haeq, -⟩ := addr_rel hA hMI hxv hxf haddr (by decide : 0 < 16) hval
        exact ⟨a, hpa, by rw [BitVec.add_assoc]; exact haeq⟩
      · have he : a = memA (REG_R0 + kn) v.auxInt.toInt := hPs a hPa
        subst he
        exact ⟨rfl, ctx_mem_reg hkn hsc⟩
    | glob hx' ha0' hsb hsy =>
      rename_i xa a0'' name abi
      obtain ⟨a', ha'⟩ := hsrc
      obtain ⟨-, -, -, -, -, y, -, hy⟩ := hPs a' ha'
      have hpa := hglob y name abi hy
      refine ⟨sym y + BitVec.ofInt 64 v.auxInt.toInt,
        ⟨fun p mm M _ hsym _ => ?_, fun q mm M _ hsym _ => ?_⟩, fun p pc a hPa hsc => ?_⟩
      · rw [symAddr_global hsy hx'] at hsym
        cases hsym
        exact ⟨_, hpa, rfl⟩
      · rw [symAddr_global (v := { v with auxInt := v.auxInt + Int64.ofNat 16 }) hsy hx'] at hsym
        cases hsym
        refine ⟨_, hpa, ?_⟩
        show _ = sym y + BitVec.ofInt 64 (v.auxInt + Int64.ofNat 16).toInt
        rw [ofInt_addN, BitVec.add_assoc]
      · obtain ⟨hf1, hf2, -, -, hf5, y', hy1, hy'⟩ := hPs a hPa
        have hyy : sym y' = sym y := Option.some.inj ((hglob y' name abi hy').symm.trans hpa)
        refine ⟨hf1, ?_⟩
        rw [ctx_mem_glob hf1 hf2 hf5 hy1]
        show Except.ok (sym y' + _, none) = _
        rw [hyy]

/-- A value whose one Prog writes its V register `V kd` with `q` holding a blob (no class). -/
theorem op_regVB {P : BitVec 64 → Prop} (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P K s osp)
    (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {pat : Pat} (hone : OneAt2 psA j pat j')
    {r kd : Nat} {x : Val} {q : BitVec 128} (hrk : objV? r = some (BitVec.ofNat 5 kd))
    (hx : VRel E.ι x q) (hKL : KLe K' (kSet K r none))
    (hstep : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m.wV (BitVec.ofNat 5 kd) q with pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E (s.setReg r x) b (i + 1) m' ∧ CoreInv E.ι P K' (s.setReg r x) osp ∧
      m'.x = m.x := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hone m
  rw [pc_eta hm hj] at hstar
  have hlm := locMatch_setRegVR hm hrk hx (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl (hstep k hk hok)), hlm,
    (core_setRegN hinv).mono hKL, rfl⟩

/-- `FMOVQ src, Fd`: the 16 bytes at the operand's address into `V kd`, a blob. -/
theorem g64_qload (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K') (hpre : QLoadPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rd : Int} {src : Addr → Bool} (hop : v.op = .ARM64FMOVQload) (hsz2 : v.args.size = 2)
    (hro : qresObj lc v = .ok rd) (hma : memArg lc v 1 = .ok ())
    (hbase : ∀ a0 x, v.args[0]? = some a0 → s.read lc a0 = .ok x →
      ∃ B, QBase E lc v x B ∧ OpAt (Link.byId sym text az ez psA.toList) m src B)
    (hvs : OneAt2 psA j ⟨plain .FMOVQ src (· == regA rd), "FMOVQ load"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨r, hvh, hfo, hty⟩ := qresObj_spec hro
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨x, hx, rfl⟩ := stepLoc_qload hl htemp hop (arr2 hsz2 ha0 ha1)
    (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, mm2, bs, hsym, hmm2, hrd⟩ := hpre.1 hop a0 x ha0 hx
  rw [hmm] at hmm2
  cases hmm2
  obtain ⟨B, hQB, hQO⟩ := hbase a0 x ha0 hx
  obtain ⟨a, hpa, hB⟩ := hQB.at0 p mm m.mem hMI hsym (Or.inr (by rw [hrd]; rfl))
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by decide : 0 < 16) (Or.inr (by rw [hrd]; rfl))
  have hrel := blobRel_load hA hMI hpa hrd
  have hlen : bs.toList.length = 16 := by
    have h' : BlobRel E.ι bs.toList _ := hrel
    exact h'.1
  rw [← hB] at hrel
  rw [write_regB hvh hty, hsym]
  simp only [Option.elim]
  rw [hty, load16_blob hrd hlen]
  refine (op_regVB (H := H) F hm hinv hj hj' hvs hkd' hrel
    (knext_setN hK hnp hvh (by rw [hty]; rfl)) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  obtain ⟨has, hf, -, ht, hsc, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at ht
  obtain ⟨hty', hma'⟩ := hQO _ _ _ hf hsc
  rw [progStep_floadAt hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; rfl) hty' hma' ht
    (by rw [hB]; exact hnil)] <;> rfl

/-- `FMOVQ Fs, dst`: the 16 bytes of `V ks` at the operand's address, outside the frame's saved
words and slots. -/
theorem g64_qstore (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rs : Int} {dst : Addr → Bool} (hop : v.op = .ARM64FMOVQstore) (hsz3 : v.args.size = 3)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hso : qargObj lc v 1 = .ok rs) (hma : memArg lc v 2 = .ok ())
    (hbase : ∀ a0 x, v.args[0]? = some a0 → s.read lc a0 = .ok x →
      ∃ B, QBase E lc v x B ∧ OpAt (Link.byId sym text az ez psA.toList) m dst B)
    (hvs : OneAt2 psA j ⟨plain .FMOVQ (· == regA rs) dst, "FMOVQ store"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨a1, r1, ha1, hah1, hfo1, hty1⟩ := qargObj_spec hso
  obtain ⟨ks, hks, rfl, hks'⟩ := fobjOf?_some hfo1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨y, hy, hyv, hyc⟩ := arg_relB hl hm hah1 hty1 hks'
  obtain ⟨x, y', p, mm', hx, hy', hsym, hw, rfl⟩ := stepLoc_qstore hl htemp hop
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hy] at hy'
  cases hy'
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨hbs, hbyte⟩ := store16_rel hyv hyc
  have hcan : mm.canWrite p 16 = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  obtain ⟨B, hQB, hQO⟩ := hbase a0 x ha0 hx
  obtain ⟨a, hpa, hB⟩ := hQB.at0 p mm m.mem hMI hsym (Or.inl hcan)
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by decide : 0 < 16) (Or.inl hcan)
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨hM', hk', -, al, hal, hoff, hout⟩ := memInj_write16 hA hMI hk0
    (V := BitVec.ofNat (8 * 16) ((m.v (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * 16))) hpa hbs
    (fun j hj => by rw [ofNat128]; exact hbyte j hj) hw
  have hsep' : SepAt osp E.ι (StkAt E) mm' := hsep0.write hk0 hw
  have hwf := write_wf hw (by rw [hbs]; omega)
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM' hk' hsep'
    (fun y hy => hout y fun j hj he => hsep0.not_mem hal hpa hy (by omega) (by omega))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k1 hk1 hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf1, -, ht1, hsc, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf1
  obtain ⟨hty', hma'⟩ := hQO _ _ _ ht1 hsc
  rw [progStep_fstoreAt hks (nextAddr_pcAt F.nodup hk1) (by rw [has]; rfl) hf1 hty' hma'
    (by rw [hB]; exact hnil), hB]

/-- `FLDPQ src, (Fa, Fb)`: the 16 bytes at the operand's address into `V ka`, the 16 above into
`V kb`, blobs. -/
theorem g64_qldp (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    {ra rb : Nat} (hK : KLe K' (kSet (kSet K ra none) rb none)) (hpre : QLoadPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {oa ob : Int} {src : Addr → Bool} (hop : v.op = .ARM64FLDPQ) (hsz2 : v.args.size = 2)
    (hty : lc.ty v.id = .tuple [.blob 16, .blob 16]) (hma : memArg lc v 1 = .ok ())
    (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hoa : fobjOf? ra = some oa) (hob : fobjOf? rb = some ob)
    (hbase : ∀ a0 x, v.args[0]? = some a0 → s.read lc a0 = .ok x →
      ∃ B, QBase E lc v x B ∧ OpAt (Link.byId sym text az ez psA.toList) m src B)
    (hvs : OneAt2 psA j ⟨plain .FLDPQ src (· == pairA oa ob), "FLDPQ"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ka, hka, rfl, hkka⟩ := fobjOf?_some hoa
  obtain ⟨kb, hkb, rfl, hkkb⟩ := fobjOf?_some hob
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨x, hx, rfl⟩ :=
    stepLoc_qldp hl htemp hop (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, q, mm2, bs, bs', hpq, hmm2, hrp, hrq⟩ := hpre.2 hop a0 x ha0 hx
  rw [hmm] at hmm2
  cases hmm2
  obtain ⟨hsp, hsq⟩ := pairAddr_eq_some hpq
  obtain ⟨B, hQB, hQO⟩ := hbase a0 x ha0 hx
  obtain ⟨a, hpa, hB⟩ := hQB.at0 p mm m.mem hMI hsp (Or.inr (by rw [hrp]; rfl))
  obtain ⟨a', hqa, hB'⟩ := hQB.at16 q mm m.mem hMI hsq (Or.inr (by rw [hrq]; rfl))
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by decide : 0 < 16) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨hnil', -⟩ := access_nil hMI hqa (by decide : 0 < 16) (Or.inr (by rw [hrq]; rfl))
  have hrel0 := blobRel_load hA hMI hpa hrp
  have hrel1 := blobRel_load hA hMI hqa hrq
  have hlen0 : bs.toList.length = 16 := by
    have h' : BlobRel E.ι bs.toList _ := hrel0
    exact h'.1
  have hlen1 : bs'.toList.length = 16 := by
    have h' : BlobRel E.ι bs'.toList _ := hrel1
    exact h'.1
  rw [← hB] at hrel0
  rw [← hB'] at hrel1
  rw [hpq]
  simp only [Option.elim]
  rw [hty, loadPair16, retypeL_pair, write_pairB hh hty, load16_blob hrp hlen0,
    load16_blob hrq hlen1]
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  have hlm1 := locMatch_setRegVR hm hkka hrel0 (b' := b) (i' := i + 1)
  have hlm2 := locMatch_setRegVR hlm1 hkkb hrel1 (b' := b) (i' := i + 1)
  rw [hj'] at hlm2
  have hinv2 := core_setRegN (r := rb) (x := Val.blob bs'.toList)
    (core_setRegN (r := ra) (x := Val.blob bs.toList) hinv)
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm2, hinv2.mono hK, hsi, rfl⟩
  obtain ⟨has, hf, -, ht, hsc, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at ht
  obtain ⟨hty', hma'⟩ := hQO _ _ _ hf hsc
  rw [progStep_fldpqAt hka hkb (nextAddr_pcAt F.nodup hk) has hma' ht (by rw [hB]; exact hnil)
    (by rw [hB']; exact hnil')]
  rfl

/-- `FSTPQ (Fx, Fy), dst`: the 16 bytes of `V kx` at the operand's address, those of `V ky` 16
above, outside the frame's saved words and slots. -/
theorem g64_qstp (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rx ry : Int} {dst : Addr → Bool} (hop : v.op = .ARM64FSTPQ) (hsz4 : v.args.size = 4)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hxo : qargObj lc v 1 = .ok rx) (hyo : qargObj lc v 2 = .ok ry)
    (hma : memArg lc v 3 = .ok ())
    (hbase : ∀ a0 x, v.args[0]? = some a0 → s.read lc a0 = .ok x →
      ∃ B, QBase E lc v x B ∧ OpAt (Link.byId sym text az ez psA.toList) m dst B)
    (hvs : OneAt2 psA j ⟨plain .FSTPQ (· == pairA rx ry) dst, "FSTPQ"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨a1, r1, ha1, hah1, hfo1, hty1⟩ := qargObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hfo2, hty2⟩ := qargObj_spec hyo
  obtain ⟨kx, hkx, rfl, hkx'⟩ := fobjOf?_some hfo1
  obtain ⟨ky, hky, rfl, hky'⟩ := fobjOf?_some hfo2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨Y, hY, hyv, hyc⟩ := arg_relB hl hm hah1 hty1 hkx'
  obtain ⟨Z, hZ, hzv, hzc⟩ := arg_relB hl hm hah2 hty2 hky'
  obtain ⟨x, y, z, p, q, mm1, mm', hx, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_qstp hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  obtain ⟨hsp, hsq⟩ := pairAddr_eq_some hpq
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨hby, hbyte1⟩ := store16_rel hyv hyc
  obtain ⟨hbz, hbyte2⟩ := store16_rel hzv hzc
  obtain ⟨B, hQB, hQO⟩ := hbase a0 x ha0 hx
  have hcan1 : mm.canWrite p 16 = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨a, hpa, hB⟩ := hQB.at0 p mm m.mem hMI hsp (Or.inl hcan1)
  obtain ⟨hnil, -⟩ := access_nil hMI hpa (by decide : 0 < 16) (Or.inl hcan1)
  obtain ⟨hM1, hk1, -, al1, hal1, hoff1, hout1⟩ := memInj_write16 hA hMI hk0
    (V := BitVec.ofNat (8 * 16) ((m.v (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 16))) hpa hby
    (fun j hj => by rw [ofNat128]; exact hbyte1 j hj) hw1
  have hcan2 : mm1.canWrite q 16 = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨a', hqa, hB'⟩ := hQB.at16 q mm1 _ hM1 hsq (Or.inl hcan2)
  obtain ⟨hnil', -⟩ := access_nil hM1 hqa (by decide : 0 < 16) (Or.inl hcan2)
  obtain ⟨hM2, hk2, -, al2, hal2, hoff2, hout2⟩ := memInj_write16 hA hM1 hk1
    (V := BitVec.ofNat (8 * 16) ((m.v (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 16))) hqa hbz
    (fun j hj => by rw [ofNat128]; exact hbyte2 j hj) hw2
  have hsep1 : SepAt osp E.ι (StkAt E) mm1 := hsep0.write hk0 hw1
  have hsep2 : SepAt osp E.ι (StkAt E) mm' := hsep1.write hk1 hw2
  have hwf1 := write_wf hw1 (by rw [hby]; omega)
  have hwf2 := write_wf hw2 (by rw [hbz]; omega)
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM2 hk2 hsep2
    (fun w hw => (hout2 w fun j hj he => hsep1.not_mem hal2 hqa hw (by omega) (by omega)).trans
      (hout1 w fun j hj he => hsep0.not_mem hal1 hpa hw (by omega) (by omega)))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf1, -, ht1, hsc, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf1
  obtain ⟨hty', hma'⟩ := hQO _ _ _ ht1 hsc
  rw [progStep_fstpqAt hkx hky (nextAddr_pcAt F.nodup hk) has hf1 hma' (by rw [hB]; exact hnil)
    (by rw [hB']; exact hnil'), hB', hB]

/-- A select of an `FLDPQ` component homed in its register: no code; the register read at the
blob shape keeps its relation. -/
theorem g64_qsel (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : ID} {ra rb r : Nat} (hop : v.op = .Select0 ∧ r = ra ∨ v.op = .Select1 ∧ r = rb)
    (hsz1 : v.args.size = 1) (hc0 : v.args[0]? = some c)
    (hpt : lc.ty c = .tuple [.blob 16, .blob 16])
    (hhc : lc.home c = some (.pair (some ra) (some rb))) (hvh : lc.home v.id = some (.reg r))
    (hfo : (fobjOf? r).isSome = true) (hbt : lc.ty v.id = .blob 16) (hvs : j' = j)
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  have hread := read_pairB (s := s) hl hhc hpt
  obtain ⟨i0, hop', hsel⟩ : ∃ i0, (v.op = .Select0 ∧ i0 = 0 ∨ v.op = .Select1 ∧ i0 = 1) ∧
      Tuple.select i0 [.tuple [(s.reg (.blob 16) ra).retypeL (.blob 16),
        (s.reg (.blob 16) rb).retypeL (.blob 16)]] = (s.reg (.blob 16) r).retypeL (.blob 16) := by
    rcases hop with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact ⟨0, .inl ⟨h, rfl⟩, rfl⟩
    · exact ⟨1, .inr ⟨h, rfl⟩, rfl⟩
  obtain ⟨x, hx, rfl⟩ := stepLoc_select hl htemp hop' (arr1 hsz1 hc0) hs
  rw [hread] at hx
  cases hx
  rw [hsel, write_regB hvh hbt, hbt]
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hfo
  obtain ⟨kd, -, rfl, hk⟩ := fobjOf?_some ho
  have hrz : r ≠ zeroReg := by have := (objV?_some hk).1; unfold zeroReg; omega
  have hrel : VRel E.ι (((s.reg (.blob 16) r).retypeL (.blob 16)).retypeL (.blob 16))
      (m.v (BitVec.ofNat 5 kd)) := by
    apply vrel_retypeB
    apply vrel_retypeB
    simp only [LocState.reg, beq_iff_eq, hrz, ↓reduceIte]
    cases hv : s.regs[r]? with
    | none => simp only [Option.getD_none]; trivial
    | some raw => simp only [Option.getD_some]; exact (hm.regs r raw hv).2 _ hk
  have hlm := locMatch_setRegVR hm hk hrel (b' := b) (i' := i + 1)
  have hpc : E.pcOf b (i + 1) = m.pc := by rw [hj', hvs, ← hj, hm.pc]
  rw [hpc, wV_self_pc] at hlm
  exact ⟨m, .refl, hlm, (core_setRegN hinv).mono
    (knext_setN hK hnp hvh (by rw [hbt]; rfl)), hsi⟩

end Cases

/-! ## The tables -/

/-- After a 128-bit move or a select of `FLDPQ` the upper-bit table is empty. -/
theorem uStep35_q64 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : v.op = .ARM64FMOVQload ∨ v.op = .ARM64FMOVQstore ∨ v.op = .ARM64FLDPQ ∨
      v.op = .ARM64FSTPQ) : uStep35 lc L v = [] := by
  rcases hop with h | h | h | h <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

/-- After a select of an `FLDPQ` the upper-bit table is empty. -/
theorem uStep35_qsel64 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v u : Value} {c : ID}
    (hop : v.op = .Select0 ∨ v.op = .Select1) (hc0 : v.args[0]? = some c)
    (hu : lc.ctx.f.value? c = some u) (huop : u.op = .ARM64FLDPQ) : uStep35 lc L v = [] := by
  rcases hop with hop | hop <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, huop, hop, hc0, hu]

end GoFV.Proof.Gen
