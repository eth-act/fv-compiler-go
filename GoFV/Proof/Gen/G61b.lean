import GoFV.Proof.Gen.G61a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G61, group A: the atomic add and the atomic and/or loops (`docs/plans/proofs3.md` §4)

The load-exclusive/store-exclusive loops of `LoweredAtomicAdd{64,32}` (`add`) and
`LoweredAtomic{And,Or}{64,32,8}` (`andL`, `orL`), from `runLoc`'s step (`stepLoc_rmw61`) to the
machine's run of their Progs, related by `atom_finish` (`G61V.lean`), as `g61_xchg` (`G61a.lean`):

* `add_run`/`g61_add`: `LDAXR (Rp), Rd` loads the location's old value, `ADD Rv, Rd` adds the
  operand, `STLXR Rd, (Rp), R27` stores the low `n` bytes of the sum and leaves `R27 = 0`, so the
  `CBNZ R27` falls through. `Atomic.step .add` stores and returns the `Int.add` of the old value and
  the fitted operand: both are related to the sum in `Rd` (`valRel_int2`, `BitVec.setWidth_add`);
* `logic_run`/`g61_logic`: `AND`/`ORR Rv, Rd, Rt` combines the old value in `Rd` with the operand
  into the temporary `Rt`, which the store-exclusive stores; `Atomic.step .andOld`/`.orOld` store
  the `Int.and`/`Int.or` (`logF61b`, against `binF (logAs61b f)`) and return the old value, left
  in `Rd` (`res_rel61`). The temporary is the one other register the loop writes (`atom_finish`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The and/or families -/

/-- The register op of the and/or loops (`AND` for `andL`, `ORR` for `orL`). -/
def logAs61b (f : AtomF61) : As :=
  match f with
  | .andL => .AND
  | _ => .ORR

/-- The bit op `Atomic.step` stores for the and/or loops. -/
def logF61b (f : AtomF61) {k : Nat} (a b : BitVec k) : BitVec k :=
  match f with
  | .andL => a &&& b
  | _ => a ||| b

theorem atomPats61_log61b {f : AtomF61} (hf : f = .andL ∨ f = .orL) (n : Nat)
    (rp rv rn rd rt : Int) :
    atomPats61 f n rp rv rn rd rt = [ldaxPat n rp rd,
      .ofShape { as := logAs61b f, from_ := regA rv, reg := rd, to := regA rt },
      stlxPat n rt rp, cbnzPat r27A] := by
  rcases hf with rfl | rfl <;> rfl

theorem atomTgt_log61b {f : AtomF61} (hf : f = .andL ∨ f = .orL) (ps : Array Prog) (j : Nat) :
    atomTgt f ps j = brTo ps j 4 1 := by
  rcases hf with rfl | rfl <;> rfl

theorem logPat_code61b {f : AtomF61} (hf : f = .andL ∨ f = .orL) {rv rd rt : Int} :
    (Pat.ofShape { as := logAs61b f, from_ := regA rv, reg := rd, to := regA rt }).Code :=
  fun _ h => by
    rcases hf with rfl | rfl <;> exact shape_noop (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nofun) h

theorem bin32_log61b {f : AtomF61} (hf : f = .andL ∨ f = .orL) :
    ∃ op, bin32? op = some (logAs61b f) := by
  rcases hf with rfl | rfl
  · exact ⟨.ARM64AND, rfl⟩
  · exact ⟨.ARM64OR, rfl⟩

theorem binF_log61b {f : AtomF61} (hf : f = .andL ∨ f = .orL) (k : Nat) (A B : BitVec 64) :
    (binF (logAs61b f) A B).setWidth k = logF61b f (A.setWidth k) (B.setWidth k) := by
  rcases hf with rfl | rfl
  · exact BitVec.setWidth_and ..
  · exact BitVec.setWidth_or ..

theorem step_log61b {f : AtomF61} (hf : f = .andL ∨ f = .orL) (w : Width) (old x : Val) :
    Atomic.step (kindF f) w old x =
      (int2 w (fun a b => .int w (logF61b f a b)) [old, x], some old) := by
  rcases hf with rfl | rfl <;> rfl

theorem step_add61b (w : Width) (old x : Val) :
    Atomic.step (kindF .add) w old x =
      (int2 w (fun a b => .int w (a + b)) [old, x], some (int2 w (fun a b => .int w (a + b)) [old, x])) :=
  (rfl)

/-! ## Stored values -/

private theorem fitPiece_int2_61b {w : Width} {g : BitVec w.bits → BitVec w.bits → BitVec w.bits}
    {x y : Val} :
    fitPiece (.int w) (int2 w (fun a b => .int w (g a b)) [x, y]) =
      int2 w (fun a b => .int w (g a b)) [x, y] := by
  simp only [int2]
  split <;> simp [fitPiece]

/-- The generic store's bytes of an `Int` op of the access's width are the `n`-byte store's. -/
theorem encode_int2_61b {w : Width} {g : BitVec w.bits → BitVec w.bits → BitVec w.bits}
    {x y : Val} :
    encode (.int w) (int2 w (fun a b => .int w (g a b)) [x, y]) =
      Arm64.storeBytes w.bytes (int2 w (fun a b => .int w (g a b)) [x, y]) := by
  rw [← encode_storeBytes (fits_int2 (g := g) (x := x) (y := y)), fitPiece_int2_61b]

private theorem storeBytes_size61b {n : Nat} (hn : n ≤ 8) (v : Val) :
    (Arm64.storeBytes n v).size = n := by
  unfold Arm64.storeBytes
  split
  · simp [ptrBytes]
  · split
    · next h => simpa using h
    · simp
  · split
    · simp [hn, intBytes]
    · simp

/-! ## Runs -/

section Runs

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64}

private theorem pstar_trans61b {L : Link} {ps : List Prog} {a b c : MState}
    (h1 : PStar H L ps ret a b) (h2 : PStar H L ps ret b c) : PStar H L ps ret a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact ih.tail hs

/-- The load-exclusive/store-exclusive loop of an atomic add: `LDAXR` loads the `n` bytes at `A`
into `X kd`, `ADD` adds `X kv` to it, `STLXR` stores the low `n` bytes of the sum there and sets
`X27 = 0`, and the `CBNZ R27` (to the `LDAXR`) falls through. -/
theorem add_run (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {n kp kv kd : Nat} (hn : n = 8 ∨ n = 4 ∨ n = 1) (hkp : kp < 31) (hkv : kv < 32)
    (hkd : kd < 31) (hpd : kp ≠ kd) (hvd : kv ≠ kd) {j j' : Nat}
    (hvs : ManyAt2 psA j (atomPats61 .add n (REG_R0 + kp) (REG_R0 + kv) (REG_R0 + kv)
      (REG_R0 + kd) 0) j')
    (htgt : atomTgt .add psA j = true) (m : MState) {A : BitVec 64}
    (hA : m.rX (BitVec.ofNat 5 kp) = A) (hnil : nilPage A = false) :
    PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
      { m with pc := pcAt text psA.toList j }
      { ((m.wX (BitVec.ofNat 5 kd) ((readMem m.mem A n).setWidth 64)).wX (BitVec.ofNat 5 kd)
          ((readMem m.mem A n).setWidth 64 + m.rX (BitVec.ofNat 5 kv))).wX (BitVec.ofNat 5 27) 0 with
        mem := writeMem m.mem A n (BitVec.ofNat (8 * n)
          (((readMem m.mem A n).setWidth 64 + m.rX (BitVec.ofNat 5 kv)).toNat % 2 ^ (8 * n))),
        pc := pcAt text psA.toList j' } := by
  simp only [atomPats61] at hvs
  obtain ⟨k1, h1, k2, h2, k3, h3, k4, h4, hj'⟩ := hvs
  simp only [ManyAt2] at hj'
  subst hj'
  -- the `CBNZ`'s target
  have e1 := oneAt2_next h1 ldaxPat_code
  have e2 := oneAt2_next h2 (fun _ hp => shape_noop (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nofun) hp)
  have e3 := oneAt2_next h3 stlxPat_code
  have e4 := oneAt2_next h4 (fun _ hp => cbnzPat_noop hp)
  simp only [atomTgt, brTo, nexts] at htgt
  rw [← e1, ← e2, ← e3, ← e4] at htgt
  obtain ⟨hk1, -⟩ : ∃ hk1 : k1 - 1 < psA.size, True := by
    obtain ⟨k, -, rfl, hk, -⟩ := h1; exact ⟨by omega, trivial⟩
  obtain ⟨hk4, -⟩ : ∃ hk4 : j' - 1 < psA.size, True := by
    obtain ⟨k, -, rfl, hk, -⟩ := h4; exact ⟨by omega, trivial⟩
  rw [Array.getElem?_eq_getElem hk4, Array.getElem?_eq_getElem hk1] at htgt
  simp only [beq_iff_eq] at htgt
  have hL : (Link.byId sym text az ez psA.toList).addr psA[k1 - 1].id =
      some (pcAt text psA.toList (k1 - 1)) := by
    have := addr_pcAt (sym := sym) (text := text) (az := az) (ez := ez) (ps := psA.toList)
      (j := k1 - 1) (by simpa using hk1)
    simpa using this
  -- `LDAXR`
  let old : BitVec 64 := (readMem m.mem A n).setWidth 64
  obtain ⟨k, hk1', hs1⟩ := step1 (H := H) hnd hlt hret h1 m
    (f := fun k => { m.wX (BitVec.ofNat 5 kd) old with pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [ldaxPat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, -⟩ := hok
      have hma : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].from_ =
          .ok (A, none) := by
        rw [hf, ctx_mem_reg (by omega) hsc]
        show Except.ok (m.rX (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0, none) = _
        rw [hA]; simp
      rw [progStep_ldaxr hn (by omega) (nextAddr_pcAt hnd hk) has hma ht hnil, wX_pc])
  rw [← hk1'] at hs1
  -- `ADD`
  let m1 : MState := m.wX (BitVec.ofNat 5 kd) old
  let V : BitVec 64 := old + m.rX (BitVec.ofNat 5 kv)
  let m2 : MState := m1.wX (BitVec.ofNat 5 kd) V
  obtain ⟨k', hk2', hs2⟩ := step1 (H := H) hnd hlt hret h2 m1
    (f := fun k => { m2 with pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, hr⟩, ht⟩, -⟩, -⟩, -⟩ := hok
      rw [progStep_addTo hkv (by omega) (nextAddr_pcAt hnd hk) has hf hr ht]
      have hd : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kd) =
          old := by
        show (m.wX (BitVec.ofNat 5 kd) old).rX (BitVec.ofNat 5 kd) = old
        exact rX_wX_self61 hkd old
      have hv : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kv) =
          m.rX (BitVec.ofNat 5 kv) := by
        show (m.wX (BitVec.ofNat 5 kd) old).rX (BitVec.ofNat 5 kv) = _
        exact rX_wX61 (by omega) (by omega) hvd old
      rw [hd, hv, wX_pc])
  rw [← hk2'] at hs2
  -- `STLXR`
  let M' : Memory := writeMem m.mem A n
    (BitVec.ofNat (8 * n) (V.toNat % 2 ^ (8 * n)))
  obtain ⟨k'', hk3', hs3⟩ := step1 (H := H) hnd hlt hret h3 m2
    (f := fun k => { m2.wX (BitVec.ofNat 5 27) 0 with mem := M', pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [stlxPat, Shape.okT, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, ht2⟩ := hok
      have hma : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m2 with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
          .ok (A, none) := by
        rw [ht, ctx_mem_reg (by omega) hsc]
        show Except.ok (((m.wX (BitVec.ofNat 5 kd) old).wX (BitVec.ofNat 5 kd) V).rX
          (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0, none) = _
        rw [rX_wX61 (by omega) (by omega) hpd, rX_wX61 (by omega) (by omega) hpd, hA]; simp
      rw [progStep_stlxr hn (by omega) (nextAddr_pcAt hnd hk) has hf hma ht2 hnil]
      have hv : ({ m2 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kd) = V := by
        show ((m.wX (BitVec.ofNat 5 kd) old).wX (BitVec.ofNat 5 kd) V).rX (BitVec.ofNat 5 kd) = V
        exact rX_wX_self61 hkd V
      rw [hv, wX_pc]
      simp only [M', m2, m1, mem_wX61])
  rw [← hk3'] at hs3
  -- `CBNZ R27`
  obtain ⟨k''', hk4', hs4⟩ := step1 (H := H) hnd hlt hret h4
    ({ m2.wX (BitVec.ofNat 5 27) 0 with mem := M' })
    (f := fun k => { m2.wX (BitVec.ofNat 5 27) 0 with mem := M', pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok hk4e => by
      have hkk : k = j' - 1 := by omega
      subst hkk
      have ht : psA.toList[j' - 1].to = brA psA[k1 - 1].id := by simpa using htgt
      rw [cbnz27_step hk hnd hok ht hL]
      show (m2.wX (BitVec.ofNat 5 27) 0).rX (BitVec.ofNat 5 27) = 0
      exact rX_wX_self61 (by omega) 0)
  rw [← hk4'] at hs4
  exact pstar_trans61b hs1 (pstar_trans61b hs2 (pstar_trans61b hs3 hs4))

/-- The load-exclusive/store-exclusive loop of an atomic and/or (`f = .andL ∨ f = .orL`):
`LDAXR` loads the `n` bytes at `A` into `X kd`, `AND`/`ORR` combines them with `X kv` into the
temporary `X kt`, `STLXR` stores the low `n` bytes of `X kt` there and sets `X27 = 0`, and the
`CBNZ R27` (to the `LDAXR`) falls through. -/
theorem logic_run (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {f : AtomF61} (hf : f = .andL ∨ f = .orL)
    {n kp kv kd kt : Nat} (hn : n = 8 ∨ n = 4 ∨ n = 1) (hkp : kp < 31) (hkv : kv < 32)
    (hkd : kd < 31) (hkt : kt < 31) (hpd : kp ≠ kd) (hvd : kv ≠ kd) (hpt : kp ≠ kt)
    {j j' : Nat}
    (hvs : ManyAt2 psA j (atomPats61 f n (REG_R0 + kp) (REG_R0 + kv) (REG_R0 + kv)
      (REG_R0 + kd) (REG_R0 + kt)) j')
    (htgt : atomTgt f psA j = true) (m : MState) {A : BitVec 64}
    (hA : m.rX (BitVec.ofNat 5 kp) = A) (hnil : nilPage A = false) :
    PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
      { m with pc := pcAt text psA.toList j }
      { ((m.wX (BitVec.ofNat 5 kd) ((readMem m.mem A n).setWidth 64)).wX (BitVec.ofNat 5 kt)
          (binF (logAs61b f) ((readMem m.mem A n).setWidth 64) (m.rX (BitVec.ofNat 5 kv)))).wX
            (BitVec.ofNat 5 27) 0 with
        mem := writeMem m.mem A n (BitVec.ofNat (8 * n)
          ((binF (logAs61b f) ((readMem m.mem A n).setWidth 64)
            (m.rX (BitVec.ofNat 5 kv))).toNat % 2 ^ (8 * n))),
        pc := pcAt text psA.toList j' } := by
  rw [atomPats61_log61b hf] at hvs
  obtain ⟨k1, h1, k2, h2, k3, h3, k4, h4, hj'⟩ := hvs
  simp only [ManyAt2] at hj'
  subst hj'
  -- the `CBNZ`'s target
  have e1 := oneAt2_next h1 ldaxPat_code
  have e2 := oneAt2_next h2 (logPat_code61b hf)
  have e3 := oneAt2_next h3 stlxPat_code
  have e4 := oneAt2_next h4 (fun _ hp => cbnzPat_noop hp)
  rw [atomTgt_log61b hf] at htgt
  simp only [brTo, nexts] at htgt
  rw [← e1, ← e2, ← e3, ← e4] at htgt
  obtain ⟨hk1, -⟩ : ∃ hk1 : k1 - 1 < psA.size, True := by
    obtain ⟨k, -, rfl, hk, -⟩ := h1; exact ⟨by omega, trivial⟩
  obtain ⟨hk4, -⟩ : ∃ hk4 : j' - 1 < psA.size, True := by
    obtain ⟨k, -, rfl, hk, -⟩ := h4; exact ⟨by omega, trivial⟩
  rw [Array.getElem?_eq_getElem hk4, Array.getElem?_eq_getElem hk1] at htgt
  simp only [beq_iff_eq] at htgt
  have hL : (Link.byId sym text az ez psA.toList).addr psA[k1 - 1].id =
      some (pcAt text psA.toList (k1 - 1)) := by
    have := addr_pcAt (sym := sym) (text := text) (az := az) (ez := ez) (ps := psA.toList)
      (j := k1 - 1) (by simpa using hk1)
    simpa using this
  obtain ⟨op, hop⟩ := bin32_log61b hf
  -- `LDAXR`
  let old : BitVec 64 := (readMem m.mem A n).setWidth 64
  obtain ⟨k, hk1', hs1⟩ := step1 (H := H) hnd hlt hret h1 m
    (f := fun k => { m.wX (BitVec.ofNat 5 kd) old with pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [ldaxPat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, -⟩ := hok
      have hma : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].from_ =
          .ok (A, none) := by
        rw [hf, ctx_mem_reg (by omega) hsc]
        show Except.ok (m.rX (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0, none) = _
        rw [hA]; simp
      rw [progStep_ldaxr hn (by omega) (nextAddr_pcAt hnd hk) has hma ht hnil, wX_pc])
  rw [← hk1'] at hs1
  -- `AND`/`ORR`
  let m1 : MState := m.wX (BitVec.ofNat 5 kd) old
  let V : BitVec 64 := binF (logAs61b f) old (m.rX (BitVec.ofNat 5 kv))
  let m2 : MState := m1.wX (BitVec.ofNat 5 kt) V
  obtain ⟨k', hk2', hs2⟩ := step1 (H := H) hnd hlt hret h2 m1
    (f := fun k => { m2 with pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, hr⟩, ht⟩, -⟩, -⟩, -⟩ := hok
      rw [progStep_bin32 hop (by omega) hkv (by omega) (nextAddr_pcAt hnd hk) has hf hr ht]
      have hd : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kd) =
          old := by
        show (m.wX (BitVec.ofNat 5 kd) old).rX (BitVec.ofNat 5 kd) = old
        exact rX_wX_self61 hkd old
      have hv : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kv) =
          m.rX (BitVec.ofNat 5 kv) := by
        show (m.wX (BitVec.ofNat 5 kd) old).rX (BitVec.ofNat 5 kv) = _
        exact rX_wX61 (by omega) (by omega) hvd old
      rw [hd, hv, wX_pc])
  rw [← hk2'] at hs2
  -- `STLXR`
  let M' : Memory := writeMem m.mem A n
    (BitVec.ofNat (8 * n) (V.toNat % 2 ^ (8 * n)))
  obtain ⟨k'', hk3', hs3⟩ := step1 (H := H) hnd hlt hret h3 m2
    (f := fun k => { m2.wX (BitVec.ofNat 5 27) 0 with mem := M', pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [stlxPat, Shape.okT, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, ht2⟩ := hok
      have hma : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m2 with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
          .ok (A, none) := by
        rw [ht, ctx_mem_reg (by omega) hsc]
        show Except.ok (((m.wX (BitVec.ofNat 5 kd) old).wX (BitVec.ofNat 5 kt) V).rX
          (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0, none) = _
        rw [rX_wX61 (by omega) (by omega) hpt, rX_wX61 (by omega) (by omega) hpd, hA]; simp
      rw [progStep_stlxr hn (by omega) (nextAddr_pcAt hnd hk) has hf hma ht2 hnil]
      have hv : ({ m2 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kt) = V := by
        show ((m.wX (BitVec.ofNat 5 kd) old).wX (BitVec.ofNat 5 kt) V).rX (BitVec.ofNat 5 kt) = V
        exact rX_wX_self61 hkt V
      rw [hv, wX_pc]
      simp only [M', m2, m1, mem_wX61])
  rw [← hk3'] at hs3
  -- `CBNZ R27`
  obtain ⟨k''', hk4', hs4⟩ := step1 (H := H) hnd hlt hret h4
    ({ m2.wX (BitVec.ofNat 5 27) 0 with mem := M' })
    (f := fun k => { m2.wX (BitVec.ofNat 5 27) 0 with mem := M', pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok hk4e => by
      have hkk : k = j' - 1 := by omega
      subst hkk
      have ht : psA.toList[j' - 1].to = brA psA[k1 - 1].id := by simpa using htgt
      rw [cbnz27_step hk hnd hok ht hL]
      show (m2.wX (BitVec.ofNat 5 27) 0).rX (BitVec.ofNat 5 27) = 0
      exact rX_wX_self61 (by omega) 0)
  rw [← hk4'] at hs4
  exact pstar_trans61b hs1 (pstar_trans61b hs2 (pstar_trans61b hs3 hs4))

end Runs

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K : Nat → Option Nat}

/-- `LoweredAtomicAdd{64,32} p x mem`: the loop loads the location's old value into `Rd`, adds
`x`, stores the sum and runs once; the sum is the result. -/
theorem g61_add (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {t0 : Ty} {rp rv rd : Int} {r : Nat}
    (hop : atom61? v.op = some (.add, n)) (hsz3 : v.args.size = 3)
    (hty : lc.ty v.id = .tuple [t0, .mem]) (hc0 : cls t0 = some (8 * n))
    (hap : argObj lc v 0 = .ok (64, rp)) (hpz : rp ≠ ARM64.REGZERO)
    (hav : argObj lc v 1 = .ok (8 * n, rv)) (hma : memArg lc v 2 = .ok ())
    (hh : lc.home v.id = some (.pair (some r) none)) (hrz : r ≠ zeroReg) (hd : destOK r = true)
    (hor : objOf? r = some rd) (hdp : rd ≠ rp) (hdv : rd ≠ rv)
    (htemp : (lc.temps[v.id]?).join = none)
    (hvs : ManyAt2 psA j (atomPats61 .add n rp rv rv rd 0) j')
    (htgt : atomTgt .add psA j = true) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kSet K r (some (8 * n))) s' osp ∧
      SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, -, -, -, -, -, -, -, hcf, -, -, -, hn, hwb, -⟩ := atom61?_facts hop
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hap
  obtain ⟨kp, hkp, rfl, hkkp⟩ := objOf?_some hor0
  have hkp31 := objOf?_lt31 hkp hkkp hpz
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hav
  obtain ⟨kv, hkv, rfl, hkkv⟩ := objOf?_some hor1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨kd, hkd, rfl, hkkd⟩ := objOf?_some hor
  obtain ⟨hkd31, hk27⟩ : kd < 31 ∧ kd ≠ 27 := by
    rcases hkkd with ⟨h, -⟩ | ⟨h, ho⟩
    · exact absurd h hrz
    · exact ⟨h, fun he => objX?_ne27 ho (by rw [he])⟩
  have hpd : kp ≠ kd := fun h => hdp (by rw [h])
  have hvd : kv ≠ kd := fun h => hdv (by rw [h])
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkp
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkv
  obtain ⟨x, y, p, mm', hx, hy, hpw, hal, hw, rfl⟩ := stepLoc_rmw61 hl hop nofun nofun
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hx] at hX; cases hX
  rw [hy] at hY; cases hY
  rw [step_add61b] at hw ⊢
  have hfy : Fits (widthN n).bits Y := by rw [widthN_bits hn]; exact hyf
  rw [encode_int2_61b, hwb] at hw
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [storeBytes_size61b (by omega)]; omega)
    rwa [storeBytes_size61b (by omega)] at this
  obtain ⟨a, hpa, haeq, hnil⟩ :=
    addr_rel hA hMI hxv hxf (addr_asPtrWord hpw) (by omega : 0 < n) (.inl hcan)
  have haeq' : m.rX (BitVec.ofNat 5 kp) = a + p.off := by simpa using haeq
  have hsz' : (Ty.int (widthN n)).size = n := by rcases hn with rfl | rfl | rfl <;> rfl
  rw [hsz'] at hal
  have hzv := valRel_int2 hA (g := fun a b => a + b)
    (old_rel61 hA hMI hn hpa hal (read_of_canWrite hcan (by omega))) (fit_asInt61 hA hyv hfy)
    (C := (readMem m.mem (a + p.off) n).setWidth 64 + m.rX (BitVec.ofNat 5 kv))
    (BitVec.setWidth_add _ _ (by rw [widthN_bits hn]; omega))
  have hzf : Fits (8 * n) (int2 (widthN n) (fun a b => .int (widthN n) (a + b))
      [mm.load (.int (widthN n)) p, fitPiece (.int (widthN n)) Y]) := by
    rw [← widthN_bits hn]; exact fits_int2
  obtain ⟨hM', hk', hsep', hP⟩ := atom_store61 hA hMI hk0 hsep0 hn hpa hzv hzf hw
  have hrun := add_run (H := H) F.nodup F.lt F.ret hn hkp31 hkv hkd31 hpd hvd hvs htgt m
    haeq' hnil
  rw [pc_eta hm hj] at hrun
  simp only [Atomic.result]
  rw [hty, retypeL_pair, retypeL_mem, write_atom61 hh hty (by rw [hc0]; rfl)]
  obtain ⟨hlm, hcore, hsl⟩ := atom_finish (m' := { ((m.wX (BitVec.ofNat 5 kd)
      ((readMem m.mem (a + p.off) n).setWidth 64)).wX (BitVec.ofNat 5 kd)
        ((readMem m.mem (a + p.off) n).setWidth 64 + m.rX (BitVec.ofNat 5 kv))).wX
          (BitVec.ofNat 5 27) 0 with
        mem := writeMem m.mem (a + p.off) n (BitVec.ofNat (8 * n)
          (((readMem m.mem (a + p.off) n).setWidth 64 + m.rX (BitVec.ofNat 5 kv)).toNat %
            2 ^ (8 * n))),
        pc := pcAt text psA.toList j' })
    hF hsz hm hinv hsi hkd hor hd hrz (fits_retypeL hc0 _)
    (by
      show ValRel E.ι _ ((((m.wX (BitVec.ofNat 5 kd) _).wX (BitVec.ofNat 5 kd) _).wX
        (BitVec.ofNat 5 27) 0).x _)
      rw [wX_x_ne (by omega) hkd hk27, wX_x_self54 hkd31]
      exact valRel_retypeL hA hc0 hzf hzv)
    hM' hk' hsep' hP (fun t ht => by rw [htemp] at ht; cases ht)
    (fun q h1 h2 _ => by
      show (((m.wX (BitVec.ofNat 5 kd) _).wX (BitVec.ofNat 5 kd) _).wX (BitVec.ofNat 5 27) 0).x q =
        m.x q
      rw [wX_x_of_ne h2, wX_x_of_ne h1, wX_x_of_ne h1])
    (by
      show (((m.wX _ _).wX _ _).wX _ _).v = m.v
      rw [wX_fields.2.2.2, wX_fields.2.2.2, wX_fields.2.2.2])
    (by
      show (((m.wX _ _).wX _ _).wX _ _).sp = m.sp
      rw [wX_fields.2.1, wX_fields.2.1, wX_fields.2.1])
    (fun _ => by
      show (((m.wX _ _).wX _ _).wX _ _).nzcv = m.nzcv
      rw [wX_fields.2.2.1, wX_fields.2.2.1, wX_fields.2.2.1])
    hj'.symm
  exact ⟨_, hrun, hlm, hcore, hsl⟩

/-- `LoweredAtomic{And,Or}{64,32,8} p x mem`: the loop loads the location's old value into `Rd`,
combines it with `x` in the temporary, stores that and runs once; the old value is the result. -/
theorem g61_logic (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {f : AtomF61} {n : Nat} {t0 : Ty} {rp rv rd rt : Int} {r t : Nat}
    (hop : atom61? v.op = some (f, n)) (hf : f = .andL ∨ f = .orL) (hsz3 : v.args.size = 3)
    (hty : lc.ty v.id = .tuple [t0, .mem]) (hc0 : cls t0 = some (8 * n))
    (hap : argObj lc v 0 = .ok (64, rp)) (hpz : rp ≠ ARM64.REGZERO)
    (hav : argObj lc v 1 = .ok (8 * n, rv)) (hma : memArg lc v 2 = .ok ())
    (hh : lc.home v.id = some (.pair (some r) none)) (hrz : r ≠ zeroReg) (hd : destOK r = true)
    (hor : objOf? r = some rd) (hdp : rd ≠ rp) (hdv : rd ≠ rv)
    (ht : (lc.temps[v.id]?).join = some t) (hto : objOf? t = some rt) (htz : t ≠ zeroReg)
    (htd : destOK t = true) (htp : rt ≠ rp) (htr : rt ≠ rd)
    (hvs : ManyAt2 psA j (atomPats61 f n rp rv rv rd rt) j')
    (htgt : atomTgt f psA j = true) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kSet K r (some (8 * n))) s' osp ∧
      SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, -, -, -, -, -, -, -, hcf, -, -, -, hn, hwb, -⟩ := atom61?_facts hop
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hap
  obtain ⟨kp, hkp, rfl, hkkp⟩ := objOf?_some hor0
  have hkp31 := objOf?_lt31 hkp hkkp hpz
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hav
  obtain ⟨kv, hkv, rfl, hkkv⟩ := objOf?_some hor1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨kd, hkd, rfl, hkkd⟩ := objOf?_some hor
  obtain ⟨hkd31, hk27⟩ : kd < 31 ∧ kd ≠ 27 := by
    rcases hkkd with ⟨h, -⟩ | ⟨h, ho⟩
    · exact absurd h hrz
    · exact ⟨h, fun he => objX?_ne27 ho (by rw [he])⟩
  obtain ⟨kt, hkt, rfl, -⟩ := objOf?_some hto
  obtain ⟨ht26, hkt27, hobjt⟩ : t < 26 ∧ kt < 27 ∧ objX? t = some (BitVec.ofNat 5 kt) := by
    rcases objOf?_dest hkt hto htd with ⟨h, -⟩ | h
    · exact absurd h htz
    · exact h
  have hpd : kp ≠ kd := fun h => hdp (by rw [h])
  have hvd : kv ≠ kd := fun h => hdv (by rw [h])
  have hpt : kp ≠ kt := fun h => htp (by rw [h])
  have hdt : kd ≠ kt := fun h => htr (by rw [h])
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkp
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkv
  obtain ⟨x, y, p, mm', hx, hy, hpw, hal, hw, rfl⟩ := stepLoc_rmw61 hl hop
    (by rcases hf with rfl | rfl <;> nofun) (by rcases hf with rfl | rfl <;> nofun)
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hx] at hX; cases hX
  rw [hy] at hY; cases hY
  rw [step_log61b hf] at hw ⊢
  have hfy : Fits (widthN n).bits Y := by rw [widthN_bits hn]; exact hyf
  rw [encode_int2_61b, hwb] at hw
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [storeBytes_size61b (by omega)]; omega)
    rwa [storeBytes_size61b (by omega)] at this
  obtain ⟨a, hpa, haeq, hnil⟩ :=
    addr_rel hA hMI hxv hxf (addr_asPtrWord hpw) (by omega : 0 < n) (.inl hcan)
  have haeq' : m.rX (BitVec.ofNat 5 kp) = a + p.off := by simpa using haeq
  have hsz' : (Ty.int (widthN n)).size = n := by rcases hn with rfl | rfl | rfl <;> rfl
  rw [hsz'] at hal
  have hzv := valRel_int2 hA (g := fun a b => logF61b f a b)
    (old_rel61 hA hMI hn hpa hal (read_of_canWrite hcan (by omega))) (fit_asInt61 hA hyv hfy)
    (C := binF (logAs61b f) ((readMem m.mem (a + p.off) n).setWidth 64) (m.rX (BitVec.ofNat 5 kv)))
    (binF_log61b hf _ _ _)
  have hzf : Fits (8 * n) (int2 (widthN n) (fun a b => .int (widthN n) (logF61b f a b))
      [mm.load (.int (widthN n)) p, fitPiece (.int (widthN n)) Y]) := by
    rw [← widthN_bits hn]; exact fits_int2
  obtain ⟨hM', hk', hsep', hP⟩ := atom_store61 hA hMI hk0 hsep0 hn hpa hzv hzf hw
  have hrun := logic_run (H := H) F.nodup F.lt F.ret hf hn hkp31 hkv hkd31 (by omega) hpd hvd
    hpt hvs htgt m haeq' hnil
  rw [pc_eta hm hj] at hrun
  have hold := res_rel61 hA hMI hn hc0 hpa hal (read_of_canWrite hcan (by omega))
  simp only [Atomic.result]
  rw [hty, retypeL_pair, retypeL_mem, write_atom61 hh hty (by rw [hc0]; rfl)]
  obtain ⟨hlm, hcore, hsl⟩ := atom_finish (m' := { ((m.wX (BitVec.ofNat 5 kd)
      ((readMem m.mem (a + p.off) n).setWidth 64)).wX (BitVec.ofNat 5 kt)
        (binF (logAs61b f) ((readMem m.mem (a + p.off) n).setWidth 64)
          (m.rX (BitVec.ofNat 5 kv)))).wX (BitVec.ofNat 5 27) 0 with
        mem := writeMem m.mem (a + p.off) n (BitVec.ofNat (8 * n)
          ((binF (logAs61b f) ((readMem m.mem (a + p.off) n).setWidth 64)
            (m.rX (BitVec.ofNat 5 kv))).toNat % 2 ^ (8 * n))),
        pc := pcAt text psA.toList j' })
    hF hsz hm hinv hsi hkd hor hd hrz (fits_retypeL hc0 _)
    (by
      show ValRel E.ι _ ((((m.wX (BitVec.ofNat 5 kd) _).wX (BitVec.ofNat 5 kt) _).wX
        (BitVec.ofNat 5 27) 0).x _)
      rw [wX_x_ne (by omega) hkd hk27, wX_x_ne (by omega) hkd hdt, wX_x_self54 hkd31]
      exact hold)
    hM' hk' hsep' hP (fun t' h => by rw [ht] at h; cases h; exact ht26)
    (fun q h1 h2 h3 => by
      have h4 : q ≠ BitVec.ofNat 5 kt := fun he => h3 t ht (by rw [hobjt, he])
      show (((m.wX (BitVec.ofNat 5 kd) _).wX (BitVec.ofNat 5 kt) _).wX (BitVec.ofNat 5 27) 0).x q =
        m.x q
      rw [wX_x_of_ne h2, wX_x_of_ne h4, wX_x_of_ne h1])
    (by
      show (((m.wX _ _).wX _ _).wX _ _).v = m.v
      rw [wX_fields.2.2.2, wX_fields.2.2.2, wX_fields.2.2.2])
    (by
      show (((m.wX _ _).wX _ _).wX _ _).sp = m.sp
      rw [wX_fields.2.1, wX_fields.2.1, wX_fields.2.1])
    (fun _ => by
      show (((m.wX _ _).wX _ _).wX _ _).nzcv = m.nzcv
      rw [wX_fields.2.2.1, wX_fields.2.2.1, wX_fields.2.2.1])
    hj'.symm
  exact ⟨_, hrun, hlm, hcore, hsl⟩

end Cases

end GoFV.Proof.Gen
