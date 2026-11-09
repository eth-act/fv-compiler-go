import GoFV.Proof.Gen.G12
import GoFV.Proof.Gen.Spec13

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G13: zeroing (`docs/plans/proofs3.md` §4)

`g13_value`, `g13_term`, `g13_nilPanic`: `g12_value`'s, `g12_term`'s and `g12_nilPanic`'s
statements over `checkG13`; `g13_value`'s per-value premise `G13Pre` adds to `G7Pre` that a
`LoweredZero` writes valid bytes (`ZeroPre`: Go zeroes memory it owns).

`LoweredZero [n] p mem` runs under `runLoc` as `Arm64.zero` (`stepLoc_zero`): `n` zero bytes
written at `p`'s address (`Mem.write`), `poison` when the write is invalid, which `ZeroPre`
excludes. Genssa emits `zeroTail`'s stores: an `STP (ZR, ZR)` of 16 bytes per 16, then
`MOVD ZR` stores of 8, the last one overlapping (`zeroOffs`); `checkG13` checks that they lie
inside the `n` bytes and cover them. The machine runs them in order (`zero_run`): the bytes a
store covers are 0 (`zeroMem_cov`), the others unchanged (`zeroMem_out`). So the bytes at the
write's injected address are the zeros `runLoc` wrote and every other byte is the old one, which
keeps `MemInj` (`memInj_writeAny`); the zeroed bytes lie inside a live block, away from the frame
(`SepFrom`), so the saved words and the spill slots keep their bytes.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## `stepLoc` of `LoweredZero` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `LoweredZero [n] p mem` writes `Arm64.zero` of its arguments (the memory after the zeroing,
or `poison`) as the memory. -/
theorem stepLoc_zero (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64LoweredZero) {a mem : ID} (ha : v.args = #[a, mem]) {mm : Mem}
    (hmem : s.read lc mem = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a = .ok x ∧
      s' = s.write lc v.id ((Arm64.zero v.auxInt [x, .mem mm]).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmv
  change ((s.read lc a).bind fun x => (s.read lc mem).bind fun y => .ok [x, y]) = .ok argv at hmv
  cases hx : s.read lc a with
  | panic e m0 => rw [hx] at hmv; cases hmv
  | stuck msg => rw [hx] at hmv; cases hmv
  | ok x =>
    rw [hx, hmem] at hmv
    cases hmv
    refine ⟨x, rfl, ?_⟩
    cases hnf : nilFaults true lc.ctx v [x, .mem mm] with
    | some m0 =>
      have he : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) = .panic .nilDeref m0 := by
        unfold evalOpL arm64Op
        simp only [hop, hnf]
        rfl
      rw [he] at hr
      cases hr
    | none =>
      have he : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
          .ok (Arm64.zero v.auxInt [x, .mem mm]) := by
        unfold evalOpL arm64Op
        simp only [hop, hnf]
        rfl
      rw [he] at hr
      cases hr
      rfl

end Step

/-! ## The machine's zeroing stores -/

/-- The machine memory after one zeroing store off `A`: 16 zero bytes at `A + off` for an
`STP (ZR, ZR)`, 8 for an `MOVD ZR`. -/
def zeroStore (A : BitVec 64) (M : Memory) (st : Bool × Nat) : Memory :=
  if st.1 then
    writeMem (writeMem M (A + BitVec.ofNat 64 st.2) 8 0) (A + BitVec.ofNat 64 st.2 + 8) 8 0
  else writeMem M (A + BitVec.ofNat 64 st.2) 8 0

/-- The machine memory after the zeroing stores `offs` off `A`, in order. -/
def zeroMem (A : BitVec 64) (M : Memory) (offs : List (Bool × Nat)) : Memory :=
  offs.foldl (zeroStore A) M

/-- The store `st` off `A` covers the address `y`. -/
def Covers (A : BitVec 64) (st : Bool × Nat) (y : BitVec 64) : Prop :=
  A.toNat + st.2 ≤ y.toNat ∧ y.toNat < A.toNat + st.2 + zeroW st.1

/-- An 8-byte store of 0 that does not wrap: 0 in its bytes, the old byte elsewhere. -/
theorem writeMem_zero8_in {M : Memory} {a y : BitVec 64} (ha : a.toNat + 8 ≤ 2 ^ 64)
    (hy : a.toNat ≤ y.toNat ∧ y.toNat < a.toNat + 8) : writeMem M a 8 0 y = 0 := by
  have hy' : y = a + BitVec.ofNat 64 (y.toNat - a.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [hy', writeMem_at 8 M a 0 _ (by omega) (Nat.le_refl _)]
  simp

theorem writeMem_zero8_out {M : Memory} {a y : BitVec 64} (ha : a.toNat + 8 ≤ 2 ^ 64)
    (hy : ¬ (a.toNat ≤ y.toNat ∧ y.toNat < a.toNat + 8)) : writeMem M a 8 0 y = M y := by
  apply writeMem_other
  intro j hj he
  apply hy
  rw [he]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem toNat_addOf {A : BitVec 64} {o : Nat} (h : A.toNat + o < 2 ^ 64) :
    (A + BitVec.ofNat 64 o).toNat = A.toNat + o := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem toNat_addOf8 {A : BitVec 64} {o : Nat} (h : A.toNat + o + 8 < 2 ^ 64) :
    (A + BitVec.ofNat 64 o + 8).toNat = A.toNat + o + 8 := by
  have h1 := toNat_addOf (A := A) (o := o) (by omega)
  rw [BitVec.toNat_add, h1, show (8 : BitVec 64).toNat = 8 from rfl]
  omega

/-- A store that covers `y` makes it 0. -/
theorem zeroStore_cov {A : BitVec 64} {M : Memory} {st : Bool × Nat} {y : BitVec 64}
    (hst : A.toNat + st.2 + zeroW st.1 ≤ 2 ^ 64) (hc : Covers A st y) : zeroStore A M st y = 0 := by
  obtain ⟨pr, o⟩ := st
  unfold Covers at hc
  unfold zeroStore
  cases pr with
  | true =>
    simp only [zeroW, ↓reduceIte] at hst hc ⊢
    have h1 := toNat_addOf (A := A) (o := o) (by omega)
    have h2 := toNat_addOf8 (A := A) (o := o) (by omega)
    by_cases hy : (A + BitVec.ofNat 64 o + 8).toNat ≤ y.toNat ∧
        y.toNat < (A + BitVec.ofNat 64 o + 8).toNat + 8
    · exact writeMem_zero8_in (by omega) hy
    · rw [writeMem_zero8_out (by omega) hy]
      exact writeMem_zero8_in (by omega) (by omega)
  | false =>
    simp only [zeroW, Bool.false_eq_true, ↓reduceIte] at hst hc ⊢
    have h1 := toNat_addOf (A := A) (o := o) (by omega)
    exact writeMem_zero8_in (by omega) (by omega)

/-- A store that does not cover `y` keeps it. -/
theorem zeroStore_out {A : BitVec 64} {M : Memory} {st : Bool × Nat} {y : BitVec 64}
    (hst : A.toNat + st.2 + zeroW st.1 ≤ 2 ^ 64) (hc : ¬ Covers A st y) :
    zeroStore A M st y = M y := by
  obtain ⟨pr, o⟩ := st
  unfold Covers at hc
  unfold zeroStore
  cases pr with
  | true =>
    simp only [zeroW, ↓reduceIte] at hst hc ⊢
    have h1 := toNat_addOf (A := A) (o := o) (by omega)
    have h2 := toNat_addOf8 (A := A) (o := o) (by omega)
    rw [writeMem_zero8_out (by omega) (by omega), writeMem_zero8_out (by omega) (by omega)]
  | false =>
    simp only [zeroW, Bool.false_eq_true, ↓reduceIte] at hst hc ⊢
    have h1 := toNat_addOf (A := A) (o := o) (by omega)
    exact writeMem_zero8_out (by omega) (by omega)

/-- Stores that do not cover `y` keep it. -/
theorem zeroMem_out {A : BitVec 64} {y : BitVec 64} : ∀ (offs : List (Bool × Nat)) (M : Memory),
    (∀ st ∈ offs, A.toNat + st.2 + zeroW st.1 ≤ 2 ^ 64) → (∀ st ∈ offs, ¬ Covers A st y) →
      zeroMem A M offs y = M y
  | [], _, _, _ => rfl
  | st :: rest, M, hb, hc => by
    have ih := zeroMem_out rest (zeroStore A M st) (fun st' h' => hb st' (List.mem_cons_of_mem _ h'))
      (fun st' h' => hc st' (List.mem_cons_of_mem _ h'))
    unfold zeroMem at ih ⊢
    rw [List.foldl_cons, ih]
    exact zeroStore_out (hb st List.mem_cons_self) (hc st List.mem_cons_self)

/-- A store that covers `y` makes it 0, whatever the later ones do. -/
theorem zeroMem_cov {A : BitVec 64} {y : BitVec 64} : ∀ (offs : List (Bool × Nat)) (M : Memory),
    (∀ st ∈ offs, A.toNat + st.2 + zeroW st.1 ≤ 2 ^ 64) → (∃ st ∈ offs, Covers A st y) →
      zeroMem A M offs y = 0
  | [], _, _, h => by obtain ⟨_, h, _⟩ := h; cases h
  | st :: rest, M, hb, hc => by
    have hb' : ∀ st' ∈ rest, A.toNat + st'.2 + zeroW st'.1 ≤ 2 ^ 64 :=
      fun st' h' => hb st' (List.mem_cons_of_mem _ h')
    unfold zeroMem
    rw [List.foldl_cons]
    by_cases hr : ∃ st' ∈ rest, Covers A st' y
    · exact zeroMem_cov rest _ hb' hr
    · have hst : Covers A st y := by
        obtain ⟨st', h', hc'⟩ := hc
        rcases List.mem_cons.1 h' with rfl | h'
        · exact hc'
        · exact absurd ⟨st', h', hc'⟩ hr
      have := zeroMem_out (A := A) (y := y) rest (zeroStore A M st) hb'
        (fun st' h' hc' => hr ⟨st', h', hc'⟩)
      unfold zeroMem at this
      rw [this]
      exact zeroStore_cov (hb st List.mem_cons_self) hst

section Run

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64}

/-- One zeroing store, `STP (ZR, ZR), off(Rn)` or `MOVD ZR, off(Rn)`, with `Rn` holding `A`. -/
theorem progStep_zero {kn : Nat} (hkn : kn < 32) {p : Prog} {st : Bool × Nat} {m : MState}
    {next A : BitVec 64} (hok : (zeroPat (ARM64.REG_R0 + kn) st).ok p = true)
    (hn : (Link.byId sym text az ez psA.toList).nextAddr p.id = some next)
    (hA : m.rX (BitVec.ofNat 5 kn) = A) (hnil : nilPage (A + BitVec.ofNat 64 st.2) = false)
    (hnil8 : st.1 = true → nilPage (A + BitVec.ofNat 64 st.2 + 8) = false) :
    progStep (Link.byId sym text az ez psA.toList) p m =
      .ok { m with mem := zeroStore A m.mem st, pc := next } := by
  obtain ⟨pr, o⟩ := st
  have hoff : BitVec.ofInt 64 ((o : Nat) : Int) = BitVec.ofNat 64 o := by
    apply BitVec.eq_of_toNat_eq; simp
  have h0 : (BitVec.ofNat (8 * 8) ((m.rX (BitVec.ofNat 5 31)).toNat % 2 ^ (8 * 8)) : BitVec 64) =
      0 := by rw [rX_31]; rfl
  cases pr with
  | true =>
    simp only [zeroPat, ↓reduceIte] at hok
    obtain ⟨has, hf, -, ht, hsc⟩ := Shape.ok_eq hok
    rw [progStep_stp hkn (kx := 31) (ky := 31) (by omega) (by omega) hn has hf hsc ht
      (by rw [hA, hoff]; exact hnil) (by rw [hA, hoff]; exact hnil8 rfl), hA, hoff, h0]
    rfl
  | false =>
    simp only [zeroPat, Bool.false_eq_true, ↓reduceIte] at hok
    obtain ⟨has, hf, -, ht, hsc⟩ := Shape.ok_eq hok
    rw [progStep_store hkn (ks := 31) (by omega) hn has hf hsc ht (by rw [hA, hoff]; exact hnil),
      hA, hoff, h0]
    rfl

/-- The zeroing stores `offs` off `Rn`, which holds `A`, from index `j` to `j'`. -/
theorem zero_run (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {kn : Nat} (hkn : kn < 32) {A : BitVec 64} :
    ∀ (offs : List (Bool × Nat)) (j j' : Nat) (m : MState),
      ManyAt2 psA j (offs.map (zeroPat (ARM64.REG_R0 + kn))) j' →
      (∀ st ∈ offs, nilPage (A + BitVec.ofNat 64 st.2) = false ∧
        (st.1 = true → nilPage (A + BitVec.ofNat 64 st.2 + 8) = false)) →
      m.rX (BitVec.ofNat 5 kn) = A →
      PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j }
        { m with mem := zeroMem A m.mem offs, pc := pcAt text psA.toList j' }
  | [], j, j', m, h, _, _ => by
    simp only [List.map_nil, ManyAt2] at h
    subst h
    exact .refl
  | st :: rest, j, j', m, h, hnil, hA => by
    obtain ⟨k, hone, hmany⟩ := h
    obtain ⟨k0, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) hnd hlt hret hone m
    have hstep := progStep_zero (sym := sym) (text := text) (az := az) (ez := ez)
      (m := { m with pc := pcAt text psA.toList k0 }) hkn hok
      (nextAddr_pcAt hnd hk) hA (hnil st List.mem_cons_self).1 (hnil st List.mem_cons_self).2
    have hrest := zero_run hnd hlt hret hkn rest (k0 + 1) j'
      { m with mem := zeroStore A m.mem st } hmany
      (fun st' h' => hnil st' (List.mem_cons_of_mem _ h')) hA
    exact (hstar.tail (pstep_at hnd hlt hret hk rfl hstep)).trans hrest

end Run

/-! ## The value -/

/-- The per-value premise of `LoweredZero`: the `n` zero bytes are written at a valid address
(Go zeroes memory it owns). -/
def ZeroPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  v.op = .ARM64LoweredZero → ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
    ∃ p mm mm', Arm64.addr x 0 = some p ∧ s.mem = .mem mm ∧
      mm.write p (Array.replicate v.auxInt.toInt.toNat (.b 0)) = some mm'

/-- The per-value premises of G13: G7's, and `ZeroPre`. -/
def G13Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop := G7Pre lc s v ∧ ZeroPre lc s v

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `LoweredZero [n] p mem`: `zeroTail`'s stores zero the `n` bytes at `p`'s injected address,
inside a live block and away from the frame. -/
theorem g13_zero (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rp : Int} (hop : v.op = .ARM64LoweredZero) (hsz2 : v.args.size = 2)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hao : argObj lc v 0 = .ok (64, rp)) (hma : memArg lc v 1 = .ok ())
    (h16 : 16 ≤ v.auxInt.toInt)
    (hcov : zeroCovers v.auxInt.toInt.toNat (zeroOffs v.auxInt.toInt.toNat) = true)
    (hvs : ManyAt2 psA j ((zeroOffs v.auxInt.toInt.toNat).map (zeroPat rp)) j')
    (hpre : ZeroPre lc s v)
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨xv, hxr, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨x, hx, rfl⟩ :=
    stepLoc_zero hl htemp hop (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  rw [hxr] at hx
  cases hx
  obtain ⟨p, mm1, mm', hp, hmm1, hw⟩ := hpre hop a0 xv ha0 hxr
  rw [hmm] at hmm1
  cases hmm1
  have hz : Arm64.zero v.auxInt [xv, .mem mm] = .mem mm' := by
    simp only [Arm64.zero, hp, hw]
  rw [hz, write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  generalize hn : v.auxInt.toInt.toNat = n at hcov hvs hw
  have hn16 : 16 ≤ n := by omega
  have hbs : (Array.replicate n (Byte.b 0)).size = n := Array.size_replicate
  obtain ⟨al, hal, hoff⟩ := write_inside hw (by rw [hbs]; omega)
  rw [hbs] at hoff
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  obtain ⟨a, hpa, haeq, -⟩ := addr_rel hA hMI hxv hxf hp (by omega : 0 < n) (Or.inl hcan)
  obtain ⟨a', ha', hlo, hhi⟩ := hMI.mapped _ _ hal
  obtain rfl : a = a' := Option.some.inj (hpa.symm.trans ha')
  have h4 := hlo (by omega)
  have hAt : (a + p.off).toNat = a.toNat + p.off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hX : m.rX (BitVec.ofNat 5 kn) = a + p.off := by simpa using haeq
  obtain ⟨hin, hcovd⟩ := zeroCovers_spec hcov
  have hw8 : ∀ pr : Bool, 8 ≤ zeroW pr := fun pr => by unfold zeroW; split <;> omega
  have hbnd : ∀ st ∈ zeroOffs n, (a + p.off).toNat + st.2 + zeroW st.1 ≤ 2 ^ 64 := by
    intro st hst; have := hin st hst; omega
  have hnil : ∀ st ∈ zeroOffs n, nilPage (a + p.off + BitVec.ofNat 64 st.2) = false ∧
      (st.1 = true → nilPage (a + p.off + BitVec.ofNat 64 st.2 + 8) = false) := by
    intro st hst
    have hi := hin st hst
    have h8 := hw8 st.1
    have h1 := toNat_addOf (A := a + p.off) (o := st.2) (by rw [hAt]; omega)
    refine ⟨?_, fun hpr => ?_⟩
    · simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt, h1]; omega
    · rw [hpr] at hi
      simp only [zeroW, ↓reduceIte] at hi
      have h2 := toNat_addOf8 (A := a + p.off) (o := st.2) (by rw [hAt]; omega)
      simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt, h2]; omega
  have hrun := zero_run (H := H) F.nodup F.lt F.ret hkn (zeroOffs n) j j' m hvs hnil hX
  rw [pc_eta hm hj] at hrun
  have hMout : ∀ y : BitVec 64, (∀ j, j < n → y.toNat ≠ a.toNat + p.off.toNat + j) →
      zeroMem (a + p.off) m.mem (zeroOffs n) y = m.mem y := by
    intro y hy
    refine zeroMem_out (zeroOffs n) m.mem hbnd fun st hst hc => ?_
    have hi := hin st hst
    have h8 := hw8 st.1
    unfold Covers at hc
    exact hy (y.toNat - (a.toNat + p.off.toNat)) (by omega) (by omega)
  obtain ⟨hMI', hk', hback, -⟩ := memInj_writeAny hA hMI hk0 (by omega) hpa hbs
    (fun j hj => by
      obtain ⟨st, hst, hc⟩ := hcovd j hj
      have hi := hin st hst
      have h8 := hw8 st.1
      rw [zeroMem_cov (zeroOffs n) m.mem hbnd ⟨st, hst, by
        unfold Covers
        rw [toNat_addOf (by rw [hAt]; omega)]
        omega⟩]
      rw [getElem!_pos _ _ (by rw [hbs]; exact hj), Array.getElem_replicate]
      rfl)
    hMout hw
  have hsep' : SepFrom E.ι (StkAt E) mm' := by
    intro b2 al2 a2 hb hι w hw'
    obtain ⟨al0, hb0, hs0⟩ := hback b2 al2 hb
    rw [← hs0]; exact hsep0 b2 al0 a2 hb0 hι w hw'
  have hP : ∀ y, StkAt E y → zeroMem (a + p.off) m.mem (zeroOffs n) y = m.mem y := fun y hy =>
    hMout y fun j hj he => hsep0 _ _ _ hal hpa y hy ⟨by omega, by omega⟩
  obtain ⟨hsl, hfr⟩ := stk_keeps hm hF hsz _ hP
  have hlm := locMatch_setMem hm hsl hfr hMI' (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hrun, hlm, (⟨hinv.regs, ⟨mm', rfl, hk', hsep'⟩⟩ :
    CoreInv E.ι (StkAt E) K { s with mem := .mem mm' }).mono
      (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)), hsi⟩

end Cases

/-! ## The theorems -/

/-- One value of G13's kinds (`VK13`) emitted at the Progs from `j` to `j'`: `vk12_step`'s
statement for G13's values, under G13's per-value premises. -/
theorem vk13_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK13 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : G13Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOK H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' := by
  cases hVK with
  | g12 hVK12 =>
    exact vk12_step hE F hhome hcf hv hVK12 hvs htemp hj hj' hreads hm hinv hpre.1 hcall hicall
      hwb hclo hs
  | zero hop hsz2 hmt hhn hao hma h16 hcov =>
    obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE.env.env.env
    have hsz := slot_sizes hlcE hcf hinv.slots
    obtain ⟨m', h1, h2, h3, h4⟩ := g13_zero (H := H) F hF hsz hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz2 hmt hhn
      hao hma h16 hcov hvs hpre.2 htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩⟩

/-- **G13, values.** `g12_value`'s statement over `checkG13`, under G13's per-value premises
(`G13Pre`: G7's, and a `LoweredZero` writes valid bytes). -/
theorem g13_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG13 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G13Pre lc s v)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks⟩ := checkG13_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind13_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk13_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre hcall hicall hwb hclo
    hs

/-- **G13, nil panics.** `g12_nilPanic`'s statement over `checkG13`. -/
theorem g13_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG13 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG13_spec hc
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
  obtain ⟨-, hVK⟩ := vkind13_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
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
                exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao
                  hma hvs hs
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

/-- **G13, terminators.** `g12_term`'s statement over `checkG13`. -/
theorem g13_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG13 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG13_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
