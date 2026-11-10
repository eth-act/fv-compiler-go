import GoFV.Proof.Gen.G6
import GoFV.Proof.Gen.Spec7
import GoFV.Proof.Gen.Progs7

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G7: nil checks (`docs/plans/proofs3.md` §4)

`g7_value`, `g7_term`: `g6_value`'s and `g6_term`'s statements over `checkG7`, with the per-value
premise `G7Pre` (G4's and `NilPre`). `g7_nilPanic`: a nil check of an accepted function that
panics under `runLoc` (its pointer is nil: `nilFaults`, `memRoot`'s `NilCheck`) is matched by
`runProg` steps to its Prog `MOVB (Rp), R27`, which faults in the nil page (`PPanics`), with the
same panic `nilDeref`.

A nil check that does not panic changes nothing in `runLoc`'s state (no home, a shape `write`
drops: `stepLoc_nilCheck`) and on the machine only `X27` (`REGTMP`, no Go register, which `LocMatch`
leaves free: `locMatch_tmp`) and the PC; its pointer is not nil, and `NilPre` (Go's nil checks
are of pointers that are nil or point to a byte of a live object) puts its address outside the nil
page (`addr_rel`), so the load does not fault (`g7_nil`). A nil pointer is the machine word 0
(`MemInj.nil`, `nil_word`), in the nil page (`g7_nilFault`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## `X27` is free -/

/-- No Go register is `X27`. -/
theorem objX?_ne27 {r : Nat} {k : Reg} (h : objX? r = some k) : k ≠ BitVec.ofNat 5 27 := by
  unfold objX? at h
  intro he
  subst he
  split at h
  · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
  · split at h
    · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
    · split at h
      · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
      · cases h

/-- Writing `X27` keeps `LocMatch` (with the PC moved). -/
theorem locMatch_tmp {E : MatchEnv} {s : LocState} {b : ID} {i : Nat} {m : MState}
    (h : LocMatch E s b i m) (val : BitVec 64) {b' : ID} {i' : Nat} :
    LocMatch E s b' i' { m.wX (BitVec.ofNat 5 27) val with pc := E.pcOf b' i' } := by
  have hw : m.wX (BitVec.ofNat 5 27) val =
      { m with x := fun j => if j = BitVec.ofNat 5 27 then val else m.x j } :=
    by simp [GoFV.Arm64.MState.wX]
  rw [hw]
  have hx : ∀ j : Reg, j ≠ BitVec.ofNat 5 27 →
      (if j = BitVec.ofNat 5 27 then val else m.x j) = m.x j := fun j hj => by simp [hj]
  refine ⟨fun r v hv => ?_, h.flags, h.slots, h.mem, ?_, rfl⟩
  · obtain ⟨h1, h2⟩ := h.regs r v hv
    exact ⟨fun k hk => by simpa only [hx k (objX?_ne27 hk)] using h1 k hk, h2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.frame
    refine ⟨h1, by simpa only [hx 28 (by decide)] using h2, fun hf => ?_, fun hf => ?_⟩
    · obtain ⟨a, b, c⟩ := h3 hf
      exact ⟨by simpa only [hx 29 (by decide)] using a, b, c⟩
    · obtain ⟨a, b⟩ := h4 hf
      exact ⟨by simpa only [hx 29 (by decide)] using a, by simpa only [hx 30 (by decide)] using b⟩

/-! ## `stepLoc` of a nil check -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The memory of a nil check whose pointer is nil (`nilFaults`): the base of its one access. -/
theorem nilFaults_nilCheck {ctx : Ctx} (hop : v.op = .ARM64LoweredNilCheck) (x : Val) (mm : Mem) :
    nilFaults true ctx v [x, .mem mm] =
      match Arm64.addr x 0#64 with
      | some b => if b.isNil && b.nilFault then some mm else none
      | none => none := by
  unfold nilFaults nilAccesses
  rw [hop]
  cases h : Arm64.addr x 0#64 <;> simp (config := { decide := true }) [h]

/-- A pointer word (`Val.asPtrWord`) is the address `Arm64.addr` reads at offset 0. -/
theorem addr_of_asPtrWord {x : Val} {p : Ptr} (h : x.asPtrWord = some p) :
    Arm64.addr x 0#64 = some p := by
  cases x with
  | ptr q =>
    cases h
    simp [Arm64.addr, Ptr.add]
  | int w k =>
    cases w <;> simp [Val.asPtrWord] at h
    subst h
    simp [Arm64.addr, Arm64.reg]
  | _ => simp [Val.asPtrWord] at h

/-- `evalOpL` of a nil check of `x`: the panic of `nilFaults`, `stuck` on a wild pointer, else
`memRoot`'s `NilCheck`. -/
theorem evalOpL_nilCheck {ctx : Ctx} {fr : GoFV.SSA.Sem.Frame} {ty : Ty}
    (hop : v.op = .ARM64LoweredNilCheck) (x : Val) (mm : Mem) :
    evalOpL true env ctx fr v [x, .mem mm] ty =
      match nilFaults true ctx v [x, .mem mm] with
      | some m => .panic .nilDeref m
      | none =>
        if true && wildNil [x, .mem mm] then
          .stuck s!"{s!"v{v.id}: {v.op.name}"}: nil check of a wild pointer"
        else memRoot ctx { v with op := .NilCheck } [x, .mem mm] := by
  unfold evalOpL arm64Op
  rw [hop]
  rfl

/-- A nil check of `x` that succeeds: `x`'s address is not in the nil block. -/
theorem evalOpL_nilCheck_ok {ctx : Ctx} {fr : GoFV.SSA.Sem.Frame} {ty : Ty}
    (hop : v.op = .ARM64LoweredNilCheck) {x : Val} {mm : Mem} {r : Val}
    (h : evalOpL true env ctx fr v [x, .mem mm] ty = .ok r) :
    ∃ p, Arm64.addr x 0#64 = some p ∧ p.blk ≠ .nil := by
  rw [evalOpL_nilCheck hop] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [memRoot] at h
      cases hx : x.asPtrWord with
      | none => simp [hx] at h
      | some p =>
        simp only [hx] at h
        split at h
        · cases h
        · rename_i hb
          exact ⟨p, addr_of_asPtrWord hx, by simpa using hb⟩

/-- A nil check of `x` that panics: with `nilDeref`, and `x` is the nil pointer. -/
theorem evalOpL_nilCheck_panic {ctx : Ctx} {fr : GoFV.SSA.Sem.Frame} {ty : Ty}
    (hop : v.op = .ARM64LoweredNilCheck) {x : Val} {mm : Mem} {e : Panic} {mm' : Mem}
    (h : evalOpL true env ctx fr v [x, .mem mm] ty = .panic e mm') :
    e = .nilDeref ∧ ∃ p, Arm64.addr x 0#64 = some p ∧ p.blk = .nil ∧ p.off = 0 := by
  rw [evalOpL_nilCheck hop] at h
  split at h
  · rename_i m hf
    cases h
    refine ⟨rfl, ?_⟩
    rw [nilFaults_nilCheck hop] at hf
    split at hf
    · rename_i b hb
      split at hf
      · rename_i hn
        simp only [Bool.and_eq_true, Ptr.isNil, beq_iff_eq] at hn
        exact ⟨b, hb, hn.1.1, hn.1.2⟩
      · cases hf
    · cases hf
  · split at h
    · cases h
    · rename_i hw
      simp only [memRoot] at h
      cases hx : x.asPtrWord with
      | none => simp [hx] at h
      | some p =>
        simp only [hx] at h
        split at h
        · rename_i hb
          cases h
          have ha := addr_of_asPtrWord hx
          have ha0 : Arm64.addr x 0 = some p := ha
          simp only [Bool.true_and, wildNil, List.head?_cons, Option.bind_some, ha0,
            Option.map_some, Option.getD_some] at hw
          simp only [beq_iff_eq] at hb
          have hn : p.isNil = true := by
            cases hi : p.isNil <;> simp_all [Ptr.wild]
          simp only [Ptr.isNil, Bool.and_eq_true, beq_iff_eq] at hn
          exact ⟨rfl, p, ha, hb, hn.2⟩
        · cases h

/-- `LocState.read` does not panic. -/
theorem read_noPanic {a : ID} {e : Panic} {m : Mem} : s.read lc a ≠ .panic e m := by
  unfold LocState.read
  cases hr : s.raw lc a with
  | ok x => simp [bind, Res.bind]
  | panic e' m' =>
    unfold LocState.raw at hr
    dsimp only at hr
    split at hr <;> (try split at hr) <;> cases hr
  | stuck msg => simp [bind, Res.bind]

/-- A value with no home and a dropped shape (`dropTy`) writes nothing. -/
theorem write_drop {id : ID} (hh : lc.home id = none) (hd : dropTy (lc.ty id) = true) (x : Val) :
    s.write lc id x = s := by
  unfold LocState.write
  rw [hh]
  cases ht : lc.ty id <;> rw [ht] at hd <;> simp_all [dropTy]

/-- A nil check that succeeds changes nothing, and its pointer is not in the nil block. -/
theorem stepLoc_nilCheck (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64LoweredNilCheck) {a0 a1 : ID} (ha : v.args = #[a0, a1]) {mm : Mem}
    (hm : s.read lc a1 = .ok (.mem mm)) (hh : lc.home v.id = none)
    (hd : dropTy (lc.ty v.id) = true) (h : stepLoc env lc s v = .ok s') :
    s' = s ∧ ∃ x p, s.read lc a0 = .ok x ∧ Arm64.addr x 0#64 = some p ∧ p.blk ≠ .nil := by
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmv
  change ((s.read lc a0).bind fun x => (s.read lc a1).bind fun y => Res.ok [x, y]) = _ at hmv
  rw [hm] at hmv
  cases hx : s.read lc a0 with
  | ok x =>
    rw [hx] at hmv
    cases hmv
    exact ⟨write_drop hh hd _, x, evalOpL_nilCheck_ok hop hr |>.imp fun p hp => ⟨rfl, hp⟩⟩
  | panic e m => rw [hx] at hmv; cases hmv
  | stuck msg => rw [hx] at hmv; cases hmv

/-- A nil check that panics: with `nilDeref`, its pointer nil. -/
theorem stepLoc_nilCheck_panic (hop : v.op = .ARM64LoweredNilCheck) {a0 a1 : ID}
    (ha : v.args = #[a0, a1]) {mm : Mem} (hm : s.read lc a1 = .ok (.mem mm)) {e : Panic}
    {mm' : Mem} (h : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ x p, s.read lc a0 = .ok x ∧ Arm64.addr x 0#64 = some p ∧ p.blk = .nil ∧
      p.off = 0 := by
  unfold stepLoc at h
  simp only [show (v.op == Op.Phi) = false by rw [hop]; rfl, Bool.false_eq_true,
    ↓reduceIte] at h
  rw [ha] at h
  change ((((s.read lc a0).bind fun x => (s.read lc a1).bind fun y => Res.ok [x, y])).bind
    fun argv => _) = _ at h
  rw [hm] at h
  cases hx : s.read lc a0 with
  | ok x =>
    rw [hx] at h
    have hfl : (LMode.loc lc.ctx.f).faulting = true := rfl
    simp only [Res.bind, hop, hfl] at h
    cases hr : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) with
    | ok r => rw [hr] at h; cases h
    | panic e' m' =>
      rw [hr] at h
      cases h
      obtain ⟨he, p, hp⟩ := evalOpL_nilCheck_panic hop hr
      exact ⟨he, x, p, rfl, hp⟩
    | stuck msg => rw [hr] at h; cases h
  | panic e' m' => exact absurd hx read_noPanic
  | stuck msg => rw [hx] at h; cases h

end Step

/-! ## The premise and the nil pointer -/

/-- The per-value premise of a nil check: its pointer, unless in the nil block, points to a byte
of a live block (Go's nil checks are of pointers that are nil or point into an object). -/
def NilPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  v.op = .ARM64LoweredNilCheck → ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
    ∀ p, Arm64.addr x 0#64 = some p → p.blk ≠ .nil → ∃ mm, s.mem = .mem mm ∧ (mm.read p 1).isSome

/-- The per-value premises of G7: G4's and the nil check's. -/
def G7Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop := G4Pre lc s v ∧ NilPre lc s v

/-- An integer address in the nil block is that block at the address. -/
theorem ofAddr_off_nil {k : BitVec 64} (h : (Ptr.ofAddr k).blk = .nil) : (Ptr.ofAddr k).off = k := by
  rw [Ptr.ofAddr_eq_nil h]

/-- The nil pointer (as a pointer or as the integer 0) is the machine word 0. -/
theorem nil_word {ι : Blk → Option (BitVec 64)} (h0 : ι .nil = some 0) {x : Val} {X : BitVec 64}
    (hx : ValRel ι x X) (hf : Fits 64 x) {p : Ptr} (hp : Arm64.addr x 0#64 = some p)
    (hb : p.blk = .nil) (ho : p.off = 0) : X = 0 := by
  cases x with
  | ptr q =>
    simp only [Arm64.addr, Option.some.injEq] at hp
    subst hp
    simp only [Ptr.add, BitVec.add_zero] at hb ho
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hb, h0] at ha
    cases ha
    simp [ho]
  | int w k =>
    cases w <;> simp [Fits, Width.bits] at hf
    simp only [Arm64.addr, Arm64.reg, Option.map_some, Option.some.injEq,
      BitVec.setWidth_eq, BitVec.add_zero] at hp
    subst hp
    have hk := ofAddr_off_nil hb
    rw [ho] at hk
    subst hk
    rcases hx with rfl | ⟨hne, -⟩
    · rfl
    · exact absurd hb hne
  | poison => simp [Arm64.addr, Arm64.reg] at hp
  | bool c => simp [Fits] at hf
  | _ => exact hf.elim

/-! ## One nil check -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- A nil check that does not panic: `MOVB (Rp), R27` loads a byte of the pointer's block into
`X27`, which `LocMatch` leaves free; `runLoc`'s state is unchanged. -/
theorem g7_nil (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : NilPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rp : Int} (hop : v.op = .ARM64LoweredNilCheck) (hsz2 : v.args.size = 2)
    (hhn : lc.home v.id = none) (hdt : dropTy (lc.ty v.id) = true)
    (hao : argObj lc v 0 = .ok (64, rp)) (hma : memArg lc v 1 = .ok ())
    (hvs : OneAt2 psA j (.ofShape (nilShape rp)) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨k0, hk0, rfl, hkk0⟩ := objOf?_some hor0
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkk0
  obtain ⟨rfl, x', p, hx', hp, hpb⟩ := stepLoc_nilCheck hl htemp hop (arr2 hsz2 ha0 ha1)
    (read_mem hl hah1 hamt hmm) hhn hdt hs
  rw [hx] at hx'
  cases hx'
  obtain ⟨mm', hmm', hrd⟩ := hpre hop a0 x ha0 hx p hp hpb
  rw [hmm] at hmm'
  cases hmm'
  obtain ⟨a, -, haddr, hnil⟩ := addr_rel hA hMI hxv hxf hp (by decide : 0 < 1) (Or.inr hrd)
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, hf, -, ht, hsc⟩ := Shape.ok_eq (sh := nilShape _) hok
  have hnil' : nilPage (({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 k0) +
      BitVec.ofInt 64 0) = false := by
    have h0 : BitVec.ofInt 64 0 = 0#64 := rfl
    rw [h0]
    exact haddr ▸ hnil
  obtain ⟨val, hstep⟩ := progStep_nilCheck hk0 (nextAddr_pcAt F.nodup hk) has hf hsc ht hnil'
  rw [wX_pc] at hstep
  have hlm := locMatch_tmp hm val (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl hstep), hlm,
    hinv.mono (knext_same hK (Or.inr fun r _ => by rw [hhn]; nofun)), hsi⟩

/-- A nil check that panics: its pointer is nil, the machine word 0, so `MOVB (Rp), R27` faults
in the nil page and `runProg` panics with the same `nilDeref`. -/
theorem g7_nilFault {P : BitVec 64 → Prop} (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P K s osp) (hR : KRead lc v K)
    (hj : E.pcOf b i = pcAt text psA.toList j)
    {rp : Int} (hop : v.op = .ARM64LoweredNilCheck) (hsz2 : v.args.size = 2)
    (hao : argObj lc v 0 = .ok (64, rp)) (hma : memArg lc v 1 = .ok ())
    (hvs : OneAt2 psA j (.ofShape (nilShape rp)) j')
    {e : Panic} {mm' : Mem} (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      PPanics H (Link.byId sym text az ez psA.toList) psA.toList ret m' e := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨k0, hk0, rfl, hkk0⟩ := objOf?_some hor0
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkk0
  obtain ⟨rfl, x', p, hx', hp, hpb, hpo⟩ :=
    stepLoc_nilCheck_panic hop (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  rw [hx] at hx'
  cases hx'
  have h0 := nil_word hMI.nil hxv hxf hp hpb hpo
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, hf, -, ht, hsc⟩ := Shape.ok_eq (sh := nilShape _) hok
  have hnil : nilPage (({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 k0) +
      BitVec.ofInt 64 0) = true := by
    show nilPage (m.rX (BitVec.ofNat 5 k0) + BitVec.ofInt 64 0) = true
    rw [h0]
    decide
  have hne : ({ m with pc := pcAt text psA.toList k } : MState).pc ≠ ret := fun hr =>
    F.ret _ (List.getElem_mem hk) (by rw [addr_pcAt hk]; exact congrArg some hr)
  exact ⟨rfl, _, hstar, hne, .inl ⟨_, _, progAt?_pcAt F.nodup F.lt hk,
    progStep_nilCheck_nil hk0 (nextAddr_pcAt F.nodup hk) has hf hsc ht hnil, rfl⟩⟩

end Cases

/-! ## The theorems -/

/-- One value of G7's kinds (`VK7`) emitted at the Progs from `j` to `j'`: `vk6_step`'s statement
for G7's values. -/
theorem vk7_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G6Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hns : CallsNotSlot lc)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK7 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hpre : G7Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G6Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp := by
  cases hVK with
  | g6 _ hVK6 =>
    exact vk6_step hE F hns hcf hv hVK6 hvs htemp hj hj' hreads hm hinv hpre.1 hcall hs
  | nil hop hsz2 hhn hdt hao hma =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g7_nil (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_none hhn).noRegs) hpre.2 hj hj' hop hsz2
      hhn hdt hao hma hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩⟩

/-- **G7, values.** `g6_value`'s statement over `checkG7`, with the per-value premises `G7Pre`
(G4's, and `NilPre` for a nil check): a value (not an entry value) of an accepted function run by
`runLoc` is matched by `runProg` steps of genssa's P0 Progs to a state related before the next
value, with the registers at the classes before the next value, under an activation that extends
`E`'s injection and is again a `G6Env`. -/
theorem g7_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG7 lc ps bstart g = .ok (tab, kt)) (hE : G6Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G7Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G6Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome4, hcf, hk, hlt, hnd, hblocks⟩ := checkG7_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind7_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk7_step hE0 F (call_not_slot4 hhome4) hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre
    hcall hs

/-- **G7, nil panics.** A nil check of a function `checkG7` accepted whose `runLoc` step panics
(its pointer is nil) panics with `nilDeref`, and so does `runProg`: its steps reach the check's
`MOVB (Rp), R27`, which faults in the nil page (`PPanics`, a panicking `runProg` by
`PPanics.runProg`). -/
theorem g7_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {mm' : Mem}
    (hc : checkG7 lc ps bstart g = .ok (tab, kt)) (hE : G6Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome4, -, hk, hlt, hnd, hblocks⟩ := checkG7_spec hc
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
  obtain ⟨-, hVK⟩ := vkind7_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩
  cases hVK with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G7, terminators.** `g6_term`'s statement over `checkG7`. -/
theorem g7_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG7 lc ps bstart g = .ok (tab, kt)) (hE : G6Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome4, -, hk, hlt, hnd, hblocks⟩ := checkG7_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
