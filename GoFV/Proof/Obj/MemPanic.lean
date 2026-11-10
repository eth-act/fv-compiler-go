import GoFV.Proof.Obj.CallPanic

variable [GoFV.SSA.Sem.Addrs]

/-!
# Loads and stores that fault in the nil page (`docs/plans/proofs3.md` §9)

A load or store of slice G60 whose `runLoc` step panics: `nilFaults` (memory ops fault under
`runLoc`) found its base nil (`Ptr.isNil`) and its address in the nil page (`Ptr.nilFault`), so it
has no symbol (a global or frame variable is never in the nil block) and its base is a register
(`off(Rn)`). That register holds the machine word 0 (`nil_word`), so the access's address
`X[n] + off` is in the nil page (`nil_fault_page`) and the access faults (`progStep_loadN_nil`,
`progStep_ldp_nil`, `progStep_storeN_nil`, `progStep_stp_nil`): `runProg` panics with
`nilDeref`, as `runLoc` does (`g60_memPanic`), and so does `runMach` (`g60_obj_memPanic`,
`obj_panic`). The accesses are `loadOp?`'s `MOV{D,W,WU,H,HU,B,BU}load`, `LDP`, `storeOp?`'s
`MOV{D,W,H,B}store` and `STP` (`memFaultOp`); the register-index loads and stores are not among
them: `runLoc` faults on their nil base whatever the index, the machine only when the index keeps
the address in the nil page. None of them is an op of G52's–G59's groups (a remainder,
`LoweredMove`, a loop, a float constant, `STPW`/`LDPW`, a frame float store, a narrow operand,
`FLDPD`), so what `vkind60` accepts of it `vkind49` or G48's `kind48` accepts (`vkind60_ok49`); an
access `kind48` takes is off `SP` (`spBase48`): its base relates to `SP` (`SPInv`, `sp_base48`),
which lies above the nil page (`FrameOK`), so it does not fault (`nil_word`).
Having no symbol, a
faulting access is no access of a frame variable G49 accepts (`frameVar49?_none`), so `vkind49` of
it is `vkind51`'s (`vkind49_eq51`), which is `vkind50`'s (`vkind51_eq50`).

An acquire load (`LDAR`, `LDARW`, `LDARB`, `ldar?`) of slice G60 whose step panics faults alike:
`nilFaults` found its address (argument 0, offset 0, no symbol) nil (`stepLoc_ldar_panic`), the
register holds the machine word 0 and `LDAR* (Rn)` faults (`progStep_ldar_nil`; `g60_ldarPanic`,
`g60_obj_ldarPanic`); what `vkind60` accepts of it `vkind49` accepts (G48's `kind48` takes no
acquire load), and what `vkind49` accepts of it `vkind51`
accepts (`vkind49_ok51`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen

/-- The loads and stores whose nil-page fault the panic theorems cover: `loadOp?`'s
`MOV{D,W,WU,H,HU,B,BU}load`, `LDP`, `storeOp?`'s `MOV{D,W,H,B}store` and `STP`. -/
def memFaultOp (o : Op) : Bool :=
  (loadOp? o).isSome || o == .ARM64LDP || (storeOp? o).isSome || o == .ARM64STP

theorem memFaultOp_cases {o : Op} (h : memFaultOp o = true) :
    o = .ARM64MOVDload ∨ o = .ARM64MOVBload ∨ o = .ARM64MOVBUload ∨ o = .ARM64MOVHload ∨
      o = .ARM64MOVHUload ∨ o = .ARM64MOVWload ∨ o = .ARM64MOVWUload ∨ o = .ARM64LDP ∨
      o = .ARM64MOVDstore ∨ o = .ARM64MOVBstore ∨ o = .ARM64MOVHstore ∨ o = .ARM64MOVWstore ∨
      o = .ARM64STP := by
  unfold memFaultOp at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((hl | h) | hs) | h
  · obtain ⟨⟨as, n, sg⟩, hl⟩ := Option.isSome_iff_exists.1 hl
    rcases loadOp?_op hl with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨h1, -⟩ <;> simp [h1]
  · simp [h]
  · obtain ⟨⟨as, n⟩, hs⟩ := Option.isSome_iff_exists.1 hs
    rcases storeOp?_op hs with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  · simp [h]

/-! ## `runLoc`: the step of a load or store that panics -/

section Step

variable {env : Env} {lc : LocCtx} {s : LocState} {v : Value}

theorem mapM_loop_read_ne_panic : ∀ (l : List ID) (acc : List Val) {e : Panic} {m : Mem},
    List.mapM.loop (s.read lc) l acc ≠ .panic e m
  | [], acc, e, m => by simp [List.mapM.loop, pure]
  | a :: l, acc, e, m => by
    simp only [List.mapM.loop]
    cases hx : s.read lc a with
    | ok x => simp only [bind, Res.bind]; exact mapM_loop_read_ne_panic l (x :: acc)
    | panic e' m' => exact absurd hx read_noPanic
    | stuck msg => simp [bind, Res.bind]

theorem mapM_read_ne_panic (l : List ID) {e : Panic} {m : Mem} :
    l.mapM (s.read lc) ≠ .panic e m := by
  unfold List.mapM
  exact mapM_loop_read_ne_panic l []

/-- The head of arguments read by `mapM`. -/
theorem mapM_read_head {l : List ID} {argv : List Val} {a : ID}
    (h : l.mapM (s.read lc) = .ok argv) (ha : l.head? = some a) :
    ∃ x, s.read lc a = .ok x ∧ argv.head? = some x := by
  obtain ⟨hlen, hk⟩ := mapM_res h
  cases l with
  | nil => cases ha
  | cons a' l =>
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    cases argv with
    | nil => simp at hlen
    | cons x xs =>
      have h0 := hk 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h0
      exact ⟨x, h0, rfl⟩

/-- `stepLoc` of an op `evalOpL` runs panics only as `evalOpL` does on the arguments read. -/
theorem stepLoc_panic_eval (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg) (h2 : v.op ≠ .StoreReg)
    (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop) {e : Panic} {mm : Mem}
    (h : stepLoc env lc s v = .panic e mm) :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) = .panic e mm := by
  unfold stepLoc at h
  simp only [show (v.op == Op.Phi) = false by simpa using hne, Bool.false_eq_true,
    ↓reduceIte] at h
  cases hm : v.args.toList.mapM (s.read lc) with
  | panic e' m' => exact absurd hm (mapM_read_ne_panic _)
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    split at h
    · exact (h1 ‹_›).elim
    · exact (h2 ‹_›).elim
    · exact (h1 ‹_›).elim
    · exact (h2 ‹_›).elim
    · exact (h3 ‹_›).elim
    · exact (h4 ‹_›).elim
    · split at h
      · cases h
      · rename_i e' m' hr; cases h; exact ⟨_, rfl, hr⟩
      · cases h

/-- The nil fault of a load or store: its base (argument 0) is nil and its address (`symAddr`) is
in the nil page. -/
theorem nilFaults_mem {ctx : GoFV.SSA.Sem.Ctx} (hop : memFaultOp v.op = true)
    {argv : List Val} {m : Mem}
    (h : nilFaults true ctx v argv = some m) :
    ∃ x b p, argv.head? = some x ∧ Arm64.addr x 0 = some b ∧ b.isNil = true ∧
      symAddr ctx v x = some p ∧ p.nilFault = true := by
  unfold nilFaults at h
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · split at h
    · rename_i hany
      rcases memFaultOp_cases hop with ho | ho | ho | ho | ho | ho | ho | ho | ho | ho | ho | ho |
        ho <;>
      · simp only [nilAccesses, ho] at hany
        simp (config := { decide := true }) only [↓reduceIte, Option.toList,
          List.append_nil] at hany
        cases hx : argv.head? with
        | none => simp [hx] at hany
        | some x =>
          cases hb : Arm64.addr x 0#64 with
          | none => simp [hx, hb] at hany
          | some b =>
            cases hp : symAddr ctx v x with
            | none => simp [hx, hb, hp] at hany
            | some p =>
              simp [hx, hb, hp] at hany
              exact ⟨x, b, p, rfl, hb, hany.1, hp, hany.2⟩
    · cases h
  · cases h

/-- `evalOpL` of a load or store is `arm64Op`'s, which panics only by `nilFaults`. -/
theorem evalOpL_mem_panic {ctx : GoFV.SSA.Sem.Ctx} {fr : GoFV.SSA.Sem.Frame} {ty : Ty}
    {argv : List Val}
    (hop : memFaultOp v.op = true) {e : Panic} {mm : Mem}
    (h : evalOpL true env ctx fr v argv ty = .panic e mm) :
    e = .nilDeref ∧ nilFaults true ctx v argv = some mm := by
  rcases memFaultOp_cases hop with ho | ho | ho | ho | ho | ho | ho | ho | ho | ho | ho | ho |
    ho <;>
  · have hev : evalOpL true env ctx fr v argv ty = arm64Op true env ctx fr v argv ty := by
      unfold evalOpL; rw [ho]; rfl
    rw [hev] at h
    cases hn : nilFaults true ctx v argv with
    | some m =>
      unfold arm64Op at h
      rw [hn] at h
      cases h
      exact ⟨rfl, rfl⟩
    | none =>
      unfold arm64Op at h
      rw [hn] at h
      simp only [ho] at h
      repeat' split at h
      all_goals first | cases h | (simp only [writeRes] at h; split at h <;> cases h)

/-- **A load or store whose step panics**: with `nilDeref`, its base (argument 0) read as a nil
pointer and its address in the nil page. -/
theorem stepLoc_mem_panic (hop : memFaultOp v.op = true) {e : Panic} {mm : Mem}
    (h : stepLoc env lc s v = .panic e mm) :
    e = .nilDeref ∧ ∃ a0 x b p, v.args[0]? = some a0 ∧ s.read lc a0 = .ok x ∧
      Arm64.addr x 0 = some b ∧ b.isNil = true ∧ symAddr lc.ctx v x = some p ∧
      p.nilFault = true := by
  have hne : ∀ o, v.op = o → memFaultOp o = true := fun o h => h ▸ hop
  have hsimp : ∀ o, v.op = o → memFaultOp o = false → False := fun o h h' => by
    rw [hne o h] at h'; cases h'
  obtain ⟨argv, hmap, hev⟩ := stepLoc_panic_eval
    (fun h' => hsimp _ h' (by decide)) (fun h' => hsimp _ h' (by decide))
    (fun h' => hsimp _ h' (by decide)) (fun h' => hsimp _ h' (by decide))
    (fun h' => hsimp _ h' (by decide)) h
  obtain ⟨rfl, hn⟩ := evalOpL_mem_panic hop hev
  obtain ⟨x, b, p, hx, hb, hbn, hp, hpf⟩ := nilFaults_mem hop hn
  cases ha : v.args.toList.head? with
  | none =>
    obtain ⟨hlen, -⟩ := mapM_res hmap
    have hl : v.args.toList = [] := by
      cases hl : v.args.toList with
      | nil => rfl
      | cons a l => rw [hl] at ha; cases ha
    rw [hl] at hlen
    cases argv with
    | nil => cases hx
    | cons _ _ => simp at hlen
  | some a0 =>
    obtain ⟨x', hx', hxh⟩ := mapM_read_head hmap ha
    rw [hx] at hxh
    cases hxh
    refine ⟨rfl, a0, x, b, p, ?_, hx', hb, hbn, hp, hpf⟩
    have : v.args.toList[0]? = some a0 := by rw [← List.head?_eq_getElem?]; exact ha
    simpa using this

/-- An access with a symbol is not in the nil block. -/
theorem symAddr_aux_ne_nil {ctx : GoFV.SSA.Sem.Ctx} {n : AuxRef} (haux : v.aux = some n)
    {a : Val} {p : Ptr}
    (h : symAddr ctx v a = some p) : p.blk ≠ .nil := by
  unfold symAddr at h
  rw [haux] at h
  simp only at h
  split at h
  · cases h; nofun
  · cases h; unfold frameBlk; split <;> nofun
  · cases h

/-- A load or store whose step panics has no symbol. -/
theorem stepLoc_mem_panic_aux (hop : memFaultOp v.op = true) {e : Panic} {mm : Mem}
    (h : stepLoc env lc s v = .panic e mm) : v.aux = none := by
  obtain ⟨-, a0, x, b, p, -, -, -, -, hp, hpf⟩ := stepLoc_mem_panic hop h
  cases haux : v.aux with
  | none => rfl
  | some n =>
    have hne := symAddr_aux_ne_nil haux hp
    simp [Ptr.nilFault, hne] at hpf

/-- **An acquire load whose step panics**: with `nilDeref`, its address (argument 0, offset 0)
read as a nil pointer in the nil page. -/
theorem stepLoc_ldar_panic {as : As} {n : Nat} (hop : ldar? v.op = some (as, n)) {e : Panic}
    {mm : Mem} (h : stepLoc env lc s v = .panic e mm) :
    e = .nilDeref ∧ ∃ a0 x b, v.args[0]? = some a0 ∧ s.read lc a0 = .ok x ∧
      Arm64.addr x 0 = some b ∧ b.isNil = true ∧ b.nilFault = true := by
  have hld : ∀ o, v.op = o → (ldar? o).isSome = true := fun o h => by rw [← h, hop]; rfl
  obtain ⟨argv, hmap, hev⟩ := stepLoc_panic_eval
    (fun h' => absurd (hld _ h') (by decide)) (fun h' => absurd (hld _ h') (by decide))
    (fun h' => absurd (hld _ h') (by decide)) (fun h' => absurd (hld _ h') (by decide))
    (fun h' => absurd (hld _ h') (by decide)) h
  have hn : nilFaults true lc.ctx v argv = some mm ∧ e = .nilDeref := by
    rcases ldar?_some hop with ⟨ho, -⟩ | ⟨ho, -⟩ | ⟨ho, -⟩ <;>
    · have hea : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
          arm64Op true env lc.ctx s.fr v argv (lc.ty v.id) := by
        unfold evalOpL; rw [ho]; rfl
      rw [hea] at hev
      cases hnf : nilFaults true lc.ctx v argv with
      | some m =>
        have hp : arm64Op true env lc.ctx s.fr v argv (lc.ty v.id) = .panic .nilDeref m := by
          unfold arm64Op; rw [hnf]
        rw [hp] at hev
        cases hev
        exact ⟨rfl, rfl⟩
      | none =>
        have hok : arm64Op true env lc.ctx s.fr v argv (lc.ty v.id) =
            .ok (atomicLoad (lc.ty v.id) argv) := by
          unfold arm64Op; rw [hnf, ho]; rfl
        rw [hok] at hev
        cases hev
  obtain ⟨hnf, rfl⟩ := hn
  refine ⟨rfl, ?_⟩
  unfold nilFaults at hnf
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hnf
  split at hnf
  · split at hnf
    · rename_i hany
      rcases ldar?_some hop with ⟨ho, -⟩ | ⟨ho, -⟩ | ⟨ho, -⟩ <;>
      · simp only [nilAccesses, ho] at hany
        simp (config := { decide := true }) only [↓reduceIte, Option.toList,
          List.append_nil] at hany
        cases ha : v.args.toList.head? with
        | none =>
          obtain ⟨hlen, -⟩ := mapM_res hmap
          have hl : v.args.toList = [] := by
            cases hl : v.args.toList with
            | nil => rfl
            | cons a l => rw [hl] at ha; cases ha
          rw [hl] at hlen
          cases argv with
          | nil => simp at hany
          | cons _ _ => simp at hlen
        | some a0 =>
          obtain ⟨x, hx, hxh⟩ := mapM_read_head hmap ha
          cases hb : Arm64.addr x 0#64 with
          | none => simp [hxh, hb] at hany
          | some b =>
            simp [hxh, hb] at hany
            have h0 : v.args.toList[0]? = some a0 := by rw [← List.head?_eq_getElem?]; exact ha
            exact ⟨a0, x, b, by simpa using h0, hx, hb, hany.1, hany.2⟩
    · cases hnf
  · cases hnf

end Step

/-! ## The machine: the access faults -/

/-- A nil base (`Ptr.isNil`) moved by `k` into the nil page: the machine word of the base plus `k`
is in the nil page. -/
theorem nil_fault_page {ι : Blk → Option (BitVec 64)} (h0 : ι .nil = some 0) {x : Val}
    {X : BitVec 64} (hx : ValRel ι x X) (hf : Fits 64 x) {b p : Ptr} {k : BitVec 64}
    (hb : Arm64.addr x 0 = some b) (hbn : b.isNil = true) (hp : Arm64.addr x k = some p)
    (hpf : p.nilFault = true) : nilPage (X + k) = true := by
  obtain ⟨hbb, hbo⟩ : b.blk = .nil ∧ b.off = 0 := by simpa [Ptr.isNil] using hbn
  have hX := nil_word h0 hx hf hb hbb hbo
  simp only [Ptr.nilFault, Bool.and_eq_true, beq_iff_eq] at hpf
  obtain ⟨hpb, hpo⟩ := hpf
  have hpo' : p.off.toNat < 4096 := of_decide_eq_true hpo
  have hpk : p.off = k := by
    cases x with
    | ptr q =>
      simp only [Arm64.addr, Option.some.injEq] at hb hp
      subst hb hp
      have hq : q.off = 0 := by simpa [Ptr.add] using hbo
      show q.off + k = k
      rw [hq]; simp
    | int w z =>
      cases w <;> simp [Fits, Width.bits] at hf
      simp only [Arm64.addr, Arm64.reg, Option.map_some, Option.some.injEq,
        BitVec.setWidth_eq] at hb hp
      subst hb hp
      have hz := ofAddr_off_nil hbb
      rw [hbo] at hz
      have hz' : z = 0 := by simpa using hz.symm
      rw [ofAddr_off_nil hpb, hz']
      simp
    | poison => simp [Arm64.addr, Arm64.reg] at hb
    | bool c => simp [Fits] at hf
    | _ => exact hf.elim
  rw [hX, ← hpk]
  simpa [nilPage] using hpo'

section Machine

open GoFV.Asm.ARM64

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- An opcode name none of `progEffect`'s branches before the `movMem` one takes (and no skip);
as `Progs3`'s private `movPre`. -/
private def movPre (name : String) : Prop :=
  name ∉ ["TEXT", "FUNCDATA", "PCDATA", "NOP"] ∧
  ProgOp.baseOf name ProgOp.binNames = none ∧ ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
  ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
  ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
  ProgOp.baseOf name ["MADD", "MSUB"] = none ∧
  ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] = none ∧
  ProgOp.baseOf name ["EXTR"] = none ∧
  ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] = none ∧
  ProgOp.baseOf name ["CSET", "CSETM"] = none

private theorem movPre_of {name : String} {n : Nat} {sg : Bool}
    (hm : ProgOp.movMem name = some (n, sg, false)) : movPre name := by
  unfold ProgOp.movMem at hm
  split at hm <;> (try cases hm) <;> simp (config := { decide := true }) [movPre]

private theorem isSkip_of {n : Nat} {sg : Bool}
    (hm : ProgOp.movMem p.as.name = some (n, sg, false)) : p.isSkip = false := by
  have h := (movPre_of hm).1
  unfold Prog.isSkip
  split <;> rename_i has <;> (try rfl) <;> rw [has] at h <;> exact absurd (by decide) h

/-- A load of the `MOV` family from the address `a` (as `Progs3`'s private `eff_load`). -/
private theorem eff_load {c : ProgCtx} {n kd : Nat} {sg : Bool} {a : BitVec 64} (hkd : kd < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, sg, false)) (hf : c.p.from_.type = .MEM)
    (hma : c.mem c.p.from_ = .ok (a, none)) (ht : c.p.to = regA (REG_R0 + kd)) :
    progEffect c = .ok (effWd { loads := [(a, n)] } kd
      (if sg then ProgOp.sextTo64 n ((readMem c.s.mem a n).setWidth 64)
       else (readMem c.s.mem a n).setWidth 64)) := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := movPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, hma, ht, regA, Eff.ld, ProgCtx.load,
    Bool.false_eq_true, ↓reduceIte]
  simp only [eff_wX_dest hkd]
  rfl

/-- `LDP` at the address `A` of its operand (as `Progs4`'s private `eff_ldp`). -/
private theorem eff_ldp {c : ProgCtx} {ka kb : Nat} {A : BitVec 64} (hka : ka < 31)
    (hkb : kb < 31) (has : c.p.as = .LDP) (hma : c.mem c.p.from_ = .ok (A, none))
    (ht : c.p.to = pairA (REG_R0 + ka) (REG_R0 + kb)) :
    progEffect c = .ok
      { x := [(kb, c.load (A + BitVec.ofNat 64 8) 8), (ka, c.load A 8)],
        loads := [(A + BitVec.ofNat 64 8, 8), (A, 8)] } := by
  have hname : As.name .LDP = "LDP" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wX_r0 hka, eff_wX_r0 hkb]
  rfl

/-- `MOV{D,B,BU,H,HU,W,WU} off(Rn), Rd` with the address in the nil page: the load faults. -/
theorem progStep_loadN_nil {kn kd n : Nat} {sg : Bool} {off : Int} (hkn : kn < 32)
    (hkd : kd < 32) (hn : L.nextAddr p.id = some next)
    (hm : ProgOp.movMem p.as.name = some (n, sg, false)) (hf : p.from_ = memA (REG_R0 + kn) off)
    (hsc : p.scond = 0) (ht : p.to = regA (REG_R0 + kd))
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = true) :
    progStep L p s = .error (.nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off)) := by
  have hma : (ProgCtx.mk L s p).mem p.from_ =
      .ok (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off, none) := by
    rw [hf]; exact ctx_mem_reg hkn hsc
  have he := eff_load (c := ⟨L, s, p⟩) hkd hm (by rw [hf]; rfl) hma ht
  by_cases h : kd = 31 <;>
    simp [progStep, hn, isSkip_of hm, he, effWd, h, Eff.nilAccess?, hnil]

/-- `LDP off(Rn), (Ra, Rb)` with the first address in the nil page: the load faults (at that
address or 8 bytes above, the first of the two `LDP` reads). -/
theorem progStep_ldp_nil {kn ka kb : Nat} {off : Int} (hkn : kn < 32) (hka : ka < 31)
    (hkb : kb < 31) (hn : L.nextAddr p.id = some next) (has : p.as = .LDP)
    (hf : p.from_ = memA (REG_R0 + kn) off) (hsc : p.scond = 0)
    (ht : p.to = pairA (REG_R0 + ka) (REG_R0 + kb))
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = true) :
    ∃ a, progStep L p s = .error (.nilPage a) := by
  have hma := ctx_mem_reg (c := ⟨L, s, p⟩) hkn hsc (off := off)
  rw [← hf] at hma
  have he := eff_ldp (c := ⟨L, s, p⟩) hka hkb has hma ht
  cases h8 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 8) with
  | true =>
    exact ⟨s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 8,
      by simp [progStep, hn, Prog.isSkip, has, he, Eff.nilAccess?, h8]⟩
  | false =>
    exact ⟨s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off,
      by simp [progStep, hn, Prog.isSkip, has, he, Eff.nilAccess?, h8, hnil]⟩

/-- A store of the `MOV` family of `X ks` to the address `a` (as `Progs3`'s private
`eff_store`). -/
private theorem eff_store {c : ProgCtx} {n ks : Nat} {sg : Bool} {a : BitVec 64} (hks : ks < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, sg, false)) (hf : c.p.from_ = regA (REG_R0 + ks))
    (ht : c.p.to.type = .MEM) (hma : c.mem c.p.to = .ok (a, none)) :
    progEffect c = .ok { stores := [(a, n, (c.s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))] } := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := movPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, ht, hma, regA, ctx_x_r0 hks,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- `STP (Rx, Ry)` at the address `A` of its operand (as `Progs4`'s private `eff_stp`). -/
private theorem eff_stp {c : ProgCtx} {kx ky : Nat} {A : BitVec 64} (hkx : kx < 32)
    (hky : ky < 32) (has : c.p.as = .STP) (hf : c.p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky))
    (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, 8, (c.s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8)),
        (A + BitVec.ofNat 64 8, 8, (c.s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))] } := by
  have hname : As.name .STP = "STP" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_x_r0 hkx, ctx_x_r0 hky]
  rfl

/-- `MOV{D,B,H,W} Rs, off(Rn)` with the address in the nil page: the store faults. -/
theorem progStep_storeN_nil {kn ks n : Nat} {sg : Bool} {off : Int} (hkn : kn < 32)
    (hks : ks < 32) (hn : L.nextAddr p.id = some next)
    (hm : ProgOp.movMem p.as.name = some (n, sg, false)) (hf : p.from_ = regA (REG_R0 + ks))
    (hsc : p.scond = 0) (ht : p.to = memA (REG_R0 + kn) off)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = true) :
    progStep L p s = .error (.nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off)) := by
  have hma : (ProgCtx.mk L s p).mem p.to =
      .ok (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off, none) := by
    rw [ht]; exact ctx_mem_reg hkn hsc
  have he := eff_store (c := ⟨L, s, p⟩) hks hm hf (by rw [ht]; rfl) hma
  simp [progStep, hn, isSkip_of hm, he, Eff.nilAccess?, hnil]

/-- `STP (Rx, Ry), off(Rn)` with the first address in the nil page: the store faults. -/
theorem progStep_stp_nil {kn kx ky : Nat} {off : Int} (hkn : kn < 32) (hkx : kx < 32)
    (hky : ky < 32) (hn : L.nextAddr p.id = some next) (has : p.as = .STP)
    (hf : p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky)) (hsc : p.scond = 0)
    (ht : p.to = memA (REG_R0 + kn) off)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = true) :
    progStep L p s = .error (.nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off)) := by
  have hma := ctx_mem_reg (c := ⟨L, s, p⟩) hkn hsc (off := off)
  rw [← ht] at hma
  have he := eff_stp (c := ⟨L, s, p⟩) hkx hky has hf hma
  simp [progStep, hn, Prog.isSkip, has, he, Eff.nilAccess?, hnil]

/-- An opcode name none of `progEffect`'s branches before the acquire-load one takes (as
`GoFV/Proof/Gen/G38.lean`'s private `ldarPre`). -/
private def ldarPreM (name : String) (n : Nat) : Prop :=
  name ∉ ["TEXT", "FUNCDATA", "PCDATA", "NOP"] ∧
  ProgOp.baseOf name ProgOp.binNames = none ∧ ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
  ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
  ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
  ProgOp.baseOf name ["MADD", "MSUB"] = none ∧
  ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] = none ∧
  ProgOp.baseOf name ["EXTR"] = none ∧
  ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] = none ∧
  ProgOp.baseOf name ["CSET", "CSETM"] = none ∧ ProgOp.movMem name = none ∧
  ProgOp.pairOp name = none ∧ ProgOp.startsS name "LDAR" = true ∧
  ProgOp.suffixBytes (ProgOp.dropS name 4) = n

private theorem ldarPreM_of {op : Op} {as : As} {n : Nat} (h : ldar? op = some (as, n)) :
    ldarPreM as.name n := by
  rcases ldar?_some h with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;>
    simp (config := { decide := true }) [ldarPreM]

/-- `LDAR{,W,B} (Rn), Rd` with the address in the nil page: the load faults. -/
theorem progStep_ldar_nil {op : Op} {as : As} {n kn kd : Nat} (hop : ldar? op = some (as, n))
    (hkn : kn < 32) (hkd : kd < 32) (hn : L.nextAddr p.id = some next) (hpa : p.as = as)
    (hf : p.from_ = memA (REG_R0 + kn) 0) (hsc : p.scond = 0) (ht : p.to = regA (REG_R0 + kd))
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0) = true) :
    progStep L p s = .error (.nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0)) := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := ldarPreM_of hop
  have hma : (ProgCtx.mk L s p).mem p.from_ =
      .ok (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0, none) := by
    rw [hf]; exact ctx_mem_reg hkn hsc
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd { loads := [(s.rX (BitVec.ofNat 5 kn) +
      BitVec.ofInt 64 0, n)] } kd
      ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0) n).setWidth 64)) := by
    unfold progEffect
    simp only [hpa, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hma, ht, regA, Eff.ld,
      ProgCtx.load, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
    rw [show p.as.name = as.name from by rw [hpa]]
    rw [h12, ite_eq_left_of_eq_true _ _ (eq_self true), h13]
    simp only [eff_wX_dest hkd]
    rfl
  have hsk : p.isSkip = false := by
    rcases ldar?_some hop with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp [Prog.isSkip, hpa]
  have hnil' : nilPage (s.rX (BitVec.ofNat 5 kn)) = true := by simpa using hnil
  by_cases h : kd = 31 <;> simp [progStep, hn, hsk, he, effWd, h, Eff.nilAccess?, hnil']

end Machine

/-! ## Slice G41 -/

/-- `vkind28` of a load or store with no symbol is `vkind6`'s. -/
theorem vkind28_mem {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : memFaultOp v.op = true) (haux : v.aux = none) (h : vkind28 lc g v = .ok kd) :
    vkind6 lc g v = .ok kd := by
  rcases memFaultOp_cases hop with ho | ho | ho | ho | ho | ho | ho | ho | ho | ho | ho | ho |
    ho <;>
    simpa [vkind28, vkind27, vkind25, vkind24, vkind23, vkind22, vkind21, vkind20, vkind19,
      vkind18, vkind17, vkind16, vkind15, vkind14, vkind13, vkind12, vkind11, vkind10, vkind9,
      vkind8, vkind7, globPair, logSh?, pbOp, Cond.ofOp, storeIdxOp?, loadIdxOp?, icallLead,
      haux, ho] using h

/-- `vkind38` of a load or store is `vkind28`'s. -/
theorem vkind38_mem {lc : LocCtx} {g : G2In} {v : Value} (hop : memFaultOp v.op = true) :
    vkind38 lc g v = vkind28 lc g v := by
  rcases memFaultOp_cases hop with ho | ho | ho | ho | ho | ho | ho | ho | ho | ho | ho | ho |
    ho <;> apply vkind38_eq28 <;> rw [ho] <;> first | rfl | nofun

/-- The kinds of G6 of a load or store with no symbol, the address in a 64-bit register `rn`:
`MOV… off(Rn), Rd` (G1's `MOVD`, G3's narrow loads), `LDP off(Rn), (Ra, Rb)` (G4),
`MOV… Rs, off(Rn)` (G1's `MOVD`, G3's narrow stores) or `STP (Rx, Ry), off(Rn)` (G4). -/
theorem vk6_mem {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (hVK : VK6 lc g v kd)
    (hop : memFaultOp v.op = true) (haux : v.aux = none) :
    ∃ rn pat, argObj lc v 0 = .ok (64, rn) ∧ kd = .prog pat ∧
      ((∃ as n sg r rd, ProgOp.movMem as.name = some (n, sg, false) ∧ objOf? r = some rd ∧
          ∀ p, pat.ok p = true →
            p.as = as ∧ p.from_ = memA rn v.auxInt.toInt ∧ p.to = regA rd ∧ p.scond = 0) ∨
        (∃ ra rb oa ob, ra ≠ zeroReg ∧ rb ≠ zeroReg ∧ objOf? ra = some oa ∧
          objOf? rb = some ob ∧ ∀ p, pat.ok p = true →
            p.as = .LDP ∧ p.from_ = memA rn v.auxInt.toInt ∧ p.to = pairA oa ob ∧ p.scond = 0) ∨
        (∃ as n cs rs sg, ProgOp.movMem as.name = some (n, sg, false) ∧
          argObj lc v 1 = .ok (cs, rs) ∧ ∀ p, pat.ok p = true →
            p.as = as ∧ p.from_ = regA rs ∧ p.to = memA rn v.auxInt.toInt ∧ p.scond = 0) ∨
        (∃ rx ry, argObj lc v 1 = .ok (64, rx) ∧ argObj lc v 2 = .ok (64, ry) ∧
          ∀ p, pat.ok p = true →
            p.as = .STP ∧ p.from_ = pairA rx ry ∧ p.to = memA rn v.auxInt.toInt ∧
              p.scond = 0)) := by
  have hcases := memFaultOp_cases hop
  cases hVK with
  | var hfv _ => rw [hfv.aux] at haux; cases haux
  | g5 h5 =>
    cases h5 with
    | mark hmk =>
      rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at hmk <;>
        cases hmk
    | g4 _ h4 =>
      cases h4 with
      | ldp _ _ _ _ _ _ _ _ hao _ _ _ hza hzb _ _ hoa hob =>
        refine ⟨_, _, hao, rfl, Or.inr (Or.inl ⟨_, _, _, _, hza, hzb, hoa, hob, fun p hp => ?_⟩)⟩
        obtain ⟨has, hf, -, ht, hsc⟩ := Shape.ok_eq hp
        exact ⟨has, hf, ht, hsc⟩
      | stp _ _ _ _ _ hao hxo hyo _ =>
        refine ⟨_, _, hao, rfl, Or.inr (Or.inr (Or.inr ⟨_, _, hxo, hyo, fun p hp => ?_⟩))⟩
        obtain ⟨has, hf, -, ht, hsc⟩ := Shape.ok_eq hp
        exact ⟨has, hf, ht, hsc⟩
      | sel hsel =>
        rcases hsel with ⟨ho, -⟩ | ⟨ho, -⟩ <;>
          rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at ho <;>
          cases ho
      | g3 hnldp hnstp _ _ h3 =>
        cases h3 with
        | g2 hcond _ h2 =>
          rcases hcond with ⟨hld, hst, -⟩ | ⟨hmd, -⟩
          · rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
              rw [h] at hld hst hnldp hnstp <;>
              first
                | exact absurd rfl hnldp
                | exact absurd rfl hnstp
                | simp [loadOp?, narrowLoad?, storeOp?, narrowStore?] at hld hst
          · cases h2 with
            | g1 _ _ _ _ _ hvk =>
              cases hvk with
              | load _ _ _ hao _ hro _ =>
                obtain ⟨r, -, -, hor, -⟩ := resObj_spec hro
                refine ⟨_, _, hao, rfl, Or.inl ⟨.MOVD, 8, false, r, _, rfl, hor, fun p hp => ?_⟩⟩
                obtain ⟨has, hf, -, ht, hsc⟩ := Shape.ok_eq hp
                exact ⟨has, hf, ht, hsc⟩
              | store _ _ _ _ _ hao hso _ _ =>
                refine ⟨_, _, hao, rfl,
                  Or.inr (Or.inr (Or.inl ⟨.MOVD, 8, _, _, false, rfl, hso, fun p hp => ?_⟩))⟩
                obtain ⟨has, hf, -, ht, hsc⟩ := Shape.ok_eq hp
                exact ⟨has, hf, ht, hsc⟩
              | _ => rcases hmd with h | h <;> simp_all
            | _ => rcases hmd with h | h <;> simp_all
        | load hld _ _ hacc _ hro _ hpat =>
          cases hacc with
          | reg _ hao =>
            obtain ⟨r, -, -, hor, -⟩ := resObj_spec hro
            refine ⟨_, _, hao, rfl,
              Or.inl ⟨_, _, _, r, _, loadOp?_movMem hld, hor, fun p hp => ?_⟩⟩
            obtain ⟨has, hf, -, ht, hsc, -, -⟩ := hpat p hp
            exact ⟨has, hf, ht, hsc⟩
          | glob hx => rw [hx] at haux; cases haux
        | store hst _ _ _ _ hacc hso _ _ hpat =>
          cases hacc with
          | reg _ hao =>
            obtain ⟨sg, hmov⟩ := storeOp?_movMem hst
            refine ⟨_, _, hao, rfl,
              Or.inr (Or.inr (Or.inl ⟨_, _, _, _, sg, hmov, hso, fun p hp => ?_⟩))⟩
            obtain ⟨has, hf, -, ht, hsc, -, -⟩ := hpat p hp
            exact ⟨has, hf, ht, hsc⟩
          | glob hx => rw [hx] at haux; cases haux
        | _ =>
          exfalso
          rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
            simp_all [extOp?]

/-- **A load or store of slice G60 that faults**: from a `LocMatch`ed P0 state, a load or store
whose `runLoc` step panics (with `nilDeref`, `stepLoc_mem_panic`) is matched by the no-ops before
its Prog, which faults in the nil page (`PPanics`). -/
theorem g60_memPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm : Mem} {osp : Bool}
    (hc : checkG60L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : memFaultOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp)
    (hsp : lc.ctx.f.lowered = true → take48 lc v = true → SPInv E s ∧ E.outSP = true)
    (hs : stepLoc env lc s v = .panic e mm) :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨rfl, a0, x, b0, p, ha0, hx, hb0, hbn, hp, hpf⟩ := stepLoc_mem_panic hop hs
  have haux := stepLoc_mem_panic_aux hop hs
  have hcases := memFaultOp_cases hop
  have hen : entryOp24 v.op = false := by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl
  refine ⟨rfl, ?_⟩
  cases hl0 : lc.ctx.f.lowered with
  | false =>
    rcases nl30_ops (checkNL30_of_60L hl0 hc) hbid hb hi hv hen with
      h | h | h | h <;>
      rcases hcases with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;>
      rw [h] at h' <;> cases h'
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, hfr⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -, -, -⟩ :=
    checkG60L_spec hl0 hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  have h7x : op57a v.op = false ∧ op57b v.op = false ∧ op58a v.op = false ∧ op59p v.op = false := by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
      exact ⟨rfl, rfl, rfl, rfl⟩
  have h5x : op56 v.op = false ∧ op55a v.op = false ∧ op55b v.op = false ∧
      op52b v.op = false ∧ op53a v.op = false ∧ op54a v.op = false := by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hvk] at hkd
  -- an access off `SP` (G48's `kind48`) does not fault: its base relates to `SP` (`SPInv`), above
  -- the nil page (`FrameOK`)
  have hkd := (vkind60_ok49 h7x.1 h7x.2.1 h7x.2.2.1 h7x.2.2.2 h5x.1 h5x.2.1 h5x.2.2.1
    h5x.2.2.2.1 h5x.2.2.2.2.1 h5x.2.2.2.2.2 hkd).resolve_right fun ⟨_, hk48⟩ => by
      rcases kind48_cases hk48 with ⟨hc0, -⟩ | ⟨-, hax, hspa, hsb, -⟩
      · rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at hc0 <;>
          cases hc0
      · obtain ⟨hspI, hosp⟩ := hsp hl0 (by simp [take48, hax, hspa, hsb])
        have hR := kread_of_reads (((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv)
        have hnp : v.op ≠ .Phi := fun h => by rw [h] at hop; exact absurd hop (by decide)
        obtain ⟨hxr, hxf⟩ := sp_base48 hl hA hspI hosp hinv.core.regs hR hnp hsb a0 x ha0 hx
        obtain ⟨mm0, -, hMI⟩ := hm.mem
        obtain ⟨hbb, hbo⟩ : b0.blk = .nil ∧ b0.off = 0 := by simpa [Ptr.isNil] using hbn
        have h0 := nil_word hMI.nil hxr hxf hb0 hbb hbo
        have hlo := hfr.lo
        rw [h0] at hlo
        simp at hlo
  rw [vkind49_eq51 (frameVar49?_none haux),
    vkind51_eq50
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl)
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl)
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl),
    vkind50_eq47
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl)
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> nofun)
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> nofun),
    vkind47_eq46
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> nofun)
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl)
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> nofun),
    vkind46_eq45 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
      simp [fops46]),
    vkind45_eq44 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl)
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl),
    vkind44_eq43 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl),
    vkind43_eq42 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> nofun),
    vkind42_eq41 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> nofun),
    vkind41_eq40 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> nofun)
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl),
    vkind40_eq38 (by
    rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> nofun),
    vkind38_mem hop] at hkd
  obtain ⟨-, hVK⟩ := vkind6_spec (vkind28_mem hop haux hkd)
    (by rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl)
  obtain ⟨rn, pat, hao, rfl, hshape⟩ := vk6_mem hVK hop haux
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have hR : KRead c.cx.lc v (kAt c.cx.lc kt bid blk i).get := kread_of_reads hreads
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hnp : v.op ≠ .Phi := fun h => by rw [h] at hop; exact absurd hop (by decide)
  -- the base, nil in a register: the machine word 0
  obtain ⟨a0', r0, ha0', hah0, hor0, hca0⟩ := argObj_spec hao
  rw [ha0] at ha0'
  cases ha0'
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv.core hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  rw [hx] at hX
  cases hX
  obtain ⟨mm0, -, hMI⟩ := hm.mem
  have hsym : Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p := by
    rw [← hp]; unfold symAddr; rw [haux]
  have hnil := nil_fault_page hMI.nil hxv hxf hb0 hbn hsym hpf
  -- the machine: no-ops, then the access, which faults
  obtain ⟨k, -, hk', hokp, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  have hne : ({ m with pc := pcAt text c.cx.ps.toList k } : MState).pc ≠ ret := fun hr =>
    F.ret _ (List.getElem_mem hk') (by rw [addr_pcAt hk']; exact congrArg some hr)
  rcases hshape with ⟨as, n, sg, r, rd, hmov, hor, hpat⟩ |
      ⟨ra, rb, oa, ob, hza, hzb, hoa, hob, hpat⟩ | ⟨as, n, cs, rs, sg, hmov, hso, hpat⟩ |
      ⟨rx, ry, hxo, hyo, hpat⟩
  · obtain ⟨has, hf, ht, hsc⟩ := hpat _ hokp
    obtain ⟨kd, hkd, rfl, -⟩ := objOf?_some hor
    exact ⟨_, hstar, hne, .inl ⟨_, _, progAt?_pcAt F.nodup F.lt hk',
      progStep_loadN_nil hkn hkd (nextAddr_pcAt F.nodup hk') (by rw [has]; exact hmov) hf hsc ht
        hnil, rfl⟩⟩
  · obtain ⟨has, hf, ht, hsc⟩ := hpat _ hokp
    obtain ⟨ka, -, rfl, hka⟩ := objOf?_some hoa
    obtain ⟨kb, -, rfl, hkb⟩ := objOf?_some hob
    have hka' : ka < 31 := hka.elim (fun h => absurd h.1 hza) (fun h => h.1)
    have hkb' : kb < 31 := hkb.elim (fun h => absurd h.1 hzb) (fun h => h.1)
    obtain ⟨a, ha⟩ := progStep_ldp_nil (s := { m with pc := pcAt text c.cx.ps.toList k }) hkn hka'
      hkb' (nextAddr_pcAt F.nodup hk') has hf hsc ht hnil
    exact ⟨_, hstar, hne, .inl ⟨_, _, progAt?_pcAt F.nodup F.lt hk', ha, rfl⟩⟩
  · obtain ⟨has, hf, ht, hsc⟩ := hpat _ hokp
    obtain ⟨a1, r1, -, -, hor1, -⟩ := argObj_spec hso
    obtain ⟨ks, hks, rfl, -⟩ := objOf?_some hor1
    exact ⟨_, hstar, hne, .inl ⟨_, _, progAt?_pcAt F.nodup F.lt hk',
      progStep_storeN_nil hkn hks (nextAddr_pcAt F.nodup hk') (by rw [has]; exact hmov) hf hsc ht
        hnil, rfl⟩⟩
  · obtain ⟨has, hf, ht, hsc⟩ := hpat _ hokp
    obtain ⟨a1, r1, -, -, hor1, -⟩ := argObj_spec hxo
    obtain ⟨kx, hkx, rfl, -⟩ := objOf?_some hor1
    obtain ⟨a2, r2, -, -, hor2, -⟩ := argObj_spec hyo
    obtain ⟨ky, hky, rfl, -⟩ := objOf?_some hor2
    exact ⟨_, hstar, hne, .inl ⟨_, _, progAt?_pcAt F.nodup F.lt hk',
      progStep_stp_nil hkn hkx hky (nextAddr_pcAt F.nodup hk') has hf hsc ht hnil, rfl⟩⟩

/-- **A load or store of slice G60 that faults, down to the machine words**: machine steps of the
linked code to a state that panics with `nilDeref` (the access's nil-page fault, `MPanics`). -/
theorem g60_obj_memPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {mm : Mem} {osp : Bool} {spills : Array Spill} {o : ObjIn} {otab : Tab}
    {base : BitVec 64}
    {code : Code} {retM : BitVec 64} {t : MState}
    (hc : checkG60L lc ps bstart g = .ok (tab, kt))
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : memFaultOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp)
    (hsp : lc.ctx.f.lowered = true → take48 lc v = true → SPInv E s ∧ E.outSP = true)
    (hs : stepLoc env lc s v = .panic e mm)
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    e = .nilDeref ∧ ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e := by
  obtain ⟨he, m', hp, hpp⟩ := g60_memPanic (H := H) hc hE hbid hb hi hv hop hm hinv hsp hs
  obtain ⟨t1, ht1, hR1, hI1⟩ := obj_star hO hH hp hR (locMatch_inv hE.env.env.env.env hm) hic
  obtain ⟨t2, ht2, hpan⟩ := obj_panic hO hHP hR1 (hI1.resolve_right hpp.1) hpp
  exact ⟨he, t2, mstar_trans ht1 ht2, hpan⟩

/-- **An acquire load of slice G60 that faults**: from a `LocMatch`ed P0 state, an acquire load
whose `runLoc` step panics (with `nilDeref`, `stepLoc_ldar_panic`) is matched by the no-ops before
its Prog, `LDAR* (Rn)`, which faults in the nil page (`PPanics`). -/
theorem g60_ldarPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm : Mem} {osp : Bool}
    (hc : checkG60L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : (ldar? v.op).isSome = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .panic e mm) :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨as, n⟩, hop⟩ := Option.isSome_iff_exists.1 hop
  obtain ⟨rfl, a0, x, b0, ha0, hx, hb0, hbn, hpf⟩ := stepLoc_ldar_panic hop hs
  have hen : entryOp24 v.op = false := by
    rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
  refine ⟨rfl, ?_⟩
  cases hl0 : lc.ctx.f.lowered with
  | false =>
    rcases nl30_ops (checkNL30_of_60L hl0 hc) hbid hb hi hv hen with h | h | h | h <;>
      rcases ldar?_some hop with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h] at h' <;> cases h'
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -, -, -⟩ :=
    checkG60L_spec hl0 hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  have h7x : op57a v.op = false ∧ op57b v.op = false ∧ op58a v.op = false ∧ op59p v.op = false := by
    rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have h5x : op56 v.op = false ∧ op55a v.op = false ∧ op55b v.op = false ∧
      op52b v.op = false ∧ op53a v.op = false ∧ op54a v.op = false := by
    rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hvk] at hkd
  -- G48's `kind48` takes no acquire load
  have hkd := (vkind60_ok49 h7x.1 h7x.2.1 h7x.2.2.1 h7x.2.2.2 h5x.1 h5x.2.1 h5x.2.2.1
    h5x.2.2.2.1 h5x.2.2.2.2.1 h5x.2.2.2.2.2 hkd).resolve_right fun ⟨_, hk48⟩ => by
      rcases kind48_cases hk48 with ⟨hc0, -⟩ | ⟨-, -, -, -, hk'⟩
      · rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hc0 <;> cases hc0
      · have ho := (spKind48_spec hk').ops
        rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at ho <;>
          simp [loadOp?, storeOp?, narrowLoad?, narrowStore?] at ho
  have hkd := vkind49_ok51
    (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun)
    (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
    (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
    (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun)
    (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun) hkd
  rw [vkind51_eq50 (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
      (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
      (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl),
    vkind50_eq47 (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
      (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun)
      (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun),
    vkind47_eq46 (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun)
      (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
      (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun),
    vkind46_eq45 (by
      rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> simp [fops46]),
    vkind45_eq44 (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
      (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl),
    vkind44_eq43 (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl),
    vkind43_eq42 (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun),
    vkind42_eq41 (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun),
    vkind41_eq40 (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun)
      (by rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)] at hkd
  obtain ⟨-, hVK⟩ := vkind40_spec hkd hen
  cases hVK with
  | g37 hn _ _ => rw [hop] at hn; cases hn
  | sel0 h => rw [h] at hop; cases hop
  | sel1 h => rw [h] at hop; cases hop
  | ldar hop' _ _ _ _ _ hao _ _ _ _ hor =>
  rw [hop] at hop'
  cases hop'
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have hR : KRead c.cx.lc v (kAt c.cx.lc kt bid blk i).get := kread_of_reads hreads
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hnp : v.op ≠ .Phi := (ldar_ne hop).1
  -- the address, nil in a register: the machine word 0
  obtain ⟨a0', r0, ha0', hah0, hor0, hca0⟩ := argObj_spec hao
  rw [ha0] at ha0'
  cases ha0'
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv.core hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  rw [hx] at hX
  cases hX
  obtain ⟨mm0, -, hMI⟩ := hm.mem
  have hnil := nil_fault_page hMI.nil hxv hxf hb0 hbn hb0 hpf
  -- the machine: no-ops, then the acquire load, which faults
  obtain ⟨k, -, hk', hokp, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  have hne : ({ m with pc := pcAt text c.cx.ps.toList k } : MState).pc ≠ ret := fun hr =>
    F.ret _ (List.getElem_mem hk') (by rw [addr_pcAt hk']; exact congrArg some hr)
  obtain ⟨has, hf, -, ht, hsc, -, -⟩ := plain_spec hokp
  simp only [beq_iff_eq] at hf ht
  obtain ⟨kr, hkr, rfl, -⟩ := objOf?_some hor
  exact ⟨_, hstar, hne, .inl ⟨_, _, progAt?_pcAt F.nodup F.lt hk',
    progStep_ldar_nil hop hkn hkr (nextAddr_pcAt F.nodup hk') has hf hsc ht hnil, rfl⟩⟩

/-- **An acquire load of slice G60 that faults, down to the machine words**: machine steps of the
linked code to a state that panics with `nilDeref` (the `LDAR*`'s nil-page fault, `MPanics`). -/
theorem g60_obj_ldarPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {mm : Mem} {osp : Bool} {spills : Array Spill} {o : ObjIn} {otab : Tab}
    {base : BitVec 64}
    {code : Code} {retM : BitVec 64} {t : MState}
    (hc : checkG60L lc ps bstart g = .ok (tab, kt))
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : (ldar? v.op).isSome = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .panic e mm)
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    e = .nilDeref ∧ ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e := by
  obtain ⟨he, m', hp, hpp⟩ := g60_ldarPanic (H := H) hc hE hbid hb hi hv hop hm hinv hs
  obtain ⟨t1, ht1, hR1, hI1⟩ := obj_star hO hH hp hR (locMatch_inv hE.env.env.env.env hm) hic
  obtain ⟨t2, ht2, hpan⟩ := obj_panic hO hHP hR1 (hI1.resolve_right hpp.1) hpp
  exact ⟨he, t2, mstar_trans ht1 ht2, hpan⟩

end GoFV.Proof.Obj
