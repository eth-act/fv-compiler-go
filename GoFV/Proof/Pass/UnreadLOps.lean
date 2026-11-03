import GoFV.Proof.Pass.UnreadLSrc

/-!
# elim unread autos on `runL`: the kept memory ops on related memories

A kept value of `armMemOps` reads equal registers but its memory, and the memories are equal
outside the eliminated variables `U` (`Mem.EqOff U M M'`): it evaluates to related results
(`armMemOp_rel`, `ResRel`): loads read outside `U` (their address avoids `U`: an argument that
avoids `U` or a symbol that is no eliminated variable, `SymOK`), stores and the other writes write
the same bytes on both sides (`EqOff.write`), calls go through dead auto elim's `callOp_rel`
(the register pieces of the arguments are fitted independently of the memory, `callArgs_snoc`),
nil checks and bounds panics panic alike. Registers related by `VR` stay related through
`Val.widen` and the lowered shaping (`VR.mdRetype`).
-/

namespace GoFV.Proof.UnreadL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.DAE

variable {U : Blk → Prop}

/-! ## Related registers at lowered shapes -/

mutual
theorem VR.widen : {a b : Val} → VR U a b → (t : Ty) → VR U (a.widen t) (b.widen t)
  | _, _, .refl _, _ => .refl _
  | _, _, .mem h, t => by
    have e : ∀ m : Mem, (Val.mem m).widen t = .mem m := fun m => by cases t <;> simp [Val.widen]
    rw [e, e]; exact .mem h
  | _, _, .tuple (vs := vs) (ws := ws) h, t => by
    cases t with
    | tuple ts => simp only [Val.widen]; exact .tuple (VRL.widenList h ts)
    | _ => simp only [Val.widen]; exact .tuple h
theorem VRL.widenList : {as bs : List Val} → VRL U as bs → (ts : List Ty) →
    VRL U (Val.widenList ts as) (Val.widenList ts bs)
  | _, _, .nil, ts => by cases ts <;> simp only [Val.widenList] <;> exact .nil
  | _, _, .cons h t, [] => by simp only [Val.widenList]; exact .cons h t
  | _, _, .cons h t, t0 :: ts => by
    simp only [Val.widenList]; exact .cons (VR.widen h t0) (VRL.widenList t ts)
end

theorem VR.retypeL {a b : Val} (h : VR U a b) (t : Ty) : VR U (a.retypeL t) (b.retypeL t) :=
  VR.retype (VR.widen h t) t

theorem VR.mdRetype {a b : Val} (h : VR U a b) (md : LMode) (t : Ty) :
    VR U (md.retype t a) (md.retype t b) := by
  unfold LMode.retype; split
  · exact VR.retypeL h t
  · exact h.retype t

/-! ## Argument lists ending in a memory -/

theorem snoc1 {L : List Val} {x y : Val} : L ++ [x] = [y] ↔ L = [] ∧ x = y := by
  cases L with
  | nil => simp
  | cons a L => cases L <;> simp
theorem snoc2 {L : List Val} {x a y : Val} : L ++ [x] = [a, y] ↔ L = [a] ∧ x = y := by
  rcases L with _ | ⟨b, _ | ⟨c, L⟩⟩ <;> simp
theorem snoc3 {L : List Val} {x a b y : Val} : L ++ [x] = [a, b, y] ↔ L = [a, b] ∧ x = y := by
  rcases L with _ | ⟨c, _ | ⟨d, _ | ⟨e, L⟩⟩⟩ <;> simp [and_assoc]
theorem snoc4 {L : List Val} {x a b c y : Val} :
    L ++ [x] = [a, b, c, y] ↔ L = [a, b, c] ∧ x = y := by
  rcases L with _ | ⟨d, _ | ⟨e, _ | ⟨g, _ | ⟨k, L⟩⟩⟩⟩ <;> simp [and_assoc]

/-! ## Loads and writes -/

theorem loadN_eq {M M' : Mem} (hM : Mem.EqOff U M M') {p : Ptr} (hp : ¬ U p.blk) (ty : Ty)
    (n : Nat) (sg : Bool) : Arm64.loadN ty n sg M' p = Arm64.loadN ty n sg M p := by
  unfold Arm64.loadN; simp only [EqOff.load hM _ p hp]

theorem load16_eq {M M' : Mem} (hM : Mem.EqOff U M M') {p : Ptr} (hp : ¬ U p.blk) :
    Arm64.load16 M' p = Arm64.load16 M p := by
  unfold Arm64.load16; rw [EqOff.read hM p _ hp]

theorem loadPair_eq {M M' : Mem} (hM : Mem.EqOff U M M') {p : Ptr} (hp : ¬ U p.blk) (ty : Ty)
    (n : Nat) (sg : Bool) : Arm64.loadPair ty n sg M' p = Arm64.loadPair ty n sg M p := by
  have hp' : ∀ k, ¬ U (p.add k).blk := fun k => by rw [add_ptr_blk]; exact hp
  unfold Arm64.loadPair
  rw [load16_eq hM hp, load16_eq hM (hp' _), loadN_eq hM hp, loadN_eq hM (hp' _)]

theorem elim_ld_eq {ctx : Ctx} {v : Value} (hs : SymOK U ctx v) {a : Val} (ha : Val.Avoids U a)
    {M M' : Mem} (hM : Mem.EqOff U M M') (ty : Ty) (n : Nat) (sg : Bool) :
    (symAddr ctx v a).elim .poison (Arm64.loadN ty n sg M') =
      (symAddr ctx v a).elim .poison (Arm64.loadN ty n sg M) := by
  cases hp : symAddr ctx v a with
  | none => rfl
  | some p => exact loadN_eq hM (hs a p ha hp) ty n sg

theorem elim_ldPair_eq {ctx : Ctx} {v : Value} (hs : SymOK U ctx v) {a : Val}
    (ha : Val.Avoids U a) {M M' : Mem} (hM : Mem.EqOff U M M') (ty : Ty) (n : Nat) (sg : Bool) :
    (symAddr ctx v a).elim .poison (Arm64.loadPair ty n sg M') =
      (symAddr ctx v a).elim .poison (Arm64.loadPair ty n sg M) := by
  cases hp : symAddr ctx v a with
  | none => rfl
  | some p => exact loadPair_eq hM (hs a p ha hp) ty n sg

theorem elim_ld16_eq {ctx : Ctx} {v : Value} (hs : SymOK U ctx v) {a : Val}
    (ha : Val.Avoids U a) {M M' : Mem} (hM : Mem.EqOff U M M') :
    (symAddr ctx v a).elim .poison (Arm64.load16 M') =
      (symAddr ctx v a).elim .poison (Arm64.load16 M) := by
  cases hp : symAddr ctx v a with
  | none => rfl
  | some p => exact load16_eq hM (hs a p ha hp)

/-- The same write on related memories. -/
theorem writeRes_rel {what : String} {M M' : Mem} (hM : Mem.EqOff U M M') {p : Ptr}
    {bs : Array Byte} {y : Val} (h : writeRes what (M.write p bs) = .ok y) :
    ∃ y', writeRes what (M'.write p bs) = .ok y' ∧ VR U y y' := by
  cases hw : M.write p bs with
  | none => rw [hw] at h; cases h
  | some M1 =>
    rw [hw] at h; cases h
    obtain ⟨M1', hw', hM1⟩ := EqOff.write hM hw
    exact ⟨_, by rw [hw']; rfl, .mem hM1⟩

/-! ## Calls -/

theorem fitPiece_mem (t : Ty) (M : Mem) : fitPiece t (.mem M) = .mem M := by
  unfold fitPiece; split <;> simp_all

theorem fitPieces_nil (tabs : Tables) : ∀ ps : List ABIParam, fitPieces tabs ps [] = []
  | [] => rfl
  | p :: ps => by
    unfold fitPieces
    split
    · exact fitPieces_nil tabs ps
    · simp [fitPieces_nil tabs ps]

/-- The register pieces of a call are fitted independently of its memory. -/
theorem fitPieces_snoc (tabs : Tables) :
    ∀ (ps : List ABIParam) (P : List Val) (M : Mem),
      fitPieces tabs ps (P ++ [.mem M]) = fitPieces tabs ps P ++ [.mem M]
  | [], P, M => rfl
  | p :: ps, P, M => by
    unfold fitPieces
    split
    · exact fitPieces_snoc tabs ps P M
    · dsimp only
      by_cases hk : p.regs.size ≤ P.length
      · rw [List.take_append_of_le_length hk, List.drop_append_of_le_length hk,
          fitPieces_snoc tabs ps, List.append_assoc]
      · rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by omega),
          List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by omega),
          fitPieces_nil, List.append_nil, List.append_nil, List.mapIdx_append]
        simp only [List.mapIdx_cons, List.mapIdx_nil, List.append_cancel_left_eq, List.cons.injEq,
          and_true]
        split <;> simp [fitPiece_mem]

/-- A call's argument list on `L ++ [mem]`: a list independent of the memory, then the memory. -/
theorem callArgs_snoc (hU : TempU U) (k : Nat) (tabs : Tables) (ins : List ABIParam)
    {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) :
    ∃ A, (∀ z ∈ A, Val.Avoids U z) ∧ ∀ M : Mem,
      (L ++ [Val.mem M]).take k ++ fitPieces tabs ins ((L ++ [Val.mem M]).drop k) = A ++ [Val.mem M] := by
  by_cases hk : k ≤ L.length
  · refine ⟨L.take k ++ fitPieces tabs ins (L.drop k), callArgs_av hU k tabs ins hL, fun M => ?_⟩
    rw [List.take_append_of_le_length hk, List.drop_append_of_le_length hk, fitPieces_snoc,
      List.append_assoc]
  · refine ⟨L, hL, fun M => ?_⟩
    rw [List.take_of_length_le (by simp; omega), List.drop_eq_nil_of_le (by simp; omega),
      fitPieces_nil, List.append_nil]

/-- A call on related memories (the arguments before the memory avoid `U`). -/
theorem call_rel {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx} {w : Value}
    {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem} (hM : Mem.EqOff U M M')
    (hMA : M.Avoids U) {k : Nat} {tabs : Tables} {ins : List ABIParam} :
    CallRel U (callOp env ctx w ((L ++ [Val.mem M]).take k ++
        fitPieces tabs ins ((L ++ [Val.mem M]).drop k)))
      (callOp env ctx w ((L ++ [Val.mem M']).take k ++
        fitPieces tabs ins ((L ++ [Val.mem M']).drop k))) := by
  obtain ⟨A, hA, hAe⟩ := callArgs_snoc hU k tabs ins hL
  rw [hAe, hAe]
  exact callOp_rel hfs hU (.mem hM) (fun z hz => by
    rcases List.mem_append.1 hz with hz | hz
    · exact hA z hz
    · simp at hz; subst hz; exact hMA)

/-! ## The arm64 memory ops `arm64Op` evaluates -/

/-- The kept memory ops `arm64Op` evaluates by an arm of its own. -/
def armA : List Op :=
  [.ARM64MOVBload, .ARM64MOVBUload, .ARM64MOVHload, .ARM64MOVHUload, .ARM64MOVWload,
    .ARM64MOVWUload, .ARM64MOVDload, .ARM64FMOVSload, .ARM64FMOVDload, .ARM64FMOVQload,
    .ARM64LDP, .ARM64LDPW, .ARM64LDPSW, .ARM64FLDPD, .ARM64FLDPS, .ARM64FLDPQ,
    .ARM64MOVBstore, .ARM64MOVHstore, .ARM64MOVWstore, .ARM64MOVDstore, .ARM64FMOVSstore,
    .ARM64FMOVDstore, .ARM64FMOVQstore, .ARM64STP, .ARM64STPW, .ARM64FSTPD, .ARM64FSTPS,
    .ARM64FSTPQ,
    .ARM64MOVBstoreidx, .ARM64MOVHstoreidx, .ARM64MOVWstoreidx, .ARM64MOVDstoreidx,
    .ARM64FMOVSstoreidx, .ARM64FMOVDstoreidx, .ARM64MOVHstoreidx2, .ARM64MOVWstoreidx4,
    .ARM64MOVDstoreidx8, .ARM64FMOVSstoreidx4, .ARM64FMOVDstoreidx8,
    .ARM64CALLstatic, .ARM64CALLclosure, .ARM64CALLinter, .ARM64LoweredNilCheck,
    .ARM64LoweredPanicBoundsRR, .ARM64LoweredPanicBoundsRC, .ARM64LoweredPanicBoundsCR,
    .ARM64LoweredPanicBoundsCC, .ARM64LoweredMemEq, .ARM64DMB, .ARM64PRFM]

/-- **A kept memory op of `arm64Op` that returns** on related memories. -/
theorem armA_ok {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx} {fr : Frame}
    {v : Value} {ty : Ty} (hs : SymOK U ctx v) (hop : v.op ∈ armA) {L : List Val}
    (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem} (hM : Mem.EqOff U M M') (hMA : M.Avoids U) :
    ∀ y, arm64Op false env ctx fr v (L ++ [.mem M]) ty = .ok y →
      ∃ y', arm64Op false env ctx fr v (L ++ [.mem M']) ty = .ok y' ∧ VR U y y' := by
  intro y h
  unfold arm64Op at h ⊢
  simp only [nilFaults, Bool.not_false, ite_true] at h ⊢
  generalize v.op = op at h hop ⊢
  split at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | exact absurd hop (by decide)
    | exact absurd h panicBounds_not_ok
    | exact ((call_rel hfs hU hL hM hMA).1 y h).2
    | (have := (nilCheck_rel (U := U) (ctx := ctx) (v := {v with op := .NilCheck}) rfl (L := L)
          (.mem hM)).1 y h
       exact ⟨y, this.1, .refl y⟩)
    | (cases h; exact ⟨_, rfl, by rw [memEq_eq hU L (.mem hM) hL]; exact .refl _⟩)
    | (simp only [snoc1, snoc2, snoc3, snoc4, Val.mem.injEq] at *
       rcases ‹L = _ ∧ _› with ⟨rfl, rfl⟩
       simp only [List.cons_append, List.nil_append] at *
       try simp only [‹symAddr ctx v _ = some _›]
       try simp only [‹Arm64.addr _ 0 = some _›]
       first
         | exact writeRes_rel hM h
         | (cases h
            first
              | exact ⟨_, rfl, by rw [elim_ld_eq hs (hL _ (by simp)) hM]; exact .refl _⟩
              | exact ⟨_, rfl, by rw [elim_ldPair_eq hs (hL _ (by simp)) hM]; exact .refl _⟩
              | exact ⟨_, rfl, by rw [elim_ld16_eq hs (hL _ (by simp)) hM]; exact .refl _⟩
              | exact ⟨_, rfl, .mem hM⟩))
    | (simp only [snoc1, snoc2, snoc3, snoc4, Val.mem.injEq] at *
       cases h
       split <;> simp only [snoc1, snoc2, snoc3, snoc4, Val.mem.injEq] at * <;>
         first | exact ⟨_, rfl, .refl _⟩ | (exfalso; simp_all; done))
    | (exfalso; simp only [armA, List.mem_cons, List.not_mem_nil, or_false] at hop; simp_all; done)

/-- **A kept memory op of `arm64Op` that panics** panics alike on related memories. -/
theorem armA_panic {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx} {fr : Frame}
    {v : Value} {ty : Ty} (hop : v.op ∈ armA) {L : List Val}
    (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem} (hM : Mem.EqOff U M M') (hMA : M.Avoids U) :
    ∀ e m, arm64Op false env ctx fr v (L ++ [.mem M]) ty = .panic e m →
      ∃ m', arm64Op false env ctx fr v (L ++ [.mem M']) ty = .panic e m' ∧ Mem.EqOff U m m' := by
  intro e m h
  unfold arm64Op at h ⊢
  simp only [nilFaults, Bool.not_false, ite_true] at h ⊢
  generalize v.op = op at h hop ⊢
  split at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | exact absurd hop (by decide)
    | exact absurd h (by unfold writeRes; split <;> nofun)
    | exact ((call_rel hfs hU hL hM hMA).2 e m h).2.2
    | exact (nilCheck_rel (U := U) (ctx := ctx) (v := {v with op := .NilCheck}) rfl (L := L)
          (.mem hM)).2 e m h
    | exact panicBounds_rel (.mem hM) h
    | (simp only [snoc1, snoc2, snoc3, snoc4, Val.mem.injEq] at *
       rcases ‹L = _ ∧ _› with ⟨rfl, rfl⟩
       simp only [List.cons_append, List.nil_append] at *
       simp only [*]
       first
         | exact panicBounds_rel (L := [_, _]) (.mem hM) h
         | exact panicBounds_rel (L := [_]) (.mem hM) h
         | exact panicBounds_rel (L := [_, _, _]) (.mem hM) h)
    | (exfalso; simp only [armA, List.mem_cons, List.not_mem_nil, or_false] at hop; simp_all; done)

/-! ## The arm64 memory ops `Arm64.evalPure` evaluates -/

/-- A write that fails on one memory fails on a memory with the same allocations. -/
theorem EqOff.write_none {M M' : Mem} (hM : Mem.EqOff U M M') {p : Ptr} {bs : Array Byte}
    (h : M.write p bs = none) : M'.write p bs = none := by
  unfold Mem.write at h ⊢
  by_cases he : bs.isEmpty = true
  · simp [he] at h
  simp only [he, Bool.false_eq_true, ite_false] at h ⊢
  rcases EqOff.find hM p.blk with ⟨h1, h2⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h2]; rfl
  · rw [ha] at h
    rw [ha']
    obtain ⟨-, hs, hwr, -⟩ := hA
    simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
    dsimp only at hs hwr
    rw [hwr, hs]
    split at h
    · cases h
    · rename_i hc; simp only [hc]; rfl

/-- The same write on related memories, or both fail. -/
theorem write_vr {M M' : Mem} (hM : Mem.EqOff U M M') (p : Ptr) (bs : Array Byte) :
    VR U (match M.write p bs with | some m' => .mem m' | none => .poison)
      (match M'.write p bs with | some m' => .mem m' | none => .poison) := by
  cases hw : M.write p bs with
  | none => rw [EqOff.write_none hM hw]; exact .refl _
  | some M1 =>
    obtain ⟨M1', hw', hM1⟩ := EqOff.write hM hw
    rw [hw']; exact .mem hM1

theorem idxBase_av (hU : TempU U) (scale : Nat) {a i : Val} (ha : Val.Avoids U a)
    (hi : Val.Avoids U i) :
    Val.Avoids U (if scale = 1 then Arm64.add .other [a, i] else
      match Arm64.reg i with
      | some k => Arm64.add .other [a, .int .w64 (k * BitVec.ofNat 64 scale)]
      | none => .poison) := by
  split
  · exact add_av _ fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> assumption
  · split
    · exact add_av _ fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact ha
        · trivial
    · trivial

theorem loadIdx_eq (hU : TempU U) {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem}
    (hM : Mem.EqOff U M M') (ty : Ty) (n scale : Nat) (sg : Bool) :
    Arm64.loadIdx ty n scale sg (L ++ [.mem M']) = Arm64.loadIdx ty n scale sg (L ++ [.mem M]) := by
  rcases L with _ | ⟨a, _ | ⟨i, _ | ⟨b, L⟩⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, Arm64.loadIdx]
  rotate_left
  · repeat' split
    all_goals first | rfl | (exfalso; simp_all; done)
  have hs := idxBase_av hU scale (hL a (by simp)) (hL i (by simp))
  generalize (if scale = 1 then Arm64.add .other [a, i] else
    match Arm64.reg i with
    | some k => Arm64.add .other [a, .int .w64 (k * BitVec.ofNat 64 scale)]
    | none => .poison) = s at hs ⊢
  cases hp : Arm64.addr s 0 with
  | none => rfl
  | some p => exact loadN_eq hM (addr_notU hU hs 0 hp) ty n sg

theorem zero_vr {L : List Val} {M M' : Mem} (hM : Mem.EqOff U M M') (k : Int64) :
    VR U (Arm64.zero k (L ++ [.mem M])) (Arm64.zero k (L ++ [.mem M'])) := by
  rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, Arm64.zero]
  all_goals try exact .refl _
  rotate_left
  · repeat' split
    all_goals first | exact .refl _ | (exfalso; simp_all; done)
  cases hp : Arm64.addr a 0 with
  | none => exact .refl _
  | some p => exact write_vr hM _ _

theorem move_vr (hU : TempU U) {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem}
    (hM : Mem.EqOff U M M') (k : Int64) :
    VR U (Arm64.move k (L ++ [.mem M])) (Arm64.move k (L ++ [.mem M'])) := by
  rcases L with _ | ⟨d, _ | ⟨s, _ | ⟨b, L⟩⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, Arm64.move]
  all_goals try exact .refl _
  rotate_left
  · repeat' split
    all_goals first | exact .refl _ | (exfalso; simp_all; done)
  cases hd : Arm64.addr d 0 with
  | none => exact .refl _
  | some pd =>
    cases hs : Arm64.addr s 0 with
    | none => exact .refl _
    | some ps =>
      simp only
      rw [EqOff.read hM ps _ (addr_notU hU (hL s (by simp)) 0 hs)]
      cases hr : M.read ps k.toInt.toNat with
      | none => exact .refl _
      | some bs => exact write_vr hM _ _

theorem wbOp_vr {L : List Val} {M M' : Mem} (hM : Mem.EqOff U M M') (k : Int64) :
    VR U (wbOp k (L ++ [.mem M])) (wbOp k (L ++ [.mem M'])) := by
  rcases L with _ | ⟨a, L⟩ <;> simp only [List.nil_append, List.cons_append, wbOp]
  · exact .tuple (.cons (.refl _) (.cons (.mem (EqOff.set hM (ARel.refl U _))) .nil))
  · repeat' split
    all_goals first | exact .refl _ | (exfalso; simp_all; done)

/-- The kept memory ops `Arm64.evalPure` evaluates. -/
def armP : List Op :=
  [.ARM64LDAR, .ARM64LDARB, .ARM64LDARW, .ARM64LoweredZero, .ARM64LoweredZeroLoop,
    .ARM64LoweredMove, .ARM64LoweredMoveLoop, .ARM64LoweredWB,
    .ARM64MOVDloadidx, .ARM64MOVWloadidx, .ARM64MOVWUloadidx, .ARM64MOVHloadidx,
    .ARM64MOVHUloadidx, .ARM64MOVBloadidx, .ARM64MOVBUloadidx, .ARM64FMOVSloadidx,
    .ARM64FMOVDloadidx, .ARM64MOVHloadidx2, .ARM64MOVHUloadidx2, .ARM64MOVWloadidx4,
    .ARM64MOVWUloadidx4, .ARM64MOVDloadidx8, .ARM64FMOVSloadidx4, .ARM64FMOVDloadidx8]

/-- **A kept memory op of `Arm64.evalPure`** on related memories. -/
theorem armP_vr (hU : TempU U) {op : Op} (hop : op ∈ armP) (ty : Ty) (k : Int64)
    (aux : Option AuxRef) {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem}
    (hM : Mem.EqOff U M M') :
    VR U (Arm64.evalPure op ty k aux (L ++ [.mem M])) (Arm64.evalPure op ty k aux (L ++ [.mem M'])) := by
  simp only [armP, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact atomicLoad_rel hU ty L (.mem hM) hL
    | exact zero_vr hM k
    | exact move_vr hU hL hM k
    | exact wbOp_vr hM k
    | (show VR U (Arm64.loadIdx ty _ _ _ (L ++ [.mem M])) (Arm64.loadIdx ty _ _ _ (L ++ [.mem M']))
       rw [loadIdx_eq hU hL hM]; exact .refl _)

/-! ## All kept memory ops of `armMemOps` -/

theorem armMemOps_split {op : Op} (h : op ∈ armMemOps) :
    op ∈ armA ∨ op ∈ armP ∨ op = .SPanchored ∨ op = .WBend := by
  have key : armMemOps.all (fun o => armA.contains o || armP.contains o || o == .SPanchored ||
      o == .WBend) = true := by decide
  have := List.all_eq_true.1 key op h
  simpa [or_assoc] using this

theorem armA_generic {op : Op} (h : op ∈ armA) : op.generic = false := by
  have key : armA.all (fun o => !o.generic) = true := by decide
  simpa using List.all_eq_true.1 key op h

theorem armP_generic {op : Op} (h : op ∈ armP) : op.generic = false ∧ isRoot op = false := by
  have key : armP.all (fun o => !o.generic && !isRoot o) = true := by decide
  simpa using List.all_eq_true.1 key op h

theorem evalOpL_armA {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op ∈ armA) :
    evalOpL false env ctx fr v argv ty = arm64Op false env ctx fr v argv ty := by
  unfold evalOpL
  rw [ite_eq_right (by simp [armA_generic hop])]
  split
  all_goals first
    | rfl
    | (exfalso; simp only [armA, List.mem_cons, List.not_mem_nil, or_false] at hop; simp_all; done)

theorem evalOpL_armP {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op ∈ armP) :
    evalOpL false env ctx fr v argv ty = .ok (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  obtain ⟨hg, hr⟩ := armP_generic hop
  unfold evalOpL
  rw [ite_eq_right (by simp [hg])]
  split
  all_goals first
    | (rw [ite_eq_right (by simp [hr])]; rfl)
    | (rename_i heq; rw [heq] at hop; exact absurd hop (by decide))
    | (rename_i heq; unfold arm64Op; simp only [nilFaults, Bool.not_false, ite_true]
       rw [heq]; rfl)

theorem evalOpL_spanchored {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .SPanchored) : evalOpL false env ctx fr v argv ty = .ok .poison := by
  unfold evalOpL evalOp frameVal
  rw [hop]
  rfl

theorem evalOpL_wbend {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .WBend) : evalOpL false env ctx fr v argv ty = memRoot ctx v argv := by
  unfold evalOpL evalOp
  rw [hop]
  rfl

theorem wbend_rel {ctx : Ctx} {v : Value} (hop : v.op = .WBend) {L : List Val} {M M' : Mem}
    (hM : Mem.EqOff U M M') :
    ResRel U (memRoot ctx v (L ++ [.mem M])) (memRoot ctx v (L ++ [.mem M'])) := by
  unfold memRoot
  rw [hop]
  rcases L with _ | ⟨a, L⟩ <;> simp only [List.nil_append, List.cons_append]
  · exact resRel_ok (.mem (EqOff.filter hM (fun e => e.1 != .wbuf) (fun _ _ _ => rfl)))
  · repeat' split
    all_goals first | exact resRel_stuck _ _ | (exfalso; simp_all; done)

/-- **A kept memory op of `armMemOps`** on related memories (the other arguments avoid `U`). -/
theorem armMemOp_rel {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx} {fr : Frame}
    {v : Value} {ty : Ty} (hs : SymOK U ctx v) (hop : v.op ∈ armMemOps) {L : List Val}
    (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem} (hM : Mem.EqOff U M M') (hMA : M.Avoids U) :
    ResRel U (evalOpL false env ctx fr v (L ++ [.mem M]) ty)
      (evalOpL false env ctx fr v (L ++ [.mem M']) ty) := by
  rcases armMemOps_split hop with h | h | h | h
  · rw [evalOpL_armA h, evalOpL_armA h]
    exact ⟨armA_ok hfs hU hs h hL hM hMA, armA_panic hfs hU h hL hM hMA⟩
  · rw [evalOpL_armP h, evalOpL_armP h]
    exact resRel_ok (armP_vr hU h ty _ _ hL hM)
  · rw [evalOpL_spanchored h, evalOpL_spanchored h]
    exact resRel_refl _
  · rw [evalOpL_wbend h, evalOpL_wbend h]
    exact wbend_rel h hM

end GoFV.Proof.UnreadL
