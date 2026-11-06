import GoFV.Proof.TabsAgreeModStep
import GoFV.Proof.Pass.UnreadLStep
import GoFV.Proof.RunLFCases
import GoFV.Proof.Pass.NilLateLEval

/-!
# Running a scheduled function in tables with extra frame temporaries: the arm64 memory ops

`TabsAgreeModOps` for the arm64 memory ops `elim unread autos` handles (`UnreadL.armMemOps`):
on argument lists `L ++ [.mem M]` and `L ++ [.mem M']` whose memories are equal once the extra
frame temporaries `X` are erased (`EqX X M M'`), and whose other arguments avoid `X`, they evaluate
to related results (`armMemOp_relX`): loads read outside `X` (their address avoids `X`: an
argument that avoids `X` or a symbol that names no block of `X`, `UnreadL.SymOK`), stores and the
other writes write the same bytes outside `X` on both sides (`EqX.write`), calls go through
`TabsMod.callOp_rel` (the register pieces are fitted independently of the memory,
`UnreadL.callArgs_snoc`), nil checks and bounds panics panic alike. When memory ops fault
(`runSched`), an access through a nil base in the nil page panics alike on both sides
(`nilFaults_relX`). Registers related by `VR` stay related through `Val.widen` and the lowered
shaping (`VR.mdRetype`).
-/

namespace GoFV.Proof.TabsMod

open GoFV.SSA GoFV.SSA.Sem

variable {X : Blk → Bool}

mutual
theorem VR.widen : {a b : Val} → VR X a b → (t : Ty) → VR X (a.widen t) (b.widen t)
  | _, _, .refl _, _ => .refl _
  | _, _, .mem h, t => by
    have e : ∀ m : Mem, (Val.mem m).widen t = .mem m := fun m => by cases t <;> simp [Val.widen]
    rw [e, e]; exact .mem h
  | _, _, .tuple (vs := vs) (ws := ws) h, t => by
    cases t with
    | tuple ts => simp only [Val.widen]; exact .tuple (VRL.widenList h ts)
    | _ => simp only [Val.widen]; exact .tuple h
theorem VRL.widenList : {as bs : List Val} → VRL X as bs → (ts : List Ty) →
    VRL X (Val.widenList ts as) (Val.widenList ts bs)
  | _, _, .nil, ts => by cases ts <;> simp only [Val.widenList] <;> exact .nil
  | _, _, .cons h t, [] => by simp only [Val.widenList]; exact .cons h t
  | _, _, .cons h t, t0 :: ts => by
    simp only [Val.widenList]; exact .cons (VR.widen h t0) (VRL.widenList t ts)
end

theorem VR.retypeL {a b : Val} (h : VR X a b) (t : Ty) : VR X (a.retypeL t) (b.retypeL t) :=
  VR.retype (VR.widen h t) t

theorem VR.mdRetype {a b : Val} (h : VR X a b) (md : LMode) (t : Ty) :
    VR X (md.retype t a) (md.retype t b) := by
  unfold LMode.retype; split
  · exact VR.retypeL h t
  · exact h.retype t

end GoFV.Proof.TabsMod

namespace GoFV.Proof.TabsModL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.TabsMod

variable {X : Blk → Bool}

local notation "U" => fun b => X b = true

/-! ## Loads and writes outside `X` -/

theorem loadN_eqX {M M' : Mem} (hM : EqX X M M') {p : Ptr} (hp : X p.blk = false) (ty : Ty)
    (n : Nat) (sg : Bool) : Arm64.loadN ty n sg M' p = Arm64.loadN ty n sg M p := by
  unfold Arm64.loadN; simp only [EqX.load hM _ p hp]

theorem load16_eqX {M M' : Mem} (hM : EqX X M M') {p : Ptr} (hp : X p.blk = false) :
    Arm64.load16 M' p = Arm64.load16 M p := by
  unfold Arm64.load16; rw [EqX.read hM p _ hp]

theorem loadElt_eqX {M M' : Mem} (hM : EqX X M M') {p : Ptr} (hp : X p.blk = false) (ty : Ty)
    (n : Nat) (sg : Bool) : Arm64.loadElt ty n sg M' p = Arm64.loadElt ty n sg M p := by
  unfold Arm64.loadElt
  rw [load16_eqX hM hp, loadN_eqX hM hp]

theorem loadPair_eqX {M M' : Mem} (hM : EqX X M M') {p q : Ptr} (hp : X p.blk = false)
    (hq : X q.blk = false) (ty : Ty) (n : Nat) (sg : Bool) :
    Arm64.loadPair ty n sg M' p q = Arm64.loadPair ty n sg M p q := by
  unfold Arm64.loadPair
  rw [loadElt_eqX hM hp, loadElt_eqX hM hq]

theorem elim_ld_eqX {ctx : Ctx} {v : Value} (hs : UnreadL.SymOK U ctx v) {a : Val}
    (ha : Val.Avoids U a) {M M' : Mem} (hM : EqX X M M') (ty : Ty) (n : Nat) (sg : Bool) :
    (symAddr ctx v a).elim .poison (Arm64.loadN ty n sg M') =
      (symAddr ctx v a).elim .poison (Arm64.loadN ty n sg M) := by
  cases hp : symAddr ctx v a with
  | none => rfl
  | some p => exact loadN_eqX hM (notX (hs _ a p ha hp)) ty n sg

theorem elim_ldPair_eqX {ctx : Ctx} {v : Value} (hs : UnreadL.SymOK U ctx v) {a : Val}
    (ha : Val.Avoids U a) {M M' : Mem} (hM : EqX X M M') (ty : Ty) (n : Nat) (sg : Bool) :
    ((pairAddr ctx v n a).elim .poison fun pq => Arm64.loadPair ty n sg M' pq.1 pq.2) =
      ((pairAddr ctx v n a).elim .poison fun pq => Arm64.loadPair ty n sg M pq.1 pq.2) := by
  cases hp : pairAddr ctx v n a with
  | none => rfl
  | some pq =>
    obtain ⟨h1, h2⟩ := pairAddr_eq_some hp
    exact loadPair_eqX hM (notX (hs _ a _ ha h1)) (notX (hs _ a _ ha h2)) ty n sg

theorem elim_ld16_eqX {ctx : Ctx} {v : Value} (hs : UnreadL.SymOK U ctx v) {a : Val}
    (ha : Val.Avoids U a) {M M' : Mem} (hM : EqX X M M') :
    (symAddr ctx v a).elim .poison (Arm64.load16 M') =
      (symAddr ctx v a).elim .poison (Arm64.load16 M) := by
  cases hp : symAddr ctx v a with
  | none => rfl
  | some p => exact load16_eqX hM (notX (hs _ a p ha hp))

/-- A write outside `X` fails on both memories or on neither. -/
theorem EqX.write_none {M M' : Mem} (hM : EqX X M M') {p : Ptr} {bs : Array Byte}
    (hb : X p.blk = false) (h : M.write p bs = none) : M'.write p bs = none := by
  have h1 := erase_write (m := M) bs hb
  have h2 := erase_write (m := M') bs hb
  rw [h] at h1
  rw [← hM, h1] at h2
  cases hw' : M'.write p bs with
  | none => rfl
  | some m => rw [hw'] at h2; cases h2

/-- The same write outside `X` on related memories. -/
theorem writeRes_relX {what : String} {M M' : Mem} (hM : EqX X M M') {p : Ptr}
    (hp : X p.blk = false) {bs : Array Byte} {y : Val} (h : writeRes what (M.write p bs) = .ok y) :
    ∃ y', writeRes what (M'.write p bs) = .ok y' ∧ VR X y y' := by
  cases hw : M.write p bs with
  | none => rw [hw] at h; cases h
  | some M1 =>
    rw [hw] at h; cases h
    obtain ⟨M1', hw', hM1⟩ := EqX.write hM hp hw
    exact ⟨_, by rw [hw']; rfl, .mem hM1⟩

/-- The same pair store outside `X` on related memories. -/
theorem storePair_relX {what : String} {M M' : Mem} (hM : EqX X M M') {n : Nat} {p q : Ptr}
    (hp : X p.blk = false) (hq : X q.blk = false) {a b y : Val}
    (h : writeRes what (Arm64.storePair n p q a b M) = .ok y) :
    ∃ y', writeRes what (Arm64.storePair n p q a b M') = .ok y' ∧ VR X y y' := by
  cases hw : Arm64.storePair n p q a b M with
  | none => rw [hw] at h; cases h
  | some M1 =>
    rw [hw] at h; cases h
    unfold Arm64.storePair at hw
    obtain ⟨M2, h1, h2⟩ := Option.bind_eq_some_iff.1 hw
    obtain ⟨M2', h1', hM2⟩ := EqX.write hM hp h1
    obtain ⟨M1', h2', hM1⟩ := EqX.write hM2 hq h2
    exact ⟨_, by unfold Arm64.storePair; rw [h1', Option.bind_some, h2']; rfl, .mem hM1⟩

/-- The same write outside `X` on related memories, or both fail. -/
theorem write_vrX {M M' : Mem} (hM : EqX X M M') {p : Ptr} (hp : X p.blk = false)
    (bs : Array Byte) :
    VR X (match M.write p bs with | some m' => .mem m' | none => .poison)
      (match M'.write p bs with | some m' => .mem m' | none => .poison) := by
  cases hw : M.write p bs with
  | none => rw [EqX.write_none hM hp hw]; exact .refl _
  | some M1 =>
    obtain ⟨M1', hw', hM1⟩ := EqX.write hM hp hw
    rw [hw']; exact .mem hM1

/-! ## Calls -/

/-- A call on related memories (the arguments before the memory avoid `X`). -/
theorem call_relX {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx} {w : Value}
    {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem} (hM : EqX X M M')
    (hMA : M.Avoids U) {k : Nat} {tabs : Tables} {ins : List ABIParam} :
    CallRel X (callOp env ctx w ((L ++ [Val.mem M]).take k ++
        fitPieces tabs ins ((L ++ [Val.mem M]).drop k)))
      (callOp env ctx w ((L ++ [Val.mem M']).take k ++
        fitPieces tabs ins ((L ++ [Val.mem M']).drop k))) := by
  obtain ⟨A, hA, hAe⟩ := UnreadL.callArgs_snoc (tempU_of hX) k tabs ins hL
  rw [hAe, hAe]
  exact callOp_rel hE hX (.mem hM) (fun z hz => by
    rcases List.mem_append.1 hz with hz | hz
    · exact hA z hz
    · simp at hz; subst hz; exact hMA)

/-! ## The arm64 memory ops `arm64Op` evaluates -/

theorem symX {ctx : Ctx} {v : Value} (hs : UnreadL.SymOK U ctx v) {a : Val} (ha : Val.Avoids U a)
    {k : Int64} {p : Ptr} (hp : symAddr ctx { v with auxInt := k } a = some p) : X p.blk = false :=
  notX (hs k a p ha hp)

theorem addrX (hX : TempX X) {a : Val} (ha : Val.Avoids U a) {p : Ptr}
    (hp : Arm64.addr a 0 = some p) : X p.blk = false :=
  notX (UnreadL.addr_notU (tempU_of hX) ha 0 hp)

/-- **A memory op of `arm64Op` that returns** on related memories. -/
theorem armA_okX {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx} {fr : Frame}
    {v : Value} {ty : Ty} (hs : UnreadL.SymOK U ctx v) (hop : v.op ∈ UnreadL.armA)
    {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem} (hM : EqX X M M')
    (hMA : M.Avoids U) :
    ∀ y, arm64Op false env ctx fr v (L ++ [.mem M]) ty = .ok y →
      ∃ y', arm64Op false env ctx fr v (L ++ [.mem M']) ty = .ok y' ∧ VR X y y' := by
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
    | exact ((call_relX hE hX hL hM hMA).1 y h).2
    | (refine ⟨y, ?_, .refl y⟩
       simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
       exact (nilCheck_rel (X := X) (ctx := ctx) (v := {v with op := .NilCheck}) rfl (L := L)
          (.mem hM)).1 y h)
    | (cases h; exact ⟨_, rfl, by rw [memEq_eq hX L (.mem hM) hL]; exact .refl _⟩)
    | (simp only [UnreadL.snoc1, UnreadL.snoc2, UnreadL.snoc3, UnreadL.snoc4, Val.mem.injEq] at *
       rcases ‹L = _ ∧ _› with ⟨rfl, rfl⟩
       simp only [List.cons_append, List.nil_append] at *
       first
         | (simp only [‹symAddr ctx v _ = some _›]
            exact writeRes_relX hM (symX hs (hL _ List.mem_cons_self)
              ‹symAddr ctx v _ = some _›) h)
         | (simp only [‹pairAddr ctx v _ _ = some _›]
            obtain ⟨h1, h2⟩ := pairAddr_eq_some ‹pairAddr ctx v _ _ = some _›
            exact storePair_relX hM (symX hs (hL _ List.mem_cons_self) h1)
              (symX hs (hL _ List.mem_cons_self) h2) h)
         | (simp only [‹Arm64.addr _ 0 = some _›]
            exact writeRes_relX hM (addrX hX (UnreadL.idxBase_av (tempU_of hX) _
              (hL _ List.mem_cons_self) (hL _ (List.mem_cons_of_mem _ List.mem_cons_self)))
              ‹Arm64.addr _ 0 = some _›) h)
         | (simp only [‹Arm64.addr _ 0 = some _›]
            refine writeRes_relX hM (addrX hX (UnreadL.add_av _ fun z hz => ?_)
              ‹Arm64.addr _ 0 = some _›) h
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl
            · exact hL _ List.mem_cons_self
            · exact hL _ (List.mem_cons_of_mem _ List.mem_cons_self))
         | (cases h
            first
              | exact ⟨_, rfl, by rw [elim_ld_eqX hs (hL _ List.mem_cons_self) hM]; exact .refl _⟩
              | exact ⟨_, rfl, by rw [elim_ldPair_eqX hs (hL _ List.mem_cons_self) hM]
                                  exact .refl _⟩
              | exact ⟨_, rfl, by rw [elim_ld16_eqX hs (hL _ List.mem_cons_self) hM]
                                  exact .refl _⟩
              | exact ⟨_, rfl, .mem hM⟩))
    | (simp only [UnreadL.snoc1, UnreadL.snoc2, UnreadL.snoc3, UnreadL.snoc4, Val.mem.injEq] at *
       cases h
       split <;> simp only [UnreadL.snoc1, UnreadL.snoc2, UnreadL.snoc3, UnreadL.snoc4,
         Val.mem.injEq] at * <;>
         first | exact ⟨_, rfl, .refl _⟩ | (exfalso; simp_all; done))
    | (exfalso; simp only [UnreadL.armA, List.mem_cons, List.not_mem_nil, or_false] at hop
       simp_all; done)

/-- **A memory op of `arm64Op` that panics** panics alike on related memories. -/
theorem armA_panicX {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx} {fr : Frame}
    {v : Value} {ty : Ty} (hop : v.op ∈ UnreadL.armA) {L : List Val}
    (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem} (hM : EqX X M M') (hMA : M.Avoids U) :
    ∀ e m, arm64Op false env ctx fr v (L ++ [.mem M]) ty = .panic e m →
      ∃ m', arm64Op false env ctx fr v (L ++ [.mem M']) ty = .panic e m' ∧ EqX X m m' := by
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
    | exact ((call_relX hE hX hL hM hMA).2 e m h).2.2
    | (simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
       exact (nilCheck_rel (X := X) (ctx := ctx) (v := {v with op := .NilCheck}) rfl (L := L)
          (.mem hM)).2 e m h)
    | exact panicBounds_rel (.mem hM) h
    | (simp only [UnreadL.snoc1, UnreadL.snoc2, UnreadL.snoc3, UnreadL.snoc4, Val.mem.injEq] at *
       rcases ‹L = _ ∧ _› with ⟨rfl, rfl⟩
       simp only [List.cons_append, List.nil_append] at *
       simp only [*]
       first
         | exact panicBounds_rel (L := [_, _]) (.mem hM) h
         | exact panicBounds_rel (L := [_]) (.mem hM) h
         | exact panicBounds_rel (L := [_, _, _]) (.mem hM) h)
    | (exfalso; simp only [UnreadL.armA, List.mem_cons, List.not_mem_nil, or_false] at hop
       simp_all; done)

/-! ## The arm64 memory ops `Arm64.evalPure` evaluates -/

theorem loadIdx_eqX (hX : TempX X) {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem}
    (hM : EqX X M M') (ty : Ty) (n scale : Nat) (sg : Bool) :
    Arm64.loadIdx ty n scale sg (L ++ [.mem M']) = Arm64.loadIdx ty n scale sg (L ++ [.mem M]) := by
  rcases L with _ | ⟨a, _ | ⟨i, _ | ⟨b, L⟩⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, Arm64.loadIdx]
  rotate_left
  · repeat' split
    all_goals first | rfl | (exfalso; simp_all; done)
  have hs := UnreadL.idxBase_av (tempU_of hX) scale (hL a (by simp)) (hL i (by simp))
  generalize (if scale = 1 then Arm64.add .other [a, i] else
    match Arm64.reg i with
    | some k => Arm64.add .other [a, .int .w64 (k * BitVec.ofNat 64 scale)]
    | none => .poison) = s at hs ⊢
  cases hp : Arm64.addr s 0 with
  | none => rfl
  | some p => exact loadN_eqX hM (addrX hX hs hp) ty n sg

theorem zero_vrX (hX : TempX X) {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem}
    (hM : EqX X M M') (k : Int64) :
    VR X (Arm64.zero k (L ++ [.mem M])) (Arm64.zero k (L ++ [.mem M'])) := by
  rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, Arm64.zero]
  all_goals try exact .refl _
  rotate_left
  · repeat' split
    all_goals first | exact .refl _ | (exfalso; simp_all; done)
  cases hp : Arm64.addr a 0 with
  | none => exact .refl _
  | some p => exact write_vrX hM (addrX hX (hL a (by simp)) hp) _

theorem move_vrX (hX : TempX X) {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem}
    (hM : EqX X M M') (k : Int64) :
    VR X (Arm64.move k (L ++ [.mem M])) (Arm64.move k (L ++ [.mem M'])) := by
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
      rw [EqX.read hM ps _ (addrX hX (hL s (by simp)) hs)]
      cases hr : M.read ps k.toInt.toNat with
      | none => exact .refl _
      | some bs => exact write_vrX hM (addrX hX (hL d (by simp)) hd) _

theorem wbOp_vrX {L : List Val} {M M' : Mem} (hM : EqX X M M') (k : Int64) :
    VR X (wbOp k (L ++ [.mem M])) (wbOp k (L ++ [.mem M'])) := by
  rcases L with _ | ⟨a, L⟩ <;> simp only [List.nil_append, List.cons_append, wbOp]
  · exact .tuple (.cons (.refl _) (.cons (.mem (EqX.set hM _ _)) .nil))
  · repeat' split
    all_goals first | exact .refl _ | (exfalso; simp_all; done)

/-- **A memory op of `Arm64.evalPure`** on related memories. -/
theorem armP_vrX (hX : TempX X) {op : Op} (hop : op ∈ UnreadL.armP) (ty : Ty) (k : Int64)
    (aux : Option AuxRef) {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem}
    (hM : EqX X M M') :
    VR X (Arm64.evalPure op ty k aux (L ++ [.mem M]))
      (Arm64.evalPure op ty k aux (L ++ [.mem M'])) := by
  simp only [UnreadL.armP, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact atomicLoad_rel hX ty L (.mem hM) hL
    | exact zero_vrX hX hL hM k
    | exact move_vrX hX hL hM k
    | exact wbOp_vrX hM k
    | (show VR X (Arm64.loadIdx ty _ _ _ (L ++ [.mem M])) (Arm64.loadIdx ty _ _ _ (L ++ [.mem M']))
       rw [loadIdx_eqX hX hL hM]; exact .refl _)

theorem wbend_relX {ctx : Ctx} {v : Value} (hop : v.op = .WBend) {L : List Val} {M M' : Mem}
    (hM : EqX X M M') :
    ResRel X (memRoot ctx v (L ++ [.mem M])) (memRoot ctx v (L ++ [.mem M'])) := by
  unfold memRoot
  rw [hop]
  rcases L with _ | ⟨a, L⟩ <;> simp only [List.nil_append, List.cons_append]
  · exact resRel_ok (.mem (EqX.filter hM (fun e => e.1 != .wbuf)))
  · repeat' split
    all_goals first | exact resRel_stuck _ _ | (exfalso; simp_all; done)

/-- **A memory op of `armMemOps`** on related memories (the other arguments avoid `X`), when
memory ops do not fault. -/
theorem armMemOp_relX {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx}
    {fr : Frame} {v : Value} {ty : Ty} (hs : UnreadL.SymOK U ctx v) (hop : v.op ∈ UnreadL.armMemOps)
    {L : List Val} (hL : ∀ z ∈ L, Val.Avoids U z) {M M' : Mem} (hM : EqX X M M')
    (hMA : M.Avoids U) :
    ResRel X (evalOpL false env ctx fr v (L ++ [.mem M]) ty)
      (evalOpL false env ctx fr v (L ++ [.mem M']) ty) := by
  rcases UnreadL.armMemOps_split hop with h | h | h | h
  · rw [UnreadL.evalOpL_armA h, UnreadL.evalOpL_armA h]
    exact ⟨armA_okX hE hX hs h hL hM hMA, armA_panicX hE hX h hL hM hMA⟩
  · rw [UnreadL.evalOpL_armP h, UnreadL.evalOpL_armP h]
    exact resRel_ok (armP_vrX hX h ty _ _ hL hM)
  · rw [UnreadL.evalOpL_spanchored h, UnreadL.evalOpL_spanchored h]
    exact resRel_refl _
  · rw [UnreadL.evalOpL_wbend h, UnreadL.evalOpL_wbend h]
    exact wbend_relX h hM

/-! ## Faulting memory ops -/

theorem nilAccesses_snoc (ctx : Ctx) (v : Value) (L : List Val) (M M' : Mem) :
    nilAccesses ctx v (L ++ [.mem M']) = nilAccesses ctx v (L ++ [.mem M]) := by
  have hr : ∀ (N : Mem) (k : BitVec 64), Arm64.addr (.mem N) k = none := fun _ _ => rfl
  by_cases hm : v.op = .ARM64LoweredMemEq
  · unfold nilAccesses
    simp only [hm]
    rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, L⟩⟩⟩⟩ <;> simp [hr]
  · rw [NilLateL.nilAccesses_eq hm, NilLateL.nilAccesses_eq hm]
    rcases L with _ | ⟨a, _ | ⟨b, L⟩⟩ <;> simp [hr]

/-- When memory ops fault, an access through a nil base in the nil page faults alike on related
memories. -/
theorem nilFaults_relX (ctx : Ctx) (v : Value) (L : List Val) {M M' m : Mem}
    (h : nilFaults true ctx v (L ++ [.mem M]) = some m) :
    m = M ∧ nilFaults true ctx v (L ++ [.mem M']) = some M' := by
  unfold nilFaults at h ⊢
  rw [nilAccesses_snoc ctx v L M M']
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.getLast?_append,
    List.getLast?_singleton, Option.some_or] at h ⊢
  split at h
  · cases h; exact ⟨rfl, by simp [*]⟩
  · cases h

theorem nilFaults_noneX (ctx : Ctx) (v : Value) (L : List Val) {M M' : Mem}
    (h : nilFaults true ctx v (L ++ [.mem M]) = none) :
    nilFaults true ctx v (L ++ [.mem M']) = none := by
  unfold nilFaults at h ⊢
  rw [nilAccesses_snoc ctx v L M M']
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.getLast?_append,
    List.getLast?_singleton, Option.some_or] at h ⊢
  split at h
  · cases h
  · rename_i hn; simp only [hn]; rfl

theorem wildNil_snoc (L : List Val) (M M' : Mem) :
    wildNil (L ++ [.mem M']) = wildNil (L ++ [.mem M]) := by
  rcases L with _ | ⟨a, L⟩ <;> simp [wildNil, Arm64.addr, Arm64.reg]

theorem arm64Op_fault_some {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {m : Mem} (h : nilFaults true ctx v argv = some m) :
    arm64Op true env ctx fr v argv ty = .panic .nilDeref m := by
  unfold arm64Op; rw [h]

/-- With no nil fault, a faulting `arm64Op` is the non-faulting one, but for a nil check of a
wild pointer. -/
theorem arm64Op_fault_none {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (h : nilFaults true ctx v argv = none)
    (hw : v.op = .ARM64LoweredNilCheck → wildNil argv = false) :
    arm64Op true env ctx fr v argv ty = arm64Op false env ctx fr v argv ty := by
  by_cases hnc : v.op = .ARM64LoweredNilCheck
  · unfold arm64Op; rw [h, nilFaults_false, hnc]; simp [hw hnc]
  · unfold arm64Op
    rw [h, nilFaults_false]
    dsimp only
    split
    all_goals first | rfl | exact absurd ‹_› hnc

/-- **Faulting memory ops on related memories**: a relation of the non-faulting results of two
argument lists differing in their memories is one of the faulting results. -/
theorem resRel_faulting {env : Env} {ctx : Ctx} {fr fr' : Frame} {v : Value} {ty : Ty}
    {L : List Val} {M M' : Mem} (hM : EqX X M M')
    (R : ResRel X (evalOpL false env ctx fr v (L ++ [.mem M]) ty)
      (evalOpL false env ctx fr' v (L ++ [.mem M']) ty)) :
    ResRel X (evalOpL true env ctx fr v (L ++ [.mem M]) ty)
      (evalOpL true env ctx fr' v (L ++ [.mem M']) ty) := by
  rw [evalOpL_eq, evalOpL_eq] at R ⊢
  split
  · rename_i hg; simpa only [hg, ite_true] using R
  rename_i hg
  simp only [hg, Bool.false_eq_true, ite_false] at R ⊢
  split
  rotate_left
  · rename_i ha; simpa only [ha, Bool.false_eq_true, ite_false] using R
  rename_i ha
  simp only [ha, ite_true] at R
  cases hn : nilFaults true ctx v (L ++ [.mem M]) with
  | some m =>
    obtain ⟨rfl, hn'⟩ := nilFaults_relX ctx v L hn
    rw [arm64Op_fault_some hn, arm64Op_fault_some hn']
    exact ⟨fun _ h => (nomatch h), fun e m h => by cases h; exact ⟨_, rfl, hM⟩⟩
  | none =>
    have hn' := nilFaults_noneX ctx v L (M' := M') hn
    by_cases hw : v.op = .ARM64LoweredNilCheck ∧ wildNil (L ++ [.mem M]) = true
    · obtain ⟨msg, hm⟩ : ∃ msg, arm64Op true env ctx fr v (L ++ [.mem M]) ty = .stuck msg := by
        unfold arm64Op; rw [hn]; simp only [hw.1, hw.2, Bool.and_self, ↓reduceIte]
        exact ⟨_, rfl⟩
      rw [hm]; exact resRel_stuck _ _
    · have hw' : v.op = .ARM64LoweredNilCheck → wildNil (L ++ [.mem M]) = false :=
        fun h1 => by simpa using fun h2 => hw ⟨h1, h2⟩
      rw [arm64Op_fault_none hn hw', arm64Op_fault_none hn' (by rw [wildNil_snoc]; exact hw')]
      exact R

/-- `evalOpL` reads the initial memory only for `InitMem`. -/
theorem evalOpL_mem0 {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hn : v.op ≠ .InitMem) (m : Mem) :
    evalOpL faulting env ctx { fr with mem0 := m } v argv ty =
      evalOpL faulting env ctx fr v argv ty := by
  rw [evalOpL_eq, evalOpL_eq]
  split
  · exact evalOp_mem0 hn m
  · rfl

end GoFV.Proof.TabsModL
