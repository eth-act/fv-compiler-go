import GoFV.Proof.Pass.DAEOps

/-!
# dead auto elim: the memory roots on related memories

`Store`/`Zero`/`Move` (`write_spec`: the write, its bytes, and the same write on another memory),
`VarDef`, `VarLive`, `KeepAlive`, `NilCheck` and `PanicBounds` on argument lists `L ++ [w]` and
`L ++ [w']` with related memories `w`, `w'`: kept roots write the same bytes into a block outside
`U` on both sides (`EqOff.write`) and keep the source's memory avoiding `U`; panics carry related
memories.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.DAE GoFV.Proof.DSE

variable {U : Blk → Prop}

/-- What a `Store`/`Zero`/`Move` that succeeds does: its write, the bytes it writes (avoiding
`U` when its arguments and memory do), and the same write on another memory (a `Move` reading
it alike). -/
theorem write_spec {ctx : Ctx} {v : Value} {argv : List Val} {y : Val}
    (hop : v.op = .Store ∨ v.op = .Zero ∨ v.op = .Move) (h : memRoot ctx v argv = .ok y) :
    ∃ p L M bs M1, argv = .ptr p :: (L ++ [.mem M]) ∧ M.write p bs = some M1 ∧ y = .mem M1 ∧
      (∀ U : Blk → Prop, (∀ a ∈ L, Val.Avoids U a) → M.Avoids U → BAv U bs) ∧
      ∀ M' M1', (∀ s, v.op = .Move → L = [.ptr s] → M'.read s bs.size = M.read s bs.size) →
        M'.write p bs = some M1' → memRoot ctx v (.ptr p :: (L ++ [.mem M'])) = .ok (.mem M1') := by
  rcases hop with hop | hop | hop
  · unfold memRoot at h
    simp only [hop] at h
    split at h
    all_goals first
      | contradiction
      | (split at h <;> cases h <;> done)
      | skip
    rename_i p x M _
    obtain ⟨M1, hw, rfl⟩ := CSE.Mem.writeRes_ok h
    refine ⟨p, [x], M, _, M1, rfl, hw, rfl, fun U hL _ => encode_avoids _ (hL x (by simp)), ?_⟩
    intro M' M1' _ hw'
    simp only [List.cons_append, List.nil_append, memRoot, hop, hw']
    rfl
  · unfold memRoot at h
    simp only [hop] at h
    split at h
    all_goals first
      | contradiction
      | (split at h <;> cases h <;> done)
      | skip
    rename_i p M _
    obtain ⟨M1, hw, rfl⟩ := CSE.Mem.writeRes_ok h
    refine ⟨p, [], M, _, M1, rfl, hw, rfl, fun U _ _ => ?_, ?_⟩
    · intro x hx
      simp only [Array.toList_replicate, List.mem_replicate] at hx
      rw [hx.2]; trivial
    · intro M' M1' _ hw'
      simp only [List.nil_append, memRoot, hop, hw']
      rfl
  · unfold memRoot at h
    simp only [hop] at h
    split at h
    all_goals first
      | contradiction
      | skip
    all_goals first
      | (split at h <;> cases h <;> done)
      | skip
    rename_i d s M _
    cases hr : M.read s v.auxInt.toInt.toNat with
    | none => rw [hr] at h; cases h
    | some bs =>
      rw [hr] at h
      obtain ⟨M1, hw, rfl⟩ := CSE.Mem.writeRes_ok h
      have hsz := DSE.read_size hr
      refine ⟨d, [.ptr s], M, bs, M1, rfl, hw, rfl,
        fun U hL hM => read_avoids hM hr (hL (.ptr s) (by simp)), ?_⟩
      intro M' M1' hrd hw'
      have hr' : M'.read s v.auxInt.toInt.toNat = some bs := by
        rw [← hsz, hrd s hop rfl, hsz, hr]
      simp only [List.cons_append, List.nil_append, memRoot, hop, hr', hw']
      rfl

theorem snoc_cons_eq {L L' : List Val} {a w : Val} {M : Mem} (h : L ++ [w] = a :: (L' ++ [.mem M])) :
    L = a :: L' ∧ w = .mem M := by
  have := snoc_inj (L := L) (L' := a :: L') (w := w) (w' := .mem M) (by rw [h]; rfl)
  exact this

/-- **A kept `Store`/`Zero`/`Move`** on related memories. -/
theorem write_rel {ctx : Ctx} {v : Value} (hop : v.op = .Store ∨ v.op = .Zero ∨ v.op = .Move)
    {L : List Val} {w w' : Val} (hw : VR U w w') (hav : ∀ a ∈ L, Val.Avoids U a) {y : Val}
    (h : memRoot ctx v (L ++ [w]) = .ok y) :
    ∃ y', memRoot ctx v (L ++ [w']) = .ok y' ∧ VR U y y' := by
  obtain ⟨p, L0, M, bs, M1, he, hwr, rfl, -, htgt⟩ := write_spec hop h
  obtain ⟨rfl, rfl⟩ := snoc_cons_eq he
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  have hp : ¬ U p.blk := hav _ List.mem_cons_self
  obtain ⟨M1', hw', hm1⟩ := EqOff.write hm hwr
  refine ⟨_, ?_, .mem hm1⟩
  rw [List.cons_append]
  refine htgt M' M1' (fun s _ hL => ?_) hw'
  subst hL
  exact EqOff.read hm s _ (hav (.ptr s) (by simp))

/-- A kept `Store`/`Zero`/`Move` keeps the source's memory avoiding `U`. -/
theorem write_avoids {ctx : Ctx} {v : Value} (hop : v.op = .Store ∨ v.op = .Zero ∨ v.op = .Move)
    {argv : List Val} (hav : ∀ a ∈ argv, Val.Avoids U a) {y : Val}
    (h : memRoot ctx v argv = .ok y) : Val.Avoids U y := by
  obtain ⟨p, L0, M, bs, M1, rfl, hwr, rfl, hb, -⟩ := write_spec hop h
  have hM : M.Avoids U := hav (.mem M) (by simp)
  exact memAvoids_write hM hwr fun _ =>
    hb U (fun a ha => hav a (by simp [ha])) hM

theorem evalOp_memRoot {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .Store ∨ v.op = .Zero ∨ v.op = .Move ∨ v.op = .VarDef ∨ v.op = .VarLive ∨
      v.op = .KeepAlive ∨ v.op = .NilCheck) :
    evalOp env ctx fr v argv ty = memRoot ctx v argv := by
  rcases hop with hop | hop | hop | hop | hop | hop | hop <;> simp only [evalOp, hop]

/-! ## `VarDef`, `VarLive`, `KeepAlive` -/

theorem varLive_spec {ctx : Ctx} {v : Value} {argv : List Val} {y : Val}
    (hop : v.op = .VarLive ∨ v.op = .KeepAlive) (h : memRoot ctx v argv = .ok y) :
    ∃ L M, argv = L ++ [.mem M] ∧ y = .mem M ∧
      ∀ M', memRoot ctx v (L ++ [.mem M']) = .ok (.mem M') := by
  rcases hop with hop | hop
  · unfold memRoot at h; simp only [hop] at h
    split at h
    all_goals first
      | contradiction
      | (split at h <;> cases h <;> done)
      | skip
    rename_i M _
    cases h
    exact ⟨[], M, rfl, rfl, fun M' => by simp only [List.nil_append, memRoot, hop]⟩
  · unfold memRoot at h; simp only [hop] at h
    split at h
    all_goals first
      | contradiction
      | (split at h <;> cases h <;> done)
      | skip
    rename_i x M _
    cases h
    exact ⟨[x], M, rfl, rfl, fun M' => by simp only [List.cons_append, List.nil_append, memRoot, hop]⟩

/-- **`VarLive`, `KeepAlive`** pass their memory through. -/
theorem varLive_rel {ctx : Ctx} {v : Value} (hop : v.op = .VarLive ∨ v.op = .KeepAlive)
    {L : List Val} {w w' : Val} (hw : VR U w w') {y : Val} (h : memRoot ctx v (L ++ [w]) = .ok y) :
    (∃ y', memRoot ctx v (L ++ [w']) = .ok y' ∧ VR U y y') ∧
      (∀ M, w = .mem M → M.Avoids U → Val.Avoids U y) := by
  obtain ⟨L0, M, he, rfl, htgt⟩ := varLive_spec hop h
  obtain ⟨rfl, rfl⟩ := snoc_inj he
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  exact ⟨⟨_, htgt M', .mem hm⟩, fun M1 h1 hM => by cases h1; exact hM⟩

/-- **A kept `VarDef`** poisons the same block on both sides. -/
theorem varDef_rel {ctx : Ctx} {v : Value} (hop : v.op = .VarDef) {L : List Val} {w w' : Val}
    (hw : VR U w w') {y : Val} (h : memRoot ctx v (L ++ [w]) = .ok y) :
    (∃ y', memRoot ctx v (L ++ [w']) = .ok y' ∧ VR U y y') ∧
      (∀ M, w = .mem M → M.Avoids U → Val.Avoids U y) := by
  obtain ⟨M, n, he, hax, rfl, htgt⟩ := DSE.varDef_shape hop h
  obtain ⟨rfl, rfl⟩ := snoc_inj (L' := []) he
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  exact ⟨⟨_, htgt M', .mem (EqOff.poison hm _)⟩, fun M1 h1 hM => by
    cases h1; exact memAvoids_poison hM _⟩

/-! ## `NilCheck` and `PanicBounds` -/

theorem nilCheck_stuck {ctx : Ctx} {v : Value} (hop : v.op = .NilCheck) {argv : List Val}
    (h1 : ∀ p m, argv ≠ [.ptr p, .mem m]) (h2 : ∀ x m, argv ≠ [.int .w64 x, .mem m]) :
    ∃ msg, memRoot ctx v argv = .stuck msg := by
  unfold memRoot
  split
  all_goals first | (exfalso; simp_all; done) | skip
  split <;> exact ⟨_, rfl⟩

theorem nilCheck_shape {ctx : Ctx} {v : Value} (hop : v.op = .NilCheck) {argv : List Val}
    (hs : ∀ msg, memRoot ctx v argv ≠ .stuck msg) :
    (∃ p M, argv = [.ptr p, .mem M]) ∨ (∃ x M, argv = [.int .w64 x, .mem M]) := by
  by_cases h1 : ∃ p M, argv = [.ptr p, .mem M]
  · exact .inl h1
  by_cases h2 : ∃ x M, argv = [.int .w64 x, .mem M]
  · exact .inr h2
  obtain ⟨msg, hm⟩ := nilCheck_stuck (ctx := ctx) hop (fun p M he => h1 ⟨p, M, he⟩)
    (fun x M he => h2 ⟨x, M, he⟩)
  exact absurd hm (hs msg)

theorem nilCheck_ok {ctx : Ctx} {v : Value} (hop : v.op = .NilCheck) {argv : List Val} {y : Val}
    (h : memRoot ctx v argv = .ok y) :
    ∃ M, argv = [y, .mem M] ∧ ∀ M', memRoot ctx v [y, .mem M'] = .ok y := by
  rcases nilCheck_shape hop (fun msg h' => by rw [h] at h'; cases h') with
    ⟨p, M, rfl⟩ | ⟨x, M, rfl⟩
  · simp only [memRoot, hop] at h ⊢
    split at h
    · cases h
    · cases h; rename_i hn; exact ⟨M, rfl, fun M' => by simp [hn]⟩
  · simp only [memRoot, hop] at h ⊢
    split at h
    · cases h
    · cases h; rename_i hn; exact ⟨M, rfl, fun M' => by simp [hn]⟩

theorem nilCheck_panic {ctx : Ctx} {v : Value} (hop : v.op = .NilCheck) {argv : List Val}
    {e : Panic} {m : Mem} (h : memRoot ctx v argv = .panic e m) :
    ∃ x, argv = [x, .mem m] ∧ ∀ M', memRoot ctx v [x, .mem M'] = .panic e M' := by
  rcases nilCheck_shape hop (fun msg h' => by rw [h] at h'; cases h') with
    ⟨p, M, rfl⟩ | ⟨x, M, rfl⟩
  · simp only [memRoot, hop] at h ⊢
    split at h
    · cases h; rename_i hn; exact ⟨_, rfl, fun M' => by simp [hn]⟩
    · cases h
  · simp only [memRoot, hop] at h ⊢
    split at h
    · cases h; rename_i hn; exact ⟨_, rfl, fun M' => by simp [hn]⟩
    · cases h

/-- **A kept `NilCheck`** on related memories. -/
theorem nilCheck_rel {ctx : Ctx} {v : Value} (hop : v.op = .NilCheck) {L : List Val} {w w' : Val}
    (hw : VR U w w') :
    (∀ y, memRoot ctx v (L ++ [w]) = .ok y → memRoot ctx v (L ++ [w']) = .ok y ∧ L = [y]) ∧
    (∀ e m, memRoot ctx v (L ++ [w]) = .panic e m →
      ∃ m', memRoot ctx v (L ++ [w']) = .panic e m' ∧ Mem.EqOff U m m') := by
  constructor
  · intro y h
    obtain ⟨M, he, ht⟩ := nilCheck_ok hop h
    obtain ⟨rfl, rfl⟩ := snoc_inj (L' := [y]) he
    obtain ⟨M', rfl, -⟩ := VR.mem_inv hw
    exact ⟨ht M', rfl⟩
  · intro e m h
    obtain ⟨x, he, ht⟩ := nilCheck_panic hop h
    obtain ⟨rfl, rfl⟩ := snoc_inj (L' := [x]) he
    obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
    exact ⟨M', ht M', hm⟩

theorem panicBounds_panic {k : Int64} {argv : List Val} {e : Panic} {m : Mem}
    (h : panicBounds k argv = .panic e m) :
    ∃ L, argv = L ++ [.mem m] ∧ ∀ M', panicBounds k (L ++ [.mem M']) = .panic e M' := by
  unfold panicBounds at h
  split at h
  · cases h
    rename_i w1 x w2 y
    exact ⟨[.int w1 x, .int w2 y], rfl, fun M' => by simp [panicBounds]⟩
  · cases h

/-- **`PanicBounds`** panics alike on related memories. -/
theorem panicBounds_rel {k : Int64} {L : List Val} {w w' : Val} (hw : VR U w w') {e : Panic}
    {m : Mem} (h : panicBounds k (L ++ [w]) = .panic e m) :
    ∃ m', panicBounds k (L ++ [w']) = .panic e m' ∧ Mem.EqOff U m m' := by
  obtain ⟨L0, he, ht⟩ := panicBounds_panic h
  obtain ⟨rfl, rfl⟩ := snoc_inj he
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  exact ⟨M', ht M', hm⟩

theorem evalOp_panicBounds {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .PanicBounds) : evalOp env ctx fr v argv ty = panicBounds v.auxInt argv := by
  simp only [evalOp, hop]

/-! ## Atomics (`Sem/Atomic.lean`) -/

/-- The atomic roots of `memOps` are `atomicRoot`. -/
theorem evalOp_atomic {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .AtomicStore32 ∨ v.op = .AtomicStore64 ∨ v.op = .AtomicAdd32 ∨
      v.op = .AtomicAdd32Variant ∨ v.op = .AtomicAdd64 ∨ v.op = .AtomicCompareAndSwap32 ∨
      v.op = .AtomicCompareAndSwap32Variant ∨ v.op = .AtomicCompareAndSwap64 ∨
      v.op = .AtomicCompareAndSwap64Variant) :
    evalOp env ctx fr v argv ty = atomicRoot v argv := by
  rcases hop with h | h | h | h | h | h | h | h | h <;>
    simp only [evalOp, frameVal, h] <;> rfl

theorem int2_avoids (w : Width) (f : BitVec w.bits → BitVec w.bits → BitVec w.bits)
    (l : List Val) : Val.Avoids U (int2 w (fun x y => .int w (f x y)) l) := by
  unfold int2
  split
  · split <;> trivial
  · trivial

theorem atomicStep_avoids (k : Atomic.Kind) (w : Width) {o x : Val} (ho : Val.Avoids U o)
    (hx : Val.Avoids U x) :
    Val.Avoids U (Atomic.step k w o x).1 ∧ ∀ r, (Atomic.step k w o x).2 = some r → Val.Avoids U r := by
  cases k <;> simp only [Atomic.step, Int.add, Int.and, Int.or] <;>
    refine ⟨?_, fun r hr => ?_⟩ <;> (try cases hr) <;>
    first | exact hx | exact ho | exact int2_avoids _ _ _

theorem atomicResult_avoids {r : Option Val} {m : Mem} (hr : ∀ y, r = some y → Val.Avoids U y)
    (hm : m.Avoids U) : Val.Avoids U (Atomic.result r m) := by
  cases r with
  | none => exact hm
  | some y => exact ⟨hr y rfl, hm, trivial⟩

theorem atomicResult_rel (r : Option Val) {m m' : Mem} (hm : Mem.EqOff U m m') :
    VR U (Atomic.result r m) (Atomic.result r m') := by
  cases r with
  | none => exact .mem hm
  | some y => exact .tuple (.cons (.refl y) (.cons (.mem hm) .nil))

theorem atomicRmw_avoids (hU : TempU U) {v : Value} {k : Atomic.Kind} {t : Ty} {p : Ptr}
    {x : Val} {m : Mem} {y : Val} (hp : ¬ U p.blk) (hx : Val.Avoids U x) (hm : m.Avoids U)
    (h : Atomic.rmw v k t p x m = .ok y) : Val.Avoids U y := by
  unfold Atomic.rmw at h
  have hs := atomicStep_avoids k (Atomic.width t) (load_avoids hU hm t hp) hx
  split at h
  · split at h
    · rename_i m1 hw
      cases h
      exact atomicResult_avoids hs.2 (memAvoids_write hm hw fun _ => encode_avoids t hs.1)
    · cases h
  · cases h

theorem atomicRmw_rel {v : Value} {k : Atomic.Kind} {t : Ty} {p : Ptr} {x : Val} {m m' : Mem}
    {y : Val} (hp : ¬ U p.blk) (hm : Mem.EqOff U m m') (h : Atomic.rmw v k t p x m = .ok y) :
    ∃ y', Atomic.rmw v k t p x m' = .ok y' ∧ VR U y y' := by
  unfold Atomic.rmw at h ⊢
  rw [EqOff.load hm t p hp]
  split at h
  · rename_i ha
    simp only [ha, ↓reduceIte]
    split at h
    · rename_i m1 hw
      cases h
      obtain ⟨m1', hw', hm1⟩ := EqOff.write hm hw
      rw [hw']
      exact ⟨_, rfl, atomicResult_rel _ hm1⟩
    · cases h
  · cases h

theorem atomicCas_avoids {v : Value} {w : Width} {p : Ptr} {o n : Val} {m : Mem} {y : Val}
    (hn : Val.Avoids U n) (hm : m.Avoids U) (h : Atomic.cas v w p o n m = .ok y) :
    Val.Avoids U y := by
  unfold Atomic.cas at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i m1 hw
          cases h
          exact ⟨trivial, memAvoids_write hm hw (fun _ => encode_avoids _ hn), trivial⟩
        · cases h
      · cases h
        exact ⟨trivial, hm, trivial⟩
    · cases h
  · cases h

theorem atomicCas_rel {v : Value} {w : Width} {p : Ptr} {o n : Val} {m m' : Mem} {y : Val}
    (hp : ¬ U p.blk) (hm : Mem.EqOff U m m') (h : Atomic.cas v w p o n m = .ok y) :
    ∃ y', Atomic.cas v w p o n m' = .ok y' ∧ VR U y y' := by
  unfold Atomic.cas at h ⊢
  rw [EqOff.load hm _ p hp]
  revert h
  generalize (m.load (.int w) p).asInt w = a
  generalize o.asInt w = b
  intro h
  by_cases ha : Atomic.aligned p w.bytes = true
  · simp only [ha, ↓reduceIte] at h ⊢
    cases a with
    | none => cases h
    | some cur =>
      cases b with
      | none => cases h
      | some old =>
        dsimp only at h ⊢
        by_cases he : cur = old
        · simp only [he, ↓reduceIte] at h ⊢
          cases hw : m.write p (encode (.int w) n) with
          | none => rw [hw] at h; cases h
          | some m1 =>
            rw [hw] at h
            cases h
            obtain ⟨m1', hw', hm1⟩ := EqOff.write hm hw
            rw [hw']
            exact ⟨_, rfl, .tuple (.cons (.refl _) (.cons (.mem hm1) .nil))⟩
        · simp only [he, ↓reduceIte] at h ⊢
          cases h
          exact ⟨_, rfl, .tuple (.cons (.refl _) (.cons (.mem hm) .nil))⟩
  · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h; cases h

/-- An atomic root returns only on a memory last argument. -/
theorem atomicRoot_ok_mem {v : Value} {L : List Val} {w y : Val}
    (h : atomicRoot v (L ++ [w]) = .ok y) : ∃ m, w = .mem m := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, L⟩⟩⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, atomicRoot] at h
  · unfold Atomic.barrier at h; split at h
    · exact ⟨_, rfl⟩
    · cases h
  · unfold Atomic.prefetch at h; split at h
    · exact ⟨_, rfl⟩
    · cases h
  · unfold Atomic.rmwRoot at h; split at h
    · exact ⟨_, rfl⟩
    · cases h
  · unfold Atomic.casRoot at h; split at h
    · exact ⟨_, rfl⟩
    · cases h
  · rcases L with _ | ⟨e, L⟩ <;> cases h

/-- **An atomic root returns a value avoiding `U`** when its arguments do. -/
theorem atomicRoot_avoids (hU : TempU U) {v : Value} {argv : List Val} {y : Val}
    (hargs : ∀ z ∈ argv, Val.Avoids U z) (h : atomicRoot v argv = .ok y) : Val.Avoids U y := by
  unfold atomicRoot at h
  split at h
  · unfold Atomic.barrier at h; split at h
    · split at h
      · cases h; exact hargs _ List.mem_cons_self
      · cases h
    · cases h
  · unfold Atomic.prefetch at h; split at h
    · split at h
      · cases h; exact hargs _ (by simp)
      · cases h
    · cases h
  · unfold Atomic.rmwRoot at h; split at h
    · split at h
      · exact atomicRmw_avoids hU (hargs (.ptr _) (by simp)) (hargs _ (by simp))
          (hargs (.mem _) (by simp)) h
      · cases h
    · cases h
  · unfold Atomic.casRoot at h; split at h
    · split at h
      · exact atomicCas_avoids (hargs _ (by simp)) (hargs (.mem _) (by simp)) h
      · cases h
    · cases h
  · cases h

end GoFV.Proof.DAE
