import GoFV.Proof.Pass.DAERel
import GoFV.Proof.Eval
import GoFV.Proof.Pass.CSEEval

/-!
# dead auto elim: the source's invariant

`U = UE E`: the frame temporaries (activation 0) of the eliminated names. In the source run,
every register `x` satisfies `SInv`: a tainted `x` (its tag in `E`) holds `poison` or a pointer
into the temporary of its tag; any other `x` holds no pointer into `U` (`Val.Avoids`). The
frame's inputs avoid `U` (`FrameOK`: argument images, initial memory, no closure context).

`src_step`: a value the source evaluates keeps the invariant, from its arguments': a tagged
`LocalAddr` or pointer op (`propOp`) points into its tag's temporary; an eliminated write writes
only into `U`; a kept op of `ptrOps` maps avoiding arguments to an avoiding result
(`evalOp_avoids`); any other kept value has a shape without pointers (`noPtr_avoids`).
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.DAE

/-- The frame temporaries of the eliminated names. -/
def UE (E : List AuxRef) (b : Blk) : Prop := ∃ n ∈ E, b = .temp 0 n

theorem tempU0_UE (E : List AuxRef) : TempU0 (UE E) := fun _ ⟨n, _, h⟩ => ⟨n, h⟩

theorem tempU_UE (E : List AuxRef) : TempU (UE E) := (tempU0_UE E).tempU

/-- The source's invariant of register `x` holding `y`. -/
def SInv (T : ID → Option AuxRef) (E : List AuxRef) (x : ID) (y : Val) : Prop :=
  (∀ n, T x = some n → n ∈ E → y = .poison ∨ ∃ off, y = .ptr ⟨.temp 0 n, off⟩) ∧
    (¬ Tainted T E x → Val.Avoids (UE E) y)

/-- The inputs of a frame avoid `U`. -/
structure FrameOK (U : Blk → Prop) (fr : Frame) : Prop where
  images : ∀ img ∈ fr.images, BAv U img
  closure : fr.closure = none
  mem0 : fr.mem0.Avoids U

/-- A property of every register of a frame. -/
def RegsP (P : ID → Val → Prop) (fr : Frame) : Prop :=
  ∀ x y, fr.regs[x]? = some (some y) → P x y

variable {U : Blk → Prop}

/-! ## Evaluation pieces -/

theorem evalValue_ok_inv {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValue env ctx fr v = .ok y) :
    ∃ vs r, CSE.argVals fr v.args = some vs ∧
      evalOp env ctx fr v vs (ctx.tys[v.id]?.getD .other) = .ok r ∧
      y = r.retype (ctx.tys[v.id]?.getD .other) := by
  obtain ⟨vs, hvs⟩ := CSE.argVals_of_eval (env := env) (ctx := ctx) (fr := fr) (v := v)
    (fun msg h' => by rw [h] at h'; cases h')
  rw [CSE.evalValue_of_argVals hvs] at h
  obtain ⟨r, hr, rfl⟩ := CSE.bind_ok h
  exact ⟨vs, r, hvs, hr, rfl⟩

theorem argVals_mem {fr : Frame} {as : Array ID} {vs : List Val} (h : CSE.argVals fr as = some vs)
    {z : Val} (hz : z ∈ vs) : ∃ a ∈ as, fr.regs[a]? = some (some z) := by
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hz
  have hlen := DSE.mapM_length h
  have hka : k < as.size := by
    have := (List.getElem?_eq_some_iff.1 hk).1
    simp at hlen; omega
  obtain ⟨z', hz', hr⟩ := DSE.argVals_get h (Array.getElem?_eq_getElem hka)
  rw [hk] at hz'; cases hz'
  exact ⟨_, Array.getElem_mem hka, hr⟩

/-- `L ++ [w]` from the arguments `as` with last argument `m`. -/
theorem argVals_snoc {fr : Frame} {as : Array ID} {vs : List Val} (h : CSE.argVals fr as = some vs)
    {m : ID} (hm : as.back? = some m) :
    ∃ L w, vs = L ++ [w] ∧ fr.regs[m]? = some (some w) ∧
      ∀ z ∈ L, ∃ a ∈ as.pop, fr.regs[a]? = some (some z) := by
  have hlen := DSE.mapM_length h
  have hne : vs ≠ [] := by
    intro he; subst he
    obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 hm
    simp at hlen
  obtain ⟨L, w, rfl⟩ := List.eq_nil_or_concat vs |>.resolve_left hne
  rw [List.concat_eq_append] at h ⊢
  refine ⟨L, w, rfl, DSE.argVals_back h hm, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hz
  have hkL := (List.getElem?_eq_some_iff.1 hk).1
  simp at hlen
  have hka : k < as.pop.size := by simp; omega
  have hk' : as[k]? = some as.pop[k] := by
    rw [Array.getElem_pop]; exact Array.getElem?_eq_getElem _
  obtain ⟨z', hz', hr⟩ := DSE.argVals_get h hk'
  rw [List.getElem?_append_left hkL, hk] at hz'
  cases hz'
  exact ⟨_, Array.getElem_mem hka, hr⟩

/-! ## The pointer ops -/

theorem ptrRes_avoids {p : Ptr} (h : ¬ U p.blk) : Val.Avoids U (PtrOps.ptrRes p) := by
  unfold PtrOps.ptrRes; split
  · exact h
  · trivial

theorem ptrRes_cases (p : Ptr) : PtrOps.ptrRes p = .poison ∨ PtrOps.ptrRes p = .ptr p := by
  unfold PtrOps.ptrRes; split
  · exact .inr rfl
  · exact .inl rfl

theorem wordRes_avoids (x k : BitVec 64) : Val.Avoids U (PtrOps.wordRes x k) := by
  unfold PtrOps.wordRes; split <;> trivial

theorem offPtr_avoids (k : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (PtrOps.offPtr k args) := by
  unfold PtrOps.offPtr
  split
  · exact ptrRes_avoids (h _ List.mem_cons_self)
  · exact wordRes_avoids _ _
  · trivial

theorem addPtr_avoids {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (PtrOps.addPtr args) := by
  unfold PtrOps.addPtr
  split
  · split
    · exact ptrRes_avoids (h _ List.mem_cons_self)
    · trivial
  · split
    · exact wordRes_avoids _ _
    · trivial
  · trivial

theorem ptrIndex_avoids (e : Option Nat) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (PtrOps.ptrIndex e args) := by
  unfold PtrOps.ptrIndex
  split
  · split
    · exact ptrRes_avoids (h _ List.mem_cons_self)
    · trivial
  · split
    · exact wordRes_avoids _ _
    · trivial
  · trivial

theorem convert_avoids (t : Ty) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (PtrOps.convert t args) := by
  unfold PtrOps.convert
  split
  · split
    · split <;> trivial
    · exact h _ List.mem_cons_self
  · trivial

theorem condSelect_avoids {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Cmp.condSelect args) := by
  unfold Cmp.condSelect
  split
  · split
    · exact h _ List.mem_cons_self
    · exact h _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · trivial
  · trivial

theorem getD_avoids {vs : List Val} (h : Val.AvoidsList U vs) (i : Nat) :
    Val.Avoids U (vs.getD i .poison) := by
  rw [avoidsList_iff] at h
  cases hi : vs[i]? with
  | none => simp [List.getD, hi]; trivial
  | some z => simp [List.getD, hi]; exact h z (List.mem_of_getElem? hi)

theorem select_avoids (i : Nat) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Tuple.select i args) := by
  unfold Tuple.select
  split
  · exact getD_avoids (h _ List.mem_cons_self) i
  · trivial

theorem selectN_avoids (k : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Tuple.selectN k args) := by
  unfold Tuple.selectN
  split
  · split
    · trivial
    · exact getD_avoids (h _ List.mem_cons_self) _
  · trivial

theorem loadOp_avoids (hU : TempU U) (t : Ty) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (loadOp t args) := by
  unfold loadOp
  split
  · split
    · rename_i hp
      exact load_avoids hU (h _ (List.mem_cons_of_mem _ List.mem_cons_self)) t
        (asPtrWord_notU hU (h _ List.mem_cons_self) hp)
    · trivial
  · trivial

theorem atomicLoad_avoids (hU : TempU U) (t : Ty) {args : List Val}
    (h : ∀ z ∈ args, Val.Avoids U z) : Val.Avoids U (atomicLoad t args) := by
  unfold atomicLoad
  split
  · rename_i a m
    have hm : m.Avoids U := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
    split
    · rename_i hp
      refine ⟨?_, hm, trivial⟩
      split
      · trivial
      · exact load_avoids hU hm _ (asPtrWord_notU hU (h _ List.mem_cons_self) hp)
    · trivial
  · trivial

/-! ## The ops of `ptrOps` -/

theorem evalOp_pure2 {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {ty : Ty} {argv : List Val}
    (hop : v.op = .Phi ∨ v.op = .OffPtr ∨ v.op = .AddPtr ∨ v.op = .PtrIndex ∨ v.op = .ConstNil ∨
      v.op = .CondSelect ∨ v.op = .GetG) :
    evalOp env ctx fr v argv ty = .ok (evalPure v.op ty v.auxInt v.aux argv) := by
  rcases hop with h | h | h | h | h | h | h <;> (simp only [evalOp, frameVal, h]; rfl)

theorem argVal_avoids (hU : TempU U) {ctx : Ctx} {fr : Frame} (hfr : FrameOK U fr) {n : AuxRef}
    {off : Int} {ty : Ty} {r : Val} (h : argVal ctx fr n off ty = .ok r) : Val.Avoids U r := by
  unfold argVal at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i img himg
      split at h
      · cases h; trivial
      · cases h
        exact decode_avoids hU (hfr.images img (Array.mem_of_getElem? himg)) _ _

/-- **A kept op of `ptrOps` (but `LocalAddr`) on avoiding arguments has an avoiding result.** -/
theorem evalOp_avoids {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx} {fr : Frame}
    (hfr : FrameOK U fr) {v : Value} {argv : List Val} {ty : Ty} {r : Val}
    (hop : v.op ∈ ptrOps) (hla : v.op ≠ .LocalAddr) (hargs : ∀ z ∈ argv, Val.Avoids U z)
    (h : evalOp env ctx fr v argv ty = .ok r) : Val.Avoids U r := by
  simp only [ptrOps, List.mem_cons, List.mem_nil_iff, or_false] at hop
  -- the pure ops
  have pure2 : ∀ op, v.op = op → (op = .Phi ∨ op = .OffPtr ∨ op = .AddPtr ∨ op = .PtrIndex ∨
      op = .ConstNil ∨ op = .CondSelect ∨ op = .GetG) → Val.Avoids U r := by
    intro op hv ho
    rw [evalOp_pure2 (hv ▸ ho)] at h
    cases h
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hv]
    · trivial
    · exact offPtr_avoids _ hargs
    · exact addPtr_avoids hargs
    · exact ptrIndex_avoids _ hargs
    · show ¬ U Blk.nil
      intro hu; obtain ⟨_, n, hn⟩ := hU _ hu; cases hn
    · exact condSelect_avoids hargs
    · show ¬ U (Blk.global "runtime.g")
      intro hu; obtain ⟨_, n, hn⟩ := hU _ hu; cases hn
  have pure1 : ∀ op, v.op = op → (op = .Copy ∨ op = .Select0 ∨ op = .Select1 ∨
      op = .SelectN ∨ op = .MakeResult ∨ op = .Convert ∨ op = .Load ∨ op = .AtomicLoad32 ∨
      op = .AtomicLoad64 ∨ op = .AtomicLoadPtr) → Val.Avoids U r := by
    intro op hv ho
    rw [evalOp_pureOp (by rcases ho with h | h | h | h | h | h | h | h | h | h <;> simp [hv, h])]
      at h
    cases h
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hv]
    · rcases argv with _ | ⟨x, _ | ⟨y, rest⟩⟩
      · trivial
      · exact hargs _ List.mem_cons_self
      · trivial
    · exact select_avoids 0 hargs
    · exact select_avoids 1 hargs
    · exact selectN_avoids _ hargs
    · show Val.AvoidsList U argv
      exact avoidsList_iff.2 hargs
    · exact convert_avoids _ hargs
    · exact loadOp_avoids hU _ hargs
    · exact atomicLoad_avoids hU _ hargs
    · exact atomicLoad_avoids hU _ hargs
    · exact atomicLoad_avoids hU _ hargs
  have roots : ∀ op, v.op = op → (op = .Store ∨ op = .Zero ∨ op = .Move ∨ op = .VarDef ∨
      op = .VarLive ∨ op = .KeepAlive ∨ op = .NilCheck) → Val.Avoids U r := by
    intro op hv ho
    rw [evalOp_memRoot (by rcases ho with h | h | h | h | h | h | h <;> simp [hv, h])] at h
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact write_avoids hU (.inl hv) hargs h
    · exact write_avoids hU (.inr (.inl hv)) hargs h
    · exact write_avoids hU (.inr (.inr hv)) hargs h
    · obtain ⟨M, n, rfl, -, rfl, -⟩ := DSE.varDef_shape hv h
      exact memAvoids_poison (hargs _ List.mem_cons_self) _
    · obtain ⟨L, M, rfl, rfl, -⟩ := varLive_spec (.inl hv) h
      exact hargs _ (by simp)
    · obtain ⟨L, M, rfl, rfl, -⟩ := varLive_spec (.inr hv) h
      exact hargs _ (by simp)
    · obtain ⟨M, rfl, -⟩ := nilCheck_ok hv h
      exact hargs _ List.mem_cons_self
  have calls : v.op = .StaticCall ∨ v.op = .InterCall ∨ v.op = .ClosureCall → Val.Avoids U r := by
    intro ho
    have he : evalOp env ctx fr v argv ty = callOp env ctx v argv := by
      rcases ho with h | h | h <;> simp only [evalOp, h]
    rw [he] at h
    rcases List.eq_nil_or_concat argv with rfl | ⟨L, w, rfl⟩
    · obtain ⟨msg, hm⟩ := callOp_nil_stuck (env := env) (ctx := ctx) (v := v)
      rw [hm] at h; cases h
    · rw [List.concat_eq_append] at hargs h
      exact ((callOp_rel hfs hU (.refl w) hargs).1 r h).1
  rcases hop with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact pure2 _ h1 (by simp)
  · exact pure1 _ h1 (by simp)
  · exact pure2 _ h1 (by simp)
  · exact pure2 _ h1 (by simp)
  · exact pure2 _ h1 (by simp)
  · exact absurd h1 hla
  · -- Addr
    simp only [evalOp, frameVal, h1] at h
    split at h
    · rename_i x hx
      cases h
      split at hx
      · cases hx; intro hu; obtain ⟨_, n, hn⟩ := hU _ hu; cases hn
      · cases hx; trivial
    · rename_i hx
      split at hx <;> cases hx
  · exact pure2 _ h1 (by simp)
  · exact pure1 _ h1 (by simp)
  · exact pure2 _ h1 (by simp)
  · exact pure2 _ h1 (by simp)
  · -- GetClosurePtr
    simp only [evalOp, h1, hfr.closure] at h
    cases h; trivial
  · -- Arg
    simp only [evalOp, h1] at h
    split at h
    · exact argVal_avoids hU hfr h
    · cases h
  · -- ArgIntReg
    simp only [evalOp, h1] at h
    split at h
    · exact argVal_avoids hU hfr h
    · cases h
  · -- InitMem
    simp only [evalOp, h1] at h
    cases h; exact hfr.mem0
  · exact pure1 _ h1 (by simp)
  · exact pure1 _ h1 (by simp)
  · exact pure1 _ h1 (by simp)
  · exact pure1 _ h1 (by simp)
  · exact pure1 _ h1 (by simp)
  · exact pure1 _ h1 (by simp)
  · exact pure1 _ h1 (by simp)
  · exact pure1 _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · -- PanicBounds
    rw [evalOp_panicBounds h1] at h
    exact absurd h panicBounds_not_ok
  · exact calls (.inl h1)
  · exact calls (.inr (.inl h1))
  · exact calls (.inr (.inr h1))
  all_goals
    rw [evalOp_atomic (by simp [h1])] at h
    exact atomicRoot_avoids hU hargs h

/-! ## The source step -/

theorem ptrShaped_iff {tabs : Tables} {t : TypeRef} :
    NilCheck.ptrShaped tabs t = true ↔ ∃ e, tabs.ty t = .ptr e := by
  unfold NilCheck.ptrShaped
  split
  · rename_i e he; exact ⟨fun _ => ⟨e, he⟩, fun _ => rfl⟩
  · rename_i hne
    exact ⟨fun h => (nomatch h), fun ⟨e, he⟩ => absurd he (hne e)⟩

theorem evalOp_localAddr {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .LocalAddr) :
    evalOp env ctx fr v argv ty = .ok (match v.aux with
      | some n => .ptr ⟨frameBlk ctx.tabs ctx.act n, 0⟩
      | none => .poison) := by
  simp only [evalOp, frameVal, hop]
  cases v.aux <;> rfl

/-- A pointer into a temporary is an integer at an integer shape and `poison` at a shape that is
not a pointer. -/
theorem retype_temp_avoids (U : Blk → Prop) {t : Ty} (ht : ∀ e, t ≠ .ptr e) (a n : Nat) (off : BitVec 64) :
    Val.Avoids U ((Val.ptr ⟨.temp a n, off⟩).retype t) := by
  cases t with
  | int w => cases w <;> simp [Val.retype, Ptr.addr?, Blk.base?] <;> trivial
  | ptr e => exact absurd rfl (ht e)
  | _ => trivial

theorem retype_ptr_shape {e : Option Nat} {z : Val} {n : Nat}
    (h : z = .poison ∨ ∃ off, z = .ptr ⟨.temp 0 n, off⟩) :
    z.retype (.ptr e) = .poison ∨ ∃ off, z.retype (.ptr e) = .ptr ⟨.temp 0 n, off⟩ := by
  rcases h with rfl | ⟨off, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨off, rfl⟩

theorem ptrRes_temp {n : Nat} (p : Ptr) (hp : p.blk = .temp 0 n) :
    PtrOps.ptrRes p = .poison ∨ ∃ off, PtrOps.ptrRes p = .ptr ⟨.temp 0 n, off⟩ := by
  rcases ptrRes_cases p with h | h
  · exact .inl h
  · exact .inr ⟨p.off, by rw [h]; cases p; simp only at hp; rw [hp]⟩

/-- A pointer op on a tainted argument 0 points into the same temporary. -/
theorem prop_tainted {op : Op} (hop : propOp op = true) (ty : Ty) (k : Int64) (ax : Option AuxRef)
    {z : Val} {rest : List Val} {n : Nat} (hz : z = .poison ∨ ∃ off, z = .ptr ⟨.temp 0 n, off⟩) :
    evalPure op ty k ax (z :: rest) = .poison ∨
      ∃ off, evalPure op ty k ax (z :: rest) = .ptr ⟨.temp 0 n, off⟩ := by
  unfold propOp at hop
  simp only [Bool.or_eq_true, beq_iff_eq] at hop
  rcases hop with ((rfl | rfl) | rfl) | rfl <;> rcases hz with rfl | ⟨off, rfl⟩
  · exact .inl (by cases rest <;> rfl)
  · show PtrOps.offPtr k (_ :: rest) = _ ∨ ∃ off, PtrOps.offPtr k (_ :: rest) = _
    cases rest with
    | nil => exact ptrRes_temp (n := n) _ rfl
    | cons _ _ => exact .inl rfl
  · exact .inl (by cases rest <;> rfl)
  · show PtrOps.addPtr (_ :: rest) = _ ∨ ∃ off, PtrOps.addPtr (_ :: rest) = _
    rcases rest with _ | ⟨i, _ | ⟨_, _⟩⟩
    · exact .inl rfl
    · simp only [PtrOps.addPtr]
      cases asOffset i
      · exact .inl rfl
      · exact ptrRes_temp (n := n) _ rfl
    · exact .inl rfl
  · exact .inl (by cases rest <;> rfl)
  · show PtrOps.ptrIndex _ (_ :: rest) = _ ∨ ∃ off, PtrOps.ptrIndex _ (_ :: rest) = _
    rcases rest with _ | ⟨i, _ | ⟨_, _⟩⟩
    · exact .inl rfl
    · simp only [PtrOps.ptrIndex]
      split
      · exact ptrRes_temp (n := n) _ rfl
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl (by cases rest <;> rfl)
  · rcases rest with _ | ⟨_, _⟩
    · exact .inr ⟨off, rfl⟩
    · exact .inl rfl

theorem evalOp_prop {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : propOp v.op = true) :
    evalOp env ctx fr v argv ty = .ok (evalPure v.op ty v.auxInt v.aux argv) := by
  unfold propOp at hop
  simp only [Bool.or_eq_true, beq_iff_eq] at hop
  rcases hop with ((h | h) | h) | h
  · exact evalOp_pure2 (.inr (.inl h))
  · exact evalOp_pure2 (.inr (.inr (.inl h)))
  · exact evalOp_pure2 (.inr (.inr (.inr (.inl h))))
  · exact evalOp_pureOp (.inl h)

variable {T : ID → Option AuxRef} {E : List AuxRef}

theorem SInv.tainted {x : ID} {y : Val} (h : SInv T E x y) {n : AuxRef} (hn : T x = some n)
    (hE : n ∈ E) : y = .poison ∨ ∃ off, y = .ptr ⟨.temp 0 n, off⟩ := h.1 n hn hE

/-- A register that is neither `poison` nor a pointer avoids `U`. -/
theorem SInv.avoids_of {x : ID} {y : Val} (h : SInv T E x y) (hp : y ≠ .poison)
    (hq : ∀ p, y ≠ .ptr p) : Val.Avoids (UE E) y := by
  by_cases ht : Tainted T E x
  · obtain ⟨n, hn, hE⟩ := ht
    rcases h.1 n hn hE with h' | ⟨off, h'⟩
    · exact absurd h' hp
    · exact absurd h' (hq _)
  · exact h.2 ht

theorem SInv.untainted {x : ID} {y : Val} (h : SInv T E x y) (ht : ¬ Tainted T E x) :
    Val.Avoids (UE E) y := h.2 ht

/-- **A value the source evaluates keeps the invariant.** -/
theorem src_step {env : Env} (hfs : env.FrameSafe) {tabs : Tables} {f g : Func}
    (R : ARelD tabs f g T E) {fr : Frame} (hfr : FrameOK (UE E) fr) (hinv : RegsP (SInv T E) fr)
    {x : ID} {fv : Value} (hfv : f.value? x = some fv) (hid : fv.id = x) {y : Val}
    (h : evalValue env (Ctx.make tabs f) fr fv = .ok y) : SInv T E x y := by
  have hU := tempU_UE E
  have hty := evalValue_hasTy h
  obtain ⟨vs, r, hvs, hr, rfl⟩ := evalValue_ok_inv h
  rw [hid, tys_of_value hfv] at hr hty ⊢
  simp only [Option.getD_some] at hr hty ⊢
  have hargInv : ∀ z ∈ vs, ∃ a ∈ fv.args, SInv T E a z := fun z hz => by
    obtain ⟨a, ha, hr'⟩ := argVals_mem hvs hz
    exact ⟨a, ha, hinv a z hr'⟩
  have htag := R.tag x fv hfv
  have hact : (Ctx.make tabs f).act = 0 := rfl
  have htabs : (Ctx.make tabs f).tabs = tabs := rfl
  by_cases ht : Tainted T E x
  · obtain ⟨n, hn, hnE⟩ := ht
    refine ⟨fun n' hn' _ => ?_, fun hnt => absurd ⟨n, hn, hnE⟩ hnt⟩
    rw [hn] at hn'; cases hn'
    unfold tagStep at htag
    rw [hn] at htag
    split at htag
    · cases htag
    rename_i hps
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hps
    obtain ⟨e, he⟩ := ptrShaped_iff.1 hps
    rw [he]
    split at htag
    · rename_i hla
      have hla' : fv.op = .LocalAddr := beq_iff_eq.1 hla
      have hfb : frameBlk (Ctx.make tabs f).tabs (Ctx.make tabs f).act n = .temp 0 n :=
        frameBlk_temp (R.temp n hnE) 0
      rw [evalOp_localAddr hla', htag] at hr
      simp only [hfb] at hr
      cases hr
      exact .inr ⟨0, rfl⟩
    split at htag
    · rename_i hp
      cases ha : fv.args[0]? with
      | none => rw [ha] at htag; cases htag
      | some a =>
        rw [ha] at htag
        simp only [Option.bind_some] at htag
        obtain ⟨z, hz, hza⟩ := DSE.argVals_get hvs ha
        have hzI := (hinv a z hza).tainted htag hnE
        rw [evalOp_prop hp] at hr
        cases hr
        cases vs with
        | nil => simp at hz
        | cons z' rest =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
          subst hz
          exact retype_ptr_shape (prop_tainted hp _ _ _ hzI)
    · cases htag
  · refine ⟨fun n hn hnE => absurd ⟨n, hn, hnE⟩ ht, fun _ => ?_⟩
    obtain ⟨gv, hgv, hk⟩ := R.value x fv hfv
    rcases hk with ⟨hs, hok⟩ | ⟨he, n, hname', hnE⟩
    · -- a kept value: every argument is untainted
      have hargA : ∀ z ∈ vs, Val.Avoids (UE E) z := fun z hz => by
        obtain ⟨a, ha, hI⟩ := hargInv z hz
        refine hI.untainted fun hta => ?_
        obtain ⟨i, hi⟩ := Array.getElem?_of_mem ha
        rcases uses_spec hfv (R.uses x (DSE.lt_of_value? hfv)) hi hta with
          ⟨-, -, hTx⟩ | ⟨gv', hgv', he, -⟩
        · obtain ⟨n, hn, hnE⟩ := hta
          exact ht ⟨n, hTx.trans hn, hnE⟩
        · rw [hgv] at hgv'; cases hgv'
          exact elimV_ne_same he hs
      rcases (opOK_spec hok).2 with hp | hn
      · by_cases hla : fv.op = .LocalAddr
        · rw [evalOp_localAddr hla] at hr
          cases hr
          cases hax : fv.aux with
          | none => exact retype_avoids hU _ trivial
          | some n =>
            by_cases hps : NilCheck.ptrShaped tabs fv.type = true
            · obtain ⟨e, he⟩ := ptrShaped_iff.1 hps
              rw [he]
              show ¬ UE E (frameBlk tabs 0 n)
              rintro ⟨m, hmE, hm⟩
              have hnm : n = m := by
                unfold frameBlk at hm; split at hm <;> cases hm; rfl
              subst hnm
              refine ht ⟨n, ?_, hmE⟩
              rw [← htag]
              unfold tagStep
              simp [hps, hla, hax]
            · have hnp : ∀ e, tabs.ty fv.type ≠ .ptr e := fun e he => hps (ptrShaped_iff.2 ⟨e, he⟩)
              show Val.Avoids _ ((Val.ptr ⟨frameBlk tabs 0 n, 0⟩).retype _)
              unfold frameBlk
              split
              · exact retype_avoids hU _ (show ¬ UE E (.local 0 n) from fun ⟨m, _, hm⟩ => by cases hm)
              · exact retype_temp_avoids _ hnp 0 n 0
        · exact retype_avoids hU _ (evalOp_avoids hfs hU hfr hp hla hargA hr)
      · exact noPtr_avoids hU hty hn
    · -- an eliminated write
      obtain ⟨hop, -⟩ := elimV_spec he
      have hmA : ∀ M, Val.mem M ∈ vs → M.Avoids (UE E) := fun M hM => by
        obtain ⟨a, -, hI⟩ := hargInv _ hM
        exact hI.avoids_of nofun nofun
      refine retype_avoids hU _ ?_
      rcases hop with hop | hop | hop | hop
      rotate_right
      · rw [evalOp_memRoot (.inr (.inr (.inr (.inl hop))))] at hr
        obtain ⟨M, n', rfl, -, rfl, -⟩ := DSE.varDef_shape hop hr
        exact memAvoids_poison (hmA M (by simp)) _
      all_goals
        have hop3 : fv.op = .Store ∨ fv.op = .Zero ∨ fv.op = .Move := by simp [hop]
        rw [evalOp_memRoot (by simp [hop])] at hr
        obtain ⟨a0, p, L, M, bs, M1, rfl, hap, hw, rfl, -, -⟩ := write_spec hop3 hr
        refine memAvoids_write (hmA M (by simp)) hw fun hpU => ?_
        exfalso
        have hname : nameOf T fv = (fv.args[0]?).bind T := by
          unfold nameOf; simp [hop]
        rw [hname] at hname'
        cases ha : fv.args[0]? with
        | none => rw [ha] at hname'; cases hname'
        | some a =>
          rw [ha] at hname'
          simp only [Option.bind_some] at hname'
          obtain ⟨z, hz, hza⟩ := DSE.argVals_get hvs ha
          simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at hz
          subst hz
          rcases (hinv a _ hza).tainted hname' hnE with h' | ⟨off, h'⟩
          · subst h'; cases hap
          · subst h'; cases hap; exact hpU ⟨n, hnE, rfl⟩

end GoFV.Proof.DAE
