import GoFV.Proof.Pass.DAERel
import GoFV.Proof.Eval
import GoFV.Proof.Pass.CSEEval

variable [GoFV.SSA.Sem.Addrs]

/-!
# dead auto elim: the source's invariant

`U = UE E`: the frame temporaries (activation 0) of the eliminated names. In the source run,
every register `x` satisfies `SInv`: a tainted `x` (its tag in `E`) holds `poison` or a pointer
into the temporary of its tag; any other `x` holds no pointer into `U` (`Val.Avoids`). The
frame's inputs avoid `U` (`FrameOK`: argument images, initial memory, closure context).

`src_step`: a value the source evaluates keeps the invariant, from its arguments': a tagged
(word-shaped, `wordShaped`) `LocalAddr` or pointer op (`propOp`) points into its tag's temporary
(at both word shapes: a temporary has no integer form, `Ptr.word`); an eliminated write writes
only into `U`; any other kept op maps avoiding arguments to an avoiding result (`evalOp_avoids`:
every op of `evalOp`, the pure ones by `evalPure_avoids`), and an untagged `LocalAddr` names no
temporary of `U` or has a shape that is not a word, where its pointer is `poison`.
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
  closure : ∀ c, fr.closure = some c → Val.Avoids U c
  mem0 : fr.mem0.Avoids U

/-- A property of every register of a frame. -/
def RegsP (P : ID → Val → Prop) (fr : Frame) : Prop :=
  ∀ x y, fr.regs[x]? = some (some y) → P x y

variable {U : Blk → Prop}

/-- `GetClosurePtr`'s value (the context, `poison` without one) avoids `U`. -/
theorem FrameOK.closure_getD {fr : Frame} (h : FrameOK U fr) :
    Val.Avoids U (fr.closure.getD .poison) := by
  cases hc : fr.closure with
  | none => exact True.intro
  | some c => exact h.closure c hc

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

/-! ## Every op keeps values avoiding `U` -/

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

theorem writeRes_avoids {what : String} {M : Mem} (hM : M.Avoids U) {p : Ptr} {bs : Array Byte}
    (hb : ¬ U p.blk → BAv U bs) {y : Val} (h : writeRes what (M.write p bs) = .ok y) :
    Val.Avoids U y := by
  cases hw : M.write p bs with
  | none => rw [hw] at h; cases h
  | some M' => rw [hw] at h; cases h; exact memAvoids_write hM hw hb

/-- **A memory root keeps values avoiding frame temporaries.** -/
theorem memRoot_avoids (hU : TempU U) {ctx : Ctx} {v : Value} {argv : List Val}
    (hav : ∀ a ∈ argv, Val.Avoids U a) {y : Val} (h : memRoot ctx v argv = .ok y) :
    Val.Avoids U y := by
  unfold memRoot at h
  have m3 : ∀ {α : Type} {a b c : α}, c ∈ [a, b, c] := by simp
  have m2 : ∀ {α : Type} {a b : α}, b ∈ [a, b] := by simp
  have m23 : ∀ {α : Type} {a b c : α}, b ∈ [a, b, c] := by simp
  have m1 : ∀ {α : Type} {a : α}, a ∈ [a] := by simp
  split at h
  iterate 2
    · dsimp only at h
      split at h
      · exact writeRes_avoids (hav _ m3) (fun _ => encode_avoids _ (hav _ m23)) h
      · cases h
  iterate 2
    · dsimp only at h
      split at h
      · split at h
        · rename_i hs _ _ hr
          exact writeRes_avoids (hav _ m3)
            (fun _ => read_avoids (hav _ m3) hr (asPtrWord_notU hU (hav _ m23) hs)) h
        · cases h
      · cases h
  iterate 2
    · dsimp only at h
      split at h
      · refine writeRes_avoids (hav _ m2) (fun _ z hz => ?_) h
        simp only [Array.toList_replicate, List.mem_replicate] at hz
        rw [hz.2]; trivial
      · cases h
  · dsimp only at h
    split at h
    · cases h; exact memAvoids_varDefMem (hav _ m1) _ _ _
    · cases h
  · cases h; exact hav _ m1
  · cases h; exact DeferRel.memAvoids_filter (hav _ m1) _
  · cases h; exact hav _ m2
  · dsimp only at h
    split at h
    · split at h
      · cases h
      · cases h; exact hav _ (List.mem_cons_self)
    · cases h
  · split at h <;> cases h

/-- The frame values avoid `U` (a `LocalAddr` naming no block of `U`). -/
theorem frameVal_avoids (hU : TempU U) {ctx : Ctx} {v : Value} {x : Val}
    (hloc : ∀ n, v.op = .LocalAddr → v.aux = some n → ¬ U (frameBlk ctx.tabs ctx.act n))
    (hf : frameVal ctx v = some x) : Val.Avoids U x := by
  have hnot : ∀ b, (∀ a n, b ≠ .temp a n) → ¬ U b := fun b hb hu => by
    obtain ⟨a, n, hn⟩ := hU _ hu; exact hb a n hn
  unfold frameVal at hf
  split at hf
  · cases hf; exact hnot _ fun _ _ hn => nomatch hn
  · cases hf; trivial
  · rename_i hop
    cases hax : v.aux with
    | none => rw [hax] at hf; cases hf
    | some n => rw [hax] at hf; cases hf; exact hloc n hop hax
  · split at hf <;> cases hf
    · exact hnot _ fun _ _ hn => nomatch hn
    · trivial
  · split at hf <;> cases hf
    · refine ofStr_avoids ⟨?_, trivial, trivial⟩
      split
      · trivial
      · exact hnot _ fun _ _ hn => nomatch hn
    · trivial
  · cases hf

/-- **Every op keeps values avoiding frame temporaries**: on arguments that avoid `U`, in a frame
whose inputs avoid `U`, a value whose calls return avoiding results (`hcall`) and that is not
a `LocalAddr` of a block of `U` (`hloc`) evaluates to a result that avoids `U`. -/
theorem evalOp_avoids {env : Env} (hU : TempU U) {ctx : Ctx} {fr : Frame} (hfr : FrameOK U fr)
    {v : Value} {argv : List Val} {ty : Ty} {r : Val}
    (hcall : ∀ r, callOp env ctx v argv = .ok r → Val.Avoids U r)
    (hloc : ∀ n, v.op = .LocalAddr → v.aux = some n → ¬ U (frameBlk ctx.tabs ctx.act n))
    (hargs : ∀ z ∈ argv, Val.Avoids U z) (h : evalOp env ctx fr v argv ty = .ok r) :
    Val.Avoids U r := by
  unfold evalOp at h
  split at h
  · cases h; exact hfr.mem0
  · split at h
    · exact argVal_avoids hU hfr h
    · cases h
  · split at h
    · exact argVal_avoids hU hfr h
    · cases h
  · cases h
    unfold argFloat
    split
    · split
      · rename_i hx; exact argVal_avoids hU hfr hx
      · trivial
    · trivial
  · exact absurd h panicBounds_not_ok
  iterate 6 exact hcall _ h
  · cases h; exact hfr.closure_getD
  iterate 11 exact memRoot_avoids hU hargs h
  · split at h
    · cases h; exact frameVal_avoids hU hloc (by assumption)
    · split at h
      · exact atomicRoot_avoids hU hargs h
      · cases h; exact evalPure_avoids hU _ _ _ _ hargs

/-- A call on avoiding arguments returns an avoiding result (the contracts are frame-safe). -/
theorem callOp_avoids {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx} {v : Value}
    {argv : List Val} (hargs : ∀ z ∈ argv, Val.Avoids U z) :
    ∀ r, callOp env ctx v argv = .ok r → Val.Avoids U r := by
  intro r h
  rcases List.eq_nil_or_concat argv with rfl | ⟨L, w, rfl⟩
  · obtain ⟨msg, hm⟩ := callOp_nil_stuck (env := env) (ctx := ctx) (v := v)
    rw [hm] at h; cases h
  · rw [List.concat_eq_append] at hargs h
    exact ((callOp_rel hfs hU (.refl w) hargs).1 r h).1

/-! ## The source step -/

theorem wordShaped_iff {tabs : Tables} {t : TypeRef} :
    wordShaped tabs t = true ↔ (∃ e, tabs.ty t = .ptr e) ∨ tabs.ty t = .int .w64 := by
  unfold wordShaped
  split
  · rename_i e he; exact ⟨fun _ => .inl ⟨e, he⟩, fun _ => rfl⟩
  · rename_i he; exact ⟨fun _ => .inr he, fun _ => rfl⟩
  · rename_i hne hni
    exact ⟨fun h => (nomatch h), fun h => by
      rcases h with ⟨e, he⟩ | he
      · exact absurd he (hne e)
      · exact absurd he hni⟩

theorem evalOp_localAddr {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .LocalAddr) :
    evalOp env ctx fr v argv ty = .ok (match v.aux with
      | some n => .ptr ⟨frameBlk ctx.tabs ctx.act n, 0⟩
      | none => .poison) := by
  simp only [evalOp, frameVal, hop]
  cases v.aux <;> rfl

/-- A pointer into a temporary is `poison` at a shape that is not a word. -/
theorem retype_temp_avoids (U : Blk → Prop) {t : Ty} (ht : ∀ e, t ≠ .ptr e) (hi : t ≠ .int .w64)
    (a n : Nat) (off : BitVec 64) : Val.Avoids U ((Val.ptr ⟨.temp a n, off⟩).retype t) := by
  cases t with
  | int w => cases w <;> first | exact absurd rfl hi | trivial
  | ptr e => exact absurd rfl (ht e)
  | _ => trivial

/-- At a word shape a pointer into a temporary stays itself (it has no integer form) or is
`poison` (outside its window). -/
theorem retype_word_shape {t : Ty} (ht : (∃ e, t = .ptr e) ∨ t = .int .w64) {z : Val} {n : Nat}
    (h : z = .poison ∨ ∃ off, z = .ptr ⟨.temp 0 n, off⟩) :
    z.retype t = .poison ∨ ∃ off, z.retype t = .ptr ⟨.temp 0 n, off⟩ := by
  rcases h with rfl | ⟨off, rfl⟩
  · exact .inl (by cases t <;> rfl)
  · have hw : (Val.ptr ⟨.temp 0 n, off⟩).retype t = Ptr.word ⟨.temp 0 n, off⟩ := by
      rcases ht with ⟨e, rfl⟩ | rfl <;> rfl
    rw [hw]
    rcases Ptr.word_cases ⟨.temp 0 n, off⟩ with ⟨-, h⟩ | ⟨hc, -⟩ | ⟨-, h⟩
    · exact .inr ⟨off, h⟩
    · simp at hc
    · exact .inl h

theorem ptrRes_temp {n : Nat} (p : Ptr) (hp : p.blk = .temp 0 n) :
    PtrOps.ptrRes p = .poison ∨ ∃ off, PtrOps.ptrRes p = .ptr ⟨.temp 0 n, off⟩ := by
  obtain ⟨b, off⟩ := p
  simp only at hp
  subst hp
  unfold PtrOps.ptrRes
  split
  · rename_i hw
    exact .inr ⟨off, Ptr.word_of_held (Ptr.held_iff.2 ⟨Ptr.convertible_temp 0 n off, hw⟩)⟩
  · exact .inl rfl

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
    have hw : (∃ e, tabs.ty fv.type = .ptr e) ∨ tabs.ty fv.type = .int .w64 :=
      wordShaped_iff.1 hps
    split at htag
    · rename_i hla
      have hla' : fv.op = .LocalAddr := beq_iff_eq.1 hla
      have hfb : frameBlk (Ctx.make tabs f).tabs (Ctx.make tabs f).act n = .temp 0 n :=
        frameBlk_temp (R.temp n hnE) 0
      rw [evalOp_localAddr hla', htag] at hr
      simp only [hfb] at hr
      cases hr
      exact retype_word_shape hw (.inr ⟨0, rfl⟩)
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
          exact retype_word_shape hw (prop_tainted hp _ _ _ hzI)
    · cases htag
  · refine ⟨fun n hn hnE => absurd ⟨n, hn, hnE⟩ ht, fun _ => ?_⟩
    obtain ⟨gv, hgv, hk⟩ := R.value x fv hfv
    rcases hk with ⟨hs, -⟩ | ⟨he, n, hname', hnE⟩
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
      by_cases hla : fv.op = .LocalAddr
      · rw [evalOp_localAddr hla] at hr
        cases hr
        cases hax : fv.aux with
        | none => exact retype_avoids hU _ trivial
        | some n =>
          by_cases hps : wordShaped tabs fv.type = true
          · refine retype_avoids hU _ ?_
            show ¬ UE E (frameBlk tabs 0 n)
            rintro ⟨m, hmE, hm⟩
            have hnm : n = m := by
              unfold frameBlk at hm; split at hm <;> cases hm; rfl
            subst hnm
            refine ht ⟨n, ?_, hmE⟩
            rw [← htag]
            unfold tagStep
            simp [hps, hla, hax]
          · have hnp : ∀ e, tabs.ty fv.type ≠ .ptr e := fun e he =>
              hps (wordShaped_iff.2 (.inl ⟨e, he⟩))
            have hni : tabs.ty fv.type ≠ .int .w64 := fun he => hps (wordShaped_iff.2 (.inr he))
            show Val.Avoids _ ((Val.ptr ⟨frameBlk tabs 0 n, 0⟩).retype _)
            unfold frameBlk
            split
            · exact retype_avoids hU _ (show ¬ UE E (.local 0 n) from fun ⟨m, _, hm⟩ => by cases hm)
            · exact retype_temp_avoids _ hnp hni 0 n 0
      · exact retype_avoids hU _ (evalOp_avoids hU hfr (callOp_avoids hfs hU hargA)
          (fun _ h _ => absurd h hla) hargA hr)
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
        exact memAvoids_varDefMem (hmA M (by simp)) _ _ _
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
