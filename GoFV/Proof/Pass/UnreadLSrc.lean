import GoFV.Proof.Pass.UnreadLPure
import GoFV.Proof.EvalL

/-!
# elim unread autos on `runL`: the source's values avoid the eliminated variables

A lowered value whose arguments avoid a set `U` of frame temporaries, in a frame whose inputs
avoid `U`, evaluates (`evalValueL` with `faulting = false`, `runL`'s mode) to a value that avoids
`U`, or panics with a value and memory that avoid `U`, provided its symbol (`symAddr`) and
`LocalAddr` name no block of `U` (`SymOK`): generic ops by dead auto elim's `DAE.evalOp_avoids`,
the arm64 ops of `arm64Op` one by one (`arm64Op_av`), the pure arm64 ops by `evalPure_av`. For
`U = UE E`, a value whose aux is no variable of `E` has `SymOK` (`symOK_of`).
-/

namespace GoFV.Proof.UnreadL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.DAE

variable {U : Blk → Prop}

theorem callArgs_av (hU : TempU U) (k : Nat) (tabs : Tables) (ins : List ABIParam) {argv : List Val}
    (h : ∀ z ∈ argv, Val.Avoids U z) :
    ∀ z ∈ argv.take k ++ fitPieces tabs ins (argv.drop k), Val.Avoids U z := by
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · exact h z (List.mem_of_mem_take hz)
  · exact fitPieces_av hU tabs ins (fun y hy => h y (List.mem_of_mem_drop hy)) z hz

theorem mapM_ofOption_some {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L →
      l.mapM r = some L
  | [], L, h => by cases h; rfl
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : r a with
    | none => rw [ha] at h; cases h
    | some z =>
      rw [ha] at h
      change Res.bind (List.mapM (fun a => Res.ofOption (m a) (r a)) l) _ = _ at h
      cases hl : l.mapM (fun a => Res.ofOption (m a) (r a)) with
      | ok L' =>
        rw [hl] at h; cases h
        simp [List.mapM_cons, ha, mapM_ofOption_some hl]
      | panic e m' => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h

/-- The argument registers `evalValueL` reads. -/
theorem argVals_of_mapM {m : ID → String} {fr : Frame} {as : Array ID} {L : List Val}
    (h : as.toList.mapM (fun a => Res.ofOption (m a) (fr.regs[a]?).join) = .ok L) :
    CSE.argVals fr as = some L :=
  mapM_ofOption_some h

/-- **The ops of `arm64Op` keep values avoiding `U`.** -/
theorem arm64Op_av {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx} {fr : Frame}
    (hfr : FrameOK U fr) {v : Value} (hs : SymOK U ctx v) {argv : List Val} {ty : Ty} {r : Val}
    (hargs : ∀ z ∈ argv, Val.Avoids U z) (h : arm64Op false env ctx fr v argv ty = .ok r) :
    Val.Avoids U r := by
  unfold arm64Op at h
  simp only [nilFaults, Bool.not_false, ite_true] at h
  split at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | exact writeRes_av h (fun M hM => memAvoids_write (hargs (.mem _) (by simp)) hM
        (fun _ => storeBytes_av _ (hargs _ (by simp))))
    | exact writeRes_av h (fun M hM => memAvoids_write (hargs (.mem _) (by simp)) hM
        (fun _ => bav_append (storeBytes_av _ (hargs _ (by simp)))
          (storeBytes_av _ (hargs _ (by simp)))))
    | exact callOp_avoids hfs hU (callArgs_av hU _ _ _ hargs) r h
    | exact memRoot_avoids hU hargs h
    | exact absurd h panicBounds_not_ok
    | exact atomicRoot_avoids hU (atomicArgs_av hU _ hargs) h
    | (cases h; first
        | exact True.intro
        | exact elim_ld hU hs (hargs _ (by simp)) (hargs (.mem _) (by simp)) _ _ _
        | exact elim_ldPair hU hs (hargs _ (by simp)) (hargs (.mem _) (by simp)) _ _ _
        | exact elim_ld16 hs (hargs _ (by simp)) (hargs (.mem _) (by simp))
        | exact elim_addr hs (hargs _ (by simp))
        | exact res_av _ _
        | exact regVal_av _ (hargs _ (by simp))
        | (rw [hfr.closure]; exact True.intro)
        | exact memEq_avoids _
        | exact hargs (.mem _) (by simp)
        | exact evalPure_av hU _ _ _ _ hargs)

/-- **A lowered op keeps values avoiding `U`.** -/
theorem evalOpL_av {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx} {fr : Frame}
    (hfr : FrameOK U fr) {v : Value} (hs : SymOK U ctx v)
    (hloc : ∀ n, v.op = .LocalAddr → v.aux = some n → ¬ U (frameBlk ctx.tabs ctx.act n))
    {argv : List Val} {ty : Ty} {r : Val} (hargs : ∀ z ∈ argv, Val.Avoids U z)
    (h : evalOpL false env ctx fr v argv ty = .ok r) : Val.Avoids U r := by
  unfold evalOpL at h
  split at h
  · exact evalOp_avoids hU hfr (callOp_avoids hfs hU hargs) hloc hargs h
  · split at h
    all_goals first
      | exact arm64Op_av hfs hU hfr hs hargs h
      | (split at h
         · exact atomicRoot_avoids hU hargs h
         · cases h; exact evalPure_av hU _ _ _ _ hargs)

/-- A panicking `panicBounds` panics with its memory argument. -/
theorem panicBounds_av {k : Int64} {argv : List Val} (hargs : ∀ z ∈ argv, Val.Avoids U z)
    {e : Panic} {m : Mem} (h : panicBounds k argv = .panic e m) : e.Avoids U ∧ m.Avoids U := by
  unfold panicBounds at h
  split at h
  · cases h; exact ⟨trivial, hargs (.mem _) (by simp)⟩
  · cases h

theorem arm64Op_panic_av {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx}
    {fr : Frame} {v : Value} {argv : List Val} {ty : Ty} (hargs : ∀ z ∈ argv, Val.Avoids U z)
    {e : Panic} {m : Mem} (h : arm64Op false env ctx fr v argv ty = .panic e m) :
    e.Avoids U ∧ m.Avoids U := by
  unfold arm64Op at h
  simp only [nilFaults, Bool.not_false, ite_true] at h
  split at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; done)
    | exact absurd h (by unfold writeRes; split <;> nofun)
    | exact callOp_panic_avoids hfs hU (callArgs_av hU _ _ _ hargs) h
    | exact memRoot_panic_avoids hargs h
    | exact panicBounds_av hargs h
    | exact panicBounds_av (fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl
        all_goals first | exact True.intro | exact hargs _ (by simp)) h
    | exact absurd h atomicRoot_ne_panic

/-- **A lowered op on arguments avoiding `U` panics avoiding `U`.** -/
theorem evalOpL_panic_av {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx}
    {fr : Frame} {v : Value} {argv : List Val} {ty : Ty} (hargs : ∀ z ∈ argv, Val.Avoids U z)
    {e : Panic} {m : Mem} (h : evalOpL false env ctx fr v argv ty = .panic e m) :
    e.Avoids U ∧ m.Avoids U := by
  unfold evalOpL at h
  split at h
  · exact evalOp_panic_avoids hfs hU hargs h
  · split at h
    all_goals first
      | exact arm64Op_panic_av hfs hU hargs h
      | (split at h
         · exact absurd h atomicRoot_ne_panic
         · cases h)

/-- **A lowered value keeps values avoiding `U`.** -/
theorem evalValueL_av {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {md : LMode}
    (hmd : md.faulting = false) {ctx : Ctx} {fr : Frame} (hfr : FrameOK U fr) {v : Value}
    (hs : SymOK U ctx v)
    (hloc : ∀ n, v.op = .LocalAddr → v.aux = some n → ¬ U (frameBlk ctx.tabs ctx.act n))
    (hargs : ∀ a ∈ v.args, ∀ z, fr.regs[a]? = some (some z) → Val.Avoids U z) {y : Val}
    (h : evalValueL md env ctx fr v = .ok y) : Val.Avoids U y := by
  unfold evalValueL at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e m => rw [hm] at h; cases h
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    cases ho : evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | panic e m => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h
    | ok r =>
      rw [ho] at h
      cases h
      rw [hmd] at ho
      refine mdRetype_av hU md _ (evalOpL_av hfs hU hfr hs hloc (fun z hz => ?_) ho)
      obtain ⟨a, ha, hz'⟩ := argVals_mem (argVals_of_mapM hm) hz
      exact hargs a ha z hz'

/-- **A panicking lowered value panics avoiding `U`.** -/
theorem evalValueL_panic_av {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {md : LMode}
    (hmd : md.faulting = false) {ctx : Ctx} {fr : Frame} {v : Value}
    (hargs : ∀ a ∈ v.args, ∀ z, fr.regs[a]? = some (some z) → Val.Avoids U z) {e : Panic} {m : Mem}
    (h : evalValueL md env ctx fr v = .panic e m) : e.Avoids U ∧ m.Avoids U := by
  unfold evalValueL at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e m => exact absurd hm mapM_ofOption_ne_panic
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    cases ho : evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h
    | panic e' m' =>
      rw [ho] at h
      cases h
      rw [hmd] at ho
      refine evalOpL_panic_av hfs hU (fun z hz => ?_) ho
      obtain ⟨a, ha, hz'⟩ := argVals_mem (argVals_of_mapM hm) hz
      exact hargs a ha z hz'

/-! ## Symbols of values that name no eliminated variable -/

theorem frameBlk_notUE {E : List AuxRef} {tabs : Tables} {n : AuxRef} (hn : n ∉ E) :
    ¬ UE E (frameBlk tabs 0 n) := by
  rintro ⟨n', hn', he⟩
  unfold frameBlk at he
  split at he
  · cases he
  · cases he; exact hn hn'

/-- A value whose aux is no variable of `E` addresses no block of `UE E`. -/
theorem symOK_of {E : List AuxRef} {ctx : Ctx} (hact : ctx.act = 0) {v : Value}
    (hv : ∀ n, v.aux = some n → n ∉ E) : SymOK (UE E) ctx v := by
  intro a p ha hp
  unfold symAddr at hp
  split at hp
  · rename_i n hn
    split at hp
    · cases hp; rintro ⟨n', -, he⟩; cases he
    · cases hp; rw [hact]; exact frameBlk_notUE (hv n hn)
    · cases hp
  · exact addr_notU (tempU_UE E) ha _ hp

end GoFV.Proof.UnreadL
