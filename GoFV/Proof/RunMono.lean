import GoFV.Proof.Refine
import GoFV.Proof.PureMono
import GoFV.Proof.CallMono

/-!
# The interpreter is monotone in refinement

`Res.Refines`: refinement of value results (`Res.Rel Refines`: results refined, the same panic
with refined memories, a stuck source refined by anything). `EvalOpMono P`: in every
environment with `P`, `evalOp` maps refined arguments to refined results, for contexts that
differ only in the function, its schedule and its value types, and frames with the same
arguments, initial memory, argument images and closure context.
-/

namespace GoFV.SSA.Sem

/-- Refinement of value results: `ok a ⊑ ok b` if `Refines a b`, `panic e m ⊑ panic e m'` if
`Mem.Refines m m'`, `stuck _ ⊑ r` for every `r`. -/
abbrev Res.Refines : Res Val → Res Val → Prop := Res.Rel Sem.Refines

theorem Res.Refines.refl : (r : Res Val) → Res.Refines r r
  | .ok a => .ok (Sem.Refines.refl a)
  | .panic e m => .panic e (Mem.Refines.refl m)
  | .stuck msg => .stuck msg _

/-- Outcomes of a contract: results and memory refined, the same panic with refined memories,
a stuck source refined by anything. -/
inductive COutcome.Refines : COutcome → COutcome → Prop where
  | returned {rs rs' : List Val} {m m' : Mem} : RefinesList rs rs' → Mem.Refines m m' →
      COutcome.Refines (.returned rs m) (.returned rs' m')
  | panicked (e : Panic) {m m' : Mem} : Mem.Refines m m' →
      COutcome.Refines (.panicked e m) (.panicked e m')
  | stuck (msg : String) (o : COutcome) : COutcome.Refines (.stuck msg) o

/-- A contract maps refined poison-free arguments and closure context and a refined memory to a
refined outcome (calls observe their arguments: a source call on `poison` is stuck). -/
def Contract.Mono (c : Contract) : Prop :=
  ∀ {args args' : List Val} {clo clo' : Option Val} {m m' : Mem},
    args.any Val.hasPoison = false → (clo.map Val.hasPoison).getD false = false →
    RefinesList args args' → OptRefines clo clo' → Mem.Refines m m' →
      COutcome.Refines (c args clo m) (c args' clo' m')

/-- Every contract of the environment is monotone. -/
def Env.Mono (env : Env) : Prop := ∀ name c, env.extern name = some c → c.Mono

/-- Non-vacuity: the panicking runtime entry points of P1 are monotone. -/
theorem Env.p1_mono : Env.p1.Mono := by
  intro name c h
  unfold Env.p1 at h
  simp only at h
  split at h <;> (try cases h) <;> intro _ _ _ _ _ _ _ _ _ _ hm <;> exact .panicked _ hm

/-! ## Lists -/

/-- A predicate that a refinement can only falsify on its source (`poison` tests). -/
theorem RefinesList.any_false {p : Val → Bool}
    (hp : ∀ {a b}, Refines a b → p a = false → p b = false) :
    {as bs : List Val} → RefinesList as bs → as.any p = false → bs.any p = false
  | _, _, .nil, _ => rfl
  | _, _, .cons h t, ha => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at ha ⊢
    exact ⟨hp h ha.1, RefinesList.any_false hp t ha.2⟩

end GoFV.SSA.Sem

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- `evalOp` is monotone in every environment with `P`. -/
def EvalOpMono (P : Env → Prop) : Prop :=
  ∀ (env : Env), P env → ∀ (ctx ctx' : Ctx),
    ctx' = { ctx with f := ctx'.f, sched := ctx'.sched, tys := ctx'.tys } →
    ∀ (fr fr' : Frame), fr'.args = fr.args → fr'.mem0 = fr.mem0 → fr'.images = fr.images →
    fr'.closure = fr.closure →
    ∀ (v : Value) (ty : Ty) {argv argv' : List Val}, RefinesList argv argv' →
      Res.Refines (evalOp env ctx fr v argv ty) (evalOp env ctx' fr' v argv' ty)

/-! ## The roots -/

theorem panicBounds_mono (k : Int64) {as bs : List Val} (h : RefinesList as bs) :
    Res.Refines (panicBounds k as) (panicBounds k bs) := by
  unfold panicBounds
  split
  · obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
    cases h.nil_inv; cases h1; cases h2; cases h3 with | mem hm => exact .panic _ hm
  · exact .stuck _ _

theorem callOp_mono {env : Env} (hE : env.Mono) (ctx : Ctx) (v : Value) {as bs : List Val}
    (h : RefinesList as bs) : Res.Refines (callOp env ctx v as) (callOp env ctx v bs) := by
  obtain ⟨hc, hclo, hrest⟩ := callTarget_mono ctx v h
  unfold callOp
  revert hc hclo hrest
  generalize callTarget ctx v as = T
  generalize callTarget ctx v bs = T'
  rcases T with ⟨callee?, clo, rest⟩
  rcases T' with ⟨callee?', clo', rest'⟩
  intro hc hclo hrest
  dsimp only at hc hclo hrest ⊢
  cases callee? with
  | none => exact .stuck _ _
  | some callee =>
    rcases hc with hc | hc
    · cases hc
    · subst hc
      dsimp only [bind, Res.bind, Res.ofOption]
      rcases hrest.getLast? with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
      · rw [h1]; exact .stuck _ _
      · rw [h1, h2]
        cases ha with
        | @mem m m' hm =>
          dsimp only
          have hpieces := hrest.dropLast
          -- the Go-typed arguments
          by_cases hpost : (v.op == Op.StaticCall || v.op == Op.ClosureCall || v.op == Op.InterCall) = true
          · simp only [hpost, ↓reduceIte]
            cases hd : decodeArgs ctx.tabs ctx.act m _ rest.dropLast with
            | none => exact .stuck _ _
            | some args =>
              obtain ⟨args', hd', ha⟩ := decodeArgs_mono ctx.tabs ctx.act hm _ hpieces hd
              rw [hd']
              dsimp only
              revert ha
              generalize args = A
              generalize args' = A'
              intro ha
              split
              · exact .stuck _ _
              · next hp =>
                simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
                have hp1 := ha.any_hasPoison hp.1
                have hp2 : (clo'.map Val.hasPoison).getD false = false := by
                  cases hclo with
                  | none => rfl
                  | some hcc => exact (hcc.noPoison (by simpa using hp.2)).1
                simp only [hp1, hp2, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
                cases hx : env.extern callee with
                | none => exact .stuck _ _
                | some c =>
                  dsimp only
                  have := hE _ _ hx hp.1 hp.2 ha hclo (hm.poisonBlock (.outargs ctx.act))
                  revert this
                  generalize c A clo (m.poisonBlock (.outargs ctx.act)) = o
                  generalize c A' clo' (m'.poisonBlock (.outargs ctx.act)) = o'
                  intro ho
                  cases ho with
                  | returned hr0 hm' =>
                    dsimp only
                    cases he : encodeResults ctx.tabs ctx.act _ _ _ with
                    | none => exact .stuck _ _
                    | some r =>
                      obtain ⟨r', he', hr1, hr2⟩ := encodeResults_mono ctx.tabs ctx.act _ (retypeResults_mono ctx.tabs _ hr0) hm' he
                      rw [he']
                      dsimp only
                      exact .ok (.tuple (hr1.append (.cons (.mem hr2) (.cons (Sem.Refines.refl _) .nil))))
                  | panicked e hm' => exact .panic e hm'
                  | stuck msg o => exact .stuck _ _
          · simp only [hpost, Bool.false_eq_true, ↓reduceIte]
            dsimp only [pure, Res.bind]
            have ha := hpieces
            revert ha
            generalize rest.dropLast = A
            generalize rest'.dropLast = A'
            intro ha
            split
            · exact .stuck _ _
            · next hp =>
              simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
              have hp1 := ha.any_hasPoison hp.1
              have hp2 : (clo'.map Val.hasPoison).getD false = false := by
                cases hclo with
                | none => rfl
                | some hcc => exact (hcc.noPoison (by simpa using hp.2)).1
              simp only [hp1, hp2, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
              cases hx : env.extern callee with
              | none => exact .stuck _ _
              | some c =>
                dsimp only
                have := hE _ _ hx hp.1 hp.2 ha hclo (hm.poisonBlock (.outargs ctx.act))
                revert this
                generalize c A clo (m.poisonBlock (.outargs ctx.act)) = o
                generalize c A' clo' (m'.poisonBlock (.outargs ctx.act)) = o'
                intro ho
                cases ho with
                | returned hr0 hm' =>
                  dsimp only
                  cases he : encodeResults ctx.tabs ctx.act _ _ _ with
                  | none => exact .stuck _ _
                  | some r =>
                    obtain ⟨r', he', hr1, hr2⟩ := encodeResults_mono ctx.tabs ctx.act _ (retypeResults_mono ctx.tabs _ hr0) hm' he
                    rw [he']
                    dsimp only
                    exact .ok (.tuple ((retypeResults_mono ctx.tabs _ hr0).append (.cons (.mem hr2) (.cons (Sem.Refines.refl _) .nil))))
                | panicked e hm' => exact .panic e hm'
                | stuck msg o => exact .stuck _ _
        | _ => exact .stuck _ _

theorem writeRes_mono (w w' : String) {a b : Option Mem}
    (h : ∀ m, a = some m → ∃ m', b = some m' ∧ Mem.Refines m m') :
    Res.Refines (writeRes w a) (writeRes w' b) := by
  cases a with
  | none => exact .stuck _ _
  | some m =>
    obtain ⟨m', rfl, hm⟩ := h m rfl
    exact .ok (.mem hm)

theorem memRoot_mono (ctx : Ctx) (v : Value) {as bs : List Val} (h : RefinesList as bs) :
    Res.Refines (memRoot ctx v as) (memRoot ctx v bs) := by
  unfold memRoot
  split
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
    cases h.nil_inv; cases h1; cases h3 with | mem hm =>
    rw [heq]; dsimp only
    exact writeRes_mono _ _ fun m1 hw => hm.write (encode_mono _ h2) hw
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
    cases h.nil_inv; cases h1; cases h3 with | mem hm =>
    rw [heq]; dsimp only
    exact writeRes_mono _ _ fun m1 hw => hm.write (encode_mono _ h2) hw
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
    cases h.nil_inv; cases h1; cases h2; cases h3 with | mem hm =>
    rw [heq]; dsimp only
    cases hr : Mem.read _ _ _ with
    | none => exact .stuck _ _
    | some bs =>
      obtain ⟨bs', hr', hb⟩ := hm.read hr
      rw [hr']
      exact writeRes_mono _ _ fun m1 hw => hm.write hb hw
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
    cases h.nil_inv; cases h1; cases h2; cases h3 with | mem hm =>
    rw [heq]; dsimp only
    cases hr : Mem.read _ _ _ with
    | none => exact .stuck _ _
    | some bs =>
      obtain ⟨bs', hr', hb⟩ := hm.read hr
      rw [hr']
      exact writeRes_mono _ _ fun m1 hw => hm.write hb hw
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    cases h.nil_inv
    cases h1; cases h2 with | mem hm =>
    rw [heq]; dsimp only
    exact writeRes_mono _ _ fun m1 hw => hm.write (BytesRefineA.refl _) hw
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    cases h.nil_inv
    cases h1; cases h2 with | mem hm =>
    rw [heq]; dsimp only
    exact writeRes_mono _ _ fun m1 hw => hm.write (BytesRefineA.refl _) hw
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    cases h.nil_inv
    cases h1 with | mem hm =>
    rw [heq]; dsimp only
    split
    · exact .ok (.mem (hm.poisonBlock _))
    · exact .stuck _ _
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    cases h.nil_inv
    cases h1 with | mem hm =>
    rw [heq]; dsimp only
    exact .ok (.mem hm)
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    cases h.nil_inv
    cases h1 with | mem hm =>
    rw [heq]; dsimp only
    exact .ok (.mem hm)
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    cases h.nil_inv
    cases h2 with | mem hm =>
    rw [heq]; dsimp only
    exact .ok (.mem hm)
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    cases h.nil_inv
    cases h1; cases h2 with | mem hm =>
    rw [heq]; dsimp only
    split
    · exact .panic _ hm
    · exact .ok (Sem.Refines.refl _)
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    cases h.nil_inv
    cases h1; cases h2 with | mem hm =>
    rw [heq]; dsimp only
    split
    · exact .panic _ hm
    · exact .ok (Sem.Refines.refl _)
  · split <;> exact .stuck _ _


/-! ## `evalOp` -/

/-- `evalOp` reads of the context only its tables, parameters and activation, and of the frame
only its initial memory and argument images. -/
theorem evalOp_congr_ctx (env : Env) {ctx ctx' : Ctx}
    (hctx : ctx' = { ctx with f := ctx'.f, sched := ctx'.sched, tys := ctx'.tys })
    {fr fr' : Frame} (hargs : fr'.args = fr.args) (hmem : fr'.mem0 = fr.mem0)
    (himg : fr'.images = fr.images) (hclo : fr'.closure = fr.closure) (v : Value) (argv : List Val) (ty : Ty) :
    evalOp env ctx' fr' v argv ty = evalOp env ctx fr v argv ty := by
  have hfr : fr' = { fr with regs := fr'.regs } := by
    cases fr; cases fr'; simp_all
  rw [hctx, hfr]
  rfl

/-- `evalOp` on refined arguments, in the same context and frame. -/
theorem evalOp_mono_same {env : Env} (hE : env.Mono) (ctx : Ctx) (fr : Frame) (v : Value)
    (ty : Ty) {argv argv' : List Val} (h : RefinesList argv argv') :
    Res.Refines (evalOp env ctx fr v argv ty) (evalOp env ctx fr v argv' ty) := by
  unfold evalOp
  split
  all_goals first
    | exact Res.Refines.refl _
    | exact panicBounds_mono _ h
    | exact memRoot_mono ctx v h
    | exact callOp_mono hE ctx v h
    | (split
       · exact Res.Refines.refl _
       · split
         · exact .stuck _ _
         · exact .ok (evalPure_mono _ _ _ _ h))

/-- **`evalOp` is monotone** in every environment whose contracts are. -/
theorem evalOp_mono : EvalOpMono Env.Mono := by
  intro env hE ctx ctx' hctx fr fr' hargs hmem himg hclo v ty argv argv' h
  rw [evalOp_congr_ctx env hctx hargs hmem himg hclo]
  exact evalOp_mono_same hE ctx fr v ty h


/-! ## Terminators -/

/-- What a terminator does, refined: the same edge, or results and memory refined. -/
inductive Next.Refines : Next → Next → Prop where
  | goto (e : Edge) : Next.Refines (.goto e) (.goto e)
  | ret {rs rs' : List Val} {m m' : Mem} : RefinesList rs rs' → Mem.Refines m m' →
      Next.Refines (.ret rs m) (.ret rs' m')

/-- Registers refined: the same number, every defined register of `r` defined in `r'`,
refined. -/
def RegsRefine (r r' : Array (Option Val)) : Prop :=
  r.size = r'.size ∧ ∀ (a : ID) x, (r[a]?).join = some x → ∃ y, (r'[a]?).join = some y ∧ Sem.Refines x y

/-- The controls of `b` refined from `fr` to `fr'`. -/
def ControlsRefine (fr fr' : Frame) (b : Block) : Prop :=
  ∀ c ∈ b.controls, ∀ x, (fr.regs[c]?).join = some x →
    ∃ y, (fr'.regs[c]?).join = some y ∧ Sem.Refines x y

theorem RegsRefine.controls {fr fr' : Frame} (h : RegsRefine fr.regs fr'.regs) (b : Block) :
    ControlsRefine fr fr' b :=
  fun c _ => h.2 c

theorem control_mono {fr fr' : Frame} {b : Block} (h : ControlsRefine fr fr' b) (k : Nat) :
    Res.Refines (Sem.control fr b k) (Sem.control fr' b k) := by
  unfold Sem.control
  cases hc : b.controls[k]? with
  | none => exact .stuck _ _
  | some c =>
    dsimp only
    cases hx : (fr.regs[c]?).join with
    | none => exact .stuck _ _
    | some x =>
      obtain ⟨y, hy, hxy⟩ := h c (Array.mem_of_getElem? hc) x hx
      rw [hy]
      exact .ok hxy

theorem succ_refl (b : Block) (k : Nat) : Res.Rel Next.Refines (Sem.succ b k) (Sem.succ b k) := by
  unfold Sem.succ
  cases b.succs[k]? with
  | none => exact .stuck _ _
  | some e => exact .ok (.goto e)

/-- **The terminator is monotone**: on refined controls, the same edge, or refined results and
memory (a stuck source carries no obligation). -/
theorem stepTerm_mono {fr fr' : Frame} {b : Block} (h : ControlsRefine fr fr' b) :
    Res.Rel Next.Refines (stepTerm fr b) (stepTerm fr' b) := by
  unfold stepTerm
  split
  · exact succ_refl b 0
  · exact succ_refl b 0
  · refine Res.Rel.bind (control_mono h 0) fun x y hxy => ?_
    cases hxy with
    | bool c => cases c <;> exact succ_refl b _
    | _ => exact .stuck _ _
  · refine Res.Rel.bind (control_mono h 0) fun x y hxy => ?_
    cases hxy with
    | int w x => exact succ_refl b _
    | _ => exact .stuck _ _
  · refine Res.Rel.bind (control_mono h 0) fun x y hxy => ?_
    cases hxy with
    | tuple hl =>
      dsimp only
      rcases hl.getLast? with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
      · rw [h1]; exact .stuck _ _
      · rw [h1, h2]
        cases ha with
        | mem hm =>
          dsimp only
          split
          · exact .stuck _ _
          · next hp =>
            have hq := RefinesList.any_false ?pf hl.dropLast (Bool.eq_false_iff.2 hp)
            case pf => intro a b hab ha; cases hab <;> simp_all
            simp only [hq, Bool.false_eq_true, ↓reduceIte]
            exact .ok (.ret hl.dropLast hm)
        | _ => exact .stuck _ _
    | _ => exact .stuck _ _
  · exact .stuck _ _
  · exact .stuck _ _

end GoFV.Proof
