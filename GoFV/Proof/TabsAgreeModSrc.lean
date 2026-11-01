import GoFV.Proof.TabsAgreeModOps
import GoFV.Proof.Pass.DAESrc
import GoFV.Opt.TabsAgreeMod

/-!
# Running in tables with extra frame temporaries: the source avoids them

The source runs in the input tables, where the extra frame temporaries `X` do not exist; no
value of the function names them, no integer converts to a `temp` block, and the run's inputs
and the contracts' results hold no pointer into them. `evalOp_avoids`: a value whose op is in
`GoFV.Opt.tamPtrOps`, on arguments that avoid `X`, has a result that avoids `X` (the other values
have pointer-free shapes, `DAE.noPtr_avoids`). `evalOp_notArm`: an op `evalOp` does not evaluate
by name is `stuck` if it is a root (`evalOp_stuckRoot`) and `evalPure` otherwise.
-/

namespace GoFV.Proof.TabsMod

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.DSE

/-- `evalOp` of an op it does not evaluate by name. -/
theorem evalOp_notArm {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hn : v.op ∉ evalOpArms) :
    evalOp env ctx fr v argv ty =
      if isRoot v.op then .stuck s!"v{v.id}: {v.op.name} is not in phases P1–P3"
      else pure (evalPure v.op ty v.auxInt v.aux argv) := by
  have hf : frameVal ctx v = none := by
    unfold frameVal
    split <;> first | rfl | (rename_i heq; rw [heq] at hn; simp [evalOpArms] at hn)
  unfold evalOp
  split <;> first | (rename_i heq; rw [heq] at hn; simp [evalOpArms] at hn; done) | skip
  rw [hf]

/-- A root `evalOp` does not evaluate by name is `stuck`. -/
theorem evalOp_stuckRoot {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (h : stuckRoot v.op = true) : ∃ msg, evalOp env ctx fr v argv ty = .stuck msg := by
  unfold stuckRoot at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  have hn : v.op ∉ evalOpArms := by
    intro hm; rw [List.contains_iff_mem.2 hm] at h; cases h.2
  rw [evalOp_notArm hn, h.1]
  exact ⟨_, rfl⟩

/-- A non-root op `evalOp` does not evaluate by name is `evalPure`. -/
theorem evalOp_pure_of {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hn : v.op ∉ evalOpArms) (hr : isRoot v.op = false) :
    evalOp env ctx fr v argv ty = .ok (evalPure v.op ty v.auxInt v.aux argv) := by
  rw [evalOp_notArm hn, hr]; rfl

variable {X : Blk → Bool}

local notation "U" => fun b => X b = true

/-! ## The pure ops of `tamPtrOps` -/

theorem make_avoids {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Comp.make args) := by
  show Val.AvoidsList U args
  exact DAE.avoidsList_iff.2 h

theorem compSelect_avoids (i : Nat) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Comp.select i args) := by
  unfold Comp.select
  split
  · exact DAE.getD_avoids (h _ List.mem_cons_self) i
  · trivial

theorem selectAux_avoids (k : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Comp.selectAux k args) := by
  unfold Comp.selectAux
  split
  · trivial
  · exact compSelect_avoids _ h

theorem tupleMake_avoids {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Tuple.make args) := by
  unfold Tuple.make
  split
  · exact DAE.avoidsList_iff.2 h
  · trivial

theorem selectNAddr_avoids (k : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Tuple.selectNAddr k args) := by
  unfold Tuple.selectNAddr
  split
  · rename_i vs
    have hvs : ∀ z ∈ vs, Val.Avoids U z := DAE.avoidsList_iff.1 (h _ List.mem_cons_self)
    split
    · rename_i addrs ha
      have hA : ∀ z ∈ addrs, Val.Avoids U z :=
        DAE.avoidsList_iff.1 (hvs _ (List.mem_of_getLast? ha))
      split
      · trivial
      · split
        · rename_i p hp
          exact hA _ (List.mem_of_getElem? hp)
        · trivial
    · trivial
  · trivial

theorem int2_avoids {w : Width} {f : BitVec w.bits → BitVec w.bits → Val}
    (hf : ∀ x y, Val.Avoids U (f x y)) (args : List Val) : Val.Avoids U (int2 w f args) := by
  unfold int2
  split
  · split
    · exact hf _ _
    · trivial
  · trivial

theorem int3_avoids {w : Width} {f : BitVec w.bits → BitVec w.bits → BitVec w.bits → Val}
    (hf : ∀ x y z, Val.Avoids U (f x y z)) (args : List Val) : Val.Avoids U (int3 w f args) := by
  unfold int3
  split
  · split
    · exact hf _ _ _
    · trivial
  · trivial

/-- **The pure ops of `tamPtrOps`** on arguments that avoid `X` (`X` frame temporaries). -/
theorem evalPure_avoids (hX : TempX X) {op : Op} (hop : op ∈ tamPtrOps) (hn : op ∉ evalOpArms)
    (ty : Ty) (k : Int64) (aux : Option AuxRef) {args : List Val}
    (h : ∀ z ∈ args, Val.Avoids U z) : Val.Avoids U (evalPure op ty k aux args) := by
  have hU := tempU_of hX
  have hnil : ¬ U Blk.nil := fun hu => by obtain ⟨n, hn⟩ := hX _ hu; cases hn
  simp only [tamPtrOps, DAE.ptrOps, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_nil_iff, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- Phi
    exact True.intro
  · -- Copy
    rcases args with _ | ⟨x, _ | ⟨y, t⟩⟩
    · exact True.intro
    · exact h x List.mem_cons_self
    · exact True.intro
  · -- OffPtr
    exact DAE.offPtr_avoids _ h
  · -- AddPtr
    exact DAE.addPtr_avoids h
  · -- PtrIndex
    exact DAE.ptrIndex_avoids _ h
  · -- LocalAddr
    exact absurd (by decide) hn
  · -- Addr
    exact absurd (by decide) hn
  · -- ConstNil
    exact hnil
  · -- Convert
    exact DAE.convert_avoids hU _ h
  · -- CondSelect
    exact DAE.condSelect_avoids h
  · -- GetG
    exact True.intro
  · -- GetClosurePtr
    exact absurd (by decide) hn
  · -- Arg
    exact absurd (by decide) hn
  · -- ArgIntReg
    exact absurd (by decide) hn
  · -- InitMem
    exact absurd (by decide) hn
  · -- Select0
    exact DAE.select_avoids _ h
  · -- Select1
    exact DAE.select_avoids _ h
  · -- SelectN
    exact DAE.selectN_avoids _ h
  · -- MakeResult
    exact DAE.avoidsList_iff.2 h
  · -- Load
    exact DAE.loadOp_avoids hU _ h
  · -- AtomicLoad32
    exact DAE.atomicLoad_avoids hU _ h
  · -- AtomicLoad64
    exact DAE.atomicLoad_avoids hU _ h
  · -- AtomicLoadPtr
    exact DAE.atomicLoad_avoids hU _ h
  · -- Store
    exact absurd (by decide) hn
  · -- Zero
    exact absurd (by decide) hn
  · -- Move
    exact absurd (by decide) hn
  · -- VarDef
    exact absurd (by decide) hn
  · -- VarLive
    exact absurd (by decide) hn
  · -- KeepAlive
    exact absurd (by decide) hn
  · -- NilCheck
    exact absurd (by decide) hn
  · -- PanicBounds
    exact absurd (by decide) hn
  · -- StaticCall
    exact absurd (by decide) hn
  · -- InterCall
    exact absurd (by decide) hn
  · -- ClosureCall
    exact absurd (by decide) hn
  · -- AtomicStore32
    exact True.intro
  · -- AtomicStore64
    exact True.intro
  · -- AtomicAdd32
    exact True.intro
  · -- AtomicAdd32Variant
    exact True.intro
  · -- AtomicAdd64
    exact True.intro
  · -- AtomicCompareAndSwap32
    exact True.intro
  · -- AtomicCompareAndSwap32Variant
    exact True.intro
  · -- AtomicCompareAndSwap64
    exact True.intro
  · -- AtomicCompareAndSwap64Variant
    exact True.intro
  · -- StaticLECall
    exact absurd (by decide) hn
  · -- InterLECall
    exact absurd (by decide) hn
  · -- ClosureLECall
    exact absurd (by decide) hn
  · -- Dereference
    exact DAE.loadOp_avoids hU _ h
  · -- AtomicLoad8
    exact DAE.atomicLoad_avoids hU _ h
  · -- AtomicLoadAcq32
    exact DAE.atomicLoad_avoids hU _ h
  · -- AtomicLoadAcq64
    exact DAE.atomicLoad_avoids hU _ h
  · -- SelectNAddr
    exact selectNAddr_avoids _ h
  · -- MakeTuple
    exact tupleMake_avoids h
  · -- StringMake
    exact make_avoids h
  · -- SliceMake
    exact make_avoids h
  · -- IMake
    exact make_avoids h
  · -- ComplexMake
    exact make_avoids h
  · -- StructMake
    exact make_avoids h
  · -- ArrayMake1
    exact make_avoids h
  · -- StringPtr
    exact compSelect_avoids _ h
  · -- SlicePtr
    exact compSelect_avoids _ h
  · -- SlicePtrUnchecked
    exact compSelect_avoids _ h
  · -- ITab
    exact compSelect_avoids _ h
  · -- IData
    exact compSelect_avoids _ h
  · -- StructSelect
    exact selectAux_avoids _ h
  · -- ArraySelect
    exact selectAux_avoids _ h
  · -- ConstSlice
    exact ⟨hnil, trivial, trivial, trivial⟩
  · -- ConstInterface
    exact ⟨trivial, hnil, trivial⟩
  · -- ConstString
    exact absurd (by decide) hn
  · -- SP
    exact absurd (by decide) hn
  · -- Mul32uhilo
    refine int2_avoids (fun x y => ?_) _
    exact ⟨trivial, trivial, trivial⟩
  · -- Mul32uover
    refine int2_avoids (fun x y => ?_) _
    exact ⟨trivial, trivial, trivial⟩
  · -- Mul64uhilo
    refine int2_avoids (fun x y => ?_) _
    exact ⟨trivial, trivial, trivial⟩
  · -- Mul64uover
    refine int2_avoids (fun x y => ?_) _
    exact ⟨trivial, trivial, trivial⟩
  · -- Div128u
    refine int3_avoids (fun x y z => ?_) _
    split
    · exact True.intro
    · exact ⟨trivial, trivial, trivial⟩
  · -- Add64carry
    refine int3_avoids (fun x y z => ?_) _
    split
    · exact True.intro
    · exact ⟨trivial, trivial, trivial⟩
  · -- Sub64borrow
    refine int3_avoids (fun x y z => ?_) _
    split
    · exact True.intro
    · exact ⟨trivial, trivial, trivial⟩
  · -- Invalid
    exact True.intro

/-- The frame values avoid `X` (a `LocalAddr` naming no block of `X`). -/
theorem frameVal_avoids (hX : TempX X) {ctx : Ctx} {v : Value} {x : Val}
    (hloc : ∀ n, v.aux = some n → X (frameBlk ctx.tabs ctx.act n) = false)
    (hf : frameVal ctx v = some x) : Val.Avoids U x := by
  have hnot : ∀ b, (∀ n, b ≠ .temp 0 n) → ¬ U b := fun b hb hu => by
    obtain ⟨n, hn⟩ := hX _ hu; exact hb n hn
  unfold frameVal at hf
  split at hf
  · cases hf; exact hnot _ fun n hn => nomatch hn
  · cases hf; trivial
  · cases hax : v.aux with
    | none => rw [hax] at hf; cases hf
    | some n =>
      rw [hax] at hf; cases hf
      show ¬ X (frameBlk ctx.tabs ctx.act n) = true
      rw [hloc n hax]; nofun
  · split at hf <;> cases hf
    · exact hnot _ fun n hn => nomatch hn
    · trivial
  · split at hf <;> cases hf
    · refine ⟨?_, trivial, trivial⟩
      split
      · exact hnot _ fun n hn => by simp [Ptr.null] at hn
      · exact hnot _ fun n hn => nomatch hn
    · trivial
  · cases hf

/-- **A value of `tamPtrOps` on arguments that avoid `X` has a result that avoids `X`** (its
frame inputs avoid `X`, and a `LocalAddr` names no block of `X`). -/
theorem evalOp_avoids {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx} {fr : Frame}
    (hfr : DAE.FrameOK U fr) {v : Value}
    (hloc : ∀ n, v.aux = some n → X (frameBlk ctx.tabs ctx.act n) = false)
    {argv : List Val} {ty : Ty} {r : Val} (hop : v.op ∈ tamPtrOps)
    (hargs : ∀ z ∈ argv, Val.Avoids U z) (h : evalOp env ctx fr v argv ty = .ok r) :
    Val.Avoids U r := by
  have hU := tempU_of hX
  have hnot : ∀ b, (∀ n, b ≠ .temp 0 n) → ¬ U b := fun b hb hu => by
    obtain ⟨n, hn⟩ := hX _ hu; exact hb n hn
  by_cases harm : v.op ∈ evalOpArms
  rotate_left
  · by_cases hr : isRoot v.op = true
    · rw [evalOp_notArm harm, hr] at h; cases h
    · rw [evalOp_pure_of harm (by simpa using hr)] at h; cases h
      exact evalPure_avoids hX hop harm _ _ _ hargs
  have calls : v.op = .StaticLECall ∨ v.op = .StaticCall ∨ v.op = .ClosureLECall ∨
      v.op = .ClosureCall ∨ v.op = .InterLECall ∨ v.op = .InterCall → Val.Avoids U r := by
    intro ho
    have he : evalOp env ctx fr v argv ty = callOp env ctx v argv := by
      rcases ho with h | h | h | h | h | h <;> simp only [evalOp, h]
    rw [he] at h
    rcases List.eq_nil_or_concat argv with rfl | ⟨L, w, rfl⟩
    · obtain ⟨msg, hm⟩ := callOp_nil_stuck (env := env) (ctx := ctx) (v := v)
      rw [hm] at h; cases h
    · rw [List.concat_eq_append] at hargs h
      exact ((callOp_rel hE hX (.refl w) hargs).1 r h).1
  have excl : ∀ op, v.op = op → op ∉ tamPtrOps → Val.Avoids U r := fun op h1 hn =>
    absurd (h1 ▸ hop) hn
  have frameOps : v.op = .SP ∨ v.op = .GetCallerSP ∨ v.op = .LocalAddr ∨ v.op = .Addr ∨
      v.op = .ConstString → Val.Avoids U r := by
    intro ho
    cases hf : frameVal ctx v with
    | some x =>
      have hr : r = x := by
        rcases ho with h1 | h1 | h1 | h1 | h1 <;> (simp only [evalOp, h1, hf] at h; cases h; rfl)
      subst hr
      exact frameVal_avoids hX hloc hf
    | none =>
      rcases ho with h1 | h1 | h1 | h1 | h1 <;>
        (simp only [evalOp, h1, hf] at h; split at h <;> cases h; exact True.intro)
  simp only [evalOpArms, List.mem_cons, List.mem_nil_iff, or_false] at harm
  rcases harm with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · -- InitMem
    simp only [evalOp, h1] at h
    cases h; exact hfr.mem0
  · -- Arg
    simp only [evalOp, h1] at h
    split at h
    · exact DAE.argVal_avoids hU hfr h
    · cases h
  · -- ArgIntReg
    simp only [evalOp, h1] at h
    split at h
    · exact DAE.argVal_avoids hU hfr h
    · cases h
  · exact excl _ h1 (by decide)
  · -- PanicBounds
    rw [DAE.evalOp_panicBounds h1] at h
    exact absurd h panicBounds_not_ok
  · exact calls (.inl h1)
  · exact calls (.inr (.inl h1))
  · exact calls (.inr (.inr (.inl h1)))
  · exact calls (.inr (.inr (.inr (.inl h1))))
  · exact calls (.inr (.inr (.inr (.inr (.inl h1)))))
  · exact calls (.inr (.inr (.inr (.inr (.inr h1)))))
  · -- GetClosurePtr
    simp only [evalOp, h1, hfr.closure] at h
    cases h; trivial
  · rw [DAE.evalOp_memRoot (by simp [h1])] at h
    exact DAE.write_avoids (.inl h1) hargs h
  · exact excl _ h1 (by decide)
  · rw [DAE.evalOp_memRoot (by simp [h1])] at h
    exact DAE.write_avoids (.inr (.inr h1)) hargs h
  · exact excl _ h1 (by decide)
  · rw [DAE.evalOp_memRoot (by simp [h1])] at h
    exact DAE.write_avoids (.inr (.inl h1)) hargs h
  · exact excl _ h1 (by decide)
  · -- VarDef
    rw [DAE.evalOp_memRoot (by simp [h1])] at h
    obtain ⟨M, n, rfl, -, rfl, -⟩ := DSE.varDef_shape h1 h
    exact DAE.memAvoids_poison (hargs _ List.mem_cons_self) _
  · rw [DAE.evalOp_memRoot (by simp [h1])] at h
    obtain ⟨L, M, rfl, rfl, -⟩ := DAE.varLive_spec (.inl h1) h
    exact hargs _ (by simp)
  · rw [DAE.evalOp_memRoot (by simp [h1])] at h
    obtain ⟨L, M, rfl, rfl, -⟩ := DAE.varLive_spec (.inr h1) h
    exact hargs _ (by simp)
  · exact excl _ h1 (by decide)
  · -- NilCheck
    rw [DAE.evalOp_memRoot (by simp [h1])] at h
    obtain ⟨M, rfl, -⟩ := DAE.nilCheck_ok h1 h
    exact hargs _ List.mem_cons_self
  · exact frameOps (.inl h1)
  · exact frameOps (.inr (.inl h1))
  · exact frameOps (.inr (.inr (.inl h1)))
  · exact frameOps (.inr (.inr (.inr (.inl h1))))
  · exact frameOps (.inr (.inr (.inr (.inr h1))))

end GoFV.Proof.TabsMod
