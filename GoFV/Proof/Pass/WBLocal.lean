import GoFV.Proof.Pass.WBMem
import GoFV.Opt.WriteBarrierCheck
import GoFV.Proof.Pass.WBEval
import GoFV.Proof.Speculate
import GoFV.Proof.Enter
import GoFV.Proof.Eval
import GoFV.Proof.Pass.DAEOps
import GoFV.Proof.Pass.DAERoot
import GoFV.Proof.Pass.DAESrc
import GoFV.Proof.AtomSimOK
import GoFV.SSA.Sem.Runtime

/-!
# writebarrier: one value of a chain (issue #36)

The simulation of a source block `b` by its chain (`WBCheck.chainRuns?`) evaluates every value
of a block of the chain against a reference frame `Gr` of the source (its frame after the block,
or before the node it panics at). `QR c rs Gr x y`: what the register of `x` holds, by `x`'s role
(`WBCheck.Ctx.roleOf`): a held value its source register; the flag address and `Const32 [0]`
their values; the flag `Load`/`Neq32` an integer/boolean once the run's memory is a memory; the
memory `Phi`, the re-emitted stores the source's memories with possibly a buffer (`W`); the
buffer block's memories the run's memory with a buffer (`Buf`); the nil-check copies the source
nil check's register.

The local steps (`local_*`): a value of each role, evaluated in a frame whose argument registers
satisfy `QR`, gives a value satisfying `QR` (`LocalQ`).
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

/-- `Gr` holds memory `M` at `a`. -/
def MemAt (Gr : Frame) (a : ID) (M : Mem) : Prop := Gr.regs[a]? = some (some (.mem M))

/-- The source memory before run `j`. -/
def RunMem (Gr : Frame) (rs : List Run) (j : Nat) (M : Mem) : Prop :=
  ∃ r, rs[j]? = some r ∧ MemAt Gr r.sp.mem M

/-- The flag's address. -/
def flagPtr : Ptr := ⟨flagBlk, 0⟩

/-- A memory of the buffer block after a helper call: `M` with a buffer, or `M` itself. -/
def BufW (M : Mem) (m : Mem) : Prop := (∃ n, Buf M n m) ∨ m = M

/-- What the register of a value of the chain holds, by its role (see the module doc). -/
def QR (c : WBCheck.Ctx) (rs : List Run) (Gr : Frame) (x : ID) (y : Val) : Prop :=
  match c.roleOf rs x with
  | .held => Gr.regs[x]? = some (some y)
  | .wbaddr => y = .ptr flagPtr
  | .const0 => y = .int .w32 0
  | .lazy | .invalid | .tload _ => True
  | .load j => ∀ M, RunMem Gr rs j M → ∃ v, y = .int .w32 v
  | .flag j => ∀ M, RunMem Gr rs j M → ∃ bb, y = .bool bb
  | .phi j => ∃ M m, RunMem Gr rs j M ∧ y = .mem m ∧ W M m
  | .ncEnd j => ∃ r n, rs[j]? = some r ∧ r.nc = some n ∧ Gr.regs[n]? = some (some y)
  | .ncThen j => ∃ r n, rs[j]? = some r ∧ r.nc = some n ∧ Gr.regs[n]? = some (some y)
  | .tgt j k => ∃ r s M m, rs[j]? = some r ∧ r.src[k]? = some s ∧ MemAt Gr s M ∧ y = .mem m ∧
      W M m
  | .wb j => ∃ r M m, rs[j]? = some r ∧ MemAt Gr r.sp.mem M ∧
      y = .tuple [.ptr ⟨.wbuf, 0⟩, .mem m] ∧ Buf M (c.wbSize x) m
  | .sel0 _ => y = .ptr ⟨.wbuf, 0⟩
  | .sel1 j => ∃ r M m, rs[j]? = some r ∧ MemAt Gr r.sp.mem M ∧ y = .mem m ∧
      Buf M (c.memSize rs x) m
  | .bstore j => ∃ r M m, rs[j]? = some r ∧ MemAt Gr r.sp.mem M ∧ y = .mem m ∧
      Buf M (c.memSize rs x) m
  | .off j => ∃ r i, rs[j]? = some r ∧ i < c.offSize x ∧
      y = .ptr ⟨.wbuf, BitVec.ofNat 64 (8 * i)⟩
  | .taddr _ => ∃ s, y = .ptr ⟨.global s, 0⟩
  | .call j => ∃ r M m, rs[j]? = some r ∧ MemAt Gr r.sp.mem M ∧ y = .tuple [.mem m, .agg []] ∧
      BufW M m
  | .seln j => ∃ r M m, rs[j]? = some r ∧ MemAt Gr r.sp.mem M ∧ y = .mem m ∧ BufW M m
  | .none => False

/-- The write-barrier helpers are the runtime's (`Runtime.wbHelper`), and a call of either clobbers
none of its caller's outgoing-arguments area (`Env.noSpill`). The `noSpill` half is a **trusted
assumption** about the runtime binary (docs/plans/semantics.md §9.6, evidence on #36): in the
pinned go1.27.3 linux/arm64 runtime, `runtime.wbZero`/`runtime.wbMove` store only the link
register and frame pointer inside their own frame, never at or above their entry `SP`, and the
runtime is always compiled with optimizations (`cmd/compile/internal/base/flag.go:366-369`), so
they never use the spill slots of their register arguments in the caller's frame. -/
def WbHelpers (env : Env) : Prop :=
  env.extern "runtime.wbZero" = some Runtime.wbHelper ∧
    env.extern "runtime.wbMove" = some Runtime.wbHelper ∧
    env.noSpill "runtime.wbZero" = true ∧ env.noSpill "runtime.wbMove" = true

/-! ## Evaluating with known argument registers -/

/-- The registers of the IDs `l` hold the values `L`. -/
def RegsAre (g : Frame) : List ID → List Val → Prop
  | [], [] => True
  | a :: l, z :: L => g.regs[a]? = some (some z) ∧ RegsAre g l L
  | _, _ => False

theorem mapM_regs {m : ID → String} {g : Frame} :
    ∀ {l : List ID} {L : List Val}, RegsAre g l L →
      l.mapM (fun a => Res.ofOption (m a) ((g.regs[a]?).join)) = .ok L
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | a :: l, z :: L, ⟨h, hs⟩ => by
    have hz : (g.regs[a]?).join = some z := by rw [h]; rfl
    rw [List.mapM_cons, hz]
    change Res.bind (List.mapM _ l) _ = _
    rw [mapM_regs hs]; rfl

/-- `evalValue` once the argument registers are known. -/
theorem evalValue_of {env : Env} {ctx : Sem.Ctx} {g : Frame} {v : Value} {L : List Val}
    (h : RegsAre g v.args.toList L) :
    evalValue env ctx g v = Res.bind (evalOp env ctx g v L (ctx.tys[v.id]?.getD .other))
      (fun r => .ok (r.retype (ctx.tys[v.id]?.getD .other))) := by
  unfold evalValue
  rw [mapM_regs h]; rfl

theorem tys_get {tabs : Tables} {h : Func} {x : ID} {w : Value} (hw : h.value? x = some w)
    (hid : w.id = x) : (Ctx.make tabs h).tys[w.id]?.getD .other = tabs.ty w.type := by
  rw [hid, tys_of_value hw]; rfl

/-- An argument's register, from `LocalQ`'s hypothesis. -/
theorem argQ {gf : Func} {g' : Frame} {Q : ID → Val → Prop} {x : ID} {w : Value}
    (hw : gf.value? x = some w)
    (hA : ∀ a ∈ argsF gf x, ∃ z, g'.regs[a]? = some (some z) ∧ Q a z) {a : ID} (ha : a ∈ w.args) :
    ∃ z, g'.regs[a]? = some (some z) ∧ Q a z :=
  hA a (by rw [argsF_of hw]; exact Array.mem_toList_iff.2 ha)


/-! ## Facts about values -/

theorem specSafe_ok {env : Env} {ctx : Sem.Ctx} {g : Frame} {x : ID} {v : Value}
    (hv : ctx.f.value? x = some v) (hs : specSafeOp v.op = true)
    (hargs : ∀ a ∈ v.args, ∃ z, g.regs[a]? = some (some z)) : ∃ y, stepV env ctx g x = .ok y := by
  rw [stepV_eq hv]; exact evalValue_specSafe hs hargs

/-- A value whose role's `QR` is `True` evaluates wherever its arguments have values. -/
theorem local_true {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} (hw : g.value? x = some w)
    (hs : specSafeOp w.op = true) (hq : ∀ y, QR c rs Gr x y) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨y, hy⟩ := specSafe_ok (env := env) (ctx := Ctx.make tabs g) (g := g') hw hs
    fun a ha => (argQ hw hA ha).imp fun _ h => h.1
  exact ⟨y, hy, hq y⟩

/-- **The flag address.** -/
theorem local_wbaddr {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} (hw : g.value? x = some w) (hid : w.id = x)
    (hrole : c.roleOf rs x = .wbaddr) (hop : w.op = .Addr)
    (hsym : symName? tabs w.aux = some "runtime.writeBarrier") (hty : isPtrTy (tabs.ty w.type) = true) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  have hargs : ∀ a ∈ w.args, ∃ z, g'.regs[a]? = some (some z) :=
    fun a ha => (argQ hw hA ha).imp fun _ h => h.1
  obtain ⟨L, hL⟩ := mapM_ofOption_ok (l := w.args.toList)
    (m := fun a => s!"v{w.id}: argument v{a} has no value") (r := fun a => (g'.regs[a]?).join)
    fun a ha => by
      obtain ⟨z, hz⟩ := hargs a (Array.mem_toList_iff.1 ha)
      exact ⟨z, by rw [hz]; rfl⟩
  refine ⟨.ptr flagPtr, ?_, by simp only [QR, hrole]⟩
  rw [stepV_eq hw]
  unfold evalValue
  rw [hL]
  change Res.bind (evalOp env (Ctx.make tabs g) g' w L _) _ = _
  rw [tys_get hw hid]
  unfold symName? at hsym
  have hfv : frameVal (Ctx.make tabs g) w = some (.ptr flagPtr) := by
    unfold frameVal
    rw [hop]
    dsimp only
    split at hsym
    · rename_i name _ _ _ he
      simp only [Ctx.make]
      rw [he]
      simp only [Option.some.injEq] at hsym
      simp [flagPtr, flagBlk, hsym]
    · cases hsym
  have hev : evalOp env (Ctx.make tabs g) g' w L (tabs.ty w.type) = .ok (.ptr flagPtr) := by
    unfold evalOp
    rw [hop]
    dsimp only
    rw [hfv]
    rfl
  rw [hev]
  obtain ⟨e, he⟩ : ∃ e, tabs.ty w.type = .ptr e := by
    unfold isPtrTy at hty; split at hty
    · exact ⟨_, ‹_›⟩
    · cases hty
  rw [he]
  rfl

/-- **`Const32 [0]`.** -/
theorem local_const0 {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} (hw : g.value? x = some w) (hid : w.id = x)
    (hrole : c.roleOf rs x = .const0) (hop : w.op = .Const32) (hai : w.auxInt = (0 : Int64))
    (hargs : w.args = #[]) (hty : tabs.ty w.type = .int .w32) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ _
  refine ⟨.int .w32 0, ?_, by simp only [QR, hrole]⟩
  rw [stepV_eq hw, evalValue_of (L := []) (by rw [hargs]; trivial), tys_get hw hid, hty]
  have : evalOp env (Ctx.make tabs g) g' w [] (.int .w32) =
      .ok (evalPure .Const32 (.int .w32) w.auxInt w.aux []) := by
    simp only [evalOp, frameVal, hop]; rfl
  rw [this, hai]
  rfl

/-- `Gr` agrees with an argument's `QR` value for held arguments, given the values of the flag
address and the constant in `Gr`. -/
abbrev HeldGr (c : WBCheck.Ctx) (rs : List Run) (Gr : Frame) : Prop :=
  ∀ a z y, c.held a = true → QR c rs Gr a z → Gr.regs[a]? = some (some y) → z = y


/-! ## Memory roots -/

theorem bind_ok_iff {x : Res Val} {k : Val → Res Val} {y : Val} :
    Res.bind x k = .ok y ↔ ∃ a, x = .ok a ∧ k a = .ok y := by
  cases x with
  | ok a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h1, h2⟩ => by cases h1; exact h2⟩
  | panic e m => exact ⟨(fun h => nomatch h), (fun ⟨_, h1, _⟩ => nomatch h1)⟩
  | stuck msg => exact ⟨(fun h => nomatch h), (fun ⟨_, h1, _⟩ => nomatch h1)⟩

theorem bind_panic_iff {x : Res Val} {k : Val → Res Val} {e : Panic} {m : Mem}
    (hk : ∀ a, ∃ y, k a = .ok y) : Res.bind x k = .panic e m ↔ x = .panic e m := by
  cases x with
  | ok a =>
    obtain ⟨y, hy⟩ := hk a
    refine ⟨fun h => ?_, (fun h => nomatch h)⟩
    change k a = _ at h; rw [hy] at h; exact nomatch h
  | panic e' m' => exact ⟨fun h => h, fun h => h⟩
  | stuck msg => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- A nil check's result does not depend on its memory (its panic carries it). -/
theorem nilCheck_ok {ctx ctx' : Sem.Ctx} {v v' : Value} (hv : v.op = .NilCheck)
    (hv' : v'.op = .NilCheck) {p : Val} {m m' : Mem} {y : Val}
    (h : memRoot ctx v [p, .mem m] = .ok y) : memRoot ctx' v' [p, .mem m'] = .ok y := by
  obtain ⟨a, m1, q, he, hq, hr⟩ := memRoot_nilCheck_res hv h (fun _ h => nomatch h)
  simp only [List.cons.injEq, Val.mem.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [memRoot_nilCheck hv' _ _ hq]
  split at hr
  · cases hr
  · rw [if_neg ‹_›]; exact hr.symm

theorem nilCheck_panic {ctx ctx' : Sem.Ctx} {v v' : Value} (hv : v.op = .NilCheck)
    (hv' : v'.op = .NilCheck) {p : Val} {m : Mem} {e : Panic} {m0 : Mem}
    (h : memRoot ctx v [p, .mem m] = .panic e m0) : m0 = m ∧ memRoot ctx' v' [p, .mem m] = .panic e m := by
  obtain ⟨a, m1, q, he, hq, hr⟩ := memRoot_nilCheck_res hv h (fun _ h => nomatch h)
  simp only [List.cons.injEq, Val.mem.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [memRoot_nilCheck hv' _ _ hq]
  split at hr
  · cases hr; rw [if_pos ‹_›]; exact ⟨rfl, rfl⟩
  · cases hr

theorem frameBlk_ne_wbuf (tabs : Tables) (act : Nat) (n : AuxRef) : frameBlk tabs act n ≠ .wbuf := by
  unfold frameBlk; split <;> simp

theorem store_inv {ctx : Sem.Ctx} {u : Value} {argv : List Val} {y : Val} (hu : u.op = .Store)
    (h : memRoot ctx u argv = .ok y) : ∃ a q x M M', argv = [a, x, .mem M] ∧
      a.asPtrWord = some q ∧ M.write q (encode (auxTy ctx.tabs u.aux) x) = some M' ∧
      y = .mem M' := by
  unfold memRoot at h
  rw [hu] at h
  split at h
  all_goals first
    | contradiction
    | (split at h
       · simp only [writeRes] at h; split at h
         · cases h; exact ⟨_, _, _, _, _, rfl, ‹_›, ‹_›, rfl⟩
         · cases h
       · cases h)
    | (simp only at h; split at h <;> cases h)

theorem varDef_inv {ctx : Sem.Ctx} {u : Value} {argv : List Val} {y : Val} (hu : u.op = .VarDef)
    (h : memRoot ctx u argv = .ok y) : ∃ M n, argv = [.mem M] ∧ u.aux = some n ∧
      y = .mem (M.poisonBlock (frameBlk ctx.tabs ctx.act n)) := by
  unfold memRoot at h
  rw [hu] at h
  split at h
  all_goals first
    | contradiction
    | (simp only at h; split at h
       · cases h; exact ⟨_, _, rfl, ‹_›, rfl⟩
       · cases h)
    | (simp only at h; split at h <;> cases h)

theorem varLive_inv {ctx : Sem.Ctx} {u : Value} {argv : List Val} {y : Val} (hu : u.op = .VarLive)
    (h : memRoot ctx u argv = .ok y) : ∃ M, argv = [.mem M] ∧ y = .mem M := by
  unfold memRoot at h
  rw [hu] at h
  split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨_, rfl, rfl⟩)
    | (simp only at h; split at h <;> cases h)

theorem move_inv {ctx : Sem.Ctx} {u : Value} {argv : List Val} {y : Val} (hu : u.op = .Move)
    (h : memRoot ctx u argv = .ok y) : ∃ a b d s bs M M', argv = [a, b, .mem M] ∧
      a.asPtrWord = some d ∧ b.asPtrWord = some s ∧ M.read s u.auxInt.toInt.toNat = some bs ∧
      M.write d bs = some M' ∧ y = .mem M' := by
  unfold memRoot at h
  rw [hu] at h
  split at h
  all_goals first
    | contradiction
    | (split at h
       · split at h
         · simp only [writeRes] at h; split at h
           · cases h; exact ⟨_, _, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩
           · cases h
         · cases h
       · cases h)
    | (simp only at h; split at h <;> cases h)

theorem zero_inv {ctx : Sem.Ctx} {u : Value} {argv : List Val} {y : Val} (hu : u.op = .Zero)
    (h : memRoot ctx u argv = .ok y) : ∃ a p M M', argv = [a, .mem M] ∧
      a.asPtrWord = some p ∧ M.write p (Array.replicate u.auxInt.toInt.toNat (.b 0)) = some M' ∧
      y = .mem M' := by
  unfold memRoot at h
  rw [hu] at h
  split at h
  all_goals first
    | contradiction
    | (split at h
       · simp only [writeRes] at h; split at h
         · cases h; exact ⟨_, _, _, _, rfl, ‹_›, ‹_›, rfl⟩
         · cases h
       · cases h)
    | (simp only at h; split at h <;> cases h)

theorem nilCheck_inv {ctx : Sem.Ctx} {u : Value} {argv : List Val} {y : Val} (hu : u.op = .NilCheck)
    (h : memRoot ctx u argv = .ok y) : ∃ p M, argv = [p, .mem M] := by
  obtain ⟨_, _, _, he, -, -⟩ := memRoot_nilCheck_res hu h (fun _ h => nomatch h)
  exact ⟨_, _, he⟩

theorem nilCheck_inv_panic {ctx : Sem.Ctx} {u : Value} {argv : List Val} {e : Panic} {m : Mem}
    (hu : u.op = .NilCheck) (h : memRoot ctx u argv = .panic e m) : ∃ p, argv = [p, .mem m] := by
  obtain ⟨_, _, _, rfl, -, hr⟩ := memRoot_nilCheck_res hu h (fun _ h => nomatch h)
  split at hr
  · cases hr; exact ⟨_, rfl⟩
  · cases hr

theorem append_single_inj {L L' : List Val} {a b : Val} (h : L ++ [a] = L' ++ [b]) : L = L' ∧ a = b := by
  have := List.append_inj' h rfl
  exact ⟨this.1, by simpa using this.2⟩

/-- **A re-emitted store** (`Store`, `VarDef`, `VarLive`, `Move`, `Zero`) on a memory
`W`-related to the source's does what the source's did, `W`-related. -/
theorem memRoot_copy {ctxS ctxT : Sem.Ctx} (htabs : ctxT.tabs = ctxS.tabs) (hact : ctxT.act = ctxS.act)
    {u w : Value} (hop : w.op = u.op)
    (hu : u.op = .Store ∨ u.op = .VarDef ∨ u.op = .VarLive ∨ u.op = .Move ∨ u.op = .Zero)
    (haux : w.aux = u.aux) (hai : w.auxInt = u.auxInt) {L : List Val} {M m : Mem} {y : Val}
    (hW : W M m) (h : memRoot ctxS u (L ++ [.mem M]) = .ok y) :
    ∃ M' m', y = .mem M' ∧ memRoot ctxT w (L ++ [.mem m]) = .ok (.mem m') ∧ W M' m' := by
  rcases hu with hu | hu | hu | hu | hu
  · obtain ⟨a, q, x, M0, M', he, hq, hwr, rfl⟩ := store_inv hu h
    obtain ⟨hL, hM⟩ := append_single_inj (L' := [a, x]) (b := .mem M0) he
    cases hM; subst hL
    obtain ⟨m', hm', hW'⟩ := hW.write hwr
    refine ⟨M', m', rfl, ?_, hW'⟩
    simp only [memRoot, hop, hu, List.cons_append, List.nil_append, hq, writeRes, haux, htabs, hm']
  · obtain ⟨M0, n, he, hn, rfl⟩ := varDef_inv hu h
    obtain ⟨hL, hM⟩ := append_single_inj (L' := []) (b := .mem M0) he
    cases hM; subst hL
    refine ⟨_, _, rfl, ?_, hW.poison (frameBlk_ne_wbuf _ _ _)⟩
    simp only [memRoot, hop, hu, List.nil_append, haux, hn, htabs, hact]
  · obtain ⟨M0, he, rfl⟩ := varLive_inv hu h
    obtain ⟨hL, hM⟩ := append_single_inj (L' := []) (b := .mem M0) he
    cases hM; subst hL
    refine ⟨_, _, rfl, ?_, hW⟩
    simp only [memRoot, hop, hu, List.nil_append]
  · obtain ⟨a, b, d, s, bs, M0, M', he, hd, hs, hrd, hwr, rfl⟩ := move_inv hu h
    obtain ⟨hL, hM⟩ := append_single_inj (L' := [a, b]) (b := .mem M0) he
    cases hM; subst hL
    obtain ⟨m', hm', hW'⟩ := hW.write hwr
    refine ⟨M', m', rfl, ?_, hW'⟩
    simp only [memRoot, hop, hu, List.cons_append, List.nil_append, hd, hs, hai, hW.read hrd,
      writeRes, hm']
  · obtain ⟨a, p, M0, M', he, hp, hwr, rfl⟩ := zero_inv hu h
    obtain ⟨hL, hM⟩ := append_single_inj (L' := [a]) (b := .mem M0) he
    cases hM; subst hL
    obtain ⟨m', hm', hW'⟩ := hW.write hwr
    refine ⟨M', m', rfl, ?_, hW'⟩
    simp only [memRoot, hop, hu, List.cons_append, List.nil_append, hp, hai, writeRes, hm']

/-! ## Argument lists -/

theorem regsAre_length {g : Frame} : ∀ {l : List ID} {L : List Val}, RegsAre g l L → L.length = l.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [regsAre_length h]

theorem regsAre_get {g : Frame} : ∀ {l : List ID} {L : List Val}, RegsAre g l L →
    ∀ {k : Nat} {a : ID}, l[k]? = some a → ∃ z, L[k]? = some z ∧ g.regs[a]? = some (some z)
  | [], [], _, _, _, h => by simp at h
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim
  | a :: l, z :: L, ⟨h1, h2⟩, k, b, hk => by
    cases k with
    | zero => simp at hk; subst hk; exact ⟨z, rfl, h1⟩
    | succ k => simpa using regsAre_get h2 (by simpa using hk)

theorem regsAre_of {g : Frame} : ∀ {l : List ID}, (∀ a ∈ l, ∃ z, g.regs[a]? = some (some z)) →
    ∃ L, RegsAre g l L
  | [], _ => ⟨[], trivial⟩
  | a :: l, h => by
    obtain ⟨z, hz⟩ := h a List.mem_cons_self
    obtain ⟨L, hL⟩ := regsAre_of (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    exact ⟨z :: L, hz, hL⟩

theorem mapM_regs_inv {m : ID → String} {g : Frame} :
    ∀ {l : List ID} {L : List Val},
      l.mapM (fun a => Res.ofOption (m a) ((g.regs[a]?).join)) = .ok L → RegsAre g l L
  | [], L, h => by cases h; trivial
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : (g.regs[a]?).join with
    | none => rw [ha] at h; cases h
    | some z =>
      rw [ha] at h
      change Res.bind (List.mapM _ l) _ = _ at h
      cases hl : List.mapM (fun a => Res.ofOption (m a) ((g.regs[a]?).join)) l with
      | ok L' =>
        rw [hl] at h; cases h
        refine ⟨?_, mapM_regs_inv hl⟩
        cases hg : g.regs[a]? with
        | none => rw [hg] at ha; cases ha
        | some o => rw [hg] at ha; cases o <;> simp_all
      | panic e mm => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h

theorem mapM_regs_ne_panic {m : ID → String} {g : Frame} {e : Panic} {mm : Mem} :
    ∀ {l : List ID}, l.mapM (fun a => Res.ofOption (m a) ((g.regs[a]?).join)) ≠ .panic e mm
  | [] => nofun
  | a :: l => by
    rw [List.mapM_cons]
    cases ha : (g.regs[a]?).join with
    | none => nofun
    | some z =>
      change Res.bind (List.mapM _ l) _ ≠ _
      cases hl : List.mapM (fun a => Res.ofOption (m a) ((g.regs[a]?).join)) l with
      | ok L' => nofun
      | panic e' mm' => exact absurd hl mapM_regs_ne_panic
      | stuck msg => nofun

/-- What a successful `evalValue` computed. -/
theorem evalValue_inv {env : Env} {ctx : Sem.Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValue env ctx fr v = .ok y) :
    ∃ L r, RegsAre fr v.args.toList L ∧ evalOp env ctx fr v L (ctx.tys[v.id]?.getD .other) = .ok r ∧
      y = r.retype (ctx.tys[v.id]?.getD .other) := by
  unfold evalValue at h
  cases hm : v.args.toList.mapM (fun a => Res.ofOption s!"v{v.id}: argument v{a} has no value"
      ((fr.regs[a]?).join)) with
  | ok L =>
    rw [hm] at h
    change Res.bind (evalOp env ctx fr v L _) _ = _ at h
    obtain ⟨r, hr, he⟩ := bind_ok_iff.1 h
    cases he
    exact ⟨L, r, mapM_regs_inv hm, hr, rfl⟩
  | panic e mm => rw [hm] at h; cases h
  | stuck msg => rw [hm] at h; cases h

theorem evalValue_inv_panic {env : Env} {ctx : Sem.Ctx} {fr : Frame} {v : Value} {e : Panic} {mm : Mem}
    (h : evalValue env ctx fr v = .panic e mm) :
    ∃ L, RegsAre fr v.args.toList L ∧ evalOp env ctx fr v L (ctx.tys[v.id]?.getD .other) = .panic e mm := by
  unfold evalValue at h
  cases hm : v.args.toList.mapM (fun a => Res.ofOption s!"v{v.id}: argument v{a} has no value"
      ((fr.regs[a]?).join)) with
  | ok L =>
    rw [hm] at h
    change Res.bind (evalOp env ctx fr v L _) _ = _ at h
    refine ⟨L, mapM_regs_inv hm, ?_⟩
    exact (bind_panic_iff fun a => ⟨_, rfl⟩).1 h
  | panic e mm => exact absurd hm mapM_regs_ne_panic
  | stuck msg => rw [hm] at h; cases h

/-- The memories `Gr` holds are `MemOK` (from the source invariant `MemInv.SInv`). -/
abbrev MemsGr (Gr : Frame) : Prop := ∀ (a : ID) (M : Mem), Gr.regs[a]? = some (some (Val.mem M)) → MemOK M

/-- **The flag load.** -/
theorem local_load {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} (hH : HeldGr c rs Gr) (hS : MemsGr Gr) {x : ID} {w : Value} {j : Nat}
    {r : Run} (hw : g.value? x = some w) (hid : w.id = x) (hrole : c.roleOf rs x = .load j)
    (hr : rs[j]? = some r) (hop : w.op = .Load) (hargs : w.args = #[r.sp.wbaddr, r.sp.mem])
    (hty : tabs.ty w.type = .int .w32) (hwa : c.roleOf rs r.sp.wbaddr = .wbaddr)
    (hmh : c.held r.sp.mem = true) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨za, hza, hqa⟩ := argQ hw hA (a := r.sp.wbaddr) (by rw [hargs]; simp)
  obtain ⟨zm, hzm, hqm⟩ := argQ hw hA (a := r.sp.mem) (by rw [hargs]; simp)
  simp only [QR, hwa] at hqa
  subst hqa
  refine ⟨(evalPure .Load (.int .w32) w.auxInt w.aux [.ptr flagPtr, zm]).retype (.int .w32),
    ?_, ?_⟩
  · rw [stepV_eq hw, evalValue_of (L := [.ptr flagPtr, zm])
      (by rw [hargs]; exact ⟨hza, hzm, trivial⟩), tys_get hw hid, hty]
    rw [DAE.evalOp_pureOp (.inr (.inr (.inr (.inr (.inr (.inr (.inl hop)))))))]
    rw [hop]
    rfl
  · simp only [QR, hrole]
    intro M ⟨r', hr', hM⟩
    rw [hr] at hr'; cases hr'
    have := hH _ _ _ hmh hqm hM
    subst this
    obtain ⟨v, hv⟩ := load_flag (hS _ _ hM)
    refine ⟨v.setWidth 32, ?_⟩
    show (loadOp (.int .w32) [.ptr flagPtr, .mem M]).retype (.int .w32) = _
    simp only [loadOp, flagPtr, Val.asPtrWord]
    rw [hv]
    simp [Val.retype]

/-- **The flag** `Neq32 (Load …) const0`. -/
theorem local_flag {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} {j : Nat} {r : Run}
    (hw : g.value? x = some w) (hid : w.id = x) (hrole : c.roleOf rs x = .flag j)
    (hop : w.op = .Neq32) (hargs : w.args = #[r.sp.load, r.sp.const0])
    (hty : tabs.ty w.type = .bool) (hl : c.roleOf rs r.sp.load = .load j)
    (hc : c.roleOf rs r.sp.const0 = .const0) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨zl, hzl, hql⟩ := argQ hw hA (a := r.sp.load) (by rw [hargs]; simp)
  obtain ⟨zc, hzc, hqc⟩ := argQ hw hA (a := r.sp.const0) (by rw [hargs]; simp)
  simp only [QR, hl] at hql
  simp only [QR, hc] at hqc
  subst hqc
  refine ⟨(evalPure .Neq32 .bool w.auxInt w.aux [zl, .int .w32 0]).retype .bool, ?_, ?_⟩
  · rw [stepV_eq hw, evalValue_of (L := [zl, .int .w32 0])
      (by rw [hargs]; exact ⟨hzl, hzc, trivial⟩), tys_get hw hid, hty]
    have : evalOp env (Ctx.make tabs g) g' w [zl, .int .w32 0] .bool =
        .ok (evalPure .Neq32 .bool w.auxInt w.aux [zl, .int .w32 0]) := by
      simp only [evalOp, frameVal, hop]; rfl
    rw [this]; rfl
  · simp only [QR, hrole]
    intro M hM
    obtain ⟨v, rfl⟩ := hql M hM
    exact ⟨_, rfl⟩

/-- **A nil-check copy** (`ncEnd`, `ncThen`) that the source's nil check passed. -/
theorem local_nc {env : Env} {tabs : Tables} {f g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} (hH : HeldGr c rs Gr) {x : ID} {w : Value} {n : ID} {u : Value}
    (hw : g.value? x = some w) (hid : w.id = x) (hu : f.value? n = some u) (huid : u.id = n)
    (hq : ∀ y, Gr.regs[n]? = some (some y) → QR c rs Gr x y)
    (hsrc : ∃ y, Gr.regs[n]? = some (some y) ∧ evalValue env (Ctx.make tabs f) Gr u = .ok y)
    (hopu : u.op = .NilCheck) (hopw : w.op = .NilCheck) (hty : w.type = u.type)
    {p mS mT : ID} (hu2 : u.args = #[p, mS]) (hw2 : w.args = #[p, mT]) (hp : c.held p = true)
    (hmem : ∀ z, QR c rs Gr mT z → ∀ M, MemAt Gr mS M → ∃ m, z = .mem m) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨y, hy, hev⟩ := hsrc
  obtain ⟨L, r0, hL, hop0, rfl⟩ := evalValue_inv hev
  rw [hu2] at hL
  have hl2 := regsAre_length hL
  obtain ⟨zp, zm, rfl⟩ : ∃ zp zm, L = [zp, zm] := by
    rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp at hl2
    exact ⟨a, b, rfl⟩
  obtain ⟨hzp, hzm, -⟩ := hL
  rw [DAE.evalOp_memRoot (.inr (.inr (.inr (.inr (.inr (.inr hopu))))))] at hop0
  obtain ⟨_, M, hpm⟩ := nilCheck_inv hopu hop0
  simp only [List.cons.injEq] at hpm
  obtain ⟨-, rfl, -⟩ := hpm
  obtain ⟨tp, htp, hqp⟩ := argQ hw hA (a := p) (by rw [hw2]; simp)
  obtain ⟨tm, htm, hqm⟩ := argQ hw hA (a := mT) (by rw [hw2]; simp)
  have := hH _ _ _ hp hqp hzp
  subst this
  obtain ⟨m, rfl⟩ := hmem _ hqm M hzm
  refine ⟨r0.retype (tabs.ty u.type), ?_, hq _ (by rw [hy, tys_get hu huid])⟩
  rw [stepV_eq hw, evalValue_of (L := [tp, .mem m]) (by rw [hw2]; exact ⟨htp, htm, trivial⟩),
    tys_get hw hid, hty,
    DAE.evalOp_memRoot (.inr (.inr (.inr (.inr (.inr (.inr hopw))))))]
  rw [nilCheck_ok hopu hopw hop0]
  rfl

/-- **A re-emitted store** of run `j`: the source's store `s` on `W`-related memories. -/
theorem local_tgt {env : Env} {tabs : Tables} {f g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} {s : ID} {u : Value} {j k : Nat} {r : Run}
    (hw : g.value? x = some w) (hid : w.id = x) (hrole : c.roleOf rs x = .tgt j k)
    (hr : rs[j]? = some r) (hs : r.src[k]? = some s)
    (hu : f.value? s = some u) (huid : u.id = s)
    (hsrc : ∃ y, Gr.regs[s]? = some (some y) ∧ evalValue env (Ctx.make tabs f) Gr u = .ok y)
    (hopu : u.op = .Store ∨ u.op = .VarDef ∨ u.op = .VarLive ∨ u.op = .Move ∨ u.op = .Zero)
    (hop : w.op = u.op) (haux : w.aux = u.aux) (hai : w.auxInt = u.auxInt) (hty : w.type = u.type)
    (hmemty : tabs.ty w.type = .mem)
    (hsz : w.args.size = u.args.size) {memS memT : ID}
    (hlastu : u.args.toList.getLast? = some memS) (hlastw : w.args.toList.getLast? = some memT)
    (hmem : ∀ z, QR c rs Gr memT z → ∃ M m, MemAt Gr memS M ∧ z = .mem m ∧ W M m)
    (hother : ∀ (i : Nat) (a a' : ID), i + 1 < u.args.size → u.args[i]? = some a →
      w.args[i]? = some a' → ∀ z y, QR c rs Gr a' z → Gr.regs[a]? = some (some y) → z = y) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨y, hy, hev⟩ := hsrc
  obtain ⟨L, r0, hL, hop0, rfl⟩ := evalValue_inv hev
  obtain ⟨L', hL'⟩ := regsAre_of (g := g') (l := w.args.toList)
    fun a ha => (argQ hw hA (Array.mem_toList_iff.1 ha)).imp fun _ h => h.1
  have hlen := regsAre_length hL
  have hlen' := regsAre_length hL'
  -- the memory arguments
  obtain ⟨us, hus⟩ := List.getLast?_eq_some_iff.1 hlastu
  obtain ⟨ws, hws⟩ := List.getLast?_eq_some_iff.1 hlastw
  have e1 : u.args.size = us.length + 1 := by
    rw [← Array.length_toList, hus]; simp
  have e2 : w.args.size = ws.length + 1 := by
    rw [← Array.length_toList, hws]; simp
  have hn : us.length = ws.length := by omega
  have hLl : L.length = us.length + 1 := by rw [hlen]; simpa using e1
  have hL'l : L'.length = us.length + 1 := by rw [hlen']; simp; omega
  -- last values
  obtain ⟨zS, hzS, hzSr⟩ := regsAre_get hL (k := us.length) (a := memS) (by rw [hus]; simp)
  obtain ⟨zT, hzT, hzTr⟩ := regsAre_get hL' (k := us.length) (a := memT) (by rw [hws, hn]; simp)
  obtain ⟨M, m, hM, rfl, hW⟩ := hmem zT (by
    obtain ⟨z', hz', hq⟩ := argQ hw hA (a := memT) (by
      rw [← Array.mem_toList_iff, hws]; simp)
    rw [hzTr] at hz'; cases hz'; exact hq)
  rw [hM] at hzSr; cases hzSr
  -- the other values agree
  have hpre : ∀ i, i < us.length → L[i]? = L'[i]? := by
    intro i hi
    have hia : u.args.toList[i]? = us[i]? := by rw [hus, List.getElem?_append_left hi]
    have hib : w.args.toList[i]? = ws[i]? := by rw [hws, List.getElem?_append_left (hn ▸ hi)]
    obtain ⟨a, ha⟩ : ∃ a, us[i]? = some a := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨a', ha'⟩ : ∃ a', ws[i]? = some a' := ⟨_, List.getElem?_eq_getElem (hn ▸ hi)⟩
    rw [ha] at hia; rw [ha'] at hib
    obtain ⟨z1, hz1, hr1⟩ := regsAre_get hL hia
    obtain ⟨z2, hz2, hr2⟩ := regsAre_get hL' hib
    obtain ⟨z3, hz3, hq3⟩ := argQ hw hA (a := a') (Array.mem_toList_iff.1 (List.mem_of_getElem? hib))
    rw [hr2] at hz3; cases hz3
    have := hother i a a' (by omega) (by simpa using hia) (by simpa using hib) z2 z1 hq3 hr1
    rw [hz1, hz2, this]
  have hLs : L = L.take us.length ++ [.mem M] := by
    apply List.ext_getElem?; intro i
    rcases Nat.lt_or_ge i us.length with hi | hi
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hi]
    · rcases Nat.lt_or_ge i (us.length + 1) with hi' | hi'
      · obtain rfl : i = us.length := by omega
        rw [hzS, List.getElem?_append_right (by simp; omega), List.length_take,
          Nat.min_eq_left (by omega), Nat.sub_self]; rfl
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  have hLs' : L' = L.take us.length ++ [.mem m] := by
    apply List.ext_getElem?; intro i
    rcases Nat.lt_or_ge i us.length with hi | hi
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hi, hpre i hi]
    · rcases Nat.lt_or_ge i (us.length + 1) with hi' | hi'
      · obtain rfl : i = us.length := by omega
        rw [hzT, List.getElem?_append_right (by simp; omega), List.length_take,
          Nat.min_eq_left (by omega), Nat.sub_self]; rfl
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  have hmr : ∀ op : Op, (op = .Store ∨ op = .VarDef ∨ op = .VarLive ∨ op = .Move ∨ op = .Zero) →
      op = .Store ∨ op = .Zero ∨ op = .Move ∨ op = .VarDef ∨ op = .VarLive ∨ op = .KeepAlive ∨
        op = .NilCheck := by
    rintro op (h | h | h | h | h) <;> simp [h]
  rw [DAE.evalOp_memRoot (hmr _ hopu), hLs] at hop0
  obtain ⟨M', m', rfl, hT, hW'⟩ := memRoot_copy (ctxS := Ctx.make tabs f) (ctxT := Ctx.make tabs g)
    rfl rfl hop hopu haux hai hW hop0
  refine ⟨.mem m', ?_, ?_⟩
  · rw [stepV_eq hw, evalValue_of (L := L') hL', tys_get hw hid, hmemty,
      DAE.evalOp_memRoot (hmr _ (hop ▸ hopu)), hLs', hT]
    rfl
  · simp only [QR, hrole]
    refine ⟨r, s, M', m', hr, hs, ?_, rfl, hW'⟩
    show Gr.regs[s]? = some (some (.mem M'))
    rw [hy, tys_get hu huid, ← hty, hmemty]; rfl

/-- **The run's last store**, `WBend` in `g`: the source's memory after the run. -/
theorem local_last {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} {t : ID} (hw : g.value? x = some w) (hid : w.id = x)
    (hrole : c.roleOf rs x = .held) (hop : w.op = .WBend) (hargs : w.args = #[t])
    (hty : tabs.ty w.type = .mem)
    (ht : ∀ z, QR c rs Gr t z → ∃ M m, MemAt Gr x M ∧ z = .mem m ∧ W M m) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨z, hz, hq⟩ := argQ hw hA (a := t) (by rw [hargs]; simp)
  obtain ⟨M, m, hM, rfl, hW⟩ := ht z hq
  refine ⟨.mem M, ?_, by simp only [QR, hrole]; exact hM⟩
  rw [stepV_eq hw, evalValue_of (L := [.mem m]) (by rw [hargs]; exact ⟨hz, trivial⟩),
    tys_get hw hid, hty]
  have : evalOp env (Ctx.make tabs g) g' w [.mem m] .mem = .ok (.mem (m.free .wbuf)) := by
    simp only [evalOp, hop, memRoot]
  rw [this, hW.free]
  rfl

/-- **A kept value**: it re-evaluates to the source's register. -/
theorem local_kept {env : Env} {tabs : Tables} {f g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w u : Value} (hw : g.value? x = some w) (hu : f.value? x = some u)
    (huid : u.id = x) (hsame : sameV u w = true) (hrole : c.roleOf rs x = .held)
    (hsrc : ∃ y, Gr.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) Gr u = .ok y)
    (hargs : ∀ a ∈ u.args, ∀ z y, QR c rs Gr a z → Gr.regs[a]? = some (some y) → z = y)
    (hGr : Gr = { fr0 with regs := Gr.regs }) (hown : f.ownAux = g.ownAux) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' hg' hA
  obtain ⟨y, hy, hev⟩ := hsrc
  simp only [sameV, Bool.and_eq_true, beq_iff_eq] at hsame
  obtain ⟨⟨⟨⟨⟨hid, hop⟩, htyp⟩, hai⟩, haux⟩, hargsEq⟩ := hsame
  obtain ⟨L, r0, hL, -, -⟩ := evalValue_inv hev
  refine ⟨y, ?_, by simp only [QR, hrole]; exact hy⟩
  rw [stepV_eq hw, ← hev]
  have hc := AtomSim.ctx_eq (tabs := tabs) hown
  refine evalValue_eq_of_args hop.symm haux.symm hai.symm hid.symm (by rw [hargsEq]) ?_ ?_ ?_
    (by rw [hc]) (by rw [hc]) (by rw [hc])
  · intro k a hk
    have hka : u.args.toList[k]? = some a := by simpa using hk
    obtain ⟨z1, -, hr1⟩ := regsAre_get hL hka
    have ha : a ∈ u.args := Array.mem_toList_iff.1 (List.mem_of_getElem? hka)
    obtain ⟨z2, hz2, hq2⟩ := argQ hw hA (a := a) (by rw [← hargsEq]; exact ha)
    exact ⟨a, z1, by rw [← hargsEq]; exact hk, hr1, by rw [hz2, hargs a ha z2 z1 hq2 hr1]⟩
  · rw [hg', hGr]
  · rw [huid, tys_of_value hu, tys_of_value hw, htyp]

/-! ## The buffer block -/

theorem runMem_mem {c : WBCheck.Ctx} {rs : List Run} {Gr : Frame} (hH : HeldGr c rs Gr) {j : Nat}
    {r : Run} {M : Mem} (hr : rs[j]? = some r) (hM : RunMem Gr rs j M)
    (hmh : c.held r.sp.mem = true) {z : Val} (hq : QR c rs Gr r.sp.mem z) : z = .mem M := by
  obtain ⟨r', hr', hM'⟩ := hM
  rw [hr] at hr'; cases hr'
  exact hH _ _ _ hmh hq hM'

/-- **`WB [n] m`**: the memory `m` (the run's memory, or the memory of an earlier buffer of the
run) with a fresh buffer of `n` entries. -/
theorem local_wb {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} (hH : HeldGr c rs Gr) (hS : MemsGr Gr) {x : ID} {w : Value} {j : Nat}
    {r : Run} {a : ID} (hw : g.value? x = some w) (hid : w.id = x) (hrole : c.roleOf rs x = .wb j)
    (hr : rs[j]? = some r) (hM : ∃ M, RunMem Gr rs j M) (hop : w.op = .WB)
    (hargs : w.args = #[a]) (hmh : c.held r.sp.mem = true)
    (ha : a = r.sp.mem ∨ c.roleOf rs a = .sel1 j ∨ c.roleOf rs a = .bstore j)
    (hn : w.auxInt.toInt.toNat = c.wbSize x) (h8 : w.auxInt.toInt.toNat ≤ 8) {e : Option Nat}
    (hty : tabs.ty w.type = .tuple [.ptr e, .mem]) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨z, hz, hq⟩ := argQ hw hA (a := a) (by rw [hargs]; simp)
  obtain ⟨M, m0, hM0, rfl, hB0⟩ : ∃ M m0, MemAt Gr r.sp.mem M ∧ z = .mem m0 ∧
      (m0 = M ∨ ∃ n', Buf M n' m0) := by
    rcases ha with rfl | h | h
    · obtain ⟨M, hM⟩ := hM
      obtain rfl := runMem_mem hH hr hM hmh hq
      obtain ⟨r', hr', hM'⟩ := hM
      rw [hr] at hr'; cases hr'
      exact ⟨M, M, hM', rfl, .inl rfl⟩
    · simp only [QR, h] at hq
      obtain ⟨r', M, m, hr', hM', rfl, hB⟩ := hq
      rw [hr] at hr'; cases hr'
      exact ⟨M, m, hM', rfl, .inr ⟨_, hB⟩⟩
    · simp only [QR, h] at hq
      obtain ⟨r', M, m, hr', hM', rfl, hB⟩ := hq
      rw [hr] at hr'; cases hr'
      exact ⟨M, m, hM', rfl, .inr ⟨_, hB⟩⟩
  have hB : Buf M w.auxInt.toInt.toNat (m0.wbAlloc w.auxInt.toInt.toNat) := by
    rcases hB0 with rfl | ⟨n', hB'⟩
    · exact buf_wbAlloc (W.refl (hS _ _ hM0).nobuf) h8
    · exact buf_wbAlloc' hB' h8
  refine ⟨.tuple [.ptr ⟨.wbuf, 0⟩, .mem (m0.wbAlloc w.auxInt.toInt.toNat)], ?_, ?_⟩
  · rw [stepV_eq hw, evalValue_of (L := [.mem m0]) (by rw [hargs]; exact ⟨hz, trivial⟩),
      tys_get hw hid, hty]
    have : evalOp env (Ctx.make tabs g) g' w [.mem m0] (.tuple [.ptr e, .mem]) =
        .ok (evalPure .WB (.tuple [.ptr e, .mem]) w.auxInt w.aux [.mem m0]) := by
      simp only [evalOp, frameVal, hop]; rfl
    rw [this]
    show Res.ok ((wbOp w.auxInt [.mem m0]).retype (.tuple [.ptr e, .mem])) = _
    simp only [wbOp]
    rfl
  · simp only [QR, hrole]
    exact ⟨r, M, _, hr, hM0, rfl, by rw [← hn]; exact hB⟩

/-- **`Select0`/`Select1` of the `WB`**: the buffer and the memory with the buffer. -/
theorem local_sel {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} {j : Nat} {a : ID}
    (hw : g.value? x = some w) (hid : w.id = x) (hargs : w.args = #[a])
    (ha : c.roleOf rs a = .wb j)
    (hcase : (w.op = .Select0 ∧ c.roleOf rs x = .sel0 j ∧ isPtrTy (tabs.ty w.type) = true) ∨
      (w.op = .Select1 ∧ c.roleOf rs x = .sel1 j ∧ tabs.ty w.type = .mem ∧
        c.memSize rs x = c.wbSize a)) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨z, hz, hq⟩ := argQ hw hA (a := a) (by rw [hargs]; simp)
  simp only [QR, ha] at hq
  obtain ⟨r, M, m, hr, hM, rfl, hB⟩ := hq
  rcases hcase with ⟨hop, hrole, hty⟩ | ⟨hop, hrole, hty, hsz⟩
  · obtain ⟨e, he⟩ : ∃ e, tabs.ty w.type = .ptr e := by
      unfold isPtrTy at hty; split at hty
      · exact ⟨_, ‹_›⟩
      · cases hty
    refine ⟨.ptr ⟨.wbuf, 0⟩, ?_, by simp only [QR, hrole]⟩
    rw [stepV_eq hw, evalValue_of (L := [_]) (by rw [hargs]; exact ⟨hz, trivial⟩),
      tys_get hw hid, he, DAE.evalOp_pureOp (.inr (.inl hop)), hop]
    rfl
  · refine ⟨.mem m, ?_, ?_⟩
    · rw [stepV_eq hw, evalValue_of (L := [_]) (by rw [hargs]; exact ⟨hz, trivial⟩),
        tys_get hw hid, hty, DAE.evalOp_pureOp (.inr (.inr (.inl hop))), hop]
      rfl
    · simp only [QR, hrole]
      exact ⟨r, M, _, hr, hM, rfl, by rw [hsz]; exact hB⟩

/-- **A buffer pointer** `OffPtr [8k] buf`, `k < n`. -/
theorem local_off {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} {j : Nat} {a : ID} {r : Run}
    (hw : g.value? x = some w) (hid : w.id = x) (hrole : c.roleOf rs x = .off j)
    (hr : rs[j]? = some r) (hop : w.op = .OffPtr) (hargs : w.args = #[a])
    (ha : c.roleOf rs a = .sel0 j) (hty : isPtrTy (tabs.ty w.type) = true)
    (h0 : 0 ≤ w.auxInt.toInt) (h8 : w.auxInt.toInt % 8 = 0)
    (hlt : w.auxInt.toInt / 8 < c.offSize x) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨z, hz, hq⟩ := argQ hw hA (a := a) (by rw [hargs]; simp)
  simp only [QR, ha] at hq
  subst hq
  obtain ⟨e, he⟩ : ∃ e, tabs.ty w.type = .ptr e := by
    unfold isPtrTy at hty; split at hty
    · exact ⟨_, ‹_›⟩
    · cases hty
  obtain ⟨k, hk, hkn⟩ : ∃ k : Nat, w.auxInt.toInt = 8 * (k : Int) ∧ k < c.offSize x :=
    ⟨(w.auxInt.toInt / 8).toNat, by omega, by omega⟩
  have hb : BitVec.ofInt 64 w.auxInt.toInt = BitVec.ofNat 64 (8 * k) := by
    rw [hk, show (8 * (k : Int)) = ((8 * k : Nat) : Int) by push_cast; rfl, BitVec.ofInt_natCast]
  refine ⟨.ptr ⟨.wbuf, BitVec.ofNat 64 (8 * k)⟩, ?_, ?_⟩
  · rw [stepV_eq hw, evalValue_of (L := [_]) (by rw [hargs]; exact ⟨hz, trivial⟩),
      tys_get hw hid, he, DAE.evalOp_pure2 (.inr (.inl hop)), hop]
    show Res.ok ((PtrOps.offPtr w.auxInt [.ptr ⟨.wbuf, 0⟩]).retype (.ptr e)) = _
    simp only [PtrOps.offPtr, PtrOps.ptrRes, Ptr.add, Ptr.inWindow, Blk.window?, hb,
      ite_true]
    have h0' : (0 : BitVec 64) + BitVec.ofNat 64 (8 * k) = BitVec.ofNat 64 (8 * k) := by
      simp
    rw [h0']
    rfl
  · simp only [QR, hrole]
    exact ⟨r, k, hr, hkn, rfl⟩

/-- **A buffer store**: 8 bytes into the buffer. -/
theorem local_bstore {env : Env} {tabs : Tables} {g : Func} {c : WBCheck.Ctx} {rs : List Run}
    {Gr fr0 : Frame} {x : ID} {w : Value} {j : Nat} {o v mm : ID}
    (hw : g.value? x = some w) (hid : w.id = x) (hrole : c.roleOf rs x = .bstore j)
    (hop : w.op = .Store) (hargs : w.args = #[o, v, mm])
    (ho : c.roleOf rs o = .off j) (hmm : c.roleOf rs mm = .sel1 j ∨ c.roleOf rs mm = .bstore j)
    (hsame : c.memSize rs mm = c.offSize o) (hsz : c.memSize rs x = c.memSize rs mm)
    (haux : auxTy tabs w.aux = .int .w64) (hty : tabs.ty w.type = .mem) :
    LocalQ env (Ctx.make tabs g) fr0 (QR c rs Gr) x := by
  intro g' _ hA
  obtain ⟨zo, hzo, hqo⟩ := argQ hw hA (a := o) (by rw [hargs]; simp)
  obtain ⟨zv, hzv, -⟩ := argQ hw hA (a := v) (by rw [hargs]; simp)
  obtain ⟨zm, hzm, hqm⟩ := argQ hw hA (a := mm) (by rw [hargs]; simp)
  simp only [QR, ho] at hqo
  obtain ⟨r, i, hr, hi, rfl⟩ := hqo
  obtain ⟨r', M, m, hr', hM, rfl, hB⟩ : ∃ r M m, rs[j]? = some r ∧ MemAt Gr r.sp.mem M ∧
      zm = .mem m ∧ Buf M (c.memSize rs mm) m := by
    rcases hmm with h | h <;> (simp only [QR, h] at hqm; exact hqm)
  rw [hr] at hr'; cases hr'
  obtain ⟨m', hm', hB'⟩ := hB.write (hsame ▸ hi) (bs := encode (.int .w64) zv) (by
    rw [encode_size]; rfl)
  refine ⟨.mem m', ?_, ?_⟩
  · rw [stepV_eq hw, evalValue_of (L := [_, _, _]) (by rw [hargs]; exact ⟨hzo, hzv, hzm, trivial⟩),
      tys_get hw hid, hty, DAE.evalOp_memRoot (.inl hop)]
    simp only [memRoot, hop, writeRes, Val.asPtrWord]
    rw [show (Ctx.make tabs g).tabs = tabs from rfl, haux, hm']
    rfl
  · simp only [QR, hrole]
    exact ⟨r, M, m', hr, hM, rfl, by rw [hsz]; exact hB'⟩

end GoFV.Proof.WB
