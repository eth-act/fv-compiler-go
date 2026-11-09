import GoFV.Proof.TabsAgreeModMem
import GoFV.Proof.Pass.DAEOps
import GoFV.Proof.Pass.DAERoot
import GoFV.Proof.Frame
import GoFV.Proof.Enter
import GoFV.Proof.Eval
import GoFV.Proof.TabsAgreeModSrc
import GoFV.Opt.WriteBarrierCheck

variable [GoFV.SSA.Sem.Addrs]

/-!
# Memory invariants of a source run (issues #36, #151)

A predicate `P` on memories that writes, `set`s of blocks that are neither globals nor the
write-barrier buffer, and freeing the buffer keep (`MemPred`: the write-barrier flag's `WB.MemOK`,
issue #36; the read-only symbols' `RoMem`, issue #151). Along a run of a function `f` that
`WBCheck.memTyOK` accepts, every memory a register holds is `P` (`SInv P`), when the initial memory
is `P` and the environment's contracts keep it (`ContractsOK P`).

A register of a shape without memories holds none (`retype_memFree`); the values whose shape may
hold one are memory ops (`memOpOK`), whose results are built from their arguments' memories, by
writes and `poisonBlock`s of frame blocks (`MemPred.write`, `MemPred.poison`), and by contracts
(`evalOp_mems`; atomic roots by `atomicRoot_mems`, `evalPure`'s tuple ops and atomic loads by
`evalPure_mems`). `SInv P` holds at entry (`sinv_entry`: the frame allocations are neither
globals nor the buffer) and is kept by the `Phi`s (`sinv_phis`), the schedule (`sinv_evalAll`)
and so by `enterBlock` (`sinv_enter`).
-/

namespace GoFV.SSA.Sem

mutual
/-- The memories inside a value (`GoFV.Proof.MemInv.MemsOK`). -/
def Val.mems : Val → List Mem
  | .mem m => [m]
  | .tuple vs => Val.memsL vs
  | .agg vs => Val.memsL vs
  | _ => []
/-- The memories inside a list of values. -/
def Val.memsL : List Val → List Mem
  | [] => []
  | v :: vs => Val.mems v ++ Val.memsL vs
end

end GoFV.SSA.Sem

namespace GoFV.Proof.MemInv

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck

/-- A memory predicate kept by writes, by `poisonBlock`s and `poisonBelow`s of blocks that are
neither globals nor the write-barrier buffer (frame blocks: `VarDef`, a callee's frame in the
outgoing-arguments area), by freeing the buffer, and by the defer contracts' replacements of the
runtime's blocks where they are absent or writable (`rtWritable`). (The frame allocations of a
run's entry are `set`s: `sinv_entry`.) -/
structure MemPred (P : Mem → Prop) : Prop where
  write : ∀ {m m' : Mem} {p : Ptr} {bs : Array Byte}, P m → m.write p bs = some m' → P m'
  poison : ∀ {m : Mem} {b : Blk}, P m → (∀ n, b ≠ .global n) → b ≠ .wbuf → P (m.poisonBlock b)
  poisonBelow : ∀ {m : Mem} {b : Blk} (n : Nat), P m → (∀ n, b ≠ .global n) → b ≠ .wbuf →
    P (m.poisonBelow b n)
  free_wbuf : ∀ {m : Mem}, P m → P (m.free .wbuf)
  rt : ∀ {m : Mem} {b : Blk} (a : Alloc), (b = deferBlk ∨ b = panicBlk) → a.writable = true →
    rtWritable m b = true → P m → P (m.set b a)

/-- A predicate kept by every `set` of a block that is neither a global nor the write-barrier
buffer is kept by its `poisonBlock`s. -/
theorem poison_of_set {P : Mem → Prop}
    (hset : ∀ {m : Mem} {b : Blk} (a : Alloc), P m → (∀ n, b ≠ .global n) → b ≠ .wbuf →
      P (m.set b a)) {m : Mem} {b : Blk} (h : P m) (hg : ∀ n, b ≠ .global n) (hw : b ≠ .wbuf) :
    P (m.poisonBlock b) := by
  unfold Mem.poisonBlock
  split
  · exact hset _ h hg hw
  · exact h

/-- A predicate kept by every `set` of a block that is neither a global nor the write-barrier
buffer is kept by its `poisonBelow`s. -/
theorem poisonBelow_of_set {P : Mem → Prop}
    (hset : ∀ {m : Mem} {b : Blk} (a : Alloc), P m → (∀ n, b ≠ .global n) → b ≠ .wbuf →
      P (m.set b a)) {m : Mem} {b : Blk} (n : Nat) (h : P m) (hg : ∀ n, b ≠ .global n)
    (hw : b ≠ .wbuf) : P (m.poisonBelow b n) := by
  unfold Mem.poisonBelow
  split
  · exact hset _ h hg hw
  · exact h

variable {P : Mem → Prop}

/-! ## The memories of a value -/

/-- Every memory inside `v` is `P`. -/
def MemsOK (P : Mem → Prop) (v : Val) : Prop := ∀ m ∈ v.mems, P m

theorem memsL_mem {vs : List Val} {m : Mem} (h : m ∈ Val.memsL vs) : ∃ v ∈ vs, m ∈ v.mems := by
  induction vs with
  | nil => simp [Val.memsL] at h
  | cons v vs ih =>
    simp only [Val.memsL, List.mem_append] at h
    rcases h with h | h
    · exact ⟨v, List.mem_cons_self, h⟩
    · obtain ⟨w, hw, hm⟩ := ih h; exact ⟨w, List.mem_cons_of_mem _ hw, hm⟩

theorem memsOK_list {vs : List Val} (h : ∀ v ∈ vs, MemsOK P v) : ∀ m ∈ Val.memsL vs, P m :=
  fun m hm => by obtain ⟨v, hv, hm⟩ := memsL_mem hm; exact h v hv m hm

theorem memsOK_tuple {vs : List Val} (h : ∀ v ∈ vs, MemsOK P v) : MemsOK P (.tuple vs) :=
  memsOK_list h

theorem memsOK_of_mems_nil {v : Val} (h : v.mems = []) : MemsOK P v := fun m hm => by
  rw [h] at hm; cases hm

theorem memsOK_getD {vs : List Val} (h : ∀ v ∈ vs, MemsOK P v) (i : Nat) :
    MemsOK P (vs.getD i .poison) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : vs[i]? with
  | none => exact memsOK_of_mems_nil rfl
  | some v => exact h v (List.mem_of_getElem? hi)

theorem mem_memsL {vs : List Val} {v : Val} (hv : v ∈ vs) {m : Mem} (hm : m ∈ v.mems) :
    m ∈ Val.memsL vs := by
  induction vs with
  | nil => cases hv
  | cons w ws ih =>
    simp only [Val.memsL, List.mem_append]
    rcases List.mem_cons.1 hv with rfl | hv
    · exact .inl hm
    · exact .inr (ih hv)

theorem memsOK_of_tuple {vs : List Val} (h : MemsOK P (.tuple vs)) : ∀ v ∈ vs, MemsOK P v :=
  fun _ hv _ hm => h _ (mem_memsL hv hm)

/-! ## Decoding and retyping -/

/-- A pointer's word holds no memory. -/
theorem word_mems (p : Ptr) : p.word.mems = [] := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> rfl

theorem decodeInt_mems (w : Width) (bs : Array Byte) : (decodeInt w bs).mems = [] := by
  unfold decodeInt; split
  · rfl
  · split <;> (try split) <;> first | rfl | exact word_mems _

theorem decodePtr_mems (bs : Array Byte) : (decodePtr bs).mems = [] := by
  unfold decodePtr; split <;> (try split) <;> first | rfl | exact word_mems _

theorem ofStr_mems {vs : List Val} (h : Val.memsL vs = []) : (Val.ofStr vs).mems = [] := by
  unfold Val.ofStr; split
  · exact h
  · rfl

theorem ofSlice_mems {vs : List Val} (h : Val.memsL vs = []) : (Val.ofSlice vs).mems = [] := by
  unfold Val.ofSlice; split
  · exact h
  · rfl

theorem retypePtr_mems (v : Val) : v.retypePtr.mems = [] := by
  unfold Val.retypePtr; split <;> first | rfl | exact word_mems _

theorem retypeI64_mems (v : Val) : v.retypeI64.mems = [] := by
  unfold Val.retypeI64; split
  · split <;> rfl
  · first | rfl | exact word_mems _ | (split <;> first | rfl | exact word_mems _)
  · rfl

/-- A string holds no memory. -/
theorem retype_str_mems (v : Val) : (v.retype .str).mems = [] := by
  cases v with
  | agg vs =>
    match vs with
    | [p, l] =>
      simp only [Val.retype]
      exact ofStr_mems (by simp [Val.memsL, retypePtr_mems, retypeI64_mems])
    | [] | [_] | _ :: _ :: _ :: _ => simp [Val.retype, Val.mems]
  | _ => simp [Val.retype, Val.mems]

/-- A slice holds no memory. -/
theorem retype_slice_mems (e : Option Nat) (v : Val) : (v.retype (.slice e)).mems = [] := by
  cases v with
  | agg vs =>
    match vs with
    | [p, l, c] =>
      simp only [Val.retype]
      exact ofSlice_mems (by simp [Val.memsL, retypePtr_mems, retypeI64_mems])
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => simp [Val.retype, Val.mems]
  | _ => simp [Val.retype, Val.mems]

mutual
theorem decode_mems : (bs : Array Byte) → (off : Nat) → (t : Ty) → (decode bs off t).mems = []
  | bs, off, .int w => by
    simp only [decode, decodeInt]
    split
    · rfl
    · split <;> (try split) <;> first | rfl | exact word_mems _
  | bs, off, .bool => by simp only [decode]; split <;> (try split) <;> rfl
  | bs, off, .ptr _ => by
    simp only [decode, decodePtr]; split <;> (try split) <;> first | rfl | exact word_mems _
  | bs, off, .agg fs _ => by
    simp only [decode, Val.mems]; exact decodeFields_mems bs off fs
  | bs, off, .str => by
    simp only [decode]
    exact ofStr_mems (by simp [Val.memsL, decodePtr_mems, decodeInt_mems])
  | bs, off, .slice _ => by
    simp only [decode]
    exact ofSlice_mems (by simp [Val.memsL, decodePtr_mems, decodeInt_mems])
  | _, _, .blob _ => rfl
  | _, _, .empty => rfl
  | _, _, .opaque _ => rfl
  | _, _, .other => rfl
  | _, _, .mem => rfl
  | _, _, .tuple _ => rfl
theorem decodeFields_mems : (bs : Array Byte) → (off : Nat) → (fs : List (Nat × Ty)) →
    Val.memsL (decodeFields bs off fs) = []
  | _, _, [] => rfl
  | bs, off, (o, t) :: fs => by
    simp only [decodeFields, Val.memsL, decode_mems bs (off + o) t, decodeFields_mems bs off fs]
    rfl
end

mutual
theorem retype_mems : (t : Ty) → (v : Val) → ∀ m ∈ (v.retype t).mems, m ∈ v.mems
  | t, .poison => by intro m hm; cases t <;> simp [Val.retype, Val.mems] at hm
  | t, .mem m' => by
    intro m hm; cases t <;> simp [Val.retype, Val.mems] at hm ⊢ <;> exact hm
  | t, .tuple vs => by
    intro m hm
    cases t with
    | tuple ts =>
      simp only [Val.retype] at hm
      split at hm
      · rename_i vs' h
        exact retypePre_mems ts vs h m hm
      · simp [Val.mems] at hm
    | _ => simp [Val.retype, Val.mems] at hm
  | t, .agg vs => by
    intro m hm
    cases t with
    | agg fs n =>
      simp only [Val.retype] at hm
      split at hm
      · rename_i vs' h
        exact retypeFields_mems fs vs h m hm
      · simp [Val.mems] at hm
    | str => simp [retype_str_mems] at hm
    | slice e => simp [retype_slice_mems] at hm
    | _ => simp [Val.retype, Val.mems] at hm
  | t, .int w x => by
    intro m hm
    cases t with
    | int w' => simp only [Val.retype] at hm; split at hm <;> simp [Val.mems] at hm
    | ptr e => cases w <;> simp [Val.retype, Val.mems] at hm
    | _ => simp [Val.retype, Val.mems] at hm
  | t, .ptr p => by
    intro m hm
    cases t with
    | int w' => cases w' <;> simp [Val.retype, Val.mems] at hm
    | _ => simp [Val.retype, Val.mems] at hm
  | t, .bool b => by intro m hm; cases t <;> simp [Val.retype, Val.mems] at hm
  | t, .blob bs => by
    intro m hm
    cases t with
    | blob n => simp only [Val.retype] at hm; split at hm <;> simp [Val.mems] at hm
    | _ => simp [Val.retype, Val.mems] at hm
  | t, .empty => by intro m hm; cases t <;> simp [Val.retype, Val.mems] at hm
theorem retypePre_mems : (ts : List Ty) → (vs : List Val) → ∀ {vs'}, Val.retypePre ts vs = some vs' →
    ∀ m ∈ Val.memsL vs', m ∈ Val.memsL vs
  | [], vs, _, h => by simp only [Val.retypePre, Option.some.injEq] at h; subst h; exact fun _ h => h
  | t :: ts, v :: vs, _, h => by
    simp only [Val.retypePre] at h
    cases hr : Val.retypePre ts vs with
    | none => rw [hr] at h; cases h
    | some ws =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      intro m hm
      simp only [Val.memsL, List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · exact .inl (retype_mems t v m hm)
      · exact .inr (retypePre_mems ts vs hr m hm)
  | _ :: _, [], _, h => by simp [Val.retypePre] at h
theorem retypeFields_mems : (fs : List (Nat × Ty)) → (vs : List Val) → ∀ {vs'},
    Val.retypeFields fs vs = some vs' → ∀ m ∈ Val.memsL vs', m ∈ Val.memsL vs
  | [], [], _, h => by simp only [Val.retypeFields, Option.some.injEq] at h; subst h; exact fun _ h => h
  | (_, t) :: fs, v :: vs, _, h => by
    simp only [Val.retypeFields] at h
    cases hr : Val.retypeFields fs vs with
    | none => rw [hr] at h; cases h
    | some ws =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      intro m hm
      simp only [Val.memsL, List.mem_append] at hm ⊢
      rcases hm with hm | hm
      · exact .inl (retype_mems t v m hm)
      · exact .inr (retypeFields_mems fs vs hr m hm)
  | [], _ :: _, _, h => by simp [Val.retypeFields] at h
  | _ :: _, [], _, h => by simp [Val.retypeFields] at h
end

theorem MemsOK.retype {v : Val} (h : MemsOK P v) (t : Ty) : MemsOK P (v.retype t) :=
  fun m hm => h m (retype_mems t v m hm)

theorem memsOK_poison : MemsOK P .poison := memsOK_of_mems_nil rfl

theorem memsOK_mem {m : Mem} (h : P m) : MemsOK P (.mem m) := fun m' hm' => by
  simp only [Val.mems, List.mem_singleton] at hm'; subst hm'; exact h

theorem MemsOK.mem {m : Mem} (h : MemsOK P (.mem m)) : P m := h m (by simp [Val.mems])

/-! ## Calls -/

/-- The environment's contracts keep memories `P` and values `MemsOK P`. -/
def ContractsOK (P : Mem → Prop) (env : Env) : Prop :=
  ∀ name c, env.extern name = some c → ∀ args clo m, (∀ a ∈ args, MemsOK P a) →
    (∀ a ∈ clo, MemsOK P a) → P m →
    match c args clo m with
    | .returned rs m' => P m' ∧ ∀ r ∈ rs, MemsOK P r
    | _ => True

/-! ## The defer contracts (`Env.atAct`) -/

theorem decode_entries_mems {m : Mem} {a c : Val} (h : (deferEntries m).getLast? = some (a, c)) :
    c.mems = [] := by
  have hm := List.mem_of_getLast? h
  unfold deferEntries at hm
  split at hm
  · obtain ⟨i, -, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    rw [← he.2]; exact decode_mems _ _ _
  · cases hm

theorem popDefer_some {act : Nat} {m m' : Mem} {clo : Val}
    (h : popDefer act m = .ok (some (clo, m'))) :
    clo.mems = [] ∧ ∃ es, m' = setDeferEntries m es := by
  simp only [popDefer] at h
  split at h
  · next a c hl =>
    split at h
    · split at h
      · cases h; exact ⟨decode_entries_mems hl, _, rfl⟩
      · cases h
    · cases h
  · cases h

theorem panicRec_mems {m : Mem} {r w : Bool} {k : Nat} {v : Val}
    (h : panicRec? m = .ok (some (r, w, k, v))) : v.mems = [] := by
  unfold panicRec? at h
  split at h
  · cases h
  · next a _ =>
    have hd := decode_mems a.data 0 recTy
    split at h
    · next r' w' k' v' he =>
      rw [he] at hd
      split at h
      · cases h
        simp only [Val.mems, Val.memsL, List.append_eq_nil_iff] at hd
        exact hd.2.2.2.1
      · cases h
    · cases h

/-- What `ContractsOK` asks of a contract's outcome, from its `returned` case. -/
theorem okOut_of {o : COutcome} (h : ∀ rs m', o = .returned rs m' → P m' ∧ ∀ r ∈ rs, MemsOK P r) :
    match (generalizing := false) o with
    | .returned rs m' => P m' ∧ ∀ r ∈ rs, MemsOK P r
    | _ => True := by
  cases o with
  | returned rs m' => exact h rs m' rfl
  | panicked => trivial
  | stuck => trivial

section DeferContracts

variable (hP : MemPred P) {env : Env} (hE : ContractsOK P env) (act : Nat)
include hP hE

theorem deferreturn_go_ok : ∀ (n : Nat) (m : Mem), P m →
    match deferreturn.go env act n m with
    | .returned rs m' => P m' ∧ ∀ r ∈ rs, MemsOK P r
    | _ => True
  | 0, m, hm => ⟨hm, fun _ h => by cases h⟩
  | n + 1, m, hm => by
    apply okOut_of
    intro rs m' ho
    simp only [deferreturn.go] at ho
    split at ho
    · cases ho
    next hw =>
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hw
    cases hp : popDefer act m with
    | error msg => rw [hp] at ho; cases ho
    | ok o =>
      rw [hp] at ho
      cases o with
      | none => cases ho; exact ⟨hm, fun _ h => by cases h⟩
      | some p =>
        obtain ⟨clo, m1⟩ := p
        obtain ⟨hclo, es, rfl⟩ := popDefer_some hp
        have hm1 : P (setDeferEntries m es) := hP.rt _ (.inl rfl) rfl hw hm
        dsimp only at ho
        cases hd : deferredCode? (setDeferEntries m es) clo with
        | error msg => rw [hd] at ho; cases ho
        | ok code =>
          rw [hd] at ho
          dsimp only at ho
          cases code with
          | none => cases ho
          | some name =>
            simp only [callDeferred] at ho
            cases hx : env.extern name with
            | none => rw [hx] at ho; cases ho
            | some c =>
              rw [hx] at ho
              dsimp only at ho
              have H := hE name c hx [] (some clo) _ (fun _ h => by cases h)
                (fun a ha => by cases ha; exact memsOK_of_mems_nil hclo)
                (hP.poison (b := .outargs act) hm1 (fun _ h => by cases h) (fun h => by cases h))
              revert ho H
              cases c [] (some clo) ((setDeferEntries m es).poisonBlock (.outargs act)) with
              | returned rs2 m2 =>
                intro ho H
                have := deferreturn_go_ok n m2 H.1
                dsimp only at ho
                rw [ho] at this
                exact this
              | panicked e m2 => intro ho _; cases ho
              | stuck msg => intro ho _; cases ho

omit hE in
theorem gorecover_ok {args : List Val} {clo : Option Val} {m : Mem} (hm : P m) :
    match gorecover act args clo m with
    | .returned rs m' => P m' ∧ ∀ r ∈ rs, MemsOK P r
    | _ => True := by
  have hnil : P m ∧ ∀ r ∈ [nilIface], MemsOK P r := ⟨hm, fun r hr => by
    rw [List.mem_singleton.1 hr]; exact memsOK_of_mems_nil rfl⟩
  apply okOut_of
  intro rs m' ho
  simp only [gorecover] at ho
  cases hr : panicRec? m with
  | error msg => rw [hr] at ho; cases ho
  | ok o =>
    rw [hr] at ho
    rcases o with _ | ⟨_ | _, w, k, v⟩
    · cases ho; exact hnil
    · dsimp only at ho
      split at ho
      · split at ho
        · next hw =>
          cases ho
          refine ⟨hP.rt _ (.inr rfl) rfl hw hm, fun r hr' => ?_⟩
          rw [List.mem_singleton.1 hr']
          exact memsOK_of_mems_nil (panicRec_mems hr)
        · cases ho
      · cases ho; exact hnil
    · cases ho; exact hnil

/-- **`Env.atAct` keeps `ContractsOK P`**: its defer contracts replace the runtime's blocks only
where they are writable (`MemPred.rt`) and call the environment's contracts. -/
theorem ContractsOK.atAct : ContractsOK P (env.atAct act) := by
  intro name c hc args clo m _ _ hm
  simp only [Env.atAct] at hc
  split at hc
  · cases hc
    apply okOut_of
    intro rs m' ho
    simp only [deferproc] at ho
    split at ho
    · split at ho
      · next hw => cases ho; exact ⟨hP.rt _ (.inl rfl) rfl hw hm, fun _ h => by cases h⟩
      · cases ho
    · cases ho
  split at hc
  · cases hc
    apply okOut_of
    intro rs m' ho
    simp only [deferprocStack] at ho
    split at ho
    all_goals first
      | cases ho
      | (split at ho
         · cases ho
         · split at ho
           · next hw => cases ho; exact ⟨hP.rt _ (.inl rfl) rfl hw hm, fun _ h => by cases h⟩
           · cases ho)
  split at hc
  · cases hc
    exact deferreturn_go_ok hP hE act _ m hm
  split at hc
  · cases hc
    exact gorecover_ok hP act hm
  · exact hE name c hc args clo m ‹_› ‹_› hm

end DeferContracts

theorem decodeArgs_mems (tabs : Tables) (act : Nat) (m : Mem) :
    ∀ (ps : List ABIParam) {pieces args : List Val}, (∀ p ∈ pieces, MemsOK P p) →
      decodeArgs tabs act m ps pieces = some args → ∀ a ∈ args, MemsOK P a
  | [], [], _, _, hd => by simp only [decodeArgs] at hd; cases hd; simp
  | [], _ :: _, _, _, hd => by simp [decodeArgs] at hd
  | p :: ps, pieces, args, hp, hd => by
    unfold decodeArgs at hd
    dsimp only at hd
    split at hd
    · cases hr : m.read ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (tabs.ty p.type).size with
      | none => rw [hr] at hd; cases hd
      | some bs =>
        rw [hr] at hd
        cases hn : decodeArgs tabs act m ps pieces with
        | none => simp [hn, bind, Option.bind] at hd
        | some r =>
          simp only [hn, bind, Option.bind, pure] at hd
          cases hd
          intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact memsOK_of_mems_nil (decode_mems _ _ _)
          · exact decodeArgs_mems tabs act m ps hp hn a ha
    · split at hd
      · cases hd
      · cases hn : decodeArgs tabs act m ps (pieces.drop p.regs.size) with
        | none => simp [hn, bind, Option.bind] at hd
        | some r =>
          simp only [hn, bind, Option.bind, pure] at hd
          cases hd
          intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact memsOK_of_mems_nil (decode_mems _ _ _)
          · exact decodeArgs_mems tabs act m ps (fun x hx => hp x (List.mem_of_mem_drop hx)) hn a ha

theorem encodeResults_mems (hP : MemPred P) (tabs : Tables) (act : Nat) :
    ∀ (ps : List ABIParam) (rs : List Val) {m : Mem} {r : List Val × Mem},
      P m → encodeResults tabs act ps rs m = some r → P r.2 ∧ ∀ p ∈ r.1, MemsOK P p
  | [], [], m, r, hm, he => by
    simp only [encodeResults] at he; cases he; exact ⟨hm, by simp⟩
  | [], _ :: _, _, _, _, he => by simp [encodeResults] at he
  | _ :: _, [], _, _, _, he => by simp [encodeResults] at he
  | p :: ps, x :: xs, m, r, hm, he => by
    unfold encodeResults at he
    dsimp only at he
    split at he
    · cases hw : m.write ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (encode (tabs.ty p.type) x) with
      | none => rw [hw] at he; cases he
      | some m1 =>
        rw [hw] at he
        exact encodeResults_mems hP tabs act ps xs (hP.write hm hw) he
    · cases hn : encodeResults tabs act ps xs m with
      | none => simp [hn, bind, Option.bind] at he
      | some q =>
        simp only [hn, bind, Option.bind, pure] at he
        cases he
        obtain ⟨h1, h2⟩ := encodeResults_mems hP tabs act ps xs hm hn
        refine ⟨h1, fun y hy => ?_⟩
        rcases List.mem_append.1 hy with hy | hy
        · simp only [toPieces, List.mem_map] at hy
          obtain ⟨_, -, rfl⟩ := hy
          exact memsOK_of_mems_nil (decode_mems _ _ _)
        · exact h2 y hy

theorem retypeResults_mems (tabs : Tables) :
    ∀ (ps : List ABIParam) (rs : List Val), (∀ r ∈ rs, MemsOK P r) →
      ∀ x ∈ retypeResults tabs ps rs, MemsOK P x
  | p :: ps, r :: rs, h => by
    intro x hx
    simp only [retypeResults, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (h r List.mem_cons_self).retype _
    · exact retypeResults_mems tabs ps rs (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx
  | [], rs, h => by simpa [retypeResults] using h
  | _ :: _, [], _ => by simp [retypeResults]

theorem callTarget_sub (ctx : Sem.Ctx) (v : Value) (argv : List Val) :
    (∀ y ∈ (callTarget ctx v argv).2.1, y ∈ argv) ∧ (∀ y ∈ (callTarget ctx v argv).2.2, y ∈ argv) := by
  unfold callTarget
  split
  · simp only [Option.mem_def, Option.some.injEq]
    exact ⟨fun y hy => by subst hy; simp, fun y hy => by simp [hy]⟩
  · simp only [Option.mem_def, Option.some.injEq]
    exact ⟨fun y hy => by subst hy; simp, fun y hy => by simp [hy]⟩
  · exact ⟨fun y hy => by simp at hy, fun y hy => by simp [hy]⟩
  · exact ⟨fun y hy => by simp at hy, fun y hy => by simp [hy]⟩
  · exact ⟨fun y hy => by simp at hy, fun y hy => hy⟩

theorem bind_ok_inv {α β : Type} {x : Res α} {k : α → Res β} {r : β}
    (h : (x >>= k) = .ok r) : ∃ a, x = .ok a ∧ k a = .ok r := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | panic e m => cases h
  | stuck msg => cases h

theorem ofOption_ok {α : Type} {msg : String} {o : Option α} {a : α}
    (h : Res.ofOption msg o = .ok a) : o = some a := by
  cases o with
  | none => cases h
  | some b => cases h; rfl

/-- **A call's result is `MemsOK P`.** -/
theorem callOp_mems (hP : MemPred P) {env : Env} (hE : ContractsOK P env) {ctx : Sem.Ctx} {v : Value}
    {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) {r : Val} (h : callOp env ctx v argv = .ok r) :
    MemsOK P r := by
  unfold callOp at h
  have hsub := callTarget_sub ctx v argv
  generalize callTarget ctx v argv = T at h hsub
  obtain ⟨callee?, clo, rest⟩ := T
  obtain ⟨hclo, hrest⟩ := hsub
  dsimp only at h hclo hrest
  have hR : ∀ a ∈ rest.dropLast, MemsOK P a := fun a h' => ha a (hrest a (List.dropLast_subset _ h'))
  have hcl : ∀ a ∈ clo, MemsOK P a := fun a h' => ha a (hclo a h')
  split at h
  rotate_left
  · cases h
  rename_i M hl
  have hM : P M := (ha _ (hrest _ (List.mem_of_getLast? hl))).mem
  obtain ⟨M', hw, h⟩ := bind_ok_inv h
  have hM' : P M' := by cases hw; exact hM
  have haddr : ∀ (ps : List ABIParam), MemsOK P (Val.agg (ps.map fun p =>
      if p.regs.isEmpty = true then Val.ptr ⟨Blk.outargs ctx.act, BitVec.ofInt 64 p.offset⟩
      else Val.poison)) := by
    intro ps
    refine memsOK_list fun a ha => ?_
    simp only [List.mem_map] at ha
    obtain ⟨p, -, rfl⟩ := ha
    split <;> exact memsOK_of_mems_nil rfl
  split at h <;> obtain ⟨args, hargs, h⟩ := bind_ok_inv h
  all_goals
    have hA : ∀ a ∈ args, MemsOK P a := by
      first
      | exact decodeArgs_mems _ _ _ _ hR (ofOption_ok hargs)
      | (cases hargs; exact retypeResults_mems ctx.tabs _ _ hR)
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    obtain ⟨callee, -, h⟩ := bind_ok_inv h
    obtain ⟨c, hc, h⟩ := bind_ok_inv h
    have hcc := ContractsOK.atAct hP hE ctx.act callee c (ofOption_ok hc) args clo
      (M'.poisonBelow (.outargs ctx.act) (callFrame ctx.tabs v.aux
        ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter (!·.out))
        (!env.noSpill callee))) hA hcl
      (hP.poisonBelow _ hM' (fun _ h => by cases h) (by simp))
    cases hco : c args clo (M'.poisonBelow (.outargs ctx.act) (callFrame ctx.tabs v.aux
        ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter (!·.out))
        (!env.noSpill callee))) with
    | stuck msg => rw [hco] at h; cases h
    | panicked e m' => rw [hco] at h; cases h
    | returned rs m' =>
      rw [hco] at h hcc
      obtain ⟨hm', hrs⟩ := hcc
      dsimp only at h
      obtain ⟨x, hx, h⟩ := bind_ok_inv h
      obtain ⟨h1, h2⟩ := encodeResults_mems hP ctx.tabs ctx.act _ _ hm' (ofOption_ok hx)
      have hrs' : ∀ ps, ∀ x ∈ retypeResults ctx.tabs ps rs, MemsOK P x :=
        fun ps => retypeResults_mems ctx.tabs ps rs hrs
      cases h
      refine memsOK_tuple fun a ha => ?_
      rcases List.mem_append.1 ha with ha | ha
      · first | exact h2 a ha | exact hrs' _ a ha
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact memsOK_mem h1
        · exact haddr _

/-! ## Memory roots, atomics, pure memory ops -/

mutual
theorem decodeLoad_mems (bs : Array Byte) (off : Nat) : (t : Ty) → (decodeLoad bs off t).mems = []
  | .agg fs _ => by
    simp only [decodeLoad]
    split
    · rfl
    · simp only [Val.mems]; exact decodeLoadFields_mems bs off fs
  | .int _ => by simp only [decodeLoad]; exact decode_mems _ _ _
  | .bool => by simp only [decodeLoad]; exact decode_mems _ _ _
  | .ptr _ => by simp only [decodeLoad]; exact decode_mems _ _ _
  | .blob _ => by simp only [decodeLoad]; exact decode_mems _ _ _
  | .empty => rfl
  | .str => by simp only [decodeLoad]; split; rfl; exact decode_mems _ _ _
  | .slice _ => by simp only [decodeLoad]; split; rfl; exact decode_mems _ _ _
  | .opaque _ => by simp only [decodeLoad]; exact decode_mems _ _ _
  | .other => rfl
  | .mem => rfl
  | .tuple _ => rfl
theorem decodeLoadFields_mems (bs : Array Byte) (off : Nat) :
    (fs : List (Nat × Ty)) → Val.memsL (decodeLoadFields bs off fs) = []
  | [] => rfl
  | (o, t) :: fs => by
    simp only [decodeLoadFields, Val.memsL, decodeLoad_mems bs (off + o) t,
      decodeLoadFields_mems bs off fs]
    rfl
end

theorem load_mems (m : Mem) (t : Ty) (p : Ptr) : (m.load t p).mems = [] := by
  unfold Mem.load
  split <;> (try split) <;> first | rfl | exact decodeLoad_mems _ _ _

theorem int2_mems (w : Width) (g : BitVec w.bits → BitVec w.bits → Val)
    (hg : ∀ x y, (g x y).mems = []) (l : List Val) : (GoFV.SSA.Sem.int2 w g l).mems = [] := by
  unfold GoFV.SSA.Sem.int2
  split
  · split
    · exact hg _ _
    · rfl
  · rfl

theorem frameBlk_ne (tabs : Tables) (act : Nat) (n : AuxRef) :
    (∀ s, frameBlk tabs act n ≠ .global s) ∧ frameBlk tabs act n ≠ .wbuf := by
  unfold frameBlk; split <;> simp

/-- **A memory root's result** (any op `memRoot` evaluates). -/
theorem memRoot_mems (hP : MemPred P) {ctx : Sem.Ctx} {v : Value} {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a)
    {r : Val} (h : memRoot ctx v argv = .ok r) : MemsOK P r := by
  have hm : ∀ m, Val.mem m ∈ argv → P m := fun m hm => (ha _ hm).mem
  have wr : ∀ {what : String} {m : Mem} {p : Ptr} {bs : Array Byte}, P m →
      writeRes what (m.write p bs) = .ok r → MemsOK P r := by
    intro what m p bs hm h
    unfold writeRes at h
    split at h
    · rename_i m' hw; cases h; exact memsOK_mem (hP.write hm hw)
    · cases h
  unfold memRoot at h
  split at h
  all_goals first
    | exact wr (hm _ (by simp)) h
    | (cases h; done)
    | (cases h; exact memsOK_of_mems_nil rfl)
    | (cases h; exact memsOK_mem (hP.free_wbuf (hm _ (by simp))))
    | (cases h; exact ha _ (by simp))
    | (split at h <;> first
       | exact wr (hm _ (by simp)) h
       | (cases h; done)
       | (cases h; exact memsOK_of_mems_nil rfl)
       | (cases h; exact memsOK_mem (hP.poison (hm _ (by simp)) (frameBlk_ne _ _ _).1
           (frameBlk_ne _ _ _).2))
       | (cases h; exact ha _ (by simp))
       | (split at h <;> first
          | exact wr (hm _ (by simp)) h
          | (cases h; done)
          | (cases h; exact ha _ (by simp))))

/-- A read-modify-write returns the old value or an integer. -/
theorem step_mems (k : Atomic.Kind) (w : Width) (m : Mem) (t : Ty) (p : Ptr) (x : Val) {y : Val}
    (hy : (Atomic.step k w (m.load t p) x).2 = some y) : y.mems = [] := by
  cases k <;> simp only [Atomic.step, Option.some.injEq, reduceCtorEq] at hy <;> subst hy
  all_goals first
    | exact load_mems _ _ _
    | exact int2_mems _ _ (fun _ _ => rfl) _

/-- **An atomic root's result.** -/
theorem atomicRoot_mems (hP : MemPred P) {v : Value} {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) {r : Val}
    (h : atomicRoot v argv = .ok r) : MemsOK P r := by
  have hm : ∀ m, Val.mem m ∈ argv → P m := fun m hm => (ha _ hm).mem
  unfold atomicRoot at h
  split at h
  · unfold Atomic.barrier at h
    split at h
    · split at h
      · cases h; exact ha _ (by simp)
      · cases h
    · cases h
  · unfold Atomic.prefetch at h
    split at h
    · split at h
      · cases h; exact ha _ (by simp)
      · cases h
    · cases h
  · unfold Atomic.rmwRoot at h
    split at h
    · rename_i p x m
      have hm0 : P m := hm _ (by simp)
      split at h
      · rename_i k t _
        unfold Atomic.rmw at h
        split at h
        · split at h
          · rename_i m' hw
            cases h
            have hm' := hP.write hm0 hw
            unfold Atomic.result
            split
            · rename_i y hy
              refine memsOK_tuple fun z hz => ?_
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
              rcases hz with rfl | rfl
              · exact memsOK_of_mems_nil (step_mems _ _ _ _ _ _ hy)
              · exact memsOK_mem hm'
            · exact memsOK_mem hm'
          · cases h
        · cases h
      · cases h
    · cases h
  · unfold Atomic.casRoot at h
    split at h
    · rename_i p o n m
      have hm0 : P m := hm _ (by simp)
      split at h
      · unfold Atomic.cas at h
        split at h
        · split at h
          · split at h
            · split at h
              · rename_i m' hw
                cases h
                refine memsOK_tuple fun z hz => ?_
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                rcases hz with rfl | rfl
                · exact memsOK_of_mems_nil rfl
                · exact memsOK_mem (hP.write hm0 hw)
              · cases h
            · cases h
              refine memsOK_tuple fun z hz => ?_
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
              rcases hz with rfl | rfl
              · exact memsOK_of_mems_nil rfl
              · exact memsOK_mem hm0
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## `evalOp` on the memory ops -/

/-- The ops of `memOps` that `evalOp` evaluates by `evalPure`. -/
def pureMemOps : List Op :=
  [.Phi, .Copy, .Select0, .Select1, .SelectN, .MakeResult, .AtomicLoad8, .AtomicLoad32,
   .AtomicLoad64, .AtomicLoadPtr, .AtomicLoadAcq32, .AtomicLoadAcq64]

theorem pureMemOps_pure : ∀ o ∈ pureMemOps, o ∉ evalOpArms ∧ isRoot o = false := by decide

theorem atomicRootOps_root : ∀ o ∈ atomicRootOps, o ∉ evalOpArms ∧ isRoot o = true := by decide

theorem memOps_split : ∀ o ∈ memOps, o ∈ pureMemOps ∨ o = .InitMem ∨ o = .PanicBounds ∨
    (o = .Store ∨ o = .Zero ∨ o = .Move ∨ o = .VarDef ∨ o = .VarLive ∨ o = .KeepAlive) ∨
    (o = .StaticCall ∨ o = .ClosureCall ∨ o = .InterCall ∨ o = .StaticLECall ∨
      o = .ClosureLECall ∨ o = .InterLECall) := by decide

theorem select_mems (i : Nat) {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) :
    MemsOK P (Tuple.select i argv) := by
  unfold Tuple.select
  split
  · exact memsOK_getD (memsOK_of_tuple (ha _ (by simp))) _
  · exact memsOK_poison

theorem selectN_mems (k : Int64) {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) :
    MemsOK P (Tuple.selectN k argv) := by
  unfold Tuple.selectN
  split
  · split
    · exact memsOK_poison
    · exact memsOK_getD (memsOK_of_tuple (ha _ (by simp))) _
  · exact memsOK_poison

theorem atomicLoad_mems (t : Ty) {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) :
    MemsOK P (atomicLoad t argv) := by
  unfold atomicLoad
  split
  · split
    · refine memsOK_tuple fun z hz => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · split
        · exact memsOK_poison
        · exact memsOK_of_mems_nil (load_mems _ _ _)
      · exact ha _ (by simp)
    · exact memsOK_poison
  · exact memsOK_poison

theorem copy_mems (ty : Ty) (k : Int64) (ax : Option AuxRef) :
    ∀ {argv : List Val}, (∀ a ∈ argv, MemsOK P a) → MemsOK P (evalPure .Copy ty k ax argv)
  | [x], ha => ha x List.mem_cons_self
  | [], _ => memsOK_poison
  | _ :: _ :: _, _ => memsOK_poison

theorem evalPure_mems {o : Op} (ho : o ∈ pureMemOps) (ty : Ty) (k : Int64) (ax : Option AuxRef)
    {argv : List Val} (ha : ∀ a ∈ argv, MemsOK P a) : MemsOK P (evalPure o ty k ax argv) := by
  simp only [pureMemOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact memsOK_poison
  · exact copy_mems ty k ax ha
  · exact select_mems 0 ha
  · exact select_mems 1 ha
  · exact selectN_mems k ha
  · exact memsOK_tuple ha
  all_goals exact atomicLoad_mems ty ha

/-- **A memory op's result** (`WBCheck.memOpOK`), from arguments and an initial memory whose
memories are `P`. -/
theorem evalOp_mems (hP : MemPred P) {env : Env} (hE : ContractsOK P env) {ctx : Sem.Ctx} {fr : Frame}
    (h0 : P fr.mem0) {v : Value} (hop : memOpOK v.op = true) {argv : List Val}
    (ha : ∀ a ∈ argv, MemsOK P a) {ty : Ty} {r : Val} (h : evalOp env ctx fr v argv ty = .ok r) :
    MemsOK P r := by
  have hop' : v.op ∈ memOps ∨ v.op ∈ atomicRootOps := by
    simpa only [memOpOK, Bool.or_eq_true, List.contains_iff_mem] using hop
  rcases hop' with hm | hm
  · rcases memOps_split _ hm with hp | hp | hp | hp | hp
    · obtain ⟨hn, hr⟩ := pureMemOps_pure _ hp
      rw [TabsMod.evalOp_pure_of hn hr] at h
      cases h
      exact evalPure_mems hp _ _ _ ha
    · simp only [evalOp, hp] at h; cases h; exact memsOK_mem h0
    · rw [DAE.evalOp_panicBounds hp] at h; exact absurd h panicBounds_not_ok
    · rw [DAE.evalOp_memRoot (by rcases hp with h | h | h | h | h | h <;> simp [h])] at h
      exact memRoot_mems hP ha h
    · have he : evalOp env ctx fr v argv ty = callOp env ctx v argv := by
        rcases hp with h | h | h | h | h | h <;> simp only [evalOp, h]
      rw [he] at h
      exact callOp_mems hP hE ha h
  · obtain ⟨hn, hr⟩ := atomicRootOps_root _ hm
    rw [TabsMod.evalOp_notArm hn, if_pos hr] at h
    exact atomicRoot_mems hP ha h

theorem int3_mems (w : Width) (g : BitVec w.bits → BitVec w.bits → BitVec w.bits → Val)
    (hg : ∀ x y z, (g x y z).mems = []) (l : List Val) : (GoFV.SSA.Sem.int3 w g l).mems = [] := by
  unfold GoFV.SSA.Sem.int3
  split
  · split
    · exact hg _ _ _
    · rfl
  · rfl

theorem memFreeOps_notArm : ∀ o ∈ memFreeOps, o ∉ evalOpArms := by decide

/-- **The result of an op of `memFreeOps`** holds no memory: a tuple of integers and booleans
(`evalPure`), or none (a tail call is `stuck`). -/
theorem evalOp_memFreeOps_mems {env : Env} {ctx : Sem.Ctx} {fr : Frame} {v : Value}
    (hop : memFreeOps.contains v.op = true) {argv : List Val} {ty : Ty} {r : Val}
    (h : evalOp env ctx fr v argv ty = .ok r) : r.mems = [] := by
  have hm : v.op ∈ memFreeOps := List.contains_iff_mem.1 hop
  rw [TabsMod.evalOp_notArm (memFreeOps_notArm _ hm)] at h
  have hunm : v.op = .TailLECall ∨ v.op = .TailLECallInter → False := fun ho => by
    have hmo : Atomic.modelled v.op = false := by rcases ho with h | h <;> rw [h] <;> rfl
    have hr : isRoot v.op = true := by rcases ho with h | h <;> rw [h] <;> rfl
    obtain ⟨msg, hs⟩ := atomicRoot_unmodelled hmo argv
    rw [if_pos hr, hs] at h
    cases h
  have hpure : isRoot v.op = false → r = evalPure v.op ty v.auxInt v.aux argv := fun hr => by
    rw [if_neg (by rw [hr]; exact Bool.false_ne_true)] at h
    cases h
    rfl
  simp only [memFreeOps, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with ho | ho | ho | ho | ho | ho | ho | ho | ho
  · rw [hpure (by rw [ho] <;> rfl), ho]; exact int2_mems .w32 _ (fun _ _ => rfl) argv
  · rw [hpure (by rw [ho] <;> rfl), ho]; exact int2_mems .w64 _ (fun _ _ => rfl) argv
  · rw [hpure (by rw [ho] <;> rfl), ho]; exact int2_mems .w32 _ (fun _ _ => rfl) argv
  · rw [hpure (by rw [ho] <;> rfl), ho]; exact int2_mems .w64 _ (fun _ _ => rfl) argv
  · rw [hpure (by rw [ho] <;> rfl), ho]; exact int3_mems .w64 _ (fun _ _ _ => by split <;> rfl) argv
  · rw [hpure (by rw [ho] <;> rfl), ho]; exact int3_mems .w64 _ (fun _ _ _ => by split <;> rfl) argv
  · rw [hpure (by rw [ho] <;> rfl), ho]; exact int3_mems .w64 _ (fun _ _ _ => by split <;> rfl) argv
  · exact (hunm (.inl ho)).elim
  · exact (hunm (.inr ho)).elim

/-! ## Retyping to a shape without memories -/

theorem nil_of_retype (t : Ty) (v : Val) (h : v.mems = []) : (v.retype t).mems = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun m hm => by
    have := retype_mems t v m hm
    rw [h] at this
    cases this

mutual
theorem retype_memFree : (t : Ty) → memFree t = true → (v : Val) → (v.retype t).mems = []
  | t, h, .mem _ => by cases t <;> simp [memFree, Val.retype, Val.mems] at h ⊢
  | t, h, .tuple _ => by cases t <;> simp [memFree, Val.retype, Val.mems] at h ⊢
  | t, h, .agg vs => by
    cases t with
    | agg fs n =>
      simp only [Val.retype]
      split
      · rename_i vs' hr
        simp only [Val.mems]
        exact retypeFields_memFree fs (by simpa only [memFree] using h) vs hr
      · rfl
    | str => exact retype_str_mems _
    | slice e => exact retype_slice_mems e _
    | _ => simp [memFree, Val.retype, Val.mems] at h ⊢
  | t, _, .poison => nil_of_retype t .poison rfl
  | t, _, .int w x => nil_of_retype t (.int w x) rfl
  | t, _, .ptr p => nil_of_retype t (.ptr p) rfl
  | t, _, .bool b => nil_of_retype t (.bool b) rfl
  | t, _, .blob bs => nil_of_retype t (.blob bs) rfl
  | t, _, .empty => nil_of_retype t .empty rfl
theorem retypeFields_memFree : (fs : List (Nat × Ty)) → memFree.memFreeFields fs = true →
    (vs : List Val) → ∀ {vs'}, Val.retypeFields fs vs = some vs' → Val.memsL vs' = []
  | [], _, [], _, h => by
    simp only [Val.retypeFields, Option.some.injEq] at h; subst h; rfl
  | (_, t) :: fs, hf, v :: vs, _, h => by
    simp only [Val.retypeFields] at h
    cases hr : Val.retypeFields fs vs with
    | none => rw [hr] at h; cases h
    | some ws =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp only [memFree.memFreeFields, Bool.and_eq_true] at hf
      simp only [Val.memsL, retype_memFree t hf.1 v, retypeFields_memFree fs hf.2 vs hr]
      rfl
  | [], _, _ :: _, _, h => by simp [Val.retypeFields] at h
  | _ :: _, _, [], _, h => by simp [Val.retypeFields] at h
end

/-! ## Registers -/

theorem regs_set_mems {r : Array (Option Val)}
    (hr : ∀ (z : Nat) (y : Val), r[z]? = some (some y) → MemsOK P y)
    {i : Nat} {x : Val} (hx : MemsOK P x) :
    ∀ (z : Nat) (y : Val), (r.set! i (some x))[z]? = some (some y) → MemsOK P y := by
  intro z y hz
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hz
  split at hz
  · split at hz
    · cases hz; exact hx
    · cases hz
  · exact hr z y hz

theorem setPhis_mems : ∀ (ps : List (ID × Val)) (r : Array (Option Val)),
    (∀ p ∈ ps, MemsOK P p.2) → (∀ (z : Nat) (y : Val), r[z]? = some (some y) → MemsOK P y) →
    ∀ (z : Nat) (y : Val), (setPhis ps r)[z]? = some (some y) → MemsOK P y
  | [], _, _, hr => hr
  | (id, x) :: ps, r, hp, hr => by
    unfold setPhis; rw [List.foldl_cons]
    exact setPhis_mems ps _ (fun p hp' => hp p (List.mem_cons_of_mem _ hp'))
      (regs_set_mems hr (hp _ List.mem_cons_self))

theorem mapM_ofOption_mems {m : ID → String} {r : ID → Option Val}
    (hr : ∀ a z, r a = some z → MemsOK P z) :
    ∀ {l : List ID} {L : List Val}, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L →
      ∀ y ∈ L, MemsOK P y
  | [], L, h => by
    rw [List.mapM_nil] at h; cases h; intro y hy; cases hy
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : r a with
    | none => rw [ha] at h; cases h
    | some z =>
      rw [ha] at h
      change Res.bind (List.mapM (fun a => Res.ofOption (m a) (r a)) l) _ = _ at h
      cases hl : l.mapM (fun a => Res.ofOption (m a) (r a)) with
      | ok L' =>
        rw [hl] at h
        cases h
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hr a _ ha
        · exact mapM_ofOption_mems hr hl y hy
      | panic e m' => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h

/-- A value evaluated from registers whose memories are `P`, by an op that keeps them. -/
theorem evalValue_mems {env : Env} {ctx : Sem.Ctx} {fr : Frame} {v : Value} {y : Val}
    (hr : ∀ (a : Nat) (z : Val), fr.regs[a]? = some (some z) → MemsOK P z)
    (hop : ∀ argv, (∀ a ∈ argv, MemsOK P a) → ∀ r,
      evalOp env ctx fr v argv (ctx.tys[v.id]?.getD .other) = .ok r →
      MemsOK P (r.retype (ctx.tys[v.id]?.getD .other)))
    (h : evalValue env ctx fr v = .ok y) : MemsOK P y := by
  unfold evalValue at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e m => rw [hm] at h; cases h
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    have ha : ∀ a ∈ argv, MemsOK P a :=
      mapM_ofOption_mems (fun a z hz => hr a z (Option.join_eq_some_iff.1 hz)) hm
    cases ho : evalOp env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [ho] at h; cases h; exact hop argv ha r ho
    | panic e m => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h

/-! ## The source invariant -/

/-- The frame of a run of the source: its initial memory and every memory a register holds are
`P`. -/
def SInv (P : Mem → Prop) (fr : Frame) : Prop :=
  P fr.mem0 ∧ ∀ (x : ID) (y : Val), fr.regs[x]? = some (some y) → MemsOK P y

theorem SInv.set {fr : Frame} (hs : SInv P fr) {id : ID} {x : Val} (hx : MemsOK P x) :
    SInv P (fr.set id x) :=
  ⟨hs.1, regs_set_mems hs.2 hx⟩

theorem wb_foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β)
    (hf : ∀ b a, P b → P (f b a)) : ∀ (L : List α) (b : β), P b → P (L.foldl f b)
  | [], _, h => h
  | a :: L, b, h => wb_foldl_inv P f hf L (f b a) (hf b a h)

/-- The entry frame of a run whose memory with the global image is `P`, for a `P` that every `set`
of a block that is neither a global nor the write-barrier buffer keeps (the frame allocations). -/
theorem sinv_entry
    (hset : ∀ {m : Mem} {b : Blk} (a : Alloc), P m → (∀ n, b ≠ .global n) → b ≠ .wbuf →
      P (m.set b a))
    {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    (h : P (addGlobals env mem)) : SInv P (entryFrame env (Ctx.make tabs f) args mem) := by
  refine ⟨?_, fun x y hx => ?_⟩
  · simp only [entryFrame, frameMem, frameAllocs]
    rw [← Array.foldl_toList]
    refine wb_foldl_inv P _ (fun m a hm => ?_) _ _
      (hset _ h (fun _ h => by cases h) (by simp))
    obtain ⟨n, sz, pi⟩ := a
    exact hset _ hm (frameBlk_ne _ _ _).1 (frameBlk_ne _ _ _).2
  · change (Array.replicate _ none)[x]? = some (some y) at hx
    rw [Array.getElem?_replicate] at hx
    split at hx <;> cases hx

theorem sinv_phis {ctx : Sem.Ctx} {fr : Frame} {B : Block} {i : Nat} {ps : List (ID × Val)}
    (hs : SInv P fr) (hps : B.values.toList.filterMapM (phiStep ctx fr i) = .ok ps) :
    SInv P { fr with regs := setPhis ps fr.regs } := by
  obtain ⟨-, hsome, -⟩ := filterMapM_phi hps
  refine ⟨hs.1, setPhis_mems ps fr.regs (fun p hp => ?_) hs.2⟩
  obtain ⟨-, v, a, y, -, -, -, hy, hp2⟩ := phiStep_some (hsome p hp)
  rw [hp2]
  exact (hs.2 a y hy).retype _

/-- What `memTyOK` says about a listed value. -/
theorem memTyOK_val {tabs : Tables} {f : Func} (hm : memTyOK tabs f = true) {b : ID}
    (hb : b ∈ f.blocks) {x : ID} (hx : x ∈ vals f b) {v : Value} (hv : f.value? x = some v) :
    memFree (tabs.ty v.type) = true ∨ memOpOK v.op = true ∨ memFreeOps.contains v.op = true := by
  unfold memTyOK at hm
  rw [Array.all_eq_true'] at hm
  have h1 := hm b hb
  rw [Array.all_eq_true'] at h1
  have h2 := h1 x hx
  rw [hv] at h2
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h2
  exact or_assoc.1 h2.2

/-- The shape `evalValue` gives a value of `f` whose type's shape holds no memory holds none. -/
theorem tys_memFree {tabs : Tables} {f : Func} {x : ID} {v : Value} (hv : f.value? x = some v)
    (hm : memFree (tabs.ty v.type) = true) :
    memFree ((Ctx.make tabs f).tys[x]?.getD .other) = true := by
  have hx : f.valueTab[x]? = some (some v) := by
    unfold Func.value? at hv
    exact Option.join_eq_some_iff.1 hv
  simp only [Ctx.make, Array.getElem?_map, hx, Option.map_some, Option.getD_some, valueTy,
    typeShapes, List.getElem?_toArray]
  by_cases hlt : v.type < tabs.types.size
  · rw [List.getElem?_range hlt]; exact hm
  · rw [List.getElem?_eq_none (by simpa using hlt)]; rfl

/-- One value of a listed block keeps the memories `P`. -/
theorem sinv_step (hP : MemPred P) {env : Env} (hE : ContractsOK P env) {ce : CheckEnv} {tabs : Tables} {f : Func}
    (hwf : WF ce f) (hm : memTyOK tabs f = true) {x : ID}
    (hx : ∃ b ∈ f.blocks, x ∈ vals f b) {fr : Frame} (hs : SInv P fr) {y : Val}
    (h : stepV env (Ctx.make tabs f) fr x = .ok y) : MemsOK P y := by
  obtain ⟨b, hb, hxb⟩ := hx
  obtain ⟨B, hB, -⟩ := hwf.blockId b hb
  have hxB : x ∈ B.values := by
    unfold vals at hxb; rw [hB] at hxb; exact hxb
  obtain ⟨v, hv, hvid, -⟩ := hwf.valueId b B ⟨hb, hB⟩ x hxB
  rw [stepV_eq (ctx := Ctx.make tabs f) hv] at h
  have hok := memTyOK_val hm hb hxb hv
  refine evalValue_mems hs.2 (fun argv ha r hr => ?_) h
  rcases hok with hfree | hop | hit
  · rw [hvid]; exact memsOK_of_mems_nil (retype_memFree _ (tys_memFree hv hfree) r)
  · exact (evalOp_mems hP hE hs.1 hop ha hr).retype _
  · exact (memsOK_of_mems_nil (evalOp_memFreeOps_mems hit hr)).retype _

theorem sinv_evalAll_aux (hP : MemPred P) {env : Env} (hE : ContractsOK P env) {ce : CheckEnv} {tabs : Tables}
    {f : Func} (hwf : WF ce f) (hm : WBCheck.memTyOK tabs f = true) :
    ∀ {o : List ID}, (∀ x ∈ o, ∃ b ∈ f.blocks, x ∈ WBCheck.vals f b) → ∀ {fr fr' : Frame},
      SInv P fr → evalAll env (Ctx.make tabs f) fr o = .ok fr' → SInv P fr'
  | [], _, fr, fr', hs, h => by cases h; exact hs
  | x :: o, ho, fr, fr', hs, h => by
    rw [evalAll_cons] at h
    cases hst : stepV env (Ctx.make tabs f) fr x with
    | ok y =>
      rw [hst] at h
      exact sinv_evalAll_aux hP hE hwf hm (fun z hz => ho z (List.mem_cons_of_mem _ hz))
        (hs.set (sinv_step hP hE hwf hm (ho x List.mem_cons_self) hs hst)) h
    | panic e m => rw [hst] at h; cases h
    | stuck msg => rw [hst] at h; cases h

/-- every value `o` lists is listed in a block of `f` -/
theorem sinv_evalAll (hP : MemPred P) {env : Env} (hE : ContractsOK P env) {ce : CheckEnv} {tabs : Tables} {f : Func}
    (hwf : WF ce f) (hm : WBCheck.memTyOK tabs f = true) {o : List ID}
    (ho : ∀ x ∈ o, ∃ b ∈ f.blocks, x ∈ WBCheck.vals f b) {fr fr' : Frame} (hs : SInv P fr)
    (h : evalAll env (Ctx.make tabs f) fr o = .ok fr') : SInv P fr' :=
  sinv_evalAll_aux hP hE hwf hm ho hs h

theorem sinv_enter (hP : MemPred P) {env : Env} (hE : ContractsOK P env) {ce : CheckEnv} {tabs : Tables} {f : Func}
    (hwf : WF ce f) (hm : WBCheck.memTyOK tabs f = true) {b : ID} {B : Block} (hb : b ∈ f.blocks)
    (hB : f.block? b = some B) {fr fr' : Frame} {i : Nat} (hs : SInv P fr)
    (h : enterBlock env (Ctx.make tabs f) fr B i = .ok fr') : SInv P fr' := by
  rw [enterBlock_eq] at h
  cases hps : B.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) with
  | panic e m => rw [hps] at h; cases h
  | stuck msg => rw [hps] at h; cases h
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ ((Ctx.make tabs f).sched[B.id]?).join).bind _ = _ at h
    cases ho : ((Ctx.make tabs f).sched[B.id]?).join with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      change evalAll env (Ctx.make tabs f) _ o.toList = .ok fr' at h
      have hnd := hwf.valuesNodup b B ⟨hb, hB⟩
      have hown := valuesOwn hwf hb hB
      obtain ⟨b', hb', hid⟩ := hwf.blockId b hb
      rw [hB] at hb'; cases hb'
      rw [hid, sched_of_block hB] at ho
      obtain ⟨-, -, omem⟩ := schedule_topo hown hnd ho
      refine sinv_evalAll hP hE hwf hm (fun x hx => ⟨b, hb, ?_⟩) (sinv_phis hs hps) h
      unfold vals; rw [hB]
      exact ((omem x).1 hx).1

/-! ## Invariants under a hypothesis -/

/-- `P` under a hypothesis `c` (a check of the function) is a memory invariant. -/
theorem MemPred.imp {c : Prop} (hP : MemPred P) : MemPred (fun m => c → P m) where
  write h hw := fun hc => hP.write (h hc) hw
  poison h hg hw := fun hc => hP.poison (h hc) hg hw
  poisonBelow n h hg hw := fun hc => hP.poisonBelow n (h hc) hg hw
  free_wbuf h := fun hc => hP.free_wbuf (h hc)
  rt a hb ha hw h := fun hc => hP.rt a hb ha hw (h hc)

theorem ContractsOK.imp {c : Prop} {env : Env} (h : c → ContractsOK P env) :
    ContractsOK (fun m => c → P m) env := by
  intro name e he args clo m ha hcl hm
  by_cases hc : c
  · have H := h hc name e he args clo m (fun a h' M hM => ha a h' M hM hc)
      (fun a h' M hM => hcl a h' M hM hc) (hm hc)
    cases hco : e args clo m with
    | returned rs m' =>
      rw [hco] at H
      exact ⟨fun _ => H.1, fun r hr M hM _ => H.2 r hr M hM⟩
    | panicked _ _ => trivial
    | stuck _ => trivial
  · cases e args clo m with
    | returned rs m' => exact ⟨fun h' => absurd h' hc, fun _ _ _ _ h' => absurd h' hc⟩
    | panicked _ _ => trivial
    | stuck _ => trivial

/-- Without the hypothesis, the invariant holds of every frame. -/
theorem SInv.of_not {c : Prop} (hc : ¬ c) (fr : Frame) : SInv (fun m => c → P m) fr :=
  ⟨fun h => absurd h hc, fun _ _ _ _ _ h => absurd h hc⟩

end GoFV.Proof.MemInv
