import GoFV.Proof.Pass.WBMem
import GoFV.Proof.Pass.DAEOps
import GoFV.Proof.Pass.DAERoot
import GoFV.Proof.Frame
import GoFV.Opt.WriteBarrierCheck

/-!
# writebarrier: the source's memories (issue #36)

Along a run of a function `f` that `WBCheck.memTyOK` accepts, every memory a register holds is
`MemOK` (`SInv`): the write-barrier flag stays defined and no write-barrier buffer appears, when
the initial memory is `MemOK` and the environment's contracts keep it (`ContractsOK`).

A register of a shape without memories holds none (`retype_memFree`); the values whose shape may
hold one are memory ops (`memOpOK`), whose results are built from their arguments' memories, by
writes and `poisonBlock`s of other blocks (`MemOK.write`, `MemOK.poison`), and by contracts
(`evalOp_mems`).
-/

namespace GoFV.SSA.Sem

mutual
/-- The memories inside a value (`GoFV.Proof.WB.MemsOK`). -/
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

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck

/-! ## The memories of a value -/

/-- Every memory inside `v` is `MemOK`. -/
def MemsOK (v : Val) : Prop := ∀ m ∈ v.mems, MemOK m

theorem memsL_mem {vs : List Val} {m : Mem} (h : m ∈ Val.memsL vs) : ∃ v ∈ vs, m ∈ v.mems := by
  induction vs with
  | nil => simp [Val.memsL] at h
  | cons v vs ih =>
    simp only [Val.memsL, List.mem_append] at h
    rcases h with h | h
    · exact ⟨v, List.mem_cons_self, h⟩
    · obtain ⟨w, hw, hm⟩ := ih h; exact ⟨w, List.mem_cons_of_mem _ hw, hm⟩

theorem memsOK_list {vs : List Val} (h : ∀ v ∈ vs, MemsOK v) : ∀ m ∈ Val.memsL vs, MemOK m :=
  fun m hm => by obtain ⟨v, hv, hm⟩ := memsL_mem hm; exact h v hv m hm

theorem memsOK_tuple {vs : List Val} (h : ∀ v ∈ vs, MemsOK v) : MemsOK (.tuple vs) :=
  memsOK_list h

theorem memsOK_of_mems_nil {v : Val} (h : v.mems = []) : MemsOK v := fun m hm => by
  rw [h] at hm; cases hm

theorem memsOK_getD {vs : List Val} (h : ∀ v ∈ vs, MemsOK v) (i : Nat) :
    MemsOK (vs.getD i .poison) := by
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

theorem memsOK_of_tuple {vs : List Val} (h : MemsOK (.tuple vs)) : ∀ v ∈ vs, MemsOK v :=
  fun _ hv _ hm => h _ (mem_memsL hv hm)

/-! ## Decoding and retyping -/

mutual
theorem decode_mems : (bs : Array Byte) → (off : Nat) → (t : Ty) → (decode bs off t).mems = []
  | bs, off, .int w => by
    simp only [decode, decodeInt]
    split
    · rfl
    · split <;> (try split) <;> rfl
  | bs, off, .bool => by simp only [decode]; split <;> (try split) <;> rfl
  | bs, off, .ptr _ => by simp only [decode, decodePtr]; split <;> (try split) <;> rfl
  | bs, off, .agg fs _ => by
    simp only [decode, Val.mems]; exact decodeFields_mems bs off fs
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
    | int w' => cases w' <;> simp [Val.retype, Val.mems] at hm; split at hm <;> simp [Val.mems] at hm
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

theorem MemsOK.retype {v : Val} (h : MemsOK v) (t : Ty) : MemsOK (v.retype t) :=
  fun m hm => h m (retype_mems t v m hm)

theorem memsOK_poison : MemsOK .poison := memsOK_of_mems_nil rfl

theorem memsOK_mem {m : Mem} (h : MemOK m) : MemsOK (.mem m) := fun m' hm' => by
  simp only [Val.mems, List.mem_singleton] at hm'; subst hm'; exact h

theorem MemsOK.mem {m : Mem} (h : MemsOK (.mem m)) : MemOK m := h m (by simp [Val.mems])

/-! ## Calls -/

/-- The environment's contracts keep memories `MemOK` and values `MemsOK`. -/
def ContractsOK (env : Env) : Prop :=
  ∀ name c, env.extern name = some c → ∀ args clo m, (∀ a ∈ args, MemsOK a) →
    (∀ a ∈ clo, MemsOK a) → MemOK m →
    match c args clo m with
    | .returned rs m' => MemOK m' ∧ ∀ r ∈ rs, MemsOK r
    | _ => True

theorem outargs_ne_flag (a : Nat) : Blk.outargs a ≠ flagBlk := by simp [flagBlk]

theorem decodeArgs_mems (tabs : Tables) (act : Nat) (m : Mem) :
    ∀ (ps : List ABIParam) {pieces args : List Val}, (∀ p ∈ pieces, MemsOK p) →
      decodeArgs tabs act m ps pieces = some args → ∀ a ∈ args, MemsOK a
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

theorem encodeResults_mems (tabs : Tables) (act : Nat) :
    ∀ (ps : List ABIParam) (rs : List Val) {m : Mem} {r : List Val × Mem},
      MemOK m → encodeResults tabs act ps rs m = some r → MemOK r.2 ∧ ∀ p ∈ r.1, MemsOK p
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
        exact encodeResults_mems tabs act ps xs (hm.write hw) he
    · cases hn : encodeResults tabs act ps xs m with
      | none => simp [hn, bind, Option.bind] at he
      | some q =>
        simp only [hn, bind, Option.bind, pure] at he
        cases he
        obtain ⟨h1, h2⟩ := encodeResults_mems tabs act ps xs hm hn
        refine ⟨h1, fun y hy => ?_⟩
        rcases List.mem_append.1 hy with hy | hy
        · simp only [toPieces, List.mem_map] at hy
          obtain ⟨_, -, rfl⟩ := hy
          exact memsOK_of_mems_nil (decode_mems _ _ _)
        · exact h2 y hy

theorem retypeResults_mems (tabs : Tables) :
    ∀ (ps : List ABIParam) (rs : List Val), (∀ r ∈ rs, MemsOK r) →
      ∀ x ∈ retypeResults tabs ps rs, MemsOK x
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

/-- **A call's result is `MemsOK`.** -/
theorem callOp_mems {env : Env} (hE : ContractsOK env) {ctx : Sem.Ctx} {v : Value}
    {argv : List Val} (ha : ∀ a ∈ argv, MemsOK a) {r : Val} (h : callOp env ctx v argv = .ok r) :
    MemsOK r := by
  unfold callOp at h
  have hsub := callTarget_sub ctx v argv
  generalize callTarget ctx v argv = T at h hsub
  obtain ⟨callee?, clo, rest⟩ := T
  obtain ⟨hclo, hrest⟩ := hsub
  dsimp only at h hclo hrest
  obtain ⟨callee, -, h⟩ := bind_ok_inv h
  have hR : ∀ a ∈ rest.dropLast, MemsOK a := fun a h' => ha a (hrest a (List.dropLast_subset _ h'))
  have hcl : ∀ a ∈ clo, MemsOK a := fun a h' => ha a (hclo a h')
  split at h
  rotate_left
  · cases h
  rename_i M hl
  have hM : MemOK M := (ha _ (hrest _ (List.mem_of_getLast? hl))).mem
  obtain ⟨M', hw, h⟩ := bind_ok_inv h
  have hM' : MemOK M' := by cases hw; exact hM
  have haddr : ∀ (ps : List ABIParam), MemsOK (Val.agg (ps.map fun p =>
      if p.regs.isEmpty = true then Val.ptr ⟨Blk.outargs ctx.act, BitVec.ofInt 64 p.offset⟩
      else Val.poison)) := by
    intro ps
    refine memsOK_list fun a ha => ?_
    simp only [List.mem_map] at ha
    obtain ⟨p, -, rfl⟩ := ha
    split <;> exact memsOK_of_mems_nil rfl
  split at h <;> obtain ⟨args, hargs, h⟩ := bind_ok_inv h
  all_goals
    have hA : ∀ a ∈ args, MemsOK a := by
      first
      | exact decodeArgs_mems _ _ _ _ hR (ofOption_ok hargs)
      | (cases hargs; exact hR)
    split at h
    · cases h
    obtain ⟨c, hc, h⟩ := bind_ok_inv h
    have hcc := hE callee c (ofOption_ok hc) args clo (M'.poisonBlock (.outargs ctx.act)) hA hcl
      (hM'.poison (outargs_ne_flag _) (by simp))
    cases hco : c args clo (M'.poisonBlock (.outargs ctx.act)) with
    | stuck msg => rw [hco] at h; cases h
    | panicked e m' => rw [hco] at h; cases h
    | returned rs m' =>
      rw [hco] at h hcc
      obtain ⟨hm', hrs⟩ := hcc
      dsimp only at h
      obtain ⟨x, hx, h⟩ := bind_ok_inv h
      obtain ⟨h1, h2⟩ := encodeResults_mems ctx.tabs ctx.act _ _ hm' (ofOption_ok hx)
      have hrs' : ∀ ps, ∀ x ∈ retypeResults ctx.tabs ps rs, MemsOK x :=
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

theorem load_mems (m : Mem) (t : Ty) (p : Ptr) : (m.load t p).mems = [] := by
  unfold Mem.load
  split
  · rfl
  · rfl
  · split
    · exact decode_mems _ _ _
    · rfl

theorem int2_mems (w : Width) (g : BitVec w.bits → BitVec w.bits → Val)
    (hg : ∀ x y, (g x y).mems = []) (l : List Val) : (Int.int2 w g l).mems = [] := by
  unfold Int.int2
  split
  · split
    · exact hg _ _
    · rfl
  · rfl

theorem frameBlk_ne (tabs : Tables) (act : Nat) (n : AuxRef) :
    frameBlk tabs act n ≠ flagBlk ∧ frameBlk tabs act n ≠ .wbuf := by
  unfold frameBlk; split <;> simp [flagBlk]

theorem MemOK.free_wbuf {m : Mem} (h : MemOK m) : MemOK (m.free .wbuf) := by
  obtain ⟨a, ha, hok⟩ := h.flag
  refine ⟨⟨a, ?_, hok⟩, ?_⟩
  · rw [free_eq_erase, TabsMod.erase_find (by rfl)]; exact ha
  · rw [free_eq_erase]; exact erase_find_wbuf m

/-- **A memory root's result** (any op `memRoot` evaluates). -/
theorem memRoot_mems {ctx : Sem.Ctx} {v : Value} {argv : List Val} (ha : ∀ a ∈ argv, MemsOK a)
    {r : Val} (h : memRoot ctx v argv = .ok r) : MemsOK r := by
  have wr : ∀ {what : String} {m : Mem} {o : Option Mem}, MemOK m →
      (∀ m', o = some m' → MemOK m') → writeRes what o = .ok r → MemsOK r := by
    intro what m o _ ho h
    unfold writeRes at h
    split at h
    · cases h; exact memsOK_mem (ho _ rfl)
    · cases h
  unfold memRoot at h
  split at h
  all_goals first
    | (cases h; exact memsOK_of_mems_nil rfl)
    | skip
  · rename_i p x m
    exact wr ((ha _ (by simp)).mem) (fun m' h' => ((ha _ (by simp)).mem).write h') h
  · rename_i p x m
    exact wr ((ha _ (by simp)).mem) (fun m' h' => ((ha _ (by simp)).mem).write h') h
  · rename_i d s m
    split at h
    · exact wr ((ha _ (by simp)).mem) (fun m' h' => ((ha _ (by simp)).mem).write h') h
    · cases h
  · rename_i d s m
    split at h
    · exact wr ((ha _ (by simp)).mem) (fun m' h' => ((ha _ (by simp)).mem).write h') h
    · cases h
  · rename_i p m
    exact wr ((ha _ (by simp)).mem) (fun m' h' => ((ha _ (by simp)).mem).write h') h
  · rename_i p m
    exact wr ((ha _ (by simp)).mem) (fun m' h' => ((ha _ (by simp)).mem).write h') h
  · rename_i m
    split at h
    · cases h
      exact memsOK_mem (((ha _ (by simp)).mem).poison (frameBlk_ne _ _ _).1 (frameBlk_ne _ _ _).2)
    · cases h
  · rename_i m; cases h; exact ha _ (by simp)
  · rename_i m; cases h; exact memsOK_mem ((ha _ (by simp)).mem).free_wbuf
  · rename_i x m; cases h; exact ha _ (by simp)
  · split at h
    · cases h
    · cases h; exact memsOK_of_mems_nil rfl
  · split at h
    · cases h
    · cases h; exact memsOK_of_mems_nil rfl
  · split at h <;> cases h

/-- **An atomic root's result.** -/
theorem atomicRoot_mems {v : Value} {argv : List Val} (ha : ∀ a ∈ argv, MemsOK a) {r : Val}
    (h : atomicRoot v argv = .ok r) : MemsOK r := by
  unfold atomicRoot at h
  split at h
  · rename_i a
    unfold Atomic.barrier at h
    split at h
    · split at h
      · cases h; exact ha _ (by simp)
      · cases h
    · cases h
  · rename_i _ a
    unfold Atomic.prefetch at h
    split at h
    · split at h
      · cases h; exact ha _ (by simp)
      · cases h
    · cases h
  · rename_i a b c
    unfold Atomic.rmwRoot at h
    split at h
    · rename_i p x m
      have hm : MemOK m := (ha _ (by simp)).mem
      split at h
      · rename_i k t _
        unfold Atomic.rmw at h
        split at h
        · split at h
          · rename_i m' hw
            cases h
            have hm' := hm.write hw
            unfold Atomic.result
            split
            · rename_i y hy
              refine memsOK_tuple fun z hz => ?_
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
              rcases hz with rfl | rfl
              · refine memsOK_of_mems_nil ?_
                cases k <;> simp only [Atomic.step, Option.some.injEq, reduceCtorEq] at hy <;>
                  (try subst hy) <;>
                  first
                  | exact load_mems _ _ _
                  | exact int2_mems _ _ (fun _ _ => rfl) _
              · exact memsOK_mem hm'
            · exact memsOK_mem hm'
          · cases h
        · cases h
      · cases h
    · cases h
  · rename_i a b c d
    unfold Atomic.casRoot at h
    split at h
    · rename_i p o n m
      have hm : MemOK m := (ha _ (by simp)).mem
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
                · exact memsOK_mem (hm.write hw)
              · cases h
            · cases h
              refine memsOK_tuple fun z hz => ?_
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
              rcases hz with rfl | rfl
              · exact memsOK_of_mems_nil rfl
              · exact memsOK_mem hm
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **A memory op's result** (`WBCheck.memOpOK`), from arguments and an initial memory whose
memories are `MemOK`. -/
theorem evalOp_mems {env : Env} (hE : ContractsOK env) {ctx : Sem.Ctx} {fr : Frame}
    (h0 : MemOK fr.mem0) {v : Value} (hop : memOpOK v.op = true) {argv : List Val}
    (ha : ∀ a ∈ argv, MemsOK a) {ty : Ty} {r : Val} (h : evalOp env ctx fr v argv ty = .ok r) :
    MemsOK r := by
  simp only [memOpOK, memOps, List.contains_cons, List.contains_nil, beq_iff_eq,
    Bool.or_eq_true, Bool.or_false, decide_eq_true_eq] at hop
  have pureL : v.op = .Copy ∨ v.op = .Select0 ∨ v.op = .Select1 ∨ v.op = .SelectN ∨
      v.op = .MakeResult ∨ v.op = .AtomicLoad32 ∨ v.op = .AtomicLoad64 ∨ v.op = .AtomicLoadPtr →
      MemsOK r := by
    intro hp
    rw [DAE.evalOp_pureOp (by rcases hp with h | h | h | h | h | h | h | h <;> simp [h])] at h
    cases h
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp <;> rw [hp]
    · show MemsOK (match argv with | [x] => x | _ => .poison)
      split
      · exact ha _ (by simp)
      · exact memsOK_poison
    · show MemsOK (Tuple.select 0 argv)
      unfold Tuple.select; split
      · exact memsOK_getD (memsOK_of_tuple (ha _ (by simp))) _
      · exact memsOK_poison
    · show MemsOK (Tuple.select 1 argv)
      unfold Tuple.select; split
      · exact memsOK_getD (memsOK_of_tuple (ha _ (by simp))) _
      · exact memsOK_poison
    · show MemsOK (Tuple.selectN v.auxInt argv)
      unfold Tuple.selectN; split
      · split
        · exact memsOK_poison
        · exact memsOK_getD (memsOK_of_tuple (ha _ (by simp))) _
      · exact memsOK_poison
    · exact memsOK_tuple ha
    all_goals
      show MemsOK (atomicLoad ty argv)
      unfold atomicLoad; split
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
  have rootL : v.op = .Store ∨ v.op = .Zero ∨ v.op = .Move ∨ v.op = .VarDef ∨ v.op = .VarLive ∨
      v.op = .KeepAlive → MemsOK r := by
    intro hp
    rw [DAE.evalOp_memRoot (by rcases hp with h | h | h | h | h | h <;> simp [h])] at h
    exact memRoot_mems ha h
  have callL : v.op = .StaticCall ∨ v.op = .ClosureCall ∨ v.op = .InterCall ∨
      v.op = .StaticLECall ∨ v.op = .ClosureLECall ∨ v.op = .InterLECall → MemsOK r := by
    intro hp
    have he : evalOp env ctx fr v argv ty = callOp env ctx v argv := by
      rcases hp with h | h | h | h | h | h <;> simp only [evalOp, h]
    rw [he] at h
    exact callOp_mems hE ha h
  have atomL : v.op = .AtomicStore32 ∨ v.op = .AtomicStore64 ∨ v.op = .AtomicAdd32 ∨
      v.op = .AtomicAdd32Variant ∨ v.op = .AtomicAdd64 ∨ v.op = .AtomicCompareAndSwap32 ∨
      v.op = .AtomicCompareAndSwap32Variant ∨ v.op = .AtomicCompareAndSwap64 ∨
      v.op = .AtomicCompareAndSwap64Variant → MemsOK r := by
    intro hp
    rw [DAE.evalOp_atomic hp] at h
    exact atomicRoot_mems ha h
  rcases hop with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  · simp only [evalOp, hp] at h; cases h; exact memsOK_mem h0
  · -- Phi: not evaluated by `evalOp` in a schedule, but `evalOp` gives it `evalPure`
    rw [DAE.evalOp_pure2 (.inl hp)] at h
    cases h; rw [hp]; exact memsOK_poison
  · exact pureL (.inl hp)
  · exact pureL (.inr (.inl hp))
  · exact pureL (.inr (.inr (.inl hp)))
  · exact pureL (.inr (.inr (.inr (.inl hp))))
  · exact pureL (.inr (.inr (.inr (.inr (.inl hp)))))
  · exact rootL (.inl hp)
  · exact rootL (.inr (.inr (.inl hp)))
  · exact rootL (.inr (.inl hp))
  · exact rootL (.inr (.inr (.inr (.inl hp))))
  · exact rootL (.inr (.inr (.inr (.inr (.inl hp)))))
  · exact rootL (.inr (.inr (.inr (.inr (.inr hp)))))
  · rw [DAE.evalOp_panicBounds hp] at h; exact absurd h panicBounds_not_ok
  · exact callL (.inl hp)
  · exact callL (.inr (.inl hp))
  · exact callL (.inr (.inr (.inl hp)))
  · exact callL (.inr (.inr (.inr (.inl hp))))
  · exact callL (.inr (.inr (.inr (.inr (.inl hp)))))
  · exact callL (.inr (.inr (.inr (.inr (.inr hp)))))
  · exact pureL (.inr (.inr (.inr (.inr (.inr (.inl hp))))))
  · exact pureL (.inr (.inr (.inr (.inr (.inr (.inr (.inl hp)))))))
  · exact pureL (.inr (.inr (.inr (.inr (.inr (.inr (.inr hp)))))))
  · exact atomL (.inl hp)
  · exact atomL (.inr (.inl hp))
  · exact atomL (.inr (.inr (.inl hp)))
  · exact atomL (.inr (.inr (.inr (.inl hp))))
  · exact atomL (.inr (.inr (.inr (.inr (.inl hp)))))
  · exact atomL (.inr (.inr (.inr (.inr (.inr (.inl hp))))))
  · exact atomL (.inr (.inr (.inr (.inr (.inr (.inr (.inl hp)))))))
  · exact atomL (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl hp))))))))
  · exact atomL (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr hp))))))))

end GoFV.Proof.WB
