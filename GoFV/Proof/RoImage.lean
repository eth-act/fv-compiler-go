import GoFV.Proof.Pass.WBMem
import GoFV.SSA.Sem.Runtime

/-!
# Read-only symbols hold their exported bytes (#151)

`generic.rules:1743` turns a `Move` from a read-only symbol whose exported bytes are all zero
(`symIsROZero`) into a `Zero`. Nothing in the semantics ties a global's allocation in the run's
memory to its `LSym` data: `addGlobals` only adds the image's allocations a memory lacks, and a
contract may return any memory. The precondition `RoImage ro env mem`:

* `RoMem ro`: the read-only symbols `ro` (name and allocation; the rewrite passes take the
  `SRODATA` symbols their input's `Addr`s name, `RewriteCheck.roSyms`, with the allocation of the
  global image, `Sem.rodataAlloc`) are read-only allocations of the memory with the global image;
* `Env.KeepsRo`: every contract keeps the read-only global allocations it is given and returns
  no memory.

Writes need a writable allocation, frame allocations and `poisonBlock`s are of other blocks, so
`RoMem ro` is a memory invariant (`roMem_pred`) that the contracts keep (`Env.KeepsRo.contractsOK`):
every memory a run of the source holds has the symbols (`MemInv.SInv`). The runtime's contracts
only write and allocate heap blocks (`Env.runtime_keepsRo`).
-/

namespace GoFV.SSA.Sem

open GoFV.Proof

/-- The read-only symbols `ro` are read-only allocations of `m`. -/
def RoMem (ro : List (String × Alloc)) (m : Mem) : Prop :=
  ∀ n a, (n, a) ∈ ro → a.writable = false ∧ m.find? (.global n) = some a

/-- `m'` keeps the read-only global allocations of `m`. -/
def Mem.KeepsRo (m m' : Mem) : Prop :=
  ∀ n a, m.find? (.global n) = some a → a.writable = false → m'.find? (.global n) = some a

/-- A contract keeps the read-only global allocations and returns no memory. -/
def Contract.KeepsRo (c : Contract) : Prop :=
  ∀ args clo m rs m', c args clo m = .returned rs m' → m.KeepsRo m' ∧ ∀ r ∈ rs, r.mems = []

/-- Every contract of the environment keeps the read-only global allocations. -/
def Env.KeepsRo (env : Env) : Prop := ∀ name c, env.extern name = some c → c.KeepsRo

/-- **The read-only image precondition**: the contracts keep read-only global allocations, and
the read-only symbols `ro` are read-only allocations of the memory with the global image. -/
def RoImage (ro : List (String × Alloc)) (env : Env) (mem : Mem) : Prop :=
  env.KeepsRo ∧ RoMem ro (addGlobals env mem)

theorem Mem.KeepsRo.refl (m : Mem) : m.KeepsRo m := fun _ _ h _ => h

theorem Mem.KeepsRo.trans {m1 m2 m3 : Mem} (h1 : m1.KeepsRo m2) (h2 : m2.KeepsRo m3) :
    m1.KeepsRo m3 := fun n a h hw => h2 n a (h1 n a h hw) hw

theorem RoMem.keep {ro : List (String × Alloc)} {m m' : Mem} (h : RoMem ro m)
    (hk : m.KeepsRo m') : RoMem ro m' := fun n a hm => by
  obtain ⟨hw, hf⟩ := h n a hm
  exact ⟨hw, hk n a hf hw⟩

theorem RoMem.nil (m : Mem) : RoMem [] m := fun _ _ h => absurd h List.not_mem_nil

/-- **A write keeps the read-only allocations.** -/
theorem Mem.keepsRo_write {m m' : Mem} {p : Ptr} {bs : Array Byte} (hw : m.write p bs = some m') :
    m.KeepsRo m' := by
  intro n a ha hro
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ↓reduceIte] at hw; cases hw; exact ha
  · simp only [he, Bool.false_eq_true, ↓reduceIte] at hw
    cases hb : m.find? p.blk with
    | none => rw [hb] at hw; cases hw
    | some a0 =>
      rw [hb] at hw
      dsimp only [bind, Option.bind] at hw
      split at hw
      · rename_i hc
        cases hw
        rw [CSE.Mem.find?_set]
        split
        · rename_i heq
          rw [heq, ha] at hb
          cases hb
          simp [hro] at hc
        · exact ha
      · cases hw

/-- Setting a block that is no global keeps the globals. -/
theorem Mem.keepsRo_set {m : Mem} {b : Blk} (hg : ∀ n, b ≠ .global n) (a : Alloc) :
    m.KeepsRo (m.set b a) := by
  intro n a' ha _
  rw [CSE.Mem.find?_set, if_neg (hg n)]
  exact ha

/-- A fresh heap allocation keeps the globals. -/
theorem Mem.keepsRo_allocHeap (m : Mem) (data : Array Byte) : m.KeepsRo (m.allocHeap data).2 :=
  Mem.keepsRo_set (b := .heap m.nextHeap) (fun _ h => by cases h) _

/-- **`RoMem ro` is a memory invariant.** -/
theorem roMem_pred (ro : List (String × Alloc)) : MemInv.MemPred (RoMem ro) where
  write h hw := h.keep (Mem.keepsRo_write hw)
  set a h hg _ := h.keep (Mem.keepsRo_set hg a)
  free_wbuf h := fun n a hm => by
    obtain ⟨hw, hf⟩ := h n a hm
    refine ⟨hw, ?_⟩
    rw [WB.free_eq_erase, TabsMod.erase_find (by simp [WB.isW])]
    exact hf

/-- **Contracts that keep the read-only allocations keep `RoMem ro`.** -/
theorem Env.KeepsRo.contractsOK {env : Env} (h : env.KeepsRo) (ro : List (String × Alloc)) :
    MemInv.ContractsOK (RoMem ro) env := by
  intro name c hc args clo m _ _ hm
  cases hco : c args clo m with
  | returned rs m' =>
    obtain ⟨hk, hrs⟩ := h name c hc args clo m rs m' hco
    exact ⟨hm.keep hk, fun r hr => MemInv.memsOK_of_mems_nil (hrs r hr)⟩
  | panicked e m' => trivial
  | stuck msg => trivial

/-! ## The runtime's contracts -/

namespace Runtime

theorem alloc_keepsRo {m : Mem} {n : Nat} {a : Ptr × Mem} (h : alloc m n = some a) :
    m.KeepsRo a.2 := by
  unfold alloc at h
  split at h
  · cases h; exact Mem.KeepsRo.refl _
  · split at h
    · cases h
    · cases h; exact Mem.keepsRo_allocHeap _ _

theorem allocBytes_keepsRo {m : Mem} {bs : Array Byte} {a : Ptr × Mem}
    (h : allocBytes m bs = some a) : m.KeepsRo a.2 := by
  unfold allocBytes at h
  split at h
  · cases h; exact Mem.KeepsRo.refl _
  · split at h
    · cases h
    · cases h; exact Mem.keepsRo_allocHeap _ _

theorem newString_keepsRo {m : Mem} {bs : Array Byte} {a : Val × Mem}
    (h : newString m bs = some a) : m.KeepsRo a.2 ∧ a.1.mems = [] := by
  unfold newString at h
  split at h
  · cases h; exact ⟨Mem.KeepsRo.refl _, rfl⟩
  · simp only [bind, Option.bind_eq_some_iff, pure] at h
    obtain ⟨b, ha, h⟩ := h
    cases h
    exact ⟨allocBytes_keepsRo ha, rfl⟩

theorem sliceVal_mems (p : Ptr) (len cap : Nat) : (sliceVal p len cap).mems = [] := rfl

theorem strVal_mems (p : Ptr) (n : Nat) : (strVal p n).mems = [] := rfl

/-- An `ok?` contract keeps the read-only allocations if its result does. -/
theorem ok?_keepsRo {name : String} {o : Option (List Val × Mem)} {m : Mem} {rs : List Val}
    {m' : Mem} (hr : ok? name o = .returned rs m')
    (h : ∀ a, o = some a → m.KeepsRo a.2 ∧ ∀ r ∈ a.1, r.mems = []) :
    m.KeepsRo m' ∧ ∀ r ∈ rs, r.mems = [] := by
  cases o with
  | none => cases hr
  | some a => cases hr; exact h _ rfl

theorem panics_keepsRo (e : Panic) : (panics e).KeepsRo := by
  intro _ _ _ _ _ h; cases h

theorem noEffect_keepsRo : noEffect.KeepsRo := by
  intro _ _ _ _ _ h; cases h; exact ⟨Mem.KeepsRo.refl _, by simp⟩

theorem newobject_keepsRo : newobject.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨_, -, _, -, b, hal, ho⟩ := ho
    cases ho
    exact ⟨alloc_keepsRo hal, by simp [Val.mems]⟩

theorem mallocSized_keepsRo : mallocSized.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _, _], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨_, -, b, hal, ho⟩ := ho
    cases ho
    exact ⟨alloc_keepsRo hal, by simp [Val.mems]⟩

theorem makeslice_keepsRo : makeslice.KeepsRo := by
  intro args clo m rs m' hr
  unfold makeslice at hr
  split at hr
  · split at hr
    · split at hr
      · cases hr
      · dsimp only at hr
        split at hr
        · split at hr <;> cases hr
        · refine ok?_keepsRo hr fun a ho => ?_
          simp only [bind, Option.bind_eq_some_iff, pure] at ho
          obtain ⟨b, hal, ho⟩ := ho
          cases ho
          exact ⟨alloc_keepsRo hal, by simp [Val.mems]⟩
    · cases hr
  · cases hr

theorem growslice_keepsRo : growslice.KeepsRo := by
  intro args clo m rs m' hr
  unfold growslice at hr
  split at hr
  · split at hr
    · split at hr
      · cases hr
      · dsimp only at hr
        split at hr
        · cases hr
        · split at hr
          · cases hr; exact ⟨Mem.KeepsRo.refl _, by simp [sliceVal_mems]⟩
          · split at hr
            · cases hr
            · refine ok?_keepsRo hr fun a ho => ?_
              simp only [bind, Option.bind_eq_some_iff, pure] at ho
              obtain ⟨b, hal, bs, -, m2, hw, ho⟩ := ho
              cases ho
              exact ⟨(alloc_keepsRo hal).trans (Mem.keepsRo_write hw), by simp [sliceVal_mems]⟩
    · cases hr
  · cases hr

/-- `growsliceBuf`'s tail: the zeroed capacity. -/
private theorem growsliceBuf_tail {m1 : Mem} {c : Prop} [Decidable c] {p : Ptr} {bs : Array Byte}
    {v : Val} {a : List Val × Mem}
    (h : (if c then (m1.write p bs).bind fun m => some ([v], m) else (some m1).bind
      fun m => some ([v], m)) = some a) : m1.KeepsRo a.2 ∧ a.1 = [v] := by
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨m2, hw, h⟩ := h
    cases h
    exact ⟨Mem.keepsRo_write hw, rfl⟩
  · cases h; exact ⟨Mem.KeepsRo.refl _, rfl⟩

theorem growsliceBuf_keepsRo : growsliceBuf.KeepsRo := by
  intro args clo m rs m' hr
  unfold growsliceBuf at hr
  split at hr
  · split at hr
    · split at hr
      · exact growslice_keepsRo _ _ _ _ _ hr
      · split at hr
        · cases hr
        · split at hr
          · cases hr
          · refine ok?_keepsRo hr fun a ho => ?_
            simp only [bind, pure] at ho
            split at ho
            · simp only [Option.bind_eq_some_iff] at ho
              obtain ⟨bs, -, m1, hw, ho⟩ := ho
              obtain ⟨hk, hrs⟩ := growsliceBuf_tail ho
              exact ⟨(Mem.keepsRo_write hw).trans hk, by simp [hrs, sliceVal_mems]⟩
            · obtain ⟨hk, hrs⟩ := growsliceBuf_tail (m1 := m) ho
              exact ⟨hk, by simp [hrs, sliceVal_mems]⟩
    · cases hr
  · cases hr

theorem moveSlice_keepsRo (noScan : Bool) : (moveSlice noScan).KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _, _, _], ho =>
    simp only [bind, pure] at ho
    split at ho <;> simp only [Option.bind_eq_some_iff] at ho
    case isTrue =>
      obtain ⟨size, -, o, -, l, -, cap, -, ho⟩ := ho
      split at ho
      · cases ho; exact ⟨Mem.KeepsRo.refl _, by simp [sliceVal_mems]⟩
      · simp only [Option.bind_eq_some_iff] at ho
        obtain ⟨bs, -, b, hal, ho⟩ := ho
        cases ho
        exact ⟨allocBytes_keepsRo hal, by simp [sliceVal_mems]⟩
    case isFalse =>
      obtain ⟨_, -, size, -, o, -, l, -, cap, -, ho⟩ := ho
      split at ho
      · cases ho; exact ⟨Mem.KeepsRo.refl _, by simp [sliceVal_mems]⟩
      · simp only [Option.bind_eq_some_iff] at ho
        obtain ⟨bs, -, b, hal, ho⟩ := ho
        cases ho
        exact ⟨allocBytes_keepsRo hal, by simp [sliceVal_mems]⟩

theorem moveSliceNoCap_keepsRo (noScan : Bool) : (moveSliceNoCap noScan).KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _, _], ho =>
    simp only [bind, pure] at ho
    split at ho <;> simp only [Option.bind_eq_some_iff] at ho
    case isTrue =>
      obtain ⟨sp, -, o, -, l, -, ho⟩ := ho
      split at ho
      · cases ho; exact ⟨Mem.KeepsRo.refl _, by simp [sliceVal_mems]⟩
      · simp only [Option.bind_eq_some_iff] at ho
        obtain ⟨b, hal, bs, -, m2, hw, ho⟩ := ho
        cases ho
        exact ⟨(alloc_keepsRo hal).trans (Mem.keepsRo_write hw), by simp [sliceVal_mems]⟩
    case isFalse =>
      obtain ⟨_, -, sp, -, o, -, l, -, ho⟩ := ho
      split at ho
      · cases ho; exact ⟨Mem.KeepsRo.refl _, by simp [sliceVal_mems]⟩
      · simp only [Option.bind_eq_some_iff] at ho
        obtain ⟨b, hal, bs, -, m2, hw, ho⟩ := ho
        cases ho
        exact ⟨(alloc_keepsRo hal).trans (Mem.keepsRo_write hw), by simp [sliceVal_mems]⟩

theorem memmove_keepsRo : memmove.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _, _], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨_, -, _, -, bs, -, _, -, m1, hw, ho⟩ := ho
    cases ho
    exact ⟨Mem.keepsRo_write hw, by simp⟩

theorem memclr_keepsRo : memclr.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨_, -, _, -, m1, hw, ho⟩ := ho
    cases ho
    exact ⟨Mem.keepsRo_write hw, by simp⟩

theorem typedmemmove_keepsRo : typedmemmove.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _, _], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨_, -, _, -, _, -, bs, -, _, -, m1, hw, ho⟩ := ho
    cases ho
    exact ⟨Mem.keepsRo_write hw, by simp⟩

theorem typedslicecopy_keepsRo : typedslicecopy.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _, _, _, _], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨_, -, _, -, _, -, _, -, _, -, bs, -, _, -, m1, hw, ho⟩ := ho
    cases ho
    exact ⟨Mem.keepsRo_write hw, by simp [Val.mems]⟩

theorem memequal_keepsRo : memequal.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _, _], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨_, -, _, -, x, -, _, -, y, -, ho⟩ := ho
    split at ho
    · cases ho
    · cases ho
      exact ⟨Mem.KeepsRo.refl _, by simp [Val.mems]⟩

theorem convT_keepsRo (t : Ty) : (convT t).KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨b, hal, ho⟩ := ho
    cases ho
    exact ⟨allocBytes_keepsRo hal, by simp [Val.mems]⟩

theorem convTtyp_keepsRo : convTtyp.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨_, -, _, -, _, -, bs, -, b, hal, ho⟩ := ho
    cases ho
    exact ⟨allocBytes_keepsRo hal, by simp [Val.mems]⟩

theorem concatstringN_keepsRo : concatstringN.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | _ :: _, ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨bs, -, b, hn, ho⟩ := ho
    cases ho
    obtain ⟨hk, hs⟩ := newString_keepsRo hn
    exact ⟨hk, by simp [hs]⟩

theorem concatstrings_keepsRo : concatstrings.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, .agg [_, _, _]], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨_, -, _, -, bs, -, b, hn, ho⟩ := ho
    cases ho
    obtain ⟨hk, hs⟩ := newString_keepsRo hn
    exact ⟨hk, by simp [hs]⟩

theorem slicebytetostring_keepsRo : slicebytetostring.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _, _], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨_, -, _, -, bs, -, b, hn, ho⟩ := ho
    cases ho
    obtain ⟨hk, hs⟩ := newString_keepsRo hn
    exact ⟨hk, by simp [hs]⟩

theorem stringtoslicebyte_keepsRo : stringtoslicebyte.KeepsRo := by
  intro args clo m rs m' hr
  refine ok?_keepsRo hr fun a ho => ?_
  match args, ho with
  | [_, _], ho =>
    simp only [bind, Option.bind_eq_some_iff, pure] at ho
    obtain ⟨bs, -, _, -, ho⟩ := ho
    split at ho
    · simp only [Option.bind_eq_some_iff] at ho
      obtain ⟨m1, hw, ho⟩ := ho
      cases ho
      exact ⟨Mem.keepsRo_write hw, by simp [sliceVal_mems]⟩
    · simp only [Option.bind_eq_some_iff] at ho
      obtain ⟨b, hal, m2, hw, ho⟩ := ho
      cases ho
      exact ⟨(alloc_keepsRo hal).trans (Mem.keepsRo_write hw), by simp [sliceVal_mems]⟩

end Runtime

open Runtime in
/-- **The runtime's contracts keep the read-only allocations**: they only write (which needs a
writable allocation) and allocate heap blocks. -/
theorem Env.runtime_keepsRo : Env.runtime.KeepsRo := by
  intro name c hc
  simp only [Env.runtime] at hc
  split at hc
  all_goals first
    | (cases hc; first
        | exact panics_keepsRo _ | exact noEffect_keepsRo | exact newobject_keepsRo
        | exact makeslice_keepsRo | exact growslice_keepsRo | exact growsliceBuf_keepsRo
        | exact moveSlice_keepsRo _ | exact moveSliceNoCap_keepsRo _ | exact memmove_keepsRo
        | exact memclr_keepsRo | exact typedmemmove_keepsRo | exact typedslicecopy_keepsRo
        | exact memequal_keepsRo | exact convT_keepsRo _ | exact convTtyp_keepsRo
        | exact concatstringN_keepsRo | exact concatstrings_keepsRo
        | exact slicebytetostring_keepsRo | exact stringtoslicebyte_keepsRo)
    | (split at hc
       · cases hc; exact mallocSized_keepsRo
       · split at hc
         · cases hc; exact panics_keepsRo _
         · cases hc)

/-- `Env.p1`'s contracts only panic. -/
theorem Env.p1_keepsRo : Env.p1.KeepsRo := by
  intro name c hc
  simp only [Env.p1] at hc
  split at hc <;> first | (cases hc; exact Runtime.panics_keepsRo _) | cases hc
  all_goals intro _ _ _ _ _ h; cases h

theorem RoImage.sub {ro ro' : List (String × Alloc)} {env : Env} {mem : Mem}
    (h : RoImage ro env mem) (hs : ∀ e ∈ ro', e ∈ ro) : RoImage ro' env mem :=
  ⟨h.1, fun n a hm => h.2 n a (hs _ hm)⟩

/-- `RoImage` without read-only symbols: contracts that keep them. -/
theorem RoImage.nil {env : Env} (h : env.KeepsRo) (mem : Mem) : RoImage [] env mem :=
  ⟨h, RoMem.nil _⟩

end GoFV.SSA.Sem
