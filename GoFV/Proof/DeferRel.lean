import GoFV.Proof.Pass.DAEAvoid
import GoFV.Proof.Refine

/-!
# Deferred calls under memory relations that hide frame temporaries

`MemRel U R`: a relation `R` on memories that the memory operations of the panic machinery keep
when they touch no block of `U`, a set of frame temporaries (`DAE.TempU`): `Mem.EqOff U` (dead
auto elim) and equality once the blocks of `X` are erased (`tabsAgreeMod`). `Respects U R c`:
contract `c`, given arguments, closure context and a memory that avoid `U`, behaves alike on
`R`-related memories and returns or panics with nothing pointing into `U`
(`Contract.FrameSafe` and `Contract.TempOblivious` are its instances). The runtime entry points
`Env.atAct` adds (`deferproc`, `deferprocStack`, `deferreturn`, `gorecover`) respect `U` and `R`
when the environment's contracts do (`atAct_respects`), and so does the panic case of `finish`
(`runDefers`, `finish_panicked_refines`) when the open-coded defer variables of the activation
are outside `U` (`DeferAvoid`).
-/

namespace GoFV.Proof.DeferRel

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.DAE

variable {U : Blk → Prop} {R : Mem → Mem → Prop}

/-- Related contract outcomes: the source returning or panicking avoids `U`, the target does the
same with an `R`-related memory. -/
def CRel (U : Blk → Prop) (R : Mem → Mem → Prop) : COutcome → COutcome → Prop
  | .stuck _, _ => True
  | .returned rs r, .returned rs' r' => rs' = rs ∧ (∀ v ∈ rs, v.Avoids U) ∧ r.Avoids U ∧ R r r'
  | .panicked e r, .panicked e' r' => e' = e ∧ e.Avoids U ∧ r.Avoids U ∧ R r r'
  | _, _ => False

/-- A contract cannot observe or leak the blocks `U` it is given no pointer to, on memories
related by `R`. -/
def Respects (U : Blk → Prop) (R : Mem → Mem → Prop) (c : Contract) : Prop :=
  ∀ args clo m m', (∀ v ∈ args, v.Avoids U) → (∀ v ∈ clo, v.Avoids U) → m.Avoids U → R m m' →
    CRel U R (c args clo m) (c args clo m')

/-- Memory relations the panic machinery keeps (see the module comment). -/
structure MemRel (U : Blk → Prop) (R : Mem → Mem → Prop) : Prop where
  refl : ∀ m, R m m
  find : ∀ {m m' : Mem}, R m m' → ∀ b, ¬ U b → m'.find? b = m.find? b
  set : ∀ {m m' : Mem}, R m m' → ∀ b a, ¬ U b → R (m.set b a) (m'.set b a)
  write : ∀ {m m' m1 : Mem} {p : Ptr} {bs : Array Byte}, R m m' → ¬ U p.blk →
    m.write p bs = some m1 → ∃ m1', m'.write p bs = some m1' ∧ R m1 m1'
  poison : ∀ {m m' : Mem}, R m m' → ∀ b, R (m.poisonBlock b) (m'.poisonBlock b)
  filter : ∀ {m m' : Mem}, R m m' → ∀ F : Blk × Alloc → Bool, (∀ b a a', F (b, a) = F (b, a')) →
    R { m with blocks := m.blocks.filter F } { m' with blocks := m'.blocks.filter F }
  nextAct : ∀ {m m' : Mem}, R m m' → m'.nextAct = m.nextAct

/-- The open-coded defer variables of activation `act` (`nextDefer`) are outside `U`. -/
def DeferAvoid (U : Blk → Prop) (di : DeferInfo) (act : Nat) : Prop :=
  (∀ nb, di.bits = some nb → ¬ U (if nb.2 then .local act nb.1 else .temp act nb.1)) ∧
  ∀ (i : Nat) sn, di.slots[i]? = some (some sn) →
    ¬ U (if sn.2 then .local act sn.1 else .temp act sn.1)

/-! ## Contract instances -/

theorem crel_of_match {o o' : COutcome}
    (h : match o, o' with
      | .stuck _, _ => True
      | .returned rs r, .returned rs' r' =>
        rs' = rs ∧ (∀ v ∈ rs, v.Avoids U) ∧ r.Avoids U ∧ R r r'
      | .panicked e r, .panicked e' r' => e' = e ∧ e.Avoids U ∧ r.Avoids U ∧ R r r'
      | _, _ => False) : CRel U R o o' := by
  cases o <;> cases o' <;> exact h

theorem match_of_crel {o o' : COutcome} : CRel U R o o' →
    match o, o' with
      | .stuck _, _ => True
      | .returned rs r, .returned rs' r' =>
        rs' = rs ∧ (∀ v ∈ rs, v.Avoids U) ∧ r.Avoids U ∧ R r r'
      | .panicked e r, .panicked e' r' => e' = e ∧ e.Avoids U ∧ r.Avoids U ∧ R r r'
      | _, _ => False := by
  cases o <;> cases o' <;> exact id

theorem respects_of_frameSafe {c : Contract} (h : c.FrameSafe) (hU : TempU U) :
    Respects U (Mem.EqOff U) c :=
  fun args clo m m' ha hc hm hmm => crel_of_match (h U hU args clo m m' ha hc hm hmm)

theorem frameSafe_of_respects {c : Contract} (h : ∀ U, TempU U → Respects U (Mem.EqOff U) c) :
    c.FrameSafe :=
  fun U hU args clo m m' ha hc hm hmm => match_of_crel (h U hU args clo m m' ha hc hm hmm)

theorem respects_of_tempOblivious {c : Contract} (h : c.TempOblivious) {X : Blk → Bool}
    (hX : ∀ b, X b = true → ∃ a n, b = .temp a n) :
    Respects (X · = true) (fun m m' => m.erase X = m'.erase X) c :=
  fun args clo m m' ha hc hm hmm => crel_of_match (h X hX args clo m m' ha hc hm hmm)

theorem tempOblivious_of_respects {c : Contract}
    (h : ∀ X : Blk → Bool, (∀ b, X b = true → ∃ a n, b = .temp a n) →
      Respects (X · = true) (fun m m' => m.erase X = m'.erase X) c) : c.TempOblivious :=
  fun X hX args clo m m' ha hc hm hmm => match_of_crel (h X hX args clo m m' ha hc hm hmm)

/-! ## Memory facts -/

section
variable (hR : MemRel U R)
include hR

theorem MemRel.read {m m' : Mem} (h : R m m') (p : Ptr) (n : Nat) (hu : ¬ U p.blk) :
    m'.read p n = m.read p n := by
  unfold Mem.read; rw [hR.find h p.blk hu]

theorem MemRel.load {m m' : Mem} (h : R m m') (t : Ty) (p : Ptr) (hu : ¬ U p.blk) :
    m'.load t p = m.load t p := by
  unfold Mem.load; simp only [hR.read h p _ hu]

theorem MemRel.free {m m' : Mem} (h : R m m') (b : Blk) : R (m.free b) (m'.free b) :=
  hR.filter h _ fun _ _ _ => rfl

theorem MemRel.dropFrames {m m' : Mem} (h : R m m') (k : Nat) :
    R (m.dropFrames k) (m'.dropFrames k) :=
  hR.filter h _ fun _ _ _ => rfl

end

theorem memAvoids_filter {m : Mem} (h : m.Avoids U) (F : Blk × Alloc → Bool) :
    ({ m with blocks := m.blocks.filter F } : Mem).Avoids U := by
  intro b a hm
  simp only [Array.toList_filter, List.mem_filter] at hm
  exact h b a hm.1

theorem memAvoids_dropFrames {m : Mem} (h : m.Avoids U) (k : Nat) : (m.dropFrames k).Avoids U :=
  memAvoids_filter h _

theorem global_notU (hU : TempU U) (s : String) : ¬ U (.global s) := by
  intro hu; obtain ⟨_, _, h⟩ := hU _ hu; cases h

theorem nil_notU (hU : TempU U) : ¬ U .nil := by
  intro hu; obtain ⟨_, _, h⟩ := hU _ hu; cases h

theorem local_notU (hU : TempU U) (a n : Nat) : ¬ U (.local a n) := by
  intro hu; obtain ⟨_, _, h⟩ := hU _ hu; cases h

theorem bav_append {a b : Array Byte} (ha : BAv U a) (hb : BAv U b) : BAv U (a ++ b) := by
  intro x hx
  simp only [Array.toList_append, List.mem_append] at hx
  rcases hx with hx | hx
  · exact ha x hx
  · exact hb x hx

/-! ## The defer list and the panic record -/

theorem deferEntries_eq (hR : MemRel U R) (hU : TempU U) {m m' : Mem} (h : R m m') :
    deferEntries m' = deferEntries m := by
  unfold deferEntries; rw [hR.find h deferBlk (global_notU hU _)]

theorem deferEntries_avoids (hU : TempU U) {m : Mem} (hm : m.Avoids U) :
    ∀ e ∈ deferEntries m, e.1.Avoids U ∧ e.2.Avoids U := by
  unfold deferEntries
  split
  · rename_i a ha
    intro e he
    simp only [List.mem_map] at he
    obtain ⟨i, -, rfl⟩ := he
    have hb := memAvoids_find hm ha (global_notU hU _)
    exact ⟨decode_avoids hU hb _ _, decode_avoids hU hb _ _⟩
  · intro e he; cases he

theorem setDeferEntries_avoids {m : Mem} (hm : m.Avoids U) {es : List (Val × Val)}
    (hes : ∀ e ∈ es, e.1.Avoids U ∧ e.2.Avoids U) : (setDeferEntries m es).Avoids U := by
  unfold setDeferEntries
  refine memAvoids_set hm fun _ => ?_
  have key : ∀ (l : List (Array Byte)) (acc : Array Byte), BAv U acc → (∀ x ∈ l, BAv U x) →
      BAv U (l.foldl (· ++ ·) acc) := by
    intro l
    induction l with
    | nil => intro acc h _; exact h
    | cons x l ih =>
      intro acc h hl
      exact ih _ (bav_append h (hl x List.mem_cons_self)) fun y hy => hl y (List.mem_cons_of_mem _ hy)
  refine key _ _ (fun x hx => by simp at hx) fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨⟨a, c⟩, he, rfl⟩ := hx
  exact encode_avoids _ (show Val.AvoidsList U [a, c] from ⟨(hes _ he).1, (hes _ he).2, trivial⟩)

theorem setDeferEntries_rel (hR : MemRel U R) (hU : TempU U) {m m' : Mem} (h : R m m')
    (es : List (Val × Val)) : R (setDeferEntries m es) (setDeferEntries m' es) :=
  hR.set h _ _ (global_notU hU _)

theorem pushDefer_avoids (hU : TempU U) {m : Mem} (hm : m.Avoids U) (act : Nat) {clo : Val}
    (hc : clo.Avoids U) : (pushDefer act clo m).Avoids U := by
  refine setDeferEntries_avoids hm fun e he => ?_
  rcases List.mem_append.1 he with he | he
  · exact deferEntries_avoids hU hm e he
  · simp only [List.mem_singleton] at he; subst he; exact ⟨trivial, hc⟩

theorem pushDefer_rel (hR : MemRel U R) (hU : TempU U) {m m' : Mem} (h : R m m') (act : Nat)
    (clo : Val) : R (pushDefer act clo m) (pushDefer act clo m') := by
  unfold pushDefer
  rw [deferEntries_eq hR hU h]
  exact setDeferEntries_rel hR hU h _

/-- Related results of `popDefer`/`nextDefer`: the same closure, related memories. -/
def PopRel (R : Mem → Mem → Prop) (x x' : Except String (Option (Val × Mem))) : Prop :=
  ∀ r, x = .ok r → match r with
    | none => x' = .ok none
    | some (c, m1) => ∃ m1', x' = .ok (some (c, m1')) ∧ R m1 m1'

theorem popDefer_rel (hR : MemRel U R) (hU : TempU U) {m m' : Mem} (h : R m m') (act : Nat) :
    PopRel R (popDefer act m) (popDefer act m') := by
  intro r hr
  unfold popDefer at hr ⊢
  dsimp only at hr ⊢
  rw [deferEntries_eq hR hU h]
  revert hr
  cases (deferEntries m).getLast? with
  | none => intro hr; cases hr; rfl
  | some e =>
    obtain ⟨a, c⟩ := e
    dsimp only
    cases a.asInt .w64 with
    | none => intro hr; cases hr
    | some k =>
      dsimp only
      split
      · intro hr; cases hr
        exact ⟨_, rfl, setDeferEntries_rel hR hU h _⟩
      · intro hr; cases hr; rfl

theorem popDefer_avoids (hU : TempU U) {m m1 : Mem} (hm : m.Avoids U) {act : Nat} {c : Val}
    (hp : popDefer act m = .ok (some (c, m1))) : c.Avoids U ∧ m1.Avoids U := by
  unfold popDefer at hp
  dsimp only at hp
  revert hp
  cases hl : (deferEntries m).getLast? with
  | none => intro hp; cases hp
  | some e =>
    obtain ⟨a, c'⟩ := e
    dsimp only
    cases a.asInt .w64 with
    | none => intro hp; cases hp
    | some k =>
      dsimp only
      split
      · intro hp
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have hmem := List.mem_of_getLast? hl
        refine ⟨(deferEntries_avoids hU hm _ hmem).2, setDeferEntries_avoids hm fun e he => ?_⟩
        exact deferEntries_avoids hU hm e (List.dropLast_subset _ he)
      · intro hp; cases hp

theorem nextDefer_rel (hR : MemRel U R) (hU : TempU U) {di : DeferInfo} {act : Nat}
    (hdi : DeferAvoid U di act) {m m' : Mem} (h : R m m') :
    PopRel R (nextDefer di act m) (nextDefer di act m') := by
  unfold nextDefer
  dsimp only
  cases hb : di.bits with
  | none => exact popDefer_rel hR hU h act
  | some nb =>
    have hu := hdi.1 nb hb
    dsimp only
    rw [hR.load h _ _ hu]
    cases (m.load (.int .w8) ⟨if nb.2 then .local act nb.1 else .temp act nb.1, 0⟩).asInt .w8 with
    | none => intro r hr; cases hr
    | some bits =>
      dsimp only
      cases (List.range 8).reverse.find? (fun i => bits.getLsbD i) with
      | none => exact popDefer_rel hR hU h act
      | some i =>
        dsimp only
        cases hs : di.slots[i]? with
        | none => intro r hr; cases hr
        | some o =>
          cases o with
          | none => intro r hr; cases hr
          | some sn =>
            dsimp only
            cases hw : m.write ⟨if nb.2 then .local act nb.1 else .temp act nb.1, 0⟩
                (encode (.int .w8) (.i8 (bits &&& ~~~((1 : BitVec 8) <<< i)))) with
            | none => intro r hr; cases hr
            | some m1 =>
              obtain ⟨m1', hw', hr1⟩ := hR.write h hu hw
              rw [hw', hR.load h _ _ (hdi.2 i sn hs)]
              intro r hr
              cases hr
              exact ⟨m1', rfl, hr1⟩

theorem nextDefer_avoids (hU : TempU U) {di : DeferInfo} {act : Nat} (hdi : DeferAvoid U di act)
    {m m1 : Mem} (hm : m.Avoids U) {c : Val} (hp : nextDefer di act m = .ok (some (c, m1))) :
    c.Avoids U ∧ m1.Avoids U := by
  unfold nextDefer at hp
  dsimp only at hp
  revert hp
  cases hb : di.bits with
  | none => exact popDefer_avoids hU hm
  | some nb =>
    dsimp only
    cases (m.load (.int .w8) ⟨if nb.2 then .local act nb.1 else .temp act nb.1, 0⟩).asInt .w8 with
    | none => intro hp; cases hp
    | some bits =>
      dsimp only
      cases (List.range 8).reverse.find? (fun i => bits.getLsbD i) with
      | none => exact popDefer_avoids hU hm
      | some i =>
        dsimp only
        cases hs : di.slots[i]? with
        | none => intro hp; cases hp
        | some o =>
          cases o with
          | none => intro hp; cases hp
          | some sn =>
            dsimp only
            cases hw : m.write ⟨if nb.2 then .local act nb.1 else .temp act nb.1, 0⟩
                (encode (.int .w8) (.i8 (bits &&& ~~~((1 : BitVec 8) <<< i)))) with
            | none => intro hp; cases hp
            | some m2 =>
              intro hp
              simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, rfl⟩ := hp
              exact ⟨load_avoids hU hm _ (hdi.2 i sn hs),
                memAvoids_write hm hw fun _ => encode_avoids _ trivial⟩

theorem panicRec_eq (hR : MemRel U R) (hU : TempU U) {m m' : Mem} (h : R m m') :
    panicRec? m' = panicRec? m := by
  unfold panicRec?; rw [hR.find h panicBlk (global_notU hU _)]

theorem panicRec_avoids (hU : TempU U) {m : Mem} (hm : m.Avoids U) {r w : Bool} {k : Nat}
    {v : Val} (hp : panicRec? m = .ok (some (r, w, k, v))) : v.Avoids U := by
  unfold panicRec? at hp
  revert hp
  cases ha : m.find? panicBlk with
  | none => intro hp; cases hp
  | some a =>
    dsimp only
    have hav := decode_avoids hU (memAvoids_find hm ha (global_notU hU _)) 0 recTy
    revert hav
    generalize decode a.data 0 recTy = d
    intro hav
    split
    · rename_i r' w' k' v'
      split
      · intro hp
        simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨-, -, -, rfl⟩ := hp
        exact hav.2.2.2.1
      · intro hp; cases hp
    · intro hp; cases hp

theorem setPanicRec_avoids {m : Mem} (hm : m.Avoids U) (r w : Bool) (k : Nat) {v : Val}
    (hv : v.Avoids U) : (setPanicRec m r w k v).Avoids U :=
  memAvoids_set hm fun _ => encode_avoids _ ⟨trivial, trivial, trivial, hv, trivial⟩

theorem setPanicRec_rel (hR : MemRel U R) (hU : TempU U) {m m' : Mem} (h : R m m')
    (r w : Bool) (k : Nat) (v : Val) : R (setPanicRec m r w k v) (setPanicRec m' r w k v) :=
  hR.set h _ _ (global_notU hU _)

theorem toAny_avoids (hU : TempU U) {e : Panic} (he : e.Avoids U) : e.toAny.Avoids U := by
  cases e with
  | value bs =>
    exact decode_avoids hU (fun x hx => he x (by simpa using hx)) 0 _
  | _ => exact ⟨global_notU hU _, trivial, trivial⟩

theorem nilIface_avoids (hU : TempU U) : nilIface.Avoids U :=
  ⟨trivial, nil_notU hU, trivial⟩

theorem restorePanicRec_avoids {m : Mem} (hm : m.Avoids U) (pe : Option Panic)
    {saved : Option Alloc} (hs : ∀ a, saved = some a → ¬ U panicBlk → BAv U a.data) :
    (restorePanicRec pe saved m).Avoids U := by
  unfold restorePanicRec
  split
  · exact memAvoids_set hm (hs _ rfl)
  · exact memAvoids_filter hm _
  · exact hm

theorem restorePanicRec_rel (hR : MemRel U R) (hU : TempU U) {m m' : Mem} (h : R m m')
    (pe : Option Panic) (saved : Option Alloc) :
    R (restorePanicRec pe saved m) (restorePanicRec pe saved m') := by
  unfold restorePanicRec
  split
  · exact hR.set h _ _ (global_notU hU _)
  · exact hR.free h _
  · exact h

/-! ## Deferred calls -/

theorem deferredCode_eq (hR : MemRel U R) (hU : TempU U) {m m' : Mem} (h : R m m') {clo : Val}
    (hc : clo.Avoids U) : deferredCode? m' clo = deferredCode? m clo := by
  unfold deferredCode?
  cases hp : clo.asPtrWord with
  | none => rfl
  | some p => dsimp only; rw [hR.load h _ p (asPtrWord_notU hU hc hp)]

theorem callDeferred_rel (hR : MemRel U R) {env : Env}
    (hE : ∀ name c, env.extern name = some c → Respects U R c) {clo : Val} (hc : clo.Avoids U)
    {m m' : Mem} (hm : m.Avoids U) (h : R m m') (act : Nat) (code : Option String) :
    CRel U R (callDeferred env act clo code m) (callDeferred env act clo code m') := by
  cases code with
  | none => exact ⟨rfl, trivial, hm, h⟩
  | some name =>
    cases hx : env.extern name with
    | none => simp only [callDeferred, hx]; trivial
    | some c =>
      simp only [callDeferred, hx]
      exact hE name c hx [] (some clo) _ _ (by simp) (by simpa using hc) (memAvoids_poison hm _)
        (hR.poison h _)

/-! ## The runtime entry points of `Env.atAct` -/

theorem deferproc_respects (hR : MemRel U R) (hU : TempU U) (act : Nat) :
    Respects U R (deferproc act) := by
  intro args clo m m' hargs _ hm h
  unfold deferproc
  match args, hargs with
  | [fn], hargs =>
    exact ⟨rfl, by simp, pushDefer_avoids hU hm act (hargs fn (by simp)),
      pushDefer_rel hR hU h act fn⟩
  | [], _ => trivial
  | _ :: _ :: _, _ => trivial

theorem deferprocStack_respects (hR : MemRel U R) (hU : TempU U) (act : Nat) :
    Respects U R (deferprocStack act) := by
  intro args clo m m' hargs _ hm h
  have reg : ∀ d : Ptr, ¬ U d.blk →
      CRel U R
        (match m.load (.ptr none) ⟨d.blk, d.off + 24⟩ with
          | .poison => .stuck "deferprocStack: undefined fn"
          | fn => .returned [] (pushDefer act fn m))
        (match m'.load (.ptr none) ⟨d.blk, d.off + 24⟩ with
          | .poison => .stuck "deferprocStack: undefined fn"
          | fn => .returned [] (pushDefer act fn m')) := by
    intro d hd
    rw [hR.load h _ ⟨d.blk, d.off + 24⟩ hd]
    have hfn := load_avoids hU hm (.ptr none) (p := ⟨d.blk, d.off + 24⟩) hd
    revert hfn
    generalize m.load (.ptr none) ⟨d.blk, d.off + 24⟩ = fn
    intro hfn
    cases fn
    case poison => trivial
    all_goals exact ⟨rfl, by simp, pushDefer_avoids hU hm act hfn, pushDefer_rel hR hU h act _⟩
  unfold deferprocStack
  split
  · rename_i d
    exact reg d (hargs (.ptr d) (by simp))
  · rename_i x
    exact reg _ (ofAddr_notU hU x)
  · trivial

theorem gorecover_respects (hR : MemRel U R) (hU : TempU U) (act : Nat) :
    Respects U R (gorecover act) := by
  intro args clo m m' _ _ hm h
  unfold gorecover
  rw [panicRec_eq hR hU h]
  cases hp : panicRec? m with
  | error msg => trivial
  | ok o =>
    cases o with
    | none => exact ⟨rfl, by simpa using nilIface_avoids hU, hm, h⟩
    | some q =>
      obtain ⟨r, w, k, v⟩ := q
      have hv := panicRec_avoids hU hm hp
      cases r with
      | true => exact ⟨rfl, by simpa using nilIface_avoids hU, hm, h⟩
      | false =>
        dsimp only
        split
        · exact ⟨rfl, by simpa using hv, setPanicRec_avoids hm _ _ _ hv,
            setPanicRec_rel hR hU h _ _ _ _⟩
        · exact ⟨rfl, by simpa using nilIface_avoids hU, hm, h⟩

theorem deferreturn_respects (hR : MemRel U R) (hU : TempU U) {env : Env}
    (hE : ∀ name c, env.extern name = some c → Respects U R c) (act : Nat) :
    Respects U R (deferreturn env act) := by
  intro args clo m m' _ _ hm h
  unfold deferreturn
  rw [deferEntries_eq hR hU h]
  generalize (deferEntries m).length = n
  induction n generalizing m m' with
  | zero => exact ⟨rfl, by simp, hm, h⟩
  | succ n ih =>
    unfold deferreturn.go
    have hp := popDefer_rel hR hU h act
    cases hpm : popDefer act m with
    | error msg => trivial
    | ok r =>
      cases r with
      | none =>
        have := hp none hpm
        simp only at this
        rw [this]
        exact ⟨rfl, by simp, hm, h⟩
      | some q =>
        obtain ⟨c, m1⟩ := q
        obtain ⟨m1', h1, hr1⟩ := hp _ hpm
        rw [h1]
        dsimp only
        obtain ⟨hcA, hm1A⟩ := popDefer_avoids hU hm hpm
        rw [deferredCode_eq hR hU hr1 hcA]
        cases deferredCode? m1 c with
        | error msg => trivial
        | ok code =>
          dsimp only
          have hc := callDeferred_rel hR hE hcA hm1A hr1 act code
          revert hc
          generalize callDeferred env act c code m1 = o
          generalize callDeferred env act c code m1' = o'
          intro hc
          cases o with
          | stuck => trivial
          | returned rs r =>
            cases o' with
            | returned rs' r' => exact ih _ _ hc.2.2.1 hc.2.2.2
            | _ => exact hc.elim
          | panicked e r =>
            cases o' with
            | panicked e' r' => exact hc
            | _ => exact hc.elim

/-- **The entry points `Env.atAct` adds respect `U` and `R`** when `env`'s contracts do. -/
theorem atAct_respects (hR : MemRel U R) (hU : TempU U) {env : Env}
    (hE : ∀ name c, env.extern name = some c → Respects U R c) (act : Nat) :
    ∀ name c, (env.atAct act).extern name = some c → Respects U R c := by
  intro name c hc
  simp only [Env.atAct] at hc
  split at hc
  · cases hc; exact deferproc_respects hR hU act
  · split at hc
    · cases hc; exact deferprocStack_respects hR hU act
    · split at hc
      · cases hc; exact deferreturn_respects hR hU hE act
      · split at hc
        · cases hc; exact gorecover_respects hR hU act
        · exact hE name c hc

/-! ## `runDefers` and the panic case of `finish` -/

theorem goResults_post_eq (hR : MemRel U R) (hU : TempU U) {m m' : Mem} (h : R m m') (act : Nat) :
    ∀ (os : List (Option AuxRef × Ty × Nat)) (pieces : List Val),
      goResults.post act m' pieces os = goResults.post act m pieces os
  | [], pieces => by unfold goResults.post; rfl
  | (name, t, k) :: os, pieces => by
    unfold goResults.post
    have hr : ∀ (n' sz : Nat), m'.read ⟨.local act n', 0⟩ sz = m.read ⟨.local act n', 0⟩ sz :=
      fun n' sz => hR.read h ⟨.local act n', 0⟩ sz (local_notU hU act n')
    simp only [goResults_post_eq hR hU h act os, hr]

theorem goResults_eq (hR : MemRel U R) (hU : TempU U) {m m' : Mem} (h : R m m')
    (outs : Array (Option AuxRef × Ty × Nat)) (act : Nat) (rs : List Val) :
    goResults outs act rs m' = goResults outs act rs m := by
  unfold goResults
  simp only [goResults_post_eq hR hU h act]

/-- Related outcomes of `runDefers`: the same results with memories `R`-related before the
frame of `act` is freed, or the same panic with `R`-related memories. -/
def DRel (R : Mem → Mem → Prop) (act : Nat) : Outcome → Outcome → Prop
  | .stuck _, _ => True
  | .outOfFuel, _ => True
  | .returned rs r, .returned rs' r' =>
    rs' = rs ∧ ∃ q q', R q q' ∧ r = q.freeFrame act ∧ r' = q'.freeFrame act
  | .panicked e r, .panicked e' r' => e' = e ∧ R r r'
  | _, _ => False

theorem runDefers_rel (hR : MemRel U R) (hU : TempU U) {env : Env}
    (hE : ∀ name c, env.extern name = some c → Respects U R c)
    (outs : Array (Option AuxRef × Ty × Nat)) {di : DeferInfo} {act : Nat}
    (hdi : DeferAvoid U di act) :
    ∀ (n : Nat) (pe : Option Panic) {m m' : Mem}, (∀ e ∈ pe, e.Avoids U) → m.Avoids U → R m m' →
      DRel R act (runDefers env outs di act n pe m) (runDefers env outs di act n pe m')
  | 0, _, _, _, _, _, _ => trivial
  | n + 1, pe, m, m', hpe, hm, h => by
    unfold runDefers
    have hp := nextDefer_rel hR hU hdi h
    cases hpm : nextDefer di act m with
    | error msg => trivial
    | ok r =>
      cases r with
      | none =>
        have := hp none hpm
        simp only at this
        rw [this]
        dsimp only
        cases pe with
        | some e => exact ⟨rfl, h⟩
        | none =>
          dsimp only
          rw [goResults_eq hR hU h]
          cases goResults (stackOuts outs) act [] m with
          | ok vals => exact ⟨rfl, m, m', h, rfl, rfl⟩
          | panic e q => exact ⟨rfl, hR.refl q⟩
          | stuck msg => trivial
      | some q =>
        obtain ⟨c, m1⟩ := q
        obtain ⟨m1', h1, hr1⟩ := hp _ hpm
        rw [h1]
        dsimp only
        obtain ⟨hcA, hm1A⟩ := nextDefer_avoids hU hdi hm hpm
        rw [deferredCode_eq hR hU hr1 hcA, hR.find hr1 panicBlk (global_notU hU _),
          hR.nextAct hr1]
        cases deferredCode? m1 c with
        | error msg => trivial
        | ok code =>
          dsimp only
          have hsaved : ∀ a, m1.find? panicBlk = some a → ¬ U panicBlk → BAv U a.data :=
            fun a ha hu => memAvoids_find hm1A ha hu
          cases pe with
          | none =>
            dsimp only
            have hc := callDeferred_rel hR hE hcA hm1A hr1 act code
            revert hc
            generalize callDeferred env act c code m1 = o
            generalize callDeferred env act c code m1' = o'
            intro hc
            cases o with
            | stuck => trivial
            | returned rs r =>
              cases o' with
              | returned rs' r' =>
                obtain ⟨-, -, hrA, hrr⟩ := hc
                exact runDefers_rel hR hU hE outs hdi n none (by simp) hrA hrr
              | _ => exact (hc : False).elim
            | panicked e2 r =>
              cases o' with
              | panicked e2' r' =>
                obtain ⟨rfl, he2, hrA, hrr⟩ := hc
                exact runDefers_rel hR hU hE outs hdi n (some _) (by simpa using he2)
                  (memAvoids_dropFrames (restorePanicRec_avoids hrA none hsaved) _)
                  (hR.dropFrames (restorePanicRec_rel hR hU hrr none _) _)
              | _ => exact (hc : False).elim
          | some e =>
            dsimp only
            have hc := callDeferred_rel hR hE hcA
              (setPanicRec_avoids hm1A false (deferredWrapper code) m1.nextAct
                (toAny_avoids hU (hpe e rfl)))
              (setPanicRec_rel hR hU hr1 false (deferredWrapper code) m1.nextAct e.toAny) act code
            revert hc
            generalize callDeferred env act c code
              (setPanicRec m1 false (deferredWrapper code) m1.nextAct e.toAny) = o
            generalize callDeferred env act c code
              (setPanicRec m1' false (deferredWrapper code) m1.nextAct e.toAny) = o'
            intro hc
            cases o with
            | stuck => trivial
            | returned rs r =>
              cases o' with
              | returned rs' r' =>
                obtain ⟨-, -, hrA, hrr⟩ := hc
                dsimp only
                rw [panicRec_eq hR hU hrr]
                have hres := restorePanicRec_rel hR hU hrr (some e) (m1.find? panicBlk)
                have hresA := restorePanicRec_avoids hrA (some e) hsaved
                cases panicRec? r with
                | error msg => trivial
                | ok o =>
                  cases o with
                  | none => trivial
                  | some q =>
                    obtain ⟨b, -⟩ := q
                    cases b with
                    | true => exact runDefers_rel hR hU hE outs hdi n none (by simp) hresA hres
                    | false => exact runDefers_rel hR hU hE outs hdi n (some e) hpe hresA hres
              | _ => exact (hc : False).elim
            | panicked e2 r =>
              cases o' with
              | panicked e2' r' =>
                obtain ⟨rfl, he2, hrA, hrr⟩ := hc
                exact runDefers_rel hR hU hE outs hdi n (some _) (by simpa using he2)
                  (memAvoids_dropFrames (restorePanicRec_avoids hrA (some e) hsaved) _)
                  (hR.dropFrames (restorePanicRec_rel hR hU hrr (some e) _) _)
              | _ => exact (hc : False).elim

/-- **The panic case of `finish`** on related memories: refinement, when the frame removals make
`R`-related memories equal. -/
theorem finish_panicked_refines (hR : MemRel U R) (hU : TempU U) {env : Env}
    (hE : ∀ name c, env.extern name = some c → Respects U R c)
    (outs : Array (Option AuxRef × Ty × Nat)) {di : DeferInfo} {act : Nat}
    (hdi : DeferAvoid U di act)
    (hfree : ∀ q q', R q q' → q'.freeFrame act = q.freeFrame act)
    (hdrop : ∀ q q', R q q' → q'.dropFrames act = q.dropFrames act)
    {e : Panic} {m m' : Mem} (he : e.Avoids U) (hm : m.Avoids U) (h : R m m')
    (hd : (finish env outs di act (.panicked e m)).Defined) :
    OutcomeRefines act (finish env outs di act (.panicked e m))
      (finish env outs di act (.panicked e m')) := by
  simp only [finish] at hd ⊢
  have hdr := hR.dropFrames h (act + 1)
  rw [deferEntries_eq hR hU hdr]
  have key := runDefers_rel hR hU hE outs hdi (9 + (deferEntries (m.dropFrames (act + 1))).length)
    (some e) (by simpa using he) (memAvoids_dropFrames hm _) hdr
  revert key hd
  generalize runDefers env outs di act (9 + (deferEntries (m.dropFrames (act + 1))).length)
    (some e) (m.dropFrames (act + 1)) = o
  generalize runDefers env outs di act (9 + (deferEntries (m.dropFrames (act + 1))).length)
    (some e) (m'.dropFrames (act + 1)) = o'
  intro hd key
  cases o with
  | stuck => exact hd.elim
  | outOfFuel => exact hd.elim
  | returned rs r =>
    cases o' with
    | returned rs' r' =>
      obtain ⟨rfl, q, q', hq, rfl, rfl⟩ := key
      rw [hfree q q' hq]
      exact OutcomeRefines.refl trivial
    | _ => exact key.elim
  | panicked e1 r =>
    cases o' with
    | panicked e1' r' =>
      obtain ⟨rfl, hrr⟩ := key
      exact .panicked _ (by rw [hdrop r r' hrr]; exact Mem.Refines.refl _)
    | _ => exact key.elim


/-! ## The open-coded defer variables -/

/-- **The variables `deferInfo` names are `DAE.deferVar`s** (open-coded defer slots or the
`deferBits` variable). -/
theorem deferInfo_vars (tabs : Tables) :
    (∀ nb, (deferInfo tabs).bits = some nb → Opt.DAE.deferVar tabs nb.1 = true) ∧
    ∀ (i : Nat) sn, (deferInfo tabs).slots[i]? = some (some sn) →
      Opt.DAE.deferVar tabs sn.1 = true := by
  unfold deferInfo
  suffices h : ∀ (l : List Nat) (di : DeferInfo),
      ((∀ nb, di.bits = some nb → Opt.DAE.deferVar tabs nb.1 = true) ∧
        ∀ (i : Nat) sn, di.slots[i]? = some (some sn) → Opt.DAE.deferVar tabs sn.1 = true) →
      let di' := l.foldl (fun di n =>
        match tabs.aux? n with
        | some { kind := .name _ cls _ off _ fl _, .. } =>
          if cls != .PAUTO then di
          else if fl.deferbits then
            { di with bits := di.bits <|> some (n, tabs.forgeable n) }
          else if fl.opendeferslot && 0 ≤ off then
            let i := off.toNat
            let slots := if i < di.slots.size then di.slots
              else di.slots ++ Array.replicate (i + 1 - di.slots.size) none
            { di with slots := slots.set! i (some (n, tabs.forgeable n)) }
          else di
        | _ => di) di
      (∀ nb, di'.bits = some nb → Opt.DAE.deferVar tabs nb.1 = true) ∧
        ∀ (i : Nat) sn, di'.slots[i]? = some (some sn) → Opt.DAE.deferVar tabs sn.1 = true from
    h _ {} ⟨fun _ h => (by cases h), fun _ _ h => (by simp at h)⟩
  intro l
  induction l with
  | nil => intro di h; exact h
  | cons n l ih =>
    intro di h
    simp only [List.foldl_cons]
    apply ih
    split
    · rename_i fmt sym cls ty off esc fl pos heq
      have hv : Opt.DAE.deferVar tabs n = (fl.opendeferslot || fl.deferbits) := by
        unfold Opt.DAE.deferVar; rw [heq]
      split
      · exact h
      split
      · rename_i hdb
        refine ⟨fun nb hb => ?_, h.2⟩
        cases hd : di.bits with
        | some x => rw [hd] at hb; cases hb; exact h.1 _ hd
        | none =>
          rw [hd] at hb
          cases hb
          rw [hv, hdb, Bool.or_true]
      split
      · rename_i hos
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hos
        refine ⟨h.1, fun i sn hs => ?_⟩
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hs
        repeat' split at hs
        all_goals first
          | (cases hs; rw [hv, hos.1, Bool.true_or])
          | exact h.2 i sn hs
          | (simp at hs; done)
          | (rw [Array.getElem?_append] at hs
             split at hs
             · exact h.2 i sn hs
             · first
                 | (simp only [Array.getElem?_replicate] at hs; split at hs <;> cases hs)
                 | cases hs
                 | simp_all)
      · exact h
    · exact h

end GoFV.Proof.DeferRel
