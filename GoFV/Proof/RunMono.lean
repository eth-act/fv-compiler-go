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

/-- Refined memories have the same writable stack-argument slots. -/
theorem Mem.Refines.outargsOK {m m' : Mem} (h : Mem.Refines m m') (tabs : Tables) (act : Nat)
    (ps : List ABIParam) : Sem.outargsOK tabs act m' ps = Sem.outargsOK tabs act m ps := by
  unfold Sem.outargsOK
  simp only [h.canWrite]


/-! ## Deferred calls and recover (§9.7) -/

theorem Refines.ne_poison {a b : Val} (h : Refines a b) (ha : a ≠ .poison) : b ≠ .poison := by
  cases h <;> first | exact absurd rfl ha | (intro h; cases h)

/-- A non-poison source has the target's pointer word. -/
theorem Refines.asPtrWord_eq {a b : Val} (h : Refines a b) (ha : a ≠ .poison) :
    b.asPtrWord = a.asPtrWord := by
  cases h <;> first | exact absurd rfl ha | rfl

theorem Val.hasPoison_of_asPtrWord {v : Val} {p : Ptr} (h : v.asPtrWord = some p) :
    v.hasPoison = false := by
  cases v with
  | int w x => cases w <;> simp_all [Val.asPtrWord, Val.hasPoison]
  | _ => simp_all [Val.asPtrWord, Val.hasPoison]

/-- `deferproc` entries refined pointwise. -/
inductive DeferEntriesRefine : List (Val × Val) → List (Val × Val) → Prop where
  | nil : DeferEntriesRefine [] []
  | cons {a a' c c' : Val} {l l' : List (Val × Val)} : Refines a a' → Refines c c' →
      DeferEntriesRefine l l' → DeferEntriesRefine ((a, c) :: l) ((a', c') :: l')

theorem DeferEntriesRefine.length_eq : {l l' : List (Val × Val)} → DeferEntriesRefine l l' →
    l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ _ t => by simp [t.length_eq]

theorem DeferEntriesRefine.append : {l l' r r' : List (Val × Val)} → DeferEntriesRefine l l' →
    DeferEntriesRefine r r' → DeferEntriesRefine (l ++ r) (l' ++ r')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ha hc t, h => .cons ha hc (t.append h)

theorem DeferEntriesRefine.dropLast : {l l' : List (Val × Val)} → DeferEntriesRefine l l' →
    DeferEntriesRefine l.dropLast l'.dropLast
  | _, _, .nil => .nil
  | _, _, .cons _ _ .nil => .nil
  | _, _, .cons ha hc (.cons hb hd t) => .cons ha hc (DeferEntriesRefine.dropLast (.cons hb hd t))

theorem DeferEntriesRefine.getLast? : {l l' : List (Val × Val)} → DeferEntriesRefine l l' →
    (l.getLast? = none ∧ l'.getLast? = none) ∨
      ∃ a c a' c', l.getLast? = some (a, c) ∧ l'.getLast? = some (a', c') ∧ Refines a a' ∧
        Refines c c'
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | _, _, .cons ha hc .nil => .inr ⟨_, _, _, _, rfl, rfl, ha, hc⟩
  | _, _, .cons _ _ (.cons hb hd t) => by
    simpa [List.getLast?_cons_cons] using DeferEntriesRefine.getLast? (.cons hb hd t)

theorem deferEntries_mono {m m' : Mem} (h : Mem.Refines m m') :
    DeferEntriesRefine (deferEntries m) (deferEntries m') := by
  unfold deferEntries
  rcases h.find? deferBlk with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · rw [h1, h2]; exact .nil
  · rw [h1, h2]
    dsimp only
    rw [← ha.size_eq]
    generalize List.range (a.data.size / 16) = l
    induction l with
    | nil => exact .nil
    | cons i l ih => exact .cons (decode_mono ha.data _ _) (decode_mono ha.data _ _) ih

theorem encodeEntries_mono : ∀ {l l' : List (Val × Val)} {acc acc' : Array Byte},
    DeferEntriesRefine l l' → BytesRefineA acc acc' →
    BytesRefineA ((l.map fun (a, c) => encode entryTy (.agg [a, c])).foldl (· ++ ·) acc)
      ((l'.map fun (a, c) => encode entryTy (.agg [a, c])).foldl (· ++ ·) acc')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons ha hc t, h => by
    simp only [List.map_cons, List.foldl_cons]
    refine encodeEntries_mono t ?_
    have := BytesRefine.append h (encode_mono entryTy (.agg (.cons ha (.cons hc .nil))))
    simpa only [BytesRefineA, Array.toList_append] using this

theorem setDeferEntries_mono {m m' : Mem} (h : Mem.Refines m m') {es es' : List (Val × Val)}
    (he : DeferEntriesRefine es es') :
    Mem.Refines (setDeferEntries m es) (setDeferEntries m' es') :=
  h.set deferBlk ⟨rfl, encodeEntries_mono he (BytesRefineA.refl _)⟩

theorem pushDefer_mono (act : Nat) {c c' : Val} (hc : Refines c c') {m m' : Mem}
    (h : Mem.Refines m m') : Mem.Refines (pushDefer act c m) (pushDefer act c' m') :=
  setDeferEntries_mono h ((deferEntries_mono h).append (.cons (Refines.refl _) hc .nil))

/-- Results of `popDefer`/`nextDefer`: a failing source, both empty, or refined closures and
memories. -/
inductive DeferNextRefines : Except String (Option (Val × Mem)) →
    Except String (Option (Val × Mem)) → Prop where
  | error (msg : String) (r : Except String (Option (Val × Mem))) : DeferNextRefines (.error msg) r
  | none : DeferNextRefines (.ok none) (.ok none)
  | some {c c' : Val} {m m' : Mem} : Refines c c' → Mem.Refines m m' →
      DeferNextRefines (.ok (some (c, m))) (.ok (some (c', m')))

theorem popDefer_mono (act : Nat) {m m' : Mem} (h : Mem.Refines m m') :
    DeferNextRefines (popDefer act m) (popDefer act m') := by
  unfold popDefer
  have he := deferEntries_mono h
  rcases he.getLast? with ⟨h1, h2⟩ | ⟨a, c, a', c', h1, h2, ha, hc⟩
  · simp only [h1, h2]; exact .none
  · simp only [h1, h2]
    cases hk : a.asInt .w64 with
    | none => exact .error _ _
    | some k =>
      rw [ha.asInt hk]
      dsimp only
      by_cases hb : (k.toNat == act) = true
      · simp only [hb, ↓reduceIte]; exact .some hc (setDeferEntries_mono h he.dropLast)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]; exact .none

theorem nextDefer_mono (di : DeferInfo) (act : Nat) {m m' : Mem} (h : Mem.Refines m m') :
    DeferNextRefines (nextDefer di act m) (nextDefer di act m') := by
  unfold nextDefer
  cases di.bits with
  | none => exact popDefer_mono act h
  | some nb =>
    dsimp only
    cases hx : (m.load (.int .w8) _).asInt .w8 with
    | none => exact .error _ _
    | some bits =>
      rw [(load_mono h _ _).asInt hx]
      dsimp only
      cases (List.range 8).reverse.find? (fun i => bits.getLsbD i) with
      | none => exact popDefer_mono act h
      | some i =>
        dsimp only
        cases di.slots[i]? with
        | none => exact .error _ _
        | some o =>
          cases o with
          | none => exact .error _ _
          | some sn =>
            dsimp only
            cases hw : m.write _ _ with
            | none => exact .error _ _
            | some m1 =>
              obtain ⟨m1', hw', hm1⟩ := h.write (BytesRefineA.refl _) hw
              rw [hw']
              exact .some (load_mono h _ _) hm1

/-- Results of `panicRec?`: a failing source, both without a record, or the same flags and
activation with refined values. -/
inductive PanicRecRefines : Except String (Option (Bool × Bool × Nat × Val)) →
    Except String (Option (Bool × Bool × Nat × Val)) → Prop where
  | error (msg : String) (r : Except String (Option (Bool × Bool × Nat × Val))) :
      PanicRecRefines (.error msg) r
  | none : PanicRecRefines (.ok none) (.ok none)
  | some (r w : Bool) (k : Nat) {v v' : Val} : Refines v v' →
      PanicRecRefines (.ok (some (r, w, k, v))) (.ok (some (r, w, k, v')))

theorem panicRec?_mono {m m' : Mem} (h : Mem.Refines m m') :
    PanicRecRefines (panicRec? m) (panicRec? m') := by
  unfold panicRec?
  rcases h.find? panicBlk with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · rw [h1, h2]; exact .none
  · rw [h1, h2]
    dsimp only
    have hd := decode_mono ha.data 0 recTy
    revert hd
    generalize decode a.data 0 recTy = d
    generalize decode a'.data 0 recTy = d'
    intro hd
    split
    · next r w k v =>
      cases hd with
      | agg hl =>
        obtain ⟨r', _, rfl, hr, hl⟩ := hl.cons_inv
        obtain ⟨w', _, rfl, hw, hl⟩ := hl.cons_inv
        obtain ⟨k', _, rfl, hk, hl⟩ := hl.cons_inv
        obtain ⟨v', _, rfl, hv, hl⟩ := hl.cons_inv
        cases hl.nil_inv
        dsimp only
        cases hr' : r.asInt .w8 with
        | none => exact .error _ _
        | some r0 =>
          cases hw' : w.asInt .w8 with
          | none => exact .error _ _
          | some w0 =>
            cases hk' : k.asInt .w64 with
            | none => exact .error _ _
            | some k0 =>
              rw [hr.asInt hr', hw.asInt hw', hk.asInt hk']
              exact .some _ _ _ hv
    · exact .error _ _

theorem setPanicRec_mono {m m' : Mem} (h : Mem.Refines m m') (r w : Bool) (k : Nat) {v v' : Val}
    (hv : Refines v v') : Mem.Refines (setPanicRec m r w k v) (setPanicRec m' r w k v') :=
  h.set panicBlk ⟨rfl, encode_mono recTy (.agg (.cons (Refines.refl _) (.cons (Refines.refl _)
    (.cons (Refines.refl _) (.cons hv .nil)))))⟩

/-- Results of `deferredCode?`: a failing source, or the same code symbol. -/
theorem deferredCode?_mono {m m' : Mem} (h : Mem.Refines m m') {c c' : Val} (hc : Refines c c')
    {code : Option String} (hd : deferredCode? m c = .ok code) :
    deferredCode? m' c' = .ok code ∧ c.hasPoison = false := by
  unfold deferredCode? at hd ⊢
  cases hp : c.asPtrWord with
  | none => rw [hp] at hd; cases hd
  | some p =>
    rw [hp] at hd
    rw [hc.asPtrWord hp]
    refine ⟨?_, Val.hasPoison_of_asPtrWord hp⟩
    dsimp only at hd ⊢
    by_cases hn : p.isNil = true
    · simp only [hn, ↓reduceIte] at hd ⊢; exact hd
    · simp only [hn, Bool.false_eq_true, ↓reduceIte] at hd ⊢
      cases ht : codeTarget? (m.load (.ptr none) p) with
      | none => rw [ht] at hd; cases hd
      | some name =>
        rw [ht] at hd
        rw [codeTarget?_mono (load_mono h _ _) ht]
        exact hd

theorem callDeferred_mono {env : Env} (hE : env.Mono) (act : Nat) {c c' : Val}
    (hc : Refines c c') (hp : c.hasPoison = false) (code : Option String) {m m' : Mem}
    (h : Mem.Refines m m') :
    COutcome.Refines (callDeferred env act c code m) (callDeferred env act c' code m') := by
  cases code with
  | none => exact .panicked _ h
  | some name =>
    simp only [callDeferred]
    cases hx : env.extern name with
    | none => exact .stuck _ _
    | some f => exact hE name f hx rfl (by simpa using hp) .nil (.some hc) (h.poisonBlock _)

/-- Refined memories have the same writable runtime blocks. -/
theorem Mem.Refines.rtWritable_eq {m m' : Mem} (h : Mem.Refines m m') (b : Blk) :
    rtWritable m' b = rtWritable m b := by
  unfold rtWritable
  rcases h.find? b with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact ha.writable.symm

theorem deferproc_mono (act : Nat) : (deferproc act).Mono := by
  intro args args' _ _ _ _ _ _ ha _ hm
  unfold deferproc
  match args, args', ha with
  | [_], _, .cons hf .nil =>
    dsimp only
    rw [hm.rtWritable_eq]
    split
    · exact .returned .nil (pushDefer_mono act hf hm)
    · exact .stuck _ _
  | [], _, .nil => exact .stuck _ _
  | _ :: _ :: _, _, .cons _ (.cons _ _) => exact .stuck _ _

theorem deferprocStack_mono (act : Nat) : (deferprocStack act).Mono := by
  intro args args' clo clo' m m' _ _ ha _ hm
  have hreg : ∀ d : Ptr, COutcome.Refines (deferprocStack act [.ptr d] clo m)
      (deferprocStack act [.ptr d] clo' m') := by
    intro d
    have hl := load_mono hm (.ptr none) ⟨d.blk, d.off + 24⟩
    simp only [deferprocStack]
    revert hl
    generalize m.load (.ptr none) ⟨d.blk, d.off + 24⟩ = x
    generalize m'.load (.ptr none) ⟨d.blk, d.off + 24⟩ = x'
    intro hl
    by_cases hx : x = .poison
    · subst hx; exact .stuck _ _
    · have hx' := hl.ne_poison hx
      split
      · exact absurd rfl hx
      · rw [hm.rtWritable_eq]
        split
        · exact .returned .nil (pushDefer_mono act hl hm)
        · exact .stuck _ _
  match args, args', ha with
  | [], _, .nil => exact .stuck _ _
  | a :: _ :: _, _, .cons _ (.cons _ _) =>
    cases a with
    | int w x => cases w <;> exact .stuck _ _
    | _ => exact .stuck _ _
  | [a], _, .cons hf .nil =>
    cases hf with
    | poison => exact .stuck _ _
    | ptr d => exact hreg d
    | int w x =>
      cases w with
      | w64 => exact hreg (Ptr.ofAddr x)
      | _ => exact .stuck _ _
    | _ => exact .stuck _ _

theorem deferreturn_go_mono {env : Env} (hE : env.Mono) (act : Nat) :
    ∀ (n : Nat) {m m' : Mem}, Mem.Refines m m' →
      COutcome.Refines (deferreturn.go env act n m) (deferreturn.go env act n m')
  | 0, _, _, h => .returned .nil h
  | n + 1, m, m', h => by
    simp only [deferreturn.go]
    rw [h.rtWritable_eq]
    by_cases hw : (!rtWritable m deferBlk) = true
    · simp only [hw, ↓reduceIte]; exact .stuck _ _
    simp only [hw, Bool.false_eq_true, ↓reduceIte]
    have hp := popDefer_mono act h
    revert hp
    generalize popDefer act m = r
    generalize popDefer act m' = r'
    intro hp
    cases hp with
    | error => exact .stuck _ _
    | none => exact .returned .nil h
    | @some c c' m1 m1' hc hm1 =>
      dsimp only
      cases hd : deferredCode? m1 c with
      | error => exact .stuck _ _
      | ok code =>
        obtain ⟨hd', hcp⟩ := deferredCode?_mono hm1 hc hd
        rw [hd']
        dsimp only
        have ho := callDeferred_mono hE act hc hcp code hm1
        revert ho
        generalize callDeferred env act c code m1 = o
        generalize callDeferred env act c' code m1' = o'
        intro ho
        cases ho with
        | returned _ hm2 => exact deferreturn_go_mono hE act n hm2
        | panicked e hm2 => exact .panicked e hm2
        | stuck => exact .stuck _ _

theorem deferreturn_mono {env : Env} (hE : env.Mono) (act : Nat) : (deferreturn env act).Mono := by
  intro _ _ _ _ m m' _ _ _ _ hm
  simp only [deferreturn]
  rw [← (deferEntries_mono hm).length_eq]
  exact deferreturn_go_mono hE act _ hm

theorem gorecover_mono (act : Nat) : (gorecover act).Mono := by
  intro _ _ _ _ m m' _ _ _ _ hm
  simp only [gorecover]
  have hp := panicRec?_mono hm
  revert hp
  generalize panicRec? m = r
  generalize panicRec? m' = r'
  intro hp
  cases hp with
  | error => exact .stuck _ _
  | none => exact .returned (.cons (Refines.refl _) .nil) hm
  | some r w k hv =>
    cases r with
    | true => exact .returned (.cons (Refines.refl _) .nil) hm
    | false =>
      dsimp only
      by_cases hc : (k != 0 && (act == k || (w && act == k + 1))) = true
      · simp only [hc, ↓reduceIte]
        rw [hm.rtWritable_eq]
        split
        · exact .returned (.cons hv .nil) (setPanicRec_mono hm true w k hv)
        · exact .stuck _ _
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact .returned (.cons (Refines.refl _) .nil) hm

/-- `Env.atAct` keeps monotonicity: its runtime entry points are monotone. -/
theorem Env.Mono.atAct {env : Env} (hE : env.Mono) (act : Nat) : (env.atAct act).Mono := by
  intro name c h
  simp only [Env.atAct] at h
  split at h
  · cases h; exact deferproc_mono act
  · split at h
    · cases h; exact deferprocStack_mono act
    · split at h
      · cases h; exact deferreturn_mono hE act
      · split at h
        · cases h; exact gorecover_mono act
        · exact hE name c h

theorem nilClosure_eq {clo clo' : Option Val} (hc : OptRefines clo clo')
    (hp : (clo.map Val.hasPoison).getD false = false) : nilClosure clo' = nilClosure clo := by
  cases hc with
  | none => rfl
  | @some c c' hcc =>
    have hc0 : c ≠ .poison := by rintro rfl; simp [Val.hasPoison] at hp
    simp only [nilClosure, Option.bind_some, hcc.asPtrWord_eq hc0]

end GoFV.SSA.Sem

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-! ## `finish` with monotone contracts -/

theorem restorePanicRec_mono (pe : Option Panic) {s s' : Option Alloc}
    (hs : (s = none ∧ s' = none) ∨ ∃ a a', s = some a ∧ s' = some a' ∧ Alloc.Refines a a')
    {r r' : Mem} (h : Mem.Refines r r') :
    Mem.Refines (restorePanicRec pe s r) (restorePanicRec pe s' r') := by
  rcases hs with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, ha⟩ <;> cases pe <;> simp only [restorePanicRec]
  · exact h
  · exact h.free _
  · exact h
  · exact h.set _ ha

/-- `runDefers` maps refined memories to refined outcomes. -/
theorem runDefers_mono {env : Env} (hE : env.Mono) (outs : Array (Option AuxRef × Ty × Nat))
    (di : DeferInfo) (act k : Nat) :
    ∀ (n : Nat) (pe : Option Panic) {m m' : Mem}, Mem.Refines m m' →
      (runDefers env outs di act n pe m).Defined →
      OutcomeRefines k (runDefers env outs di act n pe m) (runDefers env outs di act n pe m')
  | 0, _, _, _, _, hd => hd.elim
  | n + 1, pe, m, m', h, hd => by
    simp only [runDefers] at hd ⊢
    have hn := nextDefer_mono di act h
    revert hd hn
    generalize nextDefer di act m = r
    generalize nextDefer di act m' = r'
    intro hd hn
    cases hn with
    | error => exact hd.elim
    | none =>
      cases pe with
      | some e => exact .panicked e (h.dropFrames k)
      | none =>
        dsimp only at hd ⊢
        have hg := goResults_mono (outs := stackOuts outs) (act := act) (rs := []) rfl .nil h
        revert hd
        generalize goResults (stackOuts outs) act [] m = g at hg ⊢
        generalize goResults (stackOuts outs) act [] m' = g' at hg ⊢
        cases hg with
        | ok hv => intro _; exact .returned hv (h.freeFrame act)
        | panic e hm' => intro _; exact .panicked e (hm'.dropFrames k)
        | stuck => intro hd; exact hd.elim
    | @some c c' m1 m1' hc hm1 =>
      dsimp only at hd ⊢
      cases hdc : deferredCode? m1 c with
      | error => rw [hdc] at hd; exact hd.elim
      | ok code =>
        obtain ⟨hdc', hcp⟩ := deferredCode?_mono hm1 hc hdc
        rw [hdc] at hd
        rw [hdc']
        dsimp only at hd ⊢
        have hres : ∀ {r r' : Mem}, Mem.Refines r r' →
            Mem.Refines (restorePanicRec pe (m1.find? panicBlk) r)
              (restorePanicRec pe (m1'.find? panicBlk) r') :=
          fun h => restorePanicRec_mono pe (hm1.find? panicBlk) h
        cases pe with
        | none =>
          dsimp only at hd ⊢
          have ho := callDeferred_mono hE act hc hcp code hm1
          revert hd ho
          generalize callDeferred env act c code m1 = o
          generalize callDeferred env act c' code m1' = o'
          intro hd ho
          cases ho with
          | returned _ hm3 => exact runDefers_mono hE outs di act k n none hm3 hd
          | panicked e2 hm3 =>
            exact runDefers_mono hE outs di act k n (some e2) ((hres hm3).dropFrames _) hd
          | stuck => exact hd.elim
        | some e =>
          dsimp only at hd ⊢
          rw [← hm1.nextAct]
          have ho := callDeferred_mono hE act hc hcp code
            (setPanicRec_mono hm1 false (deferredWrapper code) m1.nextAct (Sem.Refines.refl e.toAny))
          revert hd ho
          generalize callDeferred env act c code _ = o
          generalize callDeferred env act c' code _ = o'
          intro hd ho
          cases ho with
          | returned _ hm3 =>
            dsimp only at hd ⊢
            have hp := panicRec?_mono hm3
            revert hd hp
            generalize panicRec? _ = p
            generalize panicRec? _ = p'
            intro hd hp
            cases hp with
            | error => exact hd.elim
            | none => exact hd.elim
            | some r w j hv =>
              cases r with
              | true => exact runDefers_mono hE outs di act k n none (hres hm3) hd
              | false => exact runDefers_mono hE outs di act k n (some e) (hres hm3) hd
          | panicked e2 hm3 =>
            exact runDefers_mono hE outs di act k n (some e2) ((hres hm3).dropFrames _) hd
          | stuck => exact hd.elim

/-- **`finish` preserves refinement** under monotone contracts: loop outcomes that panic with
refined memories (`LoopRefines Mem.Refines`) have refined `finish` outcomes, since the deferred
calls `finish` runs at a panic are monotone (`runDefers_mono`). -/
theorem finish_refines_mono {env : Env} (hE : env.Mono) {outs : Array (Option AuxRef × Ty × Nat)}
    {di : DeferInfo} {act k : Nat} {o o' : Outcome} (hd : (finish env outs di act o).Defined)
    (h : LoopRefines Mem.Refines o o') :
    OutcomeRefines k (finish env outs di act o) (finish env outs di act o') := by
  cases h with
  | returned hr hm => exact finish_returned_refines hd hr hm
  | panicked e hm =>
    have hm' := hm.dropFrames (act + 1)
    simp only [finish] at hd ⊢
    rw [← (deferEntries_mono hm').length_eq]
    exact runDefers_mono hE outs di act k _ (some e) hm' hd

/-- Non-vacuity of `Env.Mono.atAct`: `Env.p1` with the defer entry points is monotone. -/
theorem Env.p1_atAct_mono (act : Nat) : (Env.p1.atAct act).Mono := Env.p1_mono.atAct act

/-- A memory with one poison byte (`fmPoison`) and its refinement with a concrete byte
(`fmByte`). -/
def fmPoison : Mem := { blocks := #[(.global "x", { data := #[.poison] })] }
def fmByte : Mem := { blocks := #[(.global "x", { data := #[.b 7] })] }

/-- Non-vacuity of `finish_refines_mono`: a panic in `fmPoison` is refined by the same panic in
`fmByte` after `finish` (no deferred calls). -/
theorem finish_refines_mono_witness :
    OutcomeRefines 0 (finish Env.p1 #[] {} 0 (.panicked .nilDeref fmPoison))
      (finish Env.p1 #[] {} 0 (.panicked .nilDeref fmByte)) :=
  finish_refines_mono Env.p1_mono
    (by
      have h : finish Env.p1 #[] {} 0 (.panicked .nilDeref fmPoison) =
          .panicked .nilDeref (fmPoison.dropFrames 1) := by rfl
      rw [h]; trivial)
    (.panicked _ ⟨rfl, rfl, .cons _ ⟨rfl, .cons (.poison _) .nil⟩ .nil⟩)

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
            rw [hm.outargsOK]
            split
            · exact .stuck _ _
            rw [nilClosure_eq hclo hp.2]
            split
            · exact .panic _ (hm.poisonBelow _ _)
            cases callee? with
            | none => exact .stuck _ _
            | some callee =>
              rcases hc with hc | hc
              · cases hc
              subst hc
              dsimp only
              cases hx : (env.atAct ctx.act).extern callee with
              | none => exact .stuck _ _
              | some c =>
                dsimp only
                generalize callFrame ctx.tabs v.aux _ _ = F
                have := hE.atAct ctx.act _ _ hx hp.1 hp.2 ha hclo (hm.poisonBelow (.outargs ctx.act) F)
                revert this
                generalize c A clo (m.poisonBelow (.outargs ctx.act) F) = o
                generalize c A' clo' (m'.poisonBelow (.outargs ctx.act) F) = o'
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
        have ha := retypeResults_mono ctx.tabs
          ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter (!·.out)) hpieces
        revert ha
        generalize retypeResults ctx.tabs _ rest.dropLast = A
        generalize retypeResults ctx.tabs _ rest'.dropLast = A'
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
          rw [hm.outargsOK]
          split
          · exact .stuck _ _
          rw [nilClosure_eq hclo hp.2]
          split
          · exact .panic _ (hm.poisonBelow _ _)
          cases callee? with
          | none => exact .stuck _ _
          | some callee =>
            rcases hc with hc | hc
            · cases hc
            subst hc
            dsimp only
            cases hx : (env.atAct ctx.act).extern callee with
            | none => exact .stuck _ _
            | some c =>
              dsimp only
              generalize callFrame ctx.tabs v.aux _ _ = F
              have := hE.atAct ctx.act _ _ hx hp.1 hp.2 ha hclo (hm.poisonBelow (.outargs ctx.act) F)
              revert this
              generalize c A clo (m.poisonBelow (.outargs ctx.act) F) = o
              generalize c A' clo' (m'.poisonBelow (.outargs ctx.act) F) = o'
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
    cases h.nil_inv; cases h3 with | mem hm =>
    rw [heq]; dsimp only
    split
    · next p hp =>
      rw [h1.asPtrWord hp]
      exact writeRes_mono _ _ fun m1 hw => hm.write (encode_mono _ h2) hw
    · exact .stuck _ _
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
    cases h.nil_inv; cases h3 with | mem hm =>
    rw [heq]; dsimp only
    split
    · next p hp =>
      rw [h1.asPtrWord hp]
      exact writeRes_mono _ _ fun m1 hw => hm.write (encode_mono _ h2) hw
    · exact .stuck _ _
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
    cases h.nil_inv; cases h3 with | mem hm =>
    rw [heq]; dsimp only
    split
    · next d s hd hs =>
      rw [h1.asPtrWord hd, h2.asPtrWord hs]; dsimp only
      cases hr : Mem.read _ _ _ with
      | none => exact .stuck _ _
      | some bs =>
        obtain ⟨bs', hr', hb⟩ := hm.read hr
        rw [hr']
        exact writeRes_mono _ _ fun m1 hw => hm.write hb hw
    · exact .stuck _ _
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
    cases h.nil_inv; cases h3 with | mem hm =>
    rw [heq]; dsimp only
    split
    · next d s hd hs =>
      rw [h1.asPtrWord hd, h2.asPtrWord hs]; dsimp only
      cases hr : Mem.read _ _ _ with
      | none => exact .stuck _ _
      | some bs =>
        obtain ⟨bs', hr', hb⟩ := hm.read hr
        rw [hr']
        exact writeRes_mono _ _ fun m1 hw => hm.write hb hw
    · exact .stuck _ _
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    cases h.nil_inv
    cases h2 with | mem hm =>
    rw [heq]; dsimp only
    split
    · next p hp =>
      rw [h1.asPtrWord hp]
      exact writeRes_mono _ _ fun m1 hw => hm.write (BytesRefineA.refl _) hw
    · exact .stuck _ _
  · next heq =>
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    cases h.nil_inv
    cases h2 with | mem hm =>
    rw [heq]; dsimp only
    split
    · next p hp =>
      rw [h1.asPtrWord hp]
      exact writeRes_mono _ _ fun m1 hw => hm.write (BytesRefineA.refl _) hw
    · exact .stuck _ _
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
    exact .ok (.mem (hm.free _))
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
    cases h2 with | mem hm =>
    rw [heq]; dsimp only
    split
    · next p hp =>
      rw [h1.asPtrWord hp]; dsimp only
      split
      · exact .panic _ hm
      · exact .ok h1
    · exact .stuck _ _
  · split <;> exact .stuck _ _

/-! ## Atomics (`Sem/Atomic.lean`) -/

private theorem atomicStep_mono (k : Atomic.Kind) (w : Width) {o o' x x' : Val}
    (ho : Sem.Refines o o') (hx : Sem.Refines x x') {m m' : Mem} (hm : Mem.Refines m m') :
    Sem.Refines (Atomic.step k w o x).1 (Atomic.step k w o' x').1 ∧
      Sem.Refines (Atomic.result (Atomic.step k w o x).2 m)
        (Atomic.result (Atomic.step k w o' x').2 m') := by
  have h2 : RefinesList [o, x] [o', x'] := .cons ho (.cons hx .nil)
  cases k <;> refine ⟨?_, ?_⟩ <;> simp only [Atomic.step, Atomic.result]
  all_goals first
    | exact hx
    | exact .mem hm
    | exact int2_mono _ _ h2
    | exact .tuple (.cons ho (.cons (.mem hm) .nil))
    | exact .tuple (.cons (int2_mono _ _ h2) (.cons (.mem hm) .nil))

private theorem atomicRmw_mono (v : Value) (k : Atomic.Kind) (t : Ty) (p : Ptr) {x x' : Val}
    {m m' : Mem} (hx : Sem.Refines x x') (hm : Mem.Refines m m') :
    Res.Refines (Atomic.rmw v k t p x m) (Atomic.rmw v k t p x' m') := by
  unfold Atomic.rmw
  by_cases ha : Atomic.aligned p t.size = true
  · simp only [ha, ↓reduceIte]
    have hs := atomicStep_mono k (Atomic.width t) (load_mono hm t p) hx hm
    cases hw : m.write p (encode t (Atomic.step k (Atomic.width t) (m.load t p) x).1) with
    | none => exact .stuck _ _
    | some m1 =>
      obtain ⟨m1', hw', hm1⟩ := hm.write (encode_mono t hs.1) hw
      rw [hw']
      exact .ok (atomicStep_mono k (Atomic.width t) (load_mono hm t p) hx hm1).2
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]; exact .stuck _ _

private theorem atomicCas_mono (v : Value) (w : Width) (p : Ptr) {o o' n n' : Val}
    {m m' : Mem} (ho : Sem.Refines o o') (hn : Sem.Refines n n') (hm : Mem.Refines m m') :
    Res.Refines (Atomic.cas v w p o n m) (Atomic.cas v w p o' n' m') := by
  unfold Atomic.cas
  by_cases ha : Atomic.aligned p w.bytes = true
  · simp only [ha, ↓reduceIte]
    cases hc : (m.load (.int w) p).asInt w with
    | none => exact .stuck _ _
    | some cur =>
      cases hoo : o.asInt w with
      | none => exact .stuck _ _
      | some old =>
        rw [(load_mono hm (.int w) p).asInt hc, ho.asInt hoo]
        by_cases he : cur = old
        · simp only [he, ↓reduceIte]
          cases hw : m.write p (encode (.int w) n) with
          | none => exact .stuck _ _
          | some m1 =>
            obtain ⟨m1', hw', hm1⟩ := hm.write (encode_mono _ hn) hw
            rw [hw']
            exact .ok (.tuple (.cons (.bool true) (.cons (.mem hm1) .nil)))
        · simp only [he, ↓reduceIte]
          exact .ok (.tuple (.cons (.bool false) (.cons (.mem hm) .nil)))
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]; exact .stuck _ _

/-- A read-modify-write on an operand `x` that the location's shape `t` stores as `poison` and
reads as no integer is the one on `poison`, so the one on any operand refines it. -/
theorem atomicRmw_poisonArg (v : Value) (k : Atomic.Kind) (t : Ty) (p : Ptr) {x : Val} (x' : Val)
    (m : Mem) (he : encode t x = encode t .poison) (hi : x.asInt (Atomic.width t) = none) :
    Res.Refines (Atomic.rmw v k t p x m) (Atomic.rmw v k t p x' m) := by
  have hp : ∀ y : Val, y.asInt (Atomic.width t) = none →
      ∀ f : BitVec (Atomic.width t).bits → BitVec (Atomic.width t).bits → Val,
        int2 (Atomic.width t) f [m.load t p, y] = .poison := by
    intro y hy f
    simp only [int2, hy]
    split <;> simp_all
  have hs : encode t (Atomic.step k (Atomic.width t) (m.load t p) x).1 =
        encode t (Atomic.step k (Atomic.width t) (m.load t p) .poison).1 ∧
      (Atomic.step k (Atomic.width t) (m.load t p) x).2 =
        (Atomic.step k (Atomic.width t) (m.load t p) .poison).2 := by
    cases k <;>
      simp only [Atomic.step, GoFV.SSA.Sem.Int.add, GoFV.SSA.Sem.Int.and, GoFV.SSA.Sem.Int.or, he,
        hp x hi, hp .poison rfl] <;>
      exact ⟨rfl, rfl⟩
  have h : Atomic.rmw v k t p x m = Atomic.rmw v k t p .poison m := by
    unfold Atomic.rmw; rw [hs.1, hs.2]
  rw [h]; exact atomicRmw_mono v k t p (.poison x') (Mem.Refines.refl m)

/-- A compare-and-swap whose old operand is no `w`-bit integer is `stuck`: anything refines it. -/
theorem atomicCas_stuckArg (v : Value) (w : Width) (p : Ptr) {o : Val} (n : Val) (m : Mem)
    (ho : o.asInt w = none) (r : Res Val) : Res.Refines (Atomic.cas v w p o n m) r := by
  unfold Atomic.cas
  split
  · split
    · next heq => rw [ho] at heq; simp at heq
    · exact .stuck _ _
  · exact .stuck _ _

/-- A compare-and-swap whose new operand the location stores as `poison` is refined by the one
on any new operand. -/
theorem atomicCas_poisonArg (v : Value) (w : Width) (p : Ptr) (o : Val) {n : Val} (n' : Val)
    (m : Mem) (he : encode (.int w) n = encode (.int w) .poison) :
    Res.Refines (Atomic.cas v w p o n m) (Atomic.cas v w p o n' m) := by
  have h : Atomic.cas v w p o n m = Atomic.cas v w p o .poison m := by
    unfold Atomic.cas; rw [he]
  rw [h]; exact atomicCas_mono v w p (Sem.Refines.refl o) (.poison n') (Mem.Refines.refl m)

/-- **The atomic roots are monotone.** -/
theorem atomicRoot_mono (v : Value) {as bs : List Val} (h : RefinesList as bs) :
    Res.Refines (atomicRoot v as) (atomicRoot v bs) := by
  unfold atomicRoot
  split
  · obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    cases h.nil_inv
    dsimp only
    unfold Atomic.barrier
    cases h1 with
    | mem hm =>
      by_cases hp : v.op = .PubBarrier
      · simp only [hp, ↓reduceIte]; exact .ok (.mem hm)
      · simp only [hp, ↓reduceIte]; exact .stuck _ _
    | _ => exact .stuck _ _
  · obtain ⟨_, _, rfl, -, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    cases h.nil_inv
    dsimp only
    unfold Atomic.prefetch
    cases h1 with
    | mem hm =>
      by_cases hp : v.op = .PrefetchCache ∨ v.op = .PrefetchCacheStreamed
      · simp only [hp, ↓reduceIte]; exact .ok (.mem hm)
      · simp only [hp, ↓reduceIte]; exact .stuck _ _
    | _ => exact .stuck _ _
  · obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
    cases h.nil_inv
    dsimp only
    unfold Atomic.rmwRoot
    cases h3 with
    | @mem m m' hm =>
      dsimp only
      split
      · next p k t hp hi =>
        rw [h1.asPtrWord hp, hi]
        exact atomicRmw_mono v k t p h2 hm
      · simp only [Atomic.unmodelled]; exact .stuck _ _
    | _ => exact .stuck _ _
  · obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
    obtain ⟨_, _, rfl, h4, h⟩ := h.cons_inv
    cases h.nil_inv
    dsimp only
    unfold Atomic.casRoot
    cases h4 with
    | @mem m m' hm =>
      dsimp only
      split
      · next p w hp hw =>
        rw [h1.asPtrWord hp, hw]
        exact atomicCas_mono v w p h2 h3 hm
      · simp only [Atomic.unmodelled]; exact .stuck _ _
    | _ => exact .stuck _ _
  · exact .stuck _ _


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
         · exact atomicRoot_mono v h
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
  · exact succ_refl b 0
  · exact .stuck _ _

end GoFV.Proof
