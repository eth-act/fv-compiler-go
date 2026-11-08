import GoFV.Opt.Fuse.PlainCheck

variable [GoFV.SSA.Sem.Addrs]

/-!
# fuseBlockPlain: what the rewrite leaves unchanged

`fuseRun_frame`: the rewrite `fuseRun f b c run` changes value table entries only at the values
of the run's blocks and block table entries only at the run's blocks and `b`'s predecessors; it
keeps `f.blocks`, `ownAux` and the value table's size, and moves the entry from `b` to `c`. The
checked step (`Plain.fuseBlockPlainChecked`) checks only the changed entries against its
snapshot; this lemma covers the rest (issue #147).
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain

/-- `g` agrees with `f` but at the values `V` and the blocks `B` (the entry may differ). -/
structure Fr (V B : ID → Prop) (f g : Func) : Prop where
  blocks : g.blocks = f.blocks
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  value : ∀ x, ¬ V x → g.value? x = f.value? x
  block : ∀ x, ¬ B x → g.block? x = f.block? x

/-- A block without its position. -/
def Block.unpos (B : Block) : Block := { B with pos := default }

/-- `f` and `g` have the same blocks up to positions. -/
def SameUnpos (f g : Func) : Prop := ∀ y, (g.block? y).map Block.unpos = (f.block? y).map Block.unpos

private theorem value?_modV (F : Func) (v : ID) (k : Value → Value) (x : ID) :
    (F.modV v k).value? x = if v = x then (F.value? x).map k else F.value? x := by
  unfold Func.modV Func.value?
  simp only [Array.getElem?_modify]
  split
  · cases F.valueTab[x]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rfl

private theorem block?_modB (F : Func) (b : ID) (k : Block → Block) (x : ID) :
    (F.modB b k).block? x = if b = x then (F.block? x).map k else F.block? x := by
  unfold Func.modB Func.block?
  simp only [Array.getElem?_modify]
  split
  · cases F.blockTab[x]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rfl

private theorem block?_modV (F : Func) (v : ID) (k : Value → Value) (x : ID) :
    (F.modV v k).block? x = F.block? x := rfl

private theorem foldl_inv {α σ : Type} (I : σ → Prop) (step : σ → α → σ) :
    ∀ (l : List α) (s : σ), (∀ a ∈ l, ∀ s, I s → I (step s a)) → I s → I (l.foldl step s)
  | [], _, _, h => h
  | a :: l, s, hs, h =>
    foldl_inv I step l (step s a) (fun a' ha' => hs a' (List.mem_cons_of_mem _ ha'))
      (hs a List.mem_cons_self s h)

private theorem getElem!_mem {α : Type} [Inhabited α] {a : Array α} {k : Nat} (hk : k < a.size) :
    a[k]! ∈ a.toList := by
  rw [getElem!_pos a k hk]
  exact Array.mem_toList_iff.2 (Array.getElem_mem hk)

namespace Fr

variable {V B V' B' : ID → Prop} {f g h : Func}

theorem refl : Fr V B f f := ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem trans (h1 : Fr V B f g) (h2 : Fr V B g h) : Fr V B f h :=
  ⟨h2.blocks.trans h1.blocks, h2.ownAux.trans h1.ownAux, h2.vsize.trans h1.vsize,
    fun x hx => (h2.value x hx).trans (h1.value x hx),
    fun x hx => (h2.block x hx).trans (h1.block x hx)⟩

theorem mono (h : Fr V B f g) (hV : ∀ x, V x → V' x) (hB : ∀ x, B x → B' x) : Fr V' B' f g :=
  ⟨h.blocks, h.ownAux, h.vsize, fun x hx => h.value x (fun h' => hx (hV x h')),
    fun x hx => h.block x (fun h' => hx (hB x h'))⟩

theorem modV (h : Fr V B f g) {v : ID} (hv : V v) (k : Value → Value) : Fr V B f (g.modV v k) where
  blocks := h.blocks
  ownAux := h.ownAux
  vsize := by
    show (g.valueTab.modify v (Option.map k)).size = _
    rw [Array.size_modify]; exact h.vsize
  value x hx := by
    rw [value?_modV, if_neg (fun e : v = x => hx (e ▸ hv))]; exact h.value x hx
  block := h.block

theorem modB (h : Fr V B f g) {b : ID} (hb : B b) (k : Block → Block) : Fr V B f (g.modB b k) where
  blocks := h.blocks
  ownAux := h.ownAux
  vsize := h.vsize
  value := h.value
  block x hx := by
    rw [block?_modB, if_neg (fun e : b = x => hx (e ▸ hb))]; exact h.block x hx

theorem setEntry (h : Fr V B f g) (e : ID) : Fr V B f { g with entry := e } :=
  ⟨h.blocks, h.ownAux, h.vsize, h.value, h.block⟩

end Fr

theorem SameUnpos.refl {f : Func} : SameUnpos f f := fun _ => rfl

theorem SameUnpos.trans {f g h : Func} (h1 : SameUnpos f g) (h2 : SameUnpos g h) : SameUnpos f h :=
  fun y => (h2 y).trans (h1 y)

theorem SameUnpos.getB {f g : Func} (h : SameUnpos f g) (y : ID) :
    Block.unpos (g.getB y) = Block.unpos (f.getB y) := by
  have := h y
  unfold Func.getB
  revert this
  cases g.block? y <;> cases f.block? y <;> intro this
  · rfl
  · simp at this
  · simp at this
  · exact Option.some.inj this

theorem SameUnpos.getB_values {f g : Func} (h : SameUnpos f g) (y : ID) :
    (g.getB y).values = (f.getB y).values := by
  have := congrArg Block.values (h.getB y); exact this

theorem SameUnpos.getB_preds {f g : Func} (h : SameUnpos f g) (y : ID) :
    (g.getB y).preds = (f.getB y).preds := by
  have := congrArg Block.preds (h.getB y); exact this

/-! ## The pieces -/

theorem endScan_mem (f : Func) : ∀ (l : Nat) (o : Bool) (vs : List ID) (v : ID) (l' : Nat) (o' : Bool),
    endScan f l o vs = (some v, l', o') → v ∈ vs
  | _, _, [], _, _, _, h => by cases h
  | l, o, w :: vs, v, l', o', h => by
    unfold endScan at h
    simp only at h
    split at h
    · exact List.mem_cons_of_mem _ (endScan_mem f _ _ vs v l' o' h)
    · split at h
      · cases h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (endScan_mem f _ _ vs v l' o' h)

private theorem endIf {V : ID → Prop} {f f1 : Func} {next : ID} (P : Prop) [Decidable P]
    (k : Block → Block) (hk : ∀ B, Block.unpos (k B) = Block.unpos B)
    (hF : Fr V (fun x => x = next) f f1) (hU : SameUnpos f f1) (hE : f1.entry = f.entry) :
    Fr V (fun x => x = next) f (if P then f1.modB next k else f1) ∧
      SameUnpos f (if P then f1.modB next k else f1) ∧
      (if P then f1.modB next k else f1).entry = f.entry := by
  split
  · refine ⟨hF.modB rfl _, fun y => ?_, hE⟩
    rw [block?_modB]
    split
    · subst_vars
      rw [← hU y]
      cases f1.block? y <;> simp [hk]
    · exact hU y
  · exact ⟨hF, hU, hE⟩

theorem moveEndStmt_frame (f : Func) (bx next : ID) :
    Fr (fun x => x ∈ (f.getB next).values) (fun x => x = next) f (moveEndStmt f bx next) ∧
      SameUnpos f (moveEndStmt f bx next) ∧ (moveEndStmt f bx next).entry = f.entry := by
  unfold moveEndStmt
  simp only
  split
  · exact ⟨Fr.refl, SameUnpos.refl, rfl⟩
  · obtain ⟨⟨hit, l, o⟩, hs⟩ : ∃ r, endScan f (f.getB bx).pos.line false
        (f.getB next).values.toList = r := ⟨_, rfl⟩
    rw [hs]
    cases hit with
    | none => exact endIf _ _ (fun _ => rfl) Fr.refl SameUnpos.refl rfl
    | some v =>
      have hv := endScan_mem f _ _ _ v l o hs
      exact endIf _ _ (fun _ => rfl) (Fr.refl.modV (Array.mem_toList_iff.1 hv) _)
        (fun y => by rw [block?_modV]) rfl

theorem retagBlock_frame (c bx : ID) (f : Func) :
    Fr (fun x => x ∈ (f.getB bx).values) (fun _ => False) f (retagBlock c bx f) ∧
      (∀ y, (retagBlock c bx f).block? y = f.block? y) ∧ (retagBlock c bx f).entry = f.entry := by
  unfold retagBlock
  rw [← Array.foldl_toList]
  refine foldl_inv (fun g => Fr (fun x => x ∈ (f.getB bx).values) (fun _ => False) f g ∧
      (∀ y, g.block? y = f.block? y) ∧ g.entry = f.entry) _ _ _ ?_ ⟨Fr.refl, fun _ => rfl, rfl⟩
  intro v hv g ⟨hF, hB, hE⟩
  exact ⟨hF.modV (Array.mem_toList_iff.1 hv) _, fun y => (block?_modV _ _ _ _).trans (hB y), hE⟩

theorem retag_frame (c : ID) (run : Array ID) (f : Func) :
    Fr (fun x => ∃ y ∈ run.toList, x ∈ (f.getB y).values) (fun x => x ∈ run.toList) f
        (retag c run f) ∧ SameUnpos f (retag c run f) ∧ (retag c run f).entry = f.entry := by
  unfold retag
  refine foldl_inv (fun g => Fr (fun x => ∃ y ∈ run.toList, x ∈ (f.getB y).values)
      (fun x => x ∈ run.toList) f g ∧ SameUnpos f g ∧ g.entry = f.entry) _ _ _ ?_
    ⟨Fr.refl, SameUnpos.refl, rfl⟩
  intro k hk g ⟨hF, hU, hE⟩
  rw [List.mem_range] at hk
  have hk0 : run[k]! ∈ run.toList := getElem!_mem (by omega)
  have hk1 : run[k + 1]! ∈ run.toList := getElem!_mem (by omega)
  obtain ⟨mF, mU, mE⟩ := moveEndStmt_frame g run[k]! run[k + 1]!
  obtain ⟨rF, rB, rE⟩ := retagBlock_frame c run[k]! (moveEndStmt g run[k]! run[k + 1]!)
  have hU1 := hU.trans mU
  refine ⟨(hF.trans (mF.mono (fun x hx => ⟨run[k + 1]!, hk1, ?_⟩) (fun x hx => hx ▸ hk1))).trans
    (rF.mono (fun x hx => ⟨run[k]!, hk0, ?_⟩) (fun _ h => h.elim)), fun y => ?_, rE.trans (mE.trans hE)⟩
  · rw [← hU.getB_values]; exact hx
  · rw [← hU1.getB_values]; exact hx
  · rw [rB y]; exact hU1 y

theorem redirectPreds_frame (c : ID) (preds : Array Edge) (f : Func) :
    Fr (fun _ => False) (fun x => ∃ e ∈ preds.toList, e.b = x) f (redirectPreds c preds f) ∧
      (redirectPreds c preds f).entry = f.entry := by
  unfold redirectPreds
  refine foldl_inv (fun g => Fr (fun _ => False) (fun x => ∃ e ∈ preds.toList, e.b = x) f g ∧
    g.entry = f.entry) _ _ _ ?_ ⟨Fr.refl, rfl⟩
  intro i hi g ⟨hF, hE⟩
  rw [List.mem_range] at hi
  exact ⟨hF.modB ⟨_, getElem!_mem hi, rfl⟩ _, hE⟩

theorem killRun_frame (run : Array ID) (f : Func) :
    Fr (fun _ => False) (fun x => x ∈ run.toList) f (killRun run f) ∧
      (killRun run f).entry = f.entry := by
  unfold killRun
  refine foldl_inv (fun g => Fr (fun _ => False) (fun x => x ∈ run.toList) f g ∧
    g.entry = f.entry) _ _ _ ?_ ⟨Fr.refl, rfl⟩
  intro k hk g ⟨hF, hE⟩
  rw [List.mem_range] at hk
  exact ⟨hF.modB (getElem!_mem (by omega)) _, hE⟩

theorem valsOf_eq_getB (f : Func) (y : ID) : valsOf f y = (f.getB y).values := by
  unfold valsOf Func.getB
  cases f.block? y <;> rfl

theorem isPredOf_of_getB {f : Func} {b x : ID} {e : Edge} (he : e ∈ (f.getB b).preds.toList)
    (hx : e.b = x) : isPredOf f b x = true := by
  unfold isPredOf
  unfold Func.getB at he
  cases hb : f.block? b with
  | none =>
    rw [hb] at he
    have h0 : (default : Block).preds = #[] := rfl
    rw [Option.getD_none, h0] at he; simp at he
  | some B0 =>
    rw [hb] at he
    exact Array.any_eq_true'.2 ⟨e, Array.mem_toList_iff.1 he, by simp [hx]⟩

/-- **The frame of the plain fusion rewrite.** -/
theorem fuseRun_frame (f : Func) (b c : ID) (run : Array ID) (hc : c ∈ run.toList) :
    Fr (fun x => ∃ y ∈ run.toList, x ∈ (valsOf f y).toList)
        (fun x => x ∈ run.toList ∨ isPredOf f b x = true) f (fuseRun f b c run) ∧
      (fuseRun f b c run).entry = if f.entry = b then c else f.entry := by
  unfold fuseRun
  simp only
  obtain ⟨tF, tU, tE⟩ := retag_frame c run f
  generalize retag c run f = f1 at tF tU tE
  generalize run.foldl (init := #[]) (fun acc bx => acc ++ (f1.getB bx).values) = vals
  have hp : ((f1.modB c fun x => { x with values := vals }).getB b).preds = (f.getB b).preds := by
    rw [← tU.getB_preds]
    unfold Func.getB
    rw [block?_modB]
    split
    · rename_i heq; subst heq; cases f1.block? c <;> rfl
    · rfl
  rw [hp]
  let V : ID → Prop := fun x => ∃ y ∈ run.toList, x ∈ (valsOf f y).toList
  let B : ID → Prop := fun x => x ∈ run.toList ∨ isPredOf f b x = true
  have hF1 : Fr V B f f1 := tF.mono (fun x ⟨y, hy, hx⟩ => ⟨y, hy, by
    rw [valsOf_eq_getB]; exact Array.mem_toList_iff.2 hx⟩) (fun x hx => .inl hx)
  have hF2 : Fr V B f ((f1.modB c fun x => { x with values := vals }).modB c
      fun x => { x with preds := (f.getB b).preds }) :=
    (hF1.modB (.inl hc) _).modB (.inl hc) _
  have hE2 : ((f1.modB c fun x => { x with values := vals }).modB c
      fun x => { x with preds := (f.getB b).preds }).entry = f.entry := tE
  generalize ((f1.modB c fun x => { x with values := vals }).modB c
      fun x => { x with preds := (f.getB b).preds }) = f2 at hF2 hE2
  obtain ⟨rF, rE⟩ := redirectPreds_frame c (f.getB b).preds f2
  have hF3 := hF2.trans (rF.mono (fun _ h => h.elim)
    (fun x ⟨e, he, hx⟩ => .inr (isPredOf_of_getB he hx)))
  rw [← rE] at hE2
  generalize redirectPreds c (f.getB b).preds f2 = f3 at hF3 hE2
  have hF4 : Fr V B f (if f3.entry = b then { f3 with entry := c } else f3) ∧
      (if f3.entry = b then { f3 with entry := c } else f3).entry =
        if f.entry = b then c else f.entry := by
    rw [hE2]
    split
    · exact ⟨hF3.setEntry c, rfl⟩
    · exact ⟨hF3, hE2⟩
  simp only [beq_iff_eq]
  generalize (if f3.entry = b then { f3 with entry := c } else f3) = f4 at hF4
  obtain ⟨kF, kE⟩ := killRun_frame run f4
  exact ⟨hF4.1.trans (kF.mono (fun _ h => h.elim) (fun x hx => .inl hx)), kE.trans hF4.2⟩

end GoFV.Proof.FusePlain
