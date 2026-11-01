import GoFV.Proof.WF
import GoFV.SSA.Edges

/-!
# Removing one edge (`removeSucc`, `removePred`)

`XL F B`: the blocks `B` are in `F`'s table and their edges are crosslinked (the `predLink` and
`succLink` facts of `WF`, stated on `getB`). `removeSucc b i` followed by `removePred c j` for
the edge `b.succs[i] = ⟨c, j⟩` (the CFG part of `removeEdge`) keeps `XL`; successor slots are
renamed (`b`'s last successor moves to slot `i`), predecessor slots of `c` are permuted (the
last moves to slot `j`, `predIdx`) and the back indices of the two moved edges are fixed
(`edge_core`).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA

/-- Successor `k` of block `x`. -/
abbrev sOf (F : Func) (x : ID) (k : Nat) : Option Edge := (F.getB x).succs[k]?

/-- Predecessor `l` of block `y`. -/
abbrev pOf (F : Func) (y : ID) (l : Nat) : Option Edge := (F.getB y).preds[l]?

/-- The blocks `B` are in the table, with crosslinked edges among them. -/
structure XL (F : Func) (B : Array ID) : Prop where
  pres : ∀ x ∈ B, (F.block? x).isSome
  succ : ∀ x ∈ B, ∀ k e, sOf F x k = some e → e.b ∈ B ∧ pOf F e.b e.i = some ⟨x, k⟩
  pred : ∀ y ∈ B, ∀ l e, pOf F y l = some e → e.b ∈ B ∧ sOf F e.b e.i = some ⟨y, l⟩

theorem block?_modB (F : Func) (x : ID) (g : Block → Block) (y : ID) :
    (F.modB x g).block? y = if x = y then (F.block? y).map g else F.block? y := by
  unfold Func.modB Func.block?
  simp only [Array.getElem?_modify]
  split
  · cases F.blockTab[y]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rfl

theorem getB_modB {F : Func} {x : ID} (hx : (F.block? x).isSome) (g : Block → Block) (y : ID) :
    (F.modB x g).getB y = if x = y then g (F.getB y) else F.getB y := by
  unfold Func.getB
  rw [block?_modB]
  split
  · rename_i h
    subst h
    obtain ⟨bl, hbl⟩ := Option.isSome_iff_exists.1 hx
    rw [hbl]; rfl
  · rfl

theorem isSome_modB {F : Func} (x : ID) (g : Block → Block) (y : ID) :
    ((F.modB x g).block? y).isSome = (F.block? y).isSome := by
  rw [block?_modB]; split <;> simp

@[simp] theorem block?_invalidateCFG (F : Func) (y : ID) : F.invalidateCFG.block? y = F.block? y :=
  rfl

@[simp] theorem getB_invalidateCFG (F : Func) (y : ID) : F.invalidateCFG.getB y = F.getB y := rfl

@[simp] theorem value?_modB (F : Func) (x : ID) (g : Block → Block) (y : ID) :
    (F.modB x g).value? y = F.value? y := rfl

@[simp] theorem value?_invalidateCFG (F : Func) (y : ID) : F.invalidateCFG.value? y = F.value? y :=
  rfl

/-- `b`'s successor index `k` before `removeSucc b i` (`n` the last index). -/
def succIdx (i n k : Nat) : Nat := if k = i then n else k

/-- Rename the back index of the edge from successor slot `(b, n)` to `(b, i)`. -/
def renS (b : ID) (n i : Nat) (e : Edge) : Edge := if e = ⟨b, n⟩ then ⟨b, i⟩ else e

/-- `c`'s predecessor index `l` before `removePred c j` (`m` the last index). -/
def predIdx (j m l : Nat) : Nat := if l = j then m else l

/-- Rename the back index of the edge to predecessor slot `(c, m)` to `(c, j)`. -/
def renP (c : ID) (m j : Nat) (e : Edge) : Edge := if e = ⟨c, m⟩ then ⟨c, j⟩ else e

/-- The block without its edges. -/
def bview (bl : Block) : Block := { bl with succs := #[], preds := #[] }

/-- Update a block's successors. -/
def setS (h : Array Edge → Array Edge) (bl : Block) : Block := { bl with succs := h bl.succs }

/-- Update a block's predecessors. -/
def setP (h : Array Edge → Array Edge) (bl : Block) : Block := { bl with preds := h bl.preds }

@[simp] theorem setS_succs (h : Array Edge → Array Edge) (bl : Block) : (setS h bl).succs = h bl.succs := rfl
@[simp] theorem setS_preds (h : Array Edge → Array Edge) (bl : Block) : (setS h bl).preds = bl.preds := rfl
@[simp] theorem setP_succs (h : Array Edge → Array Edge) (bl : Block) : (setP h bl).succs = bl.succs := rfl
@[simp] theorem setP_preds (h : Array Edge → Array Edge) (bl : Block) : (setP h bl).preds = h bl.preds := rfl
@[simp] theorem bview_setS (h : Array Edge → Array Edge) (bl : Block) : bview (setS h bl) = bview bl := rfl
@[simp] theorem bview_setP (h : Array Edge → Array Edge) (bl : Block) : bview (setP h bl) = bview bl := rfl

/-- `G` with block `x` updated by `g`. -/
def updAt (x : ID) (g : Block → Block) (G : ID → Block) (y : ID) : Block :=
  if x = y then g (G y) else G y

theorem getB_modB_fun {F : Func} {x : ID} (hx : (F.block? x).isSome) (g : Block → Block) :
    (F.modB x g).getB = updAt x g F.getB := by
  funext y; rw [getB_modB hx]; rfl

@[simp] theorem updAt_setS_preds (x : ID) (h : Array Edge → Array Edge) (G : ID → Block) (y : ID) :
    (updAt x (setS h) G y).preds = (G y).preds := by
  unfold updAt; split <;> rfl

@[simp] theorem updAt_setP_succs (x : ID) (h : Array Edge → Array Edge) (G : ID → Block) (y : ID) :
    (updAt x (setP h) G y).succs = (G y).succs := by
  unfold updAt; split <;> rfl

theorem updAt_setS_succs (x : ID) (h : Array Edge → Array Edge) (G : ID → Block) (y : ID) :
    (updAt x (setS h) G y).succs = if x = y then h (G y).succs else (G y).succs := by
  unfold updAt; split <;> rfl

theorem updAt_setP_preds (x : ID) (h : Array Edge → Array Edge) (G : ID → Block) (y : ID) :
    (updAt x (setP h) G y).preds = if x = y then h (G y).preds else (G y).preds := by
  unfold updAt; split <;> rfl

section
variable {F : Func} {B : Array ID} {b : ID} {i n : Nat} {e2 : Edge}

theorem getB_removeSucc (hpb : (F.block? b).isSome) (hp2 : (F.block? e2.b).isSome)
    (hn : n + 1 = (F.getB b).succs.size) (he2 : sOf F b n = some e2) :
    (F.removeSucc b i).getB = if i = n then updAt b (setS Array.pop) F.getB else
      updAt b (setS Array.pop) (updAt e2.b (setP fun ps => ps.modify e2.i fun p => { p with i })
        (updAt b (setS fun ss => ss.set! i e2) F.getB)) := by
  have hsz : (F.getB b).succs.size - 1 = n := by omega
  have h2 : (F.getB b).succs[n]! = e2 := by
    have hlt : n < (F.getB b).succs.size := by omega
    rw [getElem!_pos ((F.getB b).succs) _ hlt]
    exact Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans he2)
  unfold Func.removeSucc
  simp only [hsz, h2]
  funext y
  rw [getB_invalidateCFG]
  by_cases hin : i = n
  · subst hin
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]
    rw [getB_modB_fun hpb]; rfl
  · have hne : (i != n) = true := by simpa using hin
    simp only [hne, ite_true, hin, ite_false]
    have hp1 : ((F.modB b (setS fun ss => ss.set! i e2)).block? e2.b).isSome := by
      rw [isSome_modB]; exact hp2
    have hp1b : (((F.modB b (setS fun ss => ss.set! i e2)).modB e2.b
        (setP fun ps => ps.modify e2.i fun p => { p with i })).block? b).isSome := by
      rw [isSome_modB, isSome_modB]; exact hpb
    show (((F.modB b (setS fun ss => ss.set! i e2)).modB e2.b
        (setP fun ps => ps.modify e2.i fun p => { p with i })).modB b (setS Array.pop)).getB y = _
    rw [getB_modB_fun hp1b, getB_modB_fun hp1, getB_modB_fun hpb]

theorem updAt_succs (x : ID) (g : Block → Block) (G : ID → Block) (y : ID) :
    (updAt x g G y).succs = if x = y then (g (G y)).succs else (G y).succs := by
  unfold updAt; split <;> rfl

theorem updAt_preds (x : ID) (g : Block → Block) (G : ID → Block) (y : ID) :
    (updAt x g G y).preds = if x = y then (g (G y)).preds else (G y).preds := by
  unfold updAt; split <;> rfl

theorem bview_updAt (x : ID) (g : Block → Block) (G : ID → Block) (y : ID)
    (hg : ∀ bl, bview (g bl) = bview bl) : bview (updAt x g G y) = bview (G y) := by
  unfold updAt; split
  · exact hg _
  · rfl

/-- **`removeSucc b i`**: `b`'s successors lose slot `i` (the last, `n`, moves there), the
moved edge's predecessor entry gets back index `i`; nothing else changes. -/
theorem removeSucc_spec (hX : XL F B) (hb : b ∈ B) (hn : n + 1 = (F.getB b).succs.size)
    (hi : i ≤ n) :
    (∀ k, sOf (F.removeSucc b i) b k = if k < n then sOf F b (succIdx i n k) else none) ∧
    (∀ x, x ≠ b → ∀ k, sOf (F.removeSucc b i) x k = sOf F x k) ∧
    (∀ y ∈ B, ∀ l, pOf (F.removeSucc b i) y l = (pOf F y l).map (renS b n i)) ∧
    (∀ y, ((F.removeSucc b i).getB y).preds.size = (F.getB y).preds.size) ∧
    (∀ y, ((F.removeSucc b i).getB y).succs.size =
      if b = y then n else (F.getB y).succs.size) ∧
    (∀ y, bview ((F.removeSucc b i).getB y) = bview (F.getB y)) ∧
    (∀ y, ((F.removeSucc b i).block? y).isSome = (F.block? y).isSome) ∧
    (F.removeSucc b i).valueTab = F.valueTab ∧ (F.removeSucc b i).blocks = F.blocks := by
  have hpb := hX.pres b hb
  have hnl : n < (F.getB b).succs.size := by omega
  obtain ⟨e2, he2⟩ : ∃ e2, sOf F b n = some e2 := ⟨_, Array.getElem?_eq_getElem hnl⟩
  obtain ⟨he2B, he2P⟩ := hX.succ b hb n e2 he2
  have hp2 := hX.pres e2.b he2B
  have hG := getB_removeSucc (i := i) hpb hp2 hn he2
  have hrenS : ∀ y ∈ B, ∀ l, (pOf F y l = some ⟨b, n⟩ ↔ y = e2.b ∧ l = e2.i) := by
    intro y hy l
    constructor
    · intro h
      have := (hX.pred y hy l _ h).2
      rw [he2] at this
      cases this; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact he2P
  have hsn : (F.getB b).succs.pop.size = n := by simp; omega
  refine ⟨fun k => ?_, fun x hx k => ?_, fun y hy l => ?_, fun y => ?_, fun y => ?_, fun y => ?_,
    fun y => ?_, ?_, ?_⟩
  · simp only [sOf, hG]
    split
    · rename_i hin; subst hin
      simp only [updAt, ite_true, setS_succs, Array.getElem?_pop]
      have hs : (F.getB b).succs.size - 1 = i := by omega
      rw [hs]; unfold succIdx
      by_cases hk : k < i
      · simp [hk, show k ≠ i by omega]
      · simp [hk]
    · rename_i hin
      have hP : ∀ (G : ID → Block) (h : Array Edge → Array Edge),
          (updAt e2.b (setP h) G b).succs = (G b).succs := by
        intro G h; unfold updAt; split <;> rfl
      rw [updAt_succs, if_pos rfl, setS_succs, Array.getElem?_pop, hP]
      have hs1 : (updAt b (setS fun ss => ss.set! i e2) F.getB b).succs =
          (F.getB b).succs.set! i e2 := by simp [updAt]
      rw [hs1]
      have hs : ((F.getB b).succs.set! i e2).size - 1 = n := by simp [Array.set!]; omega
      rw [hs]
      by_cases hk : k < n
      · rw [if_pos hk, if_pos hk]; unfold succIdx
        simp only [Array.set!, Array.getElem?_setIfInBounds]
        by_cases hki : i = k
        · subst hki
          simp only [ite_true, show i < (F.getB b).succs.size by omega]
          exact he2.symm
        · simp only [hki, ite_false, Ne.symm hki]
      · rw [if_neg hk, if_neg hk]
  · simp only [sOf, hG]
    split <;> simp [updAt, Ne.symm hx] <;> split <;> rfl
  · simp only [pOf, hG]
    have hr := hrenS y hy l
    have hgoal : (if e2.b = y ∧ i ≠ n then (F.getB y).preds.modify e2.i (fun p => { p with i })
        else (F.getB y).preds)[l]? = ((F.getB y).preds[l]?).map (renS b n i) := by
      by_cases hc : e2.b = y ∧ e2.i = l
      · obtain ⟨rfl, rfl⟩ := hc
        have hP : (F.getB e2.b).preds[e2.i]? = some ⟨b, n⟩ := he2P
        by_cases hin : i = n
        · subst hin; simp [hP, renS]
        · simp [hin, Array.getElem?_modify, hP, renS]
      · have hL : (if e2.b = y ∧ i ≠ n then (F.getB y).preds.modify e2.i (fun p => { p with i })
            else (F.getB y).preds)[l]? = (F.getB y).preds[l]? := by
          split
          · rename_i hh
            rw [Array.getElem?_modify]
            have : ¬ (e2.i = l) := fun h' => hc ⟨hh.1, h'⟩
            simp [this]
          · rfl
        rw [hL]
        cases h : (F.getB y).preds[l]? with
        | none => rfl
        | some e =>
          simp only [Option.map_some, Option.some.injEq]
          unfold renS; split
          · rename_i hh; subst hh
            exact absurd (hr.1 h) (fun h' => hc ⟨h'.1.symm, h'.2.symm⟩)
          · rfl
    rw [← hgoal]
    split
    · rename_i hin
      simp [updAt_setS_preds, hin]
    · rename_i hin
      simp only [updAt_setS_preds, updAt_setP_preds]
      by_cases he : e2.b = y <;> simp [he, hin]
  · rw [hG]; split
    · simp only [updAt_setS_preds]
    · simp only [updAt_setS_preds, updAt_setP_preds]
      split <;> simp
  · rw [hG]; split
    · rename_i hin; subst hin
      simp only [updAt_setS_succs]; split
      · rename_i h; subst h; simp; omega
      · rfl
    · simp only [updAt_setS_succs, updAt_setP_succs]
      by_cases hby : b = y
      · subst hby; simp [Array.set!]; omega
      · simp [hby]
  · rw [hG]; split
    · exact bview_updAt _ _ _ _ (fun _ => rfl)
    · rw [bview_updAt _ (setS Array.pop) _ _ (fun _ => rfl), bview_updAt _ (setP _) _ _
        (fun _ => rfl), bview_updAt _ (setS _) _ _ (fun _ => rfl)]
  · unfold Func.removeSucc
    simp only [block?_invalidateCFG, isSome_modB]
    by_cases h : (i != (F.getB b).succs.size - 1) = true <;>
      simp only [h, ite_true, ite_false, Bool.false_eq_true, isSome_modB]
  · unfold Func.removeSucc
    by_cases h : (i != (F.getB b).succs.size - 1) = true <;>
      simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> rfl
  · unfold Func.removeSucc
    by_cases h : (i != (F.getB b).succs.size - 1) = true <;>
      simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> rfl

/-- `XL` except at the predecessor slot `(c, j)` of the edge being removed: no successor points
there, and its entry need not point back. -/
structure XLx (F : Func) (B : Array ID) (c : ID) (j : Nat) : Prop where
  pres : ∀ x ∈ B, (F.block? x).isSome
  succ : ∀ x ∈ B, ∀ k e, sOf F x k = some e →
    e.b ∈ B ∧ pOf F e.b e.i = some ⟨x, k⟩ ∧ ¬ (e.b = c ∧ e.i = j)
  pred : ∀ y ∈ B, ∀ l e, ¬ (y = c ∧ l = j) → pOf F y l = some e →
    e.b ∈ B ∧ sOf F e.b e.i = some ⟨y, l⟩

variable {c : ID} {j m : Nat} {e3 : Edge}

theorem getB_removePred (hpc : (F.block? c).isSome) (hp3 : j ≠ m → (F.block? e3.b).isSome)
    (hm : m + 1 = (F.getB c).preds.size) (he3 : pOf F c m = some e3) :
    (F.removePred c j).getB = if j = m then updAt c (setP Array.pop) F.getB else
      updAt c (setP Array.pop) (updAt e3.b (setS fun ps => ps.modify e3.i fun p => { p with i := j })
        (updAt c (setP fun ss => ss.set! j e3) F.getB)) := by
  have hsz : (F.getB c).preds.size - 1 = m := by omega
  have h2 : (F.getB c).preds[m]! = e3 := by
    have hlt : m < (F.getB c).preds.size := by omega
    rw [getElem!_pos ((F.getB c).preds) _ hlt]
    exact Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans he3)
  unfold Func.removePred
  simp only [hsz, h2]
  funext x
  rw [getB_invalidateCFG]
  by_cases hjm : j = m
  · subst hjm
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]
    rw [getB_modB_fun hpc]; rfl
  · have hne : (j != m) = true := by simpa using hjm
    simp only [hne, ite_true, hjm, ite_false]
    have hp1 : ((F.modB c (setP fun ss => ss.set! j e3)).block? e3.b).isSome := by
      rw [isSome_modB]; exact hp3 hjm
    have hp1b : (((F.modB c (setP fun ss => ss.set! j e3)).modB e3.b
        (setS fun ps => ps.modify e3.i fun p => { p with i := j })).block? c).isSome := by
      rw [isSome_modB, isSome_modB]; exact hpc
    show (((F.modB c (setP fun ss => ss.set! j e3)).modB e3.b
        (setS fun ps => ps.modify e3.i fun p => { p with i := j })).modB c (setP Array.pop)).getB x
      = _
    rw [getB_modB_fun hp1b, getB_modB_fun hp1, getB_modB_fun hpc]

/-- **`removePred c j`**: `c`'s predecessors lose slot `j` (the last, `m`, moves there), the
moved edge's successor entry gets back index `j`; nothing else changes. -/
theorem removePred_spec (hX : XLx F B c j) (hc : c ∈ B) (hm : m + 1 = (F.getB c).preds.size)
    (hj : j ≤ m) :
    (∀ l, pOf (F.removePred c j) c l = if l < m then pOf F c (predIdx j m l) else none) ∧
    (∀ y, y ≠ c → ∀ l, pOf (F.removePred c j) y l = pOf F y l) ∧
    (∀ x ∈ B, ∀ k, sOf (F.removePred c j) x k = (sOf F x k).map (renP c m j)) ∧
    (∀ x, ((F.removePred c j).getB x).succs.size = (F.getB x).succs.size) ∧
    (∀ x, ((F.removePred c j).getB x).preds.size =
      if c = x then m else (F.getB x).preds.size) ∧
    (∀ x, bview ((F.removePred c j).getB x) = bview (F.getB x)) ∧
    (∀ x, ((F.removePred c j).block? x).isSome = (F.block? x).isSome) ∧
    (F.removePred c j).valueTab = F.valueTab ∧ (F.removePred c j).blocks = F.blocks := by
  have hpc := hX.pres c hc
  have hml : m < (F.getB c).preds.size := by omega
  obtain ⟨e3, he3⟩ : ∃ e3, pOf F c m = some e3 := ⟨_, Array.getElem?_eq_getElem hml⟩
  have hE3 : j ≠ m → e3.b ∈ B ∧ sOf F e3.b e3.i = some ⟨c, m⟩ := fun hjm =>
    hX.pred c hc m e3 (fun h => hjm h.2.symm) he3
  have hG := getB_removePred (j := j) hpc (fun hjm => hX.pres _ (hE3 hjm).1) hm he3
  have hsm : (F.getB c).preds.pop.size = m := by simp; omega
  refine ⟨fun l => ?_, fun y hy l => ?_, fun x hx k => ?_, fun x => ?_, fun x => ?_, fun x => ?_,
    fun x => ?_, ?_, ?_⟩
  · simp only [pOf, hG]
    split
    · rename_i hjm; subst hjm
      simp only [updAt, ite_true, setP_preds, Array.getElem?_pop]
      have hs : (F.getB c).preds.size - 1 = j := by omega
      rw [hs]; unfold predIdx
      by_cases hl : l < j
      · simp [hl, show l ≠ j by omega]
      · simp [hl]
    · rename_i hjm
      rw [updAt_setP_preds, if_pos rfl, Array.getElem?_pop, updAt_setS_preds]
      have hs1 : (updAt c (setP fun ss => ss.set! j e3) F.getB c).preds =
          (F.getB c).preds.set! j e3 := by simp [updAt]
      rw [hs1]
      have hs : ((F.getB c).preds.set! j e3).size - 1 = m := by simp [Array.set!]; omega
      rw [hs]
      by_cases hl : l < m
      · rw [if_pos hl, if_pos hl]; unfold predIdx
        simp only [Array.set!, Array.getElem?_setIfInBounds]
        by_cases hlj : j = l
        · subst hlj
          simp only [ite_true, show j < (F.getB c).preds.size by omega]
          exact he3.symm
        · simp only [hlj, ite_false, Ne.symm hlj]
      · rw [if_neg hl, if_neg hl]
  · simp only [pOf, hG]
    split <;> simp [updAt, Ne.symm hy] <;> split <;> rfl
  · simp only [sOf, hG]
    have hgoal : (if e3.b = x ∧ j ≠ m then (F.getB x).succs.modify e3.i (fun p => { p with i := j })
        else (F.getB x).succs)[k]? = ((F.getB x).succs[k]?).map (renP c m j) := by
      by_cases hjm : j = m
      · subst hjm
        simp only [ne_eq, not_true_eq_false, and_false, ite_false]
        cases (F.getB x).succs[k]? with
        | none => rfl
        | some e => simp only [Option.map_some, renP]; split <;> simp_all
      obtain ⟨-, he3P⟩ := hE3 hjm
      have hr : sOf F x k = some ⟨c, m⟩ ↔ x = e3.b ∧ k = e3.i := by
        constructor
        · intro h
          have := (hX.pred c hc m e3 (fun h' => hjm h'.2.symm) he3).2
          have h2 := (hX.succ x hx k _ h).2.1
          rw [he3] at h2
          cases h2; exact ⟨rfl, rfl⟩
        · rintro ⟨rfl, rfl⟩; exact he3P
      by_cases hcc : e3.b = x ∧ e3.i = k
      · obtain ⟨rfl, rfl⟩ := hcc
        have hP : (F.getB e3.b).succs[e3.i]? = some ⟨c, m⟩ := he3P
        simp [hjm, Array.getElem?_modify, hP, renP]
      · have hL : (if e3.b = x ∧ j ≠ m then (F.getB x).succs.modify e3.i (fun p => { p with i := j })
            else (F.getB x).succs)[k]? = (F.getB x).succs[k]? := by
          split
          · rename_i hh
            rw [Array.getElem?_modify]
            have : ¬ (e3.i = k) := fun h' => hcc ⟨hh.1, h'⟩
            simp [this]
          · rfl
        rw [hL]
        cases h : (F.getB x).succs[k]? with
        | none => rfl
        | some e =>
          simp only [Option.map_some, Option.some.injEq]
          unfold renP; split
          · rename_i hh; subst hh
            exact absurd (hr.1 h) (fun h' => hcc ⟨h'.1.symm, h'.2.symm⟩)
          · rfl
    rw [← hgoal]
    split
    · rename_i hjm
      simp [hjm]
    · rename_i hjm
      simp only [updAt_setP_succs, updAt_setS_succs]
      by_cases he : e3.b = x <;> simp [he, hjm]
  · rw [hG]; split
    · simp only [updAt_setP_succs]
    · simp only [updAt_setP_succs, updAt_setS_succs]
      split <;> simp
  · rw [hG]; split
    · rename_i hjm; subst hjm
      simp only [updAt_setP_preds]; split
      · rename_i h; subst h; simp; omega
      · rfl
    · simp only [updAt_setP_preds, updAt_setS_preds]
      by_cases hcy : c = x
      · subst hcy; simp [Array.set!]; omega
      · simp [hcy]
  · rw [hG]; split
    · exact bview_updAt _ _ _ _ (fun _ => rfl)
    · rw [bview_updAt _ (setP Array.pop) _ _ (fun _ => rfl), bview_updAt _ (setS _) _ _
        (fun _ => rfl), bview_updAt _ (setP _) _ _ (fun _ => rfl)]
  · unfold Func.removePred
    simp only [block?_invalidateCFG, isSome_modB]
    by_cases h : (j != (F.getB c).preds.size - 1) = true <;>
      simp only [h, ite_true, ite_false, Bool.false_eq_true, isSome_modB]
  · unfold Func.removePred
    by_cases h : (j != (F.getB c).preds.size - 1) = true <;>
      simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> rfl
  · unfold Func.removePred
    by_cases h : (j != (F.getB c).preds.size - 1) = true <;>
      simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> rfl

end

end GoFV.Proof.Dead
