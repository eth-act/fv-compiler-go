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
    · rw [bview_updAt _ _ _ _ (fun _ => rfl), bview_updAt _ _ _ _ (fun _ => rfl),
        bview_updAt _ _ _ _ (fun _ => rfl)]
  · unfold Func.removeSucc
    simp only [block?_invalidateCFG, isSome_modB]
    split <;> simp only [isSome_modB]
  · unfold Func.removeSucc; split <;> rfl
  · unfold Func.removeSucc; split <;> rfl

end

end GoFV.Proof.Dead
