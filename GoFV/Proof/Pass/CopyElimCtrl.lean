import GoFV.Proof.Pass.CopyElimSweep
import GoFV.Proof.Pass.CopyElimRel

/-!
# copyelim's control step and the final relation

After `phielim` (`G`), copyelim replaces each copy control `c` of a block by its argument
(`rc G c`), one block at a time. `replaceControl` changes only the block's controls (and use
counts); `pmap G k cs` is a control array whose first `k` entries are replaced. `argRel_of_join`
turns `Join` with a non-copy into `ArgRel` once every listed value's arguments are non-copies.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.DomCert GoFV.Opt GoFV.Proof

/-- A control after copyelim's control step. -/
def rc (G : Func) (c : ID) : ID := if (G.getV c).op == .Copy then (G.getV c).args[0]! else c

/-- Replace the controls of a block. -/
def setCtl (h : Array ID → Array ID) (blk : Block) : Block := { blk with controls := h blk.controls }

/-- The first `k` controls replaced. -/
def pmap (G : Func) (k : Nat) (cs : Array ID) : Array ID :=
  cs.mapIdx fun j c => if j < k then rc G c else c

/-- What the control step keeps. -/
def cskel (F : Func) : ID × Nat × Array ID × Option AuxRef × Nat × Nat :=
  (F.entry, F.bidLast, F.blocks, F.ownAux, F.valueTab.size, F.blockTab.size)

theorem pmap_get (G : Func) (k : Nat) (cs : Array ID) (i : Nat) :
    (pmap G k cs)[i]? = cs[i]?.map fun c => if i < k then rc G c else c := by
  unfold pmap; rw [Array.getElem?_mapIdx]

theorem pmap_zero (G : Func) (cs : Array ID) : pmap G 0 cs = cs := by
  apply Array.ext_getElem?; intro i
  rw [pmap_get]; cases cs[i]? <;> simp

theorem pmap_full (G : Func) (cs : Array ID) : pmap G cs.size cs = cs.map (rc G) := by
  apply Array.ext_getElem?; intro i
  rw [pmap_get, Array.getElem?_map]
  cases h : cs[i]? with
  | none => rfl
  | some c =>
    have : i < cs.size := (Array.getElem?_eq_some_iff.1 h).1
    simp [this]

theorem pmap_succ (G : Func) (cs : Array ID) {k : Nat} (hk : k < cs.size) :
    (pmap G k cs).set! k (rc G cs[k]) = pmap G (k + 1) cs := by
  apply Array.ext_getElem?; intro i
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, pmap_get, pmap_get]
  have hsz : (pmap G k cs).size = cs.size := by simp [pmap]
  by_cases hki : k = i
  · subst hki
    rw [ite_eq_left rfl, ite_eq_left (by omega), Array.getElem?_eq_getElem hk]
    simp
  · rw [ite_eq_right hki]
    cases cs[i]? with
    | none => rfl
    | some c =>
      by_cases hlt : i < k
      · simp [hlt, show i < k + 1 by omega]
      · simp [hlt, show ¬ i < k + 1 by omega]

theorem pmap_succ_same (G : Func) (cs : Array ID) {k : Nat} (hk : k < cs.size)
    (h : rc G cs[k] = cs[k]) : pmap G k cs = pmap G (k + 1) cs := by
  apply Array.ext_getElem?; intro i
  rw [pmap_get, pmap_get]
  by_cases hki : i = k
  · subst hki
    rw [Array.getElem?_eq_getElem hk]
    simp [h]
  · cases cs[i]? with
    | none => rfl
    | some c =>
      by_cases hlt : i < k
      · simp [hlt, show i < k + 1 by omega]
      · simp [hlt, show ¬ i < k + 1 by omega]

theorem blockTab_replaceControl (H : Func) (b : ID) (i : Nat) (x : ID) (y : ID) :
    (H.replaceControl b i x).blockTab[y]? =
      if b = y then (H.blockTab[y]?).map (Option.map (setCtl fun cs => cs.set! i x))
      else H.blockTab[y]? := by
  unfold Func.replaceControl Func.incUses Func.decUses Func.modV Func.modB
  simp only [Array.getElem?_modify]
  rfl

theorem vw_replaceControl (H : Func) (b : ID) (i : Nat) (x : ID) :
    vw (H.replaceControl b i x) = vw H := by
  unfold Func.replaceControl
  rw [vw_incUses]
  show vw (H.decUses _) = vw H
  exact vw_decUses _ _

theorem cskel_replaceControl (H : Func) (b : ID) (i : Nat) (x : ID) :
    cskel (H.replaceControl b i x) = cskel H := by
  simp [cskel, Func.replaceControl, Func.incUses, Func.decUses, Func.modV, Func.modB]

theorem block?_replaceControl (H : Func) (b : ID) (i : Nat) (x : ID) (y : ID) :
    (H.replaceControl b i x).block? y =
      if b = y then (H.block? y).map (setCtl fun cs => cs.set! i x) else H.block? y := by
  unfold Func.block?
  rw [blockTab_replaceControl]
  split
  · cases H.blockTab[y]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rfl

theorem cfgView_replaceControl (H : Func) (b : ID) (i : Nat) (x : ID) :
    cfgView (H.replaceControl b i x) = cfgView H := by
  have hbt : (H.replaceControl b i x).blockTab =
      H.blockTab.modify b (Option.map (setCtl fun cs => cs.set! i x)) := rfl
  have hmap : (H.blockTab.modify b (Option.map (setCtl fun cs => cs.set! i x))).map
      (Option.map fun b => { (default : Block) with id := b.id, succs := b.succs, preds := b.preds }) =
      H.blockTab.map
      (Option.map fun b => { (default : Block) with id := b.id, succs := b.succs, preds := b.preds }) := by
    apply Array.ext_getElem?
    intro j
    simp only [Array.getElem?_map, Array.getElem?_modify]
    split
    · cases H.blockTab[j]? with
      | none => rfl
      | some o => cases o <;> rfl
    · rfl
  unfold cfgView
  rw [hbt, hmap]
  rfl

theorem getV_congr {H G : Func} (h : vw H = vw G) (x : ID) :
    (H.getV x).op = (G.getV x).op ∧ (H.getV x).args = (G.getV x).args := by
  cases hx : vw G x with
  | none =>
    have hx' : vw H x = none := by rw [h]; exact hx
    rw [getV_of_vw_none hx, getV_of_vw_none hx']
    exact ⟨rfl, rfl⟩
  | some u =>
    have hx' : vw H x = some u := by rw [h]; exact hx
    obtain ⟨h1, h2, -⟩ := getV_of_vw hx
    obtain ⟨h1', h2', -⟩ := getV_of_vw hx'
    exact ⟨h1'.trans h1.symm, h2'.trans h2.symm⟩

theorem value_of_vw {g : Func} {x : ID} {u : Value} (h : vw g x = some u) :
    ∃ u', g.value? x = some u' ∧ u'.op = u.op ∧ u'.args = u.args ∧ u'.type = u.type ∧
      u'.block = u.block ∧ u'.aux = u.aux ∧ u'.auxInt = u.auxInt := by
  obtain ⟨u', h1, rfl⟩ := vw_eq_some h
  exact ⟨u', h1, rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {tabs : Tables} {ce : CheckEnv} {f G : Func}

/-- `Join` with a non-copy is `ArgRel` once arguments of listed values are non-copies. -/
theorem argRel_of_join (hset : Settled f (vw G)) {g : Func}
    (hg : vw g = vw G) {a c : ID} (ha : Listed f a) (hj : Join (vw G) a c)
    (hc : cstep (vw G) c = none) : ArgRel g a c := by
  obtain ⟨n, hs⟩ := hj.sink hc
  cases hs with
  | sink _ => exact .inl rfl
  | @step _ y _ n hy hs' =>
    obtain ⟨u, hu, hop, hargs⟩ := cstep_some_some hy
    have hys : cstep (vw G) y = none := hset a ha u hu y (by rw [hargs]; simp)
    obtain ⟨rfl, -⟩ := hs'.of_sink hys
    rw [← hg] at hu
    obtain ⟨u', h1, h2, h3, -⟩ := value_of_vw hu
    exact .inr ⟨u', h1, h2.trans hop, h3.trans hargs⟩

end

end GoFV.Proof.CopyElim
