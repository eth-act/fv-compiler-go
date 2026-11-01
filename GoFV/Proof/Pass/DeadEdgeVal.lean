import GoFV.Proof.Pass.DeadEdge
import GoFV.Proof.Pass.CopyElimEdit
import GoFV.Opt.Deadcode

/-!
# Removing one edge: the `Phi` arguments

`removeEdgeG el` is `removeEdge` (`el = true`, `removeEdgeG_true`) or the same edit without
`removePhiArg`'s `phielimValue` step (`el = false`): the `Phi`s of the target lose the removed
edge's argument, the last argument moving to its slot (`dropArg`), like the predecessors.
`removeEdge_vw`: the values after `removeEdgeG false`; the CFG part is `edge_core`.
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Proof.CopyElim

/-- `removePhiArg`, with (`el`) or without the `phielimValue` step. -/
def removePhiArgG (el : Bool) (f : Func) (b phi : ID) (i : Nat) : Func :=
  let n := (f.getB b).preds.size
  let args := (f.getV phi).args
  let f := (f.decUses args[i]!).modV phi fun x => { x with args := (x.args.set! i args[n]!).pop }
  if el then (f.phielimValue phi).1 else f

/-- `removeEdge`, with (`el`) or without `phielimValue` on the target's `Phi`s. -/
def removeEdgeG (el : Bool) (f : Func) (b : ID) (i : Nat) : Func :=
  let e := (f.getB b).succs[i]!
  let c := e.b
  let j := e.i
  let f := (f.removeSucc b i).removePred c j
  (f.getB c).values.foldl (init := f) fun f v =>
    if (f.getV v).op == .Phi then removePhiArgG el f c v j else f

theorem removeEdgeG_true : removeEdgeG true = Func.removeEdge := by
  funext f b i; rfl

/-- The `Phi`'s argument list without slot `j` (the last, `m`, moves there). -/
def dropArg (j m : Nat) (u : Value) : Value := { u with args := (u.args.set! j u.args[m]!).pop }

/-- The `Phi`s among the values `l` lose argument `j`. -/
def dropPhis (l : List ID) (j m : Nat) (x : ID) (u : Value) : Value :=
  if x ∈ l ∧ u.op = .Phi then dropArg j m u else u

theorem strip_dropArg (j m : Nat) (u : Value) : strip (dropArg j m u) = dropArg j m (strip u) :=
  rfl

theorem getB_modV (F : Func) (v : ID) (g : Value → Value) (y : ID) :
    (F.modV v g).getB y = F.getB y := rfl

theorem getB_decUses (F : Func) (v : ID) (y : ID) : (F.decUses v).getB y = F.getB y := rfl

theorem block?_modV (F : Func) (v : ID) (g : Value → Value) (y : ID) :
    (F.modV v g).block? y = F.block? y := rfl

/-- `dropArg` with the moved argument given. -/
def dropArg' (j n : Nat) (args : Array ID) (x : Value) : Value :=
  { x with args := (x.args.set! j args[n]!).pop }

theorem vw_removePhiArg (F : Func) (c v : ID) (j : Nat) :
    vw (removePhiArgG false F c v j) =
      upd (vw F) v (dropArg' j (F.getB c).preds.size (F.getV v).args) := by
  unfold removePhiArgG
  simp only [Bool.false_eq_true, ite_false]
  show vw ((F.decUses _).modV v (dropArg' j (F.getB c).preds.size (F.getV v).args)) = _
  rw [vw_modV _ _ (dropArg' j (F.getB c).preds.size (F.getV v).args) (fun _ => rfl), vw_decUses]

theorem skel_removePhiArg (F : Func) (c v : ID) (j : Nat) :
    skel (removePhiArgG false F c v j) = skel F := by
  unfold removePhiArgG
  simp only [Bool.false_eq_true, ite_false]
  rw [skel_modV, skel_decUses]

theorem getB_removePhiArg (F : Func) (c v : ID) (j : Nat) :
    (removePhiArgG false F c v j).getB = F.getB := rfl

theorem block?_removePhiArg (F : Func) (c v : ID) (j : Nat) :
    (removePhiArgG false F c v j).block? = F.block? := rfl

theorem default_op_ne_phi : (default : Value).op ≠ .Phi := by decide

/-- The `Phi` step of `removeEdgeG false` over the values `l` (no duplicates): every `Phi` among
them loses argument `j`. -/
theorem vw_phiFold {c : ID} {j m : Nat} :
    ∀ (l : List ID) (F : Func), l.Nodup → (F.getB c).preds.size = m →
      vw (l.foldl (fun f v => if (f.getV v).op == .Phi then removePhiArgG false f c v j else f) F)
        = fun x => (vw F x).map (dropPhis l j m x)
  | [], F, _, _ => by funext x; cases h : vw F x <;> simp [dropPhis, h]
  | v :: l, F, hnd, hm => by
    rw [List.foldl_cons]
    obtain ⟨hvl, hnd'⟩ := List.nodup_cons.1 hnd
    split
    · rename_i hop
      have hm' : ((removePhiArgG false F c v j).getB c).preds.size = m := by
        rw [getB_removePhiArg]; exact hm
      rw [vw_phiFold l _ hnd' hm', vw_removePhiArg]
      funext x
      by_cases hxv : x = v
      · subst hxv
        rw [upd_self]
        cases hu : vw F x with
        | none =>
          rw [getV_of_vw_none hu] at hop
          exact absurd (by simpa using hop) default_op_ne_phi
        | some u =>
          obtain ⟨hgo, hga, -⟩ := getV_of_vw hu
          have hop' : u.op = .Phi := by rw [← hgo]; simpa using hop
          simp only [Option.map_some, dropPhis, hvl, false_and, ite_false, List.mem_cons_self,
            true_and, hop', ite_true, hm, dropArg, dropArg', hga]
      · rw [upd_ne _ _ _ hxv]
        congr 1
        funext u
        simp only [dropPhis, List.mem_cons, hxv, false_or]
    · rename_i hop
      rw [vw_phiFold l _ hnd' hm]
      funext x
      by_cases hxv : x = v
      · subst hxv
        cases hu : vw F x with
        | none => rfl
        | some u =>
          have hop' : u.op ≠ .Phi := by
            obtain ⟨hgo, -, -⟩ := getV_of_vw hu; rw [← hgo]; simpa using hop
          simp [dropPhis, hvl, hop']
      · congr 1
        funext u
        simp only [dropPhis, List.mem_cons, hxv, false_or]

theorem getB_of_skel {F G : Func} (h : skel G = skel F) : G.getB = F.getB := by
  simp only [skel, Prod.mk.injEq] at h
  funext y; unfold Func.getB Func.block?; rw [h.2.2.2.1]

theorem block?_of_skel {F G : Func} (h : skel G = skel F) : G.block? = F.block? := by
  simp only [skel, Prod.mk.injEq] at h
  funext y; unfold Func.block?; rw [h.2.2.2.1]

theorem skel_phielimValue (F : Func) (v : ID) : skel (F.phielimValue v).1 = skel F := by
  rcases phielimValue_cases F v with h | ⟨w, -, -, -, -, h⟩
  · rw [h]
  · rw [h]; exact skel_toCopy F v w

theorem skel_removePhiArgG (el : Bool) (F : Func) (c v : ID) (j : Nat) :
    skel (removePhiArgG el F c v j) = skel F := by
  cases el
  · exact skel_removePhiArg F c v j
  · unfold removePhiArgG
    simp only [ite_true]
    rw [skel_phielimValue, skel_modV, skel_decUses]

theorem skel_phiFoldG (el : Bool) (c : ID) (j : Nat) :
    ∀ (l : List ID) (F : Func),
      skel (l.foldl (fun f v => if (f.getV v).op == .Phi then removePhiArgG el f c v j else f) F)
        = skel F
  | [], _ => rfl
  | v :: l, F => by
    rw [List.foldl_cons, skel_phiFoldG el c j l]
    split
    · exact skel_removePhiArgG el F c v j
    · rfl

/-- The CFG part of `removeEdgeG`: only `removeSucc` and `removePred` touch blocks. -/
theorem skel_removeEdgeG (el : Bool) (F : Func) (b : ID) (i : Nat) :
    skel (removeEdgeG el F b i) =
      skel ((F.removeSucc b i).removePred (F.getB b).succs[i]!.b (F.getB b).succs[i]!.i) := by
  unfold removeEdgeG
  rw [← Array.foldl_toList, skel_phiFoldG]

/-- **`removeEdgeG false`** on an edge `b.succs[i] = ⟨c, j⟩`: the CFG part (`edge_core`), and
the `Phi`s of `c` lose argument `j`. -/
theorem removeEdge_false {F : Func} {B : Array ID} {b c : ID} {i j : Nat} (hX : XL F B)
    (hb : b ∈ B) (hi : i < (F.getB b).succs.size) (hbi : sOf F b i = some ⟨c, j⟩)
    (hnd : (F.getB c).values.toList.Nodup) :
    skel (removeEdgeG false F b i) = skel ((F.removeSucc b i).removePred c j) ∧
    vw (removeEdgeG false F b i) =
      fun x => (vw F x).map (dropPhis (F.getB c).values.toList j ((F.getB c).preds.size - 1) x) := by
  have he : (F.getB b).succs[i]! = ⟨c, j⟩ := by
    rw [getElem!_pos ((F.getB b).succs) _ hi]
    exact Option.some.inj ((Array.getElem?_eq_getElem hi).symm.trans hbi)
  refine ⟨by rw [skel_removeEdgeG, he], ?_⟩
  obtain ⟨-, hcj⟩ := hX.succ b hb i _ hbi
  dsimp only at hcj
  have hcs : 0 < (F.getB c).preds.size := by
    have := (Array.getElem?_eq_some_iff.1 hcj).1; omega
  obtain ⟨-, -, -, -, -, -, h7, h8, -, h10, -⟩ :=
    edge_core (n := (F.getB b).succs.size - 1) (m := (F.getB c).preds.size - 1) hX hb (by omega)
      (by omega) hbi (by omega)
  have hvals : (((F.removeSucc b i).removePred c j).getB c).values = (F.getB c).values := by
    have := congrArg Block.values (h8 c); simpa [bview] using this
  have hvw : vw ((F.removeSucc b i).removePred c j) = vw F := by
    funext x; unfold vw Func.value?; rw [h10]
  unfold removeEdgeG
  simp only [he]
  rw [← Array.foldl_toList, vw_phiFold (m := (F.getB c).preds.size - 1) _ _
    (by rw [hvals]; exact hnd) (by rw [h7]; simp), hvw, hvals]

end GoFV.Proof.Dead
