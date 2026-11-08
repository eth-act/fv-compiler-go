import GoFV.Proof.Pass.DAEVal
import GoFV.Proof.Pass.DSEVal

variable [GoFV.SSA.Sem.Addrs]

/-!
# dead auto elim: the ops of `memOps` on related last arguments

A kept value whose last argument is memory- or tuple-shaped has an op of `DAE.memOps`; its
other arguments are equal in source and target. On such argument lists `L ++ [w]` and
`L ++ [w']` with `VR U w w'` (and source arguments that avoid `U`), each op of `memOps`
evaluates to related results: ops that ignore their arguments (`LocalAddr`, `GetCallerSP`,
`InlMark`, `GetG`), tuple ops (`Copy`, `Select0/1/N`, `MakeResult`), `Convert` (which ignores its
memory), loads (`Load`, atomic loads, `MemEq`: their pointers avoid `U`, so they read the same
bytes), and roots that are always stuck (`PanicBounds` only panics; the P3 atomics). The memory
roots and calls are in `DAERoot`/`DAECall`.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.DAE

variable {U : Blk → Prop}

theorem snoc_inj {L L' : List Val} {w w' : Val} (h : L ++ [w] = L' ++ [w']) : L = L' ∧ w = w' := by
  have := List.append_inj' h rfl
  exact ⟨this.1, by simpa using this.2⟩

theorem snoc_cons (L : List Val) (w : Val) : ∃ y rest, L ++ [w] = y :: rest := by
  cases L <;> simp

/-- Both sides of a list of at least two elements ending in `w`/`w'`, in constructor form. -/
theorem two_snoc (x : Val) (L : List Val) (w w' : Val) :
    ∃ y y' r r', x :: L ++ [w] = x :: y :: r ∧ x :: L ++ [w'] = x :: y' :: r' := by
  obtain ⟨y, r, h⟩ := snoc_cons L w
  obtain ⟨y', r', h'⟩ := snoc_cons L w'
  exact ⟨y, y', r, r', by rw [List.cons_append, h], by rw [List.cons_append, h']⟩

theorem VRL.snoc (L : List Val) {w w' : Val} (h : VR U w w') : VRL U (L ++ [w]) (L ++ [w']) :=
  VRL.append (VRL.refl L) (.cons h .nil)

/-! ## Ops that ignore their arguments -/

theorem evalOp_argfree {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {ty : Ty}
    (hop : v.op = .LocalAddr ∨ v.op = .GetCallerSP ∨ v.op = .InlMark ∨ v.op = .GetG)
    (argv argv' : List Val) : evalOp env ctx fr v argv' ty = evalOp env ctx fr v argv ty := by
  rcases hop with h | h | h | h <;> simp only [evalOp, frameVal, h] <;> rfl

/-! ## Pure ops on the last argument -/

theorem evalOp_pureOp {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {ty : Ty} {argv : List Val}
    (hop : v.op = .Copy ∨ v.op = .Select0 ∨ v.op = .Select1 ∨ v.op = .SelectN ∨
      v.op = .MakeResult ∨ v.op = .Convert ∨ v.op = .Load ∨ v.op = .AtomicLoad32 ∨
      v.op = .AtomicLoad64 ∨ v.op = .AtomicLoadPtr ∨ v.op = .MemEq) :
    evalOp env ctx fr v argv ty = .ok (evalPure v.op ty v.auxInt v.aux argv) := by
  rcases hop with h | h | h | h | h | h | h | h | h | h | h <;>
    (simp only [evalOp, frameVal, h]; rfl)

theorem select_len (i : Nat) {l : List Val} (h : l.length ≠ 1) : Tuple.select i l = .poison := by
  unfold Tuple.select; split
  · simp at h
  · rfl

theorem selectN_len (k : Int64) {l : List Val} (h : l.length ≠ 1) : Tuple.selectN k l = .poison := by
  unfold Tuple.selectN; split
  · simp at h
  · rfl

theorem copy_len (ty : Ty) (k : Int64) (ax : Option AuxRef) {l : List Val} (h : l.length ≠ 1) :
    evalPure .Copy ty k ax l = .poison := by
  show (match l with | [x] => x | _ => .poison) = .poison
  split
  · simp at h
  · rfl

theorem convert_len (t : Ty) {l : List Val} (h : l.length ≠ 2) : PtrOps.convert t l = .poison := by
  unfold PtrOps.convert; split
  · simp at h
  · rfl

theorem loadOp_len (t : Ty) {l : List Val} (h : l.length ≠ 2) : loadOp t l = .poison := by
  unfold loadOp; split
  · simp at h
  · rfl

theorem atomicLoad_len (t : Ty) {l : List Val} (h : l.length ≠ 2) : atomicLoad t l = .poison := by
  unfold atomicLoad; split
  · simp at h
  · rfl

theorem memEq_len {l : List Val} (h : l.length ≠ 4) : memEq l = .poison := by
  unfold memEq; split
  · simp at h
  · rfl

theorem len_snoc (L : List Val) (w : Val) : (L ++ [w]).length = L.length + 1 := by simp

theorem select_rel (i : Nat) (L : List Val) {w w' : Val} (h : VR U w w') :
    VR U (Tuple.select i (L ++ [w])) (Tuple.select i (L ++ [w'])) := by
  cases L with
  | cons x L =>
    rw [select_len i (by simp), select_len i (by simp)]; exact .refl _
  | nil =>
    cases h with
    | refl => exact .refl _
    | mem => exact .refl _
    | tuple h => exact h.getD i

theorem selectN_rel (k : Int64) (L : List Val) {w w' : Val} (h : VR U w w') :
    VR U (Tuple.selectN k (L ++ [w])) (Tuple.selectN k (L ++ [w'])) := by
  cases L with
  | cons x L =>
    rw [selectN_len k (by simp), selectN_len k (by simp)]; exact .refl _
  | nil =>
    cases h with
    | refl => exact .refl _
    | mem => exact .refl _
    | tuple h =>
      simp only [List.nil_append, Tuple.selectN]
      split
      · exact .refl _
      · exact h.getD _

theorem copy_rel (ty : Ty) (k : Int64) (ax : Option AuxRef) (L : List Val) {w w' : Val}
    (h : VR U w w') :
    VR U (evalPure .Copy ty k ax (L ++ [w])) (evalPure .Copy ty k ax (L ++ [w'])) := by
  cases L with
  | nil => exact h
  | cons x L => rw [copy_len _ _ _ (by simp), copy_len _ _ _ (by simp)]; exact .refl _

theorem convert_eq (t : Ty) (L : List Val) (w w' : Val) :
    PtrOps.convert t (L ++ [w']) = PtrOps.convert t (L ++ [w]) := by
  cases L with
  | nil => rw [convert_len t (by simp), convert_len t (by simp)]
  | cons x L => cases L with
    | nil => rfl
    | cons z L => rw [convert_len t (by simp), convert_len t (by simp)]

/-! ## Loads -/

theorem loadOp_eq (hU : TempU U) (t : Ty) (L : List Val) {w w' : Val} (h : VR U w w')
    (hav : ∀ a ∈ L, Val.Avoids U a) : loadOp t (L ++ [w']) = loadOp t (L ++ [w]) := by
  match L, hav with
  | [x], hav =>
    cases h with
    | refl => rfl
    | tuple => cases x <;> rfl
    | mem hm =>
      simp only [List.cons_append, List.nil_append, loadOp]
      cases hp : x.asPtrWord with
      | none => rfl
      | some p => exact EqOff.load hm t p (asPtrWord_notU hU (hav _ List.mem_cons_self) hp)
  | [], _ => rw [loadOp_len t (by simp), loadOp_len t (by simp)]
  | _ :: _ :: _, _ => rw [loadOp_len t (by simp), loadOp_len t (by simp)]

theorem atomicLoad_rel (hU : TempU U) (t : Ty) (L : List Val) {w w' : Val} (h : VR U w w')
    (hav : ∀ a ∈ L, Val.Avoids U a) :
    VR U (atomicLoad t (L ++ [w])) (atomicLoad t (L ++ [w'])) := by
  match L, hav with
  | [x], hav =>
    cases h with
    | refl => exact .refl _
    | tuple => cases x <;> exact .refl _
    | mem hm =>
      simp only [List.cons_append, List.nil_append, atomicLoad]
      cases hp : x.asPtrWord with
      | none => exact .refl _
      | some p =>
        have hu : ¬ U p.blk := asPtrWord_notU hU (hav _ List.mem_cons_self) hp
        split
        · rename_i heq
          cases heq
          split
          · exact .tuple (.cons (.refl _) (.cons (.mem hm) .nil))
          · rw [EqOff.load hm _ p hu]
            exact .tuple (.cons (.refl _) (.cons (.mem hm) .nil))
        · exact .refl _
  | [], _ => rw [atomicLoad_len t (by simp), atomicLoad_len t (by simp)]; exact .refl _
  | _ :: _ :: _, _ => rw [atomicLoad_len t (by simp), atomicLoad_len t (by simp)]; exact .refl _

theorem memEq_tuple (a b c : Val) (vs : List Val) : memEq [a, b, c, .tuple vs] = .poison := by
  unfold memEq; split
  · rename_i h; simp at h
  · rfl

theorem memEq_eq (hU : TempU U) (L : List Val) {w w' : Val} (h : VR U w w')
    (hav : ∀ a ∈ L, Val.Avoids U a) : memEq (L ++ [w']) = memEq (L ++ [w]) := by
  match L, hav with
  | [a, b, c], hav =>
    simp only [List.cons_append, List.nil_append]
    cases h with
    | refl => rfl
    | tuple => rw [memEq_tuple, memEq_tuple]
    | mem hm =>
      rcases c with ⟨w, n⟩ | _ | _ | _ | _ | _ | _ | _ | _ <;> try rfl
      simp only [memEq]
      cases hp : a.asPtrWord with
      | none => rfl
      | some p =>
      cases hq : b.asPtrWord with
      | none => rfl
      | some q =>
      have hp' : ¬ U p.blk := asPtrWord_notU hU (hav _ List.mem_cons_self) hp
      have hq' : ¬ U q.blk :=
        asPtrWord_notU hU (hav _ (List.mem_cons_of_mem _ List.mem_cons_self)) hq
      simp only [EqOff.read hm _ _ hp', EqOff.read hm _ _ hq']
  | [], _ => rw [memEq_len (by simp), memEq_len (by simp)]
  | [_], _ => rw [memEq_len (by simp), memEq_len (by simp)]
  | [_, _], _ => rw [memEq_len (by simp), memEq_len (by simp)]
  | _ :: _ :: _ :: _ :: _, _ => rw [memEq_len (by simp), memEq_len (by simp)]

end GoFV.Proof.DAE
