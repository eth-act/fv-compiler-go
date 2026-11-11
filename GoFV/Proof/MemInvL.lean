import GoFV.Proof.MemInv
import GoFV.SSA.Sem.RunL

variable [GoFV.SSA.Sem.Addrs]

/-!
# The memories of a lowered value (issue #385, `docs/plans/proofs3.md` §10)

`Val.widen` and so `Val.retypeL` (a value read at a lowered shape) keep the memories inside a
value (`widen_mems`, `MemsOK.retypeL`): the read-only symbols in every memory a run holds carry
over to the values `runL` and `runLoc` read.
-/

namespace GoFV.Proof.MemInv

open GoFV.SSA GoFV.SSA.Sem

variable {P : Mem → Prop}

mutual
theorem widen_mems : (t : Ty) → (v : Val) → ∀ m ∈ (v.widen t).mems, m ∈ v.mems
  | t, .tuple vs => fun m hm => by
    cases t with
    | tuple ts =>
      simp only [Val.widen, Val.mems] at hm ⊢
      exact widenList_mems ts vs m hm
    | _ => simpa [Val.widen] using hm
  | t, .int w x => fun m hm => by
    cases t <;> simp only [Val.widen] at hm <;> (try split at hm) <;> simp [Val.mems] at hm
  | t, .bool b => fun m hm => by cases t <;> simp [Val.widen, Val.mems] at hm
  | t, .mem m' => fun m hm => by cases t <;> simpa [Val.widen] using hm
  | t, .ptr p => fun m hm => by cases t <;> simp [Val.widen, Val.mems] at hm
  | t, .agg vs => fun m hm => by cases t <;> simpa [Val.widen] using hm
  | t, .blob bs => fun m hm => by cases t <;> simp [Val.widen, Val.mems] at hm
  | t, .empty => fun m hm => by cases t <;> simp [Val.widen, Val.mems] at hm
  | t, .poison => fun m hm => by cases t <;> simp [Val.widen, Val.mems] at hm
theorem widenList_mems : (ts : List Ty) → (vs : List Val) →
    ∀ m ∈ Val.memsL (Val.widenList ts vs), m ∈ Val.memsL vs
  | t :: ts, v :: vs => fun m hm => by
    simp only [Val.widenList, Val.memsL, List.mem_append] at hm ⊢
    rcases hm with h | h
    · exact .inl (widen_mems t v m h)
    · exact .inr (widenList_mems ts vs m h)
  | [], vs => fun m hm => by simpa [Val.widenList] using hm
  | _ :: _, [] => fun m hm => by simpa [Val.widenList] using hm
end

theorem MemsOK.retypeL {v : Val} (h : MemsOK P v) (t : Ty) : MemsOK P (v.retypeL t) :=
  fun m hm => h m (widen_mems t v m (retype_mems t _ m hm))

end GoFV.Proof.MemInv
