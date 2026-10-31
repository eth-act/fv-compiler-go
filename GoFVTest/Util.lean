import GoFV.Util.PdqSort
import GoFV.Util.SparseSet
import GoFV.Util.SparseMapPos

/-!
Non-vacuity witnesses and axiom checks for `GoFV.Util` (#41). The concrete results are
evaluated by the kernel (`decide +kernel`), so the definitions stay kernel-reducible.
-/

namespace GoFVTest.Util

open GoFV.Util

/-! ## PdqSort -/

-- Insertion sort path (n ≤ 12).
example : PdqSort.sortBy (fun a b : Nat => decide (a < b)) #[3, 1, 2] = #[1, 2, 3] := by
  decide +kernel

-- pdqsort path (n = 20 > 12): reversed input is detected (decreasing hint) and reversed.
example : PdqSort.sortBy (fun a b : Nat => decide (a < b))
    #[19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0] =
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] := by
  decide +kernel

-- Unstable with ties: `slices.SortFunc` by the first component (pairs `(key, position)`).
example : PdqSort.sortFunc (fun a b : Nat × Nat => (a.1 : Int) - b.1)
    #[(1, 0), (0, 1), (1, 2), (0, 3)] = #[(0, 1), (0, 3), (1, 0), (1, 2)] := by
  decide +kernel

example : (PdqSort.sortBy (fun a b : Nat => decide (a < b)) #[3, 1, 2]).Perm #[3, 1, 2] :=
  PdqSort.sortBy_perm _ _

example : (PdqSort.sortFunc (fun _ _ : Nat => -1) #[3, 1, 2]).Perm #[3, 1, 2] :=
  PdqSort.sortFunc_perm _ _

/-- info: 'GoFV.Util.PdqSort.sortBy_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms PdqSort.sortBy_perm

/-- info: 'GoFV.Util.PdqSort.sortFunc_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms PdqSort.sortFunc_perm

/-! ## Sparse set and maps -/

-- `remove` moves the last element into the hole: `[2, 0, 3]` minus `2` is `[3, 0]`.
example : (((SparseSet.new 4).add 2 |>.add 0 |>.add 3 |>.remove 2).contents) = #[3, 0] := by
  decide +kernel

example : ((SparseSet.new 4).add 2 |>.add 0 |>.pop).1 = 0 := by decide +kernel

example : ((SparseSet.new 4).add 2).WF := SparseSet.wf_add (SparseSet.wf_new 4) (by decide)

example : (((SparseSet.new 4).add 2).remove 2).WF :=
  SparseSet.wf_remove (SparseSet.wf_add (SparseSet.wf_new 4) (by decide)) 2

example : ((SparseSet.new 4).add 2).contains 2 = decide (2 ∈ ((SparseSet.new 4).add 2).dense) :=
  SparseSet.contains_eq (SparseSet.wf_add (SparseSet.wf_new 4) (by decide)) 2

example : 1 ∈ (((SparseSet.new 4).add 2 |>.add 1).remove 2).dense ↔
    1 ∈ ((SparseSet.new 4).add 2 |>.add 1).dense ∧ 1 ≠ 2 :=
  SparseSet.mem_remove
    (SparseSet.wf_add (SparseSet.wf_add (SparseSet.wf_new 4) (by decide)) (by decide)) 2 1

example : (((SparseMap.new 4 : SparseMap Int).set 1 5 |>.set 3 7 |>.set 1 6).contents.map
    (fun e => (e.key, e.val))) = #[(1, 6), (3, 7)] := by
  decide +kernel

example : ((SparseMap.new 4 : SparseMap Int).set 1 5).WF :=
  SparseMap.wf_set (SparseMap.wf_new 4) (by decide) 5

example : (((SparseMap.new 4 : SparseMap Int).set 1 5).remove 1).WF :=
  SparseMap.wf_remove (SparseMap.wf_set (SparseMap.wf_new 4) (by decide) 5) 1

example : SparseMapPos.get ((SparseMapPos.new 4 : SparseMapPos Nat).set 2 9 0 |>.remove 2) 2 = -1 := by
  decide +kernel

example : ((SparseMapPos.new 4 : SparseMapPos Nat).set 2 9 0).WF :=
  SparseMapPos.wf_set (SparseMap.wf_new 4) (by decide) 9 0

/-- info: 'GoFV.Util.SparseSet.mem_remove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SparseSet.mem_remove

/-- info: 'GoFV.Util.SparseMap.wf_remove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SparseMap.wf_remove

end GoFVTest.Util
