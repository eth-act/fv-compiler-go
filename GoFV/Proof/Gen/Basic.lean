import GoFV.SSA.Sem.RunProg

/-!
# `runProg` runs between related states, and the ID layout (`docs/plans/proofs3.md` §3)

`PStep`/`PStar` are the steps of `runProg H L ps ret` that continue (an executed Prog or a
returning hook), as `MStep`/`MStar` are for `runMach` (`GoFV/SSA/Sem/LocMatch.lean`);
`PStar.runProg` relates them to `runProg`. For P0's ID layout `Link.byId`, a list with distinct
IDs below `2^32` puts each Prog at its own address and lets it fall through to its list successor
(`progAt?_byId`, `nextAddr_byId`).
-/

namespace GoFV.Proof.Gen

open GoFV.Arm64 GoFV.Asm

/-! ## Steps of `runProg` -/

/-- One step of `runProg H L ps ret` that continues: a Prog executed, or a hook that returns.
The PC is not yet `ret`. -/
inductive PStep (H : Hooks) (L : Link) (ps : List Prog) (ret : BitVec 64) :
    MState → MState → Prop where
  | prog {s s' : MState} {p : Prog} : s.pc ≠ ret → progAt? L ps s.pc = some p →
      progStep L p s = .ok s' → PStep H L ps ret s s'
  | hook {s s' : MState} : s.pc ≠ ret → progAt? L ps s.pc = none → H.call s = some (.ret s') →
      PStep H L ps ret s s'

/-- Zero or more `PStep`s. -/
inductive PStar (H : Hooks) (L : Link) (ps : List Prog) (ret : BitVec 64) (s : MState) :
    MState → Prop where
  | refl : PStar H L ps ret s s
  | tail {s' s'' : MState} : PStar H L ps ret s s' → PStep H L ps ret s' s'' →
      PStar H L ps ret s s''

namespace PStar

variable {H : Hooks} {L : Link} {ps : List Prog} {ret : BitVec 64}

theorem single {s s' : MState} (h : PStep H L ps ret s s') : PStar H L ps ret s s' :=
  .tail .refl h

theorem trans {s s' s'' : MState} (h : PStar H L ps ret s s') (h' : PStar H L ps ret s' s'') :
    PStar H L ps ret s s'' := by
  induction h' with
  | refl => exact h
  | tail _ hs ih => exact .tail ih hs

theorem head {s s' s'' : MState} (h : PStep H L ps ret s s') (h' : PStar H L ps ret s' s'') :
    PStar H L ps ret s s'' :=
  (single h).trans h'

end PStar

theorem PStep.runProg {H : Hooks} {L : Link} {ps : List Prog} {ret : BitVec 64} {s s' : MState}
    (h : PStep H L ps ret s s') (k : Nat) :
    GoFV.Arm64.runProg H L ps ret (k + 1) s = GoFV.Arm64.runProg H L ps ret k s' := by
  cases h with
  | prog hpc hp hs => simp [GoFV.Arm64.runProg, hpc, hp, hs]
  | hook hpc hp hh => simp [GoFV.Arm64.runProg, hpc, hp, hh]

/-- `PStar` is a prefix of `runProg`. -/
theorem PStar.runProg {H : Hooks} {L : Link} {ps : List Prog} {ret : BitVec 64} {s s' : MState}
    (h : PStar H L ps ret s s') :
    ∃ n, ∀ k, GoFV.Arm64.runProg H L ps ret (n + k) s = GoFV.Arm64.runProg H L ps ret k s' := by
  induction h with
  | refl => exact ⟨0, fun k => by simp⟩
  | tail _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, fun k => by rw [show n + 1 + k = n + (k + 1) by omega, hn, hstep.runProg]⟩

/-! ## The ID layout -/

section ById

variable {sym : Nat → BitVec 64} {text : BitVec 64} {a x : Int}

/-- The fall-through offset of the Prog at index `j` of a list with distinct IDs. -/
theorem nextOff_getElem (off : Prog → Int) (e : Int) :
    ∀ (ps : List Prog) (j : Nat) (hj : j < ps.length), (ps.map (·.id)).Nodup →
      Link.nextOff off e ps[j].id ps =
        some (if h : j + 1 < ps.length then off ps[j + 1] else e)
  | [], _, hj, _ => absurd hj (by simp)
  | [p], 0, _, _ => by simp [Link.nextOff]
  | [p], j + 1, hj, _ => absurd hj (by simp)
  | p :: q :: r, 0, _, _ => by simp [Link.nextOff]
  | p :: q :: r, j + 1, hj, hnd => by
    have hj' : j < (q :: r).length := by simpa using hj
    have hne : p.id ≠ (q :: r)[j].id := by
      intro h
      have hmem : (q :: r)[j].id ∈ (q :: r).map (·.id) :=
        List.mem_map.2 ⟨_, List.getElem_mem hj', rfl⟩
      simp only [List.map_cons, List.nodup_cons] at hnd
      exact hnd.1 (h ▸ by simpa using hmem)
    have hnd' : ((q :: r).map (·.id)).Nodup := (List.nodup_cons.1 (by simpa using hnd)).2
    have ih := nextOff_getElem off e (q :: r) j hj' hnd'
    simp only [List.getElem_cons_succ] at ih ⊢
    rw [Link.nextOff, if_neg hne, ih]
    simp

/-- The offset of a Prog of the list. -/
theorem off_byId {ps : List Prog} {p : Prog} (hp : p ∈ ps) :
    (Link.byId sym text a x ps).off p.id = some (4 * (p.id : Int)) := by
  simp only [Link.byId, Link.ofProgs]
  obtain ⟨q, hq⟩ : ∃ q, ps.find? (fun r => decide (r.id = p.id)) = some q := by
    cases h : ps.find? (fun r => decide (r.id = p.id)) with
    | none => exact absurd (List.find?_eq_none.1 h p hp) (by simp)
    | some q => exact ⟨q, rfl⟩
  have hqid : q.id = p.id := by simpa using List.find?_some hq
  rw [hq]
  simp [hqid]

/-- The address of the Prog with ID `id` of the list. -/
theorem addr_byId {ps : List Prog} {p : Prog} (hp : p ∈ ps) :
    (Link.byId sym text a x ps).addr p.id = some (text + BitVec.ofNat 64 (4 * p.id)) := by
  simp only [Link.addr, off_byId hp, Option.map_some]
  rw [show (4 * (p.id : Int)) = ((4 * p.id : Nat) : Int) by omega, BitVec.ofInt_natCast]
  rfl

/-- The largest ID of the list (0 if empty). -/
def maxId (ps : List Prog) : Nat := ps.foldl (fun m p => max m p.id) 0

private theorem le_foldl_max (ps : List Prog) (m : Nat) : m ≤ ps.foldl (fun m p => max m p.id) m := by
  induction ps generalizing m with
  | nil => exact Nat.le_refl _
  | cons p ps ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem foldl_max_ge : ∀ (ps : List Prog) (m : Nat) (p : Prog), p ∈ ps →
    p.id ≤ ps.foldl (fun m p => max m p.id) m
  | [], _, _, h => absurd h (by simp)
  | q :: ps, m, p, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right m p.id) (le_foldl_max ps _)
    · exact foldl_max_ge ps _ p h

private theorem foldl_max_lt (B : Nat) : ∀ (ps : List Prog) (m : Nat), m < B →
    (∀ p ∈ ps, p.id < B) → ps.foldl (fun m p => max m p.id) m < B
  | [], _, hm, _ => hm
  | q :: ps, m, hm, h => foldl_max_lt B ps _ (Nat.max_lt.2 ⟨hm, h q (by simp)⟩)
      (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem le_maxId {ps : List Prog} {p : Prog} (hp : p ∈ ps) : p.id ≤ maxId ps :=
  foldl_max_ge ps 0 p hp

theorem maxId_lt {ps : List Prog} {B : Nat} (hB : 0 < B) (h : ∀ p ∈ ps, p.id < B) : maxId ps < B :=
  foldl_max_lt B ps 0 hB h

/-- The fall-through address of the Prog at index `j` of a list with distinct IDs: the next
Prog's address, after the last one `4 (maxId + 1)` past the text base. -/
theorem nextAddr_byId {ps : List Prog} (hnd : (ps.map (·.id)).Nodup) {j : Nat}
    (hj : j < ps.length) :
    (Link.byId sym text a x ps).nextAddr ps[j].id =
      some (text + BitVec.ofNat 64
        (if h : j + 1 < ps.length then 4 * ps[j + 1].id else 4 * (maxId ps + 1))) := by
  simp only [Link.nextAddr, Link.byId, Link.ofProgs]
  rw [nextOff_getElem _ _ ps j hj hnd]
  simp only [Option.map_some]
  congr 2
  split
  · rw [show (4 * (ps[j + 1].id : Int)) = ((4 * ps[j + 1].id : Nat) : Int) by omega]
    exact BitVec.ofInt_natCast 64 _
  · rw [show (4 * ((ps.foldl (fun m p => max m p.id) 0 : Nat) + 1 : Int)) =
        ((4 * (maxId ps + 1) : Nat) : Int) by simp only [maxId]; omega]
    exact BitVec.ofInt_natCast 64 _

/-- Distinct small IDs give distinct addresses. -/
theorem addr_inj {text : BitVec 64} {i k : Nat} (hi : i < 2 ^ 34) (hk : k < 2 ^ 34)
    (h : text + BitVec.ofNat 64 (4 * i) = text + BitVec.ofNat 64 (4 * k)) : i = k := by
  have h1 : BitVec.ofNat 64 (4 * i) = BitVec.ofNat 64 (4 * k) := by
    have := congrArg (· - text) h
    simpa only [BitVec.add_comm text, BitVec.add_sub_cancel] using this
  have h' := congrArg BitVec.toNat h1
  simp only [BitVec.toNat_ofNat] at h'
  omega

/-- Distinct indices of a list with distinct IDs have distinct IDs. -/
theorem id_ne_of_nodup {ps : List Prog} (hnd : (ps.map (·.id)).Nodup) {i k : Nat}
    (hi : i < ps.length) (hk : k < ps.length) (hik : i ≠ k) : ps[i].id ≠ ps[k].id := by
  intro h
  have hp := List.nodup_iff_pairwise_ne.1 hnd
  rw [List.pairwise_iff_getElem] at hp
  rcases Nat.lt_or_gt_of_ne hik with hlt | hlt
  · exact hp i k (by simpa using hi) (by simpa using hk) hlt (by simpa using h)
  · exact hp k i (by simpa using hk) (by simpa using hi) hlt (by simpa using h.symm)

/-- In a list with distinct IDs below `2^32`, the Prog at the address of the Prog at index `j` is
that Prog. -/
theorem progAt?_byId {ps : List Prog} (hnd : (ps.map (·.id)).Nodup)
    (hlt : ∀ p ∈ ps, p.id < 2 ^ 32) {j : Nat} (hj : j < ps.length) :
    progAt? (Link.byId sym text a x ps) ps (text + BitVec.ofNat 64 (4 * ps[j].id)) =
      some ps[j] := by
  have hmax := maxId_lt (by decide) hlt
  have hidj := hlt _ (List.getElem_mem hj)
  unfold progAt?
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨?_, j, hj, rfl, fun k hk => ?_⟩
  · simp only [Link.occupies, addr_byId (List.getElem_mem hj), nextAddr_byId hnd hj]
    simp only [beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]
    intro h
    split at h
    · rename_i h1
      have := addr_inj (by omega) (by have := hlt _ (List.getElem_mem h1); omega) h
      exact id_ne_of_nodup hnd hj h1 (by omega) this
    · have := addr_inj (by omega) (by omega) h
      have := le_maxId (List.getElem_mem hj)
      omega
  · have hkj : k < ps.length := Nat.lt_trans hk hj
    have hne : (some (text + BitVec.ofNat 64 (4 * ps[k].id)) ==
        some (text + BitVec.ofNat 64 (4 * ps[j].id))) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
      intro h1
      have := addr_inj (by have := hlt _ (List.getElem_mem hkj); omega) (by omega) h1
      exact id_ne_of_nodup hnd hkj hj (by omega) this
    simp [addr_byId (List.getElem_mem hkj), hne]

end ById

end GoFV.Proof.Gen
