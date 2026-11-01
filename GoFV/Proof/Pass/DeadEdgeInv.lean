import GoFV.Proof.Pass.DeadEdges

/-!
# The invariant of deadcode's edge removal

`EI f r F`: the function `F` reached by `removeEdgeG false` steps from `f` (removing edges out of
unreachable blocks and edge 1 of reachable `First` blocks, `r`: the reachable blocks) keeps `f`'s
blocks with crosslinked edges (`XL`), block contents except edges and terminator kind, values
except `Phi` arguments (each a subset of the original ones, one per predecessor), and every edge a
run can take out of a reachable block: it leads to the same block, at a predecessor index where
each `Phi` reads what it read in `f` (`PA`). `ei_step`: one removed edge keeps it.
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Opt GoFV.Proof.CopyElim

/-- The block without edges, terminator kind and prediction. -/
def kview (bl : Block) : Block :=
  { bl with succs := #[], preds := #[], kind := .Invalid, likely := .unknown }

/-- The value without arguments. -/
def noArgs (u : Value) : Value := { u with args := #[] }

/-- The `Phi`s of `F`'s block `c` read along `iT` what they read along `iS` in `f`. -/
def PA (f F : Func) (c : ID) (iS iT : Nat) : Prop :=
  ∀ x ∈ (F.getB c).values, ∀ u, vw F x = some u → u.op = .Phi →
    ∃ u0, vw f x = some u0 ∧ u.args[iT]? = u0.args[iS]?

/-- The invariant of the edge-removal walk (`removeEdgeG false`). -/
structure EI (f : Func) (r : Array Bool) (F : Func) : Prop where
  entry : F.entry = f.entry
  blocks : F.blocks = f.blocks
  ownAux : F.ownAux = f.ownAux
  vsize : F.valueTab.size = f.valueTab.size
  vidLast : F.vidLast = f.vidLast
  bidLast : F.bidLast = f.bidLast
  xl : XL F f.blocks
  pres : ∀ y, (F.block? y).isSome = (f.block? y).isSome
  kv : ∀ y, kview (F.getB y) = kview (f.getB y)
  kind : ∀ y, (F.getB y).kind = (f.getB y).kind ∨
    (r.getD y false = true ∧ (f.getB y).kind = .First ∧ (F.getB y).kind = .Plain)
  vals : ∀ x, (vw F x).map noArgs = (vw f x).map noArgs
  nonphi : ∀ x u, vw f x = some u → u.op ≠ .Phi → vw F x = some u
  sub : ∀ x u u', vw f x = some u → vw F x = some u' → ∀ a ∈ u'.args, a ∈ u.args
  arity : ∀ y ∈ f.blocks, ∀ x ∈ (F.getB y).values, ∀ u, vw F x = some u → u.op = .Phi →
    u.args.size = (F.getB y).preds.size
  edge : ∀ b ∈ f.blocks, r.getD b false = true → ∀ k e, sOf f b k = some e →
    ((f.getB b).kind = .First → k = 0) →
    ∃ e', sOf F b k = some e' ∧ e'.b = e.b ∧ PA f F e.b e.i e'.i

theorem dropArg_get {args : Array ID} {j m l : Nat} (hs : args.size = m + 1) (hj : j ≤ m) :
    ((args.set! j args[m]!).pop)[l]? = if l < m then args[predIdx j m l]? else none := by
  rw [Array.getElem?_pop]
  simp only [Array.set!, Array.size_setIfInBounds, hs, Nat.add_sub_cancel]
  split
  · rename_i hl
    rw [Array.getElem?_setIfInBounds]
    unfold predIdx
    by_cases hjl : j = l
    · subst hjl
      simp only [ite_true, show j < args.size by omega]
      rw [getElem!_pos args m (by omega), Array.getElem?_eq_getElem (by omega)]
    · simp only [hjl, ite_false, Ne.symm hjl]
  · rfl

theorem mem_dropArg {args : Array ID} {j m : Nat} (hs : args.size = m + 1) (hj : j ≤ m) {a : ID}
    (h : a ∈ (args.set! j args[m]!).pop) : a ∈ args := by
  obtain ⟨l, hl⟩ := Array.getElem?_of_mem h
  rw [dropArg_get hs hj] at hl
  split at hl
  · exact Array.mem_of_getElem? hl
  · cases hl

theorem size_dropArg {args : Array ID} {j m : Nat} (hs : args.size = m + 1) :
    ((args.set! j args[m]!).pop).size = m := by
  simp [Array.set!, hs]

theorem removeSucc_eta (F : Func) (b : ID) (i : Nat) :
    F.removeSucc b i =
      { F with blockTab := (F.removeSucc b i).blockTab, cache := (F.removeSucc b i).cache } := by
  unfold Func.removeSucc
  by_cases h : (i != (F.getB b).succs.size - 1) = true <;>
    simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> rfl

theorem removePred_eta (F : Func) (c : ID) (j : Nat) :
    F.removePred c j =
      { F with blockTab := (F.removePred c j).blockTab, cache := (F.removePred c j).cache } := by
  unfold Func.removePred
  by_cases h : (j != (F.getB c).preds.size - 1) = true <;>
    simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> rfl

theorem kview_of_bview {a b : Block} (h : bview a = bview b) : kview a = kview b := by
  have h1 : kview a = { bview a with kind := .Invalid, likely := .unknown } := rfl
  have h2 : kview b = { bview b with kind := .Invalid, likely := .unknown } := rfl
  rw [h1, h2, h]

theorem kind_of_bview {a b : Block} (h : bview a = bview b) : a.kind = b.kind := by
  have := congrArg Block.kind h; exact this

theorem values_of_kview {a b : Block} (h : kview a = kview b) : a.values = b.values := by
  have := congrArg Block.values h; exact this

theorem noArgs_dropPhis (l : List ID) (j m : Nat) (x : ID) (u : Value) :
    noArgs (dropPhis l j m x u) = noArgs u := by
  unfold dropPhis; split <;> rfl

theorem op_dropPhis (l : List ID) (j m : Nat) (x : ID) (u : Value) :
    (dropPhis l j m x u).op = u.op := by
  unfold dropPhis; split <;> rfl

/-- A value listed in two listed blocks of `f` (as seen in `F`) is listed in one. -/
theorem listed_once {ce : CheckEnv} {f F : Func} {r : Array Bool} (hwf : WF ce f)
    (hE : EI f r F) {y c : ID} (hy : y ∈ f.blocks) (hc : c ∈ f.blocks) {x : ID}
    (hxy : x ∈ (F.getB y).values) (hxc : x ∈ (F.getB c).values) : y = c := by
  obtain ⟨by', hby, -⟩ := hwf.blockId y hy
  obtain ⟨bc, hbc, -⟩ := hwf.blockId c hc
  rw [values_of_kview (hE.kv y)] at hxy
  rw [values_of_kview (hE.kv c)] at hxc
  unfold Func.getB at hxy hxc
  rw [hby] at hxy; rw [hbc] at hxc
  exact hwf.valueOnce y by' c bc ⟨hy, hby⟩ ⟨hc, hbc⟩ x hxy hxc

/-- **One removed edge keeps `EI`** (`hsafe`: a reachable source is only cut at its edge 1,
as a `First` block with two successors). -/
theorem ei_step {ce : CheckEnv} {f F : Func} {r : Array Bool} (hwf : WF ce f) (hE : EI f r F)
    {b0 : ID} {i0 : Nat} (hb0 : b0 ∈ f.blocks) (hi0 : i0 < (F.getB b0).succs.size)
    (hsafe : r.getD b0 false = true →
      (f.getB b0).kind = .First ∧ i0 = 1 ∧ (F.getB b0).succs.size = 2) :
    EI f r (removeEdgeG false F b0 i0) := by
  obtain ⟨ec, hec⟩ : ∃ ec, sOf F b0 i0 = some ec := ⟨_, Array.getElem?_eq_getElem hi0⟩
  obtain ⟨c, j⟩ := ec
  have hX := hE.xl
  have hb0' : b0 ∈ F.blocks := hE.blocks ▸ hb0
  obtain ⟨hcB, hcj⟩ := hX.succ b0 hb0 i0 _ hec
  dsimp only at hcB hcj
  have hcs : 0 < (F.getB c).preds.size := by
    have := (Array.getElem?_eq_some_iff.1 hcj).1; omega
  -- names for the sizes
  generalize hn : (F.getB b0).succs.size - 1 = n
  generalize hm : (F.getB c).preds.size - 1 = m
  have hnd : (F.getB c).values.toList.Nodup := by
    obtain ⟨bc, hbc, -⟩ := hwf.blockId c hcB
    have := hwf.valuesNodup c bc ⟨hcB, hbc⟩
    rw [values_of_kview (hE.kv c)]; unfold Func.getB; rw [hbc]; exact this
  obtain ⟨hsk, hvw⟩ := removeEdge_false hX hb0 hi0 hec hnd
  obtain ⟨c1, hjm, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ :=
    edge_core (n := n) (m := m) hX hb0 (by omega) (by omega) hec (by omega)
  rw [hm] at hvw
  have hG := getB_of_skel hsk
  have hB := block?_of_skel hsk
  have hvx : ∀ x, vw (removeEdgeG false F b0 i0) x =
      (vw F x).map (dropPhis (F.getB c).values.toList j m x) := fun x => congrFun hvw x
  -- the fields outside the block table
  have hF4 := removePred_eta (F.removeSucc b0 i0) c j
  have hF2 := removeSucc_eta F b0 i0
  have hsk' := hsk
  simp only [CopyElim.skel, Prod.mk.injEq] at hsk'
  obtain ⟨s1, s2, s3, -, s5, s6, s7⟩ := hsk'
  rw [hF4, hF2] at s1 s2 s3 s5 s6 s7
  simp only at s1 s2 s3 s5 s6 s7
  -- the reachable source and index of a run edge are not the removed edge
  have hne : ∀ b k e, b ∈ f.blocks → r.getD b false = true → sOf F b k = some e →
      ((f.getB b).kind = .First → k = 0) → b = b0 → k < n ∧ succIdx i0 n k = k ∧ k ≠ i0 := by
    intro b k e hb hr he hk hbb
    subst hbb
    obtain ⟨hF, h1, h2⟩ := hsafe hr
    have := hk hF
    subst this; subst h1
    refine ⟨by omega, rfl, by omega⟩
  have hsucc : ∀ b k e, b ∈ f.blocks → r.getD b false = true → sOf F b k = some e →
      ((f.getB b).kind = .First → k = 0) →
      sOf (removeEdgeG false F b0 i0) b k = some (renP c m j e) := by
    intro b k e hb hr he hk
    show (((removeEdgeG false F b0 i0).getB b).succs[k]?) = _
    rw [hG]
    change sOf _ b k = _
    rw [c3 b hb]
    split
    · rename_i hbb
      obtain ⟨hkn, hσ, -⟩ := hne b k e hb hr he hk hbb
      subst hbb
      rw [if_pos hkn, hσ, he]; rfl
    · rw [he]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s1]; exact hE.entry
  · rw [s3]; exact hE.blocks
  · rw [s6]; exact hE.ownAux
  · rw [s7]; exact hE.vsize
  · rw [s5]; exact hE.vidLast
  · rw [s2]; exact hE.bidLast
  · exact ⟨fun x hx => by rw [hB]; exact c1.pres x hx,
      fun x hx k e he => by
        unfold sOf pOf at *; rw [hG] at he ⊢; exact c1.succ x hx k e he,
      fun y hy l e he => by
        unfold sOf pOf at *; rw [hG] at he ⊢; exact c1.pred y hy l e he⟩
  · intro y; rw [hB, c9]; exact hE.pres y
  · intro y; rw [hG, kview_of_bview (c8 y)]; exact hE.kv y
  · intro y; rw [hG, kind_of_bview (c8 y)]; exact hE.kind y
  · intro x; rw [hvx, ← hE.vals x]
    cases vw F x <;> simp [noArgs_dropPhis]
  · intro x u hu hop
    rw [hvx, hE.nonphi x u hu hop]
    simp [dropPhis, hop]
  · intro x u u' hu hu' a ha
    rw [hvx] at hu'
    cases hF : vw F x with
    | none => rw [hF] at hu'; cases hu'
    | some u1 =>
      rw [hF] at hu'
      simp only [Option.map_some, Option.some.injEq] at hu'
      subst hu'
      unfold dropPhis at ha
      split at ha
      · rename_i hph
        have har := hE.arity c hcB x (by simpa using hph.1) u1 hF hph.2
        exact hE.sub x u u1 hu hF a (mem_dropArg (by omega) hjm ha)
      · exact hE.sub x u u1 hu hF a ha
  · intro y hy x hx u hu hop
    rw [hG] at hx ⊢
    rw [values_of_kview (kview_of_bview (c8 y))] at hx
    rw [c7 y]
    rw [hvx] at hu
    cases hF : vw F x with
    | none => rw [hF] at hu; cases hu
    | some u1 =>
      rw [hF] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      subst hu
      rw [op_dropPhis] at hop
      have har := hE.arity y hy x hx u1 hF hop
      unfold dropPhis
      split
      · rename_i hph
        have hyc : y = c := listed_once hwf hE hy hcB hx (by simpa using hph.1)
        subst hyc
        rw [if_pos rfl]
        exact size_dropArg (by omega)
      · rename_i hph
        split
        · rename_i hyc; subst hyc
          exact absurd ⟨by simpa using hx, hop⟩ hph
        · exact har
  · intro b hb hr k e he hk
    obtain ⟨e', he', heb, hPA⟩ := hE.edge b hb hr k e he hk
    have hrb : (renP c m j e').b = e'.b := by
      unfold renP; split
      · next h => rw [h]
      · rfl
    refine ⟨renP c m j e', hsucc b k e' hb hr he' hk, by rw [hrb, heb], ?_⟩
    intro x hx u'' hu'' hop''
    rw [hG] at hx
    rw [values_of_kview (kview_of_bview (c8 e.b))] at hx
    rw [hvx] at hu''
    cases hF : vw F x with
    | none => rw [hF] at hu''; cases hu''
    | some u1 =>
    rw [hF] at hu''
    simp only [Option.map_some, Option.some.injEq] at hu''
    subst hu''
    rw [op_dropPhis] at hop''
    obtain ⟨u0, hu0, hargs⟩ := hPA x hx u1 hF hop''
    refine ⟨u0, hu0, ?_⟩
    -- the source `b`'s edge `k` is not the removed one
    have hbk : ¬ (b = b0 ∧ k = i0) := by
      rintro ⟨rfl, rfl⟩
      exact (hne b k e' hb hr he' hk rfl).2.2 rfl
    obtain ⟨-, hpe'⟩ := hX.succ b hb k e' he'
    by_cases hbc : e.b = c
    · have hxc : x ∈ (F.getB c).values.toList := by rw [← hbc]; simpa using hx
      have har := hE.arity c hcB x (by simpa using hxc) u1 hF hop''
      simp only [dropPhis, hxc, hop'', and_self, ite_true, dropArg]
      have hs : u1.args.size = m + 1 := by omega
      rw [dropArg_get hs hjm]
      have he'c : e'.b = c := by rw [heb, hbc]
      have hlt : e'.i < m + 1 := by
        rw [he'c] at hpe'
        have := (Array.getElem?_eq_some_iff.1 hpe').1; omega
      have hij : e'.i ≠ j := by
        intro h
        rw [he'c, h, hcj] at hpe'
        simp only [Option.some.injEq, Edge.mk.injEq] at hpe'
        exact hbk ⟨hpe'.1.symm, hpe'.2.symm⟩
      unfold renP
      split
      · rename_i h
        have hm' : e'.i = m := by rw [h]
        have hjm' : j < m := by omega
        simp only [hjm', ite_true, predIdx]
        rw [← hm']; exact hargs
      · rename_i h
        have hm' : e'.i ≠ m := fun h' => h (by
          cases e'; simp only [Edge.mk.injEq] at he'c h' ⊢; exact ⟨he'c, h'⟩)
        simp only [show e'.i < m by omega, ite_true, predIdx, hij, ite_false]
        exact hargs
    · have hxc : x ∉ (F.getB c).values.toList := fun h =>
        hbc (listed_once hwf hE (heb ▸ (hX.succ b hb k e' he').1 :) hcB hx (by simpa using h))
      simp only [dropPhis, hxc, false_and, ite_false]
      unfold renP
      split
      · rename_i h; exact absurd (by rw [← heb, h]) hbc
      · exact hargs

end GoFV.Proof.Dead
