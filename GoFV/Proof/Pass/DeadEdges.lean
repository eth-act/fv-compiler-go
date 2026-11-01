import GoFV.Proof.Pass.DeadEdgeVal

/-!
# deadcode's edge removal as recursions

`removeDeadEdges` and `removeFirstEdges` (`GoFV.Opt.Deadcode`) written as structural
recursions over `f.Blocks` and the fuel of the successor loop, for `removeEdgeG el`
(`edgesG true` is deadcode's own edge removal, `edgesG_true`; `edgesG false` is the same walk
where `Phi`s only lose arguments).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Opt

/-- The successor loop of `removeDeadEdges` for the unreachable block `b`. -/
def deadInner (el : Bool) (r : Array Bool) (b : ID) : Nat → Nat → Func → Func
  | 0, _, f => f
  | fuel + 1, i, f =>
    if h : i < (f.getB b).succs.size then
      if r.getD (f.getB b).succs[i].b false then deadInner el r b fuel i (removeEdgeG el f b i)
      else deadInner el r b fuel (i + 1) f
    else f

/-- The block loop of `removeDeadEdges`. -/
def deadOuter (el : Bool) (r : Array Bool) : List ID → Func → Func
  | [], f => f
  | b :: bs, f => deadOuter el r bs
      (if r.getD b false then f else deadInner el r b (2 * (f.getB b).succs.size + 1) 0 f)

/-- One block of `removeFirstEdges`. -/
def firstStep (el : Bool) (r : Array Bool) (f : Func) (b : ID) : Func :=
  if !r.getD b false || (f.getB b).kind != .First then f else
  (removeEdgeG el f b 1).modB b fun x => { x with kind := .Plain, likely := .unknown }

/-- deadcode's edge removal (`el = true`), or the same walk keeping `Phi`s (`el = false`). -/
def edgesG (el : Bool) (f : Func) : Func :=
  f.blocks.toList.foldl (firstStep el f.reachableBlocks)
    (deadOuter el f.reachableBlocks f.blocks.toList f)

theorem deadInner_forIn (r : Array Bool) (b : ID) :
    ∀ (L : List Nat) (f : Func) (i : Nat),
      (forIn (m := Id) L (f, i) (fun _ (s : Func × Nat) =>
        have f := s.fst
        have i := s.snd
        have ss := (f.getB b).succs
        if h : i < ss.size then
          if r.getD ss[i].b false = true then
            have f := f.removeEdge b i
            pure (ForInStep.yield (f, i))
          else
            have i := i + 1
            pure (ForInStep.yield (f, i))
        else pure (ForInStep.done (f, i)))).fst = deadInner true r b L.length i f
  | [], f, i => rfl
  | x :: L, f, i => by
    rw [List.forIn_cons]
    simp only [List.length_cons, deadInner]
    split
    · split
      · rw [← removeEdgeG_true]; exact deadInner_forIn r b L _ i
      · exact deadInner_forIn r b L f (i + 1)
    · rfl

theorem deadOuter_forIn (r : Array Bool) :
    ∀ (L : List ID) (f : Func),
      (forIn (m := Id) L f (fun b (f : Func) =>
        if r.getD b false = true then pure (ForInStep.yield f)
        else do
          let s ← forIn [:2 * (f.getB b).succs.size + 1] (f, 0) fun _ (s : Func × Nat) =>
            have f := s.fst
            have i := s.snd
            have ss := (f.getB b).succs
            if h : i < ss.size then
              if r.getD ss[i].b false = true then
                have f := f.removeEdge b i
                pure (ForInStep.yield (f, i))
              else
                have i := i + 1
                pure (ForInStep.yield (f, i))
            else pure (ForInStep.done (f, i))
          pure (ForInStep.yield s.fst))) = deadOuter true r L f
  | [], f => rfl
  | b :: L, f => by
    rw [List.forIn_cons]
    simp only [deadOuter]
    split
    · exact deadOuter_forIn r L f
    · rw [Std.Legacy.Range.forIn_eq_forIn_range']
      have := deadInner_forIn r b (List.range' 0 [:2 * (f.getB b).succs.size + 1].size) f 0
      have hsz : [:2 * (f.getB b).succs.size + 1].size = 2 * (f.getB b).succs.size + 1 := by
        simp [Std.Legacy.Range.size]
      rw [List.length_range', hsz] at this
      rw [hsz]
      show forIn L (forIn (m := Id) _ _ _).fst _ = _
      rw [this]
      exact deadOuter_forIn r L _

theorem removeDeadEdges_eq (r : Array Bool) (f : Func) :
    Deadcode.removeDeadEdges r f = deadOuter true r f.blocks.toList f := by
  rw [← deadOuter_forIn r f.blocks.toList f, Array.forIn_toList]; rfl

theorem foldl_firstStep_blocks (el : Bool) (r : Array Bool) :
    ∀ (L : List ID) (f : Func), (L.foldl (firstStep el r) f).blocks = f.blocks := by
  sorry

theorem edgesG_true (f : Func) :
    edgesG true f = Deadcode.removeFirstEdges f.reachableBlocks
      (Deadcode.removeDeadEdges f.reachableBlocks f) := by
  sorry

end GoFV.Proof.Dead
