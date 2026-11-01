import GoFV.Proof.Pass.CopyElimGraph

/-!
# What copyelim's primitives do to the value table

`vw F` is `F`'s value table without use counts (`strip`): `incUses`/`decUses` and `unCache`
leave it unchanged, and `setArg`, `resetValue` and the phi-to-copy step of `phielimValue` update
one value (`upd`). `skel F` is what no step of the sweeps changes (entry, block list and table,
ID counters, aux, value table size).
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.Opt

/-- A value without its use count. -/
def strip (v : Value) : Value := { v with uses := 0 }

/-- The value table without use counts. -/
def vw (F : Func) (x : ID) : Option Value := (F.value? x).map strip

/-- `V` with the value `v` updated by `g`. -/
def upd (V : ID → Option Value) (v : ID) (g : Value → Value) (x : ID) : Option Value :=
  if v = x then (V x).map g else V x

/-- What the sweeps keep. -/
def skel (F : Func) : ID × Nat × Array ID × Array (Option Block) × Nat × Option AuxRef × Nat :=
  (F.entry, F.bidLast, F.blocks, F.blockTab, F.vidLast, F.ownAux, F.valueTab.size)

theorem value?_modV (F : Func) (v : ID) (g : Value → Value) (x : ID) :
    (F.modV v g).value? x = if v = x then (F.value? x).map g else F.value? x := by
  unfold Func.modV Func.value?
  simp only [Array.getElem?_modify]
  split
  · cases F.valueTab[x]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rfl

theorem vw_modV (F : Func) (v : ID) (g : Value → Value) (hg : ∀ y, strip (g y) = g (strip y)) :
    vw (F.modV v g) = upd (vw F) v g := by
  funext x
  unfold vw upd
  rw [value?_modV]
  split
  · rw [Option.map_map, Option.map_map]
    congr 1
    funext y
    exact hg y
  · rfl

theorem vw_modV_uses (F : Func) (v : ID) (g : Value → Value) (hg : ∀ y, strip (g y) = strip y) :
    vw (F.modV v g) = vw F := by
  funext x
  unfold vw
  rw [value?_modV]
  split
  · cases F.value? x <;> simp [hg]
  · rfl

theorem vw_incUses (F : Func) (a : ID) : vw (F.incUses a) = vw F :=
  vw_modV_uses F a _ fun _ => rfl

theorem vw_decUses (F : Func) (a : ID) : vw (F.decUses a) = vw F :=
  vw_modV_uses F a _ fun _ => rfl

theorem vw_foldl_uses (xs : List ID) (k : Func → ID → Func) (hk : ∀ F a, vw (k F a) = vw F) :
    ∀ F, vw (xs.foldl k F) = vw F := by
  induction xs with
  | nil => intro F; rfl
  | cons a xs ih => intro F; rw [List.foldl_cons, ih, hk]

theorem vw_afoldl_uses (xs : Array ID) (k : Func → ID → Func) (hk : ∀ F a, vw (k F a) = vw F)
    (F : Func) : vw (xs.foldl k F) = vw F := by
  rw [← Array.foldl_toList]; exact vw_foldl_uses _ k hk F

theorem skel_modV (F : Func) (v : ID) (g : Value → Value) : skel (F.modV v g) = skel F := by
  simp [skel, Func.modV]

theorem skel_foldl_uses (xs : List ID) (k : Func → ID → Func) (hk : ∀ F a, skel (k F a) = skel F) :
    ∀ F, skel (xs.foldl k F) = skel F := by
  induction xs with
  | nil => intro F; rfl
  | cons a xs ih => intro F; rw [List.foldl_cons, ih, hk]

theorem skel_afoldl_uses (xs : Array ID) (k : Func → ID → Func) (hk : ∀ F a, skel (k F a) = skel F)
    (F : Func) : skel (xs.foldl k F) = skel F := by
  rw [← Array.foldl_toList]; exact skel_foldl_uses _ k hk F

/-- `unCache` changes only the constant cache. -/
theorem unCacheLine_consts {F F' : Func} {v : ID} {k : Int64} (h : F.unCacheLine v k = some F') :
    ∃ c, F' = { F with consts := c } := by
  unfold Func.unCacheLine at h
  cases h1 : F.constLine? k with
  | none => rw [h1] at h; cases h
  | some li =>
    rw [h1] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    cases h2 : (F.consts[li]!.2).idxOf? v with
    | none => rw [h2] at h; cases h
    | some i =>
      rw [h2] at h
      simp only [Option.bind_some, pure] at h
      split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h; exact ⟨_, rfl⟩

theorem unCache_magic (F : Func) (v : ID) (m : Int64) :
    ∃ c, (if (m == 0) = true then F else (F.unCacheLine v m).getD F) = { F with consts := c } := by
  split
  · exact ⟨_, rfl⟩
  · cases h' : F.unCacheLine v m with
    | none => exact ⟨_, rfl⟩
    | some F' => exact unCacheLine_consts h'

theorem unCache_consts (F : Func) (v : ID) : ∃ c, F.unCache v = { F with consts := c } := by
  unfold Func.unCache
  dsimp only
  cases h : F.unCacheLine v (F.getV v).auxInt with
  | some F' => exact unCacheLine_consts h
  | none =>
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · split <;> exact unCache_magic F v _

theorem vw_unCache (F : Func) (v : ID) : vw (F.unCache v) = vw F := by
  obtain ⟨c, h⟩ := unCache_consts F v
  rw [h]; rfl

theorem skel_unCache (F : Func) (v : ID) : skel (F.unCache v) = skel F := by
  obtain ⟨c, h⟩ := unCache_consts F v
  rw [h]; rfl

/-! ## The three edits -/

theorem vw_setArg (F : Func) (v : ID) (i : Nat) (w : ID) :
    vw (F.setArg v i w) = upd (vw F) v fun y => { y with args := y.args.set! i w } := by
  unfold Func.setArg
  rw [vw_incUses, vw_modV, vw_decUses]
  intro _; rfl

theorem skel_setArg (F : Func) (v : ID) (i : Nat) (w : ID) : skel (F.setArg v i w) = skel F := by
  unfold Func.setArg Func.incUses Func.decUses
  rw [skel_modV, skel_modV, skel_modV]

theorem upd_upd (V : ID → Option Value) (v : ID) (g h : Value → Value) :
    upd (upd V v g) v h = upd V v (h ∘ g) := by
  funext x
  unfold upd
  split
  · subst_vars; simp only [Option.map_map]
  · rfl

theorem vw_resetArgs (F : Func) (v : ID) :
    vw (F.resetArgs v) = upd (vw F) v fun y => { y with args := #[] } := by
  unfold Func.resetArgs
  rw [vw_modV, vw_afoldl_uses _ _ vw_decUses]
  intro _; rfl

theorem skel_decUses (F : Func) (a : ID) : skel (F.decUses a) = skel F := skel_modV _ _ _

theorem skel_incUses (F : Func) (a : ID) : skel (F.incUses a) = skel F := skel_modV _ _ _

theorem skel_resetArgs (F : Func) (v : ID) : skel (F.resetArgs v) = skel F := by
  unfold Func.resetArgs
  rw [skel_modV, skel_afoldl_uses _ _ skel_decUses]

theorem vw_resetValue (F : Func) (v : ID) (op : Op) :
    vw (F.resetValue v op) =
      upd (vw F) v fun y => { y with op, args := #[], auxInt := 0, aux := none } := by
  unfold Func.resetValue
  rw [vw_modV, vw_resetArgs, vw_modV, vw_unCache, upd_upd, upd_upd]
  · rfl
  all_goals intro _; rfl

theorem skel_resetValue (F : Func) (v : ID) (op : Op) : skel (F.resetValue v op) = skel F := by
  unfold Func.resetValue
  rw [skel_modV, skel_resetArgs, skel_modV, skel_unCache]

theorem vw_toCopy (F : Func) (v w : ID) :
    vw ((F.modV v fun y => { y with op := .Copy }).setArgs1 v w) =
      upd (vw F) v fun y => { y with op := .Copy, args := #[w] } := by
  unfold Func.setArgs1 Func.setArgs Func.addArgs
  rw [vw_afoldl_uses _ _ vw_incUses, vw_modV, vw_resetArgs, vw_modV, upd_upd, upd_upd]
  · congr 1
  all_goals intro _; rfl

theorem skel_toCopy (F : Func) (v w : ID) :
    skel ((F.modV v fun y => { y with op := .Copy }).setArgs1 v w) = skel F := by
  unfold Func.setArgs1 Func.setArgs Func.addArgs
  rw [skel_afoldl_uses _ _ skel_incUses, skel_modV, skel_resetArgs, skel_modV]

/-! ## Reading the view -/

theorem vw_eq_some {F : Func} {x : ID} {u : Value} (h : vw F x = some u) :
    ∃ u', F.value? x = some u' ∧ u = strip u' := by
  unfold vw at h
  cases h' : F.value? x with
  | none => rw [h'] at h; cases h
  | some u' => rw [h'] at h; cases h; exact ⟨u', rfl, rfl⟩

theorem vw_of_value? {F : Func} {x : ID} {u : Value} (h : F.value? x = some u) :
    vw F x = some (strip u) := by
  unfold vw; rw [h]; rfl

theorem getV_of_vw {F : Func} {x : ID} {u : Value} (h : vw F x = some u) :
    (F.getV x).op = u.op ∧ (F.getV x).args = u.args ∧ (F.getV x).type = u.type := by
  obtain ⟨u', h1, rfl⟩ := vw_eq_some h
  unfold Func.getV; rw [h1]
  exact ⟨rfl, rfl, rfl⟩

theorem getV_of_vw_none {F : Func} {x : ID} (h : vw F x = none) : F.getV x = default := by
  unfold vw at h
  unfold Func.getV
  cases h' : F.value? x with
  | none => rfl
  | some _ => rw [h'] at h; cases h

theorem cstep_vw (F : Func) : cstep (vw F) = cstep F.value? := by
  funext x
  unfold cstep vw
  cases F.value? x <;> rfl

theorem cstep_some_some {V : ID → Option Value} {x y : ID} (h : cstep V x = some (some y)) :
    ∃ u, V x = some u ∧ u.op = .Copy ∧ u.args = #[y] := by
  unfold cstep at h
  cases hx : V x with
  | none => rw [hx] at h; cases h
  | some u =>
    rw [hx] at h
    dsimp only at h
    by_cases hop : u.op = .Copy
    · rw [ite_eq_left hop] at h
      by_cases hs : u.args.size = 1
      · rw [ite_eq_left hs] at h
        refine ⟨u, rfl, hop, ?_⟩
        have h0 : u.args[0]? = some y := Option.some.inj h
        apply Array.ext
        · simp [hs]
        · intro i h1 _
          have : i = 0 := by omega
          subst this
          rw [Array.getElem?_eq_some_iff] at h0
          obtain ⟨_, h0⟩ := h0
          simpa using h0
      · rw [ite_eq_right hs] at h; cases h
    · rw [ite_eq_right hop] at h; cases h

theorem cstep_of_copy {V : ID → Option Value} {x y : ID} {u : Value} (hx : V x = some u)
    (hop : u.op = .Copy) (ha : u.args = #[y]) : cstep V x = some (some y) := by
  unfold cstep; rw [hx]; simp [hop, ha]

theorem cstep_of_ne {V : ID → Option Value} {x : ID} {u : Value} (hx : V x = some u)
    (hop : u.op ≠ .Copy) : cstep V x = none := by
  unfold cstep; rw [hx]; simp [hop]

theorem cstep_none {V : ID → Option Value} {x : ID} (h : cstep V x = none) :
    ∀ u, V x = some u → u.op ≠ .Copy := by
  intro u hu hop
  unfold cstep at h; rw [hu] at h; simp [hop] at h

theorem cstep_upd_ne (V : ID → Option Value) (v : ID) (g : Value → Value) {x : ID} (h : x ≠ v) :
    cstep (upd V v g) x = cstep V x := by
  unfold cstep upd; rw [ite_eq_right (Ne.symm h)]

theorem upd_self (V : ID → Option Value) (v : ID) (g : Value → Value) :
    upd V v g v = (V v).map g := by
  unfold upd; simp

theorem upd_ne (V : ID → Option Value) (v : ID) (g : Value → Value) {x : ID} (h : x ≠ v) :
    upd V v g x = V x := by
  unfold upd; rw [ite_eq_right (Ne.symm h)]

/-- How the code reads a copy edge. -/
theorem getV_cstep_some {F : Func} {x y : ID} (h : cstep (vw F) x = some (some y)) :
    (F.getV x).op = .Copy ∧ (F.getV x).args[0]! = y := by
  obtain ⟨u, hu, hop, ha⟩ := cstep_some_some h
  obtain ⟨h1, h2, -⟩ := getV_of_vw hu
  rw [h1, h2, hop, ha]
  exact ⟨rfl, rfl⟩

theorem getV_cstep_none {F : Func} {x : ID} (h : cstep (vw F) x = none) :
    (F.getV x).op ≠ .Copy := by
  cases hx : vw F x with
  | none => rw [getV_of_vw_none hx]; decide
  | some u => rw [(getV_of_vw hx).1]; exact cstep_none h u hx

end GoFV.Proof.CopyElim
