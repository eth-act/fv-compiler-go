import GoFV.Proof.Pass.LoadFwdPtr
import GoFV.Proof.Pass.RewriteTerm
import GoFV.Proof.AtomSim

/-!
# Load-of-Store forwarding refines its input (issue #151)

`fwd_refines`: if `RewriteCheck.fwdRel tabs f g` (`g` is `f` with Loads replaced by `Copy x` of
the value a `Store` wrote, through `Store`s at disjoint addresses, at a pointer equal to the
Load's, every other value unchanged), `g` refines `f`, by the atom simulation
(`AtomSim.atomSimInv_refines`, trivial invariant). Its premises hold because every value listed
in `f` is refined by the same value in `g` as a term (`fwd_den`), for valuations whose memory
roots hold the writes of their arguments and whose `LocalAddr`s their frame variables
(`MemAtoms`): by induction on `fwdRank` (a replaced Load's stored value ranks below it), a
replaced Load reads, through the writes of the disjoint `Store`s (`disjoint_sep`,
`load_write_sep`), the write of the stored value's term at the Load's pointer (`samePtr_den`),
and reads that value back (`load_write`): `chain_load`.
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.Pass.Rewrite GoFV.Proof.CSE.Mem

/-- What `fwdRel` establishes. -/
structure FwdFacts (tabs : Tables) (f g : Func) : Prop where
  atoms : atomsOK f g = true
  cf : closedOK f = true
  cg : closedOK g = true
  blocks : g.blocks = f.blocks
  btab : g.blockTab = f.blockTab
  rank : fwdRankOK f (fwdRank f) = true
  rep : ∀ x < f.valueTab.size, fwdRepOK tabs f g x = true

theorem fwdRel_spec {tabs : Tables} {f g : Func} (h : fwdRel tabs f g = true) :
    FwdFacts tabs f g := by
  unfold fwdRel at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The rank of a listed non-`Phi` value is above its arguments'. -/
theorem fwdRankOK_spec {f : Func} {rk : Array Nat} (h : fwdRankOK f rk = true) {z : ID}
    (hz : LM f z)
    {u : Value} (hu : f.value? z = some u) (hph : u.op ≠ .Phi) :
    ∀ a ∈ u.args, rk[a]?.getD 0 < rk[z]?.getD 0 := by
  unfold fwdRankOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  have := h z (lt_of_value? hu)
  rw [hu] at this
  simp only [LM] at hz
  rcases this with h1 | h1
  · exact absurd hz h1
  · simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hph
    · intro a ha
      simpa using (Array.all_eq_true_iff_forall_mem.1 h1) a ha

theorem loadOp_other {t : Ty} {p m : Val} (h : ¬ ∃ a M, p = .ptr a ∧ m = .mem M) :
    loadOp t [p, m] = .poison := by
  unfold loadOp
  split
  · rename_i a M heq
    simp only [List.cons.injEq] at heq
    exact absurd ⟨a, M, heq.1, heq.2.1⟩ h
  · rfl

/-- `fwdTyEq` shapes retype alike. -/
theorem fwdTyEq_retype {t s : Ty} (h : fwdTyEq t s = true) : Val.retype t = Val.retype s := by
  funext v
  cases t <;> cases s <;> simp only [fwdTyEq, beq_iff_eq, reduceCtorEq] at h
  · rw [h]
  · rfl
  · exact retype_ptr_elem _ _ v

theorem fwdTyEq_fwdTy {t s : Ty} (h : fwdTyEq t s = true) : fwdTy t = true := by
  cases t <;> cases s <;> simp_all [fwdTyEq, fwdTy]

/-- A `Store` at shape `s` (`fwdStoreTy t s`) writes a value of shape `t` as a write at `t`. -/
theorem fwdStoreTy_encode {t s : Ty} (h : fwdStoreTy t s = true) {v : Val} (hv : v.retype t = v) :
    encode s v = encode t v := by
  unfold fwdStoreTy at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨hp, hs⟩
  · cases t <;> cases s <;> simp only [fwdTyEq, beq_iff_eq, reduceCtorEq] at h
    · rw [h]
    · rfl
    · cases v with
      | int w x => cases w <;> rfl
      | _ => rfl
  · obtain ⟨e, rfl⟩ : ∃ e, t = .ptr e := by cases t <;> simp_all [isPtrTy]
    obtain rfl : s = .int .w64 := by
      revert hs
      cases s <;> first | (intro hs; cases hs) | skip
      rename_i w
      cases w <;> first | (intro; rfl) | (intro hs; cases hs)
    rcases ptr_fixed (t := .ptr e) rfl hv with rfl | ⟨q, rfl⟩ <;> rfl

/-- `Val.retype` fixes `mem` only at the memory shape. -/
theorem retype_mem {t : Ty} {M M' : Mem} (h : (Val.mem M').retype t = .mem M) : M' = M := by
  cases t <;> simp [Val.retype] at h
  exact h

/-- Only a memory retypes to a memory. -/
theorem retype_eq_mem {t : Ty} {v : Val} {M : Mem} (h : v.retype t = .mem M) : v = .mem M := by
  unfold Val.retype at h
  split at h <;> (repeat' split at h) <;> simp_all

/-- A `Store`'s write: a pointer, a memory and the written memory. -/
theorem memDef_store {tabs : Tables} {s : Value} (hs : s.op = .Store ∨ s.op = .StoreWB)
    {a b c y : Val} (h : memDef tabs s [a, b, c] = some y) :
    ∃ q m0 M', a = .ptr q ∧ c = .mem m0 ∧ m0.write q (encode (auxTy tabs s.aux) b) = some M' ∧
      y = .mem M' := by
  rcases hs with hs | hs <;>
  · cases a <;> try (simp [memDef, hs] at h; done)
    cases c <;> try (simp [memDef, hs] at h; done)
    rename_i q m0
    simp only [memDef, hs, Option.map_eq_some_iff] at h
    obtain ⟨M', hw, rfl⟩ := h
    exact ⟨q, m0, M', rfl, rfl, hw, rfl⟩

/-- The arguments of a list of values are refined by some fuel. -/
theorem fuel_list {α : Type} {F : α → Val} {G : Nat → α → Val}
    (hG : ∀ a m m', m ≤ m' → Sem.Refines (G m a) (G m' a)) :
    ∀ l : List α, (∀ a ∈ l, ∃ m, Sem.Refines (F a) (G m a)) →
      ∃ m, ∀ a ∈ l, Sem.Refines (F a) (G m a)
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l, h => by
    obtain ⟨m1, h1⟩ := h a List.mem_cons_self
    obtain ⟨m2, h2⟩ := fuel_list hG l fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨max m1 m2, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h1.trans (hG _ _ _ (Nat.le_max_left _ _))
    · exact (h2 b hb).trans (hG _ _ _ (Nat.le_max_right _ _))

/-- **A `Load` through a `Store` chain** (`fwdChain`): the memory read at the Load's pointer
holds, through the disjoint writes, the write of the stored value, which it reads back. -/
theorem chain_load {tabs : Tables} {f : Func} {ρ : ID → Val} (hT : Term.Typed f.value? tabs ρ)
    (hM : MemAtoms f.value? tabs ρ) {p x : ID} {t : Ty} {kp : Nat} {P : Ptr}
    (hp : den f.value? tabs ρ kp p = .ptr P) :
    ∀ (d : Nat) (m : ID), fwdChain tabs f p t x d m = true → ∀ {k : Nat} {M : Mem},
      den f.value? tabs ρ k m = .mem M → ∃ K, Sem.Refines (M.load t P) (den f.value? tabs ρ K x)
  | 0, _, h, _, _, _ => by simp [fwdChain] at h
  | d + 1, m, h, k, M, hm => by
    unfold fwdChain at h
    cases hs : f.value? m with
    | none => rw [hs] at h; cases h
    | some s =>
    cases hx : f.value? x with
    | none => rw [hs, hx] at h; cases h
    | some xv =>
    rw [hs, hx] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hcop, hcsz⟩, hch⟩ | ⟨⟨hsop, hssz⟩, h⟩
    · -- a `Copy` of memory
      have ht : termOp s.op = true := by rw [hcop]; rfl
      cases k with
      | zero => simp [den] at hm
      | succ k =>
      rw [den_succ_term hs ht, toList_one hcsz, List.map_cons, List.map_nil, hcop,
        GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy] at hm
      have hm' : den f.value? tabs ρ k s.args[0]! = .mem M := retype_eq_mem hm
      exact chain_load hT hM hp d _ hch hm'
    have hmem : memOp s.op = true := by rcases hsop with h | h <;> rw [h] <;> rfl
    -- `ρ` holds the `Store`'s write
    cases k with
    | zero => simp [den] at hm
    | succ k =>
    have hsat : ¬ IsTerm f.value? m := not_term_of hs (by rw [memOp_not_term hmem]; decide)
    rw [den_succ_atom hsat] at hm
    obtain ⟨N, hN⟩ := hM m s hs hmem (by rw [hm]; nofun)
    obtain ⟨y, hy, hρs⟩ := hN N (Nat.le_refl _)
    rw [toList_three hssz, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hy
    obtain ⟨q, m0, M', hq, hm0, hwr, rfl⟩ := memDef_store hsop hy
    rw [hm] at hρs
    have hMM := retype_mem hρs.symm
    subst hMM
    rcases h with ⟨⟨⟨⟨hsx, hsame⟩, hsty⟩, hxty⟩⟩ | ⟨hdis, hch⟩
    · -- the `Store` of `x` at the Load's pointer
      rw [samePtr_den hT hM hsame hp hq]
      have hxk : (den f.value? tabs ρ N x).retype t = den f.value? tabs ρ N x := by
        rw [fwdTyEq_retype hxty]; exact den_fix hT hx N
      rw [hsx, fwdStoreTy_encode hsty hxk] at hwr
      exact ⟨N, load_write (fwdTyEq_fwdTy hxty) hxk hwr⟩
    · -- a `Store` at a disjoint pointer
      have hsep := disjoint_sep hT hM hdis hp hq
      rw [load_write_sep hwr (by rw [GoFV.Proof.CSE.Mem.encode_size]; exact hsep)]
      exact chain_load hT hM hp d _ hch hm0

section
variable {tabs : Tables} {f g : Func} (F : FwdFacts tabs f g)
include F

/-- A value listed in `f` is listed in `g`, as `g`'s value. -/
theorem marked_g {x : ID} {u w : Value} (hx : LM f x) (hu : f.value? x = some u)
    (hw : g.value? x = some w) (hwb : w.block = u.block) : listedDefs g x = some w := by
  obtain ⟨b, hb, fb, hfb, hxv, u', hu', hub⟩ := listedMarks_sound f x hx
  rw [hu] at hu'; cases hu'
  have hgb : g.block? b = some fb := by unfold Func.block?; rw [F.btab]; exact hfb
  rw [listedDefs_of_marked ⟨b, F.blocks ▸ hb, fb, hgb, hxv, w, hw, hwb.trans hub⟩, hw]

/-- The definition of a listed value of `g`: `fwdRepOK`. -/
theorem rep_of {x : ID} {u : Value} (hu : f.value? x = some u) :
    ∃ w, g.value? x = some w ∧ w.id = u.id ∧ w.block = u.block ∧ w.type = u.type ∧
      ((w.op = u.op ∧ w.auxInt = u.auxInt ∧ w.aux = u.aux ∧ w.args = u.args) ∨
       (w.op = .Copy ∧ w.args.size = 1 ∧ fwdOK tabs f u (w.args[0]?.getD 0) = true)) := by
  have h := F.rep x (lt_of_value? hu)
  unfold fwdRepOK at h
  rw [hu] at h
  cases hw : g.value? x with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hid, hblk⟩, hty⟩, h⟩ := h
    refine ⟨w, rfl, hid, hblk, hty, ?_⟩
    rcases h with ⟨⟨⟨hop, hai⟩, hax⟩, hargs⟩ | ⟨⟨hop, hsz⟩, hok⟩
    · exact .inl ⟨hop, hai, hax, hargs⟩
    · exact .inr ⟨hop, hsz, hok⟩

/-- The arguments of a value listed in `f` are listed. -/
theorem lm_arg {x : ID} {u : Value} (hx : LM f x) (hu : f.value? x = some u) :
    ∀ a ∈ u.args, LM f a := by
  obtain ⟨b, hb, fb, hfb, hxv, u', hu', -⟩ := listedMarks_sound f x hx
  rw [hu] at hu'; cases hu'
  exact (closedOK_facts F.cf b hb fb hfb).2 x hxv u hu

/-- The value a `Store` chain (`fwdChain`) reads back is listed and ranks below the chain's
memory. -/
theorem chain_rank {p x : ID} {t : Ty} :
    ∀ (d : Nat) (m : ID), fwdChain tabs f p t x d m = true → LM f m →
      LM f x ∧ (fwdRank f)[x]?.getD 0 < (fwdRank f)[m]?.getD 0
  | 0, _, h, _ => by simp [fwdChain] at h
  | d + 1, m, h, hm => by
    unfold fwdChain at h
    cases hs : f.value? m with
    | none => rw [hs] at h; cases h
    | some s =>
    cases hx : f.value? x with
    | none => rw [hs, hx] at h; cases h
    | some xv =>
    rw [hs, hx] at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hcop, hcsz⟩, hch⟩ | ⟨⟨hsop, hssz⟩, h⟩
    · have hc : s.args[0]! ∈ s.args := by
        rw [getElem!_pos s.args 0 (by omega)]; exact Array.getElem_mem _
      have hph : s.op ≠ .Phi := by rw [hcop]; decide
      obtain ⟨hlx, hrx⟩ := chain_rank d _ hch (lm_arg F hm hs _ hc)
      exact ⟨hlx, Nat.lt_trans hrx (fwdRankOK_spec F.rank hm hs hph _ hc)⟩
    have hsph : s.op ≠ .Phi := by rcases hsop with h | h <;> rw [h] <;> decide
    have hmem : ∀ i, i < 3 → s.args[i]! ∈ s.args := fun i hi => by
      rw [getElem!_pos s.args i (by omega)]; exact Array.getElem_mem _
    rcases h with ⟨⟨⟨⟨hsx, -⟩, -⟩, -⟩⟩ | ⟨-, hch⟩
    · rw [← hsx]
      exact ⟨lm_arg F hm hs _ (hmem 1 (by omega)),
        fwdRankOK_spec F.rank hm hs hsph _ (hmem 1 (by omega))⟩
    · have hc := hmem 2 (by omega)
      obtain ⟨hlx, hrx⟩ := chain_rank d _ hch (lm_arg F hm hs _ hc)
      exact ⟨hlx, Nat.lt_trans hrx (fwdRankOK_spec F.rank hm hs hsph _ hc)⟩

/-- **Values as terms**: each value listed in `f` is refined by the same value listed in `g`,
for valuations whose memory roots hold the writes of their arguments. -/
theorem fwd_den {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ') (hT : Term.Typed f.value? tabs ρ)
    (hM : MemAtoms f.value? tabs ρ) :
    ∀ (r : Nat) (x : ID), (fwdRank f)[x]?.getD 0 = r → LM f x → ∀ n, ∃ m,
      Sem.Refines (den f.value? tabs ρ n x) (den (listedDefs g) tabs ρ' m x) := by
  intro r
  refine Nat.strongRecOn r ?_
  intro r ih x hr hx n
  cases n with
  | zero => exact ⟨0, .poison _⟩
  | succ n =>
  have hxv := listedMarks_sound f x hx
  obtain ⟨-, -, -, -, -, u, hu, -⟩ := hxv
  obtain ⟨w, hw, -, hwb, hwty, hrep⟩ := rep_of F hu
  have hL := marked_g F hx hu hw hwb
  have hIH : ∀ a, (fwdRank f)[a]?.getD 0 < r → LM f a → ∀ n, ∃ m,
      Sem.Refines (den f.value? tabs ρ n a) (den (listedDefs g) tabs ρ' m a) :=
    fun a ha hla => ih _ ha a rfl hla
  rcases hrep with ⟨hop, hai, hax, hargs⟩ | ⟨hop, hsz, hok⟩
  · by_cases ht : termOp u.op = true
    · have hph : u.op ≠ .Phi := fun h => by rw [h] at ht; cases ht
      obtain ⟨m, hm⟩ := fuel_list (F := fun a => den f.value? tabs ρ n a)
        (G := fun m a => den (listedDefs g) tabs ρ' m a)
        (fun a m m' h => den_fuel_mono _ _ _ m m' a h) u.args.toList fun a ha =>
          hIH a (hr ▸ fwdRankOK_spec F.rank hx hu hph a (Array.mem_toList_iff.1 ha))
            (lm_arg F hx hu a (Array.mem_toList_iff.1 ha)) n
      refine ⟨m + 1, ?_⟩
      rw [den_succ_term hu ht, den_succ_term hL (hop ▸ ht), hop, hwty, hai, hax, hargs]
      exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_map hm))
    · refine ⟨1, ?_⟩
      rw [den_succ_atom (not_term_of hu ht), den_succ_atom (not_term_of hL (hop ▸ ht))]
      exact hρ x
  · -- `x` is a Load forwarded to `Copy c`
    obtain ⟨c, hc⟩ : ∃ c, c = w.args[0]?.getD 0 := ⟨_, rfl⟩
    rw [← hc] at hok
    unfold fwdOK at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨hld, hsz2⟩, hch⟩ := hok
    have hph : u.op ≠ .Phi := by rw [hld]; decide
    have hLt : termOp u.op = true := by rw [hld]; decide
    have hu1 : u.args[1]! ∈ u.args := by
      rw [getElem!_pos u.args 1 (by omega)]; exact Array.getElem_mem _
    -- the ranks: `c` below the chain's memory, below the Load
    have hls : LM f u.args[1]! := lm_arg F hx hu _ hu1
    obtain ⟨hlc, hrc'⟩ := chain_rank F 8 _ hch hls
    have hrc : (fwdRank f)[c]?.getD 0 < r := by
      have := fwdRankOK_spec F.rank hx hu hph _ hu1
      omega
    -- the target: `Copy c`
    have hcopy : termOp Op.Copy = true := by decide
    have hw0 : w.args.toList = [c] := by
      apply List.ext_getElem (by simp [hsz])
      intro i h1 h2
      have : i = 0 := by simp [hsz] at h1; omega
      subst this
      simp [hc, Array.getElem?_eq_getElem (show 0 < w.args.size by omega)]
    have hden_t : ∀ m, den (listedDefs g) tabs ρ' (m + 1) x =
        (den (listedDefs g) tabs ρ' m c).retype (tabs.ty u.type) := fun m => by
      rw [den_succ_term hL (hop ▸ hcopy), hop, hw0, List.map_cons, List.map_nil,
        GoFV.Proof.Rules.opVal_pure (op := Op.Copy) rfl, evalPure_copy, hwty]
    -- the source: a Load through the chain
    rw [den_succ_term hu hLt, toList_two hsz2, List.map_cons, List.map_cons, List.map_nil, hld,
      GoFV.Proof.Rules.opVal_pure (op := Op.Load) rfl, evalPure_load]
    by_cases hcase : ∃ a M, den f.value? tabs ρ n u.args[0]! = .ptr a ∧
      den f.value? tabs ρ n u.args[1]! = .mem M
    · obtain ⟨a, M, hpa, hsM⟩ := hcase
      rw [hpa, hsM, loadOp]
      obtain ⟨K, hK⟩ := chain_load hT hM hpa 8 _ hch hsM
      obtain ⟨m, hm⟩ := hIH c hrc hlc K
      refine ⟨m + 1, ?_⟩
      rw [hden_t m]
      exact retype_mono _ (hK.trans hm)
    · rw [loadOp_other hcase, AtomSim.retype_poison]; exact ⟨0, .poison _⟩

/-- Each value listed in `f` refines as a term in `g`, under any invariant. -/
theorem fwd_termRefP {x : ID} (hx : LM f x) (P : ID → Val → Prop) (Q : (ID → Val) → Prop)
    (S : ID → Prop) : TermRefP P Q S f.value? tabs x (listedDefs g) tabs x :=
  fun _ _ hρ hT _ _ _ _ hM n => fwd_den F hρ hT hM _ x rfl hx n

theorem fwd_atomArgs : AtomArgsRefP (SrcInv.triv tabs f) g := by
  intro b hb gb hgb a ha u hu ht
  obtain ⟨fb, hfb, -, hatoms⟩ := atomsOK_facts F.atoms b hb gb hgb
  obtain ⟨haf, u', hu', hop, hty, hai, hax, hsz⟩ := hatoms a ha u hu ht
  refine ⟨u', hu', hop, hty, hai, hax, hsz, fun i hi => ?_⟩
  obtain ⟨w, hw, -, -, -, hrep⟩ := rep_of F hu'
  rw [hu] at hw; cases hw
  have hargs : u.args = u'.args := by
    rcases hrep with ⟨-, -, -, h⟩ | ⟨h, -⟩
    · exact h
    · rw [h] at ht; cases ht
  have hbf : b ∈ f.blocks := F.blocks ▸ hb
  have hi' : i < u'.args.size := hargs ▸ hi
  rw [hargs]
  have hx := (closedOK_facts F.cf b hbf fb hfb).2 a haf u' hu' u'.args[i]!
    (by rw [getElem!_pos u'.args i hi']; exact Array.getElem_mem hi')
  exact ⟨fun _ => fwd_termRefP F hx _ _ _, fun _ _ _ _ _ _ _ => fwd_termRefP F hx _ _ _⟩

theorem fwd_steps : StepRefsP (SrcInv.triv tabs f) g := by
  refine ControlsRefP.toStepRefsP (fun b hb fb gb hfb hgb => ?_) fun b hb fb gb hfb hgb => ?_
  · have hgb' : g.block? b = some fb := by unfold Func.block?; rw [F.btab]; exact hfb
    rw [hgb] at hgb'; cases hgb'
    have hbf : b ∈ f.blocks := F.blocks ▸ hb
    refine ⟨rfl, fun k hk => fwd_termRefP F ((closedOK_facts F.cf b hbf fb hfb).1 _
      (by rw [getElem!_pos fb.controls k hk]; exact Array.getElem_mem hk)) _ _ _⟩
  · have hgb' : g.block? b = some fb := by unfold Func.block?; rw [F.btab]; exact hfb
    rw [hgb] at hgb'; cases hgb'
    exact ⟨rfl, rfl, rfl⟩

end

/-- **Load-of-Store forwarding refines its input.** -/
theorem fwd_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ()) (h : fwdRel tabs f g = true) :
    RefinesUnder Env.Mono tabs g tabs f :=
  have F := fwdRel_spec h
  atomSimInv_refines hf hg F.atoms (SrcInv.triv tabs f) (fwd_atomArgs F) (fwd_steps F)

end GoFV.Proof.Pass.LoadFwd
