import GoFV.Proof.Pass.LoadFwdMem
import GoFV.Proof.Pass.RewriteTerm
import GoFV.Proof.AtomSim

/-!
# Load-of-Store forwarding refines its input (issue #151)

`fwd_refines`: if `RewriteCheck.fwdRel tabs f g` (`g` is `f` with Loads replaced by `Copy x` of
the value a `Store` wrote at a pointer that evaluates like the Load's, every other value
unchanged), `g` refines `f`, by the atom simulation (`AtomSim.atomSimInv_refines`, trivial
invariant). Its premises hold because every value listed in `f` is refined by the same value in
`g` as a term (`fwd_den`), for valuations whose memory roots hold the writes of their arguments
(`MemAtoms`): by induction on `fwdRank` (a replaced Load's stored value ranks below it), a
replaced Load reads through its `Store`'s value, which `MemAtoms` gives as the write of the
stored value's term at the Load's pointer (`samePtrB_den`), and reads that value back
(`load_write`).
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.Pass.Rewrite

/-- `samePtrB`: the two pointers' terms evaluate equally, at every fuel. -/
theorem samePtrB_den {tabs : Tables} {f : Func} (ρ : ID → Val) :
    ∀ (n : Nat) (a b : ID), samePtrB tabs f n a b = true →
      ∀ k, den f.value? tabs ρ k a = den f.value? tabs ρ k b
  | 0, a, b, h, k => by simp only [samePtrB, beq_iff_eq] at h; rw [h]
  | n + 1, a, b, h, k => by
    unfold samePtrB at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · rfl
    split at h
    · rename_i u w hu hw
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨ht, hop⟩, hty⟩, hai⟩, hax⟩, hsz⟩, hargs⟩ := h
      cases k with
      | zero => rfl
      | succ k =>
        rw [den_succ_term hu ht, den_succ_term hw (hop ▸ ht), ← hop, ← tyEq_sound hty, hai, hax]
        congr 2
        apply List.ext_getElem (by simp [hsz])
        intro i h1 h2
        simp only [List.getElem_map, Array.getElem_toList]
        have h1' : i < u.args.size := by simpa using h1
        have h2' : i < w.args.size := by simpa using h2
        refine samePtrB_den ρ n _ _ (hargs (u.args[i], w.args[i]) ?_) k
        have hz : i < (u.args.toList.zip w.args.toList).length := by
          simp only [List.length_zip, Array.length_toList]; omega
        have := List.getElem_mem hz
        simpa [List.getElem_zip] using this
    · cases h

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

theorem toList_two {a : Array ID} (h : a.size = 2) : a.toList = [a[0]!, a[1]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩⟩ <;> simp_all

theorem toList_three {a : Array ID} (h : a.size = 3) : a.toList = [a[0]!, a[1]!, a[2]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨z', l⟩⟩⟩⟩⟩ <;> simp_all

theorem evalPure_copy (ty : Ty) (ai : Int64) (aux : Option AuxRef) (y : Val) :
    evalPure .Copy ty ai aux [y] = y := rfl

theorem evalPure_load (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val) :
    evalPure .Load ty ai aux args = loadOp ty args := rfl

theorem loadOp_other {t : Ty} {p m : Val} (h : ¬ ∃ a M, p = .ptr a ∧ m = .mem M) :
    loadOp t [p, m] = .poison := by
  unfold loadOp
  split
  · rename_i a M heq
    simp only [List.cons.injEq] at heq
    exact absurd ⟨a, M, heq.1, heq.2.1⟩ h
  · rfl

theorem ptr_refines {p : Ptr} {v : Val} (h : Sem.Refines (.ptr p) v) : v = .ptr p := by
  cases h; rfl

theorem not_term_of {D : ID → Option Value} {x : ID} {v : Value} (hv : D x = some v)
    (ht : ¬ termOp v.op = true) : ¬ IsTerm D x := fun ⟨w, hw, hw'⟩ => by
  rw [hv] at hw; cases hw; exact ht hw'

/-- What `fwdOK` checks. -/
theorem fwdOK_spec {tabs : Tables} {f : Func} {u : Value} {x : ID}
    (h : fwdOK tabs f u x = true) :
    u.op = .Load ∧ u.args.size = 2 ∧ ∃ s xv, f.value? u.args[1]! = some s ∧
      f.value? x = some xv ∧ (s.op = .Store ∨ s.op = .StoreWB) ∧ s.args.size = 3 ∧
      s.args[1]! = x ∧ samePtrB tabs f 8 u.args[0]! s.args[0]! = true ∧
      fwdTy (tabs.ty u.type) = true ∧ tabs.ty u.type = auxTy tabs s.aux ∧
      tabs.ty u.type = tabs.ty xv.type := by
  unfold fwdOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  cases hs : f.value? u.args[1]! with
  | none => rw [hs] at h3; cases h3
  | some s =>
    cases hx : f.value? x with
    | none => rw [hs, hx] at h3; cases h3
    | some xv =>
      rw [hs, hx] at h3
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h3
      obtain ⟨⟨⟨⟨⟨⟨hsop, hssz⟩, hsx⟩, hsame⟩, hfty⟩, hsty⟩, hxty⟩ := h3
      exact ⟨s, xv, rfl, rfl, hsop, hssz, hsx, hsame, hfty, tyEq_sound hsty, tyEq_sound hxty⟩

/-- `Val.retype` fixes `mem` only at the memory shape. -/
theorem retype_mem {t : Ty} {M M' : Mem} (h : (Val.mem M').retype t = .mem M) : M' = M := by
  cases t <;> simp [Val.retype] at h
  exact h

/-- A `Store`'s write: a pointer, a memory and the written memory. -/
theorem memDef_store {tabs : Tables} {s : Value} (hs : s.op = .Store ∨ s.op = .StoreWB)
    {a b c y : Val} (h : memDef tabs s [a, b, c] = some y) :
    ∃ q m0 M', a = .ptr q ∧ c = .mem m0 ∧ m0.write q (encode (auxTy tabs s.aux) b) = some M' ∧
      y = .mem M' := by
  unfold memDef at h
  rcases hs with hs | hs <;> rw [hs] at h <;>
  · split at h
    all_goals first
      | (rename_i hop _; cases hop; done)
      | skip
    all_goals first
      | (simp at h; done)
      | skip
    all_goals
      rename_i heq
      simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl, rfl, -⟩ := heq
      cases hw : Mem.write _ _ _ with
      | none => rw [hw] at h; cases h
      | some M' => rw [hw] at h; cases h; exact ⟨_, _, _, rfl, rfl, hw, rfl⟩

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
    obtain ⟨hld, hsz2, s, xv, hs, hxv', hsop, hssz, hsx, hsame, hfty, hsty, hxty⟩ := fwdOK_spec hok
    have hph : u.op ≠ .Phi := by rw [hld]; decide
    have hLt : termOp u.op = true := by rw [hld]; decide
    have hr1 := fwdRankOK_spec F.rank hx hu hph
    · -- the Load's arguments
      have hu1 : u.args[1]! ∈ u.args := by
        rw [getElem!_pos u.args 1 (by omega)]; exact Array.getElem_mem _
      have hu0 : u.args[0]! ∈ u.args := by
        rw [getElem!_pos u.args 0 (by omega)]; exact Array.getElem_mem _
      have huargs : u.args.toList = [u.args[0]!, u.args[1]!] := toList_two hsz2
      have hsargs : s.args.toList = [s.args[0]!, c, s.args[2]!] := by
        rw [toList_three hssz, hsx]
      have hsc : c ∈ s.args := by
        rw [← hsx, getElem!_pos s.args 1 (by omega)]; exact Array.getElem_mem _
      -- the ranks: `c` below the `Store`, below the Load
      have hls : LM f u.args[1]! := lm_arg F hx hu _ hu1
      have hsph : s.op ≠ .Phi := by rcases hsop with h | h <;> rw [h] <;> decide
      have hlc : LM f c := lm_arg F hls hs c hsc
      have hrc : (fwdRank f)[c]?.getD 0 < r := by
        have h1 := fwdRankOK_spec F.rank hls hs hsph c hsc
        have h2 := hr1 _ hu1
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
      -- the source: a Load through the `Store`
      rw [den_succ_term hu hLt, huargs, List.map_cons, List.map_cons, List.map_nil, hld,
        GoFV.Proof.Rules.opVal_pure (op := Op.Load) rfl, evalPure_load]
      by_cases hcase : ∃ a M, den f.value? tabs ρ n u.args[0]! = .ptr a ∧
        den f.value? tabs ρ n u.args[1]! = .mem M
      rotate_left
      · rw [loadOp_other hcase, AtomSim.retype_poison]; exact ⟨0, .poison _⟩
      · obtain ⟨a, M, hpa, hsM⟩ := hcase
        rw [hpa, hsM, loadOp]
        -- `ρ` holds the `Store`'s write
        have hsn : n ≠ 0 := by rintro rfl; simp [den] at hsM
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        have hsat : ¬ IsTerm f.value? u.args[1]! :=
          not_term_of hs (by rw [memOp_not_term (by rcases hsop with h | h <;> rw [h] <;> rfl)]; decide)
        rw [den_succ_atom hsat] at hsM
        obtain ⟨N, hN⟩ := hM _ s hs (by rcases hsop with h | h <;> rw [h] <;> rfl)
          (by rw [hsM]; nofun)
        obtain ⟨y, hy, hρs⟩ := hN (max N (n' + 1)) (Nat.le_max_left _ _)
        rw [hsargs, List.map_cons, List.map_cons, List.map_cons, List.map_nil] at hy
        obtain ⟨q, m0, M', hq, -, hwr, rfl⟩ := memDef_store hsop hy
        rw [hsM] at hρs
        have hMM := retype_mem hρs.symm
        subst hMM
        -- the pointers agree
        have hpk : den f.value? tabs ρ (max N (n' + 1)) u.args[0]! = .ptr a := by
          have := den_fuel_mono f.value? tabs ρ (n' + 1) (max N (n' + 1)) u.args[0]!
            (Nat.le_max_right _ _)
          rw [hpa] at this
          exact ptr_refines this
        rw [samePtrB_den ρ 8 _ _ hsame, hq] at hpk
        cases hpk
        -- the stored value has the Load's shape
        have hxk : (den f.value? tabs ρ (max N (n' + 1)) c).retype (tabs.ty u.type) =
            den f.value? tabs ρ (max N (n' + 1)) c := by
          obtain ⟨k, hk⟩ : ∃ k, max N (n' + 1) = k + 1 := ⟨max N (n' + 1) - 1, by omega⟩
          rw [hk]
          by_cases hct : IsTerm f.value? c
          · obtain ⟨v, hv, hvt⟩ := hct
            rw [hxv'] at hv; cases hv
            rw [den_succ_term hxv' hvt, hxty, retype_idem]
          · rw [den_succ_atom hct]
            have := hT c hct (by rw [hxv']; rfl)
            simp only [shape, hxv', Option.map_some, Option.getD_some] at this
            rw [hxty]; exact this
        rw [← hsty] at hwr
        have hld' := load_write hfty hxk hwr
        obtain ⟨m, hm⟩ := hIH c hrc hlc (max N (n' + 1))
        refine ⟨m + 1, ?_⟩
        rw [hden_t m]
        exact retype_mono _ (hld'.trans hm)

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
