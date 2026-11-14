import GoFV.Proof.AtomSim
import GoFV.Proof.Pass.RewriteTerm
import GoFV.Proof.Pass.RewriteAddrCmp
import GoFV.Proof.Pass.LoadFwdPtr

variable [GoFV.SSA.Sem.Addrs]

/-!
# Devirtualised interface calls refine their input (issue #69)

`dv_refines`: if `RewriteCheck.dvRel tabs f g` (`g` is `f` with interface calls
`InterLECall {aux} code args…` turned into `StaticLECall {aux} args…`, `generic.rules:1733`, each
`dvOK`: the code pointer reaches, through compatible copies, an `Addr` of the global the aux's
callee names in `tabs`; every other value unchanged), `g` refines `f` under monotone contracts,
by the generalised atom simulation (`AtomSim.atomSimX_refines`) with the trivial source
invariant: the atoms are `f`'s but the devirtualised calls (`atomsXOK` with `dv`); the terms are
`f`'s, so the arguments of unchanged atoms and the controls refine as the same terms (`dv_den`);
a devirtualised call's arguments are its source's but the code pointer, which as a term is
refined by the pointer to the callee (`copy_addr_den`), so it points to no other function
(`AtomSim.CodeP`), and both calls reach the same contract (`callOp_devirt`).
-/

namespace GoFV.Proof.Pass.Devirt

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.Pass.Rewrite

/-- What `dvRel` establishes. -/
structure DvFacts (tabs : Tables) (f g : Func) : Prop where
  atoms : atomsXOK f g false true = true
  cf : closedOK f = true
  btab : f.blockTab = g.blockTab
  size : f.valueTab.size = g.valueTab.size
  val : ∀ x < f.valueTab.size, dvValOK tabs f g x = true

theorem dvRel_spec {tabs : Tables} {f g : Func} (h : dvRel tabs f g = true) : DvFacts tabs f g := by
  unfold dvRel at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h4, h5, h6⟩

/-- What `dvOK` says of a devirtualised call: `DvAtom`, the arguments but the first, and the
callee of the aux is the global the code pointer reaches (`dvCode?`). -/
theorem dvOK_spec {tabs : Tables} {f : Func} {u w : Value} (h : dvOK tabs f u w = true) :
    DvAtom u w ∧ w.args = u.args.extract 1 u.args.size ∧
      ∃ a ax n, u.args[0]? = some a ∧ u.aux = some ax ∧ dvCode? tabs f a = some n ∧
        tabs.callee? ax = some n := by
  unfold dvOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hf, hargs⟩, hc⟩ := h
  refine ⟨?_, hargs, ?_⟩
  · unfold dvFieldsOK at hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hf
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  · split at hc
    · next a ax ha hax =>
      simp only [Bool.and_eq_true, Option.isSome_iff_exists, beq_iff_eq] at hc
      obtain ⟨⟨n, hn⟩, hcal⟩ := hc
      exact ⟨a, ax, n, ha, hax, hn, hcal.trans hn⟩
    · cases hc

section
variable {tabs : Tables} {f g : Func} (F : DvFacts tabs f g)
include F

/-- The value of `g` at a value of `f`: the same but for its use count, or devirtualised. -/
theorem val_g {x : ID} {u : Value} (hu : f.value? x = some u) :
    ∃ w, g.value? x = some w ∧
      ((w.op = u.op ∧ w.type = u.type ∧ w.auxInt = u.auxInt ∧ w.aux = u.aux ∧ w.args = u.args ∧
          w.block = u.block) ∨ dvOK tabs f u w = true) := by
  have h := F.val x (CheckFacts.lt_of_value? hu)
  unfold dvValOK at h
  rw [hu] at h
  cases hw : g.value? x with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨w, rfl, ?_⟩
    rcases h with ⟨⟨⟨⟨⟨⟨-, hop⟩, hty⟩, hai⟩, hax⟩, hargs⟩, hb⟩ | h
    · exact .inl ⟨hop.symm, hty.symm, hai.symm, hax.symm, hargs.symm, hb.symm⟩
    · exact .inr h

theorem block_g {b : ID} {fb : Block} (hfb : f.block? b = some fb) : g.block? b = some fb := by
  show (g.blockTab[b]?).join = some fb
  rw [← F.btab]
  exact hfb

/-- A value listed in `f` is listed in `g`. -/
theorem marked_g (hbs : f.blocks = g.blocks) {x : ID} (hm : Marked f x) :
    listedDefs g x = g.value? x := by
  obtain ⟨b, hb, fb, hfb, hx, u, hu, hub⟩ := hm
  obtain ⟨w, hw, hr⟩ := val_g F hu
  have hwb : w.block = b := by
    rcases hr with h | h
    · exact h.2.2.2.2.2.trans hub
    · exact (dvOK_spec h).1.2.2.2.2.2.2.1.symm.trans hub
  exact listedDefs_of_marked ⟨b, hbs ▸ hb, fb, block_g F hfb, hx, w, hw, hwb⟩

/-- **The terms of `f` are `g`'s**: a listed value of `f` as a term over refined atoms is refined
by the same value of `g`. -/
theorem dv_den (hbs : f.blocks = g.blocks) :
    ∀ n x, LM f x → ∀ ρ ρ', ValRef ρ ρ' →
      Sem.Refines (den f.value? tabs ρ n x) (den (listedDefs g) tabs ρ' n x)
  | 0, _, _, _, _, _ => by simp only [den]; exact .poison _
  | n + 1, x, hx, ρ, ρ', hρ => by
    have hm := listedMarks_sound f x hx
    have hlg := marked_g F hbs hm
    obtain ⟨b, hb, fb, hfb, hxb, u, hu, -⟩ := hm
    obtain ⟨w, hw, hr⟩ := val_g F hu
    rw [hw] at hlg
    rcases hr with ⟨hop, hty, hai, hax, hargs, -⟩ | hdv
    · cases ht : termOp u.op with
      | true =>
        rw [den_succ_term hu ht, den_succ_term hlg (by rw [hop]; exact ht), hop, hty, hai, hax,
          hargs]
        refine retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_map fun a ha => ?_))
        exact dv_den hbs n a
          ((closedOK_facts F.cf b hb fb hfb).2 x hxb u hu a (Array.mem_toList_iff.1 ha)) ρ ρ' hρ
      | false =>
        rw [den_succ_atom (fun ⟨v, hv, ht'⟩ => by rw [hu] at hv; cases hv; rw [ht] at ht'; cases ht'),
          den_succ_atom (fun ⟨v, hv, ht'⟩ => by
            rw [hlg] at hv; cases hv; rw [hop, ht] at ht'; cases ht')]
        exact hρ x
    · obtain ⟨⟨h1, h2, -⟩, -⟩ := dvOK_spec hdv
      rw [den_succ_atom (fun ⟨v, hv, ht'⟩ => by
          rw [hu] at hv; cases hv; rw [h1] at ht'; exact absurd ht' (by decide)),
        den_succ_atom (fun ⟨v, hv, ht'⟩ => by
          rw [hlg] at hv; cases hv; rw [h2] at ht'; exact absurd ht' (by decide))]
      exact hρ x

theorem dv_termRef (hbs : f.blocks = g.blocks) {x : ID} (hx : LM f x) :
    TermRef f.value? tabs x (listedDefs g) tabs x :=
  fun n => ⟨n, fun ρ ρ' hρ _ _ => dv_den F hbs n x hx ρ ρ' hρ⟩

end

/-! ## The code pointer -/

/-- A pointer to the start of a global retyped at any shape is itself or `poison` (a global has
no address). -/
private theorem retype_global (n : String) (t : Ty) :
    (Val.ptr ⟨.global n, 0⟩).retype t = .ptr ⟨.global n, 0⟩ ∨
      (Val.ptr ⟨.global n, 0⟩).retype t = .poison := by
  cases t with
  | int w => cases w <;> simp [Val.retype, Ptr.word, Ptr.addr?, Ptr.inWindow, Blk.window?]
  | ptr e => exact .inl (by simp [Val.retype, Ptr.word, Ptr.addr?, Ptr.inWindow, Blk.window?])
  | _ => exact .inr rfl

/-- An `Addr` of the global `n`, as a term, is refined by the pointer to `n`. -/
theorem addr_den {tabs : Tables} {f : Func} {e : ID} {n : String}
    (he : addrSymOf tabs f.valueTab e = some n) (ρ : ID → Val) (k : Nat) :
    Sem.Refines (den f.value? tabs ρ (k + 1) e) (.ptr ⟨.global n, 0⟩) := by
  obtain ⟨y, hy, hop, hval⟩ := addrSymOf_spec he
  have hy' : f.value? e = some y := hy
  rw [den_succ_term hy' (by rw [hop]; rfl), hop, GoFV.Proof.Rules.opVal_addr, hval]
  rcases retype_global n (tabs.ty y.type) with h | h <;> rw [h]
  · exact .ptr _
  · exact .poison _

/-- A code pointer that reaches an `Addr` of the global `n` through compatible copies is, as a
term, refined by the pointer to `n`. -/
theorem copy_addr_den {tabs : Tables} {f : Func} {e : ID} {n : String}
    (he : addrSymOf tabs f.valueTab e = some n) :
    ∀ N a, copyReach tabs f.valueTab N a e = true → ∀ ρ k,
      Sem.Refines (den f.value? tabs ρ k a) (.ptr ⟨.global n, 0⟩)
  | _, _, _, _, 0 => by simp only [den]; exact .poison _
  | 0, a, h, ρ, k + 1 => by
    simp only [copyReach, beq_iff_eq] at h
    subst h
    exact addr_den he ρ k
  | N + 1, a, h, ρ, k + 1 => by
    simp only [copyReach, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact addr_den he ρ k
    · cases hx : Defs.get? f.valueTab a with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨hop, hsz⟩, -⟩, hr⟩ := h
        have hfx : f.value? a = some x := hx
        rw [den_succ_term hfx (by rw [hop]; rfl), LoadFwd.toList_one hsz, List.map_cons, List.map_nil,
          GoFV.Proof.Rules.opVal_pure (by rw [hop]; rfl), hop, LoadFwd.evalPure_copy]
        have ih := copy_addr_den he N _ hr ρ k
        rcases retype_global n (tabs.ty x.type) with h' | h'
        · rw [← h']; exact retype_mono _ ih
        · have := retype_mono (tabs.ty x.type) ih
          rw [h'] at this
          generalize (den f.value? tabs ρ k x.args[0]!).retype (tabs.ty x.type) = y at this ⊢
          cases this
          exact .poison _

/-- The code pointer `dvOK` accepts points to no function but the global `dvCode?` names. -/
theorem dv_codeP {tabs : Tables} {f : Func} {a : ID} {n : String} (h : dvCode? tabs f a = some n) :
    CodeP f.value? tabs a n := by
  intro ρ k s hs
  unfold dvCode? at h
  dsimp only at h
  split at h
  · next hr =>
    have := codeTarget?_mono (copy_addr_den h _ _ hr ρ k) hs
    simp only [codeTarget?, beq_self_eq_true, ite_true, Option.some.injEq] at this
    exact this.symm
  · cases h

theorem extract_one_get {a b : Array ID} (h : b = a.extract 1 a.size) {i : Nat} (hi : i < b.size) :
    b[i]! = a[i + 1]! := by
  subst h
  have hi' : i + 1 < a.size := by simp at hi; omega
  rw [getElem!_pos _ i hi, getElem!_pos _ (i + 1) hi']
  simp [Array.getElem_extract, Nat.add_comm]

section
variable {tabs : Tables} {f g : Func} (F : DvFacts tabs f g) (hbs : f.blocks = g.blocks)
include F hbs

/-- **Atoms' arguments**: an unchanged atom's are the same terms; a devirtualised call's are its
source's but the code pointer, which points to the callee (`dv_codeP`). -/
theorem dv_atomArgs : AtomArgsRefX (SrcInv.triv tabs f) g := by
  intro b hb gb hgb a ha u hu ht
  have hbf : b ∈ f.blocks := by rw [hbs]; exact hb
  have hfb : f.block? b = some gb := by
    show (f.blockTab[b]?).join = some gb
    rw [F.btab]
    exact hgb
  obtain ⟨haf, u', hu', -⟩ := atomsXOK_sub F.atoms hbf hfb hgb ha hu ht
  obtain ⟨w, hw, hr⟩ := val_g F hu'
  rw [hu] at hw; cases hw
  have hargsL : ∀ y ∈ u'.args, LM f y := (closedOK_facts F.cf b hbf gb hfb).2 a haf u' hu'
  rcases hr with ⟨hop, hty, hai, hax, hargs, -⟩ | hdv
  · refine .inl ⟨u', hu', hop.symm, hty.symm, hai.symm, hax.symm, by rw [hargs], fun i hi => ?_⟩
    have hi' : i < u'.args.size := hargs ▸ hi
    have hT : TermRef f.value? tabs u'.args[i]! (listedDefs g) tabs u.args[i]! := by
      rw [hargs]; exact dv_termRef F hbs (hargsL _ (getElem!_mem' hi'))
    exact ⟨fun _ => TermRef.toP hT _ _ _, fun _ _ _ _ _ _ _ => TermRef.toP hT _ _ _⟩
  · obtain ⟨hdv', hargs, a0, ax, n, ha0, hax, hn, hcal⟩ := dvOK_spec hdv
    refine .inr (.inr ⟨u', hu', hdv', fun i hi => ?_, n, ?_, ?_⟩)
    · have hi1 : i + 1 < u'.args.size := by have := hdv'.2.2.2.2.2.1; omega
      have hT : TermRef f.value? tabs u'.args[i + 1]! (listedDefs g) tabs u.args[i]! := by
        rw [extract_one_get hargs hi]
        exact dv_termRef F hbs (hargsL _ (getElem!_mem' hi1))
      exact TermRef.toP hT _ _ _
    · rw [← hdv'.2.2.2.2.1, hax]
      exact hcal
    · obtain ⟨h0, rfl⟩ := Array.getElem?_eq_some_iff.1 ha0
      rw [getElem!_pos _ 0 h0]
      exact dv_codeP hn

/-- **Controls**: `g`'s blocks are `f`'s, their controls the same terms. -/
theorem dv_controls : ControlsRef tabs f g := by
  intro b hb fb gb hfb hgb
  rw [block_g F hfb] at hgb; cases hgb
  exact ⟨rfl, fun k hk =>
    dv_termRef F hbs ((closedOK_facts F.cf b (by rw [hbs]; exact hb) fb hfb).1 _ (getElem!_mem' hk))⟩

end

/-- **Devirtualised interface calls refine**: an accepted layer (`dvRel`) refines its input under
monotone contracts. -/
theorem dv_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (hf : check ce f = .ok ())
    (hg : check ce' g = .ok ()) (h : dvRel tabs f g = true) :
    RefinesUnder Env.Mono tabs g tabs f := by
  have F := dvRel_spec h
  have hbs : f.blocks = g.blocks := (atomsXOK_spec F.atoms).blocks
  exact atomSimX_refines hf hg (atomsXOK_spec F.atoms) (SrcInv.triv tabs f) (dv_atomArgs F hbs)
    (TermStepRef.toStepRefsP (ControlsRef.toTermStepRef (dv_controls F hbs)
      fun b _ fb gb hfb hgb => by
        rw [block_g F hfb] at hgb; cases hgb
        exact ⟨rfl, rfl, rfl⟩) _) (atomsXOK_dropNP F.atoms _)

end GoFV.Proof.Pass.Devirt
