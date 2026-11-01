import GoFV.Proof.Pass.FuseRedirectPres
import GoFV.Proof.ProveCheck.DecideSound
import GoFV.Proof.AtomSimDen
import GoFV.Proof.Avail
import GoFV.Proof.Eval

/-!
# The redirect decision is sound

When the source leaves `p` along `p → b`, its registers are a valuation under which the path
facts of the decision hold (`asmHolds`): lemma (D) at `p` makes every term node placed in a
block dominating `p` hold its value over its arguments' registers, so along the dependency
order the checker lists (`topoOK`) every such node's term (`den`) settles on its register
(`conv`); `p`'s control holds the branch taken; registers are typed. Then `decides_sound` (or
the signed range test, `eqDisjoint_sound`) fixes the boolean `b`'s control takes (`decide_ctl`):
the source leaves `b` towards `child`.
-/

namespace GoFV.Proof.FuseRedirect

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Redir GoFV.Opt.RewriteCheck
  GoFV.Opt.ProveCheck GoFV.Proof GoFV.Proof.Term GoFV.Proof.AtomSim GoFV.Proof.ProveCheck Dom

variable {tabs : Tables} {f : Func}

theorem isTerm_iff {x : ID} : isTerm f x = true ↔ IsTerm f.value? x := by
  unfold isTerm IsTerm
  cases f.value? x <;> simp

theorem mem_of_contains {l : List ID} {x : ID} (h : l.contains x = true) : x ∈ l := by
  simpa using h

/-- Arguments that settle settle together. -/
theorem conv_list {D : ID → Option Value} {ρ : ID → Val} {fr : Frame} :
    ∀ (l : List ID), (∀ a ∈ l, ∃ N, ∀ n, N ≤ n → den D tabs ρ n a = rv fr a) →
      ∃ N, ∀ n, N ≤ n → l.map (den D tabs ρ n) = l.map (rv fr)
  | [], _ => ⟨0, fun _ _ => rfl⟩
  | a :: l, h => by
    obtain ⟨N1, h1⟩ := h a List.mem_cons_self
    obtain ⟨N2, h2⟩ := conv_list l fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    rw [List.map_cons, List.map_cons, h1 n (by omega), h2 n (by omega)]

/-- An atom's term is its register (from fuel 1). -/
theorem conv_atom {fr : Frame} {x : ID} (ht : ¬ IsTerm f.value? x) :
    ∃ N, ∀ n, N ≤ n → den f.value? tabs (rv fr) n x = rv fr x :=
  ⟨1, fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact den_succ_atom ht⟩

section
variable {ce : CheckEnv} {env : Env} {fr : Frame} {p : ID}

/-- The values placed in blocks dominating `p`. -/
def DomP (f : Func) (p x : ID) : Prop := ∃ v, Placed f x v ∧ SDom f v.block p

/-- A term node's value under lemma (D): its term over its arguments' registers. -/
theorem term_val (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a p) fr) {x : ID} {v : Value}
    (hP : Placed f x v) (hd : SDom f v.block p) (ht : termOp v.op = true) (hid : v.id = x) :
    rv fr x = (GoFV.Proof.Rules.opVal tabs v.op (tabs.ty v.type) v.auxInt v.aux
      (v.args.toList.map (rv fr))).retype (tabs.ty v.type) := by
  have hnp : v.op ≠ .Phi := fun h => by rw [h] at ht; exact absurd ht (by decide)
  obtain ⟨y, hy, hev⟩ := hdi x v hP hd
  rw [rv_of hy, evalValue_term ht (hev hnp)]
  have ht' : (Ctx.make tabs f).tys[v.id]? = some (tabs.ty v.type) := by
    rw [hid]; exact tys_of_value hP.1
  rw [ht']
  rfl

/-- The arguments of a node dominating `p` dominate `p`. -/
theorem arg_domP (hwf : WF ce f) (hu : UseDom f) {x : ID} (hx : DomP f p x) {v : Value}
    (hv : f.value? x = some v) (hnp : v.op ≠ .Phi) {a : ID} (ha : a ∈ v.args) : DomP f p a := by
  obtain ⟨v', hP, hd⟩ := hx
  rw [hP.1] at hv; cases hv
  obtain ⟨hv, hbm, blk, hblk, hxv⟩ := hP
  have hsd := hu.domRel.uses hbm hblk hd.left hxv hv hnp ha
  obtain ⟨u, U, hPa, hub, -, -, -⟩ :=
    blockOf_listed hwf (hwf.argListed _ blk x v ⟨⟨hbm, hblk⟩, hxv, hv⟩ a ha)
  exact ⟨u, hPa, by rw [hub]; exact SDom.trans hsd hd⟩

theorem placed_id (hwf : WF ce f) {x : ID} {v : Value} (hP : Placed f x v) : v.id = x := by
  obtain ⟨hv, hbm, blk, hblk, hxv⟩ := hP
  obtain ⟨w, hw, hwid, -⟩ := hwf.valueId _ blk ⟨hbm, hblk⟩ x hxv
  rw [hv] at hw; cases hw; exact hwid

/-- **Terms settle on their registers**, along a dependency order. -/
theorem conv (hwf : WF ce f) (hu : UseDom f)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a p) fr) :
    ∀ (L : List ID), topoOK f L = true → ∀ x ∈ L, DomP f p x →
      ∃ N, ∀ n, N ≤ n → den f.value? tabs (rv fr) n x = rv fr x
  | [], _, x, hx, _ => by simp at hx
  | y :: rest, hL, x, hx, hdx => by
    unfold topoOK at hL
    rw [Bool.and_eq_true] at hL
    have ih := conv hwf hu hdi rest hL.2
    rcases List.mem_cons.1 hx with rfl | hx'
    · by_cases ht : IsTerm f.value? x
      · obtain ⟨v, hv, hvt⟩ := ht
        obtain ⟨v', hP, hd⟩ := hdx
        have hvv : v' = v := by rw [hP.1] at hv; cases hv; rfl
        subst hvv
        have hnp : v'.op ≠ .Phi := fun h => by rw [h] at hvt; exact absurd hvt (by decide)
        have hargs : ∀ a ∈ v'.args.toList, ∃ N, ∀ n, N ≤ n →
            den f.value? tabs (rv fr) n a = rv fr a := by
          intro a ha
          have ha' := Array.mem_toList_iff.1 ha
          have hda := arg_domP hwf hu ⟨v', hP, hd⟩ hP.1 hnp ha'
          by_cases hat : IsTerm f.value? a
          · have hin : a ∈ rest := by
              have h1 := hL.1
              rw [show Redir.argsOf f x = v'.args by simp [Redir.argsOf, hP.1]] at h1
              have := (Array.all_eq_true'.1 h1) a ha'
              rw [Bool.or_eq_true, Bool.not_eq_true'] at this
              rcases this with h | h
              · rw [← Bool.not_eq_true, isTerm_iff] at h; exact absurd hat h
              · exact mem_of_contains h
            exact ih a hin hda
          · exact conv_atom hat
        obtain ⟨N, hN⟩ := conv_list _ hargs
        refine ⟨N + 1, fun n hn => ?_⟩
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [den_succ_term hP.1 hvt, hN m (by omega), term_val hdi hP hd hvt (placed_id hwf hP)]
      · exact conv_atom ht
    · exact ih x hx' hdx

/-- A node dominating `p` settles: through the dependency order if it is a term. -/
theorem conv_root (hwf : WF ce f) (hu : UseDom f)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a p) fr) {L : List ID}
    (hL : topoOK f L = true) {x : ID} (hxL : !isTerm f x || L.contains x) (hdx : DomP f p x) :
    ∃ N, ∀ n, N ≤ n → den f.value? tabs (rv fr) n x = rv fr x := by
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hxL
  rcases hxL with h | h
  · rw [← Bool.not_eq_true, isTerm_iff] at h; exact conv_atom h
  · exact conv hwf hu hdi L hL x (mem_of_contains h) hdx

end

/-- The same term has the same value. -/
theorem den_sameTerm {ρ : ID → Val} {u w : ID} (h : sameTerm f u w = true) (n : Nat) :
    den f.value? tabs ρ (n + 1) w = den f.value? tabs ρ (n + 1) u := by
  unfold sameTerm at h
  split at h
  · rename_i a c hu hw
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨ht, hop⟩, hty⟩, hai⟩, hax⟩, hargs⟩ := h
    rw [den_succ_term hu ht, den_succ_term hw (hop ▸ ht), hop, hty, hai, hax, hargs]
  · cases h

/-- Registers of a typed frame are fixed by `retype` at their values' shapes. -/
theorem typed_rv {fr : Frame} (ht : Proof.Typed (Ctx.make tabs f) fr) :
    Term.Typed f.value? tabs (rv fr) := by
  intro a _ hs
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  have hsh : shape f.value? tabs a = tabs.ty v.type := by simp [shape, hv]
  rw [hsh]
  unfold rv
  cases hr : fr.regs[a]? with
  | none => exact retype_poison' _
  | some o =>
    cases o with
    | none => exact retype_poison' _
    | some y =>
      have := ht a y hr
      rw [tys_of_value hv] at this
      exact this

/-- **The path facts along `p → b` hold** of the registers at the end of `p`. -/
theorem asmHolds {ce : CheckEnv} {env : Env} {fr : Frame} {p : ID} (hwf : WF ce f)
    (hu : UseDom f) (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a p) fr)
    (htyp : Proof.Typed (Ctx.make tabs f) fr) {cp ctl : ID} {pv : Bool}
    (hL : topoOK f (termClosure f [cp, ctl]) = true)
    (hcpL : (!isTerm f cp || (termClosure f [cp, ctl]).contains cp) = true)
    (hcpD : DomP f p cp) (hcpv : rv fr cp = .bool pv) :
    AsmHolds f.value? tabs (rv fr) (asm f cp ctl pv) := by
  obtain ⟨N, hN⟩ := conv_root hwf hu hdi hL hcpL hcpD
  refine ⟨fun c v hc => ?_, fun _ _ _ hz => by simp [asm] at hz,
    fun _ _ _ _ hz => by simp [asm] at hz, typed_rv htyp⟩
  unfold asm at hc
  rcases List.mem_cons.1 hc with h | h
  · cases h
    exact ⟨N, fun n hn => (hN n hn).trans hcpv⟩
  · split at h
    · rename_i hcg
      simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨N + 1, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [den_sameTerm hcg, hN (m + 1) (by omega), hcpv]
    · simp at h

/-- What `zextOf` says. -/
theorem zextOf_spec {s z : ID} {a b : Width} (h : zextOf tabs f s = some (z, a, b)) :
    ∃ e, f.value? s = some e ∧ termOp e.op = true ∧ rTab.lookup e.op = some (.zext a b) ∧
      e.args.toList = [z] ∧ a.bits ≤ b.bits ∧ tabs.ty e.type = .int b := by
  unfold zextOf at h
  split at h
  · rename_i e he
    split at h
    · rename_i ht
      split at h
      · rename_i a' b' z' hk hl
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          refine ⟨e, he, ht, hk, hl, hc.1, width_some ?_⟩
          simpa [intAt] using hc.2
        · cases h
      · cases h
    · cases h
  · cases h

/-- **The ranges through zero extensions hold** where the path facts do. -/
theorem extInv_holds {ρ : ID → Val} {A : Asm} (hA : AsmHolds f.value? tabs ρ A) :
    ∀ z w r, (z, w, r) ∈ extInv tabs f A → ∀ n (y : BitVec w.bits),
      den f.value? tabs ρ n z = .int w y → r.Mem y := by
  intro z w r hm n y hy
  unfold extInv at hm
  obtain ⟨fact, -, hm⟩ := List.mem_flatMap.1 hm
  split at hm
  · rename_i s1 s2 w' rel _
    obtain ⟨s, -, hs⟩ := List.mem_filterMap.1 hm
    split at hs
    · rename_i z' a b hz
      split at hs
      · rename_i hbw
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl, rfl⟩ := hs
        have hbw' : b = w' := by simpa using hbw
        subst hbw'
        obtain ⟨e, he, ht, hk, hl, hab, hty⟩ := zextOf_spec hz
        have hden : den f.value? tabs ρ (n + 1) s = .int b (y.setWidth b.bits) := by
          rw [den_succ_term he ht, hl, List.map_cons, List.map_nil, hy, rTab_opVal hk, hty]
          simp [rOpEval, Conv.zeroExt, Sem.int1, retype_int_self]
        obtain ⟨m1, m2, -, -⟩ := rng_sound hA fuel b s (n + 1) _ hden
        have hlt : y.toNat < 2 ^ b.bits := Nat.lt_of_lt_of_le y.isLt (pow_le_pow_bits hab)
        have he' : (y.setWidth b.bits).toNat = y.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt]
        rw [he'] at m1 m2
        have := y.isLt
        exact Rng.mem_ofU (Width.one_le _) m1 (by omega)
      · cases hs
    · cases hs
  · simp at hm

/-- **The decision's assumptions hold** of the registers at the end of `p`. -/
theorem asmXHolds {ce : CheckEnv} {env : Env} {fr : Frame} {p : ID} (hwf : WF ce f)
    (hu : UseDom f) (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a p) fr)
    (htyp : Proof.Typed (Ctx.make tabs f) fr) {cp ctl : ID} {pv : Bool}
    (hL : topoOK f (termClosure f [cp, ctl]) = true)
    (hcpL : (!isTerm f cp || (termClosure f [cp, ctl]).contains cp) = true)
    (hcpD : DomP f p cp) (hcpv : rv fr cp = .bool pv) :
    AsmHolds f.value? tabs (rv fr) (asmX tabs f cp ctl pv) := by
  have h0 := asmHolds hwf hu hdi htyp hL hcpL hcpD hcpv
  exact ⟨h0.facts, extInv_holds h0, fun _ _ _ _ hz => by simp [asmX, asm] at hz, h0.typed⟩

/-- The signed range test is sound. -/
theorem eqDisjoint_sound {ρ : ID → Val} {A : Asm} (hA : AsmHolds f.value? tabs ρ A) {ctl : ID}
    {v : Bool} (h : eqDisjoint tabs f A ctl v = true) {n : Nat} {bb : Bool}
    (hc : den f.value? tabs ρ (n + 1) ctl = .bool bb) : bb = v := by
  unfold eqDisjoint at h
  split at h
  · rename_i cv hcv
    rw [Bool.and_eq_true] at h
    obtain ⟨ht, h⟩ := h
    split at h
    · rename_i a b w isEq hl hk
      rw [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hdis⟩ := h
      rw [den_succ_term hcv ht,
        show cv.args.toList.map (den f.value? tabs ρ n) = [den f.value? tabs ρ n a,
          den f.value? tabs ρ n b] by rw [hl]; rfl, cTab_opVal hk] at hc
      obtain ⟨X, Y, hl', he⟩ := cmp_val (r := .eq isEq) hc
      simp only [List.cons.injEq, and_true] at hl'
      have hx := rng_sound hA fuel w a n X hl'.1
      have hy := rng_sound hA fuel w b n Y hl'.2
      have hne : X ≠ Y := by
        rintro rfl
        obtain ⟨-, -, hx1, hx2⟩ := hx
        obtain ⟨-, -, hy1, hy2⟩ := hy
        rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hdis
        rcases hdis with h | h <;> omega
      rw [← he]
      cases isEq <;> simp [relVal, hne]
    · cases h
  · cases h

/-- **The decision fixes `b`'s control**: once its term settles on `Y`, a boolean `Y` is `v`. -/
theorem decide_ctl {ρ : ID → Val} {A : Asm} (hA : AsmHolds f.value? tabs ρ A) {ctl : ID}
    {v : Bool} (hd : (decides f.value? tabs A fuel fuel ctl v || eqDisjoint tabs f A ctl v) = true)
    {N : Nat} {Y : Val} (hN : ∀ n, N ≤ n → den f.value? tabs ρ n ctl = Y) {bb : Bool}
    (hY : Y = .bool bb) : bb = v := by
  rw [Bool.or_eq_true] at hd
  rcases hd with hd | hd
  · exact decides_sound hA fuel ctl v hd N bb ((hN N (Nat.le_refl _)).trans hY)
  · exact eqDisjoint_sound hA hd ((hN (N + 1) (by omega)).trans hY)

end GoFV.Proof.FuseRedirect
