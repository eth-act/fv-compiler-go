import GoFV.Proof.Pass.CSEEval
import GoFV.Proof.Pass.CSEOp
import GoFV.Proof.Pass.CSEMem

/-!
# cse: a representative holds its value

Within one block's evaluation: the source has evaluated, in order, the values `pre` into its
frame `S`, the target the values `pre'` into `T`; `B` are the values from before the block
(other blocks' and this block's `Phi`s), where the frames agree and every value and its
representative hold the same register. `rep_corr`: for every source-evaluated value `b` whose
representative the target has evaluated, `T[rep b] = S[b]`, by induction along `pre`: `rep b`
and `b` are congruent (`Congr`: the same op and the same arguments in `g`, which are the
representatives of `b`'s arguments, already related), or `rep b = b` and the target's arguments
are the representatives of the source's.
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.SSA.Sem

/-- What `rep_corr` reads: one block `bid`'s evaluation in source and target. -/
structure Corr (env : Env) (tabs : Tables) (f g : Func) (rw : Array (Option ID)) (bid : ID)
    (B : ID → Prop) (S T : Frame) (pre pre' : List ID) : Prop where
  rel : CRel tabs f g rw
  frame : T = { S with regs := T.regs }
  bS : ∀ x, B x → ∃ v y, f.value? x = some v ∧ S.regs[x]? = some (some y) ∧
    (v.op ≠ .Phi → evalValue env (Ctx.make tabs f) S v = .ok y)
  bT : ∀ x, B x → T.regs[x]? = S.regs[x]?
  bRep : ∀ x, B x → B (Opt.CSE.rep rw x) ∧ S.regs[Opt.CSE.rep rw x]? = S.regs[x]?
  bCl : ∀ x v, B x → f.value? x = some v → v.op ≠ .Phi → ∀ a ∈ v.args, B a
  bOut : ∀ x v, B x → f.value? x = some v → v.block ≠ bid ∨ v.op = .Phi
  sPre : ∀ x ∈ pre, ∃ v y, f.value? x = some v ∧ v.op ≠ .Phi ∧ v.block = bid ∧
    S.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) S v = .ok y
  sOrd : ∀ (j : Nat) x, pre[j]? = some x → ∀ v, f.value? x = some v → ∀ a ∈ v.args,
    B a ∨ ∃ i < j, pre[i]? = some a
  tPre : ∀ x ∈ pre', ∃ v y, g.value? x = some v ∧ v.op ≠ .Phi ∧ v.block = bid ∧
    T.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs g) T v = .ok y
  tArgs : ∀ x ∈ pre', ∀ v, g.value? x = some v → ∀ a ∈ v.args, B a ∨ a ∈ pre'
  ts : ∀ x ∈ pre, x ∈ pre' → T.regs[x]? = S.regs[x]?
  roots : ∀ x ∈ pre', Opt.CSE.rootNode f x = true → x ∈ pre
  load2 : ∀ x v, f.value? x = some v → v.op = .Load → (B x ∨ x ∈ pre ∨ x ∈ pre') →
    v.args.size = 2
  ids : ∀ x v, f.value? x = some v → (B x ∨ x ∈ pre ∨ x ∈ pre') → v.id = x

variable {env : Env} {tabs : Tables} {f g : Func} {rw : Array (Option ID)} {bid : ID}
  {B : ID → Prop} {S T : Frame} {pre pre' : List ID}

namespace Corr

variable (C : Corr env tabs f g rw bid B S T pre pre')
include C

theorem tys_f {x : ID} {v : Value} (h : f.value? x = some v) :
    (Ctx.make tabs f).tys[x]? = some (tabs.ty v.type) := tys_of_value h

theorem notB_of_pre {x : ID} (hx : x ∈ pre) : ¬ B x := fun hB => by
  obtain ⟨v, y, hv, hph, hb, -⟩ := C.sPre x hx
  rcases C.bOut x v hB hv with h | h
  · exact h hb
  · exact hph h

/-- The target's version of a value of `f`. -/
theorem gval {x : ID} {fv : Value} (hfv : f.value? x = some fv) :
    ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧ gv.op = fv.op ∧ gv.aux = fv.aux ∧
      gv.auxInt = fv.auxInt ∧ gv.type = fv.type ∧ gv.block = fv.block ∧
      ArgsRel rw fv.op fv.args gv.args :=
  C.rel.value x fv hfv

/-- Each source argument's representative is a target argument. -/
theorem rep_mem_of_argsRel {op : Op} {fa ga : Array ID} (h : ArgsRel rw op fa ga) {a : ID}
    (ha : a ∈ fa) : Opt.CSE.rep rw a ∈ ga := by
  rcases h with rfl | ⟨-, -, rfl⟩
  · exact Array.mem_map_of_mem ha
  · apply Array.mem_map_of_mem
    rcases fa with ⟨l⟩
    match l, ha with
    | x :: y :: l, ha =>
      have hsw : (List.toArray (x :: y :: l)).swapIfInBounds 0 1 = List.toArray (y :: x :: l) := by
        simp [Array.swapIfInBounds, Array.swap]
      rw [hsw]
      simp only [List.mem_toArray, List.mem_cons] at ha ⊢
      rcases ha with h | h | h <;> simp [h]
    | [], ha => simp at ha
    | [x], ha => simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha; subst ha; simp [Array.swapIfInBounds]

theorem ctx_tabs : (Ctx.make tabs g).tabs = (Ctx.make tabs f).tabs := rfl
theorem ctx_act : (Ctx.make tabs g).act = (Ctx.make tabs f).act := rfl
theorem ctx_params : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
  simp only [Ctx.make, abiParams, C.rel.ownAux]

/-- A target value whose arguments' registers in `T` are its source arguments' in `S`
evaluates as its source. -/
theorem eval_rel {x : ID} {fv gv : Value} (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (hxid : fv.id = x) (hargs : ∀ a ∈ fv.args, ∃ y, S.regs[a]? = some (some y) ∧
      T.regs[Opt.CSE.rep rw a]? = some (some y)) :
    evalValue env (Ctx.make tabs g) T gv = evalValue env (Ctx.make tabs f) S fv := by
  obtain ⟨gv', hgv', hid, hop, hax, hai, hty, -, hrel⟩ := C.gval hfv
  rw [hgv] at hgv'; cases hgv'
  obtain ⟨vs, hS, hT⟩ := argVals_rel hrel hargs
  refine evalValue_rel hop hax hai hid ?_ rfl C.ctx_params rfl C.frame hS hT
  rw [hid, hxid, tys_of_value hgv, tys_of_value hfv, hty]

/-- A non-`Phi` value from before the block evaluates in the target as in the source. -/
theorem baseEval {x : ID} (hB : B x) {fv : Value} (hfv : f.value? x = some fv)
    (hph : fv.op ≠ .Phi) :
    ∃ gv y, g.value? x = some gv ∧ T.regs[x]? = some (some y) ∧
      evalValue env (Ctx.make tabs g) T gv = .ok y ∧
      evalValue env (Ctx.make tabs f) S fv = .ok y := by
  obtain ⟨v, y, hv, hy, hev⟩ := C.bS x hB
  rw [hfv] at hv; cases hv
  obtain ⟨gv, hgv, -⟩ := C.gval hfv
  refine ⟨gv, y, hgv, by rw [C.bT x hB, hy], ?_, hev hph⟩
  rw [C.eval_rel hfv hgv (C.ids x fv hfv (.inl hB)) fun a ha => ?_, hev hph]
  have haB := C.bCl x fv hB hfv hph a ha
  obtain ⟨-, ya, -, hya, -⟩ := C.bS a haB
  obtain ⟨hrB, hrS⟩ := C.bRep a haB
  exact ⟨ya, hya, by rw [C.bT _ hrB, hrS, hya]⟩

end Corr

theorem bind_ok {r : Res Val} {k : Val → Val} {s : Val} (h : r.bind (fun x => .ok (k x)) = .ok s) :
    ∃ x, r = .ok x ∧ s = k x := by
  cases r with
  | ok x => exact ⟨x, rfl, by cases h; rfl⟩
  | panic e m => cases h
  | stuck msg => cases h

theorem rep_none {rw : Array (Option ID)} {x : ID} (h : rw.getD x none = none) :
    Opt.CSE.rep rw x = x := by
  unfold Opt.CSE.rep; rw [h]; rfl

theorem rep_some {rw : Array (Option ID)} {x r : ID} (h : rw.getD x none = some r) :
    Opt.CSE.rep rw x = r := by
  unfold Opt.CSE.rep; rw [h]; rfl

/-- A target argument is the representative of a source argument. -/
theorem mem_of_argsRel {rw : Array (Option ID)} {op : Op} {fa ga : Array ID}
    (h : ArgsRel rw op fa ga) {x : ID} (hx : x ∈ ga) : ∃ a ∈ fa, x = Opt.CSE.rep rw a := by
  rcases h with rfl | ⟨-, -, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := Array.mem_map.1 hx; exact ⟨a, ha, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := Array.mem_map.1 hx
    refine ⟨a, ?_, rfl⟩
    rcases fa with ⟨l⟩
    match l, ha with
    | x :: y :: l, ha =>
      have hsw : (List.toArray (x :: y :: l)).swapIfInBounds 0 1 = List.toArray (y :: x :: l) := by
        simp [Array.swapIfInBounds, Array.swap]
      rw [hsw] at ha
      simp only [List.mem_toArray, List.mem_cons] at ha ⊢
      rcases ha with h | h | h <;> simp [h]
    | [], ha => simp [Array.swapIfInBounds] at ha
    | [x], ha => simpa [Array.swapIfInBounds] using ha

namespace Corr

variable (C : Corr env tabs f g rw bid B S T pre pre')
include C

/-- The argument relation for a source-evaluated value at position `j` of `pre`, given the
claim for the earlier ones. -/
theorem argIH {j : Nat} {b : ID} (hj : pre[j]? = some b) {fb : Value} (hfb : f.value? b = some fb)
    (ih : ∀ i < j, ∀ a, pre[i]? = some a → (B (Opt.CSE.rep rw a) ∨ Opt.CSE.rep rw a ∈ pre') →
      T.regs[Opt.CSE.rep rw a]? = S.regs[a]?)
    {a : ID} (ha : a ∈ fb.args) (hr : B (Opt.CSE.rep rw a) ∨ Opt.CSE.rep rw a ∈ pre') :
    ∃ y, S.regs[a]? = some (some y) ∧ T.regs[Opt.CSE.rep rw a]? = some (some y) := by
  rcases C.sOrd j b hj fb hfb a ha with hB | ⟨i, hi, hia⟩
  · obtain ⟨-, y, -, hy, -⟩ := C.bS a hB
    obtain ⟨hrB, hrS⟩ := C.bRep a hB
    exact ⟨y, hy, by rw [C.bT _ hrB, hrS, hy]⟩
  · obtain ⟨-, y, -, -, -, hy, -⟩ := C.sPre a (List.mem_of_getElem? hia)
    exact ⟨y, hy, by rw [ih i hi a hia hr, hy]⟩

/-- The target's arguments of a target-evaluated value (or one from before the block) are
target-evaluated or from before the block. -/
theorem gArgs {c : ID} (hc : B c ∨ c ∈ pre') {fr gr : Value} (hfr : f.value? c = some fr)
    (hgr : g.value? c = some gr) (hph : fr.op ≠ .Phi) :
    ∀ a ∈ gr.args, B a ∨ a ∈ pre' := by
  intro a ha
  rcases hc with hB | hp
  · obtain ⟨gr', hgr', -, -, -, -, -, -, hrel⟩ := C.gval hfr
    rw [hgr] at hgr'; cases hgr'
    obtain ⟨a', ha', rfl⟩ := mem_of_argsRel hrel ha
    exact .inl (C.bRep a' (C.bCl c fr hB hfr hph a' ha')).1
  · exact C.tArgs c hp gr hgr a ha

/-- `T`'s register of a target-evaluated value (or one from before the block) is its
evaluation in the target. -/
theorem tEval {c : ID} (hc : B c ∨ c ∈ pre') {fr gr : Value} (hfr : f.value? c = some fr)
    (hgr : g.value? c = some gr) (hph : fr.op ≠ .Phi) :
    ∃ t, T.regs[c]? = some (some t) ∧ evalValue env (Ctx.make tabs g) T gr = .ok t := by
  rcases hc with hB | hp
  · obtain ⟨gr', t, hgr', ht, hev, -⟩ := C.baseEval hB hfr hph
    rw [hgr] at hgr'; cases hgr'
    exact ⟨t, ht, hev⟩
  · obtain ⟨gr', t, hgr', -, -, ht, hev⟩ := C.tPre c hp
    rw [hgr] at hgr'; cases hgr'
    exact ⟨t, ht, hev⟩

end Corr

theorem argVals_head {fr : Frame} {as : Array ID} {r : Val} {rest : List Val} {a : ID}
    (h : argVals fr as = some (r :: rest)) (ha : as[0]? = some a) : fr.regs[a]? = some (some r) := by
  unfold argVals at h
  rcases as with ⟨l⟩
  match l, h, ha with
  | x :: l, h, ha =>
    simp at ha
    subst ha
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, List.cons.injEq] at h
    obtain ⟨y, hy, _, _, rfl, -⟩ := h
    cases hx : fr.regs[x]? with
    | none => rw [hx] at hy; cases hy
    | some o => rw [hx] at hy; simp at hy; rw [hy]
  | [], h, ha => simp at ha

theorem argVals_two {fr : Frame} {as : Array ID} {vs : List Val} (h : argVals fr as = some vs)
    (hsz : as.size = 2) : ∃ p m yp ym, as = #[p, m] ∧ vs = [yp, ym] ∧
      fr.regs[p]? = some (some yp) ∧ fr.regs[m]? = some (some ym) := by
  rcases as with ⟨l⟩
  match l, hsz, h with
  | [p, m], _, h =>
    unfold argVals at h
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨yp, hp, l1, ⟨ym, hm, l2, rfl, rfl⟩, rfl⟩ := h
    refine ⟨p, m, yp, ym, rfl, rfl, ?_, ?_⟩
    · cases hx : fr.regs[p]? with
      | none => rw [hx] at hp; cases hp
      | some o => rw [hx] at hp; simp at hp; rw [hp]
    · cases hx : fr.regs[m]? with
      | none => rw [hx] at hm; cases hm
      | some o => rw [hx] at hm; simp at hm; rw [hm]

namespace Corr

variable (C : Corr env tabs f g rw bid B S T pre pre')
include C

/-- The source-evaluated values and those from before the block (`load_memEnd`'s set). -/
theorem memA_facts :
    (∀ x, (B x ∨ x ∈ pre) → ∃ v y, f.value? x = some v ∧ S.regs[x]? = some (some y) ∧
      (v.op ≠ .Phi → evalValue env (Ctx.make tabs f) S v = .ok y)) ∧
    (∀ x v, (B x ∨ x ∈ pre) → f.value? x = some v → v.op ≠ .Phi → ∀ a ∈ v.args, B a ∨ a ∈ pre) := by
  refine ⟨fun x hx => ?_, fun x v hx hv hph a ha => ?_⟩
  · rcases hx with hB | hp
    · exact C.bS x hB
    · obtain ⟨v, y, hv, -, -, hy, hev⟩ := C.sPre x hp
      exact ⟨v, y, hv, hy, fun _ => hev⟩
  · rcases hx with hB | hp
    · exact .inl (C.bCl x v hB hv hph a ha)
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hp
      rcases C.sOrd j x hj v hv a ha with h | ⟨i, -, hi⟩
      · exact .inl h
      · exact .inr (List.mem_of_getElem? hi)

/-- **Representatives hold their values**, for the values at the positions of `pre`. -/
theorem step_corr : ∀ (j : Nat) (b : ID), pre[j]? = some b →
    (B (Opt.CSE.rep rw b) ∨ Opt.CSE.rep rw b ∈ pre') →
    T.regs[Opt.CSE.rep rw b]? = S.regs[b]? := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro b hj hr
  have hbpre := List.mem_of_getElem? hj
  obtain ⟨fb, s, hfb, hph, -, hs, hev⟩ := C.sPre b hbpre
  have hbid : fb.id = b := C.ids b fb hfb (.inr (.inl hbpre))
  have hargIH := fun {a} (ha : a ∈ fb.args) hra => C.argIH hj hfb (fun i hi a ha hr => ih i hi a ha hr) ha hra
  cases hrw : rw.getD b none with
  | none =>
    rw [rep_none hrw] at hr ⊢
    have hbp : b ∈ pre' := hr.resolve_left (C.notB_of_pre hbpre)
    obtain ⟨gb, hgb, -, -, -, -, -, -, hrel⟩ := C.gval hfb
    obtain ⟨t, ht, hevT⟩ := C.tEval (.inr hbp) hfb hgb hph
    have := C.eval_rel hfb hgb hbid fun a ha =>
      hargIH ha (C.tArgs b hbp gb hgb _ (C.rep_mem_of_argsRel hrel ha))
    rw [hevT, hev] at this; cases this
    rw [ht, hs]
  | some c =>
    rw [rep_some hrw] at hr ⊢
    obtain ⟨hcr, fx, fr, gx, gr, hfx, hfr, hgx, hgr, hcg, hroot, -⟩ := C.rel.subst b c hrw
    rw [hfb] at hfx; cases hfx
    obtain ⟨hop, hax, hai, hty, hargs⟩ := hcg
    have hphr : fr.op ≠ .Phi := by rw [hop]; exact hph
    obtain ⟨t, ht, hevT⟩ := C.tEval hr hfr hgr hphr
    have hgA := C.gArgs hr hfr hgr hphr
    obtain ⟨gx', hgx', hgid, hgop, hgax, hgai, hgty, -, hrelx⟩ := C.gval hfb
    rw [hgx] at hgx'; cases hgx'
    obtain ⟨gr', hgr', hrid, hrop, hrax, hrai, hrty, hrbl, hrelr⟩ := C.gval hfr
    rw [hgr] at hgr'; cases hgr'
    have hcid : fr.id = c := C.ids c fr hfr (hr.elim .inl fun h => .inr (.inr h))
    have htyx : (Ctx.make tabs g).tys[gx.id]?.getD .other = tabs.ty fb.type := by
      rw [hgid, hbid, tys_of_value hgx, hgty]; rfl
    have htyr : (Ctx.make tabs g).tys[gr.id]?.getD .other = tabs.ty fb.type := by
      rw [hrid, hcid, tys_of_value hgr, hrty, hty]; rfl
    have htyf : (Ctx.make tabs f).tys[fb.id]?.getD .other = tabs.ty fb.type := by
      rw [hbid, tys_of_value hfb]; rfl
    rw [ht, hs]
    suffices t = s by rw [this]
    obtain ⟨vT, hvT⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs g) (fr := T) (v := gr)
      fun msg h => by rw [hevT] at h; cases h
    obtain ⟨vS, hvS⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S) (v := fb)
      fun msg h => by rw [hev] at h; cases h
    rw [evalValue_of_argVals hvT, htyr] at hevT
    obtain ⟨r2, hr2, rfl⟩ := bind_ok hevT
    have hnc : Op.commutative .NilCheck = false := rfl
    have hlc : Op.commutative .Load = false := rfl
    rcases hargs with heq | ⟨-, h0, hspec⟩
    · -- the same arguments in `g`
      have hevx := C.eval_rel hfb hgx hbid fun a ha =>
        hargIH ha (hgA _ (heq ▸ C.rep_mem_of_argsRel hrelx ha))
      rw [hev, evalValue_of_argVals (heq ▸ hvT), htyx] at hevx
      obtain ⟨r1, hr1, hr1s⟩ := bind_ok hevx
      rw [hr1s]
      congr 1
      rcases hroot with hnr | hnc'
      · exact (evalOp_ok_id (u := gx) (v := gr) (by rw [hrop, hgop, hop]) (by rw [hrax, hgax, hax])
          (by rw [hrai, hgai, hai]) (by rw [hgop]; exact hnr) hr1 hr2).symm
      · obtain ⟨rest1, h1⟩ := evalOp_nilCheck_ok (by rw [hgop]; exact hnc') hr1
        obtain ⟨rest2, h2⟩ := evalOp_nilCheck_ok (by rw [hrop, hop]; exact hnc') hr2
        rw [h1] at h2; cases h2; rfl
    · rw [evalValue_of_argVals hvS, htyf] at hev
      obtain ⟨r1, hr1, rfl⟩ := bind_ok hev
      congr 1
      rcases hspec with ⟨hla, hsome⟩ | hnil | ⟨hld, hok⟩
      · -- `LocalAddr`: the address of the named local
        obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hsome
        rw [evalOp_localAddr hla hn] at hr1
        rw [evalOp_localAddr (by rw [hrop, hop]; exact hla) (by rw [hrax, hax]; exact hn)] at hr2
        cases hr1; cases hr2; rfl
      · -- `NilCheck`: its pointer
        obtain ⟨rest1, h1⟩ := evalOp_nilCheck_ok hnil hr1
        obtain ⟨rest2, h2⟩ := evalOp_nilCheck_ok (by rw [hrop, hop]; exact hnil) hr2
        subst h1; subst h2
        have hmap : gx.args = fb.args.map (Opt.CSE.rep rw) := by
          rcases hrelx with h | ⟨hc, -⟩
          · exact h
          · rw [hnil] at hc; exact absurd hc (by rw [hnc]; decide)
        obtain ⟨a0, ha0⟩ : ∃ a0, fb.args[0]? = some a0 := by
          cases h : fb.args[0]? with
          | some a0 => exact ⟨a0, rfl⟩
          | none =>
            unfold argVals at hvS
            rcases hfa : fb.args with ⟨l⟩
            rw [hfa] at h hvS
            cases l with
            | nil => simp at hvS
            | cons _ _ => simp at h
        have hg0 : gr.args[0]? = some (Opt.CSE.rep rw a0) := by
          rw [← h0, hmap]; simp [ha0]
        obtain ⟨y, hy, hy'⟩ := hargIH (Array.mem_of_getElem? ha0)
          (hgA _ (Array.mem_of_getElem? hg0))
        have e1 := argVals_head hvS ha0
        have e2 := argVals_head hvT hg0
        rw [hy] at e1; rw [hy'] at e2
        cases e1; cases e2; rfl
      · -- `Load` through disjoint stores
        rw [evalOp_load hld] at hr1
        rw [evalOp_load (by rw [hrop, hop]; exact hld)] at hr2
        cases hr1; cases hr2
        rw [hrai, hai, hrax, hax]
        have hsz := C.load2 b fb hfb hld (.inr (.inl hbpre))
        have hszr := C.load2 c fr hfr (by rw [hop]; exact hld) (hr.elim .inl fun h => .inr (.inr h))
        obtain ⟨p, m, yp, ym, hfa, rfl, hyp, hym⟩ := argVals_two hvS hsz
        have hgsz : gr.args.size = 2 := by
          rcases hrelr with h | ⟨-, -, h⟩ <;> rw [h] <;> simp [hszr]
        obtain ⟨p', m'', yp', ym', hga, rfl, hyp', hym'⟩ := argVals_two hvT hgsz
        unfold Opt.CSE.loadOK at hok
        rw [hfa] at hok
        obtain ⟨q, m', hfra⟩ : ∃ q m', fr.args = #[q, m'] := by
          rcases hfr' : fr.args with ⟨l⟩
          rw [hfr'] at hszr
          match l, hszr with
          | [q, m'], _ => exact ⟨q, m', rfl⟩
        rw [hfra] at hok hrelr
        simp only [List.getElem?_toArray, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hok
        obtain ⟨⟨⟨⟨hrp, hend⟩, hmn⟩, hm'n⟩, hsimple⟩ := hok
        have hgra : gr.args = #[Opt.CSE.rep rw q, m'] := by
          rcases hrelr with h | ⟨hc, -⟩
          · rw [h]; simp [rep_none hm'n]
          · rw [hop, hld] at hc; exact absurd hc (by rw [hlc]; decide)
        rw [hgra] at hga
        have hga' := congrArg Array.toList hga
        simp only [List.cons.injEq, and_true] at hga'
        obtain ⟨rfl, rfl⟩ := hga'
        -- the address
        have hpx : Opt.CSE.rep rw p ∈ gr.args := by
          rw [hgra, ← hrp]; simp
        obtain ⟨y0, hy0, hy0'⟩ := hargIH (by rw [hfa]; simp) (hgA _ hpx)
        rw [hyp] at hy0; cases hy0
        rw [hrp, hyp'] at hy0'; cases hy0'
        -- the representative's memory argument is evaluated by the source, alike
        have hm'A : (B m' ∨ m' ∈ pre) ∧ T.regs[m']? = S.regs[m']? := by
          have hm'g : B m' ∨ m' ∈ pre' := hgA m' (by rw [hgra]; simp)
          rcases hr with hcB | hcp
          · have : B m' := C.bCl c fr hcB hfr hphr m' (by rw [hfra]; simp)
            exact ⟨.inl this, C.bT _ this⟩
          · rcases hm'g with hB | hp
            · exact ⟨.inl hB, C.bT _ hB⟩
            · obtain ⟨gm, ym0, hgm, hgmph, hgmb, -⟩ := C.tPre m' hp
              obtain ⟨gc, yc0, hgc, -, hgcb, -⟩ := C.tPre c hcp
              rw [hgr] at hgc; cases hgc
              obtain ⟨mv, hmv⟩ : ∃ mv, f.value? m' = some mv := by
                cases h : f.value? m' with
                | some mv => exact ⟨mv, rfl⟩
                | none => rw [h] at hsimple; cases hsimple
              obtain ⟨gm', hgm', -, hmop, -, -, -, hmbl, -⟩ := C.gval hmv
              rw [hgm] at hgm'; cases hgm'
              rw [hmv] at hsimple
              simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hsimple
              have hroot : Opt.CSE.rootNode f m' = true := by
                rcases hsimple with (h | h) | h
                · exact absurd (by rw [← hmbl, hgmb, ← hgcb, hrbl]) h
                · exact absurd (by rw [hmop]; exact h) hgmph
                · simp [Opt.CSE.rootNode, hmv, h]
              have hmp := C.roots m' hp hroot
              exact ⟨.inr hmp, C.ts m' hmp hp⟩
        -- the source loads alike through both memory chains
        obtain ⟨hAf, hAc⟩ := C.memA_facts
        have hpA : B p ∨ p ∈ pre := hAc b fb (.inr hbpre) hfb hph p (by rw [hfa]; simp)
        have hmA : B m ∨ m ∈ pre := hAc b fb (.inr hbpre) hfb hph m (by rw [hfa]; simp)
        obtain ⟨hEA, hE⟩ := load_memEnd (env := env) (fr := S) hAf hAc (t := fb.type) hpA hmA
        obtain ⟨-, hE'⟩ := load_memEnd (env := env) (fr := S) hAf hAc (t := fb.type) hpA hm'A.1
        obtain ⟨-, yE, -, hyE, -⟩ := hAf _ hEA
        have hym'S : S.regs[m']? = some (some ym') := by rw [← hm'A.2, hym']
        rw [hE fb.auxInt fb.aux yp ym yE hyp hym hyE,
          hE' fb.auxInt fb.aux yp ym' yE hyp hym'S (hend ▸ hyE)]

/-- **Representatives hold their values**: a source-evaluated value (or one from before the
block) whose representative the target has evaluated (or is from before the block). -/
theorem rep_corr {b : ID} (hb : B b ∨ b ∈ pre)
    (hr : B (Opt.CSE.rep rw b) ∨ Opt.CSE.rep rw b ∈ pre') :
    T.regs[Opt.CSE.rep rw b]? = S.regs[b]? := by
  rcases hb with hB | hp
  · exact (C.bT _ (C.bRep b hB).1).trans (C.bRep b hB).2
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hp
    exact C.step_corr j b hj hr

end Corr

end GoFV.Proof.CSE
