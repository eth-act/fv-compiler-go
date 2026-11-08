import GoFV.Proof.Pass.CSELRel
import GoFV.Proof.Pass.CSEClass
import GoFV.Proof.RetypeL

variable [GoFV.SSA.Sem.Addrs]

/-!
# lowered cse: a representative holds its value

`GoFV.Proof.CSE.Corr`/`rep_corr` for `runL` (`evalValueL` in mode `md`, memory ops not
faulting): within one block's evaluation, every source-evaluated value whose representative the
target has evaluated holds the same register (`CorrL.rep_corr`). A substituted value and its
representative have the same op, aux, auxint, type and arguments in the target (`CRelL.subst`),
so they evaluate alike (`evalOpL_ok_id`); an unreplaced value's target arguments are the
representatives of the source's, the first two possibly swapped (`evalValueL_rel`,
`evalOpL_swap`).
-/

namespace GoFV.Proof.CSEL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.CSE

/-! ## Evaluating related values -/

/-- A lowered value evaluates as its op on its argument registers. -/
theorem evalValueL_of_argVals {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {vs : List Val} (h : argVals fr v.args = some vs) :
    evalValueL md env ctx fr v =
      (evalOpL md.faulting env ctx fr v vs (ctx.tys[v.id]?.getD .other)).bind
        fun r => .ok (md.retype (ctx.tys[v.id]?.getD .other) r) := by
  unfold evalValueL
  rw [mapM_res_ofOption h]
  rfl

/-- A lowered value that does not get stuck has all its argument registers. -/
theorem argValsL_of_eval {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (h : ∀ msg, evalValueL md env ctx fr v ≠ .stuck msg) : ∃ vs, argVals fr v.args = some vs :=
  argVals_some (evalValueL_args_def h)

/-- A commutative op reads nothing of the function (`sxOf`). -/
theorem evalOpL_congr_comm {fl : Bool} {env : Env} {ctx ctx' : Ctx} {fr : Frame} {v v' : Value}
    {argv : List Val} {ty : Ty} (hc : v.op.commutative = true) (hop : v'.op = v.op)
    (haux : v'.aux = v.aux) (hai : v'.auxInt = v.auxInt) (hid : v'.id = v.id)
    (htabs : ctx'.tabs = ctx.tabs) (hpar : ctx'.params = ctx.params) (hact : ctx'.act = ctx.act) :
    evalOpL fl env ctx' fr v' argv ty = evalOpL fl env ctx fr v argv ty := by
  cases hg : v.op.generic
  · obtain ⟨hr, ha⟩ := comm_plain hc
    rw [evalOpL_tail hg ha, evalOpL_tail (hop ▸ hg) (hop ▸ ha), hop, hr, haux, hai]
    rfl
  · rw [evalOpL_generic _ _ _ _ _ _ hg, evalOpL_generic _ _ _ _ _ _ (hop ▸ hg)]
    exact evalOp_congr hop haux hai hid htabs hpar hact

/-- A target value whose argument registers are its source's (the first two possibly swapped
for a commutative op) evaluates alike. -/
theorem evalValueL_rel {md : LMode} {env : Env} {ctxF ctxG : Ctx} {S T : Frame} {fv gv : Value}
    (hop : gv.op = fv.op) (hax : gv.aux = fv.aux) (hai : gv.auxInt = fv.auxInt)
    (hid : gv.id = fv.id) (hty : ctxG.tys[gv.id]? = ctxF.tys[fv.id]?)
    (htabs : ctxG.tabs = ctxF.tabs) (hpar : ctxG.params = ctxF.params) (hact : ctxG.act = ctxF.act)
    (hsx : fv.op.commutative = true ∨ sxOf ctxG.f gv = sxOf ctxF.f fv)
    (hfr : T = { S with regs := T.regs }) {vs : List Val} (hS : argVals S fv.args = some vs)
    (hT : argVals T gv.args = some vs ∨ (fv.op.commutative = true ∧
      ∃ a b rest, vs = a :: b :: rest ∧ argVals T gv.args = some (b :: a :: rest))) :
    evalValueL md env ctxG T gv = evalValueL md env ctxF S fv := by
  have hc : ∀ argv ty, evalOpL md.faulting env ctxG T gv argv ty =
      evalOpL md.faulting env ctxF S fv argv ty := fun argv ty => by
    rw [hfr, evalOpL_frame]
    rcases hsx with hcm | hsx
    · exact evalOpL_congr_comm hcm hop hax hai hid htabs hpar hact
    · exact evalOpL_congr hop hax hai hid htabs hpar hact hsx
  rcases hT with hT | ⟨hcomm, a, b, rest, rfl, hT⟩
  · rw [evalValueL_of_argVals hT, evalValueL_of_argVals hS, hty, hc]
  · rw [evalValueL_of_argVals hT, evalValueL_of_argVals hS, hty, hc, evalOpL_swap hcomm]

/-! ## The shapes of related values -/

theorem tysL_shape {tabs : Tables} {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    (Ctx.makeL tabs f).tys[x]? = some (Opt.CSEL.shape tabs f.lowered v.type) := by
  rw [tysL_of_value h]; rfl

theorem tysL_rel {tabs : Tables} {f g : Func} (hlow : g.lowered = f.lowered) {x y : ID}
    {fv gv : Value} (hfv : f.value? x = some fv) (hgv : g.value? y = some gv)
    (hty : Opt.CSEL.shape tabs f.lowered gv.type = Opt.CSEL.shape tabs f.lowered fv.type) :
    (Ctx.makeL tabs g).tys[y]? = (Ctx.makeL tabs f).tys[x]? := by
  rw [tysL_shape hfv, tysL_shape hgv, hlow, hty]

/-! ## The correspondence -/

/-- What `rep_corr` reads: one block `bid`'s evaluation in source and target (`Corr` for
`runL`). -/
structure CorrL (md : LMode) (env : Env) (tabs : Tables) (f g : Func) (rw : Array (Option ID))
    (bid : ID) (B : ID → Prop) (S T : Frame) (pre pre' : List ID) : Prop where
  rel : CRelL tabs f g rw
  fl : md.faulting = false
  frame : T = { S with regs := T.regs }
  bS : ∀ x, B x → ∃ v y, f.value? x = some v ∧ S.regs[x]? = some (some y) ∧
    (v.op ≠ .Phi → evalValueL md env (Ctx.makeL tabs f) S v = .ok y)
  bT : ∀ x, B x → T.regs[x]? = S.regs[x]?
  bRep : ∀ x, B x → B (Opt.CSE.rep rw x) ∧ S.regs[Opt.CSE.rep rw x]? = S.regs[x]?
  bCl : ∀ x v, B x → f.value? x = some v → v.op ≠ .Phi → ∀ a ∈ v.args, B a
  bOut : ∀ x v, B x → f.value? x = some v → v.block ≠ bid ∨ v.op = .Phi
  sPre : ∀ x ∈ pre, ∃ v y, f.value? x = some v ∧ v.op ≠ .Phi ∧ v.block = bid ∧
    S.regs[x]? = some (some y) ∧ evalValueL md env (Ctx.makeL tabs f) S v = .ok y
  sOrd : ∀ (j : Nat) x, pre[j]? = some x → ∀ v, f.value? x = some v → ∀ a ∈ v.args,
    B a ∨ ∃ i < j, pre[i]? = some a
  tPre : ∀ x ∈ pre', ∃ v y, g.value? x = some v ∧ v.op ≠ .Phi ∧ v.block = bid ∧
    T.regs[x]? = some (some y) ∧ evalValueL md env (Ctx.makeL tabs g) T v = .ok y
  tArgs : ∀ x ∈ pre', ∀ v, g.value? x = some v → ∀ a ∈ v.args, B a ∨ a ∈ pre'
  ts : ∀ x ∈ pre, x ∈ pre' → T.regs[x]? = S.regs[x]?
  roots : ∀ x ∈ pre', Opt.CSE.rootNode f x = true → x ∈ pre
  ids : ∀ x v, f.value? x = some v → (B x ∨ x ∈ pre ∨ x ∈ pre') → v.id = x

variable {md : LMode} {env : Env} {tabs : Tables} {f g : Func} {rw : Array (Option ID)} {bid : ID}
  {B : ID → Prop} {S T : Frame} {pre pre' : List ID}

namespace CorrL

variable (C : CorrL md env tabs f g rw bid B S T pre pre')
include C

theorem notB_of_pre {x : ID} (hx : x ∈ pre) : ¬ B x := fun hB => by
  obtain ⟨v, y, hv, hph, hb, -⟩ := C.sPre x hx
  rcases C.bOut x v hB hv with h | h
  · exact h hb
  · exact hph h

theorem gval {x : ID} {fv : Value} (hfv : f.value? x = some fv) :
    ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧ gv.op = fv.op ∧ gv.aux = fv.aux ∧
      gv.auxInt = fv.auxInt ∧ gv.type = fv.type ∧ gv.block = fv.block ∧
      ArgsRel rw fv.op fv.args gv.args :=
  C.rel.value x fv hfv

theorem ctx_tabs : (Ctx.makeL tabs g).tabs = (Ctx.makeL tabs f).tabs := by
  rw [tabs_makeL, tabs_makeL]
theorem ctx_act : (Ctx.makeL tabs g).act = (Ctx.makeL tabs f).act := by
  rw [act_makeL, act_makeL]; rfl
theorem ctx_params : (Ctx.makeL tabs g).params = (Ctx.makeL tabs f).params := by
  rw [params_makeL, params_makeL]
  simp only [Ctx.make, abiParams, C.rel.ownAux]

/-- A target value whose arguments' registers in `T` are its source arguments' in `S`
evaluates as its source. -/
theorem eval_rel {x : ID} {fv gv : Value} (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (hxid : fv.id = x) (hargs : ∀ a ∈ fv.args, ∃ y, S.regs[a]? = some (some y) ∧
      T.regs[Opt.CSE.rep rw a]? = some (some y)) :
    evalValueL md env (Ctx.makeL tabs g) T gv = evalValueL md env (Ctx.makeL tabs f) S fv := by
  obtain ⟨gv', hgv', hid, hop, hax, hai, hty, -, hrel⟩ := C.gval hfv
  rw [hgv] at hgv'; cases hgv'
  obtain ⟨vs, hS, hT⟩ := argVals_rel hrel hargs
  refine evalValueL_rel hop hax hai hid ?_ C.ctx_tabs C.ctx_params C.ctx_act ?_ C.frame hS hT
  · rw [hid, hxid]; exact tysL_rel C.rel.lowered hfv hgv (by rw [hty])
  · rw [makeL_f, makeL_f]; exact C.rel.sx x fv gv hfv hgv

theorem baseEval {x : ID} (hB : B x) {fv : Value} (hfv : f.value? x = some fv)
    (hph : fv.op ≠ .Phi) :
    ∃ gv y, g.value? x = some gv ∧ T.regs[x]? = some (some y) ∧
      evalValueL md env (Ctx.makeL tabs g) T gv = .ok y ∧
      evalValueL md env (Ctx.makeL tabs f) S fv = .ok y := by
  obtain ⟨v, y, hv, hy, hev⟩ := C.bS x hB
  rw [hfv] at hv; cases hv
  obtain ⟨gv, hgv, -⟩ := C.gval hfv
  refine ⟨gv, y, hgv, by rw [C.bT x hB, hy], ?_, hev hph⟩
  rw [C.eval_rel hfv hgv (C.ids x fv hfv (.inl hB)) fun a ha => ?_, hev hph]
  have haB := C.bCl x fv hB hfv hph a ha
  obtain ⟨-, ya, -, hya, -⟩ := C.bS a haB
  obtain ⟨hrB, hrS⟩ := C.bRep a haB
  exact ⟨ya, hya, by rw [C.bT _ hrB, hrS, hya]⟩

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

theorem tEval {c : ID} (hc : B c ∨ c ∈ pre') {fr gr : Value} (hfr : f.value? c = some fr)
    (hgr : g.value? c = some gr) (hph : fr.op ≠ .Phi) :
    ∃ t, T.regs[c]? = some (some t) ∧ evalValueL md env (Ctx.makeL tabs g) T gr = .ok t := by
  rcases hc with hB | hp
  · obtain ⟨gr', t, hgr', ht, hev, -⟩ := C.baseEval hB hfr hph
    rw [hgr] at hgr'; cases hgr'
    exact ⟨t, ht, hev⟩
  · obtain ⟨gr', t, hgr', -, -, ht, hev⟩ := C.tPre c hp
    rw [hgr] at hgr'; cases hgr'
    exact ⟨t, ht, hev⟩

/-- The source-evaluated values and those from before the block. -/
theorem memA {x : ID} (hx : B x ∨ x ∈ pre) : ∃ v y, f.value? x = some v ∧
    S.regs[x]? = some (some y) ∧
    (v.op ≠ .Phi → evalValueL md env (Ctx.makeL tabs f) S v = .ok y) := by
  rcases hx with hB | hp
  · exact C.bS x hB
  · obtain ⟨v, y, hv, -, -, hy, hev⟩ := C.sPre x hp
    exact ⟨v, y, hv, hy, fun _ => hev⟩

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
  have hargIH := fun {a} (ha : a ∈ fb.args) hra =>
    C.argIH hj hfb (fun i hi a ha hr => ih i hi a ha hr) ha hra
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
    obtain ⟨fx, fr, gx, gr, hfx, hfr, hgx, hgr, hop, hax, hai, hty, hargs, hsub⟩ :=
      C.rel.cong b c hrw
    rw [hfb] at hfx; cases hfx
    have hphr : fr.op ≠ .Phi := by rw [hop]; exact hph
    obtain ⟨t, ht, hevT⟩ := C.tEval hr hfr hgr hphr
    have hgA := C.gArgs hr hfr hgr hphr
    obtain ⟨gx', hgx', hgid, hgop, hgax, hgai, hgty, -, hrelx⟩ := C.gval hfb
    rw [hgx] at hgx'; cases hgx'
    obtain ⟨gr', hgr', hrid, hrop, hrax, hrai, hrty, -, -⟩ := C.gval hfr
    rw [hgr] at hgr'; cases hgr'
    have hcid : fr.id = c := C.ids c fr hfr (hr.elim .inl fun h => .inr (.inr h))
    -- the target evaluates `b`'s version as the source evaluates `b`
    have hevx := C.eval_rel hfb hgx hbid fun a ha =>
      hargIH ha (hgA _ (hargs ▸ C.rep_mem_of_argsRel hrelx ha))
    rw [hev] at hevx
    rw [ht, hs]
    suffices t = s by rw [this]
    obtain ⟨vT, hvT⟩ := argValsL_of_eval (md := md) (env := env) (ctx := Ctx.makeL tabs g)
      (fr := T) (v := gr) fun msg h => by rw [hevT] at h; cases h
    have htyx : (Ctx.makeL tabs g).tys[gx.id]? = (Ctx.makeL tabs g).tys[gr.id]? := by
      rw [hgid, hbid, hrid, hcid]
      rw [tysL_shape hgx, tysL_shape hgr, C.rel.lowered, hgty, hrty, hty]
    rw [evalValueL_of_argVals hvT, C.fl] at hevT
    rw [evalValueL_of_argVals (hargs ▸ hvT), C.fl, htyx] at hevx
    obtain ⟨r2, hr2, rfl⟩ := bind_ok hevT
    obtain ⟨r1, hr1, rfl⟩ := bind_ok hevx
    congr 1
    refine (evalOpL_ok_id (u := gx) (v := gr) (by rw [hrop, hgop, hop]) (by rw [hrax, hgax, hax])
      (by rw [hrai, hgai, hai]) ?_ (by rw [hgop]; exact hsub) ?_ hr2).symm
    · unfold sxOf; rw [hargs]
    · exact hr1

/-- **Representatives hold their values**: a source-evaluated value (or one from before the
block) whose representative the target has evaluated (or is from before the block). -/
theorem rep_corr {b : ID} (hb : B b ∨ b ∈ pre)
    (hr : B (Opt.CSE.rep rw b) ∨ Opt.CSE.rep rw b ∈ pre') :
    T.regs[Opt.CSE.rep rw b]? = S.regs[b]? := by
  rcases hb with hB | hp
  · exact (C.bT _ (C.bRep b hB).1).trans (C.bRep b hB).2
  · obtain ⟨j, hj⟩ := List.getElem?_of_mem hp
    exact C.step_corr j b hj hr

end CorrL

end GoFV.Proof.CSEL
