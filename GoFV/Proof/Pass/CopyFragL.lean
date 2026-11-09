import GoFV.Proof.Pass.CopyElimSim
import GoFV.Proof.RetypeL
import GoFV.Proof.EvalL
import GoFV.SSA.Sem.TyEq
import GoFV.Proof.EvalOpLDispatch

variable [GoFV.SSA.Sem.Addrs]

/-!
# copyelim on lowered code: the fragment `CopyLFrag`

On `runL` copyelim's simulation needs three facts Phase 1's `CopyRel` does not give, the
fragment `CopyLFrag tabs f g` of the input `f` and output `g` (on the blocks of `f`'s dominator
tree), decided by `copyLFragB` (`copyLFrag_of`):

* `auxInt`: the block keeps its `auxInt` (the bit an arm64 `TBZ`/`TBNZ` tests, `stepTermL`;
  `CopyRel` compares the control-flow graph, which has no `auxInt`).
* `sx`: a `MOVDreg`/`MOVDnop` reads whether its first argument sign-extends (`sxOf`,
  `arm64Op`); copyelim may replace that argument by the copy's source, so the answer must not
  change. Every other op reads nothing of the function (`evalOpL_f`), so only these are checked.
* `shape`: in a lowered function a copy of `g` and its argument have the same lowered shape
  (`Ctx.makeL`'s `tys`). A copy of shape `t` yields its argument at `t` (`Val.retypeL`); with
  equal shapes the argument's register is unchanged (`LMode.retype_idem`). On generic code
  Phase 1's `CopyRel.copyShape` (`RetypeInto`) is used.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-! ## Only `MOVDreg`/`MOVDnop` read the function -/

/-- An arm64 op other than `MOVDreg`/`MOVDnop` does not read `ctx.f`. -/
theorem arm64Op_f {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (F : Func) (hm : v.op ≠ .ARM64MOVDreg)
    (hn : v.op ≠ .ARM64MOVDnop) :
    arm64Op faulting env { ctx with f := F } fr v argv ty = arm64Op faulting env ctx fr v argv ty := by
  unfold arm64Op
  rw [show nilFaults faulting { ctx with f := F } v argv = nilFaults faulting ctx v argv from rfl]
  cases nilFaults faulting ctx v argv with
  | some m => rfl
  | none =>
    dsimp only
    split
    all_goals first | rfl | (exfalso; simp_all; done)

/-- `evalOpL` of an op other than `MOVDreg`/`MOVDnop` does not read `ctx.f`. -/
theorem evalOpL_f {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (F : Func) (hm : v.op ≠ .ARM64MOVDreg)
    (hn : v.op ≠ .ARM64MOVDnop) :
    evalOpL faulting env { ctx with f := F } fr v argv ty = evalOpL faulting env ctx fr v argv ty := by
  rw [evalOpL_eq, evalOpL_eq]
  split
  · exact evalOp_congr rfl rfl rfl rfl rfl rfl rfl
  · split
    · exact arm64Op_f F hm hn
    · rfl

theorem sxOf_default (v : Value) : sxOf default v = none := by
  unfold sxOf
  cases v.args[0]? with
  | none => rfl
  | some a =>
    simp only [Option.bind_some, Func.value?]
    rfl

/-- `evalOpL_congr` where only `MOVDreg`/`MOVDnop` need the sign extension of the first
argument. -/
theorem evalOpL_congr_sx {faulting : Bool} {env : Env} {ctx ctx' : Ctx} {fr : Frame}
    {v v' : Value} {argv : List Val} {ty : Ty} (hop : v'.op = v.op) (haux : v'.aux = v.aux)
    (hai : v'.auxInt = v.auxInt) (hid : v'.id = v.id) (htabs : ctx'.tabs = ctx.tabs)
    (hpar : ctx'.params = ctx.params) (hact : ctx'.act = ctx.act)
    (hsx : (v.op = .ARM64MOVDreg ∨ v.op = .ARM64MOVDnop) → sxOf ctx'.f v' = sxOf ctx.f v) :
    evalOpL faulting env ctx' fr v' argv ty = evalOpL faulting env ctx fr v argv ty := by
  by_cases hm : v.op = .ARM64MOVDreg ∨ v.op = .ARM64MOVDnop
  · exact evalOpL_congr hop haux hai hid htabs hpar hact (hsx hm)
  · have h1 : v.op ≠ .ARM64MOVDreg := fun h => hm (.inl h)
    have h2 : v.op ≠ .ARM64MOVDnop := fun h => hm (.inr h)
    rw [← evalOpL_f (ctx := ctx') default (by rw [hop]; exact h1) (by rw [hop]; exact h2),
      ← evalOpL_f (ctx := ctx) default h1 h2]
    exact evalOpL_congr hop haux hai hid htabs hpar hact (by
      rw [sxOf_default, sxOf_default])

/-- `evalValueL_eq_of_args` where only `MOVDreg`/`MOVDnop` need the sign extension of the first
argument. -/
theorem evalValueL_eq_of_args_sx {md : LMode} {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame}
    {v v' : Value} (hop : v'.op = v.op) (haux : v'.aux = v.aux) (hai : v'.auxInt = v.auxInt)
    (hid : v'.id = v.id) (hsz : v'.args.size = v.args.size)
    (hargs : ∀ (k : Nat) (a : ID), v.args[k]? = some a →
      ∃ a' y, v'.args[k]? = some a' ∧ fr.regs[a]? = some (some y) ∧ fr'.regs[a']? = some (some y))
    (hfr : fr' = { fr with regs := fr'.regs }) (hty : ctx'.tys[v.id]? = ctx.tys[v.id]?)
    (htabs : ctx'.tabs = ctx.tabs) (hpar : ctx'.params = ctx.params) (hact : ctx'.act = ctx.act)
    (hsx : (v.op = .ARM64MOVDreg ∨ v.op = .ARM64MOVDnop) → sxOf ctx'.f v' = sxOf ctx.f v) :
    evalValueL md env ctx' fr' v' = evalValueL md env ctx fr v := by
  unfold evalValueL
  rw [mapM_ofOption_eq (l := v'.args.toList) (l' := v.args.toList)
    (m := fun a => s!"v{v'.id}: argument v{a} has no value")
    (m' := fun a => s!"v{v.id}: argument v{a} has no value")
    (r := fun a => (fr'.regs[a]?).join) (r' := fun a => (fr.regs[a]?).join) (by simp [hsz])
    (fun k a' ha' => by
      have hk : k < v.args.size := by
        have := (List.getElem?_eq_some_iff.1 ha').1; simp at this; omega
      obtain ⟨a'', y, h1, h2, h3⟩ := hargs k v.args[k] (by simp [hk])
      rw [Array.getElem?_toList] at ha'
      rw [ha'] at h1; cases h1
      exact ⟨v.args[k], y, by simp [hk], by simp [h3], by simp [h2]⟩)]
  rw [hid, hty, hfr]
  simp only [evalOpL_frame, evalOpL_congr_sx hop haux hai hid htabs hpar hact hsx]

end GoFV.Proof

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt

/-! ## The fragment -/

/-- What copyelim's simulation on `runL` needs beyond `CopyRel`, on the tree blocks of `f`. -/
structure CopyLFrag (tabs : Tables) (f g : Func) : Prop where
  /-- Tree blocks keep their `auxInt`. -/
  auxInt : ∀ bid, Tree f bid → ∀ fb gb, f.block? bid = some fb → g.block? bid = some gb →
    gb.auxInt = fb.auxInt
  /-- A `MOVDreg`/`MOVDnop` of a tree block sees the same sign extension of its first argument. -/
  sx : ∀ bid, Tree f bid → ∀ fb, f.block? bid = some fb → ∀ x ∈ fb.values, ∀ fv gv,
    f.value? x = some fv → g.value? x = some gv →
    (gv.op = .ARM64MOVDreg ∨ gv.op = .ARM64MOVDnop) → sxOf g gv = sxOf f fv
  /-- In lowered code a copy of a tree block has its argument's lowered shape. -/
  shape : g.lowered = true → ∀ bid, Tree f bid → ∀ fb, f.block? bid = some fb →
    ∀ x ∈ fb.values, ∀ gv w, g.value? x = some gv → gv.op = .Copy → gv.args = #[w] →
      (Ctx.makeL tabs g).tys[w]?.getD .other = (Ctx.makeL tabs g).tys[x]?.getD .other

/-- Decides `CopyLFrag.sx` for value `x`. -/
def sxOKB (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some fv, some gv =>
    !(gv.op == .ARM64MOVDreg || gv.op == .ARM64MOVDnop) || decide (sxOf g gv = sxOf f fv)
  | _, _ => true

/-- Decides `CopyLFrag.shape` for value `x` (`low`: `g.lowered`; `tys`: the shapes of
`Ctx.makeL tabs g`, computed once per function by `copyLFragB`). -/
def shapeOKB (low : Bool) (tys : Array Ty) (g : Func) (x : ID) : Bool :=
  !low ||
    match g.value? x with
    | some gv =>
      !(gv.op == .Copy) ||
        match gv.args.toList with
        | [w] => Ty.beq (tys[w]?.getD .other) (tys[x]?.getD .other)
        | _ => true
    | none => true

/-- Decides `CopyLFrag`. -/
def copyLFragB (tabs : Tables) (f g : Func) : Bool :=
  let C := make f
  let low := g.lowered
  let tys := (Ctx.makeL tabs g).tys
  f.blocks.all fun bid =>
    !C.inTree bid ||
    match f.block? bid with
    | none => true
    | some fb =>
      (match g.block? bid with
       | some gb => decide (gb.auxInt = fb.auxInt)
       | none => true) &&
      fb.values.all fun x => sxOKB f g x && shapeOKB low tys g x

theorem copyLFrag_of {tabs : Tables} {f g : Func} (h : copyLFragB tabs f g = true) :
    CopyLFrag tabs f g := by
  unfold copyLFragB at h
  dsimp only at h
  rw [Array.all_eq_true'] at h
  have hb : ∀ bid, Tree f bid → ∀ fb, f.block? bid = some fb →
      (match g.block? bid with
       | some gb => decide (gb.auxInt = fb.auxInt)
       | none => true) = true ∧
      ∀ x ∈ fb.values, sxOKB f g x = true ∧ shapeOKB g.lowered (Ctx.makeL tabs g).tys g x = true := by
    intro bid hbt fb hfb
    have h := h bid hbt.1
    simp only [DomCert.Cert.inTree, hbt.2, Bool.not_true, Bool.false_or, hfb, Bool.and_eq_true,
      Array.all_eq_true'] at h
    exact ⟨h.1, h.2⟩
  refine ⟨fun bid hbt fb gb hfb hgb => ?_, fun bid hbt fb hfb x hx fv gv hfv hgv hm => ?_,
    fun hl bid hbt fb hfb x hx gv w hgv hop hargs => ?_⟩
  · have := (hb bid hbt fb hfb).1
    rw [hgb] at this
    exact of_decide_eq_true this
  · have := ((hb bid hbt fb hfb).2 x hx).1
    unfold sxOKB at this
    rw [hfv, hgv] at this
    simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at this
    rcases this with h1 | h1
    · simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h1
      rcases hm with hm | hm
      · exact absurd hm h1.1
      · exact absurd hm h1.2
    · exact h1
  · have := ((hb bid hbt fb hfb).2 x hx).2
    unfold shapeOKB at this
    rw [hl, hgv] at this
    simp only [Bool.not_true, Bool.false_or, hop, beq_self_eq_true, hargs] at this
    exact Ty.eq_of_beq this

end GoFV.Proof.CopyElim
