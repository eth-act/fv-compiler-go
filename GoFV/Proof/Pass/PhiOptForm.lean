import GoFV.Proof.Pass.PhiOptSetup
import GoFV.Proof.Pass.ZCSEEval

/-!
# phiopt: the rewritten `Phi`s evaluate to the `Phi`'s value

`boolArm_eval`: a boolean form (`Copy c`, `Not c`, `OrB c n`, `AndB c n`) evaluated with the
control `c` holding the edge's fact `d` yields the arm the `Phi` takes on that edge (`OrB`/`AndB`
are parallel, `Sem/Cmp.lean`, so the arm not taken may be `poison`; a non-boolean arm is
`poison` at the `bool` shape). `intForm_eval`: phioptint's `extOp w (CvtBoolToUint8 [Not] c)`
yields the integer constant 0/1 of the arm. Constants hold their value (`constBool_reg`,
`constI_reg`, from `ArglessInv`).
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.PhiOpt
open GoFV.Proof.ZCSE (ArglessInv)

/-! ## Evaluating pure ops -/

/-- The ops of the forms and constants: `evalOp` is `evalPure`. -/
def formOp (op : Op) : Prop :=
  op = .Copy ∨ op = .Not ∨ op = .OrB ∨ op = .AndB ∨ op = .CvtBoolToUint8 ∨
  op = .ZeroExt8to16 ∨ op = .ZeroExt8to32 ∨ op = .ZeroExt8to64 ∨ op = .ConstBool ∨
  op = .Const8 ∨ op = .Const16 ∨ op = .Const32 ∨ op = .Const64

theorem evalOp_form {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (h : formOp v.op) : evalOp env ctx fr v argv ty = .ok (evalPure v.op ty v.auxInt v.aux argv) := by
  unfold evalOp frameVal
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl

theorem evalValue_nil {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} (ha : v.args = #[])
    (h : formOp v.op) :
    evalValue env ctx fr v = .ok ((evalPure v.op (ctx.tys[v.id]?.getD .other) v.auxInt v.aux
      []).retype (ctx.tys[v.id]?.getD .other)) := by
  unfold evalValue
  rw [ha]
  simp [bind, Res.bind, pure, evalOp_form h]

theorem evalValue_un {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {a : ID} {x : Val}
    (ha : v.args = #[a]) (hx : fr.regs[a]? = some (some x)) (h : formOp v.op) :
    evalValue env ctx fr v = .ok ((evalPure v.op (ctx.tys[v.id]?.getD .other) v.auxInt v.aux
      [x]).retype (ctx.tys[v.id]?.getD .other)) := by
  unfold evalValue
  rw [ha]
  simp [hx, Res.ofOption, bind, Res.bind, pure, evalOp_form h]

theorem evalValue_bin {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {a b : ID} {x y : Val}
    (ha : v.args = #[a, b]) (hx : fr.regs[a]? = some (some x)) (hy : fr.regs[b]? = some (some y))
    (h : formOp v.op) :
    evalValue env ctx fr v = .ok ((evalPure v.op (ctx.tys[v.id]?.getD .other) v.auxInt v.aux
      [x, y]).retype (ctx.tys[v.id]?.getD .other)) := by
  unfold evalValue
  rw [ha]
  simp [hx, hy, Res.ofOption, bind, Res.bind, pure, evalOp_form h]

/-! ## Values -/

theorem retype_bool_val (b : Bool) : (Val.bool b).retype .bool = .bool b := rfl

theorem orB_false_left (y : Val) :
    (Cmp.orB [.bool false, y]).retype .bool = y.retype .bool := by
  cases y <;> try rfl
  rename_i b; cases b <;> rfl

theorem andB_true_left (y : Val) :
    (Cmp.andB [.bool true, y]).retype .bool = y.retype .bool := by
  cases y <;> try rfl
  rename_i b; cases b <;> rfl

theorem orB_true_left (z : Val) : Cmp.orB [.bool true, z] = .bool true := by
  cases z <;> rfl

theorem evalPure_orB (t : Ty) (k : Int64) (x : Option AuxRef) (args : List Val) :
    evalPure .OrB t k x args = Cmp.orB args := rfl

theorem evalPure_andB (t : Ty) (k : Int64) (x : Option AuxRef) (args : List Val) :
    evalPure .AndB t k x args = Cmp.andB args := rfl

theorem andB_false_left (z : Val) : Cmp.andB [.bool false, z] = .bool false := by
  cases z <;> rfl

theorem evalPure_not (t : Ty) (k : Int64) (x : Option AuxRef) (d : Bool) :
    evalPure .Not t k x [.bool d] = .bool (!d) := by
  cases d <;> rfl

/-- A `ConstBool`'s register holds its constant. -/
theorem constBool_reg {env : Env} {tabs : Tables} {f : Func} {fr : Frame}
    (hinv : ArglessInv env (Ctx.make tabs f) fr) {a : ID} {u : Value} (hu : f.value? a = some u)
    (hop : u.op = .ConstBool) (hty : tabs.ty u.type = .bool) (hid : u.id = a)
    (hargs : u.args = #[]) {y : Val}
    (hy : fr.regs[a]? = some (some y)) : y = .bool (u.auxInt != 0) := by
  have h := hinv a u y hu hargs (by rw [hop]; decide) hy
  rw [evalValue_nil hargs (by unfold formOp; simp [hop])] at h
  cases h
  rw [hop, hid, tys_of_value hu, hty]
  rfl

/-- The integer constant op of a width evaluates to its auxint's low bits. -/
theorem evalPure_constOp (w : Sem.Width) (ty : Ty) (k : Int64) (x : Option AuxRef) :
    evalPure (constOp w) ty k x [] = .int w (BitVec.ofInt w.bits k.toInt) := by
  cases w <;> rfl

theorem formOp_constOp (w : Sem.Width) : formOp (constOp w) := by
  unfold formOp; cases w <;> simp [constOp]

/-- An integer constant's register holds its constant. -/
theorem constI_reg {env : Env} {tabs : Tables} {f : Func} {fr : Frame}
    (hinv : ArglessInv env (Ctx.make tabs f) fr) {a : ID} {u : Value} (hu : f.value? a = some u)
    {w : Sem.Width} (hop : u.op = constOp w) (hty : tabs.ty u.type = .int w)
    (hid : u.id = a) (hargs : u.args = #[]) {y : Val}
    (hy : fr.regs[a]? = some (some y)) : y = .int w (BitVec.ofInt w.bits u.auxInt.toInt) := by
  have h := hinv a u y hu hargs (by rw [hop]; cases w <;> decide) hy
  rw [evalValue_nil hargs (by rw [hop]; exact formOp_constOp w)] at h
  cases h
  rw [hop, evalPure_constOp, hid, tys_of_value hu, hty]
  simp [Val.retype, BitVec.setWidth_eq]

/-- An arm `armB` accepts holds the claimed boolean. -/
theorem armB_val {tabs : Tables} {f : Func} {fr : Frame} {c a : ID} {dc d : Bool}
    (hc : fr.regs[c]? = some (some (.bool dc)))
    {y : Val} (hy : fr.regs[a]? = some (some y)) (hconst : ∀ d', constB tabs f a d' = true → y = .bool d')
    (h : armB tabs f c a dc d = true) : y = .bool d := by
  unfold armB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨rfl, rfl⟩ | h
  · rw [hc] at hy; cases hy; rfl
  · exact hconst d h

/-- **A boolean form yields the arm of the edge.** -/
theorem boolArm_eval {env : Env} {tabs : Tables} {f g : Func} {b c a : ID} {gv : Value}
    {d : Bool} (harm : BoolArm tabs f b c gv a d) {fr : Frame}
    (hc : fr.regs[c]? = some (some (.bool d)))
    (havail : ∀ x, avail f b x = true → ∃ y, fr.regs[x]? = some (some y))
    {y : Val} (hy : fr.regs[a]? = some (some y)) (hconst : ∀ d', constB tabs f a d' = true → y = .bool d')
    {g' : Frame}
    (hg' : ∀ x ∈ gv.args, g'.regs[x]? = fr.regs[x]?)
    (hty : (Ctx.make tabs g).tys[gv.id]?.getD .other = .bool) :
    evalValue env (Ctx.make tabs g) g' gv = .ok (y.retype .bool) := by
  rcases harm with ⟨hop, ha, harm⟩ | ⟨hop, ha, harm⟩ | ⟨n, hop, ha, hn, harm⟩ |
    ⟨n, hop, ha, hn, harm⟩
  · have hc' : g'.regs[c]? = some (some (.bool d)) := by rw [hg' c (by simp [ha]), hc]
    rw [evalValue_un ha hc' (by unfold formOp; simp [hop]), hty, hop, armB_val hc hy hconst harm]
    rfl
  · have hc' : g'.regs[c]? = some (some (.bool d)) := by rw [hg' c (by simp [ha]), hc]
    rw [evalValue_un ha hc' (by unfold formOp; simp [hop]), hty, hop, armB_val hc hy hconst harm]
    cases d <;> rfl
  · have hc' : g'.regs[c]? = some (some (.bool d)) := by rw [hg' c (by simp [ha]), hc]
    obtain ⟨z, hz⟩ := havail n hn
    have hn' : g'.regs[n]? = some (some z) := by rw [hg' n (by simp [ha]), hz]
    rw [evalValue_bin ha hc' hn' (by unfold formOp; simp [hop]), hty, hop]
    cases d with
    | true =>
      simp only [↓reduceIte] at harm
      rw [armB_val hc hy hconst harm]
      rw [evalPure_orB, orB_true_left]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at harm
      subst harm
      rw [hz] at hy; cases hy
      exact congrArg _ (orB_false_left _)
  · have hc' : g'.regs[c]? = some (some (.bool d)) := by rw [hg' c (by simp [ha]), hc]
    obtain ⟨z, hz⟩ := havail n hn
    have hn' : g'.regs[n]? = some (some z) := by rw [hg' n (by simp [ha]), hz]
    rw [evalValue_bin ha hc' hn' (by unfold formOp; simp [hop]), hty, hop]
    cases d with
    | true =>
      simp only [↓reduceIte] at harm
      subst harm
      rw [hz] at hy; cases hy
      exact congrArg _ (andB_true_left _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at harm
      rw [armB_val hc hy hconst harm]
      rw [evalPure_andB, andB_false_left]

/-! ## phioptint -/

/-- `extOp w` of the byte 0/1 is the integer 0/1 of width `w`. -/
theorem evalPure_extOp (w : Sem.Width) (ty : Ty) (k : Int64) (x : Option AuxRef) (b : Bool) :
    evalPure (extOp w) ty k x [.i8 (if b then 1 else 0)] =
      .int w (BitVec.ofInt w.bits (if b then (1 : Int64) else 0).toInt) := by
  cases w <;> cases b <;> rfl

theorem formOp_extOp (w : Sem.Width) : formOp (extOp w) := by
  unfold formOp; cases w <;> simp [extOp]

/-- **phioptint's form yields the arm of the edge.** `H`: the target's frame in which the new
values hold their evaluation; `c` holds `d` there. -/
theorem intForm_eval {env : Env} {tabs : Tables} {f g : Func} {b c : ID} {fv gv : Value}
    {w : Sem.Width} {neg d : Bool} (hshape : IntShape tabs f g b fv gv w c neg) {H : Frame}
    (hc : H.regs[c]? = some (some (.bool d)))
    (hnew : ∀ x, isNew f g b x = true → ∀ v, g.value? x = some v →
      ∃ z, H.regs[x]? = some (some z) ∧ evalValue env (Ctx.make tabs g) H v = .ok z)
    (hids : ∀ x v, g.value? x = some v → isNew f g b x = true → v.id = x)
    {g' : Frame} (hg' : ∀ x ∈ gv.args, g'.regs[x]? = H.regs[x]?)
    (hty : (Ctx.make tabs g).tys[gv.id]?.getD .other = .int w) :
    evalValue env (Ctx.make tabs g) g' gv =
      .ok (.int w (BitVec.ofInt w.bits (if d != neg then (1 : Int64) else 0).toInt)) := by
  obtain ⟨-, hop, -, cv, cvv, x, hargs, hcvn, hcvv, hcop, hcty, hxargs, hx⟩ := hshape
  -- the byte argument of the conversion
  have hxval : H.regs[x]? = some (some (.bool (d != neg))) := by
    rcases hx with ⟨rfl, rfl⟩ | ⟨hxn, nv, hnv, hnop, hnargs, hnty, rfl⟩
    · simpa using hc
    · obtain ⟨z, hz, hev⟩ := hnew x hxn nv hnv
      rw [evalValue_un hnargs hc (by unfold formOp; simp [hnop]), hnop] at hev
      cases hev
      rw [hz, evalPure_not, hids x nv hnv hxn, tys_of_value hnv, hnty]
      cases d <;> rfl
  obtain ⟨z, hz, hev⟩ := hnew cv hcvn cvv hcvv
  rw [evalValue_un hxargs hxval (by unfold formOp; simp [hcop]), hcop] at hev
  rw [hids cv cvv hcvv hcvn, tys_of_value hcvv, hcty] at hev
  have hz' : z = .i8 (if d != neg then 1 else 0) := by
    cases hev; cases (d != neg) <;> rfl
  subst hz'
  have hcv' : g'.regs[cv]? = some (some (.i8 (if d != neg then 1 else 0))) := by
    rw [hg' cv (by simp [hargs]), hz]
  rw [evalValue_un hargs hcv' (by rw [hop]; exact formOp_extOp w), hty, hop, evalPure_extOp]
  simp [Val.retype, BitVec.setWidth_eq]

end GoFV.Proof.PhiOpt
