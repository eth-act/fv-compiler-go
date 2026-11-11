import GoFV.Proof.Pass.LateLowerVal

variable [GoFV.SSA.Sem.Addrs]

/-!
# `late lower`'s removed extensions, value by value (issue #385)

The facts `GoFV.Proof.LateLowerL.lateLower_refinesL` needs of line 29 of `ARM64latelower.rules`,
`(MOVBUreg x:(Equal|…|GreaterEqualF _)) => x`, which `lateB` accepts (`rw29`): `x`, at the `bool`
shape, holds a boolean or `poison` (`BoolV`), so its `MOVBUreg` holds the integer 0 or 1 or
`poison` (`movbu_narrow`; `NarrowR` relates it to `x`). A reader that reads its argument as a
register (`regPos`) reads both alike: the ops of `regOps` (`evalPure_rl`, an `AND` off the
`bool` shape, where it absorbs a `false` operand: `and_rl`; by the register
families `op1`, `op2`, `add`, `sub`, `addSh`, `subSh`, `addK`, whose pointer cases neither value
takes: `RegLike`), the stored value of a store (`st_narrow`: `storeBytes` writes the register's
low bytes), a `Phi` at an integer shape (`retype_narrow`: `Val.widen` zero-extends the boolean).
-/

namespace GoFV.Proof.LateLowerL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.LateLowerCheck

/-! ## The values -/

/-- A value at the `bool` shape (`Val.retypeL .bool`): a boolean or `poison`. -/
def BoolV (y : Val) : Prop := y = .poison ∨ ∃ c, y = .bool c

theorem boolV_retype {md : LMode} (hl : md.low = true) (y : Val) : BoolV (md.retype .bool y) := by
  unfold LMode.retype
  rw [hl, if_pos (rfl : true = true)]
  cases y <;> simp [BoolV, Val.retypeL, Val.widen, Val.retype]

/-- The register of a removed `MOVBUreg` (`s`) and of its condition `x` (`t`): equal, or the
boolean `c` and the integer `c ? 1 : 0`. -/
def NarrowR (s t : Val) : Prop := s = t ∨ ∃ c w, t = .bool c ∧ s = .int w (if c then 1 else 0)

/-- Not a pointer. -/
def NP (a : Val) : Prop := ∀ p, a ≠ .ptr p

/-- Two values an op that reads registers reads alike: equal, or two non-pointers with the same
register. -/
def RegLike (a a' : Val) : Prop := a = a' ∨ (NP a ∧ NP a' ∧ Arm64.reg a = Arm64.reg a')

/-- `RegLike` elementwise. -/
inductive RegLikeL : List Val → List Val → Prop
  | nil : RegLikeL [] []
  | cons {a a' : Val} {l l' : List Val} : RegLike a a' → RegLikeL l l' → RegLikeL (a :: l) (a' :: l')

theorem RegLike.refl (a : Val) : RegLike a a := .inl rfl

theorem RegLike.reg {a a' : Val} (h : RegLike a a') : Arm64.reg a = Arm64.reg a' := by
  rcases h with rfl | ⟨-, -, h⟩
  · rfl
  · exact h

theorem regLike_of {s t : Val} (h : NarrowR s t) : RegLike s t := by
  rcases h with rfl | ⟨c, w, rfl, rfl⟩
  · exact .inl rfl
  · refine .inr ⟨fun p h => (by cases h), fun p h => (by cases h), ?_⟩
    cases c <;> cases w <;> rfl

/-- **The removed `MOVBUreg`** of a register at the `bool` shape, at an integer shape. -/
theorem movbu_narrow {md : LMode} (hl : md.low = true) {w : Width} {a : Val} (hb : BoolV a) :
    NarrowR (md.retype (.int w) (Arm64.op1 (.int w) (Arm64.ext false 8) [a])) a := by
  unfold LMode.retype
  rw [hl, if_pos (rfl : true = true)]
  rcases hb with rfl | ⟨c, rfl⟩
  · exact .inl (by simp [Arm64.op1, Arm64.reg, Val.retypeL, Val.widen, Val.retype])
  · right
    refine ⟨c, w, rfl, ?_⟩
    have he := ext_bool (sE := false) (kE := 8) (by omega) (by omega) c
    simp only [Arm64.op1, Arm64.reg, Arm64.res, he]
    cases c <;> cases w <;> rfl

/-- **A `Phi` at an integer shape** reads both alike. -/
theorem retype_narrow {md : LMode} (hl : md.low = true) (w' : Width) {s t : Val}
    (h : NarrowR s t) : md.retype (.int w') s = md.retype (.int w') t := by
  rcases h with rfl | ⟨c, w, rfl, rfl⟩
  · rfl
  · unfold LMode.retype
    rw [hl, if_pos (rfl : true = true), if_pos (rfl : true = true)]
    cases c <;> cases w <;> cases w' <;> rfl

/-! ## Register families -/

theorem op1_rl {ty : Ty} {f : BitVec 64 → BitVec 64} :
    ∀ {l l' : List Val}, RegLikeL l l' → Arm64.op1 ty f l = Arm64.op1 ty f l'
  | [], [], .nil => rfl
  | [_], [_], .cons h .nil => by simp only [Arm64.op1, h.reg]
  | _ :: _ :: _, _ :: _ :: _, .cons _ (.cons _ _) => rfl

theorem op2_rl {ty : Ty} {f : BitVec 64 → BitVec 64 → BitVec 64} :
    ∀ {l l' : List Val}, RegLikeL l l' → Arm64.op2 ty f l = Arm64.op2 ty f l'
  | [], [], .nil => rfl
  | [_], [_], .cons _ .nil => rfl
  | [_, _], [_, _], .cons h1 (.cons h2 .nil) => by simp only [Arm64.op2, h1.reg, h2.reg]
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ _)) => rfl

theorem addP_rl {ty : Ty} {k : BitVec 64} {a a' : Val} (h : RegLike a a') :
    Arm64.addP ty a k = Arm64.addP ty a' k := by
  rcases h with rfl | ⟨ha, ha', hr⟩
  · rfl
  · have e : ∀ b, NP b → Arm64.addP ty b k =
        match Arm64.reg b with
        | some x => Arm64.res ty (x + k)
        | none => .poison := by
      intro b hb; cases b <;> first | exact absurd rfl (hb _) | rfl
    rw [e a ha, e a' ha', hr]

theorem addK_rl {ty : Ty} {k : BitVec 64} :
    ∀ {l l' : List Val}, RegLikeL l l' → Arm64.addK ty k l = Arm64.addK ty k l'
  | [], [], .nil => rfl
  | [_], [_], .cons h .nil => addP_rl h
  | _ :: _ :: _, _ :: _ :: _, .cons _ (.cons _ _) => rfl

theorem addSh_rl {ty : Ty} {sh : Arm64.Shift} {k : Int64} :
    ∀ {l l' : List Val}, RegLikeL l l' → Arm64.addSh ty sh k l = Arm64.addSh ty sh k l'
  | [], [], .nil => rfl
  | [_], [_], .cons _ .nil => rfl
  | [_, _], [_, _], .cons h1 (.cons h2 .nil) => by
    simp only [Arm64.addSh, h2.reg]
    split
    · exact addP_rl h1
    · rfl
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ _)) => rfl

theorem subSh_rl {ty : Ty} {sh : Arm64.Shift} {k : Int64} :
    ∀ {l l' : List Val}, RegLikeL l l' → Arm64.subSh ty sh k l = Arm64.subSh ty sh k l'
  | [], [], .nil => rfl
  | [_], [_], .cons _ .nil => rfl
  | [_, _], [_, _], .cons h1 (.cons h2 .nil) => by
    simp only [Arm64.subSh, h2.reg]
    split
    · exact addP_rl h1
    · rfl
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ _)) => rfl

/-- `ADD` of a non-pointer first argument reads its register. -/
theorem add_np0 {ty : Ty} {a : Val} (ha : NP a) (b : Val) :
    Arm64.add ty [a, b] =
      match b with
      | .ptr p => (match Arm64.reg a with
        | some k => PtrOps.ptrRes (p.add k)
        | none => .poison)
      | _ => Arm64.op2 ty (· + ·) [a, b] := by
  cases a <;> (try exact absurd rfl (ha _)) <;> cases b <;> rfl

/-- `ADD` of a non-pointer second argument reads its register. -/
theorem add_np1 {ty : Ty} {b : Val} (hb : NP b) (a : Val) :
    Arm64.add ty [a, b] =
      match a with
      | .ptr p => (match Arm64.reg b with
        | some k => PtrOps.ptrRes (p.add k)
        | none => .poison)
      | _ => Arm64.op2 ty (· + ·) [a, b] := by
  cases b <;> (try exact absurd rfl (hb _)) <;> cases a <;> rfl

theorem add_one {ty : Ty} (a : Val) : Arm64.add ty [a] = .poison := by cases a <;> rfl

theorem add_long {ty : Ty} (a b c : Val) (l : List Val) : Arm64.add ty (a :: b :: c :: l) = .poison := by
  cases a <;> cases b <;> rfl

theorem add_rl {ty : Ty} :
    ∀ {l l' : List Val}, RegLikeL l l' → Arm64.add ty l = Arm64.add ty l'
  | [], [], .nil => rfl
  | [a], [a'], .cons _ .nil => by rw [add_one, add_one]
  | [a, b], [a', b'], .cons h1 (.cons h2 .nil) => by
    have s1 : Arm64.add ty [a, b] = Arm64.add ty [a', b] := by
      rcases h1 with rfl | ⟨ha, ha', hr⟩
      · rfl
      · rw [add_np0 ha, add_np0 ha']
        cases b <;> simp only [Arm64.op2, hr]
    have s2 : Arm64.add ty [a', b] = Arm64.add ty [a', b'] := by
      rcases h2 with rfl | ⟨hb, hb', hr⟩
      · rfl
      · rw [add_np1 hb, add_np1 hb']
        cases a' <;> simp only [Arm64.op2, hr]
    rw [s1, s2]
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ _)) => by
    rw [add_long, add_long]

/-- `SUB` of a non-pointer first argument is `op2`. -/
theorem sub_np0 {ty : Ty} {a : Val} (ha : NP a) (b : Val) :
    Arm64.sub ty [a, b] = Arm64.op2 ty (· - ·) [a, b] := by
  cases a <;> (try exact absurd rfl (ha _)) <;> cases b <;> rfl

/-- `SUB` of a non-pointer second argument reads its register. -/
theorem sub_np1 {ty : Ty} {b : Val} (hb : NP b) (a : Val) :
    Arm64.sub ty [a, b] =
      match a with
      | .ptr p => (match Arm64.reg b with
        | some k => PtrOps.ptrRes (p.add (-k))
        | none => .poison)
      | _ => Arm64.op2 ty (· - ·) [a, b] := by
  cases b <;> (try exact absurd rfl (hb _)) <;> cases a <;> rfl

theorem sub_one {ty : Ty} (a : Val) : Arm64.sub ty [a] = .poison := by cases a <;> rfl

theorem sub_long {ty : Ty} (a b c : Val) (l : List Val) : Arm64.sub ty (a :: b :: c :: l) = .poison := by
  cases a <;> cases b <;> rfl

theorem sub_rl {ty : Ty} :
    ∀ {l l' : List Val}, RegLikeL l l' → Arm64.sub ty l = Arm64.sub ty l'
  | [], [], .nil => rfl
  | [a], [a'], .cons _ .nil => by rw [sub_one, sub_one]
  | [a, b], [a', b'], .cons h1 (.cons h2 .nil) => by
    have s1 : Arm64.sub ty [a, b] = Arm64.sub ty [a', b] := by
      rcases h1 with rfl | ⟨ha, ha', hr⟩
      · rfl
      · rw [sub_np0 ha, sub_np0 ha']
        simp only [Arm64.op2, hr]
    have s2 : Arm64.sub ty [a', b] = Arm64.sub ty [a', b'] := by
      rcases h2 with rfl | ⟨hb, hb', hr⟩
      · rfl
      · rw [sub_np1 hb, sub_np1 hb']
        cases a' <;> simp only [Arm64.op2, hr]
    rw [s1, s2]
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ _)) => by
    rw [sub_long, sub_long]

/-! ## The readers -/

/-- The ops of `regOps` are pure arm64 ops, neither `MOVDreg`/`MOVDnop` nor `Phi` nor a store. -/
theorem regOps_pure : ∀ o ∈ regOps, o.generic = false ∧ LowerTerm.actOp o = false ∧
    isRoot o = false ∧ o ≠ .ARM64MOVDreg ∧ o ≠ .ARM64MOVDnop ∧ o ≠ .Phi ∧ o ∉ stOps := by
  decide +kernel

/-- The stores of `stOps` need the activation, and are neither `MOVDreg`/`MOVDnop` nor `Phi`. -/
theorem stOps_act : ∀ o ∈ stOps, o.generic = false ∧ LowerTerm.actOp o = true ∧
    o ≠ .ARM64MOVDreg ∧ o ≠ .ARM64MOVDnop ∧ o ≠ .Phi := by
  decide +kernel

/-- `AND` off the `bool` shape (where it absorbs a `false` operand) reads registers alike. -/
theorem and_rl {ty : Ty} (hb : ty ≠ .bool) {l l' : List Val} (h : RegLikeL l l') :
    Arm64.and ty l = Arm64.and ty l' := by
  rw [Arm64.and_of_ne_bool hb, Arm64.and_of_ne_bool hb]
  exact op2_rl h

/-- **A `regOps` op reads registers alike** (an `AND` off the `bool` shape). -/
theorem evalPure_rl {o : Op} (ho : o ∈ regOps) {ty : Ty} (hand : o = .ARM64AND → ty ≠ .bool)
    {k : Int64} {ax : Option AuxRef} {l l' : List Val} (h : RegLikeL l l') :
    Arm64.evalPure o ty k ax l = Arm64.evalPure o ty k ax l' := by
  simp only [regOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  repeat' (rcases ho with rfl | ho)
  · exact add_rl h
  · exact addK_rl h
  · exact sub_rl h
  · exact addK_rl h
  · exact op2_rl h
  · exact op1_rl h
  · exact op1_rl h
  · exact and_rl (hand rfl) h
  · exact op1_rl h
  · exact op2_rl h
  · exact op1_rl h
  · exact op2_rl h
  · exact op1_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op1_rl h
  · exact op1_rl h
  · exact op1_rl h
  · exact addSh_rl h
  · exact addSh_rl h
  · exact addSh_rl h
  · exact subSh_rl h
  · exact subSh_rl h
  · exact subSh_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op2_rl h
  · exact op1_rl h
  · exact op1_rl h
  · exact op1_rl h
  · exact op1_rl h
  · exact op1_rl h
  · exact op1_rl h

/-- A store writes the low bytes of the register of either value. -/
theorem storeBytes_narrow (n : Nat) {s t : Val} (h : NarrowR s t) :
    Arm64.storeBytes n s = Arm64.storeBytes n t := by
  rcases h with rfl | ⟨c, w, rfl, rfl⟩
  · rfl
  · have hr := (regLike_of (.inr ⟨c, w, rfl, rfl⟩)).reg
    unfold Arm64.storeBytes
    simp only [hr]

/-- **A store of either value** (`stOps`, the stored value) does the same. -/
theorem st_narrow {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} (ho : u.op ∈ stOps)
    {a xs xt : Val} {m : Mem} {ty : Ty} (h : NarrowR xs xt) :
    arm64Op false env ctx fr u [a, xt, .mem m] ty = arm64Op false env ctx fr u [a, xs, .mem m] ty := by
  rcases h with rfl | ⟨c, w, rfl, rfl⟩
  · rfl
  have hs := storeBytes_narrow (s := .int w (if c then 1 else 0)) (t := .bool c)
    (h := .inr ⟨c, w, rfl, rfl⟩)
  simp only [stOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold arm64Op
  rcases ho with h | h | h | h <;>
  · simp only [show nilFaults false ctx u _ = none from rfl, h]
    cases symAddr ctx u a with
    | some p => simp only [Arm64.storeN, hs]
    | none => simp [List.any]

end GoFV.Proof.LateLowerL
