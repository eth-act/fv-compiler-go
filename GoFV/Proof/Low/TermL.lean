import GoFV.Proof.TermStep
import GoFV.Opt.LowerCheck

/-!
# Lowered values as terms over atoms (issue #385)

Phase 1's `GoFV.Proof.Term` for `runL`: a value whose `termVL` holds is a term over the *atoms*
(phis, roots, activation-dependent values): `denL low D tabs ρ n x` evaluates `x`'s definition in
`D` recursively with fuel `n` as `runL` does in mode `low` (`Sem.evalValueL`: `opValL` at the
value's shape `shp low`, then `rty low`), reading atoms (and values `D` does not define) from
`ρ`. `low` is the function's `Func.lowered` (`runL` reads a lowered function's values as
registers, `Val.retypeL`, at the lowered shapes, `Sem.tyOfL`).

`ArgTermRefL o lowD D x lowE E y`: for every fuel on the left there is one on the right such that
for valuations `ρ ⊑ ρ'` whose atom values are fixed by `rty` at their shapes (`TypedL`), `denL lowD
D … x` and `denL lowE E … y` are related by `ArgRel o`: refinement, or (`o = some k`, the address
of an arm64 store lowering a `Store`, `stArg`) `AddrRef k`: the second moved by `k` is, as an
address, the pointer word the first is. `AtomArgsRefL` and `TermStepRefL` are the premises of the
atom simulation (`GoFV.Proof.Low.atomSimL_refines`) that the validator
(`GoFV.Opt.LowerCheck.validateL`) establishes (`GoFV.Proof.Low.validateL_termRef`).
-/

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.LowerCheck GoFV.Proof.Term

/-- `x` is a term node of `D`. -/
def IsTermL (tabs : Tables) (D : ID → Option Value) (x : ID) : Prop :=
  ∃ v, D x = some v ∧ termVL tabs v = true

/-- The shape of `x`'s type in `D` in mode `low` (`other` if undefined). -/
def shapeL (low : Bool) (D : ID → Option Value) (tabs : Tables) (x : ID) : Ty :=
  ((D x).map fun v => shp low tabs v.type).getD .other

/-- The value of `x` as a term over the atoms, in mode `low`, with fuel `n` (`poison` when
exhausted). -/
def denL (low : Bool) (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) : Nat → ID → Val
  | 0, _ => .poison
  | n + 1, x =>
    match D x with
    | some v =>
      if termVL tabs v then
        rty low (shp low tabs v.type)
          (opValL tabs v.op (shp low tabs v.type) v.auxInt v.aux
            (v.args.toList.map (denL low D tabs ρ n)))
      else ρ x
    | none => ρ x

/-- The atoms `D` defines hold values fixed by `rty low` at their shapes (as `runL`'s registers
do). -/
def TypedL (low : Bool) (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) : Prop :=
  ∀ a, ¬ IsTermL tabs D a → (D a).isSome → rty low (shapeL low D tabs a) (ρ a) = ρ a

/-- `y` moved by `k` is, as an arm64 address (`Arm64.addr`), the pointer word `x` is
(`Val.asPtrWord`, the address a `Store` writes at). -/
def AddrRef (k : Int64) (x y : Val) : Prop :=
  ∀ p, x.asPtrWord = some p → Arm64.addr y (BitVec.ofInt 64 k.toInt) = some p

/-- How argument `i` of the atom `w` relates to argument `i` of the atom `u` it corresponds to:
the address of an arm64 store lowering a `Store` (argument 0) at the store's offset
(`AddrRef`, `ARM64.rules:758-776` fold `ADDconst` offsets into it), else by refinement. -/
def stArg (u w : Value) (i : Nat) : Option Int64 :=
  if i == 0 && u.op == .Store && (stSize w.op).isSome then some w.auxInt else none

/-- `stArg` is refinement unless `w` is an arm64 store. -/
theorem stArg_none {u w : Value} {i : Nat} (h : stSize w.op = none) : stArg u w i = none := by
  unfold stArg; rw [h]; simp

/-- `stArg` is refinement beyond argument 0. -/
theorem stArg_succ (u w : Value) (i : Nat) : stArg u w (i + 1) = none := by
  unfold stArg; simp

/-- `stArg` is refinement unless `u` is a `Store`. -/
theorem stArg_of_ne {u w : Value} {i : Nat} (h : u.op ≠ .Store) : stArg u w i = none := by
  unfold stArg; simp [h]

/-- An atom paired with itself: refinement. -/
theorem stArg_self (a : Value) (i : Nat) : stArg a a i = none := by
  by_cases h : a.op = .Store
  · exact stArg_none (by rw [h]; rfl)
  · exact stArg_of_ne h

/-- The address argument of an arm64 store lowering a `Store`. -/
theorem stArg_zero {u w : Value} (hu : u.op = .Store) (hw : (stSize w.op).isSome = true) :
    stArg u w 0 = some w.auxInt := by
  unfold stArg; simp [hu, hw]

/-- The arguments of an arm64 store lowering a `Store`. -/
theorem stArg_store {u w : Value} {i : Nat} (hu : u.op = .Store) (hw : (stSize w.op).isSome = true) :
    stArg u w i = if i = 0 then some w.auxInt else none := by
  unfold stArg; simp [hu, hw]

/-- `stArg` reads the op and the auxint. -/
theorem stArg_congr {u w w' : Value} {i : Nat} (hop : w.op = w'.op) (hai : w.auxInt = w'.auxInt) :
    stArg u w i = stArg u w' i := by
  unfold stArg; rw [hop, hai]

/-- `Sem.Refines`, or `AddrRef` at an offset. -/
def ArgRel : Option Int64 → Val → Val → Prop
  | none, x, y => Sem.Refines x y
  | some k, x, y => AddrRef k x y

/-- `y` in `E` (mode `lowE`) is related by `ArgRel o` to `x` in `D` (mode `lowD`) as a term over
the atoms. -/
def ArgTermRefL (o : Option Int64) (lowD : Bool) (D : ID → Option Value) (tabs : Tables) (x : ID)
    (lowE : Bool) (E : ID → Option Value) (tabs' : Tables) (y : ID) : Prop :=
  ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → TypedL lowD D tabs ρ → TypedL lowE E tabs' ρ' →
    ArgRel o (denL lowD D tabs ρ n x) (denL lowE E tabs' ρ' m y)

/-- A refinement whose source is a pointer word is that word. -/
theorem asPtrWord_of_refines {x y : Val} {p : Ptr} (h : Sem.Refines x y)
    (hp : x.asPtrWord = some p) : y = x := by
  cases h <;> first | rfl | simp [Val.asPtrWord] at hp

/-- A defined arm64 address is read off a value its refinements equal. -/
theorem addr_of_refines {y y' : Val} {k : BitVec 64} {p : Ptr} (h : Sem.Refines y y')
    (hp : Arm64.addr y k = some p) : y' = y := by
  cases h <;> first | rfl | simp [Arm64.addr, Arm64.reg] at hp

/-- `ArgRel` is closed under refinement on the right. -/
theorem ArgRel.trans_right {o : Option Int64} {x y y' : Val} (h : ArgRel o x y)
    (h2 : Sem.Refines y y') : ArgRel o x y' := by
  cases o with
  | none => exact Sem.Refines.trans h h2
  | some k =>
    intro p hp
    have := h p hp
    rw [addr_of_refines h2 this]; exact this

/-- `ArgRel` is closed under refinement on the left. -/
theorem ArgRel.trans_left {o : Option Int64} {x x' y : Val} (h1 : Sem.Refines x x')
    (h : ArgRel o x' y) : ArgRel o x y := by
  cases o with
  | none => exact Sem.Refines.trans h1 h
  | some k =>
    intro p hp
    exact h p (by rw [asPtrWord_of_refines h1 hp]; exact hp)

/-- A pointer word is its own arm64 address at offset 0. -/
theorem addr_of_asPtrWord {a : Val} {p : Ptr} (h : a.asPtrWord = some p) :
    Arm64.addr a 0 = some p := by
  cases a with
  | ptr q =>
    simp only [Val.asPtrWord, Option.some.injEq] at h
    subst h
    simp [Arm64.addr, Ptr.add]
  | int w x =>
    cases w <;> simp only [Val.asPtrWord, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    simp [Arm64.addr, Arm64.reg]
  | _ => simp [Val.asPtrWord] at h

/-- A refinement is an address at offset 0. -/
theorem addrRef_zero {x y : Val} (h : Sem.Refines x y) : AddrRef 0 x y := by
  intro p hp
  rw [asPtrWord_of_refines h hp, show BitVec.ofInt 64 (0 : Int64).toInt = 0 by decide]
  exact addr_of_asPtrWord hp

/-- The arguments of every atom listed in `g` refine, as terms, those of the atom of `f` it
corresponds to (`atomPair`: the same ID and fields, a renamed op, or a lowered store, whose address
is related by `AddrRef` at its offset, `stArg`), unless the atom of `g` reads no argument
(`argFree`: a lowered frame address). -/
def AtomArgsRefL (tabs : Tables) (f g : Func) : Prop :=
  ∀ b ∈ g.blocks, ∀ gb, g.block? b = some gb → ∀ a ∈ gb.values, ∀ u, g.value? a = some u →
    termVL tabs u = false →
    ∃ u', f.value? a = some u' ∧ atomPair tabs u' u = true ∧ (argFree tabs u = true ∨
      ∀ i < u.args.size, ArgTermRefL (stArg u' u i)
        f.lowered f.value? tabs u'.args[i]! g.lowered (listedDefs g) tabs u.args[i]!)

/-- The terminator of `b` (`Sem.stepTermL`) on the control values `cs`. -/
def stepValsL (b : Block) (cs : List Val) : Res Next :=
  if b.kind.isArm64 then
    match b.kind with
    | .ARM64JUMPTABLE => do
      match Arm64.reg (← ctlV b cs 0) with
      | some x => succ b x.toNat
      | none => .stuck s!"b{b.id}: JUMPTABLE on poison or non-int"
    | k => do
      match Arm64.taken k b.auxInt (← ctlV b cs 0) with
      | some true => succ b 0
      | some false => succ b 1
      | none => .stuck s!"b{b.id}: {k.name} on poison or an ill-typed control"
  else stepVals b cs

/-- The terminator of every block of `g`, as a function of its controls' terms over the atoms,
refines that of `f`'s block, and the successors of `f`'s block are successors of `g`'s. -/
def TermStepRefL (tabs : Tables) (f g : Func) : Prop :=
  ∀ b ∈ g.blocks, ∀ fb gb, f.block? b = some fb → g.block? b = some gb →
    (∀ e ∈ fb.succs, e ∈ gb.succs) ∧
    ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → TypedL f.lowered f.value? tabs ρ →
      TypedL g.lowered (listedDefs g) tabs ρ' →
      Res.Rel Next.Refines (stepValsL fb (fb.controls.toList.map (denL f.lowered f.value? tabs ρ n)))
        (stepValsL gb (gb.controls.toList.map (denL g.lowered (listedDefs g) tabs ρ' m)))

end GoFV.Proof.Low
