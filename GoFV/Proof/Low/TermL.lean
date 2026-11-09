import GoFV.Proof.TermStep
import GoFV.Opt.LowerCheck

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lowered values as terms over atoms (issue #385)

Phase 1's `GoFV.Proof.Term` for `runL`: a value whose `termVL` holds is a term over the *atoms*
(phis, roots, activation-dependent values): `denL low D tabs ρ n x` evaluates `x`'s definition in
`D` recursively with fuel `n` as `runL` does in mode `low` (`Sem.evalValueL`: `opValL` at the
value's shape `shp low`, then `rty low`), reading atoms (and values `D` does not define) from
`ρ`. `low` is the function's `Func.lowered` (`runL` reads a lowered function's values as
registers, `Val.retypeL`, at the lowered shapes, `Sem.tyOfL`).

`ArgTermRefL o lowD D x lowE E y`: for every fuel on the left there is one on the right such that
for valuations `ρ ⊑ ρ'` whose atom values are fixed by `rty` at their shapes (`TypedL`) and whose
frame addresses (`LocalAddr {n}` atoms of `D`) hold `n`'s address in activation 0 (`FrameVals`;
`runL`'s activation, where the integer loads of a frame variable read, `ldVal`), `denL lowD D … x`
and `denL lowE E … y` are related by `ArgRel 0 o`: refinement,
or (`o = some (k, ax)`, the address of an arm64 store lowering a `Store`, `stArg`) `AddrRef 0 ax
k`: the store's address on the second (`addrAt`, `Sem.symAddr`: a global symbol's or frame
variable's at the offset, or the base moved by it) is, as an address, the pointer word the first
is. `AtomArgsRefL` and `TermStepRefL` are the premises of the atom simulation
(`GoFV.Proof.Low.atomSimL_refines`) that the validator (`GoFV.Opt.LowerCheck.validateL`)
establishes (`GoFV.Proof.Low.validateL_termRef`).
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

/-- The address an arm64 store at offset `k` with aux `ax` writes at on the base `y`, in
activation `act` (`Sem.symAddr`): a global symbol's or a frame variable's at the offset, or the
base moved by it. -/
def addrAt (tabs : Tables) (act : Nat) (ax : Option AuxRef) (k : Int64) (y : Val) : Option Ptr :=
  match ax with
  | some n =>
    match tabs.aux? n with
    | some { kind := .sym name .., .. } =>
      some ⟨.global name.toStringLossy, BitVec.ofInt 64 k.toInt⟩
    | some { kind := .name .., .. } => some ⟨frameBlk tabs act n, BitVec.ofInt 64 k.toInt⟩
    | _ => none
  | none => Arm64.addr y (BitVec.ofInt 64 k.toInt)

/-- An arm64 store's address on base `y` (`addrAt` at its aux and offset) is the pointer word `x`
is (`Val.asPtrWord`, the address a `Store` writes at). -/
def AddrRef (tabs : Tables) (act : Nat) (ax : Option AuxRef) (k : Int64) (x y : Val) : Prop :=
  ∀ p, x.asPtrWord = some p → addrAt tabs act ax k y = some p

/-- The 16-byte half `i` that a `Move` copies from the pointer word `s` in the memory `m`: the blob
of the 16 bytes at `s` moved by `16 i` (`Arm64.load16`), `poison` without a pointer word or a
memory. The 128-bit store lowering the `Move` (`moveQLower`) writes refinements of them. -/
def qPart (i : Nat) (s m : Val) : Val :=
  match s.asPtrWord, m with
  | some p, .mem mm => Arm64.load16 mm (p.add (BitVec.ofNat 64 (16 * i)))
  | _, _ => .poison

/-- The 16 bytes a `Move` copies from the pointer word `s` in the memory `m`, `k` bytes in
(`qPart i` is `qAt (16 i)`): what each 128-bit store of a `Move` lowered to two stores
(`ARM64.rules:423`, `431`, `434`) writes, the outer one at `k = s - 16` or `s - 32`. -/
def qAt (k : Nat) (s m : Val) : Val :=
  match s.asPtrWord, m with
  | some p, .mem mm => Arm64.load16 mm (p.add (BitVec.ofNat 64 k))
  | _, _ => .poison

theorem qPart_eq_qAt (i : Nat) (s m : Val) : qPart i s m = qAt (16 * i) s m := rfl

/-- How argument `i` of the atom `w` relates to argument `i` of the atom `u` it corresponds to:
the address of an arm64 store lowering a `Store` (argument 0) at the store's offset and aux
(`AddrRef`; `ARM64.rules:758-776` fold `ADDconst` offsets into it, `881-905` symbols and frame
variables), else by refinement. -/
def stArg (u w : Value) (i : Nat) : Option (Int64 × Option AuxRef) :=
  if i == 0 && u.op == .Store && (stSize w.op).isSome then some (w.auxInt, w.aux) else none

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
    stArg u w 0 = some (w.auxInt, w.aux) := by
  unfold stArg; simp [hu, hw]

/-- The arguments of an arm64 store lowering a `Store`. -/
theorem stArg_store {u w : Value} {i : Nat} (hu : u.op = .Store) (hw : (stSize w.op).isSome = true) :
    stArg u w i = if i = 0 then some (w.auxInt, w.aux) else none := by
  unfold stArg; simp [hu, hw]

/-- `stArg` reads the op, the auxint and the aux. -/
theorem stArg_congr {u w w' : Value} {i : Nat} (hop : w.op = w'.op) (hai : w.auxInt = w'.auxInt)
    (hax : w.aux = w'.aux) : stArg u w i = stArg u w' i := by
  unfold stArg; rw [hop, hai, hax]

/-- `Sem.Refines`, or `AddrRef` at an offset and aux, in activation `act`. -/
def ArgRel (tabs : Tables) (act : Nat) : Option (Int64 × Option AuxRef) → Val → Val → Prop
  | none, x, y => Sem.Refines x y
  | some (k, ax), x, y => AddrRef tabs act ax k x y

/-- The address an indexed store at the scale `s` writes at on the base `a` and the index `i`
(`Sem.arm64Op`'s `stIdx`, at offset 0): `a + i` (`Arm64.add`), or `a` moved by `i`'s register
times `s`. -/
def idxAddr (s : Nat) (a i : Val) : Val :=
  if s = 1 then Arm64.add .other [a, i] else
    match Arm64.reg i with
    | some k => Arm64.add .other [a, .int .w64 (k * BitVec.ofNat 64 s)]
    | none => .poison

/-- The scale of the indexed store `o` (`idxStore`). -/
def idxScale (o : Op) : Nat := ((idxStore o).map (·.2)).getD 1

/-- The address of the frame variable `n` in activation `act` (`Sem.frameVal`). -/
def framePtr (tabs : Tables) (act : Nat) (n : AuxRef) : Ptr := ⟨frameBlk tabs act n, 0⟩

/-- The atoms of `D` that are frame addresses (`LocalAddr {n}`) hold, under `ρ`, the address of
`n` in activation `act` as a word (`Ptr.word`) at a word shape, or `poison` (as `runL`'s
registers do, `Sem.frameVal` shaped). -/
def FrameVals (tabs : Tables) (act : Nat) (D : ID → Option Value) (ρ : ID → Val) : Prop :=
  ∀ a l n, D a = some l → l.op = .LocalAddr → l.aux = some n →
    ρ a = .poison ∨ (ρ a = (framePtr tabs act n).word ∧ wordShape (shpL tabs l.type) = true)

/-- The stack pointer of activation `act` (`Sem.evalOp` of `SP`: the outgoing-arguments block at
offset 0). -/
def spPtr (act : Nat) : Ptr := ⟨.outargs act, 0⟩

/-- The atoms of `D` that are the stack pointer (`SP`) hold, under `ρ`, the stack pointer of
activation `act` as a word at a word shape, or `poison` (as `runL`'s registers do, `SP` shaped). -/
def SPVals (tabs : Tables) (act : Nat) (D : ID → Option Value) (ρ : ID → Val) : Prop :=
  ∀ a s, D a = some s → s.op = .SP →
    ρ a = .poison ∨ (ρ a = (spPtr act).word ∧ wordShape (shpL tabs s.type) = true)

/-- The atoms of `E` that are lowered frame addresses (`MOVDaddr {n}` with one argument, an atom by
`termVL`: a name at offset 0) hold, under `ρ'`, the address of `n` in activation `act` as a word at
a word shape (`Sem.symAddr` of a frame variable, whatever the argument; `runL`'s registers do,
`RegsFrameL`). -/
def FrameValsL (tabs : Tables) (act : Nat) (E : ID → Option Value) (ρ' : ID → Val) : Prop :=
  ∀ a w n, E a = some w → w.op = .ARM64MOVDaddr → w.aux = some n → termVL tabs w = false →
    w.args.size = 1 → wordShape (shpL tabs w.type) = true → ρ' a = (framePtr tabs act n).word

/-- What `frameAtomG` says. -/
theorem frameAtomG_cases {tabs : Tables} {f : Func} {x : ID} {w : Value}
    (h : frameAtomG tabs f x w = true) : w.op = .ARM64MOVDaddr ∧ termVL tabs w = false ∧
      w.args.size = 1 ∧ IsTermL tabs f.value? x := by
  unfold frameAtomG at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  cases hv : f.value? x with
  | none => rw [hv] at h4; cases h4
  | some v => rw [hv] at h4; exact ⟨v, hv, by simpa using h4⟩

/-- `y` in `E` (mode `lowE`) is related by `ArgRel o` to `x` in `D` (mode `lowD`) as a term over
the atoms, the valuations holding the frame addresses and the source's stack pointer in
activation 0 (`FrameVals`, `FrameValsL`, `SPVals`; `runL` runs a function in activation 0,
`Ctx.makeL`, where the integer loads of a frame variable read, `ldVal`). -/
def ArgTermRefL (o : Option (Int64 × Option AuxRef)) (lowD : Bool) (D : ID → Option Value)
    (tabs : Tables) (x : ID) (lowE : Bool) (E : ID → Option Value) (tabs' : Tables) (y : ID) :
    Prop :=
  ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → TypedL lowD D tabs ρ → TypedL lowE E tabs' ρ' →
    FrameVals tabs 0 D ρ → SPVals tabs 0 D ρ → FrameValsL tabs' 0 E ρ' →
      ArgRel tabs 0 o (denL lowD D tabs ρ n x) (denL lowE E tabs' ρ' m y)

/-- `fitPiece t` is monotone. -/
theorem fitPiece_mono (t : Ty) {x y : Val} (h : Sem.Refines x y) :
    Sem.Refines (fitPiece t x) (fitPiece t y) := by
  cases h with
  | poison v => cases t <;> exact .poison _
  | int w a => exact Sem.Refines.refl _
  | bool b => exact Sem.Refines.refl _
  | ptr p => exact Sem.Refines.refl _
  | mem h => cases t <;> exact .mem h
  | tuple h => cases t <;> exact .tuple h
  | agg h => cases t <;> exact .agg h
  | blob h => cases t <;> exact .blob h
  | empty => exact Sem.Refines.refl _

/-- **A piece narrowed to `w ≥ w'` bits fits an integer leaf of `w'` bits as the piece does**
(`fitPiece` keeps the leaf's low bits, `Val.retypeL`). -/
theorem fitPiece_retypeL {w w' : Width} (hw : w'.bits ≤ w.bits) (hw64 : w ≠ .w64) (X : Val) :
    Sem.Refines (fitPiece (.int w') (X.retypeL (.int w))) (fitPiece (.int w') X) := by
  cases X with
  | int v x =>
    cases w <;> cases w' <;> cases v <;> simp_all (config := { decide := true }) [fitPiece,
      Val.retypeL, Val.widen, Val.retype, Width.bits, BitVec.setWidth_setWidth_of_le] <;>
      exact Sem.Refines.refl _
  | bool b =>
    cases w <;> cases w' <;> cases b <;> simp_all (config := { decide := true }) [fitPiece,
      Val.retypeL, Val.widen, Val.retype, Width.bits] <;> exact Sem.Refines.refl _
  | ptr p =>
    have : (Val.ptr p).retypeL (.int w) = .poison := by
      cases w <;> simp_all [Val.retypeL, Val.widen, Val.retype]
    rw [this]; exact .poison _
  | _ => simp only [Val.retypeL, Val.widen, Val.retype]; exact .poison _

/-- The lowered calls `callLead` lists. -/
theorem callLead_some {o : Op} {k : Nat} (h : callLead o = some k) :
    (o = .ARM64CALLstatic ∧ k = 0) ∨ (o = .ARM64CALLclosure ∧ k = 2) ∨
      (o = .ARM64CALLinter ∧ k = 1) := by
  unfold callLead at h
  split at h <;> simp_all

/-- `y` in `E` holds, fitted to the leaf shape `t` (`fitPiece`, a lowered call's register piece),
a refinement of `x` in `D` so fitted, as terms over the atoms (as `ArgTermRefL`). -/
def ArgTermFitL (t : Ty) (lowD : Bool) (D : ID → Option Value) (tabs : Tables) (x : ID)
    (lowE : Bool) (E : ID → Option Value) (tabs' : Tables) (y : ID) : Prop :=
  ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → TypedL lowD D tabs ρ → TypedL lowE E tabs' ρ' →
    FrameVals tabs 0 D ρ → SPVals tabs 0 D ρ → FrameValsL tabs' 0 E ρ' →
      Sem.Refines (fitPiece t (denL lowD D tabs ρ n x)) (fitPiece t (denL lowE E tabs' ρ' m y))

/-- The base `y` and the index `z` in `E` give at the scale `s` (`idxAddr`, an indexed store's
address) the address the pointer word `x` in `D` is (`AddrRef` at offset 0 without aux), as terms
over the atoms (as `ArgTermRefL`). -/
def ArgTermIdxL (s : Nat) (lowD : Bool) (D : ID → Option Value) (tabs : Tables) (x : ID)
    (lowE : Bool) (E : ID → Option Value) (tabs' : Tables) (y z : ID) : Prop :=
  ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → TypedL lowD D tabs ρ → TypedL lowE E tabs' ρ' →
    FrameVals tabs 0 D ρ → SPVals tabs 0 D ρ → FrameValsL tabs' 0 E ρ' →
      AddrRef tabs 0 none 0 (denL lowD D tabs ρ n x)
        (idxAddr s (denL lowE E tabs' ρ' m y) (denL lowE E tabs' ρ' m z))

/-- `y` in `E` holds a refinement of the 16-byte half `i` a `Move` copies from the source `s` in
the memory `m` of `D` (`qPart`), as terms over the atoms (as `ArgTermRefL`). -/
def ArgTermQL (i : Nat) (lowD : Bool) (D : ID → Option Value) (tabs : Tables) (s m : ID)
    (lowE : Bool) (E : ID → Option Value) (tabs' : Tables) (y : ID) : Prop :=
  ∀ n, ∃ k, ∀ ρ ρ', ValRef ρ ρ' → TypedL lowD D tabs ρ → TypedL lowE E tabs' ρ' →
    FrameVals tabs 0 D ρ → SPVals tabs 0 D ρ → FrameValsL tabs' 0 E ρ' →
      Sem.Refines (qPart i (denL lowD D tabs ρ n s) (denL lowD D tabs ρ n m))
        (denL lowE E tabs' ρ' k y)

/-- A refinement whose source is a pointer word is that word. -/
theorem asPtrWord_of_refines {x y : Val} {p : Ptr} (h : Sem.Refines x y)
    (hp : x.asPtrWord = some p) : y = x := by
  cases h <;> first | rfl | simp [Val.asPtrWord] at hp

/-- A defined arm64 address is read off a value its refinements equal. -/
theorem addr_of_refines {y y' : Val} {k : BitVec 64} {p : Ptr} (h : Sem.Refines y y')
    (hp : Arm64.addr y k = some p) : y' = y := by
  cases h <;> first | rfl | simp [Arm64.addr, Arm64.reg] at hp

/-- A defined store address is read off a base its refinements equal. -/
theorem addrAt_of_refines {tabs : Tables} {act : Nat} {ax : Option AuxRef} {k : Int64}
    {y y' : Val} {p : Ptr} (h : Sem.Refines y y') (hp : addrAt tabs act ax k y = some p) :
    addrAt tabs act ax k y' = some p := by
  cases ax with
  | none => unfold addrAt at hp ⊢; rw [addr_of_refines h hp]; exact hp
  | some n => exact hp

/-- `ArgRel` is closed under refinement on the right. -/
theorem ArgRel.trans_right {tabs : Tables} {act : Nat} {o : Option (Int64 × Option AuxRef)}
    {x y y' : Val} (h : ArgRel tabs act o x y) (h2 : Sem.Refines y y') :
    ArgRel tabs act o x y' := by
  rcases o with _ | ⟨k, ax⟩
  · exact Sem.Refines.trans h h2
  · intro p hp
    exact addrAt_of_refines h2 (h p hp)

/-- `ArgRel` is closed under refinement on the left. -/
theorem ArgRel.trans_left {tabs : Tables} {act : Nat} {o : Option (Int64 × Option AuxRef)}
    {x x' y : Val} (h1 : Sem.Refines x x') (h : ArgRel tabs act o x' y) :
    ArgRel tabs act o x y := by
  rcases o with _ | ⟨k, ax⟩
  · exact Sem.Refines.trans h1 h
  · intro p hp
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

/-- A refinement is a store address at offset 0 without aux. -/
theorem addrRef_zero {tabs : Tables} {act : Nat} {x y : Val} (h : Sem.Refines x y) :
    AddrRef tabs act none 0 x y := by
  intro p hp
  unfold addrAt
  rw [asPtrWord_of_refines h hp, show BitVec.ofInt 64 (0 : Int64).toInt = 0 by decide]
  exact addr_of_asPtrWord hp

/-- The arguments of every atom listed in `g` refine, as terms, those of the atom of `f` it
corresponds to (`atomPair`: the same ID and fields, a renamed op, or a lowered store, whose address
is related by `AddrRef` at its offset, `stArg`; a bounds panic with constant operands reads the
kept ones, `argIx`, and its constants are `f`'s, `pbConstOK`), or, for a lowered call's register
piece, a `Phi`'s argument or a narrow store's value, refine fitted to the leaf it is read at
(`argFitTy`, `ArgTermFitL`), unless the atom of `g` reads no argument (`argFree`: a lowered frame
address); a `Store` lowered to an indexed store (`idxLower`) has its address given by the base and
the index (`ArgTermIdxL`), its value refined (or fitted, as above) and its memory refined; a `Move`
lowered to a 128-bit store (`moveQLower`) has its address related at the store's offset and aux,
its values refining the halves the `Move` copies (`ArgTermQL`) and its memory refined. A lowered
frame address where `f` has a term (`frameAtomG`) corresponds to no atom and reads no argument. -/
def AtomArgsRefL (tabs : Tables) (f g : Func) : Prop :=
  ∀ b ∈ g.blocks, ∀ gb, g.block? b = some gb → ∀ a ∈ gb.values, ∀ u, g.value? a = some u →
    termVL tabs u = false → frameAtomG tabs f a u = true ∨
    ∃ u', f.value? a = some u' ∧ atomPair tabs u' u = true ∧ pbConstOK tabs f u' u = true ∧
      (argFree tabs u = true ∨ (idxLower tabs u' u = false ∧ moveQLower tabs u' u = false ∧
        ∀ i < u.args.size, ArgTermRefL
        (stArg u' u i) f.lowered f.value? tabs u'.args[argIx u' u i]! g.lowered (listedDefs g) tabs
          u.args[i]! ∨
        ∃ t, argFitTy tabs u i = some t ∧ ArgTermFitL t
          f.lowered f.value? tabs u'.args[argIx u' u i]! g.lowered (listedDefs g) tabs u.args[i]!) ∨
        (idxLower tabs u' u = true ∧
          ArgTermIdxL (idxScale u.op) f.lowered f.value? tabs u'.args[0]! g.lowered (listedDefs g)
            tabs u.args[0]! u.args[1]! ∧
          (ArgTermRefL none f.lowered f.value? tabs u'.args[1]! g.lowered (listedDefs g) tabs
            u.args[2]! ∨
          ∃ t, argFitTy tabs u 2 = some t ∧ ArgTermFitL t f.lowered f.value? tabs u'.args[1]!
            g.lowered (listedDefs g) tabs u.args[2]!) ∧
          ArgTermRefL none f.lowered f.value? tabs u'.args[2]! g.lowered (listedDefs g) tabs
            u.args[3]!) ∨
        (moveQLower tabs u' u = true ∧
          ArgTermRefL (some (u.auxInt, u.aux)) f.lowered f.value? tabs u'.args[0]! g.lowered
            (listedDefs g) tabs u.args[0]! ∧
          (∀ i, i + 2 < u.args.size → ArgTermQL i f.lowered f.value? tabs u'.args[1]! u'.args[2]!
            g.lowered (listedDefs g) tabs u.args[i + 1]!) ∧
          ArgTermRefL none f.lowered f.value? tabs u'.args[2]! g.lowered (listedDefs g) tabs
            u.args[u.args.size - 1]!))

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

/-- The terminator of every block of `g`, as a function of its controls' terms over the atoms
(the frame addresses and the stack pointer those of activation 0, `FrameVals`, `FrameValsL`,
`SPVals`), refines that of `f`'s
block, and the successors of `f`'s block are successors of `g`'s. -/
def TermStepRefL (tabs : Tables) (f g : Func) : Prop :=
  ∀ b ∈ g.blocks, ∀ fb gb, f.block? b = some fb → g.block? b = some gb →
    (∀ e ∈ fb.succs, e ∈ gb.succs) ∧
    ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → TypedL f.lowered f.value? tabs ρ →
      TypedL g.lowered (listedDefs g) tabs ρ' → FrameVals tabs 0 f.value? ρ →
      SPVals tabs 0 f.value? ρ → FrameValsL tabs 0 (listedDefs g) ρ' →
      Res.Rel Next.Refines (stepValsL fb (fb.controls.toList.map (denL f.lowered f.value? tabs ρ n)))
        (stepValsL gb (gb.controls.toList.map (denL g.lowered (listedDefs g) tabs ρ' m)))

end GoFV.Proof.Low
