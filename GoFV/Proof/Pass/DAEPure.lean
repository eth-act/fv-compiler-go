import GoFV.Proof.Pass.DAEAvoid

/-!
# dead auto elim: the pure ops keep values avoiding frame temporaries

`evalPure_avoids`: every pure op (`evalPure`) on arguments that avoid a set `U` of frame
temporaries (`TempU`) has a result that avoids `U`. The pointer ops step a pointer inside its
own block or compute an integer word; the integer, boolean and float families give integers,
booleans and `poison`; selections and composites take their components from the arguments;
loads decode avoiding bytes (`load_avoids`); `GetG` and `WB` give pointers to blocks that are
not frame temporaries. One lemma per family of `Sem/Pure`, then one case per op (as
`evalPure_mono`).
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem

variable {U : Blk → Prop}

theorem count_avoids (rw : Option Width) (n : Nat) : Val.Avoids U (Int.count rw n) := by
  unfold Int.count; split <;> trivial

/-- Closes `Val.Avoids U v` for a `v` built from integers, booleans, `poison` and tuples or
composites of those, through `if`s and `match`es. -/
syntax "avoids_tac" : tactic
macro_rules
  | `(tactic| avoids_tac) =>
    `(tactic| repeat' (first | exact True.intro | exact count_avoids _ _ | split | refine ⟨?_, ?_⟩))

/-! ## Combinators -/

theorem int1_avoids {w : Width} {f : BitVec w.bits → Val} (hf : ∀ x, Val.Avoids U (f x))
    (args : List Val) : Val.Avoids U (int1 w f args) := by
  unfold int1
  split
  · split
    · exact hf _
    · trivial
  · trivial

theorem int2_avoids {w : Width} {f : BitVec w.bits → BitVec w.bits → Val}
    (hf : ∀ x y, Val.Avoids U (f x y)) (args : List Val) : Val.Avoids U (int2 w f args) := by
  unfold int2
  split
  · split
    · exact hf _ _
    · trivial
  · trivial

theorem int3_avoids {w : Width} {f : BitVec w.bits → BitVec w.bits → BitVec w.bits → Val}
    (hf : ∀ x y z, Val.Avoids U (f x y z)) (args : List Val) : Val.Avoids U (int3 w f args) := by
  unfold int3
  split
  · split
    · exact hf _ _ _
    · trivial
  · trivial

theorem shift_avoids (w a : Width) (b : Bool) (f : BitVec w.bits → Nat → BitVec w.bits)
    (args : List Val) : Val.Avoids U (Shift.shift w a b f args) := by
  unfold Shift.shift; avoids_tac

theorem rotateLeft_avoids (w : Width) (args : List Val) : Val.Avoids U (Int.rotateLeft w args) := by
  unfold Int.rotateLeft; avoids_tac

theorem bool1_avoids (f : Bool → Bool) (args : List Val) : Val.Avoids U (bool1 f args) := by
  unfold bool1; avoids_tac

theorem bool2_avoids (f : Bool → Bool → Bool) (args : List Val) : Val.Avoids U (bool2 f args) := by
  unfold bool2; avoids_tac

theorem andB_avoids (args : List Val) : Val.Avoids U (Cmp.andB args) := by
  unfold Cmp.andB; avoids_tac

theorem orB_avoids (args : List Val) : Val.Avoids U (Cmp.orB args) := by
  unfold Cmp.orB; avoids_tac

theorem inBounds_avoids (sl : Bool) (args : List Val) : Val.Avoids U (Cmp.inBounds sl args) := by
  unfold Cmp.inBounds; avoids_tac

theorem spectreIndex_avoids (sl : Bool) (args : List Val) :
    Val.Avoids U (Cmp.spectreIndex sl args) := by
  unfold Cmp.spectreIndex; avoids_tac

theorem slicemask_avoids (o : Option Width) (args : List Val) :
    Val.Avoids U (match o with | some w => Int.slicemask w args | none => .poison) := by
  cases o with
  | none => trivial
  | some w => exact int1_avoids (fun _ => by avoids_tac) _

theorem boolToUint8_avoids (args : List Val) : Val.Avoids U (Conv.boolToUint8 args) := by
  unfold Conv.boolToUint8; avoids_tac

/-! ## Selections and composites -/

theorem getD_avoids {vs : List Val} (h : Val.AvoidsList U vs) (i : Nat) :
    Val.Avoids U (vs.getD i .poison) := by
  rw [avoidsList_iff] at h
  cases hi : vs[i]? with
  | none => simp [List.getD, hi]; trivial
  | some z => simp [List.getD, hi]; exact h z (List.mem_of_getElem? hi)

theorem tuple_avoids {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (.tuple args) :=
  avoidsList_iff.2 h

theorem agg_avoids {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (.agg args) :=
  avoidsList_iff.2 h

theorem select_avoids (i : Nat) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Tuple.select i args) := by
  unfold Tuple.select
  split
  · exact getD_avoids (h _ List.mem_cons_self) i
  · trivial

theorem selectN_avoids (k : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Tuple.selectN k args) := by
  unfold Tuple.selectN
  split
  · split
    · trivial
    · exact getD_avoids (h _ List.mem_cons_self) _
  · trivial

theorem selectNAddr_avoids (k : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Tuple.selectNAddr k args) := by
  unfold Tuple.selectNAddr
  split
  · rename_i vs
    have hvs : ∀ z ∈ vs, Val.Avoids U z := avoidsList_iff.1 (h _ List.mem_cons_self)
    split
    · rename_i addrs ha
      have hA : ∀ z ∈ addrs, Val.Avoids U z :=
        avoidsList_iff.1 (hvs _ (List.mem_of_getLast? ha))
      split
      · trivial
      · split
        · rename_i p hp
          exact word_avoids (hA _ (List.mem_of_getElem? hp))
        · trivial
    · trivial
  · trivial

theorem tupleMake_avoids {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Tuple.make args) := by
  unfold Tuple.make
  split
  · exact avoidsList_iff.2 h
  · trivial

theorem compSelect_avoids (i : Nat) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Comp.select i args) := by
  unfold Comp.select
  split
  · exact getD_avoids (h _ List.mem_cons_self) i
  · trivial

theorem selectAux_avoids (k : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Comp.selectAux k args) := by
  unfold Comp.selectAux
  split
  · trivial
  · exact compSelect_avoids _ h

theorem condSelect_avoids {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Cmp.condSelect args) := by
  unfold Cmp.condSelect
  split
  · split
    · exact h _ List.mem_cons_self
    · exact h _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · trivial
  · trivial

/-! ## Pointers and memory -/

theorem ptrRes_avoids {p : Ptr} (h : ¬ U p.blk) : Val.Avoids U (PtrOps.ptrRes p) := by
  unfold PtrOps.ptrRes; split
  · exact word_avoids h
  · trivial

theorem wordRes_avoids (x k : BitVec 64) : Val.Avoids U (PtrOps.wordRes x k) := by
  unfold PtrOps.wordRes; split <;> trivial

theorem offPtr_avoids (k : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (PtrOps.offPtr k args) := by
  unfold PtrOps.offPtr
  split
  · exact ptrRes_avoids (h _ List.mem_cons_self)
  · exact wordRes_avoids _ _
  · trivial

theorem addPtr_avoids {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (PtrOps.addPtr args) := by
  unfold PtrOps.addPtr
  split
  · split
    · exact ptrRes_avoids (h _ List.mem_cons_self)
    · trivial
  · split
    · exact wordRes_avoids _ _
    · trivial
  · trivial

theorem ptrIndex_avoids (e : Option Nat) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (PtrOps.ptrIndex e args) := by
  unfold PtrOps.ptrIndex
  split
  · split
    · exact ptrRes_avoids (h _ List.mem_cons_self)
    · trivial
  · split
    · exact wordRes_avoids _ _
    · trivial
  · trivial

theorem subPtr_avoids (args : List Val) : Val.Avoids U (PtrOps.subPtr args) := by
  unfold PtrOps.subPtr; avoids_tac

theorem eqPtr_avoids (neg : Bool) (args : List Val) : Val.Avoids U (PtrOps.eqPtr neg args) := by
  unfold PtrOps.eqPtr; avoids_tac

theorem isNonNil_avoids (args : List Val) : Val.Avoids U (PtrOps.isNonNil args) := by
  unfold PtrOps.isNonNil; avoids_tac

theorem eqFirst_avoids (neg : Bool) (args : List Val) :
    Val.Avoids U (PtrOps.eqFirst neg args) := by
  unfold PtrOps.eqFirst; avoids_tac

theorem convert_avoids (t : Ty) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (PtrOps.convert t args) := by
  unfold PtrOps.convert
  split
  · split
    · split <;> trivial
    · exact h _ List.mem_cons_self
  · trivial

theorem loadOp_avoids (hU : TempU U) (t : Ty) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (loadOp t args) := by
  unfold loadOp
  split
  · split
    · rename_i hp
      exact load_avoids hU (h _ (List.mem_cons_of_mem _ List.mem_cons_self)) t
        (asPtrWord_notU hU (h _ List.mem_cons_self) hp)
    · trivial
  · trivial

theorem atomicLoad_avoids (hU : TempU U) (t : Ty) {args : List Val}
    (h : ∀ z ∈ args, Val.Avoids U z) : Val.Avoids U (atomicLoad t args) := by
  unfold atomicLoad
  split
  · rename_i a m
    have hm : m.Avoids U := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
    split
    · rename_i hp
      refine ⟨?_, hm, trivial⟩
      split
      · trivial
      · exact load_avoids hU hm _ (asPtrWord_notU hU (h _ List.mem_cons_self) hp)
    · trivial
  · trivial

theorem memEq_avoids (args : List Val) : Val.Avoids U (memEq args) := by
  unfold memEq; avoids_tac

theorem wbOp_avoids (hU : TempU U) (n : Int64) {args : List Val}
    (h : ∀ z ∈ args, Val.Avoids U z) : Val.Avoids U (wbOp n args) := by
  unfold wbOp
  split
  · refine ⟨fun hu => ?_, memAvoids_set (h _ List.mem_cons_self)
      (fun _ => bav_replicate_poison _ _), trivial⟩
    obtain ⟨_, _, hb⟩ := hU _ hu; cases hb
  · trivial

/-! ## `evalPure` -/

/-- **Every pure op keeps values avoiding frame temporaries**: on arguments that avoid `U`
(`U` holds only frame temporaries), its result avoids `U`. -/
theorem evalPure_avoids (hU : TempU U) (op : Op) (ty : Ty) (k : Int64) (aux : Option AuxRef)
    {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (evalPure op ty k aux args) := by
  cases op
  case Add8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Sub8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mul8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case And8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Or8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Xor8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neg8 => exact int1_avoids (fun _ => by avoids_tac) _
  case Com8 => exact int1_avoids (fun _ => by avoids_tac) _
  case Add16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Sub16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mul16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case And16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Or16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Xor16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neg16 => exact int1_avoids (fun _ => by avoids_tac) _
  case Com16 => exact int1_avoids (fun _ => by avoids_tac) _
  case Add32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Sub32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mul32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case And32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Or32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Xor32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neg32 => exact int1_avoids (fun _ => by avoids_tac) _
  case Com32 => exact int1_avoids (fun _ => by avoids_tac) _
  case Add64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Sub64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mul64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case And64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Or64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Xor64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neg64 => exact int1_avoids (fun _ => by avoids_tac) _
  case Com64 => exact int1_avoids (fun _ => by avoids_tac) _
  case Hmul32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Hmul32u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mul32uhilo => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mul32uover => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Hmul64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Hmul64u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mul64uhilo => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mul64uover => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Avg64u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div8u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mod8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mod8u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div16u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mod16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mod16u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div32u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mod32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mod32u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div64u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mod64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mod64u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div128u => exact int3_avoids (fun _ _ _ => by avoids_tac) _
  case Lsh8x8 => exact shift_avoids _ _ _ _ _
  case Rsh8x8 => exact shift_avoids _ _ _ _ _
  case Rsh8Ux8 => exact shift_avoids _ _ _ _ _
  case Lsh8x16 => exact shift_avoids _ _ _ _ _
  case Rsh8x16 => exact shift_avoids _ _ _ _ _
  case Rsh8Ux16 => exact shift_avoids _ _ _ _ _
  case Lsh8x32 => exact shift_avoids _ _ _ _ _
  case Rsh8x32 => exact shift_avoids _ _ _ _ _
  case Rsh8Ux32 => exact shift_avoids _ _ _ _ _
  case Lsh8x64 => exact shift_avoids _ _ _ _ _
  case Rsh8x64 => exact shift_avoids _ _ _ _ _
  case Rsh8Ux64 => exact shift_avoids _ _ _ _ _
  case Lsh16x8 => exact shift_avoids _ _ _ _ _
  case Rsh16x8 => exact shift_avoids _ _ _ _ _
  case Rsh16Ux8 => exact shift_avoids _ _ _ _ _
  case Lsh16x16 => exact shift_avoids _ _ _ _ _
  case Rsh16x16 => exact shift_avoids _ _ _ _ _
  case Rsh16Ux16 => exact shift_avoids _ _ _ _ _
  case Lsh16x32 => exact shift_avoids _ _ _ _ _
  case Rsh16x32 => exact shift_avoids _ _ _ _ _
  case Rsh16Ux32 => exact shift_avoids _ _ _ _ _
  case Lsh16x64 => exact shift_avoids _ _ _ _ _
  case Rsh16x64 => exact shift_avoids _ _ _ _ _
  case Rsh16Ux64 => exact shift_avoids _ _ _ _ _
  case Lsh32x8 => exact shift_avoids _ _ _ _ _
  case Rsh32x8 => exact shift_avoids _ _ _ _ _
  case Rsh32Ux8 => exact shift_avoids _ _ _ _ _
  case Lsh32x16 => exact shift_avoids _ _ _ _ _
  case Rsh32x16 => exact shift_avoids _ _ _ _ _
  case Rsh32Ux16 => exact shift_avoids _ _ _ _ _
  case Lsh32x32 => exact shift_avoids _ _ _ _ _
  case Rsh32x32 => exact shift_avoids _ _ _ _ _
  case Rsh32Ux32 => exact shift_avoids _ _ _ _ _
  case Lsh32x64 => exact shift_avoids _ _ _ _ _
  case Rsh32x64 => exact shift_avoids _ _ _ _ _
  case Rsh32Ux64 => exact shift_avoids _ _ _ _ _
  case Lsh64x8 => exact shift_avoids _ _ _ _ _
  case Rsh64x8 => exact shift_avoids _ _ _ _ _
  case Rsh64Ux8 => exact shift_avoids _ _ _ _ _
  case Lsh64x16 => exact shift_avoids _ _ _ _ _
  case Rsh64x16 => exact shift_avoids _ _ _ _ _
  case Rsh64Ux16 => exact shift_avoids _ _ _ _ _
  case Lsh64x32 => exact shift_avoids _ _ _ _ _
  case Rsh64x32 => exact shift_avoids _ _ _ _ _
  case Rsh64Ux32 => exact shift_avoids _ _ _ _ _
  case Lsh64x64 => exact shift_avoids _ _ _ _ _
  case Rsh64x64 => exact shift_avoids _ _ _ _ _
  case Rsh64Ux64 => exact shift_avoids _ _ _ _ _
  case Eq8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neq8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Less8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Less8U => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Leq8 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Leq8U => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Eq16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neq16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Less16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Less16U => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Leq16 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Leq16U => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Eq32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neq32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Less32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Less32U => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Leq32 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Leq32U => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Eq64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neq64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Less64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Less64U => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Leq64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Leq64U => exact int2_avoids (fun _ _ => by avoids_tac) _
  case AndB => exact andB_avoids _
  case OrB => exact orB_avoids _
  case EqB => exact bool2_avoids _ _
  case NeqB => exact bool2_avoids _ _
  case Not => exact bool1_avoids _ _
  case CondSelect => exact condSelect_avoids h
  case IsInBounds => exact inBounds_avoids _ _
  case IsSliceInBounds => exact inBounds_avoids _ _
  case SpectreIndex => exact spectreIndex_avoids _ _
  case SpectreSliceIndex => exact spectreIndex_avoids _ _
  case Ctz8 => exact int1_avoids (fun _ => by avoids_tac) _
  case Ctz8NonZero => exact int1_avoids (fun _ => by avoids_tac) _
  case BitLen8 => exact int1_avoids (fun _ => by avoids_tac) _
  case PopCount8 => exact int1_avoids (fun _ => by avoids_tac) _
  case BitRev8 => exact int1_avoids (fun _ => by avoids_tac) _
  case RotateLeft8 => exact rotateLeft_avoids _ _
  case Ctz16 => exact int1_avoids (fun _ => by avoids_tac) _
  case Ctz16NonZero => exact int1_avoids (fun _ => by avoids_tac) _
  case BitLen16 => exact int1_avoids (fun _ => by avoids_tac) _
  case PopCount16 => exact int1_avoids (fun _ => by avoids_tac) _
  case BitRev16 => exact int1_avoids (fun _ => by avoids_tac) _
  case RotateLeft16 => exact rotateLeft_avoids _ _
  case Bswap16 => exact int1_avoids (fun _ => by avoids_tac) _
  case Ctz32 => exact int1_avoids (fun _ => by avoids_tac) _
  case Ctz32NonZero => exact int1_avoids (fun _ => by avoids_tac) _
  case BitLen32 => exact int1_avoids (fun _ => by avoids_tac) _
  case PopCount32 => exact int1_avoids (fun _ => by avoids_tac) _
  case BitRev32 => exact int1_avoids (fun _ => by avoids_tac) _
  case RotateLeft32 => exact rotateLeft_avoids _ _
  case Bswap32 => exact int1_avoids (fun _ => by avoids_tac) _
  case Ctz64 => exact int1_avoids (fun _ => by avoids_tac) _
  case Ctz64NonZero => exact int1_avoids (fun _ => by avoids_tac) _
  case BitLen64 => exact int1_avoids (fun _ => by avoids_tac) _
  case PopCount64 => exact int1_avoids (fun _ => by avoids_tac) _
  case BitRev64 => exact int1_avoids (fun _ => by avoids_tac) _
  case RotateLeft64 => exact rotateLeft_avoids _ _
  case Bswap64 => exact int1_avoids (fun _ => by avoids_tac) _
  case Min64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Min64u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Max64 => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Max64u => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Add64carry => exact int3_avoids (fun _ _ _ => by avoids_tac) _
  case Sub64borrow => exact int3_avoids (fun _ _ _ => by avoids_tac) _
  case Slicemask => exact slicemask_avoids _ _
  case SignExt8to16 => exact int1_avoids (fun _ => by avoids_tac) _
  case ZeroExt8to16 => exact int1_avoids (fun _ => by avoids_tac) _
  case SignExt8to32 => exact int1_avoids (fun _ => by avoids_tac) _
  case ZeroExt8to32 => exact int1_avoids (fun _ => by avoids_tac) _
  case SignExt8to64 => exact int1_avoids (fun _ => by avoids_tac) _
  case ZeroExt8to64 => exact int1_avoids (fun _ => by avoids_tac) _
  case SignExt16to32 => exact int1_avoids (fun _ => by avoids_tac) _
  case ZeroExt16to32 => exact int1_avoids (fun _ => by avoids_tac) _
  case SignExt16to64 => exact int1_avoids (fun _ => by avoids_tac) _
  case ZeroExt16to64 => exact int1_avoids (fun _ => by avoids_tac) _
  case SignExt32to64 => exact int1_avoids (fun _ => by avoids_tac) _
  case ZeroExt32to64 => exact int1_avoids (fun _ => by avoids_tac) _
  case Trunc16to8 => exact int1_avoids (fun _ => by avoids_tac) _
  case Trunc32to8 => exact int1_avoids (fun _ => by avoids_tac) _
  case Trunc32to16 => exact int1_avoids (fun _ => by avoids_tac) _
  case Trunc64to8 => exact int1_avoids (fun _ => by avoids_tac) _
  case Trunc64to16 => exact int1_avoids (fun _ => by avoids_tac) _
  case Trunc64to32 => exact int1_avoids (fun _ => by avoids_tac) _
  case CvtBoolToUint8 => exact boolToUint8_avoids _
  case Const8 => exact True.intro
  case Const16 => exact True.intro
  case Const32 => exact True.intro
  case Const64 => exact True.intro
  case ConstBool => exact True.intro
  case Select0 => exact select_avoids _ h
  case SelectN => exact selectN_avoids _ h
  case SelectNAddr => exact selectNAddr_avoids _ h
  case Select1 => exact select_avoids _ h
  case MakeTuple => exact tupleMake_avoids h
  case Copy =>
    rcases args with _ | ⟨x, _ | ⟨y, t⟩⟩
    · exact True.intro
    · exact h x List.mem_cons_self
    · exact True.intro
  case MakeResult => exact tuple_avoids h
  case OffPtr => exact offPtr_avoids _ h
  case AddPtr => exact addPtr_avoids h
  case PtrIndex => exact ptrIndex_avoids _ h
  case SubPtr => exact subPtr_avoids _
  case EqPtr => exact eqPtr_avoids _ _
  case NeqPtr => exact eqPtr_avoids _ _
  case IsNonNil => exact isNonNil_avoids _
  case Convert => exact convert_avoids _ h
  case EqInter => exact eqFirst_avoids _ _
  case NeqInter => exact eqFirst_avoids _ _
  case EqSlice => exact eqFirst_avoids _ _
  case NeqSlice => exact eqFirst_avoids _ _
  case StringMake => exact agg_avoids h
  case SliceMake => exact agg_avoids h
  case IMake => exact agg_avoids h
  case ComplexMake => exact agg_avoids h
  case StructMake => exact agg_avoids h
  case ArrayMake1 => exact agg_avoids h
  case StringPtr => exact compSelect_avoids _ h
  case SlicePtr => exact compSelect_avoids _ h
  case SlicePtrUnchecked => exact compSelect_avoids _ h
  case ITab => exact compSelect_avoids _ h
  case ComplexReal => exact compSelect_avoids _ h
  case StringLen => exact compSelect_avoids _ h
  case SliceLen => exact compSelect_avoids _ h
  case IData => exact compSelect_avoids _ h
  case ComplexImag => exact compSelect_avoids _ h
  case SliceCap => exact compSelect_avoids _ h
  case StructSelect => exact selectAux_avoids _ h
  case ArraySelect => exact selectAux_avoids _ h
  case ConstNil => exact True.intro
  case ConstSlice => exact ⟨trivial, trivial, trivial, trivial⟩
  case ConstInterface => exact ⟨trivial, trivial, trivial⟩
  case Empty => exact True.intro
  case HasCPUFeature => exact True.intro
  case GetG => exact fun hu => by obtain ⟨_, _, hb⟩ := hU _ hu; cases hb
  case Load => exact loadOp_avoids hU _ h
  case Dereference => exact loadOp_avoids hU _ h
  case MemEq => exact memEq_avoids _
  case AtomicLoadAcq64 => exact atomicLoad_avoids hU _ h
  case WB => exact wbOp_avoids hU _ h
  case AtomicLoad8 => exact atomicLoad_avoids hU _ h
  case AtomicLoad32 => exact atomicLoad_avoids hU _ h
  case AtomicLoad64 => exact atomicLoad_avoids hU _ h
  case AtomicLoadPtr => exact atomicLoad_avoids hU _ h
  case AtomicLoadAcq32 => exact atomicLoad_avoids hU _ h
  case Add32F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Add64F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Sub32F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Sub64F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mul32F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Mul64F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div32F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Div64F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Eq32F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Eq64F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neq32F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neq64F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Less32F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Less64F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Leq32F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Leq64F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Min32F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Min64F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Max32F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Max64F => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Copysign => exact int2_avoids (fun _ _ => by avoids_tac) _
  case Neg32F => exact int1_avoids (fun _ => by avoids_tac) _
  case Neg64F => exact int1_avoids (fun _ => by avoids_tac) _
  case Sqrt => exact int1_avoids (fun _ => by avoids_tac) _
  case Sqrt32 => exact int1_avoids (fun _ => by avoids_tac) _
  case Floor => exact int1_avoids (fun _ => by avoids_tac) _
  case Ceil => exact int1_avoids (fun _ => by avoids_tac) _
  case Trunc => exact int1_avoids (fun _ => by avoids_tac) _
  case Round => exact int1_avoids (fun _ => by avoids_tac) _
  case RoundToEven => exact int1_avoids (fun _ => by avoids_tac) _
  case Abs => exact int1_avoids (fun _ => by avoids_tac) _
  case Round32F => exact int1_avoids (fun _ => by avoids_tac) _
  case Round64F => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt32to32F => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt32to64F => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt64to32F => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt64to64F => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt32Uto32F => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt32Uto64F => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt64Uto32F => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt64Uto64F => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt32Fto32 => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt32Fto64 => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt64Fto32 => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt64Fto64 => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt32Fto32U => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt32Fto64U => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt64Fto32U => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt64Fto64U => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt32Fto64F => exact int1_avoids (fun _ => by avoids_tac) _
  case Cvt64Fto32F => exact int1_avoids (fun _ => by avoids_tac) _
  case FMA => exact int3_avoids (fun _ _ _ => by avoids_tac) _
  case Const32F => exact True.intro
  case Const64F => exact True.intro
  all_goals exact True.intro

end GoFV.Proof.DAE
