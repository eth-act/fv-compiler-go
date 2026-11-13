import GoFV.Proof.Rules.DenT
import GoFV.Proof.Rules.Dec
import GoFV.Proof.Rules.Lemmas
import GoFV.Proof.Rules.NonVacuous
import GoFV.Proof.Rules.Names
import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Retype
import GoFV.Rules.Generated.Generic.Values02
import GoFV.Rules.Generated.Generic.Values12

/-!
# Rule lemmas: constant strings and string data symbols (`generic.rules:1011`, `:1015`, `:1022`)

`(ConstString {str}) && config.PtrSize == 8 && str != "" => (StringMake (Addr <typ.BytePtr>
{fe.StringData(str)} (SB)) (Const64 <typ.Int> [int64(len(str))]))` under `Rule.SoundT`
(`DenT.lean`): the constant string is `strVal` of its aux (the data symbol's global and the
length), the result's `Addr` is `addrVal` of the aux `fe.StringData(str)`. `FrameOK`, which the
rewrite validator checks on the instance, says that this aux names the string's data symbol
and that the `Const64`'s auxint is the string's length (issue #151).

`:1015` (`str == ""`: `StringMake (ConstNil) (Const64 [0])`): `FrameOK` says that the aux bound
to `str` is the empty string, whose `strVal` is the nil pointer and length 0. `:1011`
(`(StringPtr (StringMake (Addr <t> {s} base) _)) => (Addr <t> {s} base)`): `FrameOK` says that the
rebuilt `Addr`'s aux is the matched one, so it is the matched `Addr`'s value, which the selection
of the `StringMake` gives back (`sel_make2`; issue #69).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

section

variable [GoFV.SSA.Sem.Addrs]

theorem strVal_of_strAux {tabs : Tables} {a : Option AuxRef} {s d : GoStr}
    (h : strAux? tabs a = some (s, d)) (hs : s.size ≠ 0) :
    strVal tabs a =
      Val.ofStr [.ptr ⟨.global d.toStringLossy, 0⟩, .int .w64 (BitVec.ofNat 64 s.size)] := by
  unfold strAux? at h
  unfold strVal
  split at h
  · rename_i heq
    cases h
    simp [heq, hs]
  · cases h

theorem addrVal_of_symName {tabs : Tables} {a : Option AuxRef} {d : GoStr}
    (h : symName? tabs a = some d) : addrVal tabs a = .ptr ⟨.global d.toStringLossy, 0⟩ := by
  unfold symName? at h
  unfold addrVal
  split at h
  · rename_i heq
    cases h
    simp [heq]
  · cases h

/-- `generic.rules:1022`: `(ConstString {str}) && config.PtrSize == 8 && str != "" => (StringMake (Addr <typ.BytePtr> {fe.StringData(str)} (SB)) (Const64 <typ.Int> [int64(len(str))]))` -/
theorem r_generic_1022_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_1022 := by
  refine ⟨rfl, fun tabs e or _ => ?_⟩
  intro σ ev hfr _ _ _ hty _ _
  have hn := hfr.1
  obtain ⟨p, s, d, hp, hs, hsz, hsym⟩ :=
    (hn _ (List.mem_cons_of_mem _ List.mem_cons_self)).1 _ 0 rfl rfl
  obtain ⟨p', s', d', hp', hs', hlen⟩ :=
    (hn _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))).2.1 _ 0 rfl rfl
  simp only [GoFV.Rules.Generated.Generic.r_generic_1022, Pat.auxPos, Field.bindsVar,
    beq_self_eq_true, ite_true, Option.some.injEq] at hp hp'
  subst hp hp'
  rw [hs, Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl⟩ := hs'
  clear hfr hn
  simp only [GoFV.Rules.Generated.Generic.r_generic_1022, Pat.rawT, Pat.densT, opVal_constString,
    strVal_of_strAux hs hsz] at hty ⊢
  simp only [resDenT, nodeDenT, List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.map_cons, List.map_nil, opVal_addr, addrVal_of_symName hsym]
  have hb : ev (.field (.rsv .typ) "BytePtr" (.named "*types.Type")) = .ty (.ptr (some 1)) := by
    dsimp only [ev, evalE, fieldE]; simp only [rule_helper, Option.map_some, Option.getD_some]
  have hi : ev (.field (.rsv .typ) "Int" (.named "*types.Type")) = .ty (.int .w64) := by
    dsimp only [ev, evalE, fieldE]; simp only [rule_helper, Option.map_some, Option.getD_some]
  rw [hlen, hb, hi]
  simp only [opVal, reduceCtorEq, ite_false, reduceEvalPure]
  have hc : Conv.const .w64 (Int64.ofNat s.size) = .int .w64 (BitVec.ofNat 64 s.size) := by
    simp only [Conv.const, Width.bits, Int64.toInt, BitVec.ofInt_toInt]; rfl
  simp only [hc, Comp.make, Val.retype, Nat.le_refl, ite_true, BitVec.setWidth_eq, Ptr.word,
    Ptr.convertible_global, Ptr.addr?, Blk.base?_global, Ptr.inWindow, Blk.window?]
  unfold Val.ofStr at hty ⊢
  split
  · rename_i hok
    rw [if_pos hok] at hty
    rw [Val.retype_of_hasTy hty]
    exact fun _ => Refines.refl _
  · exact fun _ => .poison _

theorem strVal_of_strAux_empty {tabs : Tables} {a : Option AuxRef} {s d : GoStr}
    (h : strAux? tabs a = some (s, d)) (hs : s.size = 0) :
    strVal tabs a = .agg [.int .w64 0, .int .w64 (BitVec.ofNat 64 0)] := by
  unfold strAux? at h
  unfold strVal
  split at h
  · rename_i heq
    cases h
    simp [heq, hs, Val.ofStr, Val.strOK]
  · cases h

/-- `generic.rules:1015`: `(ConstString {str}) && config.PtrSize == 8 && str == "" => (StringMake (ConstNil) (Const64 <typ.Int> [0]))` -/
theorem r_generic_1015_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_1015 := by
  refine ⟨rfl, fun tabs e or _ => ?_⟩
  intro σ ev hfr _ _ _ hty _ _
  obtain ⟨p, s, d, hp, hs, hsz⟩ := hfr.2.1 0
    (by simp [GoFV.Rules.Generated.Generic.r_generic_1015, emptyStrVars])
  simp only [GoFV.Rules.Generated.Generic.r_generic_1015, Pat.auxPos, Field.bindsVar,
    beq_self_eq_true, ite_true, Option.some.injEq] at hp
  subst hp
  clear hfr
  simp only [GoFV.Rules.Generated.Generic.r_generic_1015, Pat.rawT, Pat.densT, opVal_constString,
    strVal_of_strAux_empty hs hsz] at hty ⊢
  simp only [resDenT, nodeDenT, List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.map_cons, List.map_nil]
  have hb : ev (.field (.rsv .typ) "BytePtr" (.named "*types.Type")) = .ty (.ptr (some 1)) := by
    dsimp only [ev, evalE, fieldE]; simp only [rule_helper, Option.map_some, Option.getD_some]
  have hi : ev (.field (.rsv .typ) "Int" (.named "*types.Type")) = .ty (.int .w64) := by
    dsimp only [ev, evalE, fieldE]; simp only [rule_helper, Option.map_some, Option.getD_some]
  have h0 : ev (.lit .int64 (.int 0)) = .int 0 := rfl
  rw [hb, hi, h0]
  simp only [opVal, reduceCtorEq, ite_false, reduceEvalPure]
  simp only [Conv.const, Comp.make, Val.retype, Nat.le_refl, ite_true, BitVec.setWidth_eq]
  show _ → Refines _ (Val.retype (e.ty []) (.agg [.int .w64 0, .int .w64 (BitVec.ofNat 64 0)]))
  rw [Val.retype_of_hasTy hty]
  exact fun _ => Refines.refl _

/-- `generic.rules:1011`: `(StringPtr (StringMake (Addr <t> {s} base) _)) => (Addr <t> {s} base)` -/
theorem r_generic_1011_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_1011 := by
  refine ⟨rfl, fun tabs e or _ => ?_⟩
  intro σ ev hfr _ _ _ _ hlt hat _
  obtain ⟨p, hp, hax⟩ := (hfr.1 _ List.mem_cons_self).2.2.1 _ 1 rfl rfl
  simp [GoFV.Rules.Generated.Generic.r_generic_1011, Pat.auxPos, Pat.auxPoss,
    Field.bindsVar] at hp
  subst hp
  clear hfr
  have ht : ev (.var 0) = .ty (e.ty [0, 0]) := by
    simp [ev, σ, evalE, sigmaT, GoFV.Rules.Generated.Generic.r_generic_1011, Pat.bindsT,
      Pat.bindssT]
  simp only [GoFV.Rules.Generated.Generic.r_generic_1011, Pat.rawT, Pat.densT, Pat.denT, Pat.typed,
    Pat.typeds, Pat.argsOK, Pat.argsOKs, reduceArgShapeOk, Bool.and_eq_true] at hlt hat ⊢
  simp only [resDenT, nodeDenT, List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.map_cons, List.map_nil, ht, hax, opVal_addr]
  simp only [opVal, reduceCtorEq, ite_false, ite_true, reduceEvalPure]
  exact sel_make2 (Val.retype_hasTy _ _) hlt.1.2.1 hat.1.2.1.1 hat.1.2.2.1.1 0

/-! ## Non-vacuity (`rule-sat` draws no tables) -/

/-- `tabs`, `e`, `or` instantiate `r` under `Rule.SoundT`: every hypothesis holds and the
matched value is not `poison` (`Rule.Inst` with the tables). -/
def Rule.InstT (r : Rule) (tabs : Tables) (e : PEnv) (or : Oracle) : Prop :=
  Oracle.BoolTyped or ∧
  let σ := sigmaT tabs e r.pat
  let ev := evalE (r.vars.map (·.ty)) σ or e (Pat.denT tabs e [] r.pat)
  FrameOK tabs e ev or r ∧ Pat.wf e [] r.pat ∧ Pat.cons ev σ e [] r.pat ∧ condHolds ev r.cond ∧
  (Pat.rawT tabs e r.pat).hasTy (e.ty []) = true ∧ Pat.typed e [] r.pat ∧
  Pat.argsOK e.ty [] r.pat = true ∧ Pat.nonNegOK e r.pat r.cond = true ∧
  Pat.rawT tabs e r.pat ≠ .poison

/-- The string shape. -/
def strTy : Ty := .str

end

open scoped GoFV.SSA.Sem.Fixed

/-- Aux 1: the empty string constant. -/
def emptyStrTabs : Tables where
  auxes := #[none,
    some { fmt := GoStr.ofString "empty"
           kind := .str (GoStr.ofString "") (GoStr.ofString "go:string.empty") }]

/-- `generic.rules:1015` at `ConstString {""}`. -/
theorem inst_r_generic_1015 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_1015 emptyStrTabs
    { leaf := fun _ => .poison, ty := fun _ => strTy, auxInt := fun _ => 0, aux := fun _ => some 1 }
    (Oracle.const true) := by
  refine ⟨Oracle.const_boolTyped true, ?_⟩
  simp [GoFV.Rules.Generated.Generic.r_generic_1015, FrameOK, Result.nodes, emptyStrVars, sameLeaves,
    nonNegLeaves, nonNegAuxs,
    samePtrVars, numElem1Vars, size0Vars, shiftAmt?, Pat.auxPos, Field.bindsVar, strAux?,
    emptyStrTabs, Tables.aux?, Pat.rawT, Pat.densT, opVal_constString, strVal, sigmaT,
    Pat.bindsT, Pat.bindssT, Pat.denT, Val.ofStr, Val.strOK]
  rule_eval
  refine ⟨⟨fun ae x h => ?_, fun ae b h => ?_⟩, ?_⟩
  · subst h; simp [lenVar?]
  · subst h; simp
  · simp [sigmaT, Pat.bindsT, Pat.bindssT, strTy]

/-- Aux 1: the symbol `go:string.hi`. -/
def hiSymTabs : Tables where
  auxes := #[none,
    some { fmt := GoStr.ofString "go:string.hi"
           kind := .sym (GoStr.ofString "go:string.hi") 0 "" 0 default none none none #[] none }]

/-- `generic.rules:1011` at `StringPtr (StringMake (Addr {go:string.hi} SB) 2)`. -/
theorem inst_r_generic_1011 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_1011 hiSymTabs
    { leaf := fun p => if p = [1, 0] then .int .w64 2 else .poison
      ty := fun p => if p = [0] then strTy else if p = [1, 0] then .int .w64 else .ptr (some 1)
      auxInt := fun _ => 0, aux := fun _ => some 1 }
    { Oracle.const true with aux := fun _ => some 1 } := by
  refine ⟨Oracle.boolTyped_const_dv true _ _ _ _, ?_⟩
  simp [GoFV.Rules.Generated.Generic.r_generic_1011, FrameOK, Result.nodes, strDataVar?, lenVar?,
    sameLeaves, nonNegLeaves, shiftAmt?, auxVar?, numElem1Vars, size0Vars, Pat.auxPos,
    Pat.auxPoss, nonNegAuxs,
    Field.bindsVar, hiSymTabs, Tables.aux?, Pat.rawT, Pat.densT, Pat.denT, opVal, addrVal, sigmaT,
    Pat.bindsT, Pat.bindssT, strTy]
  rule_eval
  have h2 : (2#64).msb = false := by decide
  simp [Comp.select, Comp.make, Val.retype, Val.retypeFields, Val.ofStr, Val.strOK, Val.retypePtr,
    Val.retypeI64, h2, Ptr.word, Ptr.convertible_global, Ptr.addr?, Blk.base?_global,
    Ptr.inWindow, Blk.window?]
  exact ⟨fun xe x h => by subst h; simp [strDataVar?], fun xe x h => by subst h; simp [auxVar?]⟩

end GoFV.Proof.Rules
