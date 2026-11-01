import GoFV.Proof.Rules.DenT
import GoFV.Proof.Rules.Lemmas
import GoFV.Proof.Rules.Names
import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Retype
import GoFV.Rules.Generated.Generic.Values02

/-!
# Rule lemma: constant strings (`generic.rules:1022`, issue #151)

`(ConstString {str}) && config.PtrSize == 8 && str != "" => (StringMake (Addr <typ.BytePtr>
{fe.StringData(str)} (SB)) (Const64 <typ.Int> [int64(len(str))]))` under `Rule.SoundT`
(`DenT.lean`): the constant string is `strVal` of its aux (the data symbol's global and the
length), the result's `Addr` is `addrVal` of the aux `fe.StringData(str)`. `FrameOK`, which the
rewrite validator checks on the built nodes, says that this aux names the string's data symbol
and that the `Const64`'s auxint is the string's length.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

theorem strVal_of_strAux {tabs : Tables} {a : Option AuxRef} {s d : GoStr}
    (h : strAux? tabs a = some (s, d)) (hs : s.size ≠ 0) :
    strVal tabs a = .agg [.ptr ⟨.global d.toStringLossy, 0⟩, .int .w64 (BitVec.ofNat 64 s.size)] := by
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
  simp only [FrameOK, GoFV.Rules.Generated.Generic.r_generic_1022, Result.nodes, List.mem_cons,
    forall_eq_or_imp, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    Option.some.injEq, reduceCtorEq] at hfr
  obtain ⟨p, s, d, hp, hs, hsz, hsym⟩ := hfr.2.1 _ 0 rfl rfl
  obtain ⟨p', s', d', hp', hs', hlen⟩ := hfr.2.2.2.2 _ 0 rfl rfl
  simp only [Pat.auxPos, Field.bindsVar, beq_self_eq_true, ite_true, Option.some.injEq] at hp hp'
  subst hp hp'
  rw [hs, Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl⟩ := hs'
  clear hfr
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
  simp only [hc, Comp.make, Val.retype, Nat.le_refl, ite_true, BitVec.setWidth_eq]
  rw [Val.retype_of_hasTy hty]
  exact fun _ => Refines.refl _

end GoFV.Proof.Rules
