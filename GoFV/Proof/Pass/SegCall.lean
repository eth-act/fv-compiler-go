import GoFV.Opt.MemCall
import GoFV.Proof.MemOpsPre
import GoFV.Proof.MemRefine
import GoFV.Proof.ABI
import GoFV.Proof.Pass.DSEMem

/-!
# A `memclrNoHeapPointers`/`memmove` call ⊑ the plain `Zero`/`Move` write (#151)

generic.rules:1638 and :1730 replace `SelectN [0]` of a static call of
`runtime.memclrNoHeapPointers(p, n)` / `runtime.memmove(dst, src, n)` (`n` a `Const64`) by
`Zero [n] p mem` / `Move [n] dst src mem`. In an environment whose contracts for these
functions are the runtime model's (`Env.MemOps`), a call that the checks of
`GoFV.Opt.MemCall` accept (`simpleCall`, `calleeIs`) and that returns:

* `callOp_memclr`: on a pointer word `a` of `P` (`Val.asPtrWord`, which the contract's
  `Runtime.asPtr` agrees with: `runtime_asPtr_eq`), takes a memory `M` and yields
  `(mem Mc, agg [])`, where the plain write `M.write P (replicate n 0)` (what `Zero` does)
  succeeds with `M'` and `Mc ⊑ M'`;
* `callOp_memmove`: likewise with `M.read Q n = some bs` and `M.write P bs` (what `Move` does);
* `callOp_memclr_not_panic`, `callOp_memmove_not_panic`: never panics.

The contract runs on the memory with the callee's frame in the caller's outgoing-arguments area
poisoned; the proofs only use that this memory refines `M` (`poisonBelow_refines`), so they do not depend on which
bytes are poisoned: a read there gives bytes that refine the plain read (`Mem.Refines.read`),
and a write of refined bytes refines the plain write (`Mem.Refines.write`). `const64_toInt`
relates the size argument `.int .w64 (BitVec.ofInt 64 c.toInt)` of a `Const64 [c]` to the
`auxInt.toInt.toNat` that `Zero`/`Move` use. Non-vacuity: `memclr_witness`, `memmove_witness`.
-/

-- Parallel elaboration (-j4) wrote this module's constants in a different order on every build
-- (5 builds, 4 hashes), so importers missed the shared cache (#1; LEARNINGS.md). Sequential
-- elaboration costs no CPU here (7.5 s either way).
set_option Elab.async false

namespace GoFV.Proof.Seg
open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.MemCall

/-! ## `callOp` of a static call -/

/-- The ABI parameter assignments of call `v` (none without an ABI). -/
private theorem res_ok_bind {α β : Type} (a : α) (k : α → Res β) : (Res.ok a >>= k) = k a := rfl
private theorem res_stuck_bind {α β : Type} (msg : String) (k : α → Res β) :
    (Res.stuck msg >>= k) = .stuck msg := rfl
private theorem res_pure {α : Type} (a : α) : (pure a : Res α) = .ok a := rfl

abbrev callParams (tabs : Tables) (v : Value) : List ABIParam :=
  ((callABI? tabs v.aux).map (·.params.toList)).getD []

/-- A static call that returns: its callee's contract returned on the arguments (before `expand
calls` retyped at the parameters' shapes, decoded from the register pieces after) and the memory
with the callee's frame in the outgoing-arguments area poisoned, and the results were encoded. -/
theorem callOp_ok {env : Env} {ctx : Ctx} {v : Value} {argv : List Val} {y : Val}
    (hop : v.op = .StaticLECall ∨ v.op = .StaticCall) (hc : callOp env ctx v argv = .ok y) :
    ∃ name M args c rs m' r, v.aux.bind ctx.tabs.callee? = some name ∧
      argv.getLast? = some (.mem M) ∧
      (if v.op = .StaticCall then
        decodeArgs ctx.tabs ctx.act M ((callParams ctx.tabs v).filter (!·.out)) argv.dropLast = some args
      else args = retypeResults ctx.tabs ((callParams ctx.tabs v).filter (!·.out)) argv.dropLast) ∧
      (env.atAct ctx.act).extern name = some c ∧
      c args none (M.poisonBelow (.outargs ctx.act)
        (callFrame ctx.tabs v.aux ((callParams ctx.tabs v).filter (!·.out)))) = .returned rs m' ∧
      encodeResults ctx.tabs ctx.act ((callParams ctx.tabs v).filter (·.out))
        (retypeResults ctx.tabs ((callParams ctx.tabs v).filter (·.out)) rs) m' = some r ∧
      y = .tuple ((if v.op = .StaticCall then r.1
          else retypeResults ctx.tabs ((callParams ctx.tabs v).filter (·.out)) rs) ++
        [.mem r.2, .agg (((callParams ctx.tabs v).filter (·.out)).map fun p =>
          if p.regs.isEmpty then .ptr ⟨.outargs ctx.act, BitVec.ofInt 64 p.offset⟩ else .poison)]) := by
  rcases hop with hop | hop <;> unfold callOp at hc <;>
    simp only [callTarget, hop, nilClosure_none] at hc <;>
    simp only [hop] <;>
    cases hm : argv.getLast? <;> simp only [hm] at hc <;> (try cases hc) <;> rename_i w <;>
    cases w <;> simp only [res_ok_bind] at hc <;> (try cases hc) <;>
    simp (config := {decide := true}) only [Bool.or_false, ite_true, ite_false, res_pure,
      Option.map_none, Option.getD_none, Bool.false_eq_true, Res.ofOption] at hc ⊢ <;>
    (try simp only [res_ok_bind] at hc)
  · split at hc
    · cases hc
    split at hc
    · cases hc
    cases hn : v.aux.bind ctx.tabs.callee? <;> simp only [hn, Res.ofOption, res_ok_bind] at hc
    · cases hc
    rename_i name
    split at hc
    · rename_i c hx
      simp only [res_ok_bind] at hc
      split at hc
      · rename_i rs m' hr
        split at hc
        · rename_i r he
          simp only [res_ok_bind] at hc
          cases hc
          exact ⟨name, _, _, c, rs, m', r, rfl, rfl, rfl, hx, hr, he, rfl⟩
        · simp only [res_stuck_bind] at hc; cases hc
      · cases hc
      · cases hc
    · simp only [res_stuck_bind] at hc; cases hc
  · split at hc
    · rename_i args hd
      simp only [res_ok_bind] at hc
      split at hc
      · cases hc
      split at hc
      · cases hc
      cases hn : v.aux.bind ctx.tabs.callee? <;> simp only [hn, Res.ofOption, res_ok_bind] at hc
      · cases hc
      rename_i name
      split at hc
      · rename_i c hx
        simp only [res_ok_bind] at hc
        split at hc
        · rename_i rs m' hr
          split at hc
          · rename_i r he
            simp only [res_ok_bind] at hc
            cases hc
            exact ⟨name, _, args, c, rs, m', r, rfl, rfl, hd, hx, hr, he, rfl⟩
          · simp only [res_stuck_bind] at hc; cases hc
        · cases hc
        · cases hc
      · simp only [res_stuck_bind] at hc; cases hc
    · simp only [res_stuck_bind] at hc; cases hc

/-- A static call panics only when its callee's contract does. -/
theorem callOp_panic {env : Env} {ctx : Ctx} {v : Value} {argv : List Val} {e : Panic} {m : Mem}
    (hop : v.op = .StaticLECall ∨ v.op = .StaticCall) (hc : callOp env ctx v argv = .panic e m) :
    ∃ name c args M, v.aux.bind ctx.tabs.callee? = some name ∧ (env.atAct ctx.act).extern name = some c ∧
      c args none M = .panicked e m := by
  rcases hop with hop | hop <;> unfold callOp at hc <;>
    simp only [callTarget, hop, nilClosure_none] at hc <;>
    cases hm : argv.getLast? <;> simp only [hm] at hc <;> (try cases hc) <;> rename_i w <;>
    cases w <;> simp only [res_ok_bind] at hc <;> (try cases hc) <;>
    simp (config := {decide := true}) only [Bool.or_false, ite_true, ite_false, res_pure,
      Option.map_none, Option.getD_none, Bool.false_eq_true, Res.ofOption] at hc <;>
    (try simp only [res_ok_bind] at hc)
  · split at hc
    · cases hc
    split at hc
    · cases hc
    cases hn : v.aux.bind ctx.tabs.callee? <;> simp only [hn, Res.ofOption, res_ok_bind] at hc
    · cases hc
    rename_i name
    split at hc
    · rename_i c hx
      simp only [res_ok_bind] at hc
      split at hc
      · split at hc
        · simp only [res_ok_bind] at hc; cases hc
        · simp only [res_stuck_bind] at hc; cases hc
      · rename_i hr; cases hc; exact ⟨name, c, _, _, rfl, hx, hr⟩
      · cases hc
    · simp only [res_stuck_bind] at hc; cases hc
  · split at hc
    · simp only [res_ok_bind] at hc
      split at hc
      · cases hc
      split at hc
      · cases hc
      cases hn : v.aux.bind ctx.tabs.callee? <;> simp only [hn, Res.ofOption, res_ok_bind] at hc
      · cases hc
      rename_i name
      split at hc
      · rename_i c hx
        simp only [res_ok_bind] at hc
        split at hc
        · split at hc
          · simp only [res_ok_bind] at hc; cases hc
          · simp only [res_stuck_bind] at hc; cases hc
        · rename_i hr; cases hc; exact ⟨name, c, _, _, rfl, hx, hr⟩
        · cases hc
      · simp only [res_stuck_bind] at hc; cases hc
    · simp only [res_stuck_bind] at hc; cases hc

/-! ## The checks -/

theorem simpleCall_op {tabs : Tables} {v : Value} {k : Nat} (hs : simpleCall tabs v k = true) :
    v.op = .StaticLECall ∨ v.op = .StaticCall := by
  simp only [simpleCall, Bool.and_eq_true] at hs
  obtain ⟨-, h⟩ := hs
  split at h
  · exact .inl ‹_›
  · exact .inr ‹_›
  · cases h

theorem simpleCall_post {tabs : Tables} {v : Value} {k : Nat} (hs : simpleCall tabs v k = true)
    (hop : v.op = .StaticCall) :
    ∃ abi, callABI? tabs v.aux = some abi ∧ inShapes tabs k abi.params.toList = true := by
  simp only [simpleCall, Bool.and_eq_true, hop] at hs
  obtain ⟨-, h⟩ := hs
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem simpleCall_pre {tabs : Tables} {v : Value} {k : Nat} (hs : simpleCall tabs v k = true)
    (hop : ¬ v.op = .StaticCall) :
    callABI? tabs v.aux = none ∨ ∃ abi, callABI? tabs v.aux = some abi ∧ inShapes tabs k abi.params.toList = true := by
  rcases simpleCall_op hs with h | h
  · simp only [simpleCall, Bool.and_eq_true, h] at hs
    obtain ⟨-, hs⟩ := hs
    cases hc : callABI? tabs v.aux with
    | none => exact .inl rfl
    | some abi => rw [hc] at hs; exact .inr ⟨abi, rfl, hs⟩
  · exact absurd h hop

theorem calleeIs_eq {tabs : Tables} {v : Value} {name : String} (h : calleeIs tabs v name = true) :
    v.aux.bind tabs.callee? = some name := by
  simpa [calleeIs] using h

theorem inShape_ptr {tabs : Tables} {p : ABIParam} (h : inShape tabs true p = true) :
    p.out = false ∧ p.regs.size = 1 ∧ ∃ o, tabs.ty p.type = .ptr o := by
  unfold inShape at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · exact ⟨_, ‹_›⟩
  · cases h3
  · cases h3

theorem inShape_int {tabs : Tables} {p : ABIParam} (h : inShape tabs false p = true) :
    p.out = false ∧ p.regs.size = 1 ∧ tabs.ty p.type = .int .w64 := by
  unfold inShape at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  split at h3
  · cases h3
  · assumption
  · cases h3

/-! ## Decoding register arguments -/

theorem decodeArgs_reg {tabs : Tables} {act : Nat} {m : Mem} {p : ABIParam} {ps : List ABIParam}
    {a : Val} {pieces : List Val} (hr : p.regs.size = 1) :
    decodeArgs tabs act m (p :: ps) (a :: pieces) =
      (decodeArgs tabs act m ps pieces).map (ofPieces (tabs.ty p.type) [a] :: ·) := by
  simp [decodeArgs, Array.isEmpty, hr]
  cases decodeArgs tabs act m ps pieces <;> rfl

theorem ofPieces_ptr (o : Option Nat) (P : Ptr) : ofPieces (.ptr o) [.ptr P] = .ptr P := by
  rw [ABI.ofPieces_eq_build rfl (by show ABI.List.Forall₂ _ _ [(0, _)]; exact .cons rfl .nil)]; rfl

theorem ofPieces_int (x : BitVec 64) : ofPieces (.int .w64) [.int .w64 x] = .int .w64 x := by
  rw [ABI.ofPieces_eq_build rfl (by show ABI.List.Forall₂ _ _ [(0, _)]; exact .cons rfl .nil)]; rfl

/-- A pointer word decodes from its register piece at a pointer shape as itself. -/
theorem ofPieces_ptrWord (o : Option Nat) {a : Val} {P : Ptr} (ha : a.asPtrWord = some P) :
    ofPieces (.ptr o) [a] = a := by
  cases a with
  | ptr P => exact ofPieces_ptr o P
  | int w x =>
    cases w <;> simp only [Val.asPtrWord, reduceCtorEq] at ha
    rw [ABI.ofPieces_eq_build rfl (by show ABI.List.Forall₂ _ _ [(0, _)]; exact .cons rfl .nil)]; rfl
  | _ => simp only [Val.asPtrWord, reduceCtorEq] at ha

/-- The runtime model reads a pointer argument as a pointer word. -/
theorem runtime_asPtr_eq (a : Val) : Runtime.asPtr a = a.asPtrWord := by
  cases a with
  | int w x => cases w <;> rfl
  | _ => rfl

theorem decodeArgs_two {tabs : Tables} {act : Nat} {m : Mem} {ps : List ABIParam}
    (h : inShapes tabs 2 ps = true) {a : Val} (ha : ∀ o, ofPieces (.ptr o) [a] = a)
    (x : BitVec 64) :
    decodeArgs tabs act m (ps.filter (!·.out)) [a, .int .w64 x] = some [a, .int .w64 x] := by
  have hl : ps.length = 2 := by simp only [inShapes, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1
  rcases ps with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩ <;> simp at hl
  simp only [inShapes, List.dropLast, List.all, List.getLast?_cons_cons, List.getLast?_singleton, Option.all, Bool.and_eq_true,
    Bool.and_true] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  obtain ⟨ha1, ha2, o, ha3⟩ := inShape_ptr h1
  obtain ⟨hb1, hb2, hb3⟩ := inShape_int h2
  simp only [List.filter, ha1, hb1, Bool.not_false]
  rw [decodeArgs_reg ha2, decodeArgs_reg hb2, ha3, hb3, ha, ofPieces_int]
  rfl

theorem decodeArgs_three {tabs : Tables} {act : Nat} {m : Mem} {ps : List ABIParam}
    (h : inShapes tabs 3 ps = true) {a b : Val} (ha : ∀ o, ofPieces (.ptr o) [a] = a)
    (hb : ∀ o, ofPieces (.ptr o) [b] = b) (x : BitVec 64) :
    decodeArgs tabs act m (ps.filter (!·.out)) [a, b, .int .w64 x] =
      some [a, b, .int .w64 x] := by
  have hl : ps.length = 3 := by simp only [inShapes, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1
  rcases ps with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, rest⟩⟩⟩⟩ <;> simp at hl
  simp only [inShapes, List.dropLast, List.all, List.getLast?_cons_cons, List.getLast?_singleton, Option.all, Bool.and_eq_true,
    Bool.and_true] at h
  obtain ⟨⟨-, h1, h2⟩, h3⟩ := h
  obtain ⟨ha1, ha2, o, ha3⟩ := inShape_ptr h1
  obtain ⟨hb1, hb2, o', hb3⟩ := inShape_ptr h2
  obtain ⟨hc1, hc2, hc3⟩ := inShape_int h3
  simp only [List.filter, ha1, hb1, hc1, Bool.not_false]
  rw [decodeArgs_reg ha2, decodeArgs_reg hb2, decodeArgs_reg hc2, ha3, hb3, hc3, ha, hb,
    ofPieces_int]
  rfl

/-- A pointer word keeps itself at every pointer shape. -/
theorem retype_ptrWord {a : Val} {P : Ptr} (h : a.asPtrWord = some P) (o : Option Nat) :
    a.retype (.ptr o) = a := by
  cases a with
  | ptr p => rfl
  | int w x => cases w <;> first | rfl | simp [Val.asPtrWord] at h
  | _ => simp [Val.asPtrWord] at h

theorem retype_int64 (x : BitVec 64) : (Val.int .w64 x).retype (.int .w64) = .int .w64 x := by
  simp [Val.retype]

/-- A pre-`expand calls` `simpleCall` passes pointer-shaped words and a 64-bit size as they are. -/
theorem retypeArgs_two {tabs : Tables} {ps : List ABIParam} (h : inShapes tabs 2 ps = true) {a : Val}
    (ha : ∀ o, a.retype (.ptr o) = a) (x : BitVec 64) :
    retypeResults tabs (ps.filter (!·.out)) [a, .int .w64 x] = [a, .int .w64 x] := by
  have hl : ps.length = 2 := by simp only [inShapes, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1
  rcases ps with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, rest⟩⟩⟩ <;> simp at hl
  simp only [inShapes, List.dropLast, List.all, List.getLast?_cons_cons, List.getLast?_singleton, Option.all,
    Bool.and_eq_true, Bool.and_true] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  obtain ⟨h11, -, o, h13⟩ := inShape_ptr h1
  obtain ⟨h21, -, h23⟩ := inShape_int h2
  simp only [List.filter, h11, h21, Bool.not_false, retypeResults, h13, h23, ha, retype_int64]

theorem retypeArgs_three {tabs : Tables} {ps : List ABIParam} (h : inShapes tabs 3 ps = true) {a b : Val}
    (ha : ∀ o, a.retype (.ptr o) = a) (hb : ∀ o, b.retype (.ptr o) = b) (x : BitVec 64) :
    retypeResults tabs (ps.filter (!·.out)) [a, b, .int .w64 x] = [a, b, .int .w64 x] := by
  have hl : ps.length = 3 := by simp only [inShapes, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1
  rcases ps with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, rest⟩⟩⟩⟩ <;> simp at hl
  simp only [inShapes, List.dropLast, List.all, List.getLast?_cons_cons, List.getLast?_singleton, Option.all,
    Bool.and_eq_true, Bool.and_true] at h
  obtain ⟨⟨-, h1, h2⟩, h3⟩ := h
  obtain ⟨h11, -, o, h13⟩ := inShape_ptr h1
  obtain ⟨h21, -, o', h23⟩ := inShape_ptr h2
  obtain ⟨h31, -, h33⟩ := inShape_int h3
  simp only [List.filter, h11, h21, h31, Bool.not_false, retypeResults, h13, h23, h33, ha, hb, retype_int64]

theorem encodeResults_nil {tabs : Tables} {act : Nat} {outs : List ABIParam} {m : Mem}
    {r : List Val × Mem} (h : encodeResults tabs act outs (retypeResults tabs outs []) m = some r) :
    outs = [] ∧ r = ([], m) := by
  cases outs with
  | nil => simp only [retypeResults, encodeResults, Option.some.injEq] at h; exact ⟨rfl, h.symm⟩
  | cons p ps => simp [retypeResults, encodeResults] at h

/-! ## Memory -/

/-- Poisoning a block refines the memory. -/
theorem poisonBlock_refines (m : Mem) (b : Blk) : Mem.Refines (m.poisonBlock b) m := by
  unfold Mem.poisonBlock
  cases h : m.find? b with
  | none => exact Mem.Refines.refl m
  | some a =>
    have := (Mem.Refines.refl m).set b (a := { a with data := Array.replicate a.data.size .poison })
      (a' := a) ⟨rfl, BytesRefineA.replicate_poison _ rfl⟩
    rwa [DSE.set_self h] at this

/-- Poisoning the bytes of a block below an offset refines the memory. -/
theorem poisonBelow_refines (m : Mem) (b : Blk) (n : Nat) : Mem.Refines (m.poisonBelow b n) m := by
  unfold Mem.poisonBelow
  cases h : m.find? b with
  | none => exact Mem.Refines.refl m
  | some a =>
    have := (Mem.Refines.refl m).set b
      (a := { a with data := a.data.mapIdx fun i x => if i < n then .poison else x }) (a' := a)
      ⟨rfl, BytesRefine.of_getElem (by simp) fun i _ _ => by
        simp only [Array.getElem_toList, Array.getElem_mapIdx]
        split
        · exact .poison _
        · exact .refl _⟩
    rwa [DSE.set_self h] at this

/-- The value of `Const64 [c]` (`Conv.const .w64 c`) as a signed integer is `c`. -/
theorem const64_toInt (c : Int64) : (BitVec.ofInt 64 c.toInt).toInt = c.toInt := by
  simp

/-! ## The memory calls -/

/-- The arguments a `simpleCall` passes to the contract are its value arguments. -/
theorem callOp_args {ctx : Ctx} {v : Value} {k : Nat} {M : Mem} {pieces args : List Val}
    (hs : simpleCall ctx.tabs v k = true)
    (hdec : ∀ ps, inShapes ctx.tabs k ps = true →
      decodeArgs ctx.tabs ctx.act M (ps.filter (!·.out)) pieces = some pieces)
    (hret : ∀ ps, inShapes ctx.tabs k ps = true → retypeResults ctx.tabs (ps.filter (!·.out)) pieces = pieces)
    (hargs : if v.op = .StaticCall then
        decodeArgs ctx.tabs ctx.act M ((callParams ctx.tabs v).filter (!·.out)) pieces = some args
      else args = retypeResults ctx.tabs ((callParams ctx.tabs v).filter (!·.out)) pieces) : args = pieces := by
  split at hargs
  · rename_i hpost
    obtain ⟨abi, habi, hsh⟩ := simpleCall_post hs hpost
    rw [callParams, habi, Option.map_some, Option.getD_some, hdec _ hsh] at hargs
    exact (Option.some.inj hargs).symm
  · rename_i hpre
    rw [hargs]
    rcases simpleCall_pre hs hpre with hn | ⟨abi, habi, hsh⟩
    · rw [callParams, hn]; rfl
    · rw [callParams, habi, Option.map_some, Option.getD_some, hret _ hsh]

/-- A returning `memclrNoHeapPointers(a, x)` call on a pointer word `a` of `P` refines the plain
write of `x` zero bytes at `P` (`Zero`). -/
theorem callOp_memclr {env : Env} (hE : env.MemOps) {ctx : Ctx} {v : Value} {P : Ptr} {a : Val}
    {x : BitVec 64} {mm y : Val} (hs : simpleCall ctx.tabs v 2 = true)
    (hn : calleeIs ctx.tabs v "runtime.memclrNoHeapPointers" = true)
    (hpa : a.asPtrWord = some P) (hc : callOp env ctx v [a, .int .w64 x, mm] = .ok y) :
    ∃ M M' Mc, mm = .mem M ∧ M.write P (Array.replicate x.toInt.toNat (.b 0)) = some M' ∧
      y = .tuple [.mem Mc, .agg []] ∧ Mem.Refines Mc M' := by
  obtain ⟨name, M, args, c, rs, m', r, hname, hm, hargs, hx, hr, he, hy⟩ :=
    callOp_ok (simpleCall_op hs) hc
  rw [calleeIs_eq hn] at hname; cases hname
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hm
  subst hm
  have ha := callOp_args hs (fun ps h => decodeArgs_two h (ofPieces_ptrWord · hpa) x)
    (fun ps h => retypeArgs_two h (retype_ptrWord hpa) x) hargs
  subst ha
  obtain rfl := (hE.atAct ctx.act).1 c hx
  simp only [Runtime.memclr, Runtime.ok?, runtime_asPtr_eq, hpa, Runtime.asInt] at hr
  generalize callFrame ctx.tabs v.aux _ = F at hr
  cases hw : (M.poisonBelow (.outargs ctx.act) F).write P (Array.replicate x.toInt.toNat (.b 0)) with
  | none =>
    simp only [hw, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at hr
    cases hr
  | some Mc =>
    simp only [hw, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      COutcome.returned.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨hout, rfl⟩ := encodeResults_nil he
    obtain ⟨M', hw', hR⟩ := (poisonBelow_refines M _ F).write (BytesRefineA.refl _) hw
    refine ⟨M, M', Mc, rfl, hw', ?_, hR⟩
    rw [hy, hout]
    split <;> rfl

/-- A returning `memmove(a, b, x)` call on pointer words `a`, `b` of `P`, `Q` refines the plain
read of `x` bytes at `Q` and their write at `P` (`Move`). -/
theorem callOp_memmove {env : Env} (hE : env.MemOps) {ctx : Ctx} {v : Value} {P Q : Ptr}
    {a b : Val} {x : BitVec 64} {mm y : Val} (hs : simpleCall ctx.tabs v 3 = true)
    (hn : calleeIs ctx.tabs v "runtime.memmove" = true) (hpa : a.asPtrWord = some P)
    (hqb : b.asPtrWord = some Q) (hc : callOp env ctx v [a, b, .int .w64 x, mm] = .ok y) :
    ∃ M bs M' Mc, mm = .mem M ∧ M.read Q x.toInt.toNat = some bs ∧ M.write P bs = some M' ∧
      y = .tuple [.mem Mc, .agg []] ∧ Mem.Refines Mc M' := by
  obtain ⟨name, M, args, c, rs, m', r, hname, hm, hargs, hx, hr, he, hy⟩ :=
    callOp_ok (simpleCall_op hs) hc
  rw [calleeIs_eq hn] at hname; cases hname
  simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hm
  subst hm
  have ha := callOp_args hs (fun ps h =>
    decodeArgs_three h (ofPieces_ptrWord · hpa) (ofPieces_ptrWord · hqb) x)
    (fun ps h => retypeArgs_three h (retype_ptrWord hpa) (retype_ptrWord hqb) x) hargs
  subst ha
  obtain rfl := (hE.atAct ctx.act).2 c hx
  simp only [Runtime.memmove, Runtime.ok?, runtime_asPtr_eq, hpa, hqb, Runtime.asInt] at hr
  generalize callFrame ctx.tabs v.aux _ = F at hr
  have hP := poisonBelow_refines M (.outargs ctx.act) F
  cases hrd : (M.poisonBelow (.outargs ctx.act) F).read Q x.toInt.toNat with
  | none =>
    simp only [hrd, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at hr
    cases hr
  | some bs0 =>
    obtain ⟨bs, hrd', hb⟩ := hP.read hrd
    cases hw : (M.poisonBelow (.outargs ctx.act) F).write P bs0 with
    | none =>
      simp only [hrd, hw, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Option.bind_none] at hr
      cases hr
    | some Mc =>
      simp only [hrd, hw, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        COutcome.returned.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨hout, rfl⟩ := encodeResults_nil he
      obtain ⟨M', hw', hR⟩ := hP.write hb hw
      refine ⟨M, bs, M', Mc, rfl, hrd', hw', ?_, hR⟩
      rw [hy, hout]
      split <;> rfl

/-- A call of `memclrNoHeapPointers` never panics (it returns or is stuck). -/
theorem callOp_memclr_not_panic {env : Env} (hE : env.MemOps) {ctx : Ctx} {v : Value} {k : Nat}
    (hs : simpleCall ctx.tabs v k = true)
    (hn : calleeIs ctx.tabs v "runtime.memclrNoHeapPointers" = true) (argv : List Val)
    (e : Panic) (m : Mem) : callOp env ctx v argv ≠ .panic e m := by
  intro hc
  obtain ⟨name, c, args, M, hname, hx, hr⟩ := callOp_panic (simpleCall_op hs) hc
  rw [calleeIs_eq hn] at hname; cases hname
  obtain rfl := (hE.atAct ctx.act).1 c hx
  simp only [Runtime.memclr, Runtime.ok?] at hr
  split at hr <;> cases hr

/-- A call of `memmove` never panics (it returns or is stuck). -/
theorem callOp_memmove_not_panic {env : Env} (hE : env.MemOps) {ctx : Ctx} {v : Value} {k : Nat}
    (hs : simpleCall ctx.tabs v k = true) (hn : calleeIs ctx.tabs v "runtime.memmove" = true)
    (argv : List Val) (e : Panic) (m : Mem) : callOp env ctx v argv ≠ .panic e m := by
  intro hc
  obtain ⟨name, c, args, M, hname, hx, hr⟩ := callOp_panic (simpleCall_op hs) hc
  rw [calleeIs_eq hn] at hname; cases hname
  obtain rfl := (hE.atAct ctx.act).2 c hx
  simp only [Runtime.memmove, Runtime.ok?] at hr
  split at hr <;> cases hr

/-! ## Non-vacuity -/

/-- Tables of the witnesses: aux 0 is an `AuxCall` (no ABI assignments) of the symbol `fn`
(aux 1). -/
def mcTabs (fn : String) : Tables where
  auxes := #[some { fmt := GoStr.ofString "AuxCall", kind := .call (some 1) none },
    some { fmt := GoStr.ofString fn,
           kind := .sym (GoStr.ofString fn) 0 "" 0 default none none none #[] none }]

/-- A pre-`expand calls` static call of aux 0 with `k` value arguments and the memory. -/
def mcCall (k : Nat) : Value :=
  { id := 1, op := .StaticLECall, type := 0, auxInt := 0, aux := some 0, pos := default,
    uses := 1, args := (List.range (k + 1)).toArray.map (· + 2), block := 1 }

def mcCtx (fn : String) : Ctx :=
  { f := default, tabs := mcTabs fn, tys := #[], sched := #[], params := #[] }

/-- One writable heap block of 16 bytes. -/
def mcMem : Mem := { blocks := #[(.heap 0, { data := Array.replicate 16 (.b 7) })], nextHeap := 1 }

private def resOk : Res Val → Bool
  | .ok _ => true
  | _ => false

private theorem exists_of_resOk {r : Res Val} (h : resOk r = true) : ∃ y, r = .ok y := by
  cases r with
  | ok y => exact ⟨y, rfl⟩
  | _ => cases h

/-- Non-vacuity of `callOp_memclr`: `memclrNoHeapPointers(&heap0[0], 8)` in `Env.runtime`. -/
theorem memclr_witness :
    simpleCall (mcTabs "runtime.memclrNoHeapPointers") (mcCall 2) 2 = true ∧
      calleeIs (mcTabs "runtime.memclrNoHeapPointers") (mcCall 2) "runtime.memclrNoHeapPointers" = true ∧
      ∃ y, callOp Env.runtime (mcCtx "runtime.memclrNoHeapPointers") (mcCall 2)
        [.ptr ⟨.heap 0, 0⟩, .int .w64 8, .mem mcMem] = .ok y :=
  ⟨by decide +kernel, by decide +kernel, exists_of_resOk (by decide +kernel)⟩

/-- Non-vacuity of `callOp_memmove`: `memmove(&heap0[0], &heap0[8], 8)` in `Env.runtime`. -/
theorem memmove_witness :
    simpleCall (mcTabs "runtime.memmove") (mcCall 3) 3 = true ∧
      calleeIs (mcTabs "runtime.memmove") (mcCall 3) "runtime.memmove" = true ∧
      ∃ y, callOp Env.runtime (mcCtx "runtime.memmove") (mcCall 3)
        [.ptr ⟨.heap 0, 0⟩, .ptr ⟨.heap 0, 8⟩, .int .w64 8, .mem mcMem] = .ok y :=
  ⟨by decide +kernel, by decide +kernel, exists_of_resOk (by decide +kernel)⟩

end GoFV.Proof.Seg
