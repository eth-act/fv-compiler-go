import GoFV.Gen.Results
import GoFV.Proof.Gen.G1
import GoFV.Proof.Gen.G2

/-!
# The results of a return in their ABI registers (`docs/plans/proofs3.md` §9)

What `retRegsOK` (`GoFV/Gen/Results.lean`) gives: when the terminator of a `Ret` block returns
`(rs, mm)` from a state `LocMatch`ed to the machine state `m`, `rs` are the contents of the
function's result registers (`ownOutRegs`), related to `m`'s X registers, and `mm` is the state's
memory (`ret_results`, `ResultRel`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64
open GoFV.Proof.Gen

/-- The results `rs` and the memory `mm` of a return, and the machine state `t`: as many results
as result registers `outs`, the `j`-th in the X register of `outs[j]` (`R0`–`R15`), and `mm`
injected into the memory. -/
structure ResultRel (E : MatchEnv) (outs : List Nat) (rs : List Val) (mm : Mem) (t : MState) :
    Prop where
  len : rs.length = outs.length
  regs : ∀ (j : Nat) x r, rs[j]? = some x → outs[j]? = some r →
    r < 16 ∧ ValRel E.ι x (t.x (BitVec.ofNat 5 r))
  mem : MemInj E.ι mm t.mem

/-- The terminator of a `Ret` block returns the tuple of its control, the memory last. -/
theorem stepTermL_ret {fr : GoFV.SSA.Sem.Frame} {b : Block} {rs : List Val} {mm : Mem}
    (hk : b.kind = .Ret) (h : stepTermL fr b = .ok (.ret rs mm)) :
    control fr b 0 = .ok (.tuple (rs ++ [.mem mm])) := by
  have ha : b.kind.isArm64 = false := by rw [hk]; rfl
  simp only [stepTermL, ha, Bool.false_eq_true, ↓reduceIte] at h
  unfold stepTerm at h
  rw [hk] at h
  simp only [bind, Res.bind] at h
  cases hc : control fr b 0 with
  | panic e m => rw [hc] at h; cases h
  | stuck msg => rw [hc] at h; cases h
  | ok y =>
    rw [hc] at h
    simp only at h
    split at h
    · rename_i vs
      split at h
      · rename_i m' rs' hl hd
        split at h
        · cases h
        · cases h
          obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hd
          rw [List.dropLast_concat]
      · cases h
    · cases h

/-- `retypeL` of a tuple at a tuple shape of as many components: componentwise. -/
theorem retypeL_tuple {ts : List Ty} {xs : List Val} (h : ts.length = xs.length) :
    (Val.tuple xs).retypeL (.tuple ts) = .tuple (List.zipWith (fun t x => x.retypeL t) ts xs) := by
  simp only [Val.retypeL, Val.widen, Val.retype, retypePre_widen ts xs h]

/-- **The results of a return.** When `retBlockOK` accepts the `Ret` block `blk` (ID `b`) for the
result registers `outs`, its terminator returning `(rs, mm)` from a state `s` `LocMatch`ed to `m`
(the class map at the terminator holding of `s`) returns the contents of `outs`, related to `m`'s
registers, and `s`'s memory. -/
theorem ret_results {E : MatchEnv} {lc : LocCtx} {kt : KTab} {P : BitVec 64 → Prop}
    {s s' : LocState} {b : ID} {blk : Block} {m : MState} {outs : List Nat} {rs : List Val}
    {mm : Mem} (hl : lc.ctx.f.lowered = true) (hA : AddrAgree E.ι)
    (hm : LocMatch E s b blk.values.size m)
    (hinv : CoreInv E.ι P (kAt lc kt b blk blk.values.size).get s)
    (hok : retBlockOK lc kt outs b blk = true) (hk : blk.kind = .Ret)
    (ht : stepTermLoc lc s blk = .ok (.ret rs mm, s')) :
    ResultRel E outs rs mm m := by
  simp only [retBlockOK, hk, bne_self_eq_false, Bool.false_or] at hok
  split at hok
  case h_2 => cases hok
  rename_i c hctl
  have hc : blk.controls = #[c] := Array.ext' (by simpa using hctl)
  cases hv : lc.ctx.f.value? c with
  | none => rw [hv] at hok; cases hok
  | some v =>
  rw [hv] at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hop, hty⟩, hargs⟩ := hok
  have hty' := Ty.eq_of_beq hty
  obtain ⟨x, R, hx, hs', hy, hn⟩ := stepTermLoc_one hc ht
  have hctrl := stepTermL_ret hk hn
  have hxv : x = .tuple (rs ++ [.mem mm]) := (hy _ hctrl).symm
  -- the control: the tuple of the arguments' reads
  unfold LocState.control at hx
  rw [hv] at hx
  simp only [hop, beq_self_eq_true, ↓reduceIte, bind, Res.bind] at hx
  cases hxs : v.args.toList.mapM (s.read lc) with
  | panic e m' => rw [hxs] at hx; cases hx
  | stuck msg => rw [hxs] at hx; cases hx
  | ok xs =>
  rw [hxs] at hx
  simp only [pure, Res.ok.injEq] at hx
  obtain ⟨hlen, hread⟩ := mapM_res hxs
  rw [lmode_retype hl, hty', retypeL_tuple (by simp [hlen]), hxv] at hx
  simp only [Val.tuple.injEq] at hx
  -- `rs ++ [mem]` componentwise
  simp only [retArgsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hargs
  obtain ⟨⟨hnargs, hlast⟩, hall⟩ := hargs
  have hA1 : v.args.size = outs.length + 1 := by simpa using hnargs
  have hX1 : xs.length = v.args.size := by simpa using hlen
  have hrsl : rs.length = outs.length := by
    have := congrArg List.length hx
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_zipWith,
      List.length_map, Array.length_toList] at this
    omega
  have hcomp : ∀ j (hj : j < rs.length), rs[j] =
      (xs[j]'(by omega)).retypeL (lc.ty (v.args.toList[j]'(by simp; omega))) := by
    intro j hj
    have := congrArg (·[j]?) hx
    simp only [List.getElem?_append_left hj, List.getElem?_zipWith, List.getElem?_map,
      List.getElem?_eq_getElem (show j < v.args.toList.length by simp; omega),
      List.getElem?_eq_getElem (show j < xs.length by omega), Option.map_some, Option.some.injEq]
      at this
    rw [List.getElem?_eq_getElem hj] at this
    exact (Option.some.inj this).symm
  obtain ⟨mm0, hmm0, hinj⟩ := hm.mem
  refine ⟨hrsl, fun j y r hy hr => ?_, ?_⟩
  · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hy
    obtain ⟨hjo, rfl⟩ := List.getElem?_eq_some_iff.1 hr
    have hja : j < v.args.toList.length := by simp; omega
    have hz := hall (v.args.toList[j], outs[j]) (List.mem_iff_getElem.2
      ⟨j, by simp; omega, by simp⟩)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hz
    obtain ⟨⟨⟨hh, h16⟩, hcls⟩, hK⟩ := hz
    obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 hcls
    rw [hc0] at hK
    obtain ⟨x', hx', hrel, hfit⟩ := arg_rel hA hl hm hinv hh hc0 (fun _ => hK)
      (Or.inr ⟨by omega, objX?_low h16⟩)
    have hxj : xs[j]'(by omega) = x' := by
      have := hread j hja (by omega)
      rw [hx'] at this
      exact (Res.ok.inj this).symm
    refine ⟨h16, ?_⟩
    rw [hcomp j hj, hxj, ← rX_lt (by omega)]
    exact valRel_retypeL hA hc0 hfit hrel
  · -- the memory: the last argument's read, the state's memory
    have hlast' : v.args.toList.getLast? = some (v.args.toList[outs.length]'(by simp; omega)) := by
      rw [List.getLast?_eq_getElem?]
      simp [hA1]
    rw [hlast'] at hlast
    simp only [Bool.and_eq_true, beq_iff_eq] at hlast
    obtain ⟨hmt, hhn⟩ := hlast
    have hrd := hread outs.length (by simp; omega) (by omega)
    rw [read_mem hl hhn hmt hmm0] at hrd
    have hxl : xs[outs.length]'(by omega) = .mem mm0 := (Res.ok.inj hrd).symm
    have := congrArg (·[outs.length]?) hx
    simp only [List.getElem?_append_right (Nat.le_of_eq hrsl), hrsl, Nat.sub_self,
      List.getElem?_cons_zero, List.getElem?_zipWith, List.getElem?_map,
      List.getElem?_eq_getElem (show outs.length < v.args.toList.length by simp; omega),
      List.getElem?_eq_getElem (show outs.length < xs.length by omega), Option.map_some,
      Option.some.injEq, hxl, memTy_eq hmt] at this
    rw [retypeL_mem] at this
    cases this
    exact hinj
