import GoFV.Gen.Results
import GoFV.Proof.Gen.G26

/-!
# The results of a return in their ABI registers (`docs/plans/proofs3.md` §9)

What `retRegsOK` (`GoFV/Gen/Results.lean`) gives: when the terminator of a `Ret` block returns
`(rs, mm)` from a state `LocMatch`ed to the machine state `m`, `rs` are the contents of the
function's result registers (`ownOutRegs`), related to `m`'s X registers, and `mm` is the state's
memory (`ret_results`, `ResultRel`). Both modes: a lowered function reads its results as
registers (`Val.retypeL`), one with no arm64 op (slice G26's functions) at their shapes
(`Val.retype`); either keeps a register's relation at a `MakeResult` component of a class no
wider than the result's (`valRel_retypeL_le`, `lmode_valRel_le`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check
open GoFV.Arm64 (MState)
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

/-! ## Reading a register at a narrower shape -/

/-- An integer of a width other than 64 bits relates to the registers with those low bits. -/
theorem valRel_int_low {ι : Blk → Option (BitVec 64)} {w : Width} (hw : w ≠ .w64)
    {r : BitVec 64} {x : BitVec w.bits} (h : r.setWidth w.bits = x) :
    ValRel ι (.int w x) r := by
  cases w
  · exact h
  · exact h
  · exact h
  · exact absurd rfl hw

/-- A register content of class `c` read at a shape of class `c' ≤ c` keeps its relation: a
narrower integer shape keeps the low bits, every other narrower read is `poison`. -/
theorem valRel_retypeL_le {ι : Blk → Option (BitVec 64)} (hA : AddrAgree ι) {c c' : Nat}
    {t : Ty} {v : Val} {r : BitVec 64} (hc : cls t = some c') (hle : c' ≤ c) (hf : Fits c v)
    (hv : ValRel ι v r) : ValRel ι (v.retypeL t) r := by
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · exact valRel_retypeL hA hc hf hv
  cases v with
  | poison => cases t <;> trivial
  | int w x =>
    simp only [Fits] at hf
    subst hf
    cases t with
    | int w' =>
      simp only [cls, Option.some.injEq] at hc
      subst hc
      have hr : r.setWidth w.bits = x := by
        cases w
        · exact hv
        · exact hv
        · exact hv
        · rw [valRel_i64 hA hv]; exact BitVec.setWidth_eq x
      have hw' : w' ≠ .w64 := by
        rintro rfl; cases w <;> simp [Width.bits] at hlt
      have he : (Val.int w x).retypeL (.int w') = .int w' (x.setWidth w'.bits) := by
        cases w <;> cases w' <;> first | rfl | (simp [Width.bits] at hlt)
      rw [he]
      exact valRel_int_low hw' (by rw [← hr, BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt hlt)])
    | ptr e =>
      simp only [cls, Option.some.injEq] at hc
      subst hc
      cases w <;> simp [Width.bits] at hlt
    | bool =>
      cases w <;> trivial
    | _ => simp [cls] at hc
  | ptr p =>
    simp only [Fits] at hf
    subst hf
    cases t with
    | int w' =>
      simp only [cls, Option.some.injEq] at hc
      subst hc
      cases w' <;> first | trivial | simp [Width.bits] at hlt
    | ptr e => simp only [cls, Option.some.injEq] at hc; omega
    | bool => trivial
    | _ => simp [cls] at hc
  | bool b =>
    simp only [Fits] at hf
    subst hf
    cases t with
    | int w' => simp only [cls, Option.some.injEq] at hc; subst hc; cases w' <;> simp [Width.bits] at hlt
    | ptr e => simp only [cls, Option.some.injEq] at hc; omega
    | bool => simp only [cls, Option.some.injEq] at hc; omega
    | _ => simp [cls] at hc
  | _ => simp [Fits] at hf

/-- `valRel_retypeL_le` in Phase 1's mode (`Val.retype`). -/
theorem valRel_retype_le {ι : Blk → Option (BitVec 64)} (hA : AddrAgree ι) {c c' : Nat}
    {t : Ty} {v : Val} {r : BitVec 64} (hc : cls t = some c') (hle : c' ≤ c) (hf : Fits c v)
    (hv : ValRel ι v r) : ValRel ι (v.retype t) r := by
  rcases retype_cases hc v with h | h
  · rw [h]; exact valRel_retypeL_le hA hc hle hf hv
  · rw [h]; trivial

/-! ## Both modes -/

/-- `runLoc`'s reading of a register content at a shape of no wider class keeps its relation. -/
theorem lmode_valRel_le {ι : Blk → Option (BitVec 64)} (hA : AddrAgree ι) (f : Func) {c c' : Nat}
    {t : Ty} {v : Val} {r : BitVec 64} (hc : cls t = some c') (hle : c' ≤ c) (hf : Fits c v)
    (hv : ValRel ι v r) : ValRel ι ((LMode.loc f).retype t v) r := by
  cases hl : f.lowered
  · rw [lmode_retypeP hl]; exact valRel_retype_le hA hc hle hf hv
  · rw [lmode_retype hl]; exact valRel_retypeL_le hA hc hle hf hv

theorem retypePre_eq : ∀ (ts : List Ty) (xs : List Val), ts.length = xs.length →
    Val.retypePre ts xs = some (List.zipWith (fun t x => x.retype t) ts xs)
  | [], [], _ => rfl
  | t :: ts, x :: xs, h => by
    simp [Val.retypePre, retypePre_eq ts xs (by simpa using h)]

/-- A tuple read at a tuple shape of as many components: componentwise. -/
theorem lmode_retype_tuple (f : Func) {ts : List Ty} {xs : List Val} (h : ts.length = xs.length) :
    (LMode.loc f).retype (.tuple ts) (.tuple xs) =
      .tuple (List.zipWith (fun t x => (LMode.loc f).retype t x) ts xs) := by
  cases hl : f.lowered
  · simp only [lmode_retypeP hl, Val.retype, retypePre_eq ts xs h]
  · simp only [lmode_retype hl]
    simp only [Val.retypeL, Val.widen, Val.retype, retypePre_widen ts xs h]

theorem lmode_retype_mem (f : Func) {mm : Mem} : (LMode.loc f).retype .mem (.mem mm) = .mem mm := by
  cases hl : f.lowered
  · rw [lmode_retypeP hl]; rfl
  · rw [lmode_retype hl]; rfl

section Read

variable {E : MatchEnv} {lc : LocCtx} {s : LocState} {b : ID} {i : Nat} {m : MState}
  {ι : Blk → Option (BitVec 64)} {P : BitVec 64 → Prop} {K : Nat → Option Nat}

/-- A register argument read at its shape (either mode): related to its machine register and
of its class. -/
theorem arg_relL (hA : AddrAgree E.ι) (hm : LocMatch E s b i m) (hinv : CoreInv ι P K s)
    {a r c k : Nat} (hh : lc.home a = some (.reg r)) (hc : cls (lc.ty a) = some c)
    (hK : r ≠ zeroReg → K r = some c)
    (hk : (r = zeroReg ∧ k = 31) ∨ (k < 31 ∧ objX? r = some (BitVec.ofNat 5 k))) :
    ∃ x, s.read lc a = .ok x ∧ ValRel E.ι x (m.rX (BitVec.ofNat 5 k)) ∧ Fits c x := by
  cases hl : lc.ctx.f.lowered
  · exact arg_relP hA hl hm hinv hh hc hK hk
  · exact arg_rel hA hl hm hinv hh hc hK hk

/-- The memory argument (either mode). -/
theorem read_memL {a : Nat} (hh : lc.home a = none) (ht : memTy (lc.ty a) = true) {mm : Mem}
    (hm : s.mem = .mem mm) : s.read lc a = .ok (.mem mm) := by
  cases hl : lc.ctx.f.lowered
  · exact read_memP hl hh ht hm
  · exact read_mem hl hh ht hm

end Read

/-! ## The return -/

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

/-- **The results of a return.** When `retBlockOK` accepts the `Ret` block `blk` (ID `b`) for the
result registers `outs`, its terminator returning `(rs, mm)` from a state `s` `LocMatch`ed to `m`
(the class map at the terminator holding of `s`) returns the contents of `outs`, related to `m`'s
registers, and `s`'s memory; in either mode. -/
theorem ret_results {E : MatchEnv} {lc : LocCtx} {kt : KTab} {P : BitVec 64 → Prop}
    {s s' : LocState} {b : ID} {blk : Block} {m : MState} {outs : List Nat} {rs : List Val}
    {mm : Mem} (hA : AddrAgree E.ι)
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
  | none => simp [hv] at hok
  | some v =>
  obtain ⟨ts, hty⟩ : ∃ ts, lc.ty c = .tuple ts := by
    cases h : lc.ty c <;> simp [hv, h] at hok
    exact ⟨_, rfl⟩
  simp only [hv, hty, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨hop, hargs⟩ := hok
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
  simp only [retArgsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hargs
  obtain ⟨⟨⟨hnargs, hnts⟩, hlast⟩, hall⟩ := hargs
  have hA1 : v.args.size = outs.length + 1 := by simpa using hnargs
  have hX1 : xs.length = v.args.size := by simpa using hlen
  have hT1 : ts.length = v.args.size := by simpa using hnts
  rw [hty, lmode_retype_tuple _ (by omega), hxv] at hx
  simp only [Val.tuple.injEq] at hx
  -- `rs ++ [mem]` componentwise
  have hrsl : rs.length = outs.length := by
    have := congrArg List.length hx
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_zipWith] at this
    omega
  have hcomp : ∀ j (hj : j < rs.length), rs[j] =
      (LMode.loc lc.ctx.f).retype (ts[j]'(by omega)) (xs[j]'(by omega)) := by
    intro j hj
    have := congrArg (·[j]?) hx
    simp only [List.getElem?_append_left hj, List.getElem?_zipWith,
      List.getElem?_eq_getElem (show j < ts.length by omega),
      List.getElem?_eq_getElem (show j < xs.length by omega), Option.some.injEq] at this
    rw [List.getElem?_eq_getElem hj] at this
    exact (Option.some.inj this).symm
  obtain ⟨mm0, hmm0, hinj⟩ := hm.mem
  refine ⟨hrsl, fun j y r hy hr => ?_, ?_⟩
  · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hy
    obtain ⟨hjo, rfl⟩ := List.getElem?_eq_some_iff.1 hr
    have hja : j < v.args.toList.length := by simp; omega
    have hz := hall ((v.args.toList[j], ts[j]'(by omega)), outs[j]) (List.mem_iff_getElem.2
      ⟨j, by simp; omega, by simp⟩)
    simp only [retArgOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hz
    obtain ⟨⟨hh, h16⟩, hcm⟩ := hz
    cases hc0 : cls (lc.ty v.args.toList[j]) with
    | none => rw [hc0] at hcm; cases hcm
    | some c0 =>
    cases hc1 : cls (ts[j]'(by omega)) with
    | none => rw [hc0, hc1] at hcm; cases hcm
    | some c1 =>
    rw [hc0, hc1] at hcm
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcm
    obtain ⟨hle, hK⟩ := hcm
    obtain ⟨x', hx', hrel, hfit⟩ := arg_relL hA hm hinv hh hc0 (fun _ => hK)
      (Or.inr ⟨by omega, objX?_low h16⟩)
    have hxj : xs[j]'(by omega) = x' := by
      have := hread j hja (by omega)
      rw [hx'] at this
      exact (Res.ok.inj this).symm
    refine ⟨h16, ?_⟩
    rw [hcomp j hj, hxj, ← rX_lt (by omega)]
    exact lmode_valRel_le hA _ hc1 hle hfit hrel
  · -- the memory: the last argument's read, the state's memory
    have hlast' : v.args.toList.getLast? = some (v.args.toList[outs.length]'(by simp; omega)) := by
      rw [List.getLast?_eq_getElem?]
      simp [hA1]
    have hlastT : ts.getLast? = some (ts[outs.length]'(by omega)) := by
      rw [List.getLast?_eq_getElem?]
      simp [hT1, hA1]
    rw [hlast', hlastT] at hlast
    simp only [Bool.and_eq_true, beq_iff_eq] at hlast
    obtain ⟨⟨hmt, hmt'⟩, hhn⟩ := hlast
    have hrd := hread outs.length (by simp; omega) (by omega)
    rw [read_memL hhn hmt hmm0] at hrd
    have hxl : xs[outs.length]'(by omega) = .mem mm0 := (Res.ok.inj hrd).symm
    have := congrArg (·[outs.length]?) hx
    simp only [List.getElem?_append_right (Nat.le_of_eq hrsl), hrsl, Nat.sub_self,
      List.getElem?_cons_zero, List.getElem?_zipWith,
      List.getElem?_eq_getElem (show outs.length < ts.length by omega),
      List.getElem?_eq_getElem (show outs.length < xs.length by omega),
      Option.some.injEq, hxl, memTy_eq hmt'] at this
    rw [lmode_retype_mem] at this
    cases this
    exact hinj

end GoFV.Proof.Obj
