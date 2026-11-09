import GoFV.Proof.Obj.Morestack
import GoFV.SSA.Sem.Hooks
import Std.Data.HashMap.Lemmas

variable [GoFV.SSA.Sem.Addrs]

/-!
# The runtime model of `runtime.morestack` meets its contract (`morestackHook_ok`)

`MorestackOK` (`GoFV/Proof/Obj/Morestack.lean`) is the trusted contract of `runtime.morestack`
that the prologue's morestack path (`more_loop`, `obj_entry`) rests on. `morestackHook`
(`GoFV/SSA/Sem/Hooks.lean`), the hook `RtInfo.hooks` runs at `runtime.morestack` and
`runtime.morestack_noctxt`, meets it for a stack check reading `stackguard0` (`16(g)`) when the
stack can grow: `growBy > 0` and the floor `stack.lo + StackGuard` (`0(g)`) below the check's limit.
The guard it writes (`MState.withWrites`, through a hash map of the 8 bytes) is lower: `growBy`
lower, or the floor, which the failing check puts below it.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64

/-- The 8 bytes of the word `v` at `A`, as `morestackHook` writes them. -/
private def mhBytes (A v : BitVec 64) : List (BitVec 64 × BitVec 8) :=
  (List.range 8).map fun i => (A + BitVec.ofNat 64 i, v.extractLsb' (8 * i) 8)

private theorem mh_toNat_add {a : BitVec 64} {k : Nat} (h : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt h

/-- Outside the word, the writes leave the memory alone. -/
private theorem mh_other {A v a : BitVec 64} {d : BitVec 8} (hA : A.toNat + 8 ≤ 2 ^ 64)
    (ha : ¬ InWord A a) : (Std.HashMap.ofList (mhBytes A v)).getD a d = d := by
  apply Std.HashMap.getD_ofList_of_contains_eq_false
  rw [Bool.eq_false_iff]
  intro h
  simp only [mhBytes, List.map_map, List.contains_iff_mem, List.mem_map, List.mem_range,
    Function.comp_def] at h
  obtain ⟨i, hi, he⟩ := h
  apply ha
  unfold InWord
  rw [← he, mh_toNat_add (by omega)]
  exact ⟨by omega, by omega⟩

/-- In the word, the writes give `v`'s bytes. -/
private theorem mh_at {A v : BitVec 64} {d : BitVec 8} {j : Nat} (hj : j < 8) :
    (Std.HashMap.ofList (mhBytes A v)).getD (A + BitVec.ofNat 64 j) d = v.extractLsb' (8 * j) 8 := by
  apply Std.HashMap.getD_ofList_of_mem (k := A + BitVec.ofNat 64 j) (beq_self_eq_true _)
  · unfold mhBytes
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range (n := 8)).imp_of_mem fun {a b} ha hb hab => ?_
    rw [List.mem_range] at ha hb
    rw [beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    have hA := A.isLt
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    rw [h64] at this hA
    omega
  · exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

/-- The word written reads back. -/
private theorem mh_read {A v : BitVec 64} {M : Memory} :
    (readMem (fun a => (Std.HashMap.ofList (mhBytes A v)).getD a (M a)) A 8).toNat = v.toNat := by
  apply GoFV.Proof.Gen.readMem_of_bytes _ 8 A v.toNat (by have := v.isLt; simpa using this)
  intro j hj
  rw [mh_at hj]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (8 * j) = 256 ^ j by rw [Nat.pow_mul], show 2 ^ 8 = 256 from rfl]

/-- What `morestackHook` returns when the stack can grow. -/
private theorem mh_ret {R : RtInfo} {s : MState}
    (hgrow : ¬ (s.word (s.x 28 + 16)).toNat ≤ (s.word (s.x 28) + BitVec.ofNat 64 stackGuard).toNat) :
    ∃ st, morestackHook R s = .ret st (mhBytes (s.x 28 + 16)
        (if (s.word (s.x 28 + 16)).toNat ≥ (s.word (s.x 28) + BitVec.ofNat 64 stackGuard).toNat +
            R.growBy then s.word (s.x 28 + 16) - BitVec.ofNat 64 R.growBy
          else s.word (s.x 28) + BitVec.ofNat 64 stackGuard)).toArray ∧
      st.pc = s.x 30 ∧ st.sp = s.sp ∧ st.x 26 = s.x 26 ∧ st.x 28 = s.x 28 ∧ st.x 29 = s.x 29 ∧
      st.x 30 = s.x 3 ∧ st.mem = s.mem := by
  unfold morestackHook
  simp only [hgrow, ↓reduceIte]
  refine ⟨{ clobber s with
    x := fun i => if i = 30 then s.x 3 else if (i = 26 ∨ i = 28 ∨ i = 29) then s.x i
      else (clobber s).x i
    pc := s.x 30 }, ?_, rfl, rfl, by simp, by simp, by simp, by simp, rfl⟩
  congr 1
  simp only [mhBytes, List.map_toArray]

/-- **`morestackHook` meets `MorestackOK`** at the address of `runtime.morestack` or
`runtime.morestack_noctxt` (`RtInfo.hooks`), for a stack check reading `stackguard0` (`16(g)`)
of a function entered in `s0`, when the stack can grow (`growBy > 0`, the floor
`stack.lo + StackGuard` below the check's limit). -/
theorem morestackHook_ok {R : RtInfo} {code : Code} {retM tgt : BitVec 64} {az : Int}
    {s0 : MState}
    (hname : R.entry? tgt = some "runtime.morestack" ∨
      R.entry? tgt = some "runtime.morestack_noctxt")
    (hcode : code tgt = none) (hne : tgt ≠ retM) (hgrow : 0 < R.growBy)
    (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    (hfloor : (s0.word (s0.x 28)).toNat + stackGuard <
      (if az ≤ 128 then s0.sp else s0.sp + BitVec.ofInt 64 (-(az - 128))).toNat) :
    MorestackOK R.hooks code retM tgt az 16 s0 := by
  refine ⟨hcode, hne, fun s hpc hsp h28 hlo hfail => ?_⟩
  have hg' : (s.x 28).toNat + 32 ≤ 2 ^ 64 := by rw [h28]; exact hg
  have hA : (s.x 28 + 16).toNat = (s.x 28).toNat + 16 := by
    rw [BitVec.toNat_add, show (16 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
  -- the guard, the floor, the limit
  have hguard : (s.word (s.x 28 + 16)).toNat = guardOf 16 s := by
    simp [MState.word, guardOf]
  have hlim : (if az ≤ 128 then s.sp else s.sp + BitVec.ofInt 64 (-(az - 128))).toNat =
      (if az ≤ 128 then s0.sp else s0.sp + BitVec.ofInt 64 (-(az - 128))).toNat := by rw [hsp]
  have hlt : (if az ≤ 128 then s0.sp else s0.sp + BitVec.ofInt 64 (-(az - 128))).toNat < 2 ^ 64 :=
    BitVec.isLt _
  have hfl : (s.word (s.x 28) + BitVec.ofNat 64 stackGuard).toNat =
      (s.word (s.x 28)).toNat + stackGuard := by
    rw [hlo]
    exact mh_toNat_add (by omega)
  have hge : (if az ≤ 128 then s0.sp else s0.sp + BitVec.ofInt 64 (-(az - 128))).toNat ≤
      guardOf 16 s := by
    unfold CheckPasses at hfail
    rw [hlim] at hfail
    exact Nat.le_of_not_lt hfail
  have hlo' : (s.word (s.x 28)).toNat = (s0.word (s0.x 28)).toNat := by rw [hlo]
  have hng : ¬ (s.word (s.x 28 + 16)).toNat ≤
      (s.word (s.x 28) + BitVec.ofNat 64 stackGuard).toNat := by
    rw [hguard, hfl]
    omega
  obtain ⟨st, hmh, hpc', hsp', h26, h28', h29, h30, hmem⟩ := mh_ret (R := R) hng
  have hcall : R.hooks.call s = some (.ret (st.withWrites (mhBytes (s.x 28 + 16)
      (if (s.word (s.x 28 + 16)).toNat ≥ (s.word (s.x 28) + BitVec.ofNat 64 stackGuard).toNat +
          R.growBy then s.word (s.x 28 + 16) - BitVec.ofNat 64 R.growBy
        else s.word (s.x 28) + BitVec.ofNat 64 stackGuard)).toArray)) := by
    show (rtHook R s).map HookRes.out = _
    rcases hname with h | h <;> simp [rtHook, hpc, h, rtHookNamed, hmh, HookRes.out]
  have hne8 : (mhBytes (s.x 28 + 16) (if (s.word (s.x 28 + 16)).toNat ≥
      (s.word (s.x 28) + BitVec.ofNat 64 stackGuard).toNat + R.growBy then
        s.word (s.x 28 + 16) - BitVec.ofNat 64 R.growBy
      else s.word (s.x 28) + BitVec.ofNat 64 stackGuard)).toArray.isEmpty = false := by
    simp [mhBytes]
  refine ⟨_, hcall, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, ?_⟩
  all_goals simp only [MState.withWrites, hne8, Bool.false_eq_true, ↓reduceIte]
  · exact hpc'
  · exact hsp'
  · exact h26
  · exact h28'
  · exact h29
  · exact h30
  · have ha' : ¬ InWord (s.x 28 + 16) a := ha
    rw [mh_other (by omega) ha', hmem]
  · unfold guardOf
    simp only [h28']
    have hgw : (readMem s.mem (s.x 28 + 16) 8).toNat = (s.word (s.x 28 + 16)).toNat := by
      simp [MState.word]
    rw [show BitVec.ofNat 64 16 = (16 : BitVec 64) from rfl, mh_read, hgw]
    split
    · rename_i hbig
      have hgv : R.growBy ≤ (s.word (s.x 28 + 16)).toNat := by omega
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.word (s.x 28 + 16)).isLt; omega)]
        exact hgv), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := (s.word (s.x 28 + 16)).isLt; omega)]
      omega
    · rw [hfl]
      rw [hguard, hfl] at hng
      omega

end GoFV.Proof.Obj
