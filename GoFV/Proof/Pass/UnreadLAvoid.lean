import GoFV.Proof.Pass.UnreadLRel

variable [GoFV.SSA.Sem.Addrs]

/-!
# elim unread autos on `runL`: the arm64 ops keep values avoiding frame temporaries

`Arm64.evalPure_avoids`: every pure arm64 op (`Arm64.evalPure`) on arguments that avoid a set
`U` of frame temporaries (`DAE.TempU`) has a result that avoids `U`: the register families give
integers, booleans, flags and `poison`; a pointer operand moves inside its own block
(`Arm64.addP`, `Ptr.add`) or is passed on (`Arm64.regVal`); an address computed from an integer
is no frame temporary (`Ptr.ofAddr_ne_temp`); loads decode avoiding bytes, writes write avoiding
bytes into avoiding memories. One lemma per family of `Sem/Arm64`, then one case per op.
`Val.widen` and `Val.retypeL` keep values avoiding `U` (`retypeL_avoids`).
-/

namespace GoFV.Proof.UnreadL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.DAE

variable {U : Blk → Prop}

theorem flags_av (fl : Flags) : Val.Avoids U fl.toVal :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem cmpRes_av {n : Nat} (p : BitVec n × Flags) : Val.Avoids U (Arm64.cmpRes p) :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem ofFlagBit_av (o : Option Bool) : Val.Avoids U (Val.ofFlagBit o) := by
  cases o <;> trivial

theorem invertFlags_av (f : Val) : Val.Avoids U (invertFlags f) := by
  unfold invertFlags; split
  · exact ⟨ofFlagBit_av _, ofFlagBit_av _, ofFlagBit_av _, ofFlagBit_av _, ofFlagBit_av _, trivial⟩
  · trivial

theorem res_av (ty : Ty) (r : BitVec 64) : Val.Avoids U (Arm64.res ty r) := by
  unfold Arm64.res; split <;> trivial

theorem res32_av (ty : Ty) (r : BitVec 32) : Val.Avoids U (Arm64.res32 ty r) := res_av _ _

/-- Closes `Val.Avoids U v` for a `v` built from register results, integers, booleans, flags,
`poison` and tuples or composites of those, through `if`s and `match`es. -/
syntax "avL_tac" : tactic
macro_rules
  | `(tactic| avL_tac) =>
    `(tactic| repeat' (first | exact True.intro | exact res_av _ _ | exact res32_av _ _ | exact flags_av _ | exact cmpRes_av _ | split | refine ⟨?_, ?_⟩))

theorem op1_av (ty : Ty) (f : BitVec 64 → BitVec 64) (args : List Val) :
    Val.Avoids U (Arm64.op1 ty f args) := by unfold Arm64.op1; avL_tac

theorem op2_av (ty : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64) (args : List Val) :
    Val.Avoids U (Arm64.op2 ty f args) := by unfold Arm64.op2; avL_tac

theorem op3_av (ty : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) (args : List Val) :
    Val.Avoids U (Arm64.op3 ty f args) := by unfold Arm64.op3; avL_tac

theorem op1w_av (ty : Ty) (f : BitVec 32 → BitVec 32) (args : List Val) :
    Val.Avoids U (Arm64.op1w ty f args) := by unfold Arm64.op1w; avL_tac

theorem op2w_av (ty : Ty) (f : BitVec 32 → BitVec 32 → BitVec 32) (args : List Val) :
    Val.Avoids U (Arm64.op2w ty f args) := by unfold Arm64.op2w; avL_tac

theorem op3w_av (ty : Ty) (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) (args : List Val) :
    Val.Avoids U (Arm64.op3w ty f args) := by unfold Arm64.op3w; avL_tac

theorem opSh_av (ty : Ty) (sh : Arm64.Shift) (k : Int64) (f : BitVec 64 → BitVec 64 → BitVec 64)
    (args : List Val) : Val.Avoids U (Arm64.opSh ty sh k f args) := op2_av _ _ _

theorem flags1_av (f : BitVec 64 → Flags) (args : List Val) :
    Val.Avoids U (Arm64.flags1 f args) := by unfold Arm64.flags1; avL_tac

theorem flags2_av (f : BitVec 64 → BitVec 64 → Flags) (args : List Val) :
    Val.Avoids U (Arm64.flags2 f args) := by unfold Arm64.flags2; avL_tac

theorem flags1w_av (f : BitVec 32 → Flags) (args : List Val) :
    Val.Avoids U (Arm64.flags1w f args) := by unfold Arm64.flags1w; avL_tac

theorem flags2w_av (f : BitVec 32 → BitVec 32 → Flags) (args : List Val) :
    Val.Avoids U (Arm64.flags2w f args) := by unfold Arm64.flags2w; avL_tac

theorem cmp1_av (f : BitVec 64 → BitVec 64 × Flags) (args : List Val) :
    Val.Avoids U (Arm64.cmp1 f args) := by unfold Arm64.cmp1; avL_tac

theorem cmp2_av (f : BitVec 64 → BitVec 64 → BitVec 64 × Flags) (args : List Val) :
    Val.Avoids U (Arm64.cmp2 f args) := by unfold Arm64.cmp2; avL_tac

theorem cmp1w_av (f : BitVec 32 → BitVec 32 × Flags) (args : List Val) :
    Val.Avoids U (Arm64.cmp1w f args) := by unfold Arm64.cmp1w; avL_tac

theorem cmpP_av (f : BitVec 64 → BitVec 64 → BitVec 64 × Flags) (args : List Val) :
    Val.Avoids U (Arm64.cmpP f args) := by unfold Arm64.cmpP Arm64.zClear; avL_tac

theorem cmpSh_av (f : BitVec 64 → BitVec 64 → BitVec 64 × Flags) (args : List Val) :
    Val.Avoids U (Arm64.cmpSh f args) := by unfold Arm64.cmpSh Arm64.zClear; avL_tac

theorem cmp1P_av (f : BitVec 64 → BitVec 64 × Flags) (args : List Val) :
    Val.Avoids U (Arm64.cmp1P f args) := by unfold Arm64.cmp1P Arm64.zClear; avL_tac

theorem cmp2w_av (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) (args : List Val) :
    Val.Avoids U (Arm64.cmp2w f args) := by unfold Arm64.cmp2w; avL_tac

theorem cmp_av (a b : Val) : Val.Avoids U (Arm64.cmp a b) := by unfold Arm64.cmp; avL_tac

theorem cmpArgs_av (args : List Val) :
    Val.Avoids U (match args with
      | [a, b] => Arm64.cmp a b
      | _ => .poison) := by
  split
  · exact cmp_av _ _
  · trivial

theorem cmpK_av (k : Int64) (args : List Val) :
    Val.Avoids U (match args with
      | [a] => Arm64.cmp a (.int .w64 (Arm64.imm k))
      | _ => .poison) := by
  split
  · exact cmp_av _ _
  · trivial

theorem flagsTuple_av (ty : Ty) (r : BitVec 64 × Flags) :
    Val.Avoids U (Arm64.flagsTuple ty r) :=
  ⟨res_av _ _, flags_av _, trivial⟩

theorem adds_av (ty : Ty) (args : List Val) : Val.Avoids U (Arm64.adds ty args) := by
  unfold Arm64.adds; split
  · split
    · exact flagsTuple_av _ _
    · trivial
  · trivial

theorem subs_av (ty : Ty) (args : List Val) : Val.Avoids U (Arm64.subs ty args) := by
  unfold Arm64.subs; split
  · split
    · exact flagsTuple_av _ _
    · trivial
  · trivial

theorem addsConst_av (ty : Ty) (k : Int64) (args : List Val) :
    Val.Avoids U (Arm64.addsConst ty k args) := by
  unfold Arm64.addsConst; split
  · split
    · exact flagsTuple_av _ _
    · trivial
  · trivial

theorem negs_av (ty : Ty) (args : List Val) : Val.Avoids U (Arm64.negs ty args) := by
  unfold Arm64.negs; split
  · split
    · exact flagsTuple_av _ _
    · trivial
  · trivial

theorem adcs_av (ty : Ty) (args : List Val) : Val.Avoids U (Arm64.adcs ty args) := by
  unfold Arm64.adcs; split
  · split
    · exact flagsTuple_av _ _
    · trivial
  · trivial

theorem sbcs_av (ty : Ty) (args : List Val) : Val.Avoids U (Arm64.sbcs ty args) := by
  unfold Arm64.sbcs; split
  · split
    · exact flagsTuple_av _ _
    · trivial
  · trivial

theorem adcZero_av (ty : Ty) (args : List Val) : Val.Avoids U (Arm64.adcZero ty args) := by
  unfold Arm64.adcZero; avL_tac

theorem ngcZero_av (ty : Ty) (args : List Val) : Val.Avoids U (Arm64.ngcZero ty args) := by
  unfold Arm64.ngcZero; avL_tac

theorem csetm_av (ty : Ty) (k : Int64) (args : List Val) : Val.Avoids U (Arm64.csetm ty k args) := by
  unfold Arm64.csetm; avL_tac

theorem cset_av (ty : Ty) (op : Op) (args : List Val) : Val.Avoids U (Arm64.cset ty op args) := by
  unfold Arm64.cset; avL_tac

theorem ccmp_av (neg w32 konst : Bool) (k : Int64) (args : List Val) :
    Val.Avoids U (Arm64.ccmp neg w32 konst k args) := by
  unfold Arm64.ccmp; dsimp only; avL_tac

theorem regVal_av (ty : Ty) {v : Val} (h : Val.Avoids U v) : Val.Avoids U (Arm64.regVal ty v) := by
  cases v with
  | ptr p => exact h
  | _ => unfold Arm64.regVal; avL_tac

theorem csel_av (ty : Ty) (k : Int64) (g : Option (BitVec 64 → BitVec 64)) {args : List Val}
    (h : ∀ z ∈ args, Val.Avoids U z) : Val.Avoids U (Arm64.csel ty k g args) := by
  match args, h with
  | [x, y, f], h =>
    unfold Arm64.csel; dsimp only
    split
    · exact regVal_av _ (h x (by simp))
    · split
      · exact regVal_av _ (h y (by simp))
      · split
        · exact res_av _ _
        · trivial
    · trivial
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => unfold Arm64.csel; trivial

theorem csel0_av (ty : Ty) (k : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Arm64.csel0 ty k args) := by
  match args, h with
  | [x, f], h =>
    unfold Arm64.csel0; dsimp only
    split
    · exact regVal_av _ (h x (by simp))
    · exact res_av _ _
    · trivial
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ => unfold Arm64.csel0; trivial

theorem add_ptr_blk (p : Ptr) (k : BitVec 64) : (p.add k).blk = p.blk := rfl

theorem addP_av (ty : Ty) {a : Val} (h : Val.Avoids U a) (k : BitVec 64) :
    Val.Avoids U (Arm64.addP ty a k) := by
  cases a with
  | ptr p => exact ptrRes_avoids (by rw [add_ptr_blk]; exact h)
  | _ => unfold Arm64.addP; avL_tac

theorem madd_av (ty : Ty) (n : Bool) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Arm64.madd ty n args) := by
  match args, h with
  | [a, x, y], h =>
    unfold Arm64.madd; dsimp only
    split
    · exact addP_av _ (h a (by simp)) _
    · trivial
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => unfold Arm64.madd; trivial

theorem csinc_av (ty : Ty) (k : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Arm64.csinc ty k args) := by
  match args, h with
  | [x, y, f], h =>
    unfold Arm64.csinc; dsimp only
    split
    · exact regVal_av _ (h x (by simp))
    · exact regVal_av _ (addP_av _ (h y (by simp)) _)
    · trivial
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => unfold Arm64.csinc; trivial

/-- Closes `Val.Avoids U (PtrOps.ptrRes (p.add k))` from a hypothesis `Val.Avoids U (.ptr p)`. -/
theorem ptrResAdd_av {p : Ptr} (h : Val.Avoids U (.ptr p)) (k : BitVec 64) :
    Val.Avoids U (PtrOps.ptrRes (p.add k)) :=
  ptrRes_avoids (by rw [add_ptr_blk]; exact h)

theorem add_av (ty : Ty) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Arm64.add ty args) := by
  unfold Arm64.add
  split
  · exact op2_av _ _ _
  · split
    · exact ptrResAdd_av (h _ (by simp)) _
    · trivial
  · split
    · exact ptrResAdd_av (h _ (by simp)) _
    · trivial
  · exact op2_av _ _ _

theorem sub_av (ty : Ty) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Arm64.sub ty args) := by
  unfold Arm64.sub
  split
  · avL_tac
  · split
    · exact ptrResAdd_av (h _ (by simp)) _
    · trivial
  · exact op2_av _ _ _

theorem addK_av (ty : Ty) (k : BitVec 64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Arm64.addK ty k args) := by
  match args, h with
  | [a], h => exact addP_av ty (h a (by simp)) k
  | [], _ | _ :: _ :: _, _ => unfold Arm64.addK; trivial

theorem addSh_av (ty : Ty) (sh : Arm64.Shift) (k : Int64) {args : List Val}
    (h : ∀ z ∈ args, Val.Avoids U z) : Val.Avoids U (Arm64.addSh ty sh k args) := by
  match args, h with
  | [a, b], h =>
    unfold Arm64.addSh; dsimp only; split
    · exact addP_av ty (h a (by simp)) _
    · trivial
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ => unfold Arm64.addSh; trivial

theorem subSh_av (ty : Ty) (sh : Arm64.Shift) (k : Int64) {args : List Val}
    (h : ∀ z ∈ args, Val.Avoids U z) : Val.Avoids U (Arm64.subSh ty sh k args) := by
  match args, h with
  | [a, b], h =>
    unfold Arm64.subSh; dsimp only; split
    · exact addP_av ty (h a (by simp)) _
    · trivial
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ => unfold Arm64.subSh; trivial

/-! ## Floats -/

theorem fbin_av (g : (f : IEEE.Fmt) → IEEE.Bits f → IEEE.Bits f → IEEE.Bits f) (w : Width)
    (args : List Val) : Val.Avoids U (FOps.bin g w args) := by
  unfold FOps.bin; split
  · exact int2_avoids (fun _ _ => by trivial) _
  · exact int2_avoids (fun _ _ => by trivial) _
  · trivial

theorem fun_av (g : (f : IEEE.Fmt) → IEEE.Bits f → IEEE.Bits f) (w : Width) (args : List Val) :
    Val.Avoids U (FOps.un g w args) := by
  unfold FOps.un; split
  · exact int1_avoids (fun _ => by trivial) _
  · exact int1_avoids (fun _ => by trivial) _
  · trivial

theorem fma_av (w : Width) (args : List Val) : Val.Avoids U (FOps.fma w args) := by
  unfold FOps.fma; split
  · exact int3_avoids (fun _ _ _ => by trivial) _
  · exact int3_avoids (fun _ _ _ => by trivial) _
  · trivial

theorem fround_av (w : Width) (args : List Val) : Val.Avoids U (FOps.round w args) :=
  int1_avoids (fun _ => by trivial) _

theorem fnmul_av (w : Width) (args : List Val) : Val.Avoids U (Arm64.fnmul w args) :=
  fun_av _ _ _

theorem fmadd_av (w : Width) (negA negN : Bool) (args : List Val) :
    Val.Avoids U (Arm64.fmadd w negA negN args) := by
  unfold Arm64.fmadd; split
  · exact fma_av _ _
  · trivial

theorem fcmp_av (w : Width) (zero : Bool) (args : List Val) : Val.Avoids U (Arm64.fcmp w zero args) := by
  cases w <;> unfold Arm64.fcmp <;> dsimp only <;>
    first | exact True.intro | exact int2_avoids (fun _ _ => by exact flags_av _) _

theorem cvtf_av (u : Bool) (w w' : Width) (args : List Val) : Val.Avoids U (Arm64.cvtf u w w' args) := by
  unfold Arm64.cvtf; split
  · split
    · unfold FOps.ofInt; split
      · exact int1_avoids (fun _ => by trivial) _
      · exact int1_avoids (fun _ => by trivial) _
      · trivial
    · trivial
  · trivial

theorem toInt_av (u : Bool) (w' w : Width) (args : List Val) : Val.Avoids U (FOps.toInt u w' w args) := by
  unfold FOps.toInt; split
  · exact int1_avoids (fun _ => by trivial) _
  · exact int1_avoids (fun _ => by trivial) _
  · trivial

theorem fcvtz_av (ty : Ty) (u : Bool) (w w' : Width) (args : List Val) :
    Val.Avoids U (Arm64.fcvtz ty u w w' args) := by
  have h0 := toInt_av (U := U) u w' w (args.map (Arm64.fval w))
  unfold Arm64.fcvtz
  generalize FOps.toInt u w' w (args.map (Arm64.fval w)) = v at h0 ⊢
  split
  · exact res_av _ _
  · exact h0

theorem fmov_av (w : Width) (ty : Ty) (args : List Val) : Val.Avoids U (Arm64.fmov w ty args) := by
  unfold Arm64.fmov; avL_tac

theorem f32to64_av (args : List Val) : Val.Avoids U (FOps.f32to64 args) := int1_avoids (fun _ => by trivial) _
theorem f64to32_av (args : List Val) : Val.Avoids U (FOps.f64to32 args) := int1_avoids (fun _ => by trivial) _

/-! ## Memory -/

theorem addr_notU (hU : TempU U) {base : Val} (h : Val.Avoids U base) (k : BitVec 64) {p : Ptr}
    (hp : Arm64.addr base k = some p) : ¬ U p.blk := by
  unfold Arm64.addr at hp
  split at hp
  · cases hp; exact h
  · simp only [Option.map_eq_some_iff] at hp
    obtain ⟨x, -, rfl⟩ := hp
    exact ofAddr_notU hU _

theorem loadN_av (hU : TempU U) (ty : Ty) (n : Nat) (signed : Bool) {m : Mem} (hm : m.Avoids U)
    {p : Ptr} (hp : ¬ U p.blk) : Val.Avoids U (Arm64.loadN ty n signed m p) := by
  unfold Arm64.loadN
  split
  · have h0 := load_avoids hU hm (.int .w64) hp
    generalize m.load (.int .w64) p = v at h0 ⊢
    split
    · exact res_av _ _
    · exact h0
  · split
    · split
      · exact res_av _ _
      · trivial
    · trivial

theorem load16_av {m : Mem} (hm : m.Avoids U) {p : Ptr} (hp : ¬ U p.blk) :
    Val.Avoids U (Arm64.load16 m p) := by
  unfold Arm64.load16
  split
  · rename_i bs hr
    exact fun x hx => read_avoids hm hr hp x (by simpa using hx)
  · trivial

theorem loadElt_av (hU : TempU U) (ty : Ty) (n : Nat) (signed : Bool) {m : Mem} (hm : m.Avoids U)
    {p : Ptr} (hp : ¬ U p.blk) : Val.Avoids U (Arm64.loadElt ty n signed m p) := by
  unfold Arm64.loadElt
  split
  · exact load16_av hm hp
  · exact loadN_av hU _ _ _ hm hp

theorem loadPair_av (hU : TempU U) (ty : Ty) (n : Nat) (signed : Bool) {m : Mem} (hm : m.Avoids U)
    {p q : Ptr} (hp : ¬ U p.blk) (hq : ¬ U q.blk) : Val.Avoids U (Arm64.loadPair ty n signed m p q) :=
  ⟨loadElt_av hU _ _ _ hm hp, loadElt_av hU _ _ _ hm hq, trivial⟩

theorem loadIdx_av (hU : TempU U) (ty : Ty) (n scale : Nat) (signed : Bool) {args : List Val}
    (h : ∀ z ∈ args, Val.Avoids U z) : Val.Avoids U (Arm64.loadIdx ty n scale signed args) := by
  unfold Arm64.loadIdx
  split
  · rename_i a i m
    have hm : m.Avoids U := h (.mem m) (by simp)
    have hs : Val.Avoids U (if scale = 1 then Arm64.add .other [a, i] else
        match Arm64.reg i with
        | some k => Arm64.add .other [a, .int .w64 (k * BitVec.ofNat 64 scale)]
        | none => .poison) := by
      split
      · exact add_av _ fun z hz => h z (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
          rcases hz with rfl | rfl <;> simp)
      · split
        · exact add_av _ fun z hz => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with rfl | rfl
            · exact h _ (by simp)
            · trivial
        · trivial
    generalize (if scale = 1 then Arm64.add .other [a, i] else
        match Arm64.reg i with
        | some k => Arm64.add .other [a, .int .w64 (k * BitVec.ofNat 64 scale)]
        | none => .poison) = s at hs ⊢
    dsimp only
    split
    · rename_i p hp
      exact loadN_av hU _ _ _ hm (addr_notU hU hs 0 hp)
    · trivial
  · trivial

theorem zero_av (hU : TempU U) (n : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Arm64.zero n args) := by
  unfold Arm64.zero
  split
  · rename_i a m
    split
    · rename_i p hp
      split
      · rename_i m' hw
        refine memAvoids_write (h (.mem m) (by simp)) hw fun _ z hz => ?_
        simp only [Array.toList_replicate, List.mem_replicate] at hz
        rw [hz.2]; trivial
      · trivial
    · trivial
  · trivial

theorem move_av (hU : TempU U) (n : Int64) {args : List Val} (h : ∀ z ∈ args, Val.Avoids U z) :
    Val.Avoids U (Arm64.move n args) := by
  unfold Arm64.move
  split
  · rename_i d s m
    have hm : m.Avoids U := h (.mem m) (by simp)
    split
    · rename_i pd ps hpd hps
      split
      · rename_i bs hr
        split
        · rename_i m' hw
          exact memAvoids_write hm hw fun _ =>
            read_avoids hm hr (addr_notU hU (h s (by simp)) 0 hps)
        · trivial
      · trivial
    · trivial
  · trivial

/-! ## Widening and lowered shaping -/

mutual
theorem widen_av : ∀ (t : Ty) {v : Val}, Val.Avoids U v → Val.Avoids U (v.widen t)
  | .int _, .int _ _, _ => by unfold Val.widen; split <;> trivial
  | .int _, .bool _, _ => trivial
  | .ptr _, .int _ _, _ => by unfold Val.widen; split <;> trivial
  | .ptr _, .bool _, _ => trivial
  | .tuple ts, .tuple vs, h => by simp only [Val.widen]; exact widenList_av ts h
  | .int _, .poison, h | .int _, .mem _, h | .int _, .tuple _, h | .int _, .ptr _, h
  | .int _, .agg _, h | .int _, .blob _, h | .int _, .empty, h => by simpa [Val.widen] using h
  | .ptr _, .poison, h | .ptr _, .mem _, h | .ptr _, .tuple _, h | .ptr _, .ptr _, h
  | .ptr _, .agg _, h | .ptr _, .blob _, h | .ptr _, .empty, h => by simpa [Val.widen] using h
  | .tuple _, .poison, h | .tuple _, .int _ _, h | .tuple _, .bool _, h | .tuple _, .mem _, h
  | .tuple _, .ptr _, h | .tuple _, .agg _, h | .tuple _, .blob _, h | .tuple _, .empty, h => by
    simpa [Val.widen] using h
  | .bool, _, h | .mem, _, h | .other, _, h | .agg _ _, _, h | .str, _, h | .slice _, _, h
  | .blob _, _, h | .empty, _, h | .opaque _, _, h => by simpa [Val.widen] using h
theorem widenList_av : ∀ (ts : List Ty) {vs : List Val}, Val.AvoidsList U vs →
    Val.AvoidsList U (Val.widenList ts vs)
  | t :: ts, v :: vs, ⟨h1, h2⟩ => ⟨widen_av t h1, widenList_av ts h2⟩
  | [], _, h => by simpa [Val.widenList] using h
  | _ :: _, [], h => by simpa [Val.widenList] using h
end

theorem retypeL_av (hU : TempU U) (t : Ty) {v : Val} (h : Val.Avoids U v) :
    Val.Avoids U (v.retypeL t) :=
  retype_avoids hU t (widen_av t h)

theorem mdRetype_av (hU : TempU U) (md : LMode) (t : Ty) {v : Val} (h : Val.Avoids U v) :
    Val.Avoids U (md.retype t v) := by
  unfold LMode.retype; split
  · exact retypeL_av hU t h
  · exact retype_avoids hU t h

/-! ## The ops `arm64Op` evaluates -/

theorem bav_append {a b : Array Byte} (ha : BAv U a) (hb : BAv U b) : BAv U (a ++ b) := by
  intro x hx
  simp only [Array.toList_append, List.mem_append] at hx
  rcases hx with hx | hx
  · exact ha x hx
  · exact hb x hx

theorem storeBytes_av (n : Nat) {v : Val} (h : Val.Avoids U v) : BAv U (Arm64.storeBytes n v) := by
  unfold Arm64.storeBytes
  split
  · exact bav_ptrBytes h
  · split
    · intro x hx; exact h x (by simpa using hx)
    · exact bav_replicate_poison _ _
  · split
    · split
      · exact bav_intBytes _ _ _
      · exact bav_replicate_poison _ _
    · exact bav_replicate_poison _ _

theorem fitPiece_av (hU : TempU U) (t : Ty) {x : Val} (h : Val.Avoids U x) :
    Val.Avoids U (fitPiece t x) := by
  unfold fitPiece
  split
  · split
    · exact h
    · exact retypeL_av hU _ h
  · split
    · exact h
    · exact retypeL_av hU _ h
  · exact retypeL_av hU _ h
  · exact retypeL_av hU _ h
  · exact h

theorem fitPieces_av (hU : TempU U) (tabs : Tables) :
    ∀ (ps : List ABIParam) {pieces : List Val}, (∀ z ∈ pieces, Val.Avoids U z) →
      ∀ z ∈ fitPieces tabs ps pieces, Val.Avoids U z
  | [], pieces, h => by simpa [fitPieces] using h
  | p :: ps, pieces, h => by
    unfold fitPieces
    split
    · exact fitPieces_av hU tabs ps h
    · intro z hz
      simp only [List.mem_append] at hz
      rcases hz with hz | hz
      · rw [List.mem_mapIdx] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        have hx : Val.Avoids U (pieces.take p.regs.size)[i] :=
          h _ (List.mem_of_mem_take (List.getElem_mem hi))
        split
        · exact fitPiece_av hU _ hx
        · exact hx
      · exact fitPieces_av hU tabs ps (fun y hy => h y (List.mem_of_mem_drop hy)) z hz

theorem atomicArgs_av (hU : TempU U) (g : Op) {argv : List Val} (h : ∀ z ∈ argv, Val.Avoids U z) :
    ∀ z ∈ atomicArgs g argv, Val.Avoids U z := by
  unfold atomicArgs
  split
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact h _ (by simp)
    · exact fitPiece_av hU _ (h _ (by simp))
    · exact h _ (by simp)
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact h _ (by simp)
    · exact fitPiece_av hU _ (h _ (by simp))
    · exact fitPiece_av hU _ (h _ (by simp))
    · exact h _ (by simp)
  · exact h

/-- What a symbol address of a value avoiding `U` points into avoids `U`. -/
def SymOK (U : Blk → Prop) (ctx : Ctx) (v : Value) : Prop :=
  ∀ (k : Int64) a p, Val.Avoids U a → symAddr ctx { v with auxInt := k } a = some p → ¬ U p.blk

theorem elim_ld (hU : TempU U) {ctx : Ctx} {v : Value} (hs : SymOK U ctx v) {a : Val}
    (ha : Val.Avoids U a) {m : Mem} (hm : m.Avoids U) (ty : Ty) (n : Nat) (sg : Bool) :
    Val.Avoids U ((symAddr ctx v a).elim .poison (Arm64.loadN ty n sg m)) := by
  cases hp : symAddr ctx v a with
  | none => trivial
  | some p => exact loadN_av hU ty n sg hm (hs _ a p ha hp)

theorem elim_ldPair (hU : TempU U) {ctx : Ctx} {v : Value} (hs : SymOK U ctx v) {a : Val}
    (ha : Val.Avoids U a) {m : Mem} (hm : m.Avoids U) (ty : Ty) (n : Nat) (sg : Bool) :
    Val.Avoids U ((pairAddr ctx v n a).elim .poison fun pq => Arm64.loadPair ty n sg m pq.1 pq.2) := by
  cases hp : pairAddr ctx v n a with
  | none => trivial
  | some pq =>
    obtain ⟨h1, h2⟩ := pairAddr_eq_some hp
    exact loadPair_av hU ty n sg hm (hs _ a _ ha h1) (hs _ a _ ha h2)

theorem elim_ld16 {ctx : Ctx} {v : Value} (hs : SymOK U ctx v) {a : Val}
    (ha : Val.Avoids U a) {m : Mem} (hm : m.Avoids U) :
    Val.Avoids U ((symAddr ctx v a).elim .poison (Arm64.load16 m)) := by
  cases hp : symAddr ctx v a with
  | none => trivial
  | some p => exact load16_av hm (hs _ a p ha hp)

theorem elim_addr {ctx : Ctx} {v : Value} (hs : SymOK U ctx v) {a : Val}
    (ha : Val.Avoids U a) : Val.Avoids U ((symAddr ctx v a).elim .poison PtrOps.ptrRes) := by
  cases hp : symAddr ctx v a with
  | none => trivial
  | some p => exact ptrRes_avoids (hs _ a p ha hp)

theorem writeRes_av {what : String} {o : Option Mem} {r : Val}
    (h : writeRes what o = .ok r) (ho : ∀ M, o = some M → M.Avoids U) : Val.Avoids U r := by
  cases o with
  | none => cases h
  | some M => cases h; exact ho M rfl

theorem storePair_av {n : Nat} {p q : Ptr} {a b : Val} {M M1 : Mem} (hm : M.Avoids U)
    (hw : Arm64.storePair n p q a b M = some M1) (ha : BAv U (Arm64.storeBytes n a))
    (hb : BAv U (Arm64.storeBytes n b)) : M1.Avoids U := by
  unfold Arm64.storePair at hw
  obtain ⟨M2, h1, h2⟩ := Option.bind_eq_some_iff.1 hw
  exact memAvoids_write (memAvoids_write hm h1 fun _ => ha) h2 fun _ => hb

end GoFV.Proof.UnreadL
