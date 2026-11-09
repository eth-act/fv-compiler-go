import GoFV.Proof.PureMono
import GoFV.SSA.Sem.Arm64

/-!
# The arm64 op families are monotone (issue #385)

One lemma per family of `Sem/Arm64` (`op1`…`op3w`, `flags*`, `add`/`sub`/`addP` with their
pointer cases, `cmp`, the conditional ops, the float ops): refined arguments give a refined
result. A register operand (`Arm64.reg`) of a refined argument is the operand itself unless the
argument is `poison` (or a composite), which gives `poison`; a flags operand reads its bits
(`Cond.onVal`), each a refined boolean. `GoFV.Proof.Low.armPure_mono` assembles them per op.
-/

namespace GoFV.Proof.Low.Mono

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.Sem.Arm64

variable {a b : Val} {as bs : List Val}

/-! ## Reading operands -/

theorem reg_of (h : Refines a b) {x : BitVec 64} (hx : reg a = some x) : reg b = some x := by
  cases h <;> simp_all [reg]

theorem reg32_of (h : Refines a b) {x : BitVec 32} (hx : reg32 a = some x) : reg32 b = some x := by
  unfold reg32 at *
  cases ha : reg a with
  | none => rw [ha] at hx; cases hx
  | some y => rw [ha] at hx; rw [reg_of h ha]; exact hx

theorem flagBit_cases (h : Refines a b) : a.flagBit = none ∨ b.flagBit = a.flagBit := by
  cases h <;> simp [Val.flagBit]

theorem eval_of {c : Cond} {n z cf v n' z' cf' v' : Option Bool} {r : Bool}
    (hn : n = none ∨ n' = n) (hz : z = none ∨ z' = z) (hc : cf = none ∨ cf' = cf)
    (hv : v = none ∨ v' = v) (h : c.eval n z cf v = some r) : c.eval n' z' cf' v' = some r := by
  rcases hn with rfl | rfl <;> rcases hz with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hv with rfl | rfl <;> cases c <;> simp_all [Cond.eval]

theorem onVal_of {c : Cond} {r : Bool} (h : Refines a b) (hr : c.onVal a = some r) :
    c.onVal b = some r := by
  cases h with
  | agg hl =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    all_goals first
      | (simp only [Cond.onVal] at hr; cases hr)
      | exact eval_of (flagBit_cases h1) (flagBit_cases h2) (flagBit_cases h3) (flagBit_cases h4) hr
  | _ => simp [Cond.onVal] at hr

theorem bindOnVal_of (o : Option Cond) {r : Bool} (h : Refines a b)
    (hr : o.bind (·.onVal a) = some r) : o.bind (·.onVal b) = some r := by
  cases o with
  | none => cases hr
  | some c => exact onVal_of h hr

theorem condOn_of (k : Int64) {r : Bool} (h : Refines a b) (hr : condOn k a = some r) :
    condOn k b = some r := bindOnVal_of _ h hr

/-! ## Register ops -/

theorem op1_mono (ty : Ty) (f : BitVec 64 → BitVec 64) :
    RefinesList as bs → Refines (op1 ty f as) (op1 ty f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [op1]
    cases ha : reg a with
    | none => exact .poison _
    | some x => rw [reg_of h ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem op2_mono (ty : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64) :
    RefinesList as bs → Refines (op2 ty f as) (op2 ty f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [op2]
    cases ha : reg a with
    | none => exact .poison _
    | some x =>
      cases hc : reg c with
      | none => exact .poison _
      | some y => rw [reg_of h ha, reg_of h' hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem op3_mono (ty : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) :
    RefinesList as bs → Refines (op3 ty f as) (op3 ty f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons _ (.cons _ .nil) => .poison _
  | .cons (a := a) h (.cons (a := c) h' (.cons (a := d) h'' .nil)) => by
    simp only [op3]
    cases ha : reg a with
    | none => exact .poison _
    | some x =>
      cases hc : reg c with
      | none => exact .poison _
      | some y =>
        cases hd : reg d with
        | none => exact .poison _
        | some z => rw [reg_of h ha, reg_of h' hc, reg_of h'' hd]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ (.cons _ _))) => .poison _

theorem op1w_mono (ty : Ty) (f : BitVec 32 → BitVec 32) :
    RefinesList as bs → Refines (op1w ty f as) (op1w ty f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [op1w]
    cases ha : reg32 a with
    | none => exact .poison _
    | some x => rw [reg32_of h ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem op2w_mono (ty : Ty) (f : BitVec 32 → BitVec 32 → BitVec 32) :
    RefinesList as bs → Refines (op2w ty f as) (op2w ty f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [op2w]
    cases ha : reg32 a with
    | none => exact .poison _
    | some x =>
      cases hc : reg32 c with
      | none => exact .poison _
      | some y => rw [reg32_of h ha, reg32_of h' hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem op3w_mono (ty : Ty) (f : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32) :
    RefinesList as bs → Refines (op3w ty f as) (op3w ty f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons _ (.cons _ .nil) => .poison _
  | .cons (a := a) h (.cons (a := c) h' (.cons (a := d) h'' .nil)) => by
    simp only [op3w]
    cases ha : reg32 a with
    | none => exact .poison _
    | some x =>
      cases hc : reg32 c with
      | none => exact .poison _
      | some y =>
        cases hd : reg32 d with
        | none => exact .poison _
        | some z => rw [reg32_of h ha, reg32_of h' hc, reg32_of h'' hd]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ (.cons _ _))) => .poison _

theorem opSh_mono (ty : Ty) (sh : Shift) (k : Int64) (f : BitVec 64 → BitVec 64 → BitVec 64)
    (h : RefinesList as bs) : Refines (opSh ty sh k f as) (opSh ty sh k f bs) :=
  op2_mono _ _ h

theorem flags1_mono (f : BitVec 64 → Flags) :
    RefinesList as bs → Refines (flags1 f as) (flags1 f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [flags1]
    cases ha : reg a with
    | none => exact .poison _
    | some x => rw [reg_of h ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem flags2_mono (f : BitVec 64 → BitVec 64 → Flags) :
    RefinesList as bs → Refines (flags2 f as) (flags2 f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [flags2]
    cases ha : reg a with
    | none => exact .poison _
    | some x =>
      cases hc : reg c with
      | none => exact .poison _
      | some y => rw [reg_of h ha, reg_of h' hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem flags1w_mono (f : BitVec 32 → Flags) :
    RefinesList as bs → Refines (flags1w f as) (flags1w f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [flags1w]
    cases ha : reg32 a with
    | none => exact .poison _
    | some x => rw [reg32_of h ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem flags2w_mono (f : BitVec 32 → BitVec 32 → Flags) :
    RefinesList as bs → Refines (flags2w f as) (flags2w f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [flags2w]
    cases ha : reg32 a with
    | none => exact .poison _
    | some x =>
      cases hc : reg32 c with
      | none => exact .poison _
      | some y => rw [reg32_of h ha, reg32_of h' hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem cmp1_mono (f : BitVec 64 → BitVec 64 × Flags) :
    RefinesList as bs → Refines (cmp1 f as) (cmp1 f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [cmp1]
    cases ha : reg a with
    | none => exact .poison _
    | some x => rw [reg_of h ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem cmp2_mono (f : BitVec 64 → BitVec 64 → BitVec 64 × Flags) :
    RefinesList as bs → Refines (cmp2 f as) (cmp2 f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [cmp2]
    cases ha : reg a with
    | none => exact .poison _
    | some x =>
      cases hc : reg c with
      | none => exact .poison _
      | some y => rw [reg_of h ha, reg_of h' hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem cmp1w_mono (f : BitVec 32 → BitVec 32 × Flags) :
    RefinesList as bs → Refines (cmp1w f as) (cmp1w f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [cmp1w]
    cases ha : reg32 a with
    | none => exact .poison _
    | some x => rw [reg32_of h ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem cmp2w_mono (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) :
    RefinesList as bs → Refines (cmp2w f as) (cmp2w f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [cmp2w]
    cases ha : reg32 a with
    | none => exact .poison _
    | some x =>
      cases hc : reg32 c with
      | none => exact .poison _
      | some y => rw [reg32_of h ha, reg32_of h' hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem ofFlagBit_mono {o o' : Option Bool} (h : o = none ∨ o' = o) :
    Refines (Val.ofFlagBit o) (Val.ofFlagBit o') := by
  rcases h with rfl | rfl
  · exact .poison _
  · exact Refines.refl _

theorem invertFlags5_mono {a1 a2 a3 a4 a5 b1 b2 b3 b4 b5 : Val} (h1 : Refines a1 b1)
    (h2 : Refines a2 b2) (h3 : Refines a3 b3) (h4 : Refines a4 b4) (h5 : Refines a5 b5) :
    Refines (invertFlags (.agg [a1, a2, a3, a4, a5])) (invertFlags (.agg [b1, b2, b3, b4, b5])) := by
  simp only [invertFlags]
  have e1 := flagBit_cases h1; have e2 := flagBit_cases h2; have e3 := flagBit_cases h3
  have e4 := flagBit_cases h4; have e5 := flagBit_cases h5
  generalize a1.flagBit = n at e1 ⊢; generalize b1.flagBit = n' at e1 ⊢
  generalize a2.flagBit = z at e2 ⊢; generalize b2.flagBit = z' at e2 ⊢
  generalize a3.flagBit = c at e3 ⊢; generalize b3.flagBit = c' at e3 ⊢
  generalize a4.flagBit = v at e4 ⊢; generalize b4.flagBit = v' at e4 ⊢
  generalize a5.flagBit = g at e5 ⊢; generalize b5.flagBit = g' at e5 ⊢
  refine .agg (.cons (ofFlagBit_mono e5) (.cons (ofFlagBit_mono e2) (.cons
    (ofFlagBit_mono ?_) (.cons (ofFlagBit_mono ?_) (.cons (ofFlagBit_mono e1) .nil)))))
  · rcases e3 with rfl | rfl <;> rcases e2 with rfl | rfl <;> simp
  · rcases e5 with rfl | rfl <;> rcases e1 with rfl | rfl <;> rcases e4 with rfl | rfl <;>
      rcases e2 with rfl | rfl <;> simp

/-- `invertFlags` is monotone: each bit is strict in the bits it reads. -/
theorem invertFlags_mono (h : Refines a b) : Refines (invertFlags a) (invertFlags b) := by
  cases h with
  | agg hl =>
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, _ | ⟨h5, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    all_goals first
      | exact invertFlags5_mono h1 h2 h3 h4 h5
      | (simp only [invertFlags]; exact .poison _)
  | _ => first | exact .poison _ | (simp only [invertFlags]; exact .poison _)

/-! ## Pointer cases -/

theorem regVal_mono (ty : Ty) (h : Refines a b) : Refines (regVal ty a) (regVal ty b) := by
  cases h <;> first | exact .poison _ | exact Refines.refl _

theorem addP_mono (ty : Ty) (k : BitVec 64) (h : Refines a b) :
    Refines (addP ty a k) (addP ty b k) := by
  cases h <;> first | exact .poison _ | exact Refines.refl _

theorem addK_mono (ty : Ty) (k : BitVec 64) : RefinesList as bs → Refines (addK ty k as) (addK ty k bs)
  | .nil => .poison _
  | .cons h .nil => addP_mono ty k h
  | .cons _ (.cons _ _) => .poison _

theorem addSh_mono (ty : Ty) (sh : Shift) (k : Int64) :
    RefinesList as bs → Refines (addSh ty sh k as) (addSh ty sh k bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons h (.cons (a := c) h' .nil) => by
    simp only [addSh]
    cases hc : reg c with
    | none => exact .poison _
    | some y => rw [reg_of h' hc]; exact addP_mono _ _ h
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem subSh_mono (ty : Ty) (sh : Shift) (k : Int64) :
    RefinesList as bs → Refines (subSh ty sh k as) (subSh ty sh k bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons h (.cons (a := c) h' .nil) => by
    simp only [subSh]
    cases hc : reg c with
    | none => exact .poison _
    | some y => rw [reg_of h' hc]; exact addP_mono _ _ h
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem add_mono (ty : Ty) (h : RefinesList as bs) : Refines (add ty as) (add ty bs) := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨_, _⟩⟩⟩
  · exact .poison _
  · cases h1 <;> first | exact .poison _ | exact Refines.refl _
  · cases h1 <;> cases h2 <;> first | exact .poison _ | exact Refines.refl _
  · cases h1 <;> cases h2 <;> exact .poison _

/-- An arm64 load on a refined memory refines. -/
theorem loadN_mono {m m' : Mem} (h : Mem.Refines m m') (ty : Ty) (n : Nat) (s : Bool) (p : Ptr) :
    Sem.Refines (Arm64.loadN ty n s m p) (Arm64.loadN ty n s m' p) := by
  unfold Arm64.loadN
  split
  · have hl := GoFV.SSA.Sem.load_mono h (.int .w64) p
    revert hl
    generalize m.load (.int .w64) p = x
    generalize m'.load (.int .w64) p = y
    intro hl
    cases hl <;> first | exact .poison _ | exact Sem.Refines.refl _ | (constructor; assumption)
  · split
    · rename_i w _
      have hl := GoFV.SSA.Sem.load_mono h (.int w) p
      revert hl
      generalize m.load (.int w) p = x
      generalize m'.load (.int w) p = y
      intro hl
      cases hl <;> first | exact .poison _ | exact Sem.Refines.refl _
    · exact Sem.Refines.refl _

/-- A 128-bit load (`Arm64.load16`, a blob of the 16 bytes) on a refined memory refines. -/
theorem load16_mono {m m' : Mem} (h : Mem.Refines m m') (p : Ptr) :
    Sem.Refines (Arm64.load16 m p) (Arm64.load16 m' p) := by
  unfold Arm64.load16
  cases hr : m.read p 16 with
  | none => exact .poison _
  | some bs =>
    obtain ⟨bs', hr', hb⟩ := h.read hr
    rw [hr']
    exact .blob hb

/-- One element of a pair load on a refined memory refines. -/
theorem loadElt_mono {m m' : Mem} (h : Mem.Refines m m') (ty : Ty) (n : Nat) (s : Bool)
    (p : Ptr) : Sem.Refines (Arm64.loadElt ty n s m p) (Arm64.loadElt ty n s m' p) := by
  unfold Arm64.loadElt
  split
  · exact load16_mono h p
  · exact loadN_mono h ty n s p

/-- A pair load on a refined memory refines. -/
theorem loadPair_mono {m m' : Mem} (h : Mem.Refines m m') (ty : Ty) (n : Nat) (s : Bool)
    (p q : Ptr) : Sem.Refines (Arm64.loadPair ty n s m p q) (Arm64.loadPair ty n s m' p q) :=
  .tuple (.cons (loadElt_mono h _ n s p) (.cons (loadElt_mono h _ n s q) .nil))

/-- An address read from a refined value: the same, unless the source's is undefined. -/
theorem addr_of_refines (h : Refines a b) {k : BitVec 64} {p : Ptr}
    (hp : Arm64.addr a k = some p) : Arm64.addr b k = some p := by
  cases h <;> first | exact hp | simp [Arm64.addr, reg] at hp

/-- A load at the address of a refined value, on a refined memory, refines. -/
theorem addrLoad_mono {x y : Val} (hxy : Refines x y) {m m' : Mem} (hm : Mem.Refines m m')
    (ty : Ty) (n : Nat) (s : Bool) :
    Refines (match Arm64.addr x 0 with | some p => loadN ty n s m p | none => .poison)
      (match Arm64.addr y 0 with | some p => loadN ty n s m' p | none => .poison) := by
  cases hx : Arm64.addr x 0 with
  | none => exact .poison _
  | some p => rw [addr_of_refines hxy hx]; exact loadN_mono hm ty n s p

/-- A register-indexed load (`MOV…loadidx`, `Arm64.loadIdx`) on refined arguments refines: its
address is `add` of the base and the (scaled) index. -/
theorem loadIdx_mono (ty : Ty) (n scale : Nat) (s : Bool) (h : RefinesList as bs) :
    Refines (loadIdx ty n scale s as) (loadIdx ty n scale s bs) := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨_, _⟩⟩⟩⟩
  · exact .poison _
  · simp only [loadIdx]; exact .poison _
  · simp only [loadIdx]; exact .poison _
  · rename_i a a' i i' m m'
    cases h3 with
    | mem hm =>
      simp only [loadIdx]
      by_cases hsc : scale = 1
      · simp only [hsc, ite_true]
        exact addrLoad_mono (add_mono _ (.cons h1 (.cons h2 .nil))) hm ty n s
      · simp only [hsc, ite_false]
        cases hk : reg i with
        | none => exact addrLoad_mono (.poison _) hm ty n s
        | some k =>
          rw [reg_of h2 hk]
          exact addrLoad_mono (add_mono _ (.cons h1 (.cons (Refines.refl _) .nil))) hm ty n s
    | _ => simp only [loadIdx]; exact .poison _
  · simp only [loadIdx]; exact .poison _

theorem sub_mono (ty : Ty) (h : RefinesList as bs) : Refines (sub ty as) (sub ty bs) := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨_, _⟩⟩⟩
  · exact .poison _
  · cases h1 <;> first | exact .poison _ | exact Refines.refl _
  · cases h1 <;> cases h2 <;> first | exact .poison _ | exact Refines.refl _
  · cases h1 <;> cases h2 <;> exact .poison _

theorem madd_mono (ty : Ty) (n : Bool) : RefinesList as bs → Refines (madd ty n as) (madd ty n bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons _ (.cons _ .nil) => .poison _
  | .cons ha (.cons (a := x) hx (.cons (a := y) hy .nil)) => by
    simp only [madd]
    cases hu : reg x with
    | none => exact .poison _
    | some u =>
      cases hv : reg y with
      | none => exact .poison _
      | some v => rw [reg_of hx hu, reg_of hy hv]; exact addP_mono _ _ ha
  | .cons _ (.cons _ (.cons _ (.cons _ _))) => .poison _

/-! ## Compares -/

theorem cmp_mono {c d : Val} (h : Refines a b) (h' : Refines c d) : Refines (cmp a c) (cmp b d) := by
  cases h <;> cases h' <;> first
    | exact .poison _
    | exact Refines.refl _
    | (rename_i p; cases hp : ptrReg p <;> simp only [cmp, reg, hp] <;> exact .poison _)

theorem cmpP_mono (f : BitVec 64 → BitVec 64 → BitVec 64 × Flags) :
    RefinesList as bs → Refines (cmpP f as) (cmpP f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons h (.cons h' .nil) => by
    cases h <;> cases h' <;> first
      | exact .poison _
      | exact Refines.refl _
      | (rename_i p; cases hp : ptrReg p <;> simp only [cmpP, reg, hp] <;> exact .poison _)
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem cmpSh_mono (f : BitVec 64 → BitVec 64 → BitVec 64 × Flags) :
    RefinesList as bs → Refines (cmpSh f as) (cmpSh f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons h (.cons h' .nil) => by
    cases h <;> cases h' <;> first
      | exact .poison _
      | exact Refines.refl _
      | (rename_i p; cases hp : ptrReg p <;> simp only [cmpSh, reg, hp] <;> exact .poison _)
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem cmp1P_mono (f : BitVec 64 → BitVec 64 × Flags) :
    RefinesList as bs → Refines (cmp1P f as) (cmp1P f bs)
  | .nil => .poison _
  | .cons h .nil => by
    cases h <;> first | exact .poison _ | exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

/-! ## Conditional ops -/

theorem csel_mono (ty : Ty) (k : Int64) (g : Option (BitVec 64 → BitVec 64)) :
    RefinesList as bs → Refines (csel ty k g as) (csel ty k g bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons _ (.cons _ .nil) => .poison _
  | .cons (a := x) hx (.cons (a := y) hy (.cons (a := f) hf .nil)) => by
    simp only [csel]
    cases hc : condOn k f with
    | none => exact .poison _
    | some c =>
      rw [condOn_of k hf hc]
      cases c with
      | true => exact regVal_mono _ hx
      | false =>
        cases g with
        | none => exact regVal_mono _ hy
        | some g =>
          dsimp only
          cases hr : reg y with
          | none => exact .poison _
          | some r => rw [reg_of hy hr]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ (.cons _ _))) => .poison _

theorem csinc_mono (ty : Ty) (k : Int64) : RefinesList as bs → Refines (csinc ty k as) (csinc ty k bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons _ (.cons _ .nil) => .poison _
  | .cons (a := x) hx (.cons hy (.cons (a := f) hf .nil)) => by
    simp only [csinc]
    cases hc : condOn k f with
    | none => exact .poison _
    | some c =>
      rw [condOn_of k hf hc]
      cases c with
      | true => exact regVal_mono _ hx
      | false => exact regVal_mono _ (addP_mono _ _ hy)
  | .cons _ (.cons _ (.cons _ (.cons _ _))) => .poison _

theorem csel0_mono (ty : Ty) (k : Int64) : RefinesList as bs → Refines (csel0 ty k as) (csel0 ty k bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := x) hx (.cons (a := f) hf .nil) => by
    simp only [csel0]
    cases hc : condOn k f with
    | none => exact .poison _
    | some c =>
      rw [condOn_of k hf hc]
      cases c with
      | true => exact regVal_mono _ hx
      | false => exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem csetm_mono (ty : Ty) (k : Int64) : RefinesList as bs → Refines (csetm ty k as) (csetm ty k bs)
  | .nil => .poison _
  | .cons (a := f) hf .nil => by
    simp only [csetm]
    cases hc : condOn k f with
    | none => exact .poison _
    | some c => rw [condOn_of k hf hc]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem cset_mono (ty : Ty) (op : Op) : RefinesList as bs → Refines (cset ty op as) (cset ty op bs)
  | .nil => .poison _
  | .cons (a := f) hf .nil => by
    simp only [cset]
    cases hc : (Cond.ofOp op).bind (·.onVal f) with
    | none => exact .poison _
    | some c => rw [bindOnVal_of _ hf hc]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

/-! ## Float ops -/

theorem fval_mono (w : Width) : Refines a b → Refines (fval w a) (fval w b)
  | .poison _ => .poison _
  | .int _ _ => Refines.refl _
  | .bool _ => Refines.refl _
  | .mem h => .mem h
  | .tuple h => .tuple h
  | .ptr _ => Refines.refl _
  | .agg h => .agg h
  | .blob h => .blob h
  | .empty => .empty

theorem fvals_mono (w : Width) : ∀ {as bs : List Val}, RefinesList as bs →
    RefinesList (as.map (fval w)) (bs.map (fval w))
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (fval_mono w h) (fvals_mono w t)

private theorem refinesList_snoc (c : Val) : ∀ {as bs : List Val}, RefinesList as bs →
    RefinesList (as ++ [c]) (bs ++ [c])
  | _, _, .nil => .cons (Refines.refl _) .nil
  | _, _, .cons h t => .cons h (refinesList_snoc c t)

theorem bin_mono (g : (f : IEEE.Fmt) → IEEE.Bits f → IEEE.Bits f → IEEE.Bits f) (w : Width)
    (h : RefinesList as bs) : Refines (FOps.bin g w as) (FOps.bin g w bs) := by
  cases w <;> first | exact .poison _ | exact int2_mono _ _ h

theorem un_mono (g : (f : IEEE.Fmt) → IEEE.Bits f → IEEE.Bits f) (w : Width)
    (h : RefinesList as bs) : Refines (FOps.un g w as) (FOps.un g w bs) := by
  cases w <;> first | exact .poison _ | exact int1_mono _ _ h

theorem fma_mono (w : Width) (h : RefinesList as bs) : Refines (FOps.fma w as) (FOps.fma w bs) := by
  cases w <;> first | exact .poison _ | exact int3_mono _ _ h

theorem fop_bin_mono (w : Width) (g : (f : IEEE.Fmt) → IEEE.Bits f → IEEE.Bits f → IEEE.Bits f)
    (h : RefinesList as bs) : Refines (fop w (FOps.bin g) as) (fop w (FOps.bin g) bs) :=
  bin_mono g w (fvals_mono w h)

theorem fop_un_mono (w : Width) (g : (f : IEEE.Fmt) → IEEE.Bits f → IEEE.Bits f)
    (h : RefinesList as bs) : Refines (fop w (FOps.un g) as) (fop w (FOps.un g) bs) :=
  un_mono g w (fvals_mono w h)

theorem fop_round_mono (w : Width) (h : RefinesList as bs) :
    Refines (fop w FOps.round as) (fop w FOps.round bs) :=
  int1_mono _ _ (fvals_mono w h)

theorem fop_mono_add (w : Width) (h : RefinesList as bs) : Refines (fop w FOps.add as) (fop w FOps.add bs) :=
  fop_bin_mono w _ h
theorem fop_mono_sub (w : Width) (h : RefinesList as bs) : Refines (fop w FOps.sub as) (fop w FOps.sub bs) :=
  fop_bin_mono w _ h
theorem fop_mono_mul (w : Width) (h : RefinesList as bs) : Refines (fop w FOps.mul as) (fop w FOps.mul bs) :=
  fop_bin_mono w _ h
theorem fop_mono_div (w : Width) (h : RefinesList as bs) : Refines (fop w FOps.div as) (fop w FOps.div bs) :=
  fop_bin_mono w _ h
theorem fop_mono_min (w : Width) (h : RefinesList as bs) : Refines (fop w FOps.min as) (fop w FOps.min bs) :=
  fop_bin_mono w _ h
theorem fop_mono_max (w : Width) (h : RefinesList as bs) : Refines (fop w FOps.max as) (fop w FOps.max bs) :=
  fop_bin_mono w _ h
theorem fop_mono_abs (w : Width) (h : RefinesList as bs) : Refines (fop w FOps.abs as) (fop w FOps.abs bs) :=
  fop_un_mono w _ h
theorem fop_mono_neg (w : Width) (h : RefinesList as bs) : Refines (fop w FOps.neg as) (fop w FOps.neg bs) :=
  fop_un_mono w _ h
theorem fop_mono_sqrt (w : Width) (h : RefinesList as bs) :
    Refines (fop w FOps.sqrt as) (fop w FOps.sqrt bs) :=
  fop_un_mono w _ h
theorem fop_mono_roundInt (w : Width) (rm : IEEE.RMode) (h : RefinesList as bs) :
    Refines (fop w (FOps.roundInt rm) as) (fop w (FOps.roundInt rm) bs) :=
  fop_un_mono w _ h
theorem fop_mono_round (w : Width) (h : RefinesList as bs) :
    Refines (fop w FOps.round as) (fop w FOps.round bs) :=
  fop_round_mono w h

theorem cvtsd_mono (h : RefinesList as bs) :
    Refines (FOps.f32to64 (as.map (fval .w32))) (FOps.f32to64 (bs.map (fval .w32))) :=
  int1_mono _ _ (fvals_mono _ h)
theorem cvtds_mono (h : RefinesList as bs) :
    Refines (FOps.f64to32 (as.map (fval .w64))) (FOps.f64to32 (bs.map (fval .w64))) :=
  int1_mono _ _ (fvals_mono _ h)

theorem fnmul_mono (w : Width) (h : RefinesList as bs) : Refines (fnmul w as) (fnmul w bs) :=
  un_mono _ w (.cons (fop_bin_mono w _ h) .nil)

theorem fneg_mono (w : Width) (neg : Bool) (h : Refines a b) :
    Refines (if neg then FOps.neg w [a] else a) (if neg then FOps.neg w [b] else b) := by
  cases neg
  · exact h
  · exact un_mono _ w (.cons h .nil)

theorem fmadd_mono (w : Width) (negA negN : Bool) (h : RefinesList as bs) :
    Refines (fmadd w negA negN as) (fmadd w negA negN bs) := by
  rcases h with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨_, _⟩⟩⟩⟩
  · exact .poison _
  · exact .poison _
  · exact .poison _
  · exact fma_mono w (.cons (fneg_mono w negN (fval_mono w h2))
      (.cons (fval_mono w h3) (.cons (fneg_mono w negA (fval_mono w h1)) .nil)))
  · exact .poison _

theorem fcmp_mono (w : Width) (zero : Bool) (h : RefinesList as bs) :
    Refines (fcmp w zero as) (fcmp w zero bs) := by
  have hl : RefinesList (if zero then as ++ [.int w 0] else as)
      (if zero then bs ++ [.int w 0] else bs) := by
    cases zero
    · exact h
    · exact refinesList_snoc _ h
  have hm := fvals_mono w hl
  unfold fcmp
  cases w <;> first | exact .poison _ | exact int2_mono _ _ hm

theorem cvtf_mono (unsigned : Bool) (w w' : Width) :
    RefinesList as bs → Refines (cvtf unsigned w w' as) (cvtf unsigned w w' bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [cvtf]
    cases ha : reg a with
    | none => exact .poison _
    | some x => rw [reg_of h ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem int1_pe (w : Width) (f : BitVec w.bits → Val) :
    RefinesList as bs → int1 w f as = .poison ∨ int1 w f as = int1 w f bs
  | .nil => .inl rfl
  | .cons (a := a) h .nil => by
    simp only [int1]
    cases ha : a.asInt w with
    | none => exact .inl rfl
    | some x => rw [h.asInt ha]; exact .inr rfl
  | .cons _ (.cons _ _) => .inl rfl

theorem toInt_pe (unsigned : Bool) (w' w : Width) (h : RefinesList as bs) :
    FOps.toInt unsigned w' w as = .poison ∨ FOps.toInt unsigned w' w as = FOps.toInt unsigned w' w bs := by
  cases w <;> first | exact .inl rfl | exact int1_pe _ _ h

theorem fcvtz_mono (ty : Ty) (unsigned : Bool) (w w' : Width) (h : RefinesList as bs) :
    Refines (fcvtz ty unsigned w w' as) (fcvtz ty unsigned w w' bs) := by
  unfold fcvtz
  rcases toInt_pe unsigned w' w (fvals_mono w h) with he | he <;> rw [he]
  · exact .poison _
  · exact Refines.refl _

theorem fmov_mono (w : Width) (ty : Ty) : RefinesList as bs → Refines (fmov w ty as) (fmov w ty bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [fmov]
    cases ha : reg a with
    | none => exact .poison _
    | some x => rw [reg_of h ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

end GoFV.Proof.Low.Mono
