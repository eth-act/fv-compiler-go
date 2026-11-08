import GoFV.Proof.Obj.Ex

variable [GoFV.SSA.Sem.Addrs]

/-!
# `symInsn` is the symbolic `exec` (`GoFV/Asm/CheckObjSym.lean`)

One lemma per encoding class `symInsn` models: from a state `t` that the symbolic effect `σ`
describes (`Holds`) at offset `o` of code placed at `base`, `exec` succeeds (no access in the
nil page, given `NoNil` of the resulting effect) and its state is described by the resulting
effect, with the PC where the control goes (`CtlPc`). `symInsn_sound` collects them.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.SSA.Sem.Arm64 (Shift sext)

/-! ## Registers -/

private theorem insn_ofNat_eq_iff {r : Nat} (hr : r < 32) (q : Reg) :
    BitVec.ofNat 5 r = q ↔ r = q.toNat := by
  constructor
  · rintro rfl
    rw [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hr).symm
  · rintro rfl
    simp

private theorem insn_toNat_ne {r : Reg} (h : r ≠ 31) : r.toNat ≠ 31 :=
  fun e => h (BitVec.eq_of_toNat_eq e)

private theorem insn_getX_eval {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t) {r : Nat}
    (hr : r < 31) : (σ.getX r).eval c = t.x (BitVec.ofNat 5 r) := by
  rcases Nat.lt_or_ge r 30 with h | h
  · exact (hH.x r h).symm
  · obtain rfl : r = 30 := by omega
    exact hH.x30.symm

private theorem insn_ofNat_ne {r : Nat} (hr : r < 32) (h : r ≠ 31) : BitVec.ofNat 5 r ≠ 31 :=
  fun e => h ((insn_ofNat_eq_iff hr 31).1 e)

private theorem insn_ofNat_toNat (r : Reg) : BitVec.ofNat 5 r.toNat = r := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem Holds.rX_eval {c : Ctx} {σ : Sym} {t : MState} (h : Holds c σ t) {r : Nat} (hr : r < 32) :
    (σ.rX r).eval c = t.rX (BitVec.ofNat 5 r) := by
  unfold Sym.rX MState.rX
  by_cases e : r = 31
  · subst e
    rfl
  · rw [ite_eq_right e, ite_eq_right (insn_ofNat_ne hr e), insn_getX_eval h (by omega)]

theorem Holds.rXsp_eval {c : Ctx} {σ : Sym} {t : MState} (h : Holds c σ t) {r : Nat}
    (hr : r < 32) : (σ.rXsp r).eval c = t.rXsp (BitVec.ofNat 5 r) := by
  unfold Sym.rXsp MState.rXsp
  by_cases e : r = 31
  · subst e
    exact h.sp.symm
  · rw [ite_eq_right e, ite_eq_right (insn_ofNat_ne hr e), insn_getX_eval h (by omega)]

private theorem insn_getX_cons (σ : Sym) (k r : Nat) (v : Ex) :
    Sym.getX { σ with x := (k, v) :: σ.x } r = if r = k then v else σ.getX r := by
  unfold Sym.getX
  by_cases h : r = k
  · simp [List.lookup, h]
  · have hb : (r == k) = false := by simp [h]
    simp [List.lookup, h, hb]

theorem Holds.wX_sym {c : Ctx} {σ : Sym} {t : MState} (h : Holds c σ t) {r : Nat} (hr : r < 32)
    (v : Ex) : Holds c (σ.wX r v) (t.wX (BitVec.ofNat 5 r) (v.eval c)) := by
  unfold Sym.wX MState.wX
  by_cases e : r = 31
  · subst e
    exact h
  · have e' := insn_ofNat_ne hr e
    rw [ite_eq_right e, ite_eq_right e']
    have key : ∀ q, q < 31 →
        (if BitVec.ofNat 5 q = BitVec.ofNat 5 r then v.eval c else t.x (BitVec.ofNat 5 q)) =
        (Sym.getX { σ with x := (r, v) :: σ.x } q).eval c := by
      intro q hq
      have hq' : BitVec.ofNat 5 q = BitVec.ofNat 5 r ↔ q = r := by
        rw [insn_ofNat_eq_iff (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
      rw [insn_getX_cons]
      by_cases e2 : q = r
      · rw [ite_eq_left (hq'.2 e2), ite_eq_left e2]
      · rw [ite_eq_right (fun h => e2 (hq'.1 h)), ite_eq_right e2, insn_getX_eval h hq]
    exact { x := fun q hq => key q (by omega)
            x31 := by dsimp only; rw [ite_eq_right (Ne.symm e')]; exact h.x31
            sp := h.sp, nzcv := h.nzcv, v := h.v, mem := h.mem
            x30 := key 30 (by omega) }

theorem Holds.wXsp_sym {c : Ctx} {σ : Sym} {t : MState} (h : Holds c σ t) {r : Nat}
    (hr : r < 32) (v : Ex) : Holds c (σ.wXsp r v) (t.wXsp (BitVec.ofNat 5 r) (v.eval c)) := by
  by_cases e : r = 31
  · subst e
    unfold Sym.wXsp MState.wXsp
    simp only [↓reduceIte]
    exact { x := h.x, x31 := h.x31, sp := rfl, nzcv := h.nzcv, v := h.v, mem := h.mem
            x30 := h.x30 }
  · have := h.wX_sym hr v
    have e' := insn_ofNat_ne hr e
    unfold Sym.wXsp MState.wXsp
    unfold MState.wX at this
    rw [ite_eq_right e, ite_eq_right e']
    rw [ite_eq_right e'] at this
    exact this

theorem Holds.pc {c : Ctx} {σ : Sym} {t : MState} (h : Holds c σ t) (q : BitVec 64) :
    Holds c σ { t with pc := q } :=
  { x := h.x, x31 := h.x31, sp := h.sp, nzcv := h.nzcv, v := h.v, mem := h.mem
    x30 := h.x30 }

theorem holdsCore_wX30 {c : Ctx} {σ : Sym} {tm : MState} (h : HoldsCore c σ tm) (v q : BitVec 64) :
    HoldsCore c σ { tm.wX 30 v with pc := q } := by
  obtain ⟨hx, h31, hsp, hfl, hv, hmem⟩ := h
  refine ⟨fun r hr => ?_, ?_, hsp, hfl, hv, hmem⟩
  · have : (BitVec.ofNat 5 r : Reg) ≠ 30 := by
      intro he; have := congrArg BitVec.toNat he; simp at this; omega
    have h30 : ¬ BitVec.ofNat 5 r = 30#5 := this
    simp [MState.wX, hx r hr, h30]
  · simp only [MState.wX, show ¬ ((30 : Reg) = 31) by decide, ↓reduceIte]
    exact h31

private theorem insn_rX {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t) (r : Reg) :
    (σ.rX r.toNat).eval c = t.rX r := by
  rw [hH.rX_eval r.isLt, insn_ofNat_toNat]

private theorem insn_rXsp {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t) (r : Reg) :
    (σ.rXsp r.toNat).eval c = t.rXsp r := by
  rw [hH.rXsp_eval r.isLt, insn_ofNat_toNat]

private theorem insn_holds_wX {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t) (r : Reg)
    {v : Ex} {val : BitVec 64} (hv : v.eval c = val) :
    Holds c (σ.wX r.toNat v) (t.wX r val) := by
  have := hH.wX_sym r.isLt v
  rwa [insn_ofNat_toNat, hv] at this

private theorem insn_holds_wXsp {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t) (r : Reg)
    {v : Ex} {val : BitVec 64} (hv : v.eval c = val) :
    Holds c (σ.wXsp r.toNat v) (t.wXsp r val) := by
  have := hH.wXsp_sym r.isLt v
  rwa [insn_ofNat_toNat, hv] at this

private theorem insn_holds_fl {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t) {f : Fl}
    {fl : GoFV.SSA.Sem.Flags} (hf : f.eval c = fl) :
    Holds c { σ with fl := f } { t with nzcv := fl } :=
  { x := hH.x, x31 := hH.x31, sp := hH.sp, nzcv := hf.symm, v := hH.v, mem := hH.mem
    x30 := hH.x30 }

private theorem insn_holds_pc {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t)
    (p : BitVec 64) : Holds c σ { t with pc := p } := hH.pc p

private theorem insn_holds_loads {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t)
    (l : List (Ex × Nat)) : Holds c { σ with loads := l } t :=
  { x := hH.x, x31 := hH.x31, sp := hH.sp, nzcv := hH.nzcv, v := hH.v, mem := hH.mem
    x30 := hH.x30 }

private theorem insn_storesMem_append (c : Ctx) (st : List (Ex × Nat × Ex)) (a : Ex) (n : Nat)
    (v : Ex) (m : Memory) :
    storesMem c (st ++ [(a, n, v)]) m =
      writeMem (storesMem c st m) (a.eval c) n ((v.eval c).setWidth (8 * n)) := by
  induction st generalizing m with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨a', n', v'⟩ := p
    exact ih _

private theorem insn_holds_store {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t) (a : Ex)
    (n : Nat) {v : Ex} {val : BitVec (8 * n)} (hv : (v.eval c).setWidth (8 * n) = val) :
    Holds c (σ.store a n v) { t with mem := writeMem t.mem (a.eval c) n val } :=
  { x := hH.x, x31 := hH.x31, sp := hH.sp, nzcv := hH.nzcv, v := hH.v, x30 := hH.x30
    mem := by
      show writeMem t.mem _ n val = storesMem c (σ.stores ++ [(a, n, v)]) c.s.mem
      rw [insn_storesMem_append, ← hH.mem, hv] }

@[simp] private theorem insn_wX_pc (t : MState) (r : Reg) (v : BitVec 64) : (t.wX r v).pc = t.pc := by
  unfold MState.wX; split <;> rfl

@[simp] private theorem insn_wXsp_pc (t : MState) (r : Reg) (v : BitVec 64) :
    (t.wXsp r v).pc = t.pc := by
  unfold MState.wXsp; split <;> rfl

@[simp] private theorem insn_wX_loads (σ : Sym) (r : Nat) (v : Ex) : (σ.wX r v).loads = σ.loads := by
  unfold Sym.wX; split <;> rfl

@[simp] private theorem insn_wX_stores (σ : Sym) (r : Nat) (v : Ex) :
    (σ.wX r v).stores = σ.stores := by
  unfold Sym.wX; split <;> rfl

@[simp] private theorem insn_wXsp_loads (σ : Sym) (r : Nat) (v : Ex) :
    (σ.wXsp r v).loads = σ.loads := by
  unfold Sym.wXsp; split
  · rfl
  · exact insn_wX_loads σ r v

@[simp] private theorem insn_wXsp_stores (σ : Sym) (r : Nat) (v : Ex) :
    (σ.wXsp r v).stores = σ.stores := by
  unfold Sym.wXsp; split
  · rfl
  · exact insn_wX_stores σ r v

/-! ## The PC -/

private theorem insn_at_fall (base : BitVec 64) (o : Nat) :
    at_ base ((o : Int) + 4) = base + BitVec.ofNat 64 o + 4 := by
  unfold at_
  rw [show ((o : Int) + 4) = ((o + 4 : Nat) : Int) by push_cast; rfl,
    BitVec.ofInt_natCast, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

private theorem insn_fall {c : Ctx} {σ : Sym} {t t' : MState} {base : BitVec 64} {o : Nat}
    (hpc : t.pc = base + BitVec.ofNat 64 o) (hH : Holds c σ t') (hp : t'.pc = t.pc) :
    Holds c σ t'.next ∧ CtlPc c base o .fall t'.next := by
  refine ⟨insn_holds_pc hH _, ?_⟩
  show t'.pc + 4 = at_ base ((o : Int) + 4)
  rw [hp, hpc, insn_at_fall]

private theorem insn_rel_toInt {k : Nat} (imm : BitVec k) :
    (imm ++ (0 : BitVec 2)).toInt = 4 * imm.toInt := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  have h1 : (imm ++ (0 : BitVec 2)).toNat = imm.toNat * 4 := by
    rw [BitVec.toNat_append, Nat.shiftLeft_eq]
    simp
  have hp : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [Nat.pow_add]
  rw [h1, hp]
  have := imm.isLt
  generalize imm.toNat = a at *
  generalize 2 ^ k = P at *
  split <;> split <;> omega

private theorem insn_at_rel {k : Nat} (base : BitVec 64) (o : Nat) (imm : BitVec k) :
    at_ base (relOff o imm) = base + BitVec.ofNat 64 o + (imm ++ (0 : BitVec 2)).signExtend 64 := by
  unfold at_ relOff BitVec.signExtend
  rw [insn_rel_toInt, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]

private theorem insn_pcRel {t : MState} {base : BitVec 64} {o : Nat}
    (hpc : t.pc = base + BitVec.ofNat 64 o) {k : Nat} (imm : BitVec k) :
    t.pcRel imm = at_ base (relOff o imm) := by
  rw [insn_at_rel, MState.pcRel, hpc]

private theorem insn_branchIf_pc (s : MState) (b : Bool) (p : BitVec 64) :
    (s.branchIf b p).pc = if b then p else s.pc + 4 := by
  unfold MState.branchIf
  cases b <;> rfl

private theorem insn_holds_branchIf {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t) (b : Bool)
    (p : BitVec 64) : Holds c σ (t.branchIf b p) := by
  unfold MState.branchIf
  cases b
  · exact hH.pc _
  · exact hH.pc _

private theorem insn_sized_id (sf : Bool) (x : BitVec 64) :
    (sized sf fun _ e => e x) = ProgOp.trunc sf x := by
  cases sf <;> simp [sized, ProgOp.trunc]

/-! ## One lemma per encoding class -/

private theorem insn_addSubImm {sf sub setf sh : Bool} {imm12 : BitVec 12} {rn rd : Reg} {o : Nat}
    {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.addSubImm sf sub setf sh imm12 rn rd) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.addSubImm sf sub setf sh imm12 rn rd) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  cases setf
  · cases h
    exact ⟨_, rfl, insn_fall hpc (insn_holds_wXsp hH rd
      (by rw [Ex.eval_mkAddSub, insn_rXsp hH]; rfl))
      (insn_wXsp_pc _ _ _)⟩
  · cases h
    exact ⟨_, rfl, insn_fall hpc (insn_holds_fl (insn_holds_wX hH rd
      (by rw [Ex.eval_mkAddSub, insn_rXsp hH]; rfl)) (by rw [Fl.eval_mkAddSub, insn_rXsp hH]; rfl))
      (insn_wX_pc _ _ _)⟩

private theorem insn_logImm {sf : Bool} {opc : BitVec 2} {n : Bool} {immr imms : BitVec 6}
    {rn rd : Reg} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.logImm sf opc n immr imms rn rd) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.logImm sf opc n immr imms rn rd) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  delta symInsn at h
  dsimp only at h
  cases hd : decodeBitMasks (if sf then 64 else 32) n imms immr true with
  | none =>
    rw [hd] at h
    cases h
  | some p =>
    obtain ⟨w, w'⟩ := p
    rw [hd] at h
    dsimp only at h
    have ex : exec (.logImm sf opc n immr imms rn rd) t = pure (if opc = 3 then
        { t.wX rd (logical sf opc (t.rX rn) (w.setWidth 64)).1 with
          nzcv := (logical sf opc (t.rX rn) (w.setWidth 64)).2 }
        else t.wXsp rd (logical sf opc (t.rX rn) (w.setWidth 64)).1).next := by
      delta exec
      dsimp only
      rw [hd]
    rw [ex]
    by_cases ho : opc = 3
    · subst ho
      cases h
      exact ⟨_, rfl, insn_fall hpc (insn_holds_fl (insn_holds_wX hH rd
        (by rw [Ex.eval_mkLogical, insn_rX hH]; rfl)) (by rw [Fl.eval_mkAnds, insn_rX hH]; rfl))
        (insn_wX_pc _ _ _)⟩
    · simp only [ho, ↓reduceIte] at h ⊢
      cases h
      exact ⟨_, rfl, insn_fall hpc (insn_holds_wXsp hH rd
        (by rw [Ex.eval_mkLogical, insn_rX hH]; rfl)) (insn_wXsp_pc _ _ _)⟩

/-- `MOVK` (`opc` 01 or 11: `exec` and `symInsn` both take their last alternative). -/
private theorem insn_movk {sf : Bool} {opc hw : BitVec 2} {imm16 : BitVec 16} {rd : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.movWide sf opc hw imm16 rd) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) (h0 : opc.toNat ≠ 0) (h2 : opc.toNat ≠ 2) :
    ∃ t', exec (.movWide sf opc hw imm16 rd) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  delta symInsn at h
  dsimp only at h
  split at h
  · contradiction
  · contradiction
  · split at h
    next old heq =>
      cases h
      have hold : old = t.rX rd := by
        have := insn_rX hH rd
        rw [heq] at this
        exact this
      subst hold
      have ex : exec (.movWide sf opc hw imm16 rd) t = pure (t.wX rd (sized sf fun _ e =>
          e ((t.rX rd &&& ~~~((0xFFFF : BitVec 64) <<< (16 * hw.toNat))) |||
            (imm16.setWidth 64 <<< (16 * hw.toNat))))).next := by
        delta exec
        dsimp only
        split
        · contradiction
        · contradiction
        · rfl
      exact ⟨_, ex, insn_fall hpc (insn_holds_wX hH rd rfl) (insn_wX_pc _ _ _)⟩
    next => cases h

private theorem insn_movWide {sf : Bool} {opc hw : BitVec 2} {imm16 : BitVec 16} {rd : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.movWide sf opc hw imm16 rd) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.movWide sf opc hw imm16 rd) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  rcases opc with ⟨⟨_ | _ | _ | _ | k, hk⟩⟩
  · cases h
    exact ⟨_, rfl, insn_fall hpc (insn_holds_wX hH rd rfl) (insn_wX_pc _ _ _)⟩
  · exact insn_movk h hH hpc (by intro e; cases e) (by intro e; cases e)
  · cases h
    exact ⟨_, rfl, insn_fall hpc (insn_holds_wX hH rd rfl) (insn_wX_pc _ _ _)⟩
  · exact insn_movk h hH hpc (by intro e; cases e) (by intro e; cases e)
  · exact absurd hk (by omega)

private theorem insn_bitfield {sf : Bool} {opc : BitVec 2} {immr imms : BitVec 6} {rn rd : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.bitfield sf opc immr imms rn rd) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.bitfield sf opc immr imms rn rd) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  cases h
  exact ⟨_, rfl, insn_fall hpc (insn_holds_wX hH rd
    (by rw [Ex.eval_mkBfm, insn_rX hH, insn_rX hH])) (insn_wX_pc _ _ _)⟩

private theorem insn_b {link : Bool} {imm26 : BitVec 26}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.b link imm26) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.b link imm26) t = .ok t' ∧ Holds c σ' t' ∧ CtlPc c base o mc t' := by
  cases link
  · cases h
    exact ⟨_, rfl, hH.pc _, insn_pcRel hpc imm26⟩
  · cases h

private theorem insn_bcond {cond : BitVec 4} {imm19 : BitVec 19}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.bcond cond imm19) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.bcond cond imm19) t = .ok t' ∧ Holds c σ' t' ∧ CtlPc c base o mc t' := by
  cases h
  refine ⟨_, rfl, insn_holds_branchIf hH _ _, ?_⟩
  show (t.branchIf _ _).pc = _
  rw [insn_branchIf_pc, insn_pcRel hpc, insn_at_fall, MState.holds, hH.nzcv, hpc]

private theorem insn_cbz {sf nz : Bool} {imm19 : BitVec 19} {rt : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.cbz sf nz imm19 rt) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.cbz sf nz imm19 rt) t = .ok t' ∧ Holds c σ' t' ∧ CtlPc c base o mc t' := by
  cases h
  refine ⟨_, rfl, insn_holds_branchIf hH _ _, ?_⟩
  show (t.branchIf _ _).pc = _
  rw [insn_branchIf_pc, insn_pcRel hpc, insn_at_fall, insn_sized_id, insn_rX hH, hpc]

private theorem insn_tbz {nz : Bool} {b : BitVec 6} {imm14 : BitVec 14} {rt : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.tbz nz b imm14 rt) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.tbz nz b imm14 rt) t = .ok t' ∧ Holds c σ' t' ∧ CtlPc c base o mc t' := by
  cases h
  refine ⟨_, rfl, insn_holds_branchIf hH _ _, ?_⟩
  show (t.branchIf _ _).pc = _
  rw [insn_branchIf_pc, insn_pcRel hpc, insn_at_fall, insn_rX hH, hpc]

private theorem insn_br {kind : BrKind} {rn : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.br kind rn) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.br kind rn) t = .ok t' ∧ WordsPost c base o σ' mc t' := by
  cases kind
  · cases h
    exact ⟨_, rfl, (hH.pc _).toHoldsCore, fun _ => (hH.pc _).x30, (insn_rX hH rn).symm⟩
  · cases h
    have ex : exec (.br .blr rn) t = .ok { t.wX 30 (t.pc + 4) with pc := t.rX rn } := rfl
    refine ⟨_, ex, holdsCore_wX30 hH.toHoldsCore _ _, fun h => by simp [MCtl.links] at h,
      ⟨(insn_rX hH rn).symm, ?_⟩⟩
    show (t.wX 30 (t.pc + 4)).x 30 = _
    simp only [MState.wX, show (30 : Reg) ≠ 31 by decide, ↓reduceIte, hpc]
    exact (insn_at_fall base o).symm
  · cases h
    exact ⟨_, rfl, (hH.pc _).toHoldsCore, fun _ => (hH.pc _).x30, (insn_rX hH rn).symm⟩

private theorem insn_nop {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    {base : BitVec 64} (h : symInsn .nop o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec .nop t = .ok t' ∧ Holds c σ' t' ∧ CtlPc c base o mc t' := by
  cases h
  exact ⟨_, rfl, insn_fall hpc hH rfl⟩

private theorem insn_barrier {op2 : BitVec 3} {crm : BitVec 4} {o : Nat} {σ σ' : Sym} {mc : MCtl}
    {c : Ctx} {t : MState} {base : BitVec 64} (h : symInsn (.barrier op2 crm) o σ = .ok (σ', mc))
    (hH : Holds c σ t) (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.barrier op2 crm) t = .ok t' ∧ Holds c σ' t' ∧ CtlPc c base o mc t' := by
  cases h
  exact ⟨_, rfl, insn_fall hpc hH rfl⟩

private theorem insn_logShift {sf : Bool} {opc shift : BitVec 2} {n : Bool} {rm : Reg}
    {imm6 : BitVec 6} {rn rd : Reg} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    {base : BitVec 64} (h : symInsn (.logShift sf opc shift n rm imm6 rn rd) o σ = .ok (σ', mc))
    (hH : Holds c σ t) (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.logShift sf opc shift n rm imm6 rn rd) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  cases n
  · rcases opc with ⟨⟨_ | _ | _ | _ | k, hk⟩⟩
    · cases h
      exact ⟨_, rfl, insn_fall hpc (insn_holds_wX hH rd
        (by rw [Ex.eval_mkLogical, Ex.eval_mkShift, insn_rX hH, insn_rX hH] <;> rfl))
        (insn_wX_pc _ _ _)⟩
    · cases h
      exact ⟨_, rfl, insn_fall hpc (insn_holds_wX hH rd
        (by rw [Ex.eval_mkLogical, Ex.eval_mkShift, insn_rX hH, insn_rX hH] <;> rfl))
        (insn_wX_pc _ _ _)⟩
    · cases h
      exact ⟨_, rfl, insn_fall hpc (insn_holds_wX hH rd
        (by rw [Ex.eval_mkLogical, Ex.eval_mkShift, insn_rX hH, insn_rX hH] <;> rfl))
        (insn_wX_pc _ _ _)⟩
    · cases h
      exact ⟨_, rfl, insn_fall hpc (insn_holds_fl (insn_holds_wX hH rd
        (by rw [Ex.eval_mkLogical, Ex.eval_mkShift, insn_rX hH, insn_rX hH] <;> rfl))
        (by rw [Fl.eval_mkAnds, Ex.eval_mkShift, insn_rX hH, insn_rX hH] <;> rfl))
        (insn_wX_pc _ _ _)⟩
    · exact absurd hk (by omega)
  · cases h

private theorem insn_addSubShift {sf sub setf : Bool} {shift : BitVec 2} {rm : Reg}
    {imm6 : BitVec 6} {rn rd : Reg} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    {base : BitVec 64}
    (h : symInsn (.addSubShift sf sub setf shift rm imm6 rn rd) o σ = .ok (σ', mc))
    (hH : Holds c σ t) (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.addSubShift sf sub setf shift rm imm6 rn rd) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  cases setf
  · cases h
    exact ⟨_, rfl, insn_fall hpc (insn_holds_wX hH rd
      (by rw [Ex.eval_mkAddSub, Ex.eval_mkShift, insn_rX hH, insn_rX hH] <;> rfl))
      (insn_wX_pc _ _ _)⟩
  · cases h
    exact ⟨_, rfl, insn_fall hpc (insn_holds_fl (insn_holds_wX hH rd
      (by rw [Ex.eval_mkAddSub, Ex.eval_mkShift, insn_rX hH, insn_rX hH] <;> rfl))
      (by rw [Fl.eval_mkAddSub, Ex.eval_mkShift, insn_rX hH, insn_rX hH] <;> rfl))
      (insn_wX_pc _ _ _)⟩

private theorem insn_addSubExt {sf sub setf : Bool} {rm : Reg} {option : BitVec 3}
    {imm3 : BitVec 3} {rn rd : Reg} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    {base : BitVec 64}
    (h : symInsn (.addSubExt sf sub setf rm option imm3 rn rd) o σ = .ok (σ', mc))
    (hH : Holds c σ t) (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.addSubExt sf sub setf rm option imm3 rn rd) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  cases setf
  · cases h
    exact ⟨_, rfl, insn_fall hpc (insn_holds_wXsp hH rd
      (by rw [Ex.eval_mkAddSub, Ex.eval_mkExt, insn_rXsp hH, insn_rX hH] <;> rfl))
      (insn_wXsp_pc _ _ _)⟩
  · cases h
    exact ⟨_, rfl, insn_fall hpc (insn_holds_fl (insn_holds_wX hH rd
      (by rw [Ex.eval_mkAddSub, Ex.eval_mkExt, insn_rXsp hH, insn_rX hH] <;> rfl))
      (by rw [Fl.eval_mkAddSub, Ex.eval_mkExt, insn_rXsp hH, insn_rX hH] <;> rfl))
      (insn_wX_pc _ _ _)⟩

/-! ### Loads and stores -/

private theorem insn_loadInto {c : Ctx} (t : MState) (opc : BitVec 2) (n : Nat) (rt : Reg)
    (d : BitVec (8 * n)) {v : Ex} (hv : v.eval c = d.setWidth 64) :
    t.loadInto false opc n rt d = t.wX rt ((loadVal opc n v).eval c) := by
  rcases opc with ⟨⟨_ | _ | _ | _ | k, hk⟩⟩
  · show t.wX rt (d.setWidth 64) = t.wX rt (v.eval c)
    rw [hv]
  · show t.wX rt (d.setWidth 64) = t.wX rt (v.eval c)
    rw [hv]
  · show t.wX rt (sext (8 * n) (d.setWidth 64)) = t.wX rt ((Ex.mkSext (8 * n) v).eval c)
    rw [Ex.eval_mkSext, hv]
  · show t.wX rt ((sext (8 * n) (d.setWidth 64)).setWidth 32 |>.setWidth 64) =
      t.wX rt ((Ex.mkTrunc false (Ex.mkSext (8 * n) v)).eval c)
    rw [Ex.eval_mkTrunc, Ex.eval_mkSext, hv] <;> rfl
  · exact absurd hk (by omega)

private theorem insn_amode {c : Ctx} {σ : Sym} {t : MState} (hH : Holds c σ t) (mode : AMode)
    (rn : Reg) (n : Nat) :
    t.amode mode rn n = ((amodeSym σ mode rn.toNat n).1.eval c,
      (amodeSym σ mode rn.toNat n).2.map (Ex.eval c)) := by
  cases mode with
  | uimm imm12 =>
    simp only [MState.amode, amodeSym, Ex.eval_mkAdd, insn_rXsp hH, Option.map_none] <;> rfl
  | simm imm9 idx =>
    cases idx <;>
      simp only [MState.amode, amodeSym, Ex.eval_mkAdd, insn_rXsp hH, Option.map_some,
        Option.map_none] <;> rfl
  | reg rm option sc =>
    simp only [MState.amode, amodeSym, Ex.eval_mkAdd, Ex.eval_mkExt, insn_rXsp hH, insn_rX hH,
      Option.map_none] <;> rfl

private theorem insn_access {σ σ1 : Sym} {c : Ctx} {t : MState} {size opc : BitVec 2} {rt : Nat}
    {a : Ex} {mode : AMode} {rn : Reg} {wbv : Option (BitVec 64)}
    (h : symAccess σ size opc rt a = .ok σ1) (hH : Holds c σ t) (hrt : rt < 32)
    (hA : t.amode mode rn (bytesOf size) = (a.eval c, wbv)) (hnil : NoNil c σ1) :
    ∃ t1, Holds c σ1 t1 ∧ t1.pc = t.pc ∧
      execLdSt t size false opc mode rn (BitVec.ofNat 5 rt) =
        .ok (match wbv with | some b => t1.wXsp rn b | none => t1).next := by
  have hA' : t.amode mode rn (accessBytes size false opc) = (a.eval c, wbv) := hA
  unfold symAccess Sym.load at h
  unfold execLdSt
  simp only [hA', Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  cases hp : (size = 3 && opc = 2)
  · rw [hp] at h
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases ho : (opc != 0)
    · rw [ho] at h
      cases h
      have hna : nilPage (a.eval c) = false :=
        hnil.2 a (bytesOf size) (σ.rX rt) (by simp [Sym.store])
      have hst := insn_holds_store hH a (bytesOf size)
        (val := (t.rX (BitVec.ofNat 5 rt)).setWidth (8 * bytesOf size)) (by rw [hH.rX_eval hrt])
      refine ⟨_, hst, rfl, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte, store, hna, bind, Except.bind, pure,
        Except.pure]
      rfl
    · rw [ho] at h
      cases hs : σ.stores.isEmpty
      · rw [hs] at h
        cases h
      · rw [hs] at h
        cases h
        have hs' : σ.stores = [] := List.isEmpty_iff.mp hs
        have hna : nilPage (a.eval c) = false := hnil.1 a (bytesOf size) (by simp)
        have hmem : t.mem = c.s.mem := by rw [hH.mem, hs']; rfl
        have hl := insn_loadInto t opc (bytesOf size) (BitVec.ofNat 5 rt)
          (readMem t.mem (a.eval c) (bytesOf size)) (v := .ld (bytesOf size) a)
          (by rw [hmem] <;> rfl)
        refine ⟨t.loadInto false opc (bytesOf size) (BitVec.ofNat 5 rt)
          (readMem t.mem (a.eval c) (bytesOf size)), ?_, ?_, ?_⟩
        · rw [hl]
          exact (insn_holds_loads hH _).wX_sym hrt _
        · rw [hl, insn_wX_pc]
        · simp only [↓reduceIte, load, hna, Bool.false_eq_true, bind, Except.bind, pure,
            Except.pure]
          rfl
  · rw [hp] at h
    cases h

theorem symAccess_exec {σ σ' : Sym} {c : Ctx} {t : MState} {size opc : BitVec 2} {rt : Nat}
    {a : Ex} {mode : AMode} {rn : Reg} (h : symAccess σ size opc rt a = .ok σ') (hH : Holds c σ t)
    (hrt : rt < 32) (haddr : (t.amode mode rn (bytesOf size)).1 = a.eval c)
    (hwb : (t.amode mode rn (bytesOf size)).2 = none) (hnil : NoNil c σ') :
    ∃ t', execLdSt t size false opc mode rn (BitVec.ofNat 5 rt) = .ok t' ∧ Holds c σ' t' ∧
      t'.pc = t.pc + 4 := by
  obtain ⟨t1, h1, hp1, he⟩ := insn_access h hH hrt (Prod.ext haddr hwb) hnil
  exact ⟨_, he, insn_holds_pc h1 _, by show t1.pc + 4 = _; rw [hp1]⟩

private theorem insn_ldst {size : BitVec 2} {vec : Bool} {opc : BitVec 2} {mode : AMode}
    {rn rt : Reg} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.ldst size vec opc mode rn rt) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) (hnil : NoNil c σ') :
    ∃ t', exec (.ldst size vec opc mode rn rt) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  cases vec
  case true => cases h
  have hA := insn_amode hH mode rn (bytesOf size)
  delta symInsn at h
  dsimp only at h
  generalize amodeSym σ mode rn.toNat (bytesOf size) = p at h hA
  obtain ⟨a, wb⟩ := p
  dsimp only at h
  cases hs : symAccess σ size opc rt.toNat a with
  | error e =>
    rw [hs] at h
    cases h
  | ok σ1 =>
    rw [hs] at h
    cases wb with
    | none =>
      cases h
      obtain ⟨t1, h1, hp1, he⟩ := insn_access hs hH rt.isLt hA hnil
      rw [insn_ofNat_toNat] at he
      exact ⟨_, he, insn_fall hpc h1 hp1⟩
    | some b =>
      cases h
      have hnil1 : NoNil c σ1 := by
        unfold NoNil at hnil ⊢
        simpa only [insn_wXsp_loads, insn_wXsp_stores] using hnil
      obtain ⟨t1, h1, hp1, he⟩ := insn_access hs hH rt.isLt hA hnil1
      rw [insn_ofNat_toNat] at he
      exact ⟨_, he, insn_fall hpc (insn_holds_wXsp h1 rn rfl)
        (by show (t1.wXsp rn (b.eval c)).pc = t.pc; rw [insn_wXsp_pc, hp1])⟩

private theorem insn_pair {opc : BitVec 2} {vec : Bool} {mode : BitVec 2} {ld : Bool}
    {imm7 : BitVec 7} {rt2 rn rt : Reg} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    {base : BitVec 64}
    (h : symInsn (.ldstPair opc vec mode ld imm7 rt2 rn rt) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) (hnil : NoNil c σ') :
    ∃ t', exec (.ldstPair opc vec mode ld imm7 rt2 rn rt) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  cases vec
  case true => cases h
  delta symInsn at h
  dsimp only at h
  show ∃ t', execPair t opc false mode ld imm7 rt2 rn rt = .ok t' ∧ _
  unfold execPair
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, decide_eq_true_eq]
    at h ⊢
  generalize (if opc.getLsbD 1 = true then 8 else 4) = n at h ⊢
  generalize hae : (if mode = 1 then σ.rXsp rn.toNat
    else Ex.mkAdd (σ.rXsp rn.toNat) (.k (imm7.signExtend 64 * BitVec.ofNat 64 n))) = a at h
  have haA : a.eval c =
      (if mode = 1 then t.rXsp rn else t.rXsp rn + imm7.signExtend 64 * BitVec.ofNat 64 n) := by
    rw [← hae]
    split <;> simp only [Ex.eval_mkAdd, insn_rXsp hH] <;> rfl
  generalize (if mode = 1 then t.rXsp rn
    else t.rXsp rn + imm7.signExtend 64 * BitVec.ofNat 64 n) = A at haA ⊢
  have hwW : (Ex.mkAdd (σ.rXsp rn.toNat) (.k (imm7.signExtend 64 * BitVec.ofNat 64 n))).eval c =
      t.rXsp rn + imm7.signExtend 64 * BitVec.ofNat 64 n := by
    rw [Ex.eval_mkAdd, insn_rXsp hH]
    rfl
  generalize Ex.mkAdd (σ.rXsp rn.toNat) (.k (imm7.signExtend 64 * BitVec.ofNat 64 n)) = w
    at h hwW
  generalize t.rXsp rn + imm7.signExtend 64 * BitVec.ofNat 64 n = W at hwW ⊢
  have ha2 : (Ex.mkAdd a (.k (BitVec.ofNat 64 n))).eval c = A + BitVec.ofNat 64 n := by
    rw [Ex.eval_mkAdd, haA]
    rfl
  generalize Ex.mkAdd a (.k (BitVec.ofNat 64 n)) = a2 at h ha2
  generalize A + BitVec.ofNat 64 n = A2 at ha2 ⊢
  generalize (if opc = 1 then (2 : BitVec 2) else 1) = lopc at h ⊢
  clear hae
  cases ld
  · cases h
    have hna1 : nilPage A = false := by
      rw [← haA]
      exact hnil.2 a n (σ.rX rt.toNat) (by split <;> simp [Sym.store])
    have hna2 : nilPage A2 = false := by
      rw [← ha2]
      exact hnil.2 a2 n (σ.rX rt2.toNat) (by split <;> simp [Sym.store])
    have h1 := insn_holds_store hH a n (val := (t.rX rt).setWidth (8 * n)) (by rw [insn_rX hH])
    rw [haA] at h1
    have h2 := insn_holds_store h1 a2 n (val := (t.rX rt2).setWidth (8 * n)) (by rw [insn_rX hH])
    rw [ha2] at h2
    by_cases hm : mode = 2
    · simp only [hm, ↓reduceIte]
      refine ⟨_, ?_, insn_fall hpc h2 rfl⟩
      simp only [store, hna1, hna2, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
        Except.pure] <;> rfl
    · simp only [hm, ↓reduceIte]
      refine ⟨_, ?_, insn_fall hpc (insn_holds_wXsp h2 rn hwW) (by rw [insn_wXsp_pc])⟩
      simp only [store, hna1, hna2, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
        Except.pure] <;> rfl
  · rcases σ with ⟨sx, ssp, sfl, sloads, sstores⟩
    cases sstores with
    | cons p l => cases h
    | nil =>
      cases h
      have hmem : t.mem = c.s.mem := hH.mem
      have hna1 : nilPage A = false := by
        rw [← haA]
        exact hnil.1 a n (by split <;> simp)
      have hna2 : nilPage A2 = false := by
        rw [← ha2]
        exact hnil.1 a2 n (by split <;> simp)
      have e1 := insn_loadInto t lopc n rt (readMem t.mem A n) (v := .ld n a)
        (by rw [hmem, ← haA] <;> rfl)
      have e2 := fun s => insn_loadInto s lopc n rt2 (readMem t.mem A2 n) (v := .ld n a2)
        (by rw [hmem, ← ha2] <;> rfl)
      have hL := insn_holds_loads (insn_holds_loads hH ((a, n) :: sloads))
        ((a2, n) :: (a, n) :: sloads)
      have hW := insn_holds_wX (insn_holds_wX hL rt (v := loadVal lopc n (.ld n a)) rfl) rt2
        (v := loadVal lopc n (.ld n a2)) rfl
      by_cases hm : mode = 2
      · simp only [hm, ↓reduceIte]
        refine ⟨_, ?_, insn_fall hpc hW (by simp)⟩
        simp only [load, hna1, hna2, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
          Except.pure]
        show Except.ok ((t.loadInto false lopc n rt (readMem t.mem A n)).loadInto false lopc n rt2
          (readMem t.mem A2 n)).next = _
        rw [e1, e2]
      · simp only [hm, ↓reduceIte]
        refine ⟨_, ?_, insn_fall hpc (insn_holds_wXsp hW rn hwW) (by simp)⟩
        simp only [load, hna1, hna2, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
          Except.pure]
        show Except.ok (((t.loadInto false lopc n rt (readMem t.mem A n)).loadInto false lopc n rt2
          (readMem t.mem A2 n)).wXsp rn W).next = _
        rw [e1, e2]

/-! ### Conditional select, data processing, ordered accesses -/

private theorem insn_condSel {sf op op2 : Bool} {rm : Reg} {cond : BitVec 4} {rn rd : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.condSel sf op op2 rm cond rn rd) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.condSel sf op op2 rm cond rn rd) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  have hh : symCsel σ sf op op2 rm cond rn rd = .ok (σ', mc) := h
  unfold symCsel at hh
  split at hh
  · rename_i hfl
    cases hh
    have hfl' : t.nzcv = c.s.nzcv := by rw [hH.nzcv, hfl]; rfl
    exact ⟨_, rfl, insn_fall hpc (insn_holds_wX hH rd (by
      simp only [Ex.eval, insn_rX hH, cselVal, MState.holds, hfl'])) (insn_wX_pc _ _ _)⟩
  · cases hh

private theorem insn_dp1 {sf : Bool} {opc : BitVec 3} {rn rd : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.dp1 sf opc rn rd) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.dp1 sf opc rn rd) t = .ok t' ∧ Holds c σ' t' ∧ CtlPc c base o mc t' := by
  cases h
  exact ⟨_, rfl, insn_fall hpc (insn_holds_wX hH rd (by simp only [Ex.eval, insn_rX hH]))
    (insn_wX_pc _ _ _)⟩

private theorem insn_dp3 {sf : Bool} {op31 : BitVec 3} {o0 : Bool} {rm ra rn rd : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.dp3 sf op31 o0 rm ra rn rd) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', exec (.dp3 sf op31 o0 rm ra rn rd) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  cases h
  exact ⟨_, rfl, insn_fall hpc (insn_holds_wX hH rd (by simp only [Ex.eval_mkDp3, insn_rX hH]))
    (insn_wX_pc _ _ _)⟩

private theorem insn_excl {size : BitVec 2} {o2 ld o0 : Bool} {rs rn rt : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState} {base : BitVec 64}
    (h : symInsn (.ldstExcl size o2 ld o0 rs rn rt) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) (hnil : NoNil c σ') :
    ∃ t', exec (.ldstExcl size o2 ld o0 rs rn rt) t = .ok t' ∧ Holds c σ' t' ∧
      CtlPc c base o mc t' := by
  show ∃ t', execExcl t size o2 ld rs rn rt = .ok t' ∧ _
  have hh : symExcl σ size o2 ld rn rt = .ok (σ', mc) := h
  have ha := insn_rXsp hH rn
  unfold symExcl at hh
  unfold execExcl
  cases ld
  · cases o2
    · cases hh
    · simp only [Bool.false_eq_true, ↓reduceIte] at hh ⊢
      cases hh
      have hna : nilPage (t.rXsp rn) = false := by
        rw [← ha]; exact hnil.2 _ (bytesOf size) (σ.rX rt.toNat) (by simp [Sym.store])
      have hst := insn_holds_store hH (σ.rXsp rn.toNat) (bytesOf size) (v := σ.rX rt.toNat)
        (val := (t.rX rt).setWidth (8 * bytesOf size)) (by rw [insn_rX hH])
      rw [ha] at hst
      refine ⟨_, ?_, insn_fall hpc hst rfl⟩
      simp only [store, bytesOf, hna, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
        Except.pure]
  · simp only [↓reduceIte] at hh ⊢
    unfold Sym.load at hh
    cases hs : σ.stores.isEmpty
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hh; cases hh
    · simp only [hs, ↓reduceIte, pure, Except.pure] at hh
      cases hh
      have hs' : σ.stores = [] := List.isEmpty_iff.mp hs
      have hna : nilPage (t.rXsp rn) = false := by
        rw [← ha]; exact hnil.1 _ (bytesOf size) (by simp)
      have hmem : t.mem = c.s.mem := by rw [hH.mem, hs']; rfl
      have hW := insn_holds_wX (insn_holds_loads hH ((σ.rXsp rn.toNat, bytesOf size) :: σ.loads))
        rt (v := Ex.ld (bytesOf size) (σ.rXsp rn.toNat))
        (val := (readMem t.mem (t.rXsp rn) (2 ^ size.toNat)).setWidth 64)
        (by simp only [Ex.eval, ha, hmem]; rfl)
      refine ⟨_, ?_, insn_fall hpc hW (insn_wX_pc _ _ _)⟩
      simp only [load, hna, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]

/-! ## `symInsn_sound` -/

private theorem insn_post {i : Insn} {o : Nat} {σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    {base : BitVec 64} (h : ∃ t', exec i t = .ok t' ∧ Holds c σ' t' ∧ CtlPc c base o mc t') :
    ∃ t', exec i t = .ok t' ∧ WordsPost c base o σ' mc t' :=
  let ⟨t', he, hH, hc⟩ := h
  ⟨t', he, hH.toHoldsCore, fun _ => hH.x30, hc⟩

theorem symInsn_sound {i : Insn} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    {base : BitVec 64} (h : symInsn i o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) (hnil : NoNil c σ') :
    ∃ t', exec i t = .ok t' ∧ WordsPost c base o σ' mc t' := by
  cases i with
  | addSubImm => exact insn_post (insn_addSubImm h hH hpc)
  | logImm => exact insn_post (insn_logImm h hH hpc)
  | movWide => exact insn_post (insn_movWide h hH hpc)
  | bitfield => exact insn_post (insn_bitfield h hH hpc)
  | b => exact insn_post (insn_b h hH hpc)
  | bcond => exact insn_post (insn_bcond h hH hpc)
  | cbz => exact insn_post (insn_cbz h hH hpc)
  | tbz => exact insn_post (insn_tbz h hH hpc)
  | br => exact insn_br h hH hpc
  | nop => exact insn_post (insn_nop h hH hpc)
  | barrier => exact insn_post (insn_barrier h hH hpc)
  | logShift => exact insn_post (insn_logShift h hH hpc)
  | addSubShift => exact insn_post (insn_addSubShift h hH hpc)
  | addSubExt => exact insn_post (insn_addSubExt h hH hpc)
  | ldst => exact insn_post (insn_ldst h hH hpc hnil)
  | ldstPair => exact insn_post (insn_pair h hH hpc hnil)
  | condSel => exact insn_post (insn_condSel h hH hpc)
  | dp1 => exact insn_post (insn_dp1 h hH hpc)
  | dp3 => exact insn_post (insn_dp3 h hH hpc)
  | ldstExcl => exact insn_post (insn_excl h hH hpc hnil)
  | _ => cases h

/-! ## `symInsn` only adds loads and stores -/

/-- Closes `(∀ x ∈ σ.loads, x ∈ σ'.loads) ∧ (∀ x ∈ σ.stores, x ∈ σ'.stores)` once `σ'` is built
from `σ` by `wX`/`wXsp`/flag updates, `Sym.store` and consed loads. -/
local macro "insn_mono_tac" : tactic =>
  `(tactic| exact ⟨fun x hx => by (try split) <;> simp [hx, Sym.store],
    fun x hx => by (try split) <;> simp [hx, Sym.store]⟩)

theorem symAccess_mono {σ σ' : Sym} {size opc : BitVec 2} {rt : Nat} {a : Ex}
    (h : symAccess σ size opc rt a = .ok σ') :
    (∀ x ∈ σ.loads, x ∈ σ'.loads) ∧ (∀ x ∈ σ.stores, x ∈ σ'.stores) := by
  unfold symAccess Sym.load at h
  cases hp : (size = 3 && opc = 2)
  · rw [hp] at h
    cases ho : (opc != 0)
    · rw [ho] at h
      cases h
      insn_mono_tac
    · rw [ho] at h
      cases hs : σ.stores.isEmpty
      · rw [hs] at h
        cases h
      · rw [hs] at h
        cases h
        insn_mono_tac
  · rw [hp] at h
    cases h

theorem symInsn_mono {i : Insn} {o : Nat} {σ σ' : Sym} {mc : MCtl}
    (h : symInsn i o σ = .ok (σ', mc)) :
    (∀ x ∈ σ.loads, x ∈ σ'.loads) ∧ (∀ x ∈ σ.stores, x ∈ σ'.stores) := by
  cases i with
  | addSubImm sf sub setf => cases setf <;> cases h <;> insn_mono_tac
  | logImm sf opc n immr imms =>
    delta symInsn at h
    dsimp only at h
    split at h
    · cases h
    · split at h <;> cases h <;> insn_mono_tac
  | movWide =>
    delta symInsn at h
    dsimp only at h
    split at h
    · cases h
      insn_mono_tac
    · cases h
      insn_mono_tac
    · split at h
      · cases h
        insn_mono_tac
      · cases h
  | bitfield => cases h; insn_mono_tac
  | b link => cases link <;> cases h; insn_mono_tac
  | bcond => cases h; insn_mono_tac
  | cbz => cases h; insn_mono_tac
  | tbz => cases h; insn_mono_tac
  | br kind => cases kind <;> cases h <;> insn_mono_tac
  | condSel sf op op2 rm cond rn rd =>
    have hh : symCsel σ sf op op2 rm cond rn rd = .ok (σ', mc) := h
    unfold symCsel at hh
    split at hh
    · cases hh; insn_mono_tac
    · cases hh
  | dp1 => cases h; insn_mono_tac
  | dp3 => cases h; insn_mono_tac
  | ldstExcl size o2 ld o0 rs rn rt =>
    have hh : symExcl σ size o2 ld rn rt = .ok (σ', mc) := h
    unfold symExcl Sym.load at hh
    cases ld
    · cases o2
      · cases hh
      · simp only [Bool.false_eq_true, ↓reduceIte] at hh; cases hh; insn_mono_tac
    · cases hs : σ.stores.isEmpty
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hh; cases hh
      · simp only [hs, ↓reduceIte, pure, Except.pure] at hh; cases hh; insn_mono_tac
  | nop => cases h; insn_mono_tac
  | barrier => cases h; insn_mono_tac
  | logShift sf opc shift n =>
    cases n
    · rcases opc with ⟨⟨_ | _ | _ | _ | k, hk⟩⟩
      all_goals first
        | (cases h; insn_mono_tac)
        | exact absurd hk (by omega)
    · cases h
  | addSubShift sf sub setf => cases setf <;> cases h <;> insn_mono_tac
  | addSubExt sf sub setf => cases setf <;> cases h <;> insn_mono_tac
  | ldst size vec opc mode rn rt =>
    cases vec
    case true => cases h
    delta symInsn at h
    dsimp only at h
    generalize amodeSym σ mode rn.toNat (bytesOf size) = p at h
    obtain ⟨a, wb⟩ := p
    dsimp only at h
    cases hs : symAccess σ size opc rt.toNat a with
    | error e =>
      rw [hs] at h
      cases h
    | ok σ1 =>
      rw [hs] at h
      have hm := symAccess_mono hs
      cases wb <;> cases h
      · exact hm
      · exact ⟨fun x hx => by simpa using hm.1 x hx, fun x hx => by simpa using hm.2 x hx⟩
  | ldstPair opc vec mode ld =>
    cases vec
    case true => cases h
    delta symInsn at h
    dsimp only at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases ld
    · cases h
      insn_mono_tac
    · rcases σ with ⟨sx, ssp, sfl, sloads, sstores⟩
      cases sstores with
      | cons p l => cases h
      | nil =>
        cases h
        insn_mono_tac
  | _ => cases h

/-! ## A word whose symbolic access is in the nil page faults -/

/-- `NoNil` reads only the loads and stores. -/
theorem NoNil.of_same {c : Ctx} {σ σ' : Sym} (hl : σ'.loads = σ.loads) (hs : σ'.stores = σ.stores)
    (h : NoNil c σ) : NoNil c σ' := by
  unfold NoNil at *
  rw [hl, hs]
  exact h

/-- The classes `symInsn` gives loads or stores. -/
private def insnMem : Insn → Bool
  | .ldst .. | .ldstPair .. | .ldstExcl .. => true
  | _ => false

local macro "insn_same_tac" : tactic =>
  `(tactic| exact ⟨by (try split) <;> simp [Sym.store], by (try split) <;> simp [Sym.store]⟩)

private theorem symInsn_noMem {i : Insn} {o : Nat} {σ σ' : Sym} {mc : MCtl}
    (h : symInsn i o σ = .ok (σ', mc)) (hi : insnMem i = false) :
    σ'.loads = σ.loads ∧ σ'.stores = σ.stores := by
  cases i with
  | addSubImm sf sub setf => cases setf <;> cases h <;> insn_same_tac
  | logImm sf opc n immr imms =>
    delta symInsn at h
    dsimp only at h
    split at h
    · cases h
    · split at h <;> cases h <;> insn_same_tac
  | movWide =>
    delta symInsn at h
    dsimp only at h
    split at h
    · cases h
      insn_same_tac
    · cases h
      insn_same_tac
    · split at h
      · cases h
        insn_same_tac
      · cases h
  | bitfield => cases h; insn_same_tac
  | b link => cases link <;> cases h; insn_same_tac
  | bcond => cases h; insn_same_tac
  | cbz => cases h; insn_same_tac
  | tbz => cases h; insn_same_tac
  | br kind => cases kind <;> cases h <;> insn_same_tac
  | condSel sf op op2 rm cond rn rd =>
    have hh : symCsel σ sf op op2 rm cond rn rd = .ok (σ', mc) := h
    unfold symCsel at hh
    split at hh
    · cases hh; insn_same_tac
    · cases hh
  | dp1 => cases h; insn_same_tac
  | dp3 => cases h; insn_same_tac
  | nop => cases h; insn_same_tac
  | barrier => cases h; insn_same_tac
  | logShift sf opc shift n =>
    cases n
    · rcases opc with ⟨⟨_ | _ | _ | _ | k, hk⟩⟩
      all_goals first
        | (cases h; insn_same_tac)
        | exact absurd hk (by omega)
    · cases h
  | addSubShift sf sub setf => cases setf <;> cases h <;> insn_same_tac
  | addSubExt sf sub setf => cases setf <;> cases h <;> insn_same_tac
  | ldst | ldstPair | ldstExcl => cases hi
  | _ => cases h

/-- The single access of `symAccess` at `a`, in the nil page: `execLdSt` faults. -/
theorem symAccess_fault {σ σ1 : Sym} {c : Ctx} {t : MState} {size opc : BitVec 2}
    {rt : Nat} {a : Ex} {mode : AMode} {rn : Reg} {wbv : Option (BitVec 64)}
    (h : symAccess σ size opc rt a = .ok σ1)
    (hA : t.amode mode rn (bytesOf size) = (a.eval c, wbv)) (hN : NoNil c σ)
    (hbad : ¬ NoNil c σ1) :
    ∃ x, execLdSt t size false opc mode rn (BitVec.ofNat 5 rt) = .error (.nilPage x) := by
  have hA' : t.amode mode rn (accessBytes size false opc) = (a.eval c, wbv) := hA
  unfold symAccess Sym.load at h
  unfold execLdSt
  simp only [hA', Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  cases hp : (size = 3 && opc = 2)
  · rw [hp] at h
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases ho : (opc != 0)
    · rw [ho] at h
      cases h
      cases hna : nilPage (a.eval c)
      · exfalso
        apply hbad
        refine ⟨fun a' n' hl => hN.1 a' n' (by simpa [Sym.store] using hl), fun a' n' v' hs => ?_⟩
        simp only [Sym.store, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hs
        rcases hs with hs | ⟨rfl, -, -⟩
        · exact hN.2 _ _ _ hs
        · exact hna
      · refine ⟨a.eval c, ?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte, store, hna, bind, Except.bind]
    · rw [ho] at h
      cases hs : σ.stores.isEmpty
      · rw [hs] at h
        cases h
      · rw [hs] at h
        cases h
        cases hna : nilPage (a.eval c)
        · exfalso
          apply hbad
          refine ⟨fun a' n' hl => ?_, fun a' n' v' hs' => hN.2 a' n' v' (by simpa using hs')⟩
          simp only [insn_wX_loads, List.mem_cons, Prod.mk.injEq] at hl
          rcases hl with ⟨rfl, -⟩ | hl
          · exact hna
          · exact hN.1 _ _ hl
        · refine ⟨a.eval c, ?_⟩
          simp only [↓reduceIte, load, hna, bind, Except.bind]
  · rw [hp] at h
    cases h

private theorem insn_ldst_fault {size : BitVec 2} {opc : BitVec 2} {mode : AMode}
    {rn rt : Reg} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    (h : symInsn (.ldst size false opc mode rn rt) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hN : NoNil c σ) (hbad : ¬ NoNil c σ') :
    ∃ x, exec (.ldst size false opc mode rn rt) t = .error (.nilPage x) := by
  have hA := insn_amode hH mode rn (bytesOf size)
  delta symInsn at h
  dsimp only at h
  generalize amodeSym σ mode rn.toNat (bytesOf size) = pr at h hA
  obtain ⟨a, wb⟩ := pr
  dsimp only at h
  cases hs : symAccess σ size opc rt.toNat a with
  | error e =>
    rw [hs] at h
    cases h
  | ok σ1 =>
    rw [hs] at h
    have hbad1 : ¬ NoNil c σ1 := by
      cases wb <;> cases h
      · exact hbad
      · exact fun h1 => hbad (NoNil.of_same (by simp) (by simp) h1)
    obtain ⟨x, hx⟩ := symAccess_fault hs hA hN hbad1
    rw [insn_ofNat_toNat] at hx
    exact ⟨x, hx⟩

private theorem insn_pair_fault {opc : BitVec 2} {mode : BitVec 2} {ld : Bool}
    {imm7 : BitVec 7} {rt2 rn rt : Reg} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    (h : symInsn (.ldstPair opc false mode ld imm7 rt2 rn rt) o σ = .ok (σ', mc))
    (hH : Holds c σ t) (hN : NoNil c σ) (hbad : ¬ NoNil c σ') :
    ∃ x, exec (.ldstPair opc false mode ld imm7 rt2 rn rt) t = .error (.nilPage x) := by
  delta symInsn at h
  dsimp only at h
  show ∃ x, execPair t opc false mode ld imm7 rt2 rn rt = .error (.nilPage x)
  unfold execPair
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, decide_eq_true_eq]
    at h ⊢
  generalize (if opc.getLsbD 1 = true then 8 else 4) = n at h ⊢
  generalize hae : (if mode = 1 then σ.rXsp rn.toNat
    else Ex.mkAdd (σ.rXsp rn.toNat) (.k (imm7.signExtend 64 * BitVec.ofNat 64 n))) = a at h
  have haA : a.eval c =
      (if mode = 1 then t.rXsp rn else t.rXsp rn + imm7.signExtend 64 * BitVec.ofNat 64 n) := by
    rw [← hae]
    split <;> simp only [Ex.eval_mkAdd, insn_rXsp hH] <;> rfl
  generalize (if mode = 1 then t.rXsp rn
    else t.rXsp rn + imm7.signExtend 64 * BitVec.ofNat 64 n) = A at haA ⊢
  have ha2 : (Ex.mkAdd a (.k (BitVec.ofNat 64 n))).eval c = A + BitVec.ofNat 64 n := by
    rw [Ex.eval_mkAdd, haA]
    rfl
  generalize Ex.mkAdd a (.k (BitVec.ofNat 64 n)) = a2 at h ha2
  generalize A + BitVec.ofNat 64 n = A2 at ha2 ⊢
  generalize (if opc = 1 then (2 : BitVec 2) else 1) = lopc at h ⊢
  generalize Ex.mkAdd (σ.rXsp rn.toNat) (.k (imm7.signExtend 64 * BitVec.ofNat 64 n)) = w at h
  clear hae
  have hwb : ∀ X : Sym, ¬ NoNil c (if mode = 2 then X else X.wXsp rn.toNat w) → ¬ NoNil c X :=
    fun X hX hn => hX (by
      split
      · exact hn
      · exact NoNil.of_same (by simp) (by simp) hn)
  cases ld
  · cases h
    have hb := hwb _ hbad
    by_cases h1 : nilPage A = true
    · refine ⟨A, ?_⟩
      simp only [store, h1, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
    by_cases h2 : nilPage A2 = true
    · refine ⟨A2, ?_⟩
      simp only [store, h1, h2, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
    exfalso
    apply hb
    refine ⟨fun a' n' hl => hN.1 a' n' (by simpa [Sym.store] using hl), fun a' n' v' hs => ?_⟩
    simp only [Sym.store, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hs
    rcases hs with (hs | ⟨rfl, -, -⟩) | ⟨rfl, -, -⟩
    · exact hN.2 _ _ _ hs
    · rw [haA]; simpa using h1
    · rw [ha2]; simpa using h2
  · rcases σ with ⟨sx, ssp, sfl, sloads, sstores⟩
    cases sstores with
    | cons p l => cases h
    | nil =>
      cases h
      have hb := hwb _ hbad
      by_cases h1 : nilPage A = true
      · refine ⟨A, ?_⟩
        simp only [load, h1, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
      by_cases h2 : nilPage A2 = true
      · refine ⟨A2, ?_⟩
        simp only [load, h1, h2, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
      exfalso
      apply hb
      refine ⟨fun a' n' hl => ?_, fun a' n' v' hs => by simp at hs⟩
      simp only [insn_wX_loads, List.mem_cons, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, -⟩ | ⟨rfl, -⟩ | hl
      · rw [ha2]; simpa using h2
      · rw [haA]; simpa using h1
      · exact hN.1 _ _ hl

private theorem insn_excl_fault {size : BitVec 2} {o2 ld o0 : Bool} {rs rn rt : Reg}
    {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    (h : symInsn (.ldstExcl size o2 ld o0 rs rn rt) o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hN : NoNil c σ) (hbad : ¬ NoNil c σ') :
    ∃ x, exec (.ldstExcl size o2 ld o0 rs rn rt) t = .error (.nilPage x) := by
  show ∃ x, execExcl t size o2 ld rs rn rt = _
  have hh : symExcl σ size o2 ld rn rt = .ok (σ', mc) := h
  have ha := insn_rXsp hH rn
  unfold symExcl at hh
  unfold execExcl
  refine ⟨t.rXsp rn, ?_⟩
  cases ld
  · cases o2
    · cases hh
    · simp only [Bool.false_eq_true, ↓reduceIte] at hh ⊢
      cases hh
      cases hna : nilPage (t.rXsp rn)
      · exfalso
        apply hbad
        refine ⟨fun a' n' hl => hN.1 a' n' (by simpa [Sym.store] using hl), fun a' n' v' hs => ?_⟩
        simp only [Sym.store, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hs
        rcases hs with hs | ⟨rfl, -, -⟩
        · exact hN.2 _ _ _ hs
        · rw [ha]; exact hna
      · simp only [store, hna, ↓reduceIte, bind, Except.bind]
  · simp only [↓reduceIte] at hh ⊢
    unfold Sym.load at hh
    cases hs : σ.stores.isEmpty
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hh; cases hh
    · simp only [hs, ↓reduceIte, pure, Except.pure] at hh
      cases hh
      cases hna : nilPage (t.rXsp rn)
      · exfalso
        apply hbad
        refine ⟨fun a' n' hl => ?_, fun a' n' v' hs' => hN.2 a' n' v' (by simpa using hs')⟩
        simp only [insn_wX_loads, List.mem_cons, Prod.mk.injEq] at hl
        rcases hl with ⟨rfl, -⟩ | hl
        · rw [ha]; exact hna
        · exact hN.1 _ _ hl
      · simp only [load, hna, ↓reduceIte, bind, Except.bind]

/-- A word whose symbolic effect adds an access in the nil page (none before it) faults there. -/
theorem symInsn_fault {i : Insn} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    (h : symInsn i o σ = .ok (σ', mc)) (hH : Holds c σ t) (hN : NoNil c σ)
    (hbad : ¬ NoNil c σ') : ∃ x, exec i t = .error (.nilPage x) := by
  cases hm : insnMem i
  · obtain ⟨hl, hs⟩ := symInsn_noMem h hm
    exact absurd (NoNil.of_same hl hs hN) hbad
  cases i <;> simp only [insnMem, Bool.false_eq_true] at hm
  case ldst size vec opc mode rn rt =>
    cases vec
    · exact insn_ldst_fault h hH hN hbad
    · cases h
  case ldstPair opc vec mode ld imm7 rt2 rn rt =>
    cases vec
    · exact insn_pair_fault h hH hN hbad
    · cases h
  case ldstExcl => exact insn_excl_fault h hH hN hbad

end GoFV.Proof.Obj
