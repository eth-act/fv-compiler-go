import GoFV.Asm.CheckObjLink

variable [GoFV.SSA.Sem.Addrs]

/-!
# What a symbolic effect says about machine states (`docs/plans/proofs3.md` §6)

The validator `checkObj` (`GoFV/Asm/CheckObj.lean`) compares symbolic effects (`Sym`) over the
state before a Prog. This module gives them their meaning on `MState`:

* `storesMem c st m`: the memory `m` after the stores `st`, in order, evaluated in `c`.
* `HoldsCore c σ t`: every general register of `t` but `X30` is the value `σ` gives it over
  the state `c.s` before the Prog (`X31`, unused, unchanged), and `SP`, the flags, the vector
  registers (`Sym.evalV`) and the memory (after `σ`'s stores) are; `Holds` adds `X30`.
* `NoNil c σ`: no load or store of `σ` is in the nil page.
* `CtlPc c base o mc t`: the PC of `t` is where the control `mc` of the word at offset `o` of
  code placed at `base` goes (`symInsn`).
* `PcP L p pc s s'`: the PC (and for a call, `X30`) of the Prog-level step `s → s'` is where the
  control `pc` of `progSym` goes (`progStep` under the layout `L`).
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj

/-- The memory after the stores `st` in order (each the low `8 n` bits of its value's
`Ex.eval128`). -/
def storesMem (c : Ctx) : List (Ex × Nat × Ex) → Memory → Memory
  | [], m => m
  | (a, n, v) :: st, m =>
    storesMem c st (writeMem m (a.eval c) n ((v.eval128 c).setWidth (8 * n)))

/-- A store of at most 8 bytes writes the low bits of the 64-bit value. -/
theorem Ex.eval128_setWidth {n : Nat} (hn : n ≤ 8) (c : Ctx) (e : Ex) :
    (e.eval128 c).setWidth (8 * n) = (e.eval c).setWidth (8 * n) := by
  unfold Ex.eval128
  split
  · simp only [Ex.eval]
    rw [BitVec.setWidth_setWidth_of_le _ (by omega)]
  · rw [BitVec.setWidth_setWidth_of_le _ (by omega)]

/-- `t` is what `σ` describes over `c.s`, `X30` aside. -/
structure HoldsCore (c : Ctx) (σ : Sym) (t : MState) : Prop where
  x : ∀ r : Nat, r < 30 → t.x (BitVec.ofNat 5 r) = (σ.getX r).eval c
  x31 : t.x 31 = c.s.x 31
  sp : t.sp = σ.sp.eval c
  nzcv : t.nzcv = σ.fl.eval c
  v : t.v = σ.evalV c
  mem : t.mem = storesMem c σ.stores c.s.mem

/-- An effect that writes no vector register leaves them as before the Prog. -/
theorem Sym.evalV_of_nil {σ : Sym} {c : Ctx} (h : σ.v = []) : σ.evalV c = c.s.v := by
  funext r
  simp [Sym.evalV, h]

/-- A vector register the effect has not written is as before the Prog. -/
theorem Sym.evalV_of_lookup {σ : Sym} {c : Ctx} {r : Reg} (h : σ.v.lookup r.toNat = none) :
    σ.evalV c r = c.s.v r := by
  simp [Sym.evalV, h]

/-- The vector register `r` after the effect is `getV`'s value. -/
theorem Sym.evalV_getV (σ : Sym) (c : Ctx) (r : Reg) : σ.evalV c r = (σ.getV r.toNat).eval c := by
  unfold Sym.evalV Sym.getV
  cases σ.v.lookup r.toNat <;> simp [VEx.eval]

/-- A write of vector register `r < 32`. -/
theorem Sym.evalV_wV (σ : Sym) (c : Ctx) {r : Nat} (hr : r < 32) (e : VEx) :
    (σ.wV r e).evalV c = fun q => if q = BitVec.ofNat 5 r then e.eval c else σ.evalV c q := by
  funext q
  unfold Sym.evalV Sym.wV
  by_cases hq : q = BitVec.ofNat 5 r
  · subst hq
    simp [List.lookup, Nat.mod_eq_of_lt hr]
  · have hne : (q.toNat == r) = false := by
      simp only [beq_eq_false_iff_ne]
      intro h; apply hq; subst h; simp
    simp [List.lookup, hne, hq]

/-- What `Sym.vEx` accepts: `V r` is not written yet. -/
theorem Sym.vEx_ok {σ : Sym} {r : Nat} {e e' : Ex} (h : σ.vEx r e = .ok e') :
    σ.v.lookup r = none ∧ e' = e := by
  unfold Sym.vEx at h
  split at h
  · rename_i hn
    cases h
    exact ⟨Option.isNone_iff_eq_none.1 hn, rfl⟩
  · cases h

/-- `t` is what `σ` describes over `c.s`. -/
structure Holds (c : Ctx) (σ : Sym) (t : MState) : Prop extends HoldsCore c σ t where
  x30 : t.x 30 = (σ.getX 30).eval c

/-- No load or store of `σ` is in the nil page. -/
def NoNil (c : Ctx) (σ : Sym) : Prop :=
  (∀ a n, (a, n) ∈ σ.loads → nilPage (a.eval c) = false) ∧
  (∀ a n v, (a, n, v) ∈ σ.stores → nilPage (a.eval c) = false)

/-- The address of offset `q` of code placed at `base`. -/
def at_ (base : BitVec 64) (q : Int) : BitVec 64 := base + BitVec.ofInt 64 q

/-- Where the control `mc` of the word at offset `o` takes the PC of `t` (`symInsn`'s outcomes;
`call` and `jmpSym` are `symWords`'). -/
def CtlPc (c : Ctx) (base : BitVec 64) (o : Nat) : MCtl → MState → Prop
  | .fall, t => t.pc = at_ base (o + 4)
  | .jmp q, t => t.pc = at_ base q
  | .cond fl cc q, t =>
    t.pc = if (condOf cc).holds (fl.eval c) then at_ base q else at_ base (o + 4)
  | .cbz sf nz a q, t =>
    t.pc = if (ProgOp.trunc sf (a.eval c) == 0) != nz then at_ base q else at_ base (o + 4)
  | .tbz nz b a q, t =>
    t.pc = if (a.eval c).getLsbD b == nz then at_ base q else at_ base (o + 4)
  | .reg a, t => t.pc = a.eval c
  | .call n add, t => t.pc = c.sym n + BitVec.ofInt 64 add ∧ t.x 30 = at_ base (o + 4)
  | .jmpSym n add, t => t.pc = c.sym n + BitVec.ofInt 64 add
  | .callReg a, t => t.pc = a.eval c ∧ t.x 30 = at_ base (o + 4)

/-- What the state after words with effect `σ` and control `mc`, the last at `ol`, satisfies
(`X30` as `σ` says unless `mc` is a call). -/
def WordsPost (c : Ctx) (base : BitVec 64) (ol : Nat) (σ : Sym) (mc : MCtl) (tm : MState) : Prop :=
  HoldsCore c σ tm ∧ (mc.links = false → tm.x 30 = (σ.getX 30).eval c) ∧ CtlPc c base ol mc tm

/-- A `CALL (Rn)`: a call whose target is not a symbol operand (`progEffect` jumps to the
register's value). -/
def isICall (p : Prog) : Bool :=
  p.as.name == "CALL" && p.to.type != .BRANCH &&
    !(p.to.type == .MEM && (p.to.name == .EXTERN || p.to.name == .STATIC))

/-- Where the control `pc` of `progSym` takes the Prog-level step `s → s'` of `p` under `L`. -/
def PcP (L : Link) (p : Prog) (σ : Sym) (s : MState) : PCtl → MState → Prop
  | .fall, s' => L.nextAddr p.id = some s'.pc ∧ s'.x 30 = (σ.getX 30).eval ⟨s, L.sym⟩
  | .jmp id, s' => L.addr id = some s'.pc ∧ s'.x 30 = (σ.getX 30).eval ⟨s, L.sym⟩
  | .cond cc id, s' => (∃ next tgt, L.nextAddr p.id = some next ∧ L.addr id = some tgt ∧
      s'.pc = if (condOf cc).holds s.nzcv then tgt else next) ∧
      s'.x 30 = (σ.getX 30).eval ⟨s, L.sym⟩
  | .cbz sf nz a id, s' => (∃ next tgt, L.nextAddr p.id = some next ∧ L.addr id = some tgt ∧
      s'.pc = if (ProgOp.trunc sf (a.eval ⟨s, L.sym⟩) == 0) != nz then tgt else next) ∧
      s'.x 30 = (σ.getX 30).eval ⟨s, L.sym⟩
  | .tbz nz b a id, s' => (∃ next tgt, L.nextAddr p.id = some next ∧ L.addr id = some tgt ∧
      s'.pc = if (a.eval ⟨s, L.sym⟩).getLsbD b == nz then tgt else next) ∧
      s'.x 30 = (σ.getX 30).eval ⟨s, L.sym⟩
  | .reg a, s' => s'.pc = a.eval ⟨s, L.sym⟩ ∧ s'.x 30 = (σ.getX 30).eval ⟨s, L.sym⟩
  | .call n add, s' => s'.pc = L.sym n + BitVec.ofInt 64 add ∧ L.nextAddr p.id = some (s'.x 30)
  | .callReg a, s' => s'.pc = a.eval ⟨s, L.sym⟩ ∧ L.nextAddr p.id = some (s'.x 30) ∧
      isICall p = true

end GoFV.Proof.Obj
