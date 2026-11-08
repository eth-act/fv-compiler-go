import GoFV.Proof.Obj.Basic

/-!
# The smart constructors of `Ex`/`Fl` preserve the meaning (`GoFV/Asm/CheckObjSym.lean`)

Each smart constructor (`Ex.mkAdd`, `Ex.mkAddSub`, …, `Fl.mkAddSub`, `Fl.mkAnds`) evaluates to
the data operation it stands for; `Ex.eval_congr` evaluates an `Ex` alike in two contexts that
agree on what it reads.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.SSA.Sem.Arm64 (Shift sext)

theorem Ex.eval_mkAdd (c : Ctx) (a b : Ex) : (Ex.mkAdd a b).eval c = a.eval c + b.eval c := by
  sorry

theorem Ex.eval_mkTrunc (c : Ctx) (sf : Bool) (a : Ex) :
    (Ex.mkTrunc sf a).eval c = ProgOp.trunc sf (a.eval c) := by
  sorry

theorem Ex.eval_mkAddSub (c : Ctx) (sf sub : Bool) (a b : Ex) :
    (Ex.mkAddSub sf sub a b).eval c = (addSub sf sub (a.eval c) (b.eval c)).1 := by
  sorry

theorem Ex.eval_mkLogical (c : Ctx) (sf : Bool) (opc : BitVec 2) (a b : Ex) :
    (Ex.mkLogical sf opc a b).eval c = (logical sf opc (a.eval c) (b.eval c)).1 := by
  sorry

theorem Ex.eval_mkShift (c : Ctx) (sf : Bool) (kd : BitVec 2) (amt : Nat) (a : Ex) :
    (Ex.mkShift sf kd amt a).eval c =
      sized sf fun _ e => Shift.apply (shiftOf kd) (e (a.eval c)) amt := by
  sorry

theorem Ex.eval_mkExt (c : Ctx) (opt : BitVec 3) (sh : Nat) (a : Ex) :
    (Ex.mkExt opt sh a).eval c = extendReg (a.eval c) opt sh := by
  sorry

theorem Ex.eval_mkBfm (c : Ctx) (sf : Bool) (opc : BitVec 2) (immr imms : BitVec 6) (d a : Ex) :
    (Ex.mkBfm sf opc immr imms d a).eval c = bitfieldMove sf opc immr imms (d.eval c) (a.eval c) := by
  sorry

theorem Ex.eval_mkSext (c : Ctx) (n : Nat) (a : Ex) : (Ex.mkSext n a).eval c = sext n (a.eval c) := by
  sorry

theorem Fl.eval_mkAddSub (c : Ctx) (sf sub : Bool) (a b : Ex) :
    (Fl.mkAddSub sf sub a b).eval c = (addSub sf sub (a.eval c) (b.eval c)).2 := by
  sorry

theorem Fl.eval_mkAnds (c : Ctx) (sf : Bool) (a b : Ex) :
    (Fl.mkAnds sf a b).eval c = (logical sf 3 (a.eval c) (b.eval c)).2 := by
  sorry

/-- An `Ex` evaluates alike in two contexts with the same symbols, `SP` and memory that agree
on the registers it reads. -/
theorem Ex.eval_congr {c c' : Ctx} (hsym : c.sym = c'.sym) (hsp : c.s.sp = c'.s.sp)
    (hmem : c.s.mem = c'.s.mem) :
    ∀ e : Ex, (∀ r, e.reads r = true → c.s.x (BitVec.ofNat 5 r) = c'.s.x (BitVec.ofNat 5 r)) →
      e.eval c = e.eval c' := by
  sorry

/-- `Fl.eval_congr`, with the flags before the Prog equal. -/
theorem Fl.eval_congr {c c' : Ctx} (hsym : c.sym = c'.sym) (hsp : c.s.sp = c'.s.sp)
    (hmem : c.s.mem = c'.s.mem) (hfl : c.s.nzcv = c'.s.nzcv) :
    ∀ f : Fl, (∀ r, f.reads r = true → c.s.x (BitVec.ofNat 5 r) = c'.s.x (BitVec.ofNat 5 r)) →
      f.eval c = f.eval c' := by
  sorry

end GoFV.Proof.Obj
