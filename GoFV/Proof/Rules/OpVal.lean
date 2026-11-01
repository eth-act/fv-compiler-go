import GoFV.SSA.Sem.Pure
import GoFV.SSA.Export

/-!
# The value of a term node: `evalPure`, or a table lookup (issue #151)

The nodes of terms (`GoFV.Opt.RewriteCheck.termOp`) are evaluated by `evalPure`, except
`Addr {sym}` and `ConstString {str}`, which `Sem.frameVal` evaluates from the definition tables
(a global pointer; a string `agg [ptr, len]`) and which do not depend on the activation:
`opVal tabs op ty auxInt aux args`. It is `evalPure` at every other op (`opVal_pure`) and agrees
with `frameVal` at these two (`GoFV.Proof.AtomSim.frameVal_tab`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem

/-- `Addr {sym}`: the global the symbol names (`Sem.frameVal`). -/
def addrVal (tabs : Tables) (ax : Option AuxRef) : Val :=
  match ax.bind tabs.aux? with
  | some { kind := .sym name .., .. } => .ptr ⟨.global name.toStringLossy, 0⟩
  | _ => .poison

/-- `ConstString {str}`: the string's data symbol and length (`Sem.frameVal`). -/
def strVal (tabs : Tables) (ax : Option AuxRef) : Val :=
  match ax.bind tabs.aux? with
  | some { kind := .str s dataSym, .. } =>
    Val.ofStr [if s.size == 0 then .ptr Ptr.null else .ptr ⟨.global dataSym.toStringLossy, 0⟩,
      .i64 (BitVec.ofNat 64 s.size)]
  | _ => .poison

/-- The ops a term node evaluates from the tables. -/
def frameOp (op : Op) : Bool := op == .Addr || op == .ConstString

/-- The value of a term node with op `op`, type shape `ty`, fields `ai`/`ax` and argument
values `args` (before `retype`). -/
def opVal (tabs : Tables) (op : Op) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    Val :=
  if op = .Addr then addrVal tabs ax
  else if op = .ConstString then strVal tabs ax
  else evalPure op ty ai ax args

theorem opVal_pure {tabs : Tables} {op : Op} (h : frameOp op = false) (ty : Ty) (ai : Int64)
    (ax : Option AuxRef) (args : List Val) : opVal tabs op ty ai ax args = evalPure op ty ai ax args := by
  have h1 : op ≠ .Addr := fun e => by subst e; exact absurd h (by decide)
  have h2 : op ≠ .ConstString := fun e => by subst e; exact absurd h (by decide)
  simp only [opVal, h1, h2, ite_false]

theorem opVal_addr (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    opVal tabs .Addr ty ai ax args = addrVal tabs ax := by
  simp only [opVal, ite_true]

theorem opVal_constString (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef)
    (args : List Val) : opVal tabs .ConstString ty ai ax args = strVal tabs ax := by
  simp only [opVal, reduceCtorEq, ite_false, ite_true]

example : opVal {} .Add64 (.int .w64) 0 none [.i64 1, .i64 2] = .i64 3 := rfl
example : opVal {} .Addr (.ptr none) 0 none [] = .poison := rfl

end GoFV.Proof.Rules
