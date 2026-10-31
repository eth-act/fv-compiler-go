import GoFV.SSA.Alloc

/-!
# Speculative execution check (`branchelim.go:425-463`)

`canSpeculativelyExecute`, `isDivMod` and `isPtrArithmetic`, shared by `branchelim` and the
comparison fusions of `early fuse` (`fuse_comparisons.go`). `isMem` is `t.IsMemory()` (a
parameter so this module does not depend on the type tables).
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `isDivMod(op)` (`branchelim.go:445`). -/
def isDivMod : Op → Bool
  | .Div8 | .Div8u | .Div16 | .Div16u | .Div32 | .Div32u | .Div64 | .Div64u | .Div128u
  | .Div32F | .Div64F
  | .Mod8 | .Mod8u | .Mod16 | .Mod16u | .Mod32 | .Mod32u | .Mod64 | .Mod64u => true
  | _ => false

/-- `isPtrArithmetic(op)` (`branchelim.go:457`). -/
def isPtrArithmetic : Op → Bool
  | .OffPtr | .AddPtr | .SubPtr => true
  | _ => false

/-- `v.MemoryArg() != nil` (`value.go:556`) for a non-phi `v`: the last argument has a memory
type. -/
def hasMemoryArg (isMem : TypeRef → Bool) (f : Func) (v : Value) : Bool :=
  match v.args.back? with
  | some a => isMem (f.getV a).type
  | none => false

/-- `canSpeculativelyExecute(b)` (`branchelim.go:433`): no phi, division, pointer arithmetic,
memory-typed or side-effecting value, and no memory argument except on `InlMark`. -/
def canSpeculativelyExecute (isMem : TypeRef → Bool) (f : Func) (b : ID) : Bool :=
  (f.getB b).values.all fun id =>
    let v := f.getV id
    !(v.op == .Phi || isDivMod v.op || isPtrArithmetic v.op || isMem v.type ||
        v.op.hasSideEffects) &&
      (v.op == .InlMark || !hasMemoryArg isMem f v)

end GoFV.Opt
