import GoFV.SSA.Sem.Run

/-!
# Calls of `memclrNoHeapPointers` and `memmove` that a `Zero`/`Move` can replace (#151)

generic.rules:1638 turns `(SelectN [0] (StaticCall {memclrNoHeapPointers} ptr (Const64 [c])
mem))` into `(Zero [c] ptr mem)`, and :1730 `(SelectN [0] (StaticCall|StaticLECall {memmove}
dst src (Const64 [sz]) mem))` into `(Move [sz] dst src mem)`. The checks here decide the call
shapes for which `GoFV.Proof.Seg` shows that the call's memory refines the plain write:

* `calleeIs`: the call's `AuxCall` names the function;
* `simpleCall tabs v k`: a static call with `k` value arguments and the memory; post-`expand
  calls` (`StaticCall`) every argument in one register, the first `k - 1` pointer-shaped, the
  last a 64-bit integer (the size), and no results; pre-`expand calls` (`StaticLECall`, the
  arguments are passed as they are) no results in the ABI assignments, if any.
-/

namespace GoFV.Opt.MemCall

open GoFV.SSA

/-- The call `v`'s `AuxCall` names function `name`. -/
def calleeIs (tabs : Tables) (v : Value) (name : String) : Bool :=
  v.aux.bind tabs.callee? == some name

/-- An input parameter in one register, pointer-shaped (`ptr`) or a 64-bit integer (`!ptr`). -/
def inShape (tabs : Tables) (ptr : Bool) (p : ABIParam) : Bool :=
  !p.out && p.regs.size == 1 &&
    match tabs.ty p.type with
    | .ptr _ => ptr
    | .int .w64 => !ptr
    | _ => false

/-- `k` input parameters, each in one register: `k - 1` pointers, then a 64-bit integer. -/
def inShapes (tabs : Tables) (k : Nat) (ps : List ABIParam) : Bool :=
  ps.length == k && ps.dropLast.all (inShape tabs true) && ps.getLast?.all (inShape tabs false)

/-- `v` is a static call with `k` value arguments and the memory whose arguments reach the
callee as they are and which has no results (see the module doc). -/
def simpleCall (tabs : Tables) (v : Value) (k : Nat) : Bool :=
  v.args.size == k + 1 &&
    match v.op with
    | .StaticLECall => ((Sem.callABI? tabs v.aux).map fun abi => abi.params.all (!·.out)).getD true
    | .StaticCall =>
      match Sem.callABI? tabs v.aux with
      | some abi => inShapes tabs k abi.params.toList
      | none => false
    | _ => false

end GoFV.Opt.MemCall
