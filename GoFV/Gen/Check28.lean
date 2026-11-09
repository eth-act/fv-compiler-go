import GoFV.Gen.Check27

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G28: `LoweredMemEq` (`docs/plans/proofs3.md` §4)

`checkG28 lc ps bstart g` extends slice G27 (`GoFV/Gen/Check27.lean`) by `LoweredMemEq p q n mem`
(`ssa.go`'s `LoweredMemEq` case): `CALL runtime.memequal(SB)` (`TYPE_MEM`, `NAME_EXTERN`,
ABIInternal), which `runMach` hands to the runtime hook (`internal/bytealg/equal_arm64.s`
`memequal`: `R0` the result, the memory unchanged). The op's register constraints
(`ARM64Ops.go`) put `p`, `q`, `n` in `R0`, `R1`, `R2` and the result in `R0`; it clobbers what a
call does.

G28 accepts such a value with no temporary, four arguments, its arguments `p`, `q`, `n` homed in
`R0`, `R1`, `R2` at class 64 (a pointer or a 64-bit integer, which the routine reads whole), the
memory last, and its boolean result homed in `R0`. A function with `LoweredMemEq` calls, so its
activation has a frame (`G28Env`). `GoFV/Proof/Gen/G28.lean` proves what an accepted function
satisfies, under the trusted `runtime.memequal` contract (`MemEqOK`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The runtime symbol of `LoweredMemEq` (`ir.Syms.Memequal`, ABIInternal). -/
def memEqSym : GoStr × Nat := (GoStr.ofString "runtime.memequal", 1)

/-- The `CALL` target of `LoweredMemEq`: `runtime.memequal(SB)`. -/
def memEqTarget (g : G2In) (a : Addr) : Bool :=
  a.type == .MEM && a.name == .EXTERN && a.reg == 0 && a.index == 0 && a.offset == 0 &&
    match a.sym with
    | some y => g.syms[y]? == some memEqSym
    | none => false

/-- The Prog of `LoweredMemEq`: `CALL runtime.memequal(SB)`. -/
def memEqPat (g : G2In) : Pat :=
  ⟨plain .CALL (fun a : Addr => a == {}) (memEqTarget g), "CALL"⟩

/-- The boolean shape. -/
def boolTy : Ty → Bool
  | .bool => true
  | _ => false

/-- Argument `i` of `v` is homed in register `i` at class 64. -/
def memEqArg (lc : LocCtx) (v : Value) (i : Nat) : Bool :=
  match v.args[i]? with
  | some a => lc.home a == some (.reg i) && cls (lc.ty a) == some 64
  | none => false

/-- `LoweredMemEq p q n mem`: no temporary, `p`, `q`, `n` in `R0`, `R1`, `R2` at class 64, the
memory last, the boolean result in `R0`; one `CALL runtime.memequal(SB)`. -/
def memEqKind (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  unless v.args.size == 4 && lc.home v.id == some (.reg 0) && boolTy (lc.ty v.id) &&
      memEqArg lc v 0 && memEqArg lc v 1 && memEqArg lc v 2 do
    throw s!"v{v.id}: memequal shape"
  memArg lc v 3
  return .prog (memEqPat g)

/-- What `v` emits in G28, or why it is outside the slice. -/
def vkind28 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .ARM64LoweredMemEq then memEqKind lc g v else vkind27 lc g v

/-- Slice G28 of the genssa validator (module doc): G27 with G28's value check. -/
def checkG28 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind28 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK lc do throw "MOVDnop/MOVDreg: upper bits unknown"
    if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
    unless cloFirst lc do throw "LoweredGetClosurePtr after code"
    checkFrame lc g
    checkVars lc g
    let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
    let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
    checkK lc kt
    let ids := ps.toList.map (·.id)
    unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
    return (tab, kt)
  else checkNL lc ps bstart g

end GoFV.Gen.Check
