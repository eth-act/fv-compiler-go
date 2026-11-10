import GoFV.Gen.Check61

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G62: incoming stack arguments (`docs/plans/proofs3.md` §4)

A parameter that the function's ABI assigns to the stack (every parameter of an `ABI0` function,
e.g. an ABI wrapper `abigen_*`/`…,0`, and those past the integer and float registers of an
`ABIInternal` one) is read by an `Arg {x} [off]` value. `stackalloc` homes it in the slot of its
own piece (`StackAlloc.lean`: `{name := x, type, off}`), which Go's frame layout puts in the
caller's frame, at the `NAME_PARAM` operand `x+off(FP)`, where the caller stored the argument.
Genssa emits no code for it (`ssaGenValue`'s `OpArg`: "input args need no code"); a later value
reads it back with a `LoadReg` (G2's `MOVD x+off(FP), Rd`).

`checkG62 lc ps bstart g` is slice G61 (`GoFV/Gen/Check61.lean`, on P0') with, in a function with
an arm64 op, such an `Arg` (`vkind62a`), tried when G61 rejects a value: no temporary, no argument,
the aux `x` an input parameter that the ABI assigns to the stack, the value of a 64-bit class
(G2's spill slots hold 8 bytes, `checkFrame`'s `slotOK`), homed in the slot `argKey x off` with a
`NAME_PARAM` operand; no code. `homeOK10` accepts the slot home of an `Arg` (every slice before
G62 rejects the `Arg` itself). `GoFV/Proof/Gen/G62.lean` proves what an accepted function
satisfies, given the argument in the machine's slot when the `Arg` runs (`ArgOK`: the caller's
stack argument).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The slot of piece `off` of parameter `x` at type `t`: `stackalloc`'s home of an `Arg`. -/
def argKey (x : AuxRef) (t : TypeRef) (off : Int) : SlotKey :=
  { name := x, type := t, off := off, splitOf := none, splitOffset := 0 }

/-- Input parameter `x` is assigned to the stack by the function's ABI. -/
def stackParam (lc : LocCtx) (x : AuxRef) : Bool :=
  (abiParams lc.ctx.tabs lc.ctx.f).any fun p => !p.out && p.name == some x && p.regs.isEmpty

/-- An `Arg` of an incoming stack argument (module doc): no code. -/
def argKind62 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 0 do throw s!"v{v.id}: Arg shape"
  let some x := v.aux | throw s!"v{v.id}: Arg without name"
  unless stackParam lc x do throw s!"v{v.id}: Arg of a register parameter"
  unless cls (lc.ty v.id) == some 64 do throw s!"v{v.id}: Arg width"
  unless lc.home v.id == some (.slot (argKey x v.type v.auxInt.toInt)) do
    throw s!"v{v.id}: Arg home"
  let some (.PARAM, _) := g.slotOp (argKey x v.type v.auxInt.toInt)
    | throw s!"v{v.id}: Arg slot operand"
  return .none

/-- G62's values: an `Arg` (module doc); `none` off `Arg`. -/
def vkind62a (lc : LocCtx) (g : G2In) (v : Value) : Option (Except String VKind2) :=
  if v.op == .Arg then some (argKind62 lc g v) else none

/-- What `v` emits in G62, or why it is outside the slice: G61's kinds, then G62's `Arg` (`e` is
G61's reason, kept for the other values). -/
def vkind62 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind61 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind62a lc g v with
    | some r => r
    | none => .error e

/-- G61's check with G62's value check. -/
def checkG62L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind62 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless loopOK lc ps tab do throw "loop branch target"
    unless atomOK lc ps tab do throw "atomic branch target"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
    if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
    unless cloFirst lc do throw "LoweredGetClosurePtr after code"
    unless spHomes48 lc do throw "a value other than SP homed in SP"
    checkFrame lc g
    checkVars49 lc g
    let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
    let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
    checkK lc kt
    let ids := ps.toList.map (·.id)
    unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
    return (tab, kt)
  else checkNL30 lc ps bstart g

/-- Slice G62 of the genssa validator (module doc): `refsLive`, then G62's check on `liveCtx lc`. -/
def checkG62 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG62L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
