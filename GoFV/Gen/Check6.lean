import GoFV.Gen.Check5

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G6: frame variables (`docs/plans/proofs3.md` §4)

`checkG6 lc ps bstart g` extends slice G5 (`GoFV/Gen/Check5.lean`) by the addresses of frame
variables and the accesses of frame variables. A frame variable G6 handles is an `*ir.Name` aux of
class `PAUTO` whose address the function never converts to an integer (`Tables.forgeable x =
false`: its block is `Blk.temp`, which no integer converts back to), with an operand in Go's frame
layout: the operand of its slot at offset 0 (`varOp`, G2's `slotOp`: `NAME_AUTO` and the
`FrameOffset`). Its accesses address `SP`.

**Values** beyond G5's (`vkind6`):

* `MOVDaddr {x} [off] sp` of a frame variable `x` into a 64-bit register: `MOVD $off'(RSP), Rd`
  (`TYPE_ADDR`) with `off' = FrameOffset + off`;
* the loads `MOV{D,B,BU,H,HU,W,WU}load {x} [off] sp mem` and stores
  `MOV{D,B,H,W}store {x} [off] sp v mem` of G3 at `off'(RSP)`;
* the pair load `LDP {x} [off] sp mem` and the pair store `STP {x} [off] sp a b mem` of G4 at
  `off'(RSP)`.

**Frame** (`checkVars`): the windows of the variables the function accesses (their sizes from
`Ctx.locals`) lie inside the locals, pairwise disjoint (merged locals share an operand) and away
from the home slots: what lets the activation put each at its frame operand under the injection
(`GoFV/Proof/Gen/G6.lean`, `G6Env`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The slot of frame variable `x` at offset 0 (G2's `slotOp` ignores its type). -/
def varKey (x : AuxRef) : SlotKey :=
  { name := x, type := 0, off := 0, splitOf := none, splitOffset := 0 }

/-- The frame operand of variable `x`: name class and `FrameOffset`. -/
def varOp (g : G2In) (x : AuxRef) : Option (AddrName × Int) := g.slotOp (varKey x)

/-- Aux `x` names a frame variable (an `*ir.Name`). -/
def isVar (lc : LocCtx) (x : AuxRef) : Bool :=
  match lc.ctx.tabs.aux? x with
  | some { kind := .name .., .. } => true
  | _ => false

/-- The first argument of `v` is `SP`. -/
def spArg (lc : LocCtx) (v : Value) : Bool :=
  match v.args[0]? with
  | some a => (lc.ctx.f.value? a).map (·.op) == some .SP
  | none => false

/-- The variable and the `NAME_AUTO` operand offset of an access `v` of a frame variable: its aux
names a variable with a `NAME_AUTO` operand in the frame layout whose address the function does
not convert to an integer (a `PAUTO`, `Blk.temp`), and its first argument is `SP`; `none` if its
aux names no variable. -/
def frameVar? (lc : LocCtx) (g : G2In) (v : Value) : Except String (Option (AuxRef × Int)) :=
  match v.aux with
  | none => .ok none
  | some x =>
    if !isVar lc x then .ok none
    else if !spArg lc v then .error s!"v{v.id}: frame variable off another base"
    else match varOp g x with
      | some (.AUTO, off) =>
        if lc.ctx.tabs.forgeable x then .error s!"v{v.id}: frame variable with an integer address"
        else .ok (some (x, off + v.auxInt.toInt))
      | some _ => .error s!"v{v.id}: frame variable operand class"
      | none => .error s!"v{v.id}: frame variable without operand"

/-- The frame variables the function accesses (the auxes `frameVar?` reads: a variable on a value
whose first argument is `SP`). -/
def accessedVars (lc : LocCtx) : List AuxRef :=
  (lc.ctx.f.valueTab.toList.filterMap fun o => o.bind fun v =>
    match v.aux with
    | some x => if isVar lc x && spArg lc v then some x else none
    | none => none).eraseDups

/-- The window `[off, off + size)` of a frame variable's `NAME_AUTO` operand. -/
def varWin (lc : LocCtx) (g : G2In) (x : AuxRef) : Option (Int × Int) := do
  let (.AUTO, off) ← varOp g x | none
  let (_, sz, _) ← lc.ctx.locals.find? (·.1 == x)
  return (off, off + sz)

/-- Two windows are disjoint. -/
def winApart (w w' : Int × Int) : Bool := w.2 ≤ w'.1 || w'.2 ≤ w.1

/-- The frame checks of slice G6 (module doc): each accessed variable's window inside the locals,
the windows pairwise disjoint and away from the home slots' (8 bytes each). -/
def checkVars (lc : LocCtx) (g : G2In) : Except String Unit := do
  let xs := accessedVars lc
  let ws ← xs.mapM fun x => match varWin lc g x with
    | some w => pure w
    | none => throw s!"frame variable a{x}: no window"
  unless ws.all fun w => -g.stksize ≤ w.1 && w.1 ≤ w.2 && w.2 ≤ 0 do
    throw "frame variable outside the locals"
  unless (ws.zipIdx).all fun (w, i) => (ws.zipIdx).all fun (w', i') => i == i' || winApart w w' do
    throw "two frame variables overlap"
  let slots := (homeSlots lc).filterMap fun k => match g.slotOp k with
    | some (.AUTO, o) => some (o, o + slotW lc k)
    | _ => none
  unless ws.all fun w => slots.all (winApart w) do
    throw "frame variable over a spill slot"

/-- The address operand `$off(RSP)` of a `NAME_AUTO` frame operand (`TYPE_ADDR`). -/
def addrA (a : Addr) (off : Int) : Bool := a.type == .ADDR && slotA { a with type := .MEM } .AUTO off

/-- What an access of a frame variable at the `NAME_AUTO` operand offset `off` emits. -/
def vkindVar (lc : LocCtx) (v : Value) (off : Int) : Except String VKind2 := do
  if v.op == .ARM64MOVDaddr then
    unless v.args.size == 1 do throw s!"v{v.id}: address shape"
    let (c, rd) ← resObj lc v
    unless c == 64 do throw s!"v{v.id}: address width"
    return .prog ⟨plain .MOVD (addrA · off) (· == regA rd), "MOVD $var"⟩
  if let some (as, n, sg) := loadOp? v.op then
    unless v.args.size == 2 do throw s!"v{v.id}: load shape"
    memArg lc v 1
    let (c, rd) ← resObj lc v
    unless 8 ≤ c || (c == 1 && n == 1 && !sg) do throw s!"v{v.id}: load widths"
    return .prog ⟨plain as (slotA · .AUTO off) (· == regA rd), as.name⟩
  if let some (as, n) := storeOp? v.op then
    unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: store shape"
    let (cs, rs) ← argObj lc v 1
    memArg lc v 2
    unless 8 * n ≤ cs || (cs == 1 && n == 1) do throw s!"v{v.id}: store widths"
    return .prog ⟨plain as (· == regA rs) (slotA · .AUTO off), as.name⟩
  match v.op with
  | .ARM64LDP =>
    unless v.args.size == 2 && pairTys (lc.ty v.id) do throw s!"v{v.id}: pair load shape"
    memArg lc v 1
    let some (ra, rb) := pairHome? lc v.id | throw s!"v{v.id}: pair load home"
    unless ra != rb && ra != zeroReg && rb != zeroReg && destOK ra && destOK rb do
      throw s!"v{v.id}: pair load registers"
    let some oa := objOf? ra | throw s!"v{v.id}: register {ra}"
    let some ob := objOf? rb | throw s!"v{v.id}: register {rb}"
    return .prog ⟨plain .LDP (slotA · .AUTO off) (· == pairA oa ob), "LDP"⟩
  | .ARM64STP =>
    unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: pair store shape"
    let (cx, rx) ← argObj lc v 1
    let (cy, ry) ← argObj lc v 2
    memArg lc v 3
    unless cx == 64 && cy == 64 do throw s!"v{v.id}: pair store widths"
    return .prog ⟨plain .STP (· == pairA rx ry) (slotA · .AUTO off), "STP"⟩
  | _ => throw s!"v{v.id}: frame variable aux on {v.op.name}"

/-- What `v` emits in G6, or why it is outside the slice. -/
def vkind6 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if (markOp? v.op).isSome then vkind5 lc g v
  else if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  else do
    match ← frameVar? lc g v with
    | none => vkind5 lc g v
    | some (_, off) => vkindVar lc v off

/-- Slice G6 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG6 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind6 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  if let some i := (List.range lc.homes.size).find? (!homeOK4 lc ·) then throw (homeErr lc i)
  checkFrame lc g
  checkVars lc g
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
  checkK lc kt
  let ids := ps.toList.map (·.id)
  unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
  return (tab, kt)

end GoFV.Gen.Check
