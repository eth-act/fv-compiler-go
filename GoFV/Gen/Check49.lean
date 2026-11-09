import GoFV.Gen.Check50

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G49: frame variables in `Blk.local` blocks
(`docs/plans/proofs3.md` §8, item 8)

Slice G6 (`GoFV/Gen/Check6.lean`) accesses only the frame variables whose block is `Blk.temp`: a
`PAUTO` whose address the function never converts to an integer, at its `NAME_AUTO` operand.
The other frame variables have a `Blk.local` block (`Tables.forgeable`, `frameBlk`):

* every parameter and result (`PPARAM`, `PPARAMOUT`), addressed at its `NAME_PARAM` operand in
  the caller's argument area, `SP + autosize + 8 + off` (`frameOff .PARAM`): a stack-assigned
  parameter where the caller stored it, a register-assigned one where genssa's entry stores put it
  (`MOVD R1, x+8(FP)`), a result before `MakeResult` reads it;
* a `PAUTO` whose address the function converts to an integer (`addrconv`), at its `NAME_AUTO`
  operand.

G49 accepts G6's accesses (`MOVDaddr`, the loads and stores of G3, `LDP`, `STP`) of such a
variable at its operand (`frameVar49?`, `vkindVar49`). The address assignment places a `Blk.local`
block at its own address (`AddrAgree`), so the proof (`GoFV/Proof/Gen/G49.lean`) takes the
variables' places as a premise of the activation (`VarsAt49`), which the machine instance of
`docs/plans/proofs3.md` §8 item 4 satisfies with these bases.

**Frame** (`checkVars49`, in place of G6's `checkVars`): every accessed variable has a window from
`Ctx.locals`; a `NAME_AUTO` window lies inside the locals, a `NAME_PARAM` window inside the
function's argument area (`argEnd`: the end of its ABI's spill area, without the fixed frame
word); windows of one operand class are pairwise disjoint and away from the home slots of that
class (8 bytes each).

`checkG49 lc ps bstart g` is slice G50 (`GoFV/Gen/Check50.lean`, which G49 follows: G48 is
reserved) with these values (tried when G50 rejects a value) and this frame check.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The address operand `$off(<nc>)` of a frame operand of class `nc` (`TYPE_ADDR`). -/
def addrN (a : Addr) (nc : AddrName) (off : Int) : Bool :=
  a.type == .ADDR && slotA { a with type := .MEM } nc off

/-- The variable, operand class and operand offset of an access `v` of a frame variable whose
block is `Blk.local` (`Tables.forgeable`): its aux names a variable with a `NAME_PARAM` or a
`NAME_AUTO` operand in the frame layout, and its first argument is `SP`. -/
def frameVar49? (lc : LocCtx) (g : G2In) (v : Value) : Option (AuxRef × AddrName × Int) :=
  match v.aux with
  | none => none
  | some x =>
    if isVar lc x && spArg lc v && lc.ctx.tabs.forgeable x then
      match varOp g x with
      | some (.AUTO, off) => some (x, .AUTO, off + v.auxInt.toInt)
      | some (.PARAM, off) => some (x, .PARAM, off + v.auxInt.toInt)
      | _ => none
    else none

/-- What an access of a frame variable at the operand `nc`, `off` emits (`vkindVar` at any
operand class). -/
def vkindVar49 (lc : LocCtx) (v : Value) (nc : AddrName) (off : Int) : Except String VKind2 := do
  if v.op == .ARM64MOVDaddr then
    unless v.args.size == 1 do throw s!"v{v.id}: address shape"
    let (c, rd) ← resObj lc v
    unless c == 64 do throw s!"v{v.id}: address width"
    return .prog ⟨plain .MOVD (addrN · nc off) (· == regA rd), "MOVD $var"⟩
  if let some (as, n, sg) := loadOp? v.op then
    unless v.args.size == 2 do throw s!"v{v.id}: load shape"
    memArg lc v 1
    let (c, rd) ← resObj lc v
    unless 8 ≤ c || (c == 1 && n == 1 && !sg) do throw s!"v{v.id}: load widths"
    return .prog ⟨plain as (slotA · nc off) (· == regA rd), as.name⟩
  if let some (as, n) := storeOp? v.op then
    unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: store shape"
    let (cs, rs) ← argObj lc v 1
    memArg lc v 2
    unless 8 * n ≤ cs || (cs == 1 && n == 1) do throw s!"v{v.id}: store widths"
    return .prog ⟨plain as (· == regA rs) (slotA · nc off), as.name⟩
  match v.op with
  | .ARM64LDP =>
    unless v.args.size == 2 && pairTys (lc.ty v.id) do throw s!"v{v.id}: pair load shape"
    memArg lc v 1
    let some (ra, rb) := pairHome? lc v.id | throw s!"v{v.id}: pair load home"
    unless ra != rb && ra != zeroReg && rb != zeroReg && destOK ra && destOK rb do
      throw s!"v{v.id}: pair load registers"
    let some oa := objOf? ra | throw s!"v{v.id}: register {ra}"
    let some ob := objOf? rb | throw s!"v{v.id}: register {rb}"
    return .prog ⟨plain .LDP (slotA · nc off) (· == pairA oa ob), "LDP"⟩
  | .ARM64STP =>
    unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: pair store shape"
    let (cx, rx) ← argObj lc v 1
    let (cy, ry) ← argObj lc v 2
    memArg lc v 3
    unless cx == 64 && cy == 64 do throw s!"v{v.id}: pair store widths"
    return .prog ⟨plain .STP (· == pairA rx ry) (slotA · nc off), "STP"⟩
  | _ => throw s!"v{v.id}: frame variable aux on {v.op.name}"

/-- What `v` emits in G49, or why it is outside the slice: G50's kinds, then the accesses of
frame variables in `Blk.local` blocks. -/
def vkind49 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind50 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match frameVar49? lc g v with
    | some (_, nc, off) =>
      if (lc.temps[v.id]?).join != none then .error s!"v{v.id}: temporary register"
      else vkindVar49 lc v nc off
    | none => .error e

/-- The end of the function's argument area at `NAME_PARAM` offsets: the end of its ABI's spill
area (`ABIParam` offsets include the fixed frame word, `NAME_PARAM` offsets do not). -/
def argEnd (lc : LocCtx) : Option Int :=
  match lc.ctx.f.ownAux.bind lc.ctx.tabs.aux? with
  | some { kind := .call _ (some abi), .. } => some (abi.spillOff + abi.spillSize - 8)
  | _ => none

/-- The operand class and window `[off, off + size)` of a frame variable's operand. -/
def varWin49 (lc : LocCtx) (g : G2In) (x : AuxRef) : Option (AddrName × Int × Int) := do
  let (nc, off) ← varOp g x
  let (_, sz, _) ← lc.ctx.locals.find? (·.1 == x)
  return (nc, off, off + sz)

/-- A window inside its operand class's area: the locals for `NAME_AUTO`, the argument area for
`NAME_PARAM`. -/
def winIn49 (lc : LocCtx) (g : G2In) : AddrName × Int × Int → Bool
  | (.AUTO, lo, hi) => lo ≤ hi && -g.stksize ≤ lo && hi ≤ 0
  | (.PARAM, lo, hi) => 0 ≤ lo && lo ≤ hi && (argEnd lc).any (hi ≤ ·)
  | _ => false

/-- Two windows of different operand classes, or disjoint. -/
def winApart49 (w w' : AddrName × Int × Int) : Bool :=
  w.1 != w'.1 || winApart w.2 w'.2

/-- The frame checks of slice G49 (module doc): G6's `checkVars` for the variables of both operand
classes. -/
def checkVars49 (lc : LocCtx) (g : G2In) : Except String Unit := do
  let xs := accessedVars lc
  let ws ← xs.mapM fun x => match varWin49 lc g x with
    | some w => pure w
    | none => throw s!"frame variable a{x}: no window"
  unless ws.all (winIn49 lc g) do
    throw "frame variable outside the locals or the argument area"
  unless (ws.zipIdx).all fun (w, i) => (ws.zipIdx).all fun (w', i') => i == i' || winApart49 w w' do
    throw "two frame variables overlap"
  let slots := (homeSlots lc).filterMap fun k => (g.slotOp k).map fun (nc, o) => (nc, o, o + 8)
  unless ws.all fun w => slots.all (winApart49 w) do
    throw "frame variable over a spill slot"

/-- G50's check with G49's value check and frame check. -/
def checkG49L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind49 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
    if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
    unless cloFirst lc do throw "LoweredGetClosurePtr after code"
    checkFrame lc g
    checkVars49 lc g
    let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
    let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
    checkK lc kt
    let ids := ps.toList.map (·.id)
    unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
    return (tab, kt)
  else checkNL30 lc ps bstart g

/-- Slice G49 of the genssa validator (module doc): `refsLive`, then G49's check on `liveCtx lc`. -/
def checkG49 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG49L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
