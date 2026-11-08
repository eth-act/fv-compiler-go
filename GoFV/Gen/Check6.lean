import GoFV.Gen.Check5

/-!
# The genssa validator, slice G6: frame variables (`docs/plans/proofs3.md` §4)

`checkG6 lc ps bstart g` extends slice G5 (`GoFV/Gen/Check5.lean`) by the addresses of frame
variables and the accesses of frame variables. A frame variable is an `*ir.Name` aux (`PAUTO`,
`PPARAM`, `PPARAMOUT`) with an operand in Go's frame layout: the operand of its slot at offset 0
(`varOp`, G2's `slotOp`: the name class `NAME_AUTO`/`NAME_PARAM` and the `FrameOffset`). Its
accesses address `SP`.

**Values** beyond G5's (`vkind6`):

* `MOVDaddr {x} [off] sp` of a frame variable `x` into a 64-bit register: `MOVD $off'(RSP), Rd`
  (`TYPE_ADDR`) with `x`'s name class and `off' = FrameOffset + off`;
* the loads `MOV{D,B,BU,H,HU,W,WU}load {x} [off] sp mem` and stores
  `MOV{D,B,H,W}store {x} [off] sp v mem` of G3 at `off'(RSP)` with `x`'s name class;
* the pair load `LDP {x} [off] sp mem` and the pair store `STP {x} [off] sp a b mem` of G4 at
  `off'(RSP)`.

G6 is not proven yet: its proof places a frame variable's block at its frame operand under `ι`,
which `AddrAgree` (every block with a Phase 1 address at that address) does not allow
(`docs/plans/proofs3.md` §4).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The slot of frame variable `x` at offset 0 (G2's `slotOp` ignores its type). -/
def varKey (x : AuxRef) : SlotKey :=
  { name := x, type := 0, off := 0, splitOf := none, splitOffset := 0 }

/-- The frame operand of variable `x`: name class and `FrameOffset`. -/
def varOp (g : G2In) (x : AuxRef) : Option (AddrName × Int) := g.slotOp (varKey x)

/-- The frame operand of an access `v` of a frame variable: its aux names a variable with an
operand (`NAME_AUTO` or `NAME_PARAM`) in the frame layout and its address argument is `SP`;
`none` if `v` has no such aux. -/
def frameVar? (lc : LocCtx) (g : G2In) (v : Value) : Except String (Option (AddrName × Int)) := do
  let some x := v.aux | return none
  match lc.ctx.tabs.aux? x with
  | some { kind := .name .., .. } =>
    let some a := v.args[0]? | throw s!"v{v.id}: frame access shape"
    unless (lc.ctx.f.value? a).map (·.op) == some .SP do
      throw s!"v{v.id}: frame variable off another base"
    let some (nc, off) := varOp g x | throw s!"v{v.id}: frame variable without operand"
    unless nc == .AUTO || nc == .PARAM do throw s!"v{v.id}: frame variable operand class"
    return some (nc, off + v.auxInt.toInt)
  | _ => return none

/-- What `v` emits in G6, or why it is outside the slice. -/
def vkind6 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  if (markOp? v.op).isSome then return ← vkind5 lc g v
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  let some (nc, off) ← frameVar? lc g v | vkind5 lc g v
  if v.op == .ARM64MOVDaddr then
    unless v.args.size == 1 do throw s!"v{v.id}: address shape"
    let (c, rd) ← resObj lc v
    unless c == 64 do throw s!"v{v.id}: address width"
    let src (a : Addr) : Bool :=
      a.type == .ADDR && a.name == nc && a.reg == regSP && a.index == 0 && a.offset == off
    return .prog ⟨plain .MOVD src (· == regA rd), "MOVD $var"⟩
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
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
  checkK lc kt
  let ids := ps.toList.map (·.id)
  unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
  return (tab, kt)

end GoFV.Gen.Check
