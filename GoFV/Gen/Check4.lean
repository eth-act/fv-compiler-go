import GoFV.Gen.Check3

/-!
# The genssa validator, slice G4: register pairs (`docs/plans/proofs3.md` §4)

`checkG4 lc ps bstart g` extends slice G3 (`GoFV/Gen/Check3.lean`) by the 64-bit pair accesses
and the components of a pair, the first part of G4 (register pairs and tuples). It returns G3's
PC table and class table; the class table follows a pair home as a call's `results` home
(`kStep`: each register of the pair takes its component's class).

**Values** beyond G3's (`vkind4`):

* `LDP [off] a mem` homed in a register pair `(Ra, Rb)`, two distinct registers G1 may write: the
  pair load `LDP off(Rn), (Ra, Rb)` of an address in a 64-bit register (no symbol), each
  component of an integer class of at least 8 bits;
* `STP [off] a x y mem`: the pair store `STP (Rx, Ry), off(Rn)` of two 64-bit registers to an
  address in a 64-bit register (no symbol);
* `Select0`/`Select1` of an `LDP`, homed in the register of its component (no code).

`GoFV/Proof/Gen/G4.lean` proves what an accepted function satisfies (`g4_value`, `g4_term`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The register pair operand `(Ra, Rb)` (`TYPE_REGREG`: the first register in `reg`, the second
in `offset`). -/
def pairA (ra rb : Int) : Addr := { type := .REGREG, reg := ra, offset := rb }

/-- The two registers of a pair home. -/
def pairHome? (lc : LocCtx) (id : ID) : Option (Nat × Nat) :=
  match lc.home id with
  | some (.pair (some a) (some b)) => some (a, b)
  | _ => none

/-- The two component shapes of a pair load's tuple, each of an integer class of at least 8 bits. -/
def pairTys (t : Ty) : Bool :=
  match t with
  | .tuple [t0, t1] => (cls t0).any (8 ≤ ·) && (cls t1).any (8 ≤ ·)
  | _ => false

/-- What `v` emits in G4, or why it is outside the slice. -/
def vkind4 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  match v.op with
  | .ARM64LDP =>
    unless v.args.size == 2 && v.aux == none && pairTys (lc.ty v.id) do
      throw s!"v{v.id}: pair load shape"
    let (ca, rn) ← argObj lc v 0
    unless ca == 64 do throw s!"v{v.id}: address width"
    memArg lc v 1
    let some (ra, rb) := pairHome? lc v.id | throw s!"v{v.id}: pair load home"
    unless ra != rb && ra != zeroReg && rb != zeroReg && destOK ra && destOK rb do
      throw s!"v{v.id}: pair load registers"
    let some oa := objOf? ra | throw s!"v{v.id}: register {ra}"
    let some ob := objOf? rb | throw s!"v{v.id}: register {rb}"
    return .prog (.ofShape { as := .LDP, from_ := memA rn v.auxInt.toInt, to := pairA oa ob })
  | .ARM64STP =>
    unless v.args.size == 4 && v.aux == none && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: pair store shape"
    let (ca, rn) ← argObj lc v 0
    let (cx, rx) ← argObj lc v 1
    let (cy, ry) ← argObj lc v 2
    memArg lc v 3
    unless ca == 64 && cx == 64 && cy == 64 do throw s!"v{v.id}: pair store widths"
    return .prog (.ofShape { as := .STP, from_ := pairA rx ry, to := memA rn v.auxInt.toInt })
  | .Select0 | .Select1 =>
    let some c := v.args[0]? | throw s!"v{v.id}: select shape"
    let some u := lc.ctx.f.value? c | throw s!"v{v.id}: select of v{c}"
    unless v.args.size == 1 && u.op == .ARM64LDP do throw s!"v{v.id}: select of {u.op.name}"
    let some (ra, rb) := pairHome? lc c | throw s!"v{v.id}: select of a pair without registers"
    let i := if v.op == .Select0 then 0 else 1
    let r := if v.op == .Select0 then ra else rb
    unless lc.home v.id == some (.reg r) && (cls (lc.ty v.id)).isSome &&
        ((tupleTys (lc.ty c))[i]?.bind cls) == cls (lc.ty v.id) do
      throw s!"v{v.id}: select home"
    return .none
  | _ => vkind3 lc g v

/-- The home of value `i` is one G4 handles: G3's, or a register pair. -/
def homeOK4 (lc : LocCtx) (i : Nat) : Bool :=
  match lc.home i with
  | some (.pair _ _) => true
  | _ => homeOK3 lc i

/-- Slice G4 of the genssa validator (module doc): the PC table and the class table of the
accepted function. -/
def checkG4 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind4 lc g, tm := cx.termG3 }
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
