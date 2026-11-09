import GoFV.Gen.Check47

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G50: the narrow and float pair loads (`docs/plans/proofs3.md` §4)

G4 accepts the 64-bit pair load `LDP` into two X registers. G50 adds to G47 the other pair loads
genssa emits through the same case of `ssaGenValue` (`LDP*`/`FLDP*`: `op off(Rn), (Ra, Rb)`):

* `LDPW` and `LDPSW` (`pairOp50`: 4-byte elements, zero- or sign-extended to 64 bits), into two
  distinct X registers G1 may write, each component of an integer class of at least 8 bits
  (`pairTys`, as `LDP`);
* `FLDPD` and `FLDPS` (8- and 4-byte elements), into two distinct V registers, each component a
  float shape of the element's width (`fpairTys`);
* `Select0`/`Select1` of such a pair load (no code): homed in the register of its component, an X
  register G1 may write (as G4's selects of `LDP`) or, for `FLDPD`/`FLDPS`, a V register at the
  component's float shape.

The address is a 64-bit register plus the offset (no symbol), as G4's `LDP`. `checkG50 lc ps bstart
g` is slice G47 (`GoFV/Gen/Check47.lean`) with these values (`pair50`, tried when G47 rejects a
value). `GoFV/Proof/Gen/G50.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The pair loads of G50: opcode, element bytes, sign extension, V registers. -/
def pairOp50 (op : Op) : Option (As × Nat × Bool × Bool) :=
  if op = .ARM64LDPW then some (.LDPW, 4, false, false)
  else if op = .ARM64LDPSW then some (.LDPSW, 4, true, false)
  else if op = .ARM64FLDPD then some (.FLDPD, 8, false, true)
  else if op = .ARM64FLDPS then some (.FLDPS, 4, false, true)
  else none

/-- The two component shapes of a float pair load of `n`-byte elements: float shapes of `8n`
bits. -/
def fpairTys (t : Ty) (n : Nat) : Bool :=
  match t with
  | .tuple [t0, t1] => fTy t0 && fTy t1 && cls t0 == some (8 * n) && cls t1 == some (8 * n)
  | _ => false

/-- A G50 pair load `as off(Rn), (Ra, Rb)` of `n`-byte elements, into V registers if `fp`. -/
def ldp50 (lc : LocCtx) (v : Value) (as : As) (n : Nat) (fp : Bool) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && v.aux == none &&
      (if fp then fpairTys (lc.ty v.id) n else pairTys (lc.ty v.id)) do
    throw s!"v{v.id}: pair load shape"
  let (ca, rn) ← argObj lc v 0
  unless ca == 64 do throw s!"v{v.id}: address width"
  memArg lc v 1
  let some (ra, rb) := pairHome? lc v.id | throw s!"v{v.id}: pair load home"
  unless ra != rb do throw s!"v{v.id}: pair load registers"
  if fp then
    let some oa := fobjOf? ra | throw s!"v{v.id}: register {ra}"
    let some ob := fobjOf? rb | throw s!"v{v.id}: register {rb}"
    return .prog (.ofShape { as, from_ := memA rn v.auxInt.toInt, to := pairA oa ob })
  else
    unless ra != zeroReg && rb != zeroReg && destOK ra && destOK rb do
      throw s!"v{v.id}: pair load registers"
    let some oa := objOf? ra | throw s!"v{v.id}: register {ra}"
    let some ob := objOf? rb | throw s!"v{v.id}: register {rb}"
    return .prog (.ofShape { as, from_ := memA rn v.auxInt.toInt, to := pairA oa ob })

/-- `Select0`/`Select1` of the G50 pair load `c` of `n`-byte elements (into V registers if `fp`):
homed in the register of its component (no code). -/
def sel50 (lc : LocCtx) (v : Value) (c : ID) (n : Nat) (fp : Bool) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 && (if fp then fpairTys (lc.ty c) n else pairTys (lc.ty c)) do
    throw s!"v{v.id}: select shape"
  let some (ra, rb) := pairHome? lc c | throw s!"v{v.id}: select of a pair without registers"
  let i := if v.op == .Select0 then 0 else 1
  let r := if v.op == .Select0 then ra else rb
  unless lc.home v.id == some (.reg r) && (cls (lc.ty v.id)).isSome &&
      ((tupleTys (lc.ty c))[i]?.bind cls) == cls (lc.ty v.id) do
    throw s!"v{v.id}: select home"
  if fp then
    unless (fobjOf? r).isSome && fTy (lc.ty v.id) do throw s!"v{v.id}: select home"
  else
    unless r != zeroReg && destOK r && (objOf? r).isSome do throw s!"v{v.id}: select home"
  return .none

/-- G50's values (module doc), or why `v` is outside the slice; `e` is G47's reason, kept for the
other values. -/
def pair50 (lc : LocCtx) (v : Value) (e : String) : Except String VKind2 :=
  match pairOp50 v.op with
  | some (as, n, _, fp) => ldp50 lc v as n fp
  | none =>
    if v.op = .Select0 ∨ v.op = .Select1 then
      match v.args[0]? with
      | some c =>
        match (lc.ctx.f.value? c).bind (pairOp50 ·.op) with
        | some (_, n, _, fp) => sel50 lc v c n fp
        | none => .error e
      | none => .error e
    else .error e

/-- What `v` emits in G50, or why it is outside the slice: G47's kinds, then G50's pair loads and
their components. -/
def vkind50 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind47 lc g v with
  | .ok kd => .ok kd
  | .error e => pair50 lc v e

/-- G47's check with G50's value check. -/
def checkG50L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind50 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
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
  else checkNL30 lc ps bstart g

/-- Slice G50 of the genssa validator (module doc): `refsLive`, then G50's check on `liveCtx lc`. -/
def checkG50 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG50L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
