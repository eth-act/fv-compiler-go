import GoFV.Gen.Check37

/-!
# The genssa validator, slice G38: the acquire loads (`docs/plans/proofs3.md` §4)

`checkG38 lc ps bstart g` is slice G37 (`GoFV/Gen/Check37.lean`) with, in a function with an
arm64 op, the acquire loads and their components:

* `LDAR`, `LDARW`, `LDARB p mem` (`ldar? : (as, n)`): `LDAR`/`LDARW`/`LDARB (Rn), Rd`, the `n`
  bytes at the address in a 64-bit register (no symbol, offset 0), zero-extended into `Rd`. The
  value is a tuple of a component of class `8n` (an integer of `n` bytes or, for `n = 8`, a
  pointer) and the memory, homed in the register pair `(Rd, -)`, `Rd` a register G1 may write;
  no temporary;
* `Select0` of an acquire load, homed in the load's register (no code);
* `Select1` of an acquire load: the memory, without a home (no code).

The G38 values empty the upper-bit table (`uStep35` is `[]` on them).

On a function with no arm64 op, `checkG38` is `checkG33`'s `checkNL30`.
`GoFV/Proof/Gen/G38.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The acquire loads, their opcode and their bytes. -/
def ldar? : Op → Option (As × Nat)
  | .ARM64LDAR => some (.LDAR, 8) | .ARM64LDARW => some (.LDARW, 4)
  | .ARM64LDARB => some (.LDARB, 1)
  | _ => none

/-- The register of an acquire load's pair home `(Rd, -)`. -/
def ldarHome? (lc : LocCtx) (id : ID) : Option Nat :=
  match lc.home id with
  | some (.pair (some r) none) => some r
  | _ => none

/-- The shape of an acquire load of `n` bytes: a component of class `8n`, then the memory. -/
def ldarTy (n : Nat) (t : Ty) : Bool :=
  match t with
  | .tuple [t0, .mem] => cls t0 == some (8 * n)
  | _ => false

/-- An acquire load of `n` bytes (module doc): what it emits. -/
def ldarKind (lc : LocCtx) (v : Value) (as : As) (n : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && v.aux == none && v.auxInt.toInt == 0 && ldarTy n (lc.ty v.id) do
    throw s!"v{v.id}: acquire load shape"
  let (ca, rn) ← argObj lc v 0
  unless ca == 64 do throw s!"v{v.id}: address width"
  memArg lc v 1
  let some r := ldarHome? lc v.id | throw s!"v{v.id}: acquire load home"
  unless r != zeroReg && destOK r do throw s!"v{v.id}: acquire load register"
  let some rd := objOf? r | throw s!"v{v.id}: register {r}"
  return .prog ⟨plain as (· == memA rn 0) (· == regA rd), as.name⟩

/-- `Select0`/`Select1` of an acquire load. -/
def selLdar (lc : LocCtx) (v : Value) : Bool :=
  (v.op == .Select0 || v.op == .Select1) &&
    ((v.args[0]?).bind lc.ctx.f.value?).any fun u => (ldar? u.op).isSome

/-- The shape of the acquire load a component selects from: a component with a class, then the
memory. -/
def ldarSelTy (t : Ty) : Bool :=
  match t with
  | .tuple [t0, .mem] => (cls t0).isSome
  | _ => false

/-- A component of an acquire load (module doc): no code. -/
def selLdarKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let some c := v.args[0]? | throw s!"v{v.id}: select shape"
  unless v.args.size == 1 && ldarSelTy (lc.ty c) do throw s!"v{v.id}: select shape"
  let some r := ldarHome? lc c | throw s!"v{v.id}: select of a load without a register"
  if v.op == .Select0 then
    unless lc.home v.id == some (.reg r) && r != zeroReg && destOK r && (objOf? r).isSome &&
        (cls (lc.ty v.id)).isSome && ((tupleTys (lc.ty c))[0]?.bind cls) == cls (lc.ty v.id) do
      throw s!"v{v.id}: select home"
  else
    unless memTy (lc.ty v.id) && lc.home v.id == none do throw s!"v{v.id}: select home"
  return .none

/-- What `v` emits in G38, or why it is outside the slice. -/
def vkind38 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match ldar? v.op with
  | some (as, n) => ldarKind lc v as n
  | none => if selLdar lc v then selLdarKind lc v else vkind37 lc g v

/-- Slice G38 of the genssa validator (module doc): G37's check with G38's value check. -/
def checkG38 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind38 lc g, tm := cx.termG3 }
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

end GoFV.Gen.Check
