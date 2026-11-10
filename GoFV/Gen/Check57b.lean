import GoFV.Gen.Check49

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G57, group B: `DMB`, `PRFM`, float stores to frame variables
(`docs/plans/proofs3.md` §4)

The values of slice G57's group B, each one Prog of `ssaGenValue`
(`GoFV/Gen/Arm64Value.lean`, `Arm64ValueRt.lean`), of no temporary:

* `DMB [k] mem` (`PubBarrier`): `DMB $k` (`dmbShape`), a memory with no home (`mem57`);
* `PRFM [k] addr mem` (`PrefetchCache*`): `PRFM 0(Rn), $k` (`prfmShape`, `Rn` the register of
  `addr`), a memory with no home;
* `FMOVSstore`/`FMOVDstore [off] {x} SP val mem` of a frame variable `x`: `FMOVS`/`FMOVD Fs,
  off(<nc>)` (`fvarStore57`), `val` a float of the op's width;
* `FSTPS`/`FSTPD [off] {x} SP a b mem` of a frame variable `x`: `FSTPS`/`FSTPD (Fa, Fb),
  off(<nc>)` (`fvarStp57`), `a` and `b` floats of the op's element width (`fstpOf`).

A frame variable is accessed at its operand as G49 (`frameVar49?`: a `Blk.local` block, operand
`NAME_PARAM` or `NAME_AUTO`) or G6 (`frameVar?`: a `Blk.temp` block, operand `NAME_AUTO`) does
(`fvar57?`). `vkind57b lc g v` is `none` exactly off these ops (`op57b`), and off a frame
variable for the float stores. `GoFV/Proof/Gen/G57b.lean` proves what an accepted value
satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `DMB $k`. -/
def dmbShape (k : Int) : Shape := { as := .DMB, from_ := constA k }

/-- `PRFM 0(Rn), $k`. -/
def prfmShape (rn k : Int) : Shape := { as := .PRFM, from_ := memA rn 0, to := constA k }

/-- The float pair stores: element bytes. -/
def fstpOf (op : Op) : Option Nat :=
  if op = .ARM64FSTPD then some 8 else if op = .ARM64FSTPS then some 4 else none

/-- The opcode of a float pair store of `n`-byte elements. -/
def fstpAs (n : Nat) : As := if n == 4 then .FSTPS else .FSTPD

/-- The operand class and offset of an access of a frame variable: G49's (`Blk.local`), else
G6's (`Blk.temp`, `NAME_AUTO`). -/
def fvar57? (lc : LocCtx) (g : G2In) (v : Value) : Option (AddrName × Int) :=
  match frameVar49? lc g v with
  | some (_, nc, off) => some (nc, off)
  | none =>
    match frameVar? lc g v with
    | .ok (some (_, off)) => some (.AUTO, off)
    | _ => none

/-- `DMB [k] mem`: `DMB $k`. -/
def dmb57 (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: barrier shape"
  memArg lc v 0
  return .prog (.ofShape (dmbShape v.auxInt.toInt))

/-- `PRFM [k] addr mem`: `PRFM 0(Rn), $k`. -/
def prfm57 (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: prefetch shape"
  let (_, rn) ← argObj lc v 0
  memArg lc v 1
  return .prog (.ofShape (prfmShape rn v.auxInt.toInt))

/-- `FMOVSstore`/`FMOVDstore` of a frame variable at the operand `nc`, `off`:
`FMOVS`/`FMOVD Fs, off(<nc>)`. -/
def fvarStore57 (lc : LocCtx) (v : Value) (nc : AddrName) (off : Int) :
    Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: store shape"
  let (cs, rs) ← fargObj lc v 1
  memArg lc v 2
  unless cs == 8 * fBytes v.op do throw s!"v{v.id}: store widths"
  return .prog ⟨plain (fmovAs cs) (· == regA rs) (slotA · nc off), (fmovAs cs).name⟩

/-- `FSTPS`/`FSTPD` of `n`-byte elements to a frame variable at the operand `nc`, `off`:
`FSTPS`/`FSTPD (Fa, Fb), off(<nc>)`. -/
def fvarStp57 (lc : LocCtx) (v : Value) (n : Nat) (nc : AddrName) (off : Int) :
    Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: pair store shape"
  let (cx, rx) ← fargObj lc v 1
  let (cy, ry) ← fargObj lc v 2
  memArg lc v 3
  unless cx == 8 * n && cy == 8 * n do throw s!"v{v.id}: pair store widths"
  return .prog ⟨plain (fstpAs n) (· == pairA rx ry) (slotA · nc off), (fstpAs n).name⟩

/-- The ops of G57's group B. -/
def op57b (op : Op) : Bool :=
  op == .ARM64DMB || op == .ARM64PRFM || op == .ARM64FMOVSstore || op == .ARM64FMOVDstore ||
    (fstpOf op).isSome

/-- What `v` emits if it is one of G57's group B (module doc), else `none`. -/
def vkind57b (lc : LocCtx) (g : G2In) (v : Value) : Option (Except String VKind2) :=
  if v.op = .ARM64DMB then some (dmb57 lc v)
  else if v.op = .ARM64PRFM then some (prfm57 lc v)
  else if v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore then
    (fvar57? lc g v).map fun (nc, off) => fvarStore57 lc v nc off
  else
    match fstpOf v.op with
    | some n => (fvar57? lc g v).map fun (nc, off) => fvarStp57 lc v n nc off
    | none => none

end GoFV.Gen.Check
