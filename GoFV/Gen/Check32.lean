import GoFV.Gen.Check30

/-!
# The genssa validator, slice G32: simple ops (`docs/plans/proofs3.md` §4)

`checkG32 lc ps bstart g` is slice G30 (`GoFV/Gen/Check30.lean`) with more single-instruction ops in
a function with an arm64 op:

* the register ops `MUL`, `MNEG`, `AND`, `OR`, `XOR`, `BIC`, `EON`, `ORN x y` (`bin32?`), which
  genssa emits as `op Rm, Rn, Rd` (`x` in `Rn`, `y` in `Rm`);
* the constant ops `ORconst`, `XORconst [k] x` (`binK32?`): `ORR`/`EOR $k, Rn, Rd`;
* the unary ops `NEG`, `MVN x` (`un32?`): `NEG`/`MVN Rm, Rd`;
* `CSINC [cc] x y f`: `CSINC cond, Rx, Ry, Rd` (`x` if the condition holds, else `y + 1`);
* the store-release `STLR`, `STLRW`, `STLRB p x mem` (`stlr?`): `STLR{,W,B} Rx, (Rp)`.

The result of each ALU op on its low `c` bits depends only on its operands' low `c` bits, so G32
accepts one with no temporary, register arguments of classes at least the result's class `c ≥ 8`.
`AND`, `OR` and `XOR` of two booleans and `XORconst [1]` of a boolean (Go's `!`) are also accepted:
on registers holding 0 or 1 they give 0 or 1.
A select's flags argument is last, with no home, and its auxint names a condition (as G25's
`CSEL`). A store-release has no symbol and offset 0, a 64-bit address register, and a value
register of exactly the access's width (`runLoc` stores it as the generic `AtomicStore{8,32,64}`,
whose encoding of a value of another class differs from the machine's bytes); its result is the
memory, with no home.

On a function with no arm64 op, `checkG32` is `checkG30`'s `checkNL30`.
`GoFV/Proof/Gen/G32.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The register ops of G32 and their opcode: `op Rm, Rn, Rd`. -/
def bin32? : Op → Option As
  | .ARM64MUL => some .MUL | .ARM64MNEG => some .MNEG | .ARM64AND => some .AND
  | .ARM64OR => some .ORR | .ARM64XOR => some .EOR | .ARM64BIC => some .BIC
  | .ARM64EON => some .EON | .ARM64ORN => some .ORN
  | _ => none

/-- The constant ops of G32 and their opcode: `op $k, Rn, Rd`. -/
def binK32? : Op → Option As
  | .ARM64ORconst => some .ORR | .ARM64XORconst => some .EOR
  | _ => none

/-- The unary ops of G32 and their opcode: `op Rm, Rd`. -/
def un32? : Op → Option As
  | .ARM64NEG => some .NEG | .ARM64MVN => some .MVN
  | _ => none

/-- The store-release ops, their opcode and bytes: `op Rx, (Rp)`. -/
def stlr? : Op → Option (As × Nat)
  | .ARM64STLR => some (.STLR, 8) | .ARM64STLRW => some (.STLRW, 4)
  | .ARM64STLRB => some (.STLRB, 1)
  | _ => none

/-- A `CSINC` Prog: the condition `cc` in `from_`, `Rn` in `reg`, `Rm` the one `RestArgs` source,
`Rd` in `to`. -/
def csincOK (cc rn rm rd : Int) (p : Prog) : Bool :=
  p.as == .CSINC && p.from_ == specA cc && p.reg == rn && p.to == regA rd && p.scond == 0 &&
    p.regTo2 == 0 && p.rest.size == 1 && (p.rest[0]?.map (·.2)) == some (regA rm)

/-- The register ops that keep booleans boolean (0 or 1 in, 0 or 1 out). -/
def boolBin (as : As) : Bool := as == .AND || as == .ORR || as == .EOR

/-- A register op `x op y` (module doc): what it emits. -/
def bin32Kind (lc : LocCtx) (v : Value) (as : As) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless (8 ≤ c && c ≤ ca && c ≤ cb) || (c == 1 && ca == 1 && cb == 1 && boolBin as) do
    throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd })

/-- A constant op `x op k` (module doc): what it emits. -/
def binK32Kind (lc : LocCtx) (v : Value) (as : As) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless (8 ≤ c && c ≤ ca) || (c == 1 && ca == 1 && as == .EOR && v.auxInt.toInt == 1) do
    throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd })

/-- A unary op `op x` (module doc): what it emits. -/
def un32Kind (lc : LocCtx) (v : Value) (as : As) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (ca, rm) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && c ≤ ca do throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := regA rm, to := regA rd })

/-- `CSINC [cc] x y f` (module doc): what it emits. -/
def csincKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 do throw s!"v{v.id}: select shape"
  let some f := v.args[2]? | throw s!"v{v.id}: select shape"
  unless (lc.ty f).isFlags && lc.home f == none do throw s!"v{v.id}: select condition argument"
  let some o := ccOp? v.auxInt | throw s!"v{v.id}: select condition"
  unless (Cond.ofOp o).isSome do throw s!"v{v.id}: select condition"
  let some cc := ARM64.condBits o | throw s!"v{v.id}: select condition"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && c ≤ ca && c ≤ cb do throw s!"v{v.id}: select widths"
  return .prog ⟨csincOK cc rn rm rd, "CSINC"⟩

/-- A store-release of `n` bytes (module doc): what it emits. -/
def stlrKind (lc : LocCtx) (v : Value) (as : As) (n : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none && v.aux == none &&
      v.auxInt.toInt == 0 do
    throw s!"v{v.id}: store-release shape"
  let (ca, rn) ← argObj lc v 0
  let (cs, rs) ← argObj lc v 1
  memArg lc v 2
  unless ca == 64 && cs == 8 * n do throw s!"v{v.id}: {v.op.name} widths"
  return .prog ⟨plain as (· == regA rs) (· == memA rn 0), as.name⟩

/-- What `v` emits in G32, or why it is outside the slice. -/
def vkind32 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match bin32? v.op, binK32? v.op, un32? v.op, stlr? v.op with
  | some as, _, _, _ => bin32Kind lc v as
  | _, some as, _, _ => binK32Kind lc v as
  | _, _, some as, _ => un32Kind lc v as
  | _, _, _, some (as, n) => stlrKind lc v as n
  | none, none, none, none => if v.op == .ARM64CSINC then csincKind lc v else vkind28 lc g v

/-- Slice G32 of the genssa validator (module doc): G29's check with G32's value check on a
function with an arm64 op, `checkNL30` on one without. -/
def checkG32 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind32 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK29 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
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
