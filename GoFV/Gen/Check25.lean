import GoFV.Gen.Check24

/-!
# The genssa validator, slice G25: conditional selects and bit tests (`docs/plans/proofs3.md` §4)

`checkG25 lc ps bstart g` extends slice G24 (`GoFV/Gen/Check24.lean`) by

* `CSEL [cc] x y f` and `CSEL0 [cc] x f`, which genssa emits as `CSEL cond, Rx, Ry, Rd` and
  `CSEL cond, Rx, ZR, Rd` (`ssa.go`, `condBits[cc]`): `Rd` gets `Rx` when the condition holds on
  `NZCV`, else `Ry` (`ZR`). `runLoc` runs them as `Arm64.csel`/`Arm64.csel0`: the register of
  `x` or of `y` (0) by the condition on the flags argument (`Arm64.condOn`), `poison` when a flag
  bit it reads is unknown. G25 accepts such a value with no temporary, the auxint an op number that
  names a condition (`Cond.ofOp`, as `Cond.ofAux` reads it), the flags argument last with no
  home, register arguments of classes at least the result's class `c ≥ 8`;
* `TSTconst [k] x` (`TST $k, Rn`) and `TSTWconst [k] x` (`TSTW $k, Rn`): the flags of `ANDS`
  (`logicFlags`), with no temporary, a flags result and no home, the argument's class covering
  the test's datasize or `0 ≤ k < 2 ^ class` (`tstOK`: the bits above a narrow class are unknown,
  and `k` does not read them).

`GoFV/Proof/Gen/G25.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The op a `CCop` auxint names (`Cond.ofAux` reads its condition from it). -/
def ccOp? (k : Int64) : Option Op := if k.toInt < 0 then none else Op.ofGoNum? k.toInt.toNat

/-- A `CSEL` Prog: the condition `cc` in `from_`, `Rn` in `reg`, `Rm` the one `RestArgs` source,
`Rd` in `to`. -/
def cselOK (cc rn rm rd : Int) (p : Prog) : Bool :=
  p.as == .CSEL && p.from_ == specA cc && p.reg == rn && p.to == regA rd && p.scond == 0 &&
    p.regTo2 == 0 && p.rest.size == 1 && (p.rest[0]?.map (·.2)) == some (regA rm)

/-- `CSEL`/`CSEL0` (module doc): what it emits. -/
def cselKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let c0 := v.op == .ARM64CSEL0
  unless v.args.size == (if c0 then 2 else 3) do throw s!"v{v.id}: select shape"
  let some f := v.args[if c0 then 1 else 2]? | throw s!"v{v.id}: select shape"
  unless (lc.ty f).isFlags && lc.home f == none do throw s!"v{v.id}: select condition argument"
  let some o := ccOp? v.auxInt | throw s!"v{v.id}: select condition"
  unless (Cond.ofOp o).isSome do throw s!"v{v.id}: select condition"
  let some cc := ARM64.condBits o | throw s!"v{v.id}: select condition"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← if c0 then pure (64, ARM64.REG_R0 + 31) else argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && c ≤ ca && c ≤ cb do throw s!"v{v.id}: select widths"
  return .prog ⟨cselOK cc rn rm rd, "CSEL"⟩

/-- The bits a test of datasize `w` (`TST` 64, `TSTW` 32) reads of an argument of class `ca` are
known: the class covers the datasize, or the constant `k` has no bit at or above `ca` (the
register's bits above a narrow class are unknown). -/
def tstOK (w ca : Nat) (k : Int) : Bool := w ≤ ca || (0 ≤ k && k < 2 ^ ca)

/-- `TSTconst`/`TSTWconst` (module doc): what it emits. -/
def tstKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 && (lc.ty v.id).isFlags && lc.home v.id == none do
    throw s!"v{v.id}: test shape"
  let (ca, rn) ← argObj lc v 0
  let w := v.op == .ARM64TSTconst
  unless tstOK (if w then 64 else 32) ca v.auxInt.toInt do throw s!"v{v.id}: test widths"
  let as : As := if w then .TST else .TSTW
  return .prog (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn })

/-- What `v` emits in G25, or why it is outside the slice. -/
def vkind25 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .ARM64CSEL || v.op == .ARM64CSEL0 then cselKind lc v
  else if v.op == .ARM64TSTconst || v.op == .ARM64TSTWconst then tstKind lc v
  else vkind24 lc g v

/-- Slice G25 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG25 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind25 lc g, tm := cx.termG3 }
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

end GoFV.Gen.Check
