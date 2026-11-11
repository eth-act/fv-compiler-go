import GoFV.Gen.Check65

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G66b: extensions of a narrow reload (`docs/plans/slot-size.md` §2.3)

Genssa emits an extension `MOV{B,H,W}{,U}reg x` (`ssa.go:1353-1383`, port `genExt` in
`GoFV/Gen/Arm64Value.lean`) as **no code** when `x`, through `Copy` and `MOVDreg`, is a `LoadReg`
of a type of the extension's size and signedness and the two values share a register, and as
`MOVD Rx, Rv` when they do not: the reload already extended (`loadByType`). Every slice before
G66b expects the extension (`vkind3`: `MOVWU Rx, Rv`, …) and rejects such a function at its
Prog (`Prog #: …, expected MOVWU`).

* `elide66b lc v`: genssa's test, `(w, sg)` of the extension when it holds (`copySrc66b` walks the
  copies);
* `extElide66b lc v`: what such an extension emits, with `vkind3`'s checks of an extension
  (no temporary, one argument in an integer register of class `ca` with `w ≤ ca` or a boolean, a
  result register of class at least 8): nothing, or `MOVD`;
* `elideOK66b lc`: every elided extension finds its argument's register at class `w` and
  signedness `sg` in G35's upper-bit table before it (`uL35`; the reload's entry, `reloadEntry35`,
  carried through copies), so the register already holds that extension. The validator reads the
  table rather than trusting the SSA chain; `GoFV/Proof/Gen/G66b.lean` reads the extension off it.

`GoFV/Gen/Check66.lean` (slice G66) tries `extElide66b` before G65's kinds on an extension with
`elide66b`, and checks `elideOK66b`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The value `id` reaches through `Copy` and `MOVDreg` (at most `n` of them; `genExt`'s walk). -/
def copySrc66b (lc : LocCtx) : Nat → ID → Option Value
  | 0, _ => none
  | n + 1, a =>
    match lc.ctx.f.value? a with
    | some u =>
      if u.op == .Copy || u.op == .ARM64MOVDreg then
        match u.args[0]? with
        | some b => copySrc66b lc n b
        | none => none
      else some u
    | none => none

/-- Genssa's test for an extension it elides (`genExt`): `v` is an extension (`extOp?`: `w` bits,
signed `sg`) whose argument, through copies, is a `LoadReg` of a type of `w / 8` bytes and
signedness `sg` (`typeSigned`, Go's `t.IsSigned()`). -/
def elide66b (lc : LocCtx) (v : Value) : Option (Nat × Bool) :=
  match extOp? v.op, v.args[0]? with
  | some (_, w, sg), some a =>
    match copySrc66b lc lc.ctx.f.valueTab.size a with
    | some u =>
      if u.op == .LoadReg && typeSize? lc.ctx.tabs u.type == some (w / 8) &&
          typeSigned lc.ctx.tabs u.type == sg then some (w, sg)
      else none
    | none => none
  | _, _ => none

/-- An extension genssa elides (module doc): `vkind3`'s checks of an extension, then no code when
`v` shares its argument's register, `MOVD Rx, Rv` otherwise. -/
def extElide66b (lc : LocCtx) (v : Value) : Except String VKind2 := do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  let some (_, w, _) := extOp? v.op | throw s!"v{v.id}: no extension"
  unless v.args.size == 1 do throw s!"v{v.id}: extension shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless (w ≤ ca || ca == 1) && 8 ≤ c do throw s!"v{v.id}: extension widths"
  if rn == rd then return .none
  return .prog (.ofShape { as := .MOVD, from_ := regA rn, to := regA rd })

/-- Every extension genssa elides (`elide66b`: `w` bits, signed `sg`) finds its argument's register
at class `w` and signedness `sg` in G35's upper-bit table before it. -/
def elideOK66b (lc : LocCtx) : Bool :=
  lc.ctx.f.blocks.toList.all fun bid =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b => (List.range b.values.size).all fun i =>
      match (b.values[i]?).bind lc.ctx.f.value? with
      | some v =>
        match elide66b lc v with
        | none => true
        | some (w, sg) =>
          match (v.args[0]?).bind (regHome? lc) with
          | some r => (uL35 lc (uIn35 lc bid) b i).contains (r, w, sg)
          | none => false
      | none => true

end GoFV.Gen.Check
