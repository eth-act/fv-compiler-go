import GoFV.Asm.Obj7

/-!
# P0': `progedit`'s float constant loads (`docs/plans/proofs3.md` §10)

`progedit` (`GoFV/Asm/Obj7.lean`, `obj7.go:353-385`) rewrites `FMOVS`/`FMOVD $c, Fd` (`FCONST`),
when `c` is no `FMOV` immediate and not 0, into a load of the read-only constant symbol
`$f32.<bits>`/`$f64.<bits>` (`fconstSym?`). P0' is P0 with exactly that rewrite, the symbol
numbered as the assembler numbers it: `checkObj` then compares a load with a load, and the genssa
validator (slice G56) accepts the constant homed by that load.

- `p0Prime idx ps`: P0' of `ps`, the symbol of name `n` numbered `idx n` (the port's `flush`:
  its `symIdx` at `(n, ABI0)`).
- `internConsts syms ps`: `syms` with the constant symbols of `ps` added as `ctxt.LookupABI`
  (`lookup`) adds them: the first number of `(n, ABI0)`, else a new one at the end, in Prog
  order. `p0PrimeSyms` is P0' numbered by it, with that table (the validator's `G2In.syms`).
-/

namespace GoFV.Asm

open GoFV.SSA (GoStr)

/-- The load `progedit` makes of a float constant Prog: its `From` the constant symbol `k`
(`sym(SB)`, offset 0), as `progedit` writes it. -/
def fconstLoad (p : Prog) (k : Nat) : Prog :=
  { p with from_ := { p.from_ with type := .MEM, sym := some k, name := .EXTERN, offset := 0 } }

/-- P0': `ps` with `progedit`'s float constant rewrite, the symbol of name `n` numbered `idx n`. -/
def p0Prime (idx : String → Option Nat) (ps : Array Prog) : Except String (Array Prog) :=
  ps.mapM fun p =>
    match fconstSym? p with
    | none => pure p
    | some n =>
      match idx n with
      | some k => pure (fconstLoad p k)
      | none => throw s!"P0': Prog {p.id}: no symbol {n}"

/-- The constant symbols of `ps` added to `syms` as `lookup` adds them (`(n, ABI0)`). -/
def internConsts (syms : Array (GoStr × Nat)) (ps : Array Prog) : Array (GoStr × Nat) :=
  ps.foldl (init := syms) fun syms p =>
    match fconstSym? p with
    | some n =>
      let e := (GoStr.ofString n, Obj.ABI0.toNat)
      if syms.contains e then syms else syms.push e
    | none => syms

/-- The first number of `(n, ABI0)` in `syms`. -/
def symIndex? (syms : Array (GoStr × Nat)) (n : String) : Option Nat :=
  syms.findIdx? (· == (GoStr.ofString n, Obj.ABI0.toNat))

/-- P0' of `ps` numbered by `internConsts syms ps`, with that table. -/
def p0PrimeSyms (syms : Array (GoStr × Nat)) (ps : Array Prog) :
    Except String (Array (GoStr × Nat) × Array Prog) := do
  let syms' := internConsts syms ps
  return (syms', ← p0Prime (symIndex? syms') ps)

end GoFV.Asm
