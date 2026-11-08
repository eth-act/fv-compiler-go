import GoFV.Gen.Check8

/-!
# The genssa validator, slice G9: call results (`docs/plans/proofs3.md` §4)

`checkG9 lc ps bstart g` extends slice G8 (`GoFV/Gen/Check8.lean`) by the static calls whose
result registers hold values of other classes elsewhere in the function. G2's call check
(`vkind2`) asks every result register to hold one class in the whole function (`resultReg`, from
`regCls`); since G3 the class table (`kStep`, `checkK`) follows each register through the
function, and a call sets each result register to its result's class, so G9 drops that
condition: a static call `CALLstatic` whose register arguments sit in their ABI registers, whose
results are in distinct ABI result registers `R0`–`R15` (`results` home, or no home and no result)
at register shapes then the memory (`callTy`), emits `CALL sym(SB)`.

`GoFV/Proof/Gen/G9.lean` proves what an accepted function satisfies (`g9_value`, `g9_term`,
`g9_nilPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The `CALL` of a static call of the symbol `(name, abi)`: `CALL name(SB)`. -/
def callPat (g : G2In) (name : GoStr) (abi : Nat) : Pat :=
  ⟨plain .CALL (fun a : Addr => a == {}) fun a =>
    a.type == .MEM && a.name == .EXTERN && a.reg == 0 && a.index == 0 && a.offset == 0 &&
      match a.sym with
      | some y => g.syms[y]? == some (name, abi)
      | none => false, "CALL"⟩

/-- Why a call's shape `ty` is no `callTy` for `n` result registers. -/
def callTyErr (n : Nat) (ty : Ty) : String :=
  let ts := tupleTys ty
  if ts.length != n + 1 then s!"call result count {ts.length} for {n} registers"
  else if (ts.getLast?.map memTy) != some true then "call results without memory"
  else match ts.dropLast.find? fun t => (cls t).isNone with
    | some t => s!"call result shape {repr t}"
    | none => "call result shapes"

/-- What `v` emits in G9, or why it is outside the slice. -/
def vkind9 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op != .ARM64CALLstatic then vkind8 lc g v else do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  let some (name, abi, cabi) := callOf? lc.ctx.tabs v.aux | throw s!"v{v.id}: call without ABI"
  let (ins, outs) ← callRegs cabi
  unless outs.Nodup do throw s!"v{v.id}: result registers repeat"
  let some m := v.args.back? | throw s!"v{v.id}: call without memory"
  unless memTy (lc.ty m) && lc.home m == none do throw s!"v{v.id}: call memory"
  unless (ins ++ outs).all (· < 16) do throw s!"v{v.id}: floating-point argument or result"
  let rargs := v.args.toList.dropLast
  unless rargs.length == ins.length do throw s!"v{v.id}: call arguments"
  unless (rargs.zip ins).all (fun (a, r) => regHome? lc a == some r) do
    throw s!"v{v.id}: an argument not in its ABI register"
  match lc.home v.id with
  | some (.results rs) =>
    unless rs.toList == outs.map some do throw s!"v{v.id}: result registers"
  | none => unless outs.isEmpty do throw s!"v{v.id}: result registers"
  | _ => throw s!"v{v.id}: call home"
  unless callTy outs.length (lc.ty v.id) do
    throw s!"v{v.id}: {callTyErr outs.length (lc.ty v.id)}"
  return .prog (callPat g name abi)

/-- Slice G9 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG9 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind9 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  if let some i := (List.range lc.homes.size).find? (!homeOK4 lc ·) then throw (homeErr lc i)
  checkFrame lc g
  checkVars lc g
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
  checkK lc kt
  let ids := ps.toList.map (·.id)
  unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
  return (tab, kt)

end GoFV.Gen.Check
