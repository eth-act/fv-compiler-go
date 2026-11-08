import GoFV.Gen.Check9

/-!
# The genssa validator, slice G10: interface and closure calls (`docs/plans/proofs3.md` §4)

`checkG10 lc ps bstart g` extends slice G9 (`GoFV/Gen/Check9.lean`) by the indirect calls
(`ssa.go`'s `CALLclosure`/`CALLinter` case, `State.Call` without an `AuxCall` symbol):

* `CALLinter code args… mem` and `CALLclosure code ctx args… mem` whose code pointer is in a
  register `Rn` (`R0`–`R26`, Go 0–25) at a register shape, whose closure context (`CALLclosure`) is
  in `R26` (Go 25, the context register of Go's internal ABI), whose register arguments sit in
  their ABI registers and whose results are in distinct ABI result registers `R0`–`R15` (`results`
  home, or no home and no result) at register shapes then the memory (`callTy`): `CALL (Rn)`
  (`TYPE_MEM`, `NAME_NONE`, register `Rn`), which `runProg` runs as a call to the address in `Rn`;
* `SelectN [i]` of such a call: G2's selects of a static call's results and memory.

Their `results` homes are accepted (`homeOK10`). `GoFV/Proof/Gen/G10.lean` proves what an accepted
function satisfies (`g10_value`, `g10_term`, `g10_nilPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The leading arguments of an interface or closure call that are no register pieces: the code
pointer (`CALLinter`), the code pointer and the closure context (`CALLclosure`). -/
def icallLead : Op → Option Nat
  | .ARM64CALLinter => some 1
  | .ARM64CALLclosure => some 2
  | _ => none

/-- The closure context register of Go's internal ABI: `R26` (Go register 25). -/
def ctxReg : Nat := 25

/-- The `CALL` of an indirect call through the obj register `o`: `CALL (Rn)`. -/
def icallPat (o : Int) : Pat :=
  ⟨plain .CALL (fun a : Addr => a == {}) fun a => a.type == .MEM && a.name == .NONE && a.reg == o,
    "CALL (R)"⟩

/-- The selects of a call `u` (`c`) G2 accepts of a static call (`vkind2`'s `SelectN`). -/
def selKind (lc : LocCtx) (v : Value) (c : ID) : Except String VKind2 := do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: select shape"
  let ty := lc.ty v.id
  let ts := tupleTys (lc.ty c)
  unless callTy (ts.length - 1) (lc.ty c) && 0 ≤ v.auxInt.toInt do
    throw s!"v{v.id}: select of a call shape"
  let i := v.auxInt.toInt.toNat
  if memTy ty then
    unless lc.home v.id == none && i + 1 == ts.length do throw s!"v{v.id}: memory select"
    return .none
  let some r := regHome? lc v.id | throw s!"v{v.id}: select home"
  unless r < 16 && i + 1 < ts.length && (ts[i]?.bind cls) == cls ty do
    throw s!"v{v.id}: select shape"
  match lc.home c with
  | some (.results rs) =>
    unless rs[i]? == some (some r) do throw s!"v{v.id}: select register"
    return .none
  | _ => throw s!"v{v.id}: select home"

/-- The closure context of `v` (its argument 1) is in `R26` at a register shape. -/
def ctxOK (lc : LocCtx) (v : Value) : Bool :=
  match v.args[1]? with
  | some a1 => regHome? lc a1 == some ctxReg && (cls (lc.ty a1)).isSome
  | none => false

/-- The memory, the last argument of `v`, has no home. -/
def memLast (lc : LocCtx) (v : Value) : Bool :=
  match v.args.back? with
  | some m => memTy (lc.ty m) && lc.home m == none
  | none => false

/-- The results of `v` are homed in the registers `outs` (`results` home, or no home and no
result). -/
def resHome (lc : LocCtx) (v : Value) (outs : List Nat) : Bool :=
  match lc.home v.id with
  | some (.results rs) => rs.toList == outs.map some
  | none => outs.isEmpty
  | _ => false

/-- Why the interface or closure call `v` with `k` leading arguments, ABI registers `ins`/`outs`
and code pointer `a0` in register `rc` is outside the slice (`none`: it is inside). -/
def icallErr (lc : LocCtx) (v : Value) (k : Nat) (ins outs : List Nat) (a0 rc : Nat) :
    Option String :=
  let rargs := (v.args.toList.drop k).dropLast
  if !outs.Nodup then some s!"v{v.id}: result registers repeat"
  else if !(decide (k < v.args.size) && memLast lc v) then some s!"v{v.id}: call memory"
  else if !(ins ++ outs).all (· < 16) then some s!"v{v.id}: floating-point argument or result"
  else if !(decide (rc < 26) && (cls (lc.ty a0)).isSome) then
    some s!"v{v.id}: code pointer register"
  else if !(k != 2 || ctxOK lc v) then some s!"v{v.id}: closure context not in R26"
  else if !(rargs.length == ins.length) then some s!"v{v.id}: call arguments"
  else if !(rargs.zip ins).all (fun (a, r) => regHome? lc a == some r) then
    some s!"v{v.id}: an argument not in its ABI register"
  else if !resHome lc v outs then some s!"v{v.id}: result registers"
  else if !callTy outs.length (lc.ty v.id) then
    some s!"v{v.id}: {callTyErr outs.length (lc.ty v.id)}"
  else none

/-- The interface or closure call `v` with `k` leading arguments (`icallLead`). -/
def icallKind (lc : LocCtx) (v : Value) (k : Nat) : Except String VKind2 :=
  if (lc.temps[v.id]?).join != none then .error s!"v{v.id}: temporary register" else
  match callABI? lc.ctx.tabs v.aux with
  | none => .error s!"v{v.id}: call without ABI"
  | some cabi =>
    match callRegs cabi with
    | .error e => .error e
    | .ok (ins, outs) =>
      match v.args[0]? with
      | none => .error s!"v{v.id}: call without code pointer"
      | some a0 =>
        match regHome? lc a0 with
        | none => .error s!"v{v.id}: code pointer not in a register"
        | some rc =>
          match objOf? rc with
          | none => .error s!"v{v.id}: code pointer register"
          | some o =>
            match icallErr lc v k ins outs a0 rc with
            | some e => .error e
            | none => .ok (.prog (icallPat o))

/-- What `v` emits in G10, or why it is outside the slice. -/
def vkind10 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match icallLead v.op with
  | some k => icallKind lc v k
  | none =>
    if v.op == .SelectN then
      match v.args[0]? with
      | some c =>
        match lc.ctx.f.value? c with
        | some u => if (icallLead u.op).isSome then selKind lc v c else vkind9 lc g v
        | none => vkind9 lc g v
      | none => vkind9 lc g v
    else vkind9 lc g v

/-- The home of value `i` is one G10 handles: G4's, or the `results` home of an interface or
closure call. -/
def homeOK10 (lc : LocCtx) (i : Nat) : Bool :=
  homeOK4 lc i ||
    match lc.home i with
    | some (.results _) => ((lc.ctx.f.value? i).bind (icallLead ·.op)).isSome
    | _ => false

/-- Slice G10 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG10 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind10 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
  checkFrame lc g
  checkVars lc g
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
  checkK lc kt
  let ids := ps.toList.map (·.id)
  unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
  return (tab, kt)

end GoFV.Gen.Check
