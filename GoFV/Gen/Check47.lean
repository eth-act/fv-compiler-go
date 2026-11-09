import GoFV.Gen.Check46

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G47: calls with float arguments or results
(`docs/plans/proofs3.md` §4, float stage (c))

Go's internal ABI passes and returns floats in `F0`–`F15` (Go registers 31–46, `abiReg`). The calls
of slices G9, G10 and G15 and the selects of their results ask every ABI register to be one of
`R0`–`R15` (the `< 16` check). G47 adds to G46 the same calls and selects with ABI registers in
`R0`–`R15` or `F0`–`F15` (`abiRegOK`):

* a static call as G15 checks it (`callKind15`: the ABI without its zero-sized stack inputs,
  `callRegsZ`), `callKind47`;
* an interface or closure call as G10 checks it (`icallErr`), `icallKind47`;
* `SelectN [i]` of such a call whose result is homed in an `F` register, the call's result register
  `i` (G2's and G10's selects of a result in `R0`–`R15` stay G46's), `selKind47`.

An argument passed in an `F` register, a result returned in one and a select homed in one have a
float shape (`fTy`: `.int .w32`/`.int .w64`, the bits): `LocMatch` relates a V register to a value
by its low bits (`FValRel`), and the callee contract (`CallSpec`, `RegRel`) already speaks of the V
registers.

`checkG47 lc ps bstart g` is slice G46 (`GoFV/Gen/Check46.lean`) with these values (`fcall47`,
tried when G46 rejects a value). `GoFV/Proof/Gen/G47.lean` proves what an accepted function
satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- A register G47's calls pass or return a value in: `R0`–`R15` (Go 0–15) or `F0`–`F15` (Go
31–46). -/
def abiRegOK (r : Nat) : Bool := r < 16 || (31 ≤ r && r < 47)

/-- The arguments `as` in the ABI registers `rs`: one in an `F` register has a float shape. -/
def fArgsOK (lc : LocCtx) (as : List ID) (rs : List Nat) : Bool :=
  (as.zip rs).all fun (a, r) => r < 31 || fTy (lc.ty a)

/-- The result shapes `ts` in the ABI registers `rs`: one in an `F` register is a float shape. -/
def fOutsOK (ts : List Ty) (rs : List Nat) : Bool :=
  (ts.zip rs).all fun (t, r) => r < 31 || fTy t

/-- A static call as G15 checks it (`callKind15`), with ABI registers in `R0`–`R15` or `F0`–`F15`
and float shapes in the `F` registers. -/
def callKind47 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  let some (name, abi, cabi) := callOf? lc.ctx.tabs v.aux | throw s!"v{v.id}: call without ABI"
  let (ins, outs) ← callRegsZ lc.ctx.tabs cabi
  unless outs.Nodup do throw s!"v{v.id}: result registers repeat"
  let some m := v.args.back? | throw s!"v{v.id}: call without memory"
  unless memTy (lc.ty m) && lc.home m == none do throw s!"v{v.id}: call memory"
  unless (ins ++ outs).all abiRegOK do throw s!"v{v.id}: ABI register above F15"
  let rargs := v.args.toList.dropLast
  unless rargs.length == ins.length do throw s!"v{v.id}: call arguments"
  unless (rargs.zip ins).all (fun (a, r) => regHome? lc a == some r) do
    throw s!"v{v.id}: an argument not in its ABI register"
  unless fArgsOK lc rargs ins do throw s!"v{v.id}: float register argument shape"
  match lc.home v.id with
  | some (.results rs) =>
    unless rs.toList == outs.map some do throw s!"v{v.id}: result registers"
  | none => unless outs.isEmpty do throw s!"v{v.id}: result registers"
  | _ => throw s!"v{v.id}: call home"
  unless callTy outs.length (lc.ty v.id) do
    throw s!"v{v.id}: {callTyErr outs.length (lc.ty v.id)}"
  unless fOutsOK (tupleTys (lc.ty v.id)) outs do throw s!"v{v.id}: float register result shape"
  return .prog (callPat g name abi)

/-- Why the registers of the interface or closure call `v` are outside G47 (`none`: they are
inside): `icallErr`'s result, memory, ABI register (`R0`–`R15` or `F0`–`F15`), code pointer and
closure context checks. -/
def icallRegErr47 (lc : LocCtx) (v : Value) (k : Nat) (ins outs : List Nat) (a0 rc : Nat) :
    Option String :=
  if !outs.Nodup then some s!"v{v.id}: result registers repeat"
  else if !(decide (k < v.args.size) && memLast lc v) then some s!"v{v.id}: call memory"
  else if !(ins ++ outs).all abiRegOK then some s!"v{v.id}: ABI register above F15"
  else if !(decide (rc < 26) && (cls (lc.ty a0)).isSome) then
    some s!"v{v.id}: code pointer register"
  else if !(k != 2 || ctxOK lc v) then some s!"v{v.id}: closure context not in R26"
  else none

/-- Why the arguments or results of the interface or closure call `v` are outside G47 (`none`:
they are inside): `icallErr`'s argument and result checks, and float shapes in the `F`
registers. -/
def icallArgErr47 (lc : LocCtx) (v : Value) (k : Nat) (ins outs : List Nat) : Option String :=
  let rargs := (v.args.toList.drop k).dropLast
  if !(rargs.length == ins.length) then some s!"v{v.id}: call arguments"
  else if !(rargs.zip ins).all (fun (a, r) => regHome? lc a == some r) then
    some s!"v{v.id}: an argument not in its ABI register"
  else if !fArgsOK lc rargs ins then some s!"v{v.id}: float register argument shape"
  else if !resHome lc v outs then some s!"v{v.id}: result registers"
  else if !callTy outs.length (lc.ty v.id) then
    some s!"v{v.id}: {callTyErr outs.length (lc.ty v.id)}"
  else if !fOutsOK (tupleTys (lc.ty v.id)) outs then
    some s!"v{v.id}: float register result shape"
  else none

/-- Why the interface or closure call `v` is outside G47 (`none`: it is inside): `icallErr` with
ABI registers in `R0`–`R15` or `F0`–`F15` and float shapes in the `F` registers. -/
def icallErr47 (lc : LocCtx) (v : Value) (k : Nat) (ins outs : List Nat) (a0 rc : Nat) :
    Option String :=
  (icallRegErr47 lc v k ins outs a0 rc).or (icallArgErr47 lc v k ins outs)

/-- The interface or closure call `v` with `k` leading arguments (`icallKind` with
`icallErr47`). -/
def icallKind47 (lc : LocCtx) (v : Value) (k : Nat) : Except String VKind2 :=
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
            match icallErr47 lc v k ins outs a0 rc with
            | some e => .error e
            | none => .ok (.prog (icallPat o))

/-- `SelectN [i]` of a call `c` (static, interface or closure), homed in an `F` register at a
float shape: the call's result register `i`, whose component has the select's class and a float
shape. -/
def selKind47 (lc : LocCtx) (v : Value) (c : ID) : Except String VKind2 := do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: select shape"
  let ty := lc.ty v.id
  let ts := tupleTys (lc.ty c)
  unless callTy (ts.length - 1) (lc.ty c) && 0 ≤ v.auxInt.toInt do
    throw s!"v{v.id}: select of a call shape"
  let i := v.auxInt.toInt.toNat
  let some r := regHome? lc v.id | throw s!"v{v.id}: select home"
  unless 31 ≤ r && r < 47 && i + 1 < ts.length && (ts[i]?.bind cls) == cls ty do
    throw s!"v{v.id}: select shape"
  unless fTy ty && (ts[i]?.map fTy) == some true do throw s!"v{v.id}: float select shape"
  match lc.home c with
  | some (.results rs) =>
    unless rs[i]? == some (some r) do throw s!"v{v.id}: select register"
    return .none
  | _ => throw s!"v{v.id}: select home"

/-- G47's values (module doc), or why `v` is outside the slice; `e` is G46's reason, kept for the
other values. -/
def fcall47 (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Except String VKind2 :=
  if v.op = .ARM64CALLstatic then callKind47 lc g v
  else match icallLead v.op with
    | some k => icallKind47 lc v k
    | none =>
      if v.op = .SelectN then
        match v.args[0]? with
        | some c =>
          match lc.ctx.f.value? c with
          | some u =>
            if u.op = .ARM64CALLstatic ∨ (icallLead u.op).isSome then selKind47 lc v c
            else .error e
          | none => .error e
        | none => .error e
      else .error e

/-- What `v` emits in G47, or why it is outside the slice: G46's kinds, then G47's calls and
selects. -/
def vkind47 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind46 lc g v with
  | .ok kd => .ok kd
  | .error e => fcall47 lc g v e

/-- G46's check with G47's value check. -/
def checkG47L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind47 lc g, tm := cx.termG3 }
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

/-- Slice G47 of the genssa validator (module doc): `refsLive`, then G47's check on `liveCtx lc`. -/
def checkG47 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG47L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
