import GoFV.Gen.Check43

/-!
# The genssa validator, slice G44: floating-point moves, loads and stores
(`docs/plans/proofs3.md` §4)

Phase 1 holds a float as its bit pattern (`.int .w32`/`.int .w64`, `fTy`), and `LocMatch` relates
a value in an `F` register to the low bits of its V register (`FValRel`). G44 accepts the values
that only move such bit patterns, homed in the `F` registers (`objV?`, obj register
`REG_F0 + k`, `fobjOf?`) at a float shape of class 32 or 64:

* `Copy` of a float register to a float register of its class: nothing when the registers
  agree, else `FMOVS`/`FMOVD Fs, Fd` (`genCopy`);
* `FMOVSload`/`FMOVDload` (`FMOVS`/`FMOVD off(Rn), Fd` or `sym+off(SB)`, as G3's loads,
  `accessA`) of the result's 4 or 8 bytes;
* `FMOVSstore`/`FMOVDstore` (`FMOVS`/`FMOVD Fs, off(Rn)` or `sym+off(SB)`) of a float of 4 or 8
  bytes;
* `FMOVSgpfp`/`FMOVDgpfp` (`FMOVS`/`FMOVD Rn, Fd`) of an integer register of at least the
  result's class, and `FMOVSfpgp`/`FMOVDfpgp` (`FMOVS`/`FMOVD Fn, Rd`) of a float to an integer
  register of its class;
* `FMOVSconst`/`FMOVDconst` (`FMOVS`/`FMOVD $c, Fd`, an `FCONST` operand holding the
  `float64` bits of the constant).

`checkG44 lc ps bstart g` is slice G43 (`GoFV/Gen/Check43.lean`) with these values (`fkind44`,
tried when G43 rejects a value of one of their ops, `fOp44`). `GoFV/Proof/Gen/G44.lean` proves
what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The obj register of Go register `r`'s V register (`F0`–`F31`): `REG_F0 + k`. -/
def fobjOf? (r : Nat) : Option Int := (objV? r).map fun k => ARM64.REG_F0 + k.toNat

/-- A float shape: the 32- or 64-bit bit pattern. -/
def fTy : Ty → Bool
  | .int .w32 | .int .w64 => true
  | _ => false

/-- The class of float argument `i` of `v` and the obj register of its V register. -/
def fargObj (lc : LocCtx) (v : Value) (i : Nat) : Except String (Nat × Int) := do
  let some a := v.args[i]? | throw s!"v{v.id}: no argument {i}"
  let some r := regHome? lc a | throw s!"v{v.id}: argument v{a} has no register"
  let some o := fobjOf? r | throw s!"v{v.id}: argument v{a} in register {r}"
  unless fTy (lc.ty a) do throw s!"v{v.id}: argument v{a} shape"
  let some c := cls (lc.ty a) | throw s!"v{v.id}: argument v{a} shape"
  return (c, o)

/-- The obj register of the V register a float `v` writes, and the class of `v`. -/
def fresObj (lc : LocCtx) (v : Value) : Except String (Nat × Int) := do
  let some r := regHome? lc v.id | throw s!"v{v.id}: no register"
  let some o := fobjOf? r | throw s!"v{v.id}: writes register {r}"
  unless fTy (lc.ty v.id) do throw s!"v{v.id}: result shape"
  let some c := cls (lc.ty v.id) | throw s!"v{v.id}: result shape"
  return (c, o)

/-- The `FMOV` of a float of class `c`: `FMOVS` for 32 bits, else `FMOVD`. -/
def fmovAs (c : Nat) : As := if c == 32 then .FMOVS else .FMOVD

/-- The bytes of a G44 load, store, register-file move or constant: 4 for the `S` ops. -/
def fBytes (op : Op) : Nat :=
  match op with
  | .ARM64FMOVSload | .ARM64FMOVSstore | .ARM64FMOVSgpfp | .ARM64FMOVSfpgp | .ARM64FMOVSconst => 4
  | _ => 8

/-- The ops of G44. -/
def fOp44 : Op → Bool
  | .Copy | .ARM64FMOVSload | .ARM64FMOVDload | .ARM64FMOVSstore | .ARM64FMOVDstore
  | .ARM64FMOVSgpfp | .ARM64FMOVDgpfp | .ARM64FMOVSfpgp | .ARM64FMOVDfpgp | .ARM64FMOVSconst
  | .ARM64FMOVDconst => true
  | _ => false

/-- The `FCONST` operand of a float constant `v`: the `float64` bits of `auxInt`. -/
def fconstA (v : Value) : Addr := { type := .FCONST, val := .float v.auxInt.toUInt64 }

/-- What a value of `fOp44` emits in G44 (module doc), or why it is outside the slice; `e` is
G43's reason, kept for a `Copy` whose argument is not in an `F` register. -/
def fkind44 (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let n := fBytes v.op
  match v.op with
  | .Copy =>
    unless ((v.args[0]?).bind (regHome? lc) |>.bind fobjOf?).isSome do throw e
    unless v.args.size == 1 do throw s!"v{v.id}: copy shape"
    let (ca, ra) ← fargObj lc v 0
    let (c, rd) ← fresObj lc v
    unless ca == c do throw s!"v{v.id}: copy across classes"
    if ra == rd then return .none
    return .prog (.ofShape { as := fmovAs c, from_ := regA ra, to := regA rd })
  | .ARM64FMOVSload | .ARM64FMOVDload =>
    unless v.args.size == 2 do throw s!"v{v.id}: load shape"
    let src ← accessA lc g v
    memArg lc v 1
    let (c, rd) ← fresObj lc v
    unless c == 8 * n do throw s!"v{v.id}: load widths"
    return .prog ⟨plain (fmovAs c) src (· == regA rd), (fmovAs c).name⟩
  | .ARM64FMOVSstore | .ARM64FMOVDstore =>
    unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: store shape"
    let dst ← accessA lc g v
    let (cs, rs) ← fargObj lc v 1
    memArg lc v 2
    unless cs == 8 * n do throw s!"v{v.id}: store widths"
    return .prog ⟨plain (fmovAs cs) (· == regA rs) dst, (fmovAs cs).name⟩
  | .ARM64FMOVSgpfp | .ARM64FMOVDgpfp =>
    unless v.args.size == 1 do throw s!"v{v.id}: shape"
    let (ca, rn) ← argObj lc v 0
    let (c, rd) ← fresObj lc v
    unless c == 8 * n && c ≤ ca do throw s!"v{v.id}: move widths"
    return .prog (.ofShape { as := fmovAs c, from_ := regA rn, to := regA rd })
  | .ARM64FMOVSfpgp | .ARM64FMOVDfpgp =>
    unless v.args.size == 1 do throw s!"v{v.id}: shape"
    let (ca, rn) ← fargObj lc v 0
    let (c, rd) ← resObj lc v
    unless ca == 8 * n && c == 8 * n do throw s!"v{v.id}: move widths"
    return .prog (.ofShape { as := fmovAs c, from_ := regA rn, to := regA rd })
  | .ARM64FMOVSconst | .ARM64FMOVDconst =>
    unless v.args.size == 0 do throw s!"v{v.id}: const shape"
    let (c, rd) ← fresObj lc v
    unless c == 8 * n do throw s!"v{v.id}: const widths"
    return .prog (.ofShape { as := fmovAs c, from_ := fconstA v, to := regA rd })
  | _ => throw e

/-- What `v` emits in G44, or why it is outside the slice: G43's kinds, then G44's float moves. -/
def vkind44 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind43 lc g v with
  | .ok kd => .ok kd
  | .error e => if fOp44 v.op then fkind44 lc g v e else .error e

/-- G43's check with G44's value check. -/
def checkG44L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind44 lc g, tm := cx.termG3 }
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

/-- Slice G44 of the genssa validator (module doc): `refsLive`, then G44's check on `liveCtx lc`. -/
def checkG44 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG44L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
