import GoFV.Gen.Check44

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G45: register-index float loads and stores
(`docs/plans/proofs3.md` §4)

G45 adds to G44 the float register-index loads `FMOV{S,D}loadidx ptr idx mem` and their scaled
forms `FMOVSloadidx4`, `FMOVDloadidx8` (`fLoadIdxOp?`), and the stores
`FMOV{S,D}storeidx ptr idx val mem`, `FMOVSstoreidx4`, `FMOVDstoreidx8` (`fStoreIdxOp?`). Phase 1
runs them as the integer ones (`Arm64.loadIdx`, `stIdx`): the `n` bytes at `ptr + idx · 2^sh`.
Genssa emits one `FMOVS`/`FMOVD` from or to the operand of `genIndexedOperand` (`idxA`, as G14 and
G18), with the float in an `F` register as G44's loads and stores (`fresObj`, `fargObj`):

* a load: three arguments, `ptr` and `idx` in X registers of class 64, the memory last, the result
  in an `F` register at a float shape of `8n` bits;
* a store: four arguments, the memory shape and no home, `ptr` and `idx` as a load's, `val` in an
  `F` register at a float shape of `8n` bits, the memory last.

`checkG45 lc ps bstart g` is slice G44 (`GoFV/Gen/Check44.lean`) with these values (`fkind45`,
tried when G44 rejects a value of one of their ops). `GoFV/Proof/Gen/G45.lean` proves what an
accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The float register-index loads: bytes and index shift. -/
def fLoadIdxOp? : Op → Option (Nat × Nat)
  | .ARM64FMOVSloadidx => some (4, 0)
  | .ARM64FMOVDloadidx => some (8, 0)
  | .ARM64FMOVSloadidx4 => some (4, 2)
  | .ARM64FMOVDloadidx8 => some (8, 3)
  | _ => none

/-- The float register-index stores: bytes and index shift. -/
def fStoreIdxOp? : Op → Option (Nat × Nat)
  | .ARM64FMOVSstoreidx => some (4, 0)
  | .ARM64FMOVDstoreidx => some (8, 0)
  | .ARM64FMOVSstoreidx4 => some (4, 2)
  | .ARM64FMOVDstoreidx8 => some (8, 3)
  | _ => none

/-- What a float register-index load or store emits in G45 (module doc), or why it is outside
the slice; `e` is G44's reason, kept for the other ops. -/
def fkind45 (lc : LocCtx) (v : Value) (e : String) : Except String VKind2 := do
  match fLoadIdxOp? v.op, fStoreIdxOp? v.op with
  | some (n, sh), _ =>
    unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
    unless v.args.size == 3 do throw s!"v{v.id}: indexed load shape"
    let (ca, rn) ← argObj lc v 0
    let (ci, ri) ← argObj lc v 1
    unless ca == 64 && ci == 64 do throw s!"v{v.id}: indexed load widths"
    memArg lc v 2
    let (c, rd) ← fresObj lc v
    unless c == 8 * n do throw s!"v{v.id}: load widths"
    return .prog ⟨plain (fmovAs c) (· == idxA rn ri sh) (· == regA rd), (fmovAs c).name⟩
  | none, some (n, sh) =>
    unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
    unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: indexed store shape"
    let (ca, rn) ← argObj lc v 0
    let (ci, ri) ← argObj lc v 1
    unless ca == 64 && ci == 64 do throw s!"v{v.id}: indexed store widths"
    let (cs, rs) ← fargObj lc v 2
    unless cs == 8 * n do throw s!"v{v.id}: store widths"
    memArg lc v 3
    return .prog ⟨plain (fmovAs cs) (· == regA rs) (· == idxA rn ri sh), (fmovAs cs).name⟩
  | none, none => throw e

/-- What `v` emits in G45, or why it is outside the slice: G44's kinds, then G45's float
register-index loads and stores. -/
def vkind45 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind44 lc g v with
  | .ok kd => .ok kd
  | .error e => fkind45 lc v e

/-- G44's check with G45's value check. -/
def checkG45L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind45 lc g, tm := cx.termG3 }
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

/-- Slice G45 of the genssa validator (module doc): `refsLive`, then G45's check on `liveCtx lc`. -/
def checkG45 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG45L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
