import GoFV.Gen.Check7

/-!
# The genssa validator, slice G8: write barriers (`docs/plans/proofs3.md` §4)

`checkG8 lc ps bstart g` extends slice G7 (`GoFV/Gen/Check7.lean`) by the write-barrier buffer
requests (`ssa.go`'s `LoweredWB` case) and their components:

* `LoweredWB [n] mem`, `1 ≤ n ≤ 8`, of the shape `(pointer, mem)` homed in the pair `(R25, -)`
  (Go register 24 and no register for the memory): `CALL runtime.gcWriteBarrier<n>(SB)`
  (`TYPE_MEM`, `NAME_EXTERN`, ABIInternal), which `runMach` hands to the runtime hook `wbHook`
  (semantics3 §6: `R25` the buffer, `R27` and the flags garbage, every other register kept);
* `Select0` of such a request homed in `R25` at a 64-bit shape, and `Select1` of it, of the memory
  shape with no home: no code.

The buffer's entries are written by G3's stores and G4's `STP` through `R25`; `WBend` (G5) frees
it. A function with a write barrier calls, so its activation has a frame (`G8Env`).

`GoFV/Proof/Gen/G8.lean` proves what an accepted function satisfies (`g8_value`, `g8_term`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The register of the write-barrier buffer: `R25` (Go register 24). -/
def wbReg : Nat := 24

/-- The runtime symbol of `LoweredWB [n]` (`ir.Syms.GCWriteBarrier[n-1]`, ABIInternal). -/
def wbSym (n : Int) : GoStr × Nat := (GoStr.ofString s!"runtime.gcWriteBarrier{n}", 1)

/-- The shape of a write-barrier request: a pointer and the memory. -/
def wbTy : Ty → Bool
  | .tuple [.ptr _, .mem] => true
  | _ => false

/-- The `CALL` target of `LoweredWB [n]`: `runtime.gcWriteBarrier<n>(SB)`. -/
def wbTarget (g : G2In) (n : Int) (a : Addr) : Bool :=
  a.type == .MEM && a.name == .EXTERN && a.reg == 0 && a.index == 0 && a.offset == 0 &&
    match a.sym with
    | some y => g.syms[y]? == some (wbSym n)
    | none => false

/-- The Prog of `LoweredWB [n]`: `CALL runtime.gcWriteBarrier<n>(SB)`. -/
def wbPat (g : G2In) (n : Int) : Pat := ⟨plain .CALL (fun a : Addr => a == {}) (wbTarget g n), "CALL"⟩

/-- Argument `c` is a write-barrier request homed in `(R25, -)`. -/
def wbArg (lc : LocCtx) (c : ID) : Bool :=
  (lc.ctx.f.value? c).map (·.op) == some .ARM64LoweredWB &&
    lc.home c == some (.pair (some wbReg) none) && wbTy (lc.ty c)

/-- What `v` emits in G8, or why it is outside the slice. -/
def vkind8 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match v.op with
  | .ARM64LoweredWB => do
    if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
    let n := v.auxInt.toInt
    unless 1 ≤ n && n ≤ 8 && v.args.size == 1 &&
        lc.home v.id == some (.pair (some wbReg) none) && wbTy (lc.ty v.id) do
      throw s!"v{v.id}: write barrier shape"
    memArg lc v 0
    return .prog (wbPat g n)
  | .Select0 | .Select1 =>
    match v.args[0]? with
    | some c =>
      if !wbArg lc c then vkind7 lc g v else do
      if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
      unless v.args.size == 1 do throw s!"v{v.id}: select shape"
      if v.op == .Select0 then
        unless lc.home v.id == some (.reg wbReg) && cls (lc.ty v.id) == some 64 do
          throw s!"v{v.id}: write barrier buffer home"
      else
        unless memTy (lc.ty v.id) && lc.home v.id == none do
          throw s!"v{v.id}: write barrier memory"
      return .none
    | none => vkind7 lc g v
  | _ => vkind7 lc g v

/-- Slice G8 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG8 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind8 lc g, tm := cx.termG3 }
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
