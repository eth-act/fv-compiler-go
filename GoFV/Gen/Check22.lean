import GoFV.Gen.Check21

/-!
# The genssa validator, slice G22: pair loads and stores of globals (`docs/plans/proofs3.md` §4)

`checkG22 lc ps bstart g` extends slice G21 (`GoFV/Gen/Check21.lean`) by `LDP` and `STP` of a
global: the address argument is `SB` and the aux names the global (`symOf?`), as G3's narrow
accesses of globals. genssa emits `LDP sym+off(SB), (Ra, Rb)` (`ssaGenValue`, `OpARM64LDP`,
`ssagen.AddAux`) and `STP (Rx, Ry), sym+off(SB)`; the machine reads or writes the 8 bytes at the
global's address plus the offset and the 8 bytes above, which `runLoc`'s `pairAddr` names as the
global's block at the offset and at the offset plus 8.

G22 accepts `LDP` of a global with G4's result conditions (two components of integer classes of at
least 8 bits, a pair home of two distinct registers G1 may write), and `STP` of a global of two
64-bit registers, as G4's `STP`.

`GoFV/Proof/Gen/G22.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `v` is an `LDP` or `STP` with an aux whose address argument is `SB`: an access of a global. -/
def globPair (lc : LocCtx) (v : Value) : Bool :=
  (v.op == .ARM64LDP || v.op == .ARM64STP) && v.aux.isSome &&
    (v.args[0]?.bind lc.ctx.f.value?).map (·.op) == some .SB

/-- `LDP sym+off(SB), (Ra, Rb)` and `STP (Rx, Ry), sym+off(SB)` (`globPair`): no temporary, the
aux a global's symbol, G4's operand conditions. -/
def globPairKind (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let some x := v.aux | throw s!"v{v.id}: pair access shape"
  let some (name, abi) := symOf? lc.ctx.tabs x | throw s!"v{v.id}: access of a non-global"
  let src := globA g name abi v.auxInt.toInt
  if v.op == .ARM64LDP then
    unless v.args.size == 2 && pairTys (lc.ty v.id) do throw s!"v{v.id}: pair load shape"
    memArg lc v 1
    let some (ra, rb) := pairHome? lc v.id | throw s!"v{v.id}: pair load home"
    unless ra != rb && ra != zeroReg && rb != zeroReg && destOK ra && destOK rb do
      throw s!"v{v.id}: pair load registers"
    let some oa := objOf? ra | throw s!"v{v.id}: register {ra}"
    let some ob := objOf? rb | throw s!"v{v.id}: register {rb}"
    return .prog ⟨plain .LDP src (· == pairA oa ob), "LDP sym(SB)"⟩
  else
    unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: pair store shape"
    let (cx, rx) ← argObj lc v 1
    let (cy, ry) ← argObj lc v 2
    memArg lc v 3
    unless cx == 64 && cy == 64 do throw s!"v{v.id}: pair store widths"
    return .prog ⟨plain .STP (· == pairA rx ry) src, "STP sym(SB)"⟩

/-- What `v` emits in G22, or why it is outside the slice. -/
def vkind22 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if globPair lc v then globPairKind lc g v else vkind21 lc g v

/-- Slice G22 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG22 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind22 lc g, tm := cx.termG3 }
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
