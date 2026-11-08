import GoFV.Gen.Check14

/-!
# The genssa validator, slice G15: zero-sized stack arguments (`docs/plans/proofs3.md` §4)

`checkG15 lc ps bstart g` extends slice G14 (`GoFV/Gen/Check14.lean`) by the static calls with
stack-assigned inputs of size 0 (`zeroStack`: Go's ABI assigns a zero-sized argument, such as a
receiver of an empty struct type, to the stack, at an offset that holds no byte). Such an input has
no register piece and no byte in the outgoing area, so genssa emits no store for it: G15 checks
the call as G9 does (`vkind9`) on its ABI without those inputs (`callRegsZ`).

`GoFV/Proof/Gen/G15.lean` proves what an accepted function satisfies (`g15_value`, `g15_term`,
`g15_nilPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- A stack-assigned input of size 0. -/
def zeroStack (tabs : Tables) (p : ABIParam) : Bool :=
  !p.out && p.regs.isEmpty && typeSize? tabs p.type == some 0

/-- `callRegs` of the ABI without its zero-sized stack inputs. -/
def callRegsZ (tabs : Tables) (abi : CallABI) : Except String (List Nat × List Nat) :=
  callRegs { abi with params := abi.params.filter (!zeroStack tabs ·) }

/-- A static call as G9 checks it (`vkind9`), on its ABI without its zero-sized stack inputs. -/
def callKind15 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  let some (name, abi, cabi) := callOf? lc.ctx.tabs v.aux | throw s!"v{v.id}: call without ABI"
  let (ins, outs) ← callRegsZ lc.ctx.tabs cabi
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

/-- What `v` emits in G15, or why it is outside the slice. -/
def vkind15 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .ARM64CALLstatic then callKind15 lc g v else vkind14 lc g v

/-- Slice G15 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG15 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind15 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
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
