import GoFV.Gen.Check23

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G24: `SP` anywhere (`docs/plans/proofs3.md` §4)

`checkG24 lc ps bstart g` extends slice G23 (`GoFV/Gen/Check23.lean`) by `SP` values after the
entry values: in a later block, or in the entry block after a value with code (the register
allocator rematerializes `SP` next to its users). Up to G23, `SP` is an entry value
(`entryOp3`), which `Cx2.values` admits only at the entry block's head.

`SP` holds no X register (`objX? 30 = none`: Go's `RSP` is no general register), so no code
writes it, and `LocMatch` does not relate the Go register `SP`: G24 runs it as a value without
code anywhere, as G3 runs `SB` (`vkind3`). Its users are the accesses of frame variables (G6),
whose `symAddr` ignores the base register.

G24 accepts an `SP` value with no temporary, no argument, a register shape, and no home or the
home `SP` (`spReg`).

`GoFV/Proof/Gen/G24.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The Go register `SP` (no machine register G1 relates). -/
def spReg : Nat := 30

/-- The activation values G24 leaves to the entry block's head: G3's but `SP`, which G24 runs as
a value without code. -/
def entryOp24 (op : Op) : Bool := entryOp3 op && op != .SP

/-- What `v` emits in G24, or why it is outside the slice. -/
def vkind24 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .SP then do
    -- `SP` holds no machine register: no code anywhere in the function
    unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
    unless v.args.size == 0 && (cls (lc.ty v.id)).isSome &&
        (lc.home v.id == none || lc.home v.id == some (.reg spReg)) do
      throw s!"v{v.id}: SP home"
    return .none
  else vkind23 lc g v

/-- Slice G24 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG24 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind24 lc g, tm := cx.termG3 }
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
