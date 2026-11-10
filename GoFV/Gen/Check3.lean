import GoFV.Gen.Check2

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G3: widths (`docs/plans/proofs3.md` §4)

`checkG3 lc ps bstart g` extends slice G2 (`GoFV/Gen/Check2.lean`) by register width classes that
change along the function, narrow memory accesses and accesses of globals, 32-bit compares and
tests, extensions and narrow ALU ops. It returns G2's PC table and the **class table**: for each
block, the width class (`cls`) of the content of each register at the block's start.

**Classes by dataflow.** G1 and G2 let each register hold values of one class. G3 instead tracks
the class of each register's last writer (`kStep`: a value homed in register `r` sets `r` to its
class, a static call each result register to its result's class; a `Phi` writes nothing; values
homed elsewhere leave the map), forward through the blocks from the entry block (where nothing is
known), joining at joins (`kFlow`). `checkK` then checks the table it returns: every register a
value reads holds the class it is read at (`kReads`: the register arguments, the call result a
`SelectN` reads; the control of a register test), and the class map at each successor's start is
implied by the one at the end of each predecessor (`kLe`). A register clobbered by a call holds
`poison`, which fits every class, so a call keeps the map elsewhere.

**Narrower classes** (slice G59, group K). A class in the table is a class the register's content
can be read at (`kNarrow`): an integer class of at least 8 bits no wider than the content's
integer or pointer class (the low bits of the register), or any integer class over a boolean (0 or
1 in the whole register). The edges check this (`kLe`), so the dataflow may join an integer class
with a narrower one or with a boolean (`kJoin`), and set the home register of a successor's `Phi`
to the `Phi`'s class when the content allows it (`kPhis`): a 32-bit `Phi` of 64-bit arguments, a
64-bit `Phi` of booleans.

**Values** beyond G2's (`vkind3`):

* the loads `MOV{D,B,BU,H,HU,W,WU}load` and stores `MOV{D,B,H,W}store`, of an address in a 64-bit
  register (`MOVB… off(Rn)`, no symbol; G1 has `MOVD`'s) or of a global (`MOVB… sym+off(SB)`,
  argument `SB`, a symbol aux): a load's result of an integer class of at least 8 bits, or a
  boolean (`MOVBU`); a stored value at least as wide as the access, or a boolean byte;
* `MOV{B,BU,H,HU,W,WU}reg` emitted as the extension (`MOVB… Rn, Rd`): an argument at least as
  wide as the extended bits, or a boolean;
* `ANDconst` (`AND $k, Rn, Rd`) and `SLLconst` (`LSL $k, Rn, Rd`): a result no wider than the
  argument; `SRLconst` (`LSR $k, Rn, Rd`) of a 64-bit argument; `UBFX` (`UBFX $lsb, Rn, $w, Rd`)
  of an argument holding the extracted bits;
* `CMPW` (`CMPW Rm, Rn`) and `CMPWconst` (`CMPW $k, Rn`) of arguments of at least 32 bits;
* `SB` of a register shape anywhere (no code; it holds no machine register), not only at the entry
  block's head.

**Blocks** beyond G2's: `ZW`/`NZW` (`CBZW`/`CBNZW` of a register of at least 32 bits or a
boolean) and `TBZ`/`TBNZ` (`TBZ $k, Rn` of a register holding bit `k`, or a boolean), emitted as
`ssaGenBlock` does.

`GoFV/Proof/Gen/G3.lean` proves what an accepted function satisfies (`g3_value`, `g3_term`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-! ## Register classes by dataflow -/

/-- The width class of the content of each register (by Go register number; `none`: unknown). -/
abbrev KMap := Array (Option Nat)

/-- The class map's entry for register `r`. -/
def KMap.get (K : KMap) (r : Nat) : Option Nat := (K[r]?).join

/-- Nothing known: the class map at the function's entry. -/
def KMap.bot : KMap := Array.replicate ARM64.registers.size none

/-- The class map after the results `rs` of shapes `ts` are written. -/
def kResults (K : KMap) : List (Ty × Option Nat) → KMap
  | [] => K
  | (t, some r) :: rest => kResults (K.setIfInBounds r (cls t)) rest
  | (_, none) :: rest => kResults K rest

/-- The class map after `v`: the class of its register home, or of each result register of a
call or register of a pair; a `Phi` writes nothing. -/
def kStep (lc : LocCtx) (K : KMap) (v : Value) : KMap :=
  if v.op == .Phi then K else
  match lc.home v.id with
  | some (.reg r) => if r == zeroReg then K else K.setIfInBounds r (cls (lc.ty v.id))
  | some (.results rs) => kResults K ((tupleTys (lc.ty v.id)).zip rs.toList)
  | some (.pair a b) => kResults K ((tupleTys (lc.ty v.id)).zip [a, b])
  | _ => K

/-- The class map after the values `ids`. -/
def kSteps (lc : LocCtx) (K : KMap) (ids : List ID) : KMap :=
  ids.foldl (fun K id => match lc.ctx.f.value? id with
    | some v => kStep lc K v
    | none => K) K

/-- The register read by argument `a` at its class (not `ZERO`). -/
def kArg (lc : LocCtx) (a : ID) : Option (Nat × Nat) :=
  match lc.home a, cls (lc.ty a) with
  | some (.reg r), some c => if r == zeroReg then none else some (r, c)
  | _, _ => none

/-- The registers `v` reads and the class it reads each at: its register arguments (a `Phi`
reads none: its arguments share its home), and the result register a `SelectN` reads, or the
register of a pair a `Select0`/`Select1` reads. -/
def kReads (lc : LocCtx) (v : Value) : List (Nat × Nat) :=
  if v.op == .Phi then [] else
  let sel : List (Nat × Nat) := if v.op == .SelectN then
      match v.args[0]? with
      | some c => match lc.home c with
        | some (.results rs) =>
          let i := v.auxInt.toInt.toNat
          match (rs[i]?).join, ((tupleTys (lc.ty c))[i]?).bind cls with
          | some r, some k => [(r, k)]
          | _, _ => []
        | _ => []
      | none => []
    else if v.op == .Select0 || v.op == .Select1 then
      match v.args[0]? with
      | some c => match lc.home c with
        | some (.pair a b) =>
          let i := if v.op == .Select0 then 0 else 1
          match ([a, b][i]?).join, ((tupleTys (lc.ty c))[i]?).bind cls with
          | some r, some k => [(r, k)]
          | _, _ => []
        | _ => []
      | none => []
    else []
  v.args.toList.filterMap (kArg lc) ++ sel

/-- The register the control of block `b` is read from, at its class (a register test's; a flags
control or a `MakeResult` has no register home). -/
def kControl (lc : LocCtx) (b : Block) : List (Nat × Nat) :=
  match b.controls[0]? with
  | some c => (kArg lc c).toList
  | none => []

/-- Every read `(r, c)` finds class `c` in `r`. -/
def kOK (K : KMap) (rs : List (Nat × Nat)) : Bool := rs.all fun (r, c) => K.get r == some c

/-- `K` implies `K'`: every class `K'` knows can be read from the class `K` knows (`kNarrow`). -/
def kLe (K' K : KMap) : Bool :=
  (List.range K'.size).all fun r => (K'.get r).all fun c => (K.get r).any (kNarrow c)

/-- The class two predecessors both allow (`kNarrow`): the narrower of two integer classes, the
integer class over a boolean; `none` where neither reads the other. -/
def kJoin : Option Nat → Option Nat → Option Nat
  | some x, some y => if kNarrow x y then some x else if kNarrow y x then some y else none
  | _, _ => none

/-- Where the classes of `a` and `b` join (`kJoin`). -/
def kMeet (a b : KMap) : KMap :=
  Array.ofFn (n := a.size) fun i => kJoin (a.get i) (b.get i)

/-- The class map entering block `b`: the home register of each `Phi` of `b` read at the `Phi`'s
class where its content allows it (`kNarrow`), so that the `Phi`'s readers find its class. -/
def kPhis (lc : LocCtx) (b : Block) (K : KMap) : KMap :=
  b.values.foldl (fun K id => match lc.ctx.f.value? id with
    | some v =>
      if v.op == .Phi then
        match lc.home id, cls (lc.ty id) with
        | some (.reg r), some c =>
          if r != zeroReg && (K.get r).any (fun c' => c != c' && kNarrow c c') then
            K.setIfInBounds r (some c)
          else K
        | _, _ => K
      else K
    | none => K) K

/-- One pass of the forward dataflow over the blocks `bids` (layout order): the class map at the
start of each reached block, the join of the end of each reached predecessor (entering the block,
`kPhis`). -/
def kPass (lc : LocCtx) (kin : Std.HashMap ID KMap) (bids : List ID) : Std.HashMap ID KMap :=
  bids.foldl (fun kin bid =>
    match kin[bid]?, lc.ctx.f.block? bid with
    | some K, some b =>
      let out := kSteps lc K b.values.toList
      b.succs.foldl (fun kin e =>
        let o := match lc.ctx.f.block? e.b with
          | some sb => kPhis lc sb out
          | none => out
        match kin[e.b]? with
        | some K' => kin.insert e.b (kMeet K' o)
        | none => kin.insert e.b o) kin
    | _, _ => kin) kin

/-- The class table: the dataflow from the entry block (nothing known) to a fixed point (at most
`fuel` passes; `checkK` checks whatever it returns). -/
def kFlow (lc : LocCtx) (fuel : Nat) : Std.HashMap ID KMap :=
  let bids := lc.ctx.f.blocks.toList
  let rec go : Nat → Std.HashMap ID KMap → Std.HashMap ID KMap
    | 0, kin => kin
    | n + 1, kin =>
      let kin' := kPass lc kin bids
      if bids.all (fun b => kin'[b]? == kin[b]?) then kin' else go n kin'
  go fuel (({} : Std.HashMap ID KMap).insert lc.ctx.f.entry KMap.bot)

/-- The class map at the start of each block (by block ID). -/
abbrev KTab := List (ID × KMap)

/-- The class map at the start of block `b` (nothing known if the table has none). -/
def KTab.at (kt : KTab) (b : ID) : KMap := (kt.lookup b).getD KMap.bot

/-- The class map before value `i` of block `blk` (ID `b`). -/
def kAt (lc : LocCtx) (kt : KTab) (b : ID) (blk : Block) (i : Nat) : KMap :=
  kSteps lc (kt.at b) (blk.values.toList.take i)

/-- The reads of the values `ids` from the class map `K`, each before its own value. -/
def kValues (lc : LocCtx) : KMap → List ID → Except String KMap
  | K, [] => pure K
  | K, id :: ids => do
    let some v := lc.ctx.f.value? id | throw s!"v{id} is not in the function"
    unless kOK K (kReads lc v) do throw s!"v{id}: a register read at another class"
    kValues lc (kStep lc K v) ids

/-- Checks the class table `kt`: the entry block starts with nothing known, every read finds its
class, and every successor's start is implied by the end of its predecessor. -/
def checkK (lc : LocCtx) (kt : KTab) : Except String Unit := do
  unless kt.at lc.ctx.f.entry == KMap.bot do throw "entry classes"
  for bid in lc.ctx.f.blocks.toList do
    let some b := lc.ctx.f.block? bid | throw s!"b{bid} is not in the function"
    let K ← kValues lc (kt.at bid) b.values.toList
    unless kOK K (kControl lc b) do throw s!"b{bid}: control read at another class"
    for e in b.succs do
      unless kLe (kt.at e.b) K do throw s!"b{bid}: classes at b{e.b}"

/-! ## Values -/

/-- The narrow loads: opcode, bytes, sign extension. -/
def narrowLoad? : Op → Option (As × Nat × Bool)
  | .ARM64MOVBload => some (.MOVB, 1, true)
  | .ARM64MOVBUload => some (.MOVBU, 1, false)
  | .ARM64MOVHload => some (.MOVH, 2, true)
  | .ARM64MOVHUload => some (.MOVHU, 2, false)
  | .ARM64MOVWload => some (.MOVW, 4, true)
  | .ARM64MOVWUload => some (.MOVWU, 4, false)
  | _ => none

/-- The narrow stores: opcode, bytes. -/
def narrowStore? : Op → Option (As × Nat)
  | .ARM64MOVBstore => some (.MOVB, 1)
  | .ARM64MOVHstore => some (.MOVH, 2)
  | .ARM64MOVWstore => some (.MOVW, 4)
  | _ => none

/-- The extensions: opcode, extended bits, sign extension. -/
def extOp? : Op → Option (As × Nat × Bool)
  | .ARM64MOVBreg => some (.MOVB, 8, true)
  | .ARM64MOVBUreg => some (.MOVBU, 8, false)
  | .ARM64MOVHreg => some (.MOVH, 16, true)
  | .ARM64MOVHUreg => some (.MOVHU, 16, false)
  | .ARM64MOVWreg => some (.MOVW, 32, true)
  | .ARM64MOVWUreg => some (.MOVWU, 32, false)
  | _ => none

/-- A `UBFX` operand pair: `$lsb` in `from_`, `$width` the one `RestArgs` source. -/
def ubfxOK (lsb width : Int) (rn rd : Int) (p : Prog) : Bool :=
  p.as == .UBFX && p.from_ == constA lsb && p.reg == rn && p.to == regA rd && p.scond == 0 &&
    p.regTo2 == 0 && match p.rest with
    | #[(_, a)] => a == constA width
    | _ => false

/-- The loads: opcode, bytes, sign extension. -/
def loadOp? (op : Op) : Option (As × Nat × Bool) :=
  if op == .ARM64MOVDload then some (.MOVD, 8, false) else narrowLoad? op

/-- The stores: opcode, bytes. -/
def storeOp? (op : Op) : Option (As × Nat) :=
  if op == .ARM64MOVDstore then some (.MOVD, 8) else narrowStore? op

/-- A memory operand naming global `(name, abi)` at offset `off` (`sym+off(SB)`). -/
def globA (g : G2In) (name : GoStr) (abi : Nat) (off : Int) (a : Addr) : Bool :=
  a.type == .MEM && a.name == .EXTERN && a.reg == 0 && a.index == 0 && a.offset == off &&
    match a.sym with
    | some y => g.syms[y]? == some (name, abi)
    | none => false

/-- The memory operand of an access `v` (address argument 0): a 64-bit register and the offset
(`off(Rn)`, no symbol), or a global's symbol (`sym+off(SB)`, argument `SB`). -/
def accessA (lc : LocCtx) (g : G2In) (v : Value) : Except String (Addr → Bool) := do
  match v.aux with
  | none =>
    let (ca, rn) ← argObj lc v 0
    unless ca == 64 do throw s!"v{v.id}: address width"
    return (· == memA rn v.auxInt.toInt)
  | some x =>
    let some a := v.args[0]? | throw s!"v{v.id}: access shape"
    unless (lc.ctx.f.value? a).map (·.op) == some .SB do throw s!"v{v.id}: access of a frame variable"
    let some (name, abi) := symOf? lc.ctx.tabs x | throw s!"v{v.id}: access of a non-global"
    return globA g name abi v.auxInt.toInt

/-- The Go register `SB` (no machine register). -/
def sbReg : Nat := 63

/-- The activation values G3 leaves to the entry block's head: G1's but `SB`, which G3 runs as a
value without code. -/
def entryOp3 (op : Op) : Bool := entryOp op && op != .SB

/-- What `v` emits in G3, or why it is outside the slice. -/
def vkind3 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  if let some (as, n, sg) := loadOp? v.op then
    if as == .MOVD && v.aux == none then return ← vkind2 lc g v
    unless v.args.size == 2 do throw s!"v{v.id}: load shape"
    let src ← accessA lc g v
    memArg lc v 1
    let (c, rd) ← resObj lc v
    unless 8 ≤ c || (c == 1 && n == 1 && !sg) do throw s!"v{v.id}: load widths"
    return .prog ⟨plain as src (· == regA rd), as.name⟩
  if let some (as, n) := storeOp? v.op then
    if as == .MOVD && v.aux == none then return ← vkind2 lc g v
    unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: store shape"
    let dst ← accessA lc g v
    let (cs, rs) ← argObj lc v 1
    memArg lc v 2
    unless 8 * n ≤ cs || (cs == 1 && n == 1) do throw s!"v{v.id}: store widths"
    return .prog ⟨plain as (· == regA rs) dst, as.name⟩
  if v.op == .SB then
    -- `SB` holds no machine register: no code anywhere in the function
    unless v.args.size == 0 && (cls (lc.ty v.id)).isSome &&
        (lc.home v.id == none || lc.home v.id == some (.reg sbReg)) do
      throw s!"v{v.id}: SB home"
    return .none
  if let some (as, w, _) := extOp? v.op then
    unless v.args.size == 1 do throw s!"v{v.id}: extension shape"
    let (ca, rn) ← argObj lc v 0
    let (c, rd) ← resObj lc v
    unless (w ≤ ca || ca == 1) && 8 ≤ c do throw s!"v{v.id}: extension widths"
    return .prog (.ofShape { as, from_ := regA rn, to := regA rd })
  match v.op with
  | .ARM64ANDconst | .ARM64SLLconst | .ARM64SRLconst =>
    unless v.args.size == 1 do throw s!"v{v.id}: shape"
    let (ca, rn) ← argObj lc v 0
    let (c, rd) ← resObj lc v
    unless 8 ≤ c && c ≤ ca && (v.op != .ARM64SRLconst || ca == 64) &&
        (v.op == .ARM64ANDconst || (0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64)) do
      throw s!"v{v.id}: shift or mask widths"
    let as := match v.op with
      | .ARM64ANDconst => As.AND
      | .ARM64SLLconst => As.LSL
      | _ => As.LSR
    return .prog (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd })
  | .ARM64UBFX =>
    unless v.args.size == 1 && 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 2 ^ 16 do
      throw s!"v{v.id}: bitfield shape"
    let (ca, rn) ← argObj lc v 0
    let (c, rd) ← resObj lc v
    let lsb := v.auxInt.toInt / 256
    let width := v.auxInt.toInt % 256
    unless 8 ≤ c && 0 < width && lsb + width ≤ ca do throw s!"v{v.id}: bitfield widths"
    return .prog ⟨ubfxOK lsb width rn rd, "UBFX"⟩
  | .ARM64CALLstatic =>
    -- G2's call, with distinct result registers (the class table sets each to its result's class)
    let some (_, _, cabi) := callOf? lc.ctx.tabs v.aux | throw s!"v{v.id}: call without ABI"
    let (_, outs) ← callRegs cabi
    unless outs.Nodup do throw s!"v{v.id}: result registers repeat"
    vkind2 lc g v
  | .ARM64CMPW =>
    unless v.args.size == 2 && (lc.ty v.id).isFlags && lc.home v.id == none do
      throw s!"v{v.id}: compare shape"
    let (ca, rn) ← argObj lc v 0
    let (cb, rm) ← argObj lc v 1
    unless 32 ≤ ca && 32 ≤ cb do throw s!"v{v.id}: compare widths"
    return .prog (.ofShape { as := .CMPW, from_ := regA rm, reg := rn })
  | .ARM64CMPWconst =>
    unless v.args.size == 1 && (lc.ty v.id).isFlags && lc.home v.id == none do
      throw s!"v{v.id}: compare shape"
    let (ca, rn) ← argObj lc v 0
    unless 32 ≤ ca do throw s!"v{v.id}: compare widths"
    return .prog (.ofShape { as := .CMPW, from_ := constA v.auxInt.toInt, reg := rn })
  | _ => vkind2 lc g v

/-- The home of value `i` is one G3 handles: G2's homes, but a register may hold values of any
classes (the class table follows them). -/
def homeOK3 (lc : LocCtx) (i : Nat) : Bool :=
  match lc.home i with
  | some (.reg r) => r == zeroReg || (cls (lc.ty i)).isSome
  | _ => homeOK2 lc i

/-! ## Blocks -/

/-- The 32-bit register tests and the bit tests: the branch and its inverse. -/
def testBr : BlockKind → Option (As × As)
  | .ARM64ZW => some (.CBZW, .CBNZW)
  | .ARM64NZW => some (.CBNZW, .CBZW)
  | .ARM64TBZ => some (.TBZ, .TBNZ)
  | .ARM64TBNZ => some (.TBNZ, .TBZ)
  | _ => none

/-- The terminator: G2's kinds, and `ZW`/`NZW` (`CBZW`/`CBNZW Rn`) on a register of at least 32
bits or a boolean, `TBZ`/`TBNZ` (`TBZ $k, Rn`) on a register holding bit `k` or a boolean. -/
def Cx.termG3 (cx : Cx) (b : Block) (j : Nat) (next : Option (ID × Nat)) : Except String Unit := do
  match testBr b.kind with
  | none => cx.termG2 b j next
  | some (asm, inv) =>
    unless b.succs.all (cx.lc.ctx.f.blocks.contains ·.b) do throw s!"b{b.id}: successor not laid out"
    let some e0 := b.succs[0]? | throw s!"b{b.id}: no successor 0"
    let some e1 := b.succs[1]? | throw s!"b{b.id}: no successor 1"
    unless b.succs.size == 2 && b.controls.size == 1 do throw s!"b{b.id}: branch shape"
    let some c := b.controls[0]? | throw s!"b{b.id}: no control"
    let some r := regHome? cx.lc c | throw s!"b{b.id}: control has no register"
    let some o := objOf? r | throw s!"b{b.id}: control register {r}"
    let some k := cls (cx.lc.ty c) | throw s!"b{b.id}: control shape"
    let sh : Shape ← if b.kind == .ARM64ZW || b.kind == .ARM64NZW then do
        unless 32 ≤ k || k == 1 do throw s!"b{b.id}: control width"
        pure { as := .XXX, from_ := regA o }
      else do
        let bit := b.auxInt.toInt
        unless 0 ≤ bit && (bit < k || k == 1) do throw s!"b{b.id}: tested bit"
        pure { as := .XXX, from_ := constA bit, reg := o }
    match cx.two j next { sh with as := asm } e0.b e1.b with
    | .ok () => return
    | .error _ => cx.two j next { sh with as := inv } e1.b e0.b

/-! ## The whole check -/

/-- Slice G3 of the genssa validator (module doc): the PC table and the class table of the
accepted function. -/
def checkG3 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind3 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  if let some i := (List.range lc.homes.size).find? (!homeOK3 lc ·) then throw (homeErr lc i)
  checkFrame lc g
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
  checkK lc kt
  let ids := ps.toList.map (·.id)
  unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
  return (tab, kt)

end GoFV.Gen.Check
