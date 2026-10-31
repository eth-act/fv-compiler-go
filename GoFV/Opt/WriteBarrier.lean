import GoFV.Opt.Pass
import GoFV.Opt.WBHelpers
import GoFV.SSA.ABIAnalyze
import GoFV.SSA.ConstCache
import GoFV.SSA.Edges
import GoFV.SSA.StoreOrder
import GoFV.SSA.TypePred
import GoFV.SSA.TypeNew
import Std.Data.HashSet.Basic

/-!
# writebarrier (`writebarrier.go:164-597`)

Port of `writebarrier` (go1.27.3; docs/PASSES.md, writebarrier) for the configuration of the
corpus: `ABIDefault == ABI1` with at least 3 integer parameter registers (runtime calls take
their arguments in registers, no volatile-source copies, `IsNewObject` in register-result form)
and `GOEXPERIMENT=cgocheck2` off; anything else is reported as not ported.

For each original block (in `f.Blocks` order): mark the `Store`/`Move`/`Zero` that need a
barrier (`needwb`, with the known-zero map of `computeZeroMap`) as `StoreWB`/`MoveWB`/`ZeroWB`;
at the first such block create the shared values (`SB`/`SP`, the `writeBarrier` flag address,
`ConstInt32 0`); put the block in store order; then repeatedly split off the last run of
barrier stores: `b` ends in `If (Neq32 (Load wbaddr mem) 0)` (unlikely) to `bThen` (buffer
entries via `WB` + `Store`s, `wbZero`/`wbMove` calls) and `bEnd` (memory `Phi`, the plain
stores, the `WBend` marker made from the run's last store, the values after the run, `b`'s
old successors and controls). The other run stores are freed in run order.

New objects: the `(*uintptr, mem)` tuple type, `uintptr` type aux, `*AuxCall`s, and the
frontend symbols `runtime.writeBarrier`/`wbZero`/`wbMove`/`type:T` — reused when the input
tables have them, else copied from `PassEnv.frontend` (their contents are frontend state) at
fresh numbers.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.SSA.Func

namespace WB

/-- Pass-wide context. -/
structure Ctx where
  env : PassEnv
  isMem : TypeRef → Bool
  ptrSize : Int
  abi : ABIAnalyze.ABIConfig
  /-- `Config.Types` and pseudo-types used. -/
  tMem : TypeRef
  tResultMem : TypeRef
  tUintptr : TypeRef
  tUintptrPtr : TypeRef
  tUInt32 : TypeRef
  tUInt32Ptr : TypeRef
  tBool : TypeRef
  zeroes : ZeroMap
  /-- New types go at numbers `≥ typeFloor` (past the tables and the file's `typeorder`). -/
  typeFloor : Nat

/-- The values and symbols created at the first barrier block. -/
structure Lazy where
  sp : ID
  sb : ID
  wbaddr : ID
  const0 : ID
  wbZero : AuxRef
  wbMove : AuxRef

/-- Pass state. -/
structure St where
  f : Func
  tabs : Tables
  lazy : Option Lazy := none
  storeNumber : Array Int := #[]

/-- The next free number of a table (numbers start at 1). -/
@[inline] def fresh {α} (a : Array (Option α)) : Nat := max a.size 1

/-- The `*obj.LSym` `name` with ABI `abi`: the input's object if present, else the frontend's
definition at a fresh number (a minimal definition if the frontend has none). -/
def symRef (env : PassEnv) (tabs : Tables) (name : GoStr) (abi : Nat) (typeInfo : Option TypeRef) :
    Tables × AuxRef :=
  match PassEnv.findSym? tabs name (some abi) with
  | some (n, _) => (tabs, n)
  | none =>
    let d := (env.frontendSym? name (some abi)).getD
      { fmt := name, kind := .sym name abi "-" 0 {} typeInfo none none #[] none }
    let n := fresh tabs.auxes
    (tabs.add (.aux n d), n)

/-- `reflectdata.TypeLinksym(t)`. -/
def typeLinksym (env : PassEnv) (tabs : Tables) (t : TypeRef) : Except String (Tables × AuxRef) := do
  let some td := tabs.type? t | throw s!"type t{t} not defined"
  if td.symName.size == 0 then throw s!"TypeLinksym(t{t}): no type symbol name"
  return symRef env tabs ("type:" ++ td.symName) 0 (some t)

/-- `f.spSb()`. -/
def spSb (c : Ctx) (f : Func) : Func × ID × ID := Id.run do
  let mut sp? : Option ID := none
  let mut sb? : Option ID := none
  for v in (f.getB f.entry).values do
    let op := (f.getV v).op
    if op == .SB then sb? := some v
    if op == .SP then sp? := some v
    if sb?.isSome && sp?.isSome then break
  let (f, sb) := match sb? with
    | some v => (f, v)
    | none => f.newValueArgs f.entry Pos.none.withNotStmt .SB c.tUintptr
  let (f, sp) := match sp? with
    | some v => (f, v)
    | none => f.newValueArgs f.entry Pos.none.withNotStmt .SP c.tUintptr
  return (f, sp, sb)

/-- The lazily created globals (`writebarrier.go:221-245`). -/
def initLazy (c : Ctx) (s : St) : St :=
  let f := s.f
  let initpos := (f.getB f.entry).pos
  let (f, sp, sb) := spSb c f
  let syslook (k : String) (dflt : String) : GoStr :=
    match c.env.config? s!"syslook.{k}" with
    | some #[.str n] => n
    | _ => dflt
  let (tabs, wbsym) := symRef c.env s.tabs (syslook "writeBarrier" "runtime.writeBarrier") 0 none
  let (f, wbaddr) := f.newValueArgs f.entry initpos .Addr c.tUInt32Ptr (aux := some wbsym)
    (args := #[sb])
  let (tabs, wbZero) := symRef c.env tabs (syslook "wbZero" "runtime.wbZero") 1 none
  let (tabs, wbMove) := symRef c.env tabs (syslook "wbMove" "runtime.wbMove") 1 none
  let (f, const0) := f.constInt32 c.env.typeOrder.eq c.tUInt32 0
  { f, tabs, lazy := some { sp, sb, wbaddr, const0, wbZero, wbMove },
    storeNumber := Array.replicate (f.vidLast + 1) 0 }

/-- `wbcall(pos, b, fn, sp, mem, args...)` with register arguments: the new memory. -/
def wbcall (c : Ctx) (s : St) (pos : Pos) (b : ID) (fn : AuxRef) (mem : ID) (args : Array ID) :
    Except String (St × ID) := do
  let n := args.size
  let abi ← ABIAnalyze.analyzeIntScalars c.abi c.ptrSize (Array.replicate n (c.tUintptr, c.ptrSize))
  let name ← match s.tabs.aux? fn with
    | some { kind := .sym name .., .. } => pure name
    | _ => throw s!"a{fn} is not an *obj.LSym"
  let a := fresh s.tabs.auxes
  let tabs := s.tabs.add (.aux a { fmt := "AuxCall{" ++ name ++ "}", kind := .call (some fn) (some abi) })
  let (f, call) := s.f.newValueArgs b pos .StaticCall c.tResultMem (auxInt := Int64.ofInt (n * c.ptrSize))
    (aux := some a) (args := args.push mem)
  let (f, sel) := f.newValueArgs b pos .SelectN c.tMem (args := #[call])
  return ({ s with f, tabs }, sel)

/-- The write buffer state of one run (`writes`, `memThen`). -/
structure Buf where
  writes : Array (ID × Pos) := #[]
  memThen : ID

/-- `flush()`: one `WB` call for the pending entries and a buffer `Store` per entry. -/
def flush (c : Ctx) (s : St) (bThen : ID) (pos : Pos) (buf : Buf) : Except String (St × Buf) := do
  if buf.writes.isEmpty then return (s, buf)
  let (tup, tabs) ← s.tabs.newTuple c.typeFloor c.tUintptrPtr c.tMem
  let (tabs, uaux) ← GoFV.Rules.Ty.typeAux tabs c.tUintptr
  let f := s.f
  let (f, call) := f.newValueArgs bThen pos .WB tup (auxInt := Int64.ofNat buf.writes.size)
    (args := #[buf.memThen])
  let (f, curPtr) := f.newValueArgs bThen pos .Select0 c.tUintptrPtr (args := #[call])
  let (f, m) := f.newValueArgs bThen pos .Select1 c.tMem (args := #[call])
  let mut f := f
  let mut memThen := m
  for h : i in [0:buf.writes.size] do
    let (ptr, wpos) := buf.writes[i]
    let (f1, wbuf) := f.newValueArgs bThen wpos .OffPtr c.tUintptrPtr
      (auxInt := Int64.ofInt (i * c.ptrSize)) (args := #[curPtr])
    let (f2, st) := f1.newValueArgs bThen wpos .Store c.tMem (aux := some uaux)
      (args := #[wbuf, ptr, memThen])
    f := f2
    memThen := st
  return ({ s with f, tabs }, { writes := #[], memThen })

/-- `addEntry(pos, ptr)`. -/
def addEntry (c : Ctx) (s : St) (bThen : ID) (pos wpos : Pos) (ptr : ID) (buf : Buf) :
    Except String (St × Buf) := do
  let buf := { buf with writes := buf.writes.push (ptr, wpos) }
  if buf.writes.size == 8 then flush c s bThen pos buf else return (s, buf)

/-- Find the last run of barrier stores in `values` (`FindSeq`): `(start, end, last)`. -/
def findSeq (f : Func) (values : Array ID) : Option (Nat × Nat × ID) := Id.run do
  let mut last : Option ID := none
  let mut start := 0
  let mut stop := 0
  let mut nonPtrStores := 0
  let mut hasMove := false
  for k in [0:values.size] do
    let i := values.size - 1 - k
    let w := values[i]!
    match (f.getV w).op with
    | .StoreWB | .MoveWB | .ZeroWB =>
      start := i
      if last.isNone then
        last := some w
        stop := i + 1
      nonPtrStores := 0
      if (f.getV w).op == .MoveWB then hasMove := true
    | .VarDef | .VarLive => continue
    | .Store =>
      if last.isNone then continue
      nonPtrStores := nonPtrStores + 1
      if nonPtrStores > 2 then break
      if hasMove then break
    | _ =>
      if last.isNone then continue
      break
  return last.map fun l => (start, stop, l)

/-- One `again:` iteration on block `b`: expand the last run of barrier stores. Returns the
number of barrier ops expanded. -/
def expandRun (c : Ctx) (s : St) (lz : Lazy) (b : ID) : Except String (St × Nat) := do
  let mut s := s
  let values := (s.f.getB b).values
  let some (start, stop, last) := findSeq s.f values | throw s!"b{b}: no write barrier store run"
  let stores := values.extract start stop
  let after := values.extract stop values.size
  s := { s with f := s.f.truncateValues b start }
  let mem := memArg s.f stores[0]!
  let pos := (s.f.getV stores[0]!).pos
  -- a nil check of the first store's address is duplicated into both branches
  let nilcheck : Option ID :=
    let a := (s.f.getV stores[0]!).args[0]!
    let x := s.f.getV a
    if x.op == .NilCheck && x.args[1]? == some mem then some a else none
  -- branch point
  let bk := s.f.getB b
  let (f, bThen) := s.f.newBlock .Plain
  let (f, bEnd) := f.newBlock bk.kind
  let f := f.modB bThen fun x => { x with pos }
  let f := f.modB bEnd fun x => { x with pos := bk.pos }
  let f := f.modB b fun x => { x with pos }
  let f := f.copyControls bEnd b
  let f := f.modB bEnd fun x => { x with likely := bk.likely, succs := bk.succs }
  let f := bk.succs.foldl (init := f) fun f e =>
    f.modB e.b fun x => { x with preds := x.preds.modify e.i fun p => { p with b := bEnd } }
  let (f, flag) := f.newValueArgs b pos .Load c.tUInt32 (args := #[lz.wbaddr, mem])
  let (f, flag) := f.newValueArgs b pos .Neq32 c.tBool (args := #[flag, lz.const0])
  let f := (f.modB b fun x => { x with kind := .If }).setControl b flag
  let f := f.modB b fun x => { x with likely := .unlikely, succs := #[] }
  let f := ((f.addEdgeTo b bThen).addEdgeTo b bEnd).addEdgeTo bThen bEnd
  s := { s with f }
  let mut buf : Buf := { memThen := mem }
  let mut nilcheckThen : ID := 0
  if let some nc := nilcheck then
    let x := s.f.getV nc
    let (f, v) := s.f.newValueArgs bThen x.pos .NilCheck x.type (args := #[x.args[0]!, buf.memThen])
    s := { s with f }
    nilcheckThen := v
  let mut n := 0
  -- buffer entries for the StoreWBs
  let mut srcs : Std.HashSet ID := {}
  let mut dsts : Std.HashSet ID := {}
  for w in stores do
    let x := s.f.getV w
    if x.op != .StoreWB then continue
    let wpos := x.pos
    let ptr := x.args[0]!
    let val := x.args[1]!
    if !srcs.contains val then
      if ← WB.needWBsrc s.f s.tabs val then
        srcs := srcs.insert val
        (s, buf) ← addEntry c s bThen pos wpos val buf
    if !dsts.contains ptr && WB.needWBdst s.f c.ptrSize ptr x.args[2]! c.zeroes then
      dsts := dsts.insert ptr
      let p := if nilcheck == some ptr then nilcheckThen else ptr
      let (f, old) := s.f.newValueArgs bThen wpos .Load c.tUintptr (args := #[p, buf.memThen])
      s := { s with f }
      (s, buf) ← addEntry c s bThen pos wpos old buf
    n := n + 1
  (s, buf) ← flush c s bThen pos buf
  -- Zeros and Moves
  for w in stores do
    let x := s.f.getV w
    let wpos := x.pos
    let dst := if nilcheck == some x.args[0]! then nilcheckThen else x.args[0]!
    match x.op with
    | .ZeroWB | .MoveWB =>
      let t ← GoFV.Rules.Ty.ofAux s.tabs x.aux
      let (tabs, typ) ← typeLinksym c.env s.tabs t
      let (f, taddr) := s.f.newValueArgs b wpos .Addr c.tUintptr (aux := some typ) (args := #[lz.sb])
      s := { s with f, tabs }
      let (fn, args) := if x.op == .ZeroWB then (lz.wbZero, #[taddr, dst])
        else (lz.wbMove, #[taddr, dst, x.args[1]!])
      let (s', m) ← wbcall c s wpos bThen fn buf.memThen args
      s := s'
      buf := { buf with memThen := m }
      n := n + 1
    | _ => pure ()
  -- merge memory
  let (f, phi) := s.f.newValueArgs bEnd pos .Phi c.tMem (args := #[mem, buf.memThen])
  s := { s with f }
  let mut mem := phi
  let mut nilcheckEnd : ID := 0
  if let some nc := nilcheck then
    let x := s.f.getV nc
    let (f, v) := s.f.newValueArgs bEnd x.pos .NilCheck x.type (args := #[x.args[0]!, mem])
    s := { s with f }
    nilcheckEnd := v
  -- the stores proper, after the merge
  for w in stores do
    let x := s.f.getV w
    let wpos := x.pos
    let dst := if nilcheck == some x.args[0]! then nilcheckEnd else x.args[0]!
    let r : Option (Func × ID) := match x.op with
      | .StoreWB | .Store =>
        some (s.f.newValueArgs bEnd wpos .Store c.tMem (aux := x.aux) (args := #[dst, x.args[1]!, mem]))
      | .ZeroWB =>
        some (s.f.newValueArgs bEnd wpos .Zero c.tMem (auxInt := x.auxInt) (aux := x.aux)
          (args := #[dst, mem]))
      | .MoveWB =>
        some (s.f.newValueArgs bEnd wpos .Move c.tMem (auxInt := x.auxInt) (aux := x.aux)
          (args := #[dst, x.args[1]!, mem]))
      | .VarDef | .VarLive =>
        some (s.f.newValueArgs bEnd wpos x.op c.tMem (aux := x.aux) (args := #[mem]))
      | _ => none
    if let some (f, m) := r then
      s := { s with f }
      mem := m
  -- the last store becomes the WBend marker
  let mut f := s.f.modB bEnd fun x => { x with values := x.values.push last }
  f := f.modV last fun x => { x with block := bEnd }
  f := f.resetValue last .WBend
  f := f.modV last fun x => { x with pos := x.pos.withNotStmt, type := c.tMem }
  f := f.addArg last mem
  -- free the other stores
  for w in stores do
    if w != last then f := f.resetArgs w
  for w in stores do
    if w != last then
      if (f.getV w).uses != 0 then throw s!"v{w} still has {(f.getV w).uses} uses"
      f := f.freeValue w
  if let some nc := nilcheck then
    if (f.getV nc).uses == 0 then f := f.resetValue nc .Invalid
  -- values after the run move to the end block
  f := f.modB bEnd fun x => { x with values := x.values ++ after }
  for w in after do
    f := f.modV w fun x => { x with block := bEnd }
  return ({ s with f }, n)

/-- Process one original block (`writebarrier.go:198-584`). -/
def block (c : Ctx) (s : St) (b : ID) : Except String St := do
  let mut s := s
  let mut nWBops := 0
  for v in (s.f.getB b).values do
    let op := (s.f.getV v).op
    if op == .Store || op == .Move || op == .Zero then
      if ← WB.needwb s.f s.tabs c.ptrSize v c.zeroes then
        let op' : Op := match op with | .Store => .StoreWB | .Move => .MoveWB | _ => .ZeroWB
        s := { s with f := s.f.modV v fun x => { x with op := op' } }
        nWBops := nWBops + 1
  if nWBops == 0 then return s
  if s.lazy.isNone then s := initLazy c s
  let some lz := s.lazy | throw "unreachable"
  let (vals, sn) ← storeOrder s.f c.isMem c.env.passName (s.f.getB b).values s.storeNumber
  s := { s with f := s.f.modB b fun x => { x with values := vals }, storeNumber := sn }
  for _ in [0:nWBops] do
    let (s', n) ← expandRun c s lz b
    s := s'
    if n > nWBops then throw s!"b{b}: write barrier op count"
    nWBops := nWBops - n
    if nWBops == 0 then break
    if n == 0 then throw s!"b{b}: write barrier run without barrier ops"
  return s

end WB

open WB in
/-- `writebarrier(f)`. -/
def writebarrier (env : PassEnv) (f : Func) : Except String PassOut := do
  if !(← env.flag "usewb") then return { func := f, tables := env.tables }
  if ← env.flag "exp.cgocheck2" then throw "writebarrier: GOEXPERIMENT=cgocheck2 not ported"
  let abiOf (k : String) (which : Nat) : Except String ABIAnalyze.ABIConfig :=
    match env.config? k with
    | some #[.word s] => (ABIAnalyze.ABIConfig.parse which s).elim (.error s!"config {k}: bad") .ok
    | _ => .error s!"config {k}: missing"
  let abi1 ← abiOf "abi1" 1
  if env.config? "abidefault" != some #[.word "1"] || abi1.intRegs < 3 then
    throw "writebarrier: stack-argument ABI not ported"
  let ptrSize ← match env.config? "ptrsize" with
    | some #[.word s] => (s.toInt?).elim (.error "config ptrsize: bad") .ok
    | _ => .error "config ptrsize: missing"
  let localPkgRuntime := env.config? "localpkg" == some #[.str "runtime"]
  let typ (n : String) : Except String TypeRef :=
    (env.typ? n).elim (.error s!"typs: no {n}") .ok
  let tMem ← typ "Mem"
  let isMem := env.tables.isMemory tMem
  -- select1[call] = its SelectN [1]
  let mut select1 : Array (Option ID) := Array.replicate (f.vidLast + 1) none
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      if x.op == .SelectN && x.auxInt == 1 then select1 := select1.set! x.args[0]! (some v)
  let zeroes ← WB.computeZeroMap f env.tables ptrSize localPkgRuntime select1
  let c : Ctx := { env, isMem, ptrSize, abi := abi1, tMem, tResultMem := ← typ "ResultMem",
                   tUintptr := ← typ "Uintptr", tUintptrPtr := ← typ "UintptrPtr",
                   tUInt32 := ← typ "UInt32", tUInt32Ptr := ← typ "UInt32Ptr", tBool := ← typ "Bool",
                   zeroes, typeFloor := max env.tables.types.size env.typeOrder.rank.size }
  let mut s : St := { f, tabs := env.tables }
  for b in f.blocks do
    s ← WB.block c s b
  return { func := s.f, tables := s.tabs }

def writebarrierPass : Pass := writebarrier

end GoFV.Opt
