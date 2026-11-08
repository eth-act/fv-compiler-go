import GoFV.Gen.Env
import Std.Data.HashSet.Basic

/-!
# The Prog builder (`objw.Progs`) and the genssa state

Port of `cmd/compile/internal/objw/prog.go` (`docs/PASSES3.md` C1) and of the fields of
`ssagen.State` (`ssagen/ssa.go:6716-6748`) the arm64 emitters use, as one state monad `GenM`
shared by the ports of B1–C6.

Progs are stored by stable ID: `objw` numbers every Prog it allocates (`Clear` sets `Pc` to the
allocation count), and the export uses that number as the Prog's ID, so `progs[id]` is the Prog
with ID and `Pc` `id`. The list order is the `link` chain from the `TEXT` Prog: `NewProgs`
allocates the priming placeholder (ID 0) and `SetText` fills it with `TEXT`. The last element of
the chain is the current placeholder `next`, an `END` Prog, which the export includes. Branch
targets and inline marks are Prog IDs.

Symbols are interned by name and ABI (`ctxt.Lookup`/`LookupInit` and the frontend's symbol
resolution); `Addr.sym` is an index into `GenState.syms`. The comparison with the export maps
both sides to (name, ABI).
-/

namespace GoFV.Gen

open GoFV.SSA
open GoFV.Asm

/-- `objw.StackMapDontCare`. -/
def stackMapDontCare : Int := -1000

/-- A relocation of a symbol the port writes (`obj.Reloc`); `sym` indexes `GenState.syms`. -/
structure RelocOut where
  off : Int
  siz : Nat
  type : String
  add : Int
  sym : Option Nat
  deriving DecidableEq, Inhabited

/-- Contents the port gives a symbol (a metadata symbol: stack maps, stack objects, argument
info, …): `LSym.Type` (`SymKind.String()`), `Size`, `Align`, the attributes the port sets
(raw `obj.Attribute` bits), `P` and `R`. -/
structure SymOut where
  kind : String := "Sxxx"
  size : Int := 0
  align : Int := 0
  attr : Nat := 0
  data : ByteArray := .empty
  relocs : Array RelocOut := #[]
  deriving Inhabited

/-- `ssagen.Branch`: an unresolved branch (Prog ID, target block). -/
structure Branch where
  prog : Nat
  target : ID
  deriving Inhabited

/-- `liveness.Map` (`liveness/plive.go`): stack-map index per safe point value (absent:
`StackMapDontCare`), the unsafe values and blocks, the index at the open-defer `deferreturn`
call; plus the partially live arguments `liveness.Compute` returns. -/
structure LiveMap where
  vals : Std.HashMap ID Int := {}
  unsafeVals : Std.HashSet ID := {}
  unsafeBlocks : Std.HashSet ID := {}
  deferReturn : Int := stackMapDontCare
  /-- `partLiveArgs`, by name number. -/
  partLiveArgs : Std.HashSet Nat := {}
  deriving Inhabited

namespace LiveMap
/-- `Map.Get`. -/
def get (m : LiveMap) (v : ID) : Int := m.vals.getD v stackMapDontCare
/-- `Map.GetUnsafe`. -/
def getUnsafe (m : LiveMap) (v : ID) : Bool := m.unsafeVals.contains v
/-- `Map.GetUnsafeBlock`. -/
def getUnsafeBlock (m : LiveMap) (b : ID) : Bool := m.unsafeBlocks.contains b
end LiveMap

/-- The state of `objw.Progs`, the text symbol's `FuncInfo` records and `ssagen.State`. -/
structure GenState where
  /-- Prog by ID (allocation order). -/
  progs : Array Prog := #[]
  /-- `Link` by ID. -/
  link : Array (Option Nat) := #[]
  /-- `pp.Text`. -/
  text : Nat := 0
  /-- `pp.Next`: the placeholder the next `Prog` call fills. -/
  next : Nat := 0
  /-- `pp.Pos`. -/
  pos : Pos := Pos.none
  nextLive : Int := -1
  prevLive : Int := -1
  nextUnsafe : Bool := false
  prevUnsafe : Bool := false
  /-- Interned symbols: name and ABI. -/
  syms : Array (GoStr × Nat) := #[]
  symIdx : Std.HashMap (GoStr × Nat) Nat := {}
  /-- Contents of symbols the port writes, by symbol index. -/
  symData : Std.HashMap Nat SymOut := {}
  /-- `FuncInfo` records set during `genssa`. -/
  spills : Array Spill := #[]
  inlMarks : Array (Nat × Int) := #[]
  jumpTableSyms : Array (Nat × Array Nat) := #[]
  aux : FuncAux := ⟨none, none, none, none, none, none, none⟩
  /-- `f.RegArgs` (the first `ArgIntReg`/`ArgFloatReg` consumes it). -/
  regArgs : Array RegSpill := #[]
  /-- `ssagen.State` fields. -/
  branches : Array Branch := #[]
  jumpTables : Array ID := #[]
  bstart : Array (Option Nat) := #[]
  /-- `valueToProgAfter` (`ssa.go:7174`, location lists): per value, `pp.Next` after its code
  (the Prog the value is visible at; `FuncDebug.GetPC` reads its `Pc` after assembly). -/
  progAfter : Std.HashMap ID Nat := {}
  maxarg : Int := 0
  lineRunStart : Option Nat := none
  /-- `s.livenessMap` and `s.partLiveArgs` (set by `liveness.Compute`). -/
  live : LiveMap := {}
  /-- `curfn.Dcl` after `AllocFrame`, with the flags as they change (`liveness` sets
  `Needzero`). -/
  dcl : Array DclEntry := #[]
  deriving Inhabited

/-- Read-only context: the input and the frame after `AllocFrame`. -/
structure Ctx where
  env : Env
  frame : FrameOut
  /-- `Name.FrameOffset()` after `AllocFrame`, by name number (from `FrameOut.dcl` and
  `FrameOut.optDcl`). -/
  offsets : Array (Option Int)

namespace Ctx

/-- Builds the context of a frame layout. -/
def ofFrame (env : Env) (fr : FrameOut) : Ctx := Id.run do
  let mut offs : Array (Option Int) := Array.replicate env.names.size none
  for d in fr.dcl ++ fr.optDcl do
    if d.name < offs.size then offs := offs.set! d.name (some d.off)
  return { env, frame := fr, offsets := offs }

end Ctx

abbrev GenM := ReaderT Ctx (StateT GenState (Except String))

namespace GenM

def env : GenM Env := return (← read).env

def fail {α} (msg : String) : GenM α := throw msg

/-- Lifts an `Except String` computation. -/
def lift {α} (x : Except String α) : GenM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-- The Prog with ID `id`. -/
def getP (id : Nat) : GenM Prog := do
  match (← get).progs[id]? with
  | some p => pure p
  | none => throw s!"no Prog {id}"

/-- Updates the Prog with ID `id`. -/
def modP (id : Nat) (f : Prog → Prog) : GenM Unit := do
  let p ← getP id
  modify fun s => { s with progs := s.progs.set! id (f p) }

/-- `obj.Nopout` + `objw.Progs.Clear`: a fresh `AEND` Prog numbered by allocation. -/
def newProg : GenM Nat := do
  let s ← get
  let id := s.progs.size
  let p : Prog := { id, pc := id, spadj := 0, isize := 0, optab := 0, pool := none, as := .END,
                    scond := 0, from_ := {}, reg := 0, rest := #[], to := {}, regTo2 := 0,
                    mark := 0, pos := Pos.none }
  set { s with progs := s.progs.push p, link := s.link.push none }
  return id

def setLink (id : Nat) (nxt : Option Nat) : GenM Unit :=
  modify fun s => { s with link := s.link.set! id nxt }

def linkOf (id : Nat) : GenM (Option Nat) := return ((← get).link[id]?).join

/-- `objw.LosesStmtMark`. -/
def losesStmtMark (as : As) : Bool := as == .PCDATA || as == .FUNCDATA

/-- `Addr.SetConst`. -/
def constAddr (v : Int) : Addr := { type := .CONST, offset := v }

/-- `objw.Progs.Prog`: emits the pending stack-map and unsafe-point PCDATA, then fills the
placeholder with `as` at `pp.Pos` and links a new placeholder. -/
partial def prog (as : As) : GenM Nat := do
  let s ← get
  if s.nextLive != stackMapDontCare && s.nextLive != s.prevLive then
    let idx := s.nextLive
    modify fun s => { s with prevLive := idx }
    let p ← prog .PCDATA
    modP p fun p => { p with from_ := constAddr 1, to := constAddr idx }
  let s ← get
  if s.nextUnsafe != s.prevUnsafe then
    modify fun s => { s with prevUnsafe := s.nextUnsafe }
    let p ← prog .PCDATA
    modP p fun p => { p with from_ := constAddr 0, to := constAddr (if s.nextUnsafe then -2 else -1) }
  let p := (← get).next
  let q ← newProg
  modify fun s => { s with next := q }
  setLink p (some q)
  let pos := (← get).pos
  modP p fun x => { x with as := as, pos := pos }
  if pos.isStmt == Pos.isStmtMark then
    if losesStmtMark as then return p
    modify fun s => { s with pos := s.pos.withNotStmt }
  return p

/-- `objw.Progs.Append`: inserts a new Prog after `p` (no PCDATA, position of `p`). -/
def append (p : Nat) (as : As) (ftype : AddrType) (freg : Int) (foffset : Int)
    (ttype : AddrType) (treg : Int) (toffset : Int) : GenM Nat := do
  let q ← newProg
  let pp ← getP p
  modP q fun x =>
    { x with as := as, pos := pp.pos,
             from_ := { x.from_ with type := ftype, reg := freg, offset := foffset },
             to := { x.to with type := ttype, reg := treg, offset := toffset } }
  setLink q (← linkOf p)
  setLink p (some q)
  return q

/-- `objw.NewProgs` with `SetText`: the priming placeholder (ID 0) becomes `TEXT` at
`fn.Pos()`, PCDATA tables start at index −1. -/
def newProgs (fnPos : Pos) (textSym : Nat) : GenM Unit := do
  let p ← newProg
  modify fun s => { s with next := p, pos := fnPos, prevLive := -1, nextLive := -1,
                           prevUnsafe := false, nextUnsafe := false }
  let t ← prog .TEXT
  modify fun s => { s with text := t }
  modP t fun x => { x with from_ := { type := .MEM, name := .EXTERN, sym := some textSym } }

/-- Interns a symbol by name and ABI. -/
def sym (name : GoStr) (abi : Nat) : GenM Nat := do
  let s ← get
  match s.symIdx[(name, abi)]? with
  | some k => pure k
  | none =>
    let k := s.syms.size
    set { s with syms := s.syms.push (name, abi), symIdx := s.symIdx.insert (name, abi) k }
    return k

/-- The Prog IDs in list order (the `link` chain from `TEXT`). -/
partial def listOrder : GenM (Array Nat) := do
  let s ← get
  let rec go (id : Nat) (acc : Array Nat) (fuel : Nat) : Array Nat :=
    if fuel = 0 then acc else
    let acc := acc.push id
    match (s.link[id]?).join with
    | some n => go n acc (fuel - 1)
    | none => acc
  return go s.text #[] (s.progs.size + 1)

end GenM

/-- `genssa`'s result (P0): the final state (Progs by ID, symbols, `FuncInfo` records, `Dcl`
flags, `f.RegArgs`) and the Prog IDs in list order (`TEXT` first, the `END` placeholder last). -/
structure GenOut where
  st : GenState
  order : Array Nat
  deriving Inhabited

end GoFV.Gen
