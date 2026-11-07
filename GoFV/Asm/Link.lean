import GoFV.Asm.Prog
import GoFV.Asm.Reg
import GoFV.Asm.Abi
import GoFV.Asm.ObjConst
import GoFV.Asm.Optab

/-!
# The assembler's state (`obj.Link`, `LSym`, `ctxt7`) for one function

Shared state of the I4 ports (`docs/PASSES3.md` D1–D7): `Flushplist` runs `linkpatch` with
`progedit` and `preprocess` (`GoFV.Asm.Obj7`), `span7` (`GoFV.Asm.Span7`, with `oplook`/`aclass`
in `GoFV.Asm.Aclass` and the encoder in `GoFV.Asm.Asmout`), `MarkUnsafePoints` and `linkpcln`
(`GoFV.Asm.Pcln`) on one text symbol, all in the monad `AsmM` over `AsmSt`.

The Prog graph is kept as in `GoFV.Gen` (`objw`): Progs by ID (`AsmSt.progs[id].id = id`) and
`Link` by ID, so `obj.Appendp` and the branch/`Pool` pointers (Prog IDs) are cheap. The input
Progs keep their `prog0` IDs; Progs the assembler allocates get the next IDs in allocation order
and are renumbered in list order at the end (`GoFV.Asm.Flush`), as the exporter numbers them
(`docs/contracts/export.md`, "Progs"). Symbols are numbered as in the input file (`y<n>`); the
ones the assembler creates get the next numbers (named ones interned by name and ABI, as
`ctxt.Lookup`/`LookupInit` do). `ctxt.Diag` is a port error (`throw`): no corpus function has
assembler diagnostics.
-/

namespace GoFV.Asm

open GoFV.SSA (GoStr Pos PosBase)

/-- Read-only inputs: the configuration lines and the file's definitions that `linkpcln`
reads (position bases with their file index, the global inlining tree). -/
structure AsmCtxt where
  /-- `base.Flag.CompilingRuntime`. -/
  compilingRuntime : Bool := false
  /-- `ctxt.Flag_dynlink`. -/
  flagDynlink : Bool := false
  /-- `ctxt.Flag_optimize`. -/
  flagOptimize : Bool := true
  /-- `ctxt.Flag_maymorestack`. -/
  maymorestack : String := ""
  /-- Position bases by `XPos` index: the base and `FileIndex()` (`none`: not registered). -/
  posBases : Std.HashMap Nat (PosBase × Option Int) := {}
  /-- Nodes of the global inlining tree (`base.Ctxt.InlTree`) by index. -/
  inls : Std.HashMap Nat InlDef := {}
  deriving Inhabited

/-- The mutable state: the text symbol's Prog list and `FuncInfo`, the symbols, and the
fields of `ctxt7` (`asm7.go:49-63`). -/
structure AsmSt where
  /-- Progs by ID. IDs without a Prog of the input are unused slots (`as = .XXX`, never
  linked). -/
  progs : Array Prog := #[]
  /-- `Link` by ID. -/
  link : Array (Option Nat) := #[]
  /-- `cursym.Func().Text`. -/
  text : Nat := 0
  /-- IDs below `firstNew` are the input's (`prog0`); the rest were allocated here. -/
  firstNew : Nat := 0
  /-- Symbols by number: name and ABI (index 0 and gaps unused). -/
  syms : Array (GoStr × Nat) := #[]
  /-- Named symbols interned by name and ABI (first number). -/
  symIdx : Std.HashMap (GoStr × Nat) Nat := {}
  /-- `LSym.Align` of symbols whose alignment is known here (created by the assembler). -/
  symAlign : Std.HashMap Nat Int := {}
  /-- Contents of the data symbols the assembler writes (constants, jump tables, pc-value
  tables), by symbol number. -/
  symData : Std.HashMap Nat SymData := {}
  /-- The text symbol's `FuncInfo` (`fn` line: `Args`, `Locals`, `FuncFlag`, attributes,
  spills, inline marks, jump tables, funcaux). -/
  fn : FuncInfo := default
  /-- `ctxt7.autosize`, `extrasize`, `instoffset`, `pc`. -/
  autosize : Int := 0
  extrasize : Int := 0
  instoffset : Int := 0
  pc : Int := 0
  /-- `ctxt7.blitrl`, `elitrl`: the pending literal pool (a Prog chain). -/
  blitrl : Option Nat := none
  elitrl : Option Nat := none
  /-- `ctxt7.pool.start`, `pool.size` (`uint32`). -/
  poolStart : Nat := 0
  poolSize : Nat := 0
  /-- The text symbol's `P`, `R` and `Size`. -/
  textP : ByteArray := .empty
  textR : Array Reloc := #[]
  textSize : Int := 0
  /-- `FuncInfo.Pcln`. -/
  pcln : Pcln := ⟨none, none, none, none, #[], #[]⟩
  /-- `Pcln.UsedFiles` (ascending when compared). -/
  usedFiles : Array Nat := #[]
  /-- `Pcln.InlTree`, the local inlining tree. -/
  inlTree : Array InlNode := #[]
  deriving Inhabited

abbrev AsmM := ReaderT AsmCtxt (StateT AsmSt (Except String))

namespace AsmM

def fail {α} (msg : String) : AsmM α := throw msg

/-- The Prog with ID `id`. -/
def getP (id : Nat) : AsmM Prog := do
  match (← get).progs[id]? with
  | some p => pure p
  | none => throw s!"no Prog {id}"

/-- Replaces the Prog with ID `id` (keeps the ID). -/
def setP (id : Nat) (p : Prog) : AsmM Unit :=
  modify fun s => { s with progs := s.progs.set! id { p with id } }

/-- Updates the Prog with ID `id`. -/
def modP (id : Nat) (f : Prog → Prog) : AsmM Unit := do
  let p ← getP id
  setP id (f p)

/-- `p.Link`. -/
def linkOf (id : Nat) : AsmM (Option Nat) := return ((← get).link[id]?).join

/-- Sets `p.Link`. -/
def setLink (id : Nat) (nxt : Option Nat) : AsmM Unit :=
  modify fun s => { s with link := s.link.set! id nxt }

/-- The zero Prog (`newprog()`: every field zero, `As = AXXX`). -/
def zeroProg (id : Nat) : Prog :=
  { id, pc := 0, spadj := 0, isize := 0, optab := 0, pool := none, as := .XXX, scond := 0,
    from_ := {}, reg := 0, rest := #[], to := {}, regTo2 := 0, mark := 0, pos := Pos.none }

/-- `newprog()`: a fresh zero Prog, not linked. -/
def newProg : AsmM Nat := do
  let s ← get
  let id := s.progs.size
  set { s with progs := s.progs.push (zeroProg id), link := s.link.push none }
  return id

/-- `obj.Appendp(q, newprog)`: a new Prog after `q`, with `q`'s position. -/
def appendp (q : Nat) : AsmM Nat := do
  let p ← newProg
  let qp ← getP q
  modP p fun x => { x with pos := qp.pos }
  setLink p (← linkOf q)
  setLink q (some p)
  return p

/-- The Prog IDs in list order from `TEXT` (`cursym.Func().Text` along `Link`). -/
partial def listOrder : AsmM (Array Nat) := do
  let s ← get
  let rec go (id : Nat) (acc : Array Nat) (fuel : Nat) : Array Nat :=
    if fuel = 0 then acc else
    let acc := acc.push id
    match (s.link[id]?).join with
    | some n => go n acc (fuel - 1)
    | none => acc
  return go s.text #[] (s.progs.size + 1)

/-- The last Prog of the list. -/
def lastProg : AsmM Nat := do
  let o ← listOrder
  return o.back?.getD (← get).text

/-! ## Symbols -/

/-- The name and ABI of symbol `k`. -/
def symName (k : Nat) : AsmM (GoStr × Nat) := do
  match (← get).syms[k]? with
  | some x => pure x
  | none => throw s!"no symbol y{k}"

/-- `ctxt.LookupABI(name, abi)`: the symbol of that name and ABI, created if new. -/
def lookup (name : GoStr) (abi : Nat) : AsmM Nat := do
  let s ← get
  match s.symIdx[(name, abi)]? with
  | some k => pure k
  | none =>
    let k := s.syms.size
    set { s with syms := s.syms.push (name, abi), symIdx := s.symIdx.insert (name, abi) k }
    return k

/-- A new anonymous symbol (`&LSym{}`, as the pc-value table symbols are). -/
def freshSym (name : GoStr := ⟨.empty⟩) (abi : Nat := 0) : AsmM Nat := do
  let s ← get
  let k := s.syms.size
  set { s with syms := s.syms.push (name, abi) }
  return k

/-- `s.Align` (0 when not known here: symbols of other packages and of the compiler's data,
which the export does not record). -/
def symAlign (k : Nat) : AsmM Int := return ((← get).symAlign[k]?).getD 0

/-- The contents of data symbol `k` as the assembler has written them so far (an empty
`Sxxx` symbol if none). -/
def symData (k : Nat) : AsmM SymData := do
  match (← get).symData[k]? with
  | some d => pure d
  | none => pure { sym := k, kind := "Sxxx", size := 0, align := 0, attr := 0, data := .empty,
                   relocs := #[] }

def setSymData (k : Nat) (d : SymData) : AsmM Unit :=
  modify fun s => { s with symData := s.symData.insert k { d with sym := k } }

/-! ## The text symbol -/

/-- Tests attribute `a` (`obj.Attr*`) of the text symbol. -/
def textAttr (a : Int) : AsmM Bool := return (← get).fn.attr &&& a.toNat != 0

/-- Sets attribute `a` of the text symbol (`s.Set(a, v)`). -/
def setTextAttr (a : Int) (v : Bool) : AsmM Unit :=
  modify fun s => { s with fn := { s.fn with attr :=
    if v then s.fn.attr ||| a.toNat else s.fn.attr - (s.fn.attr &&& a.toNat) } }

/-- `ctxt.EmitEntryStackMap(s, p, newprog)` (`plist.go:279-289`). -/
def emitEntryStackMap (p : Nat) : AsmM Nat := do
  let q ← appendp p
  let tpos := (← getP (← get).text).pos
  modP q fun x => { x with pos := tpos, as := .PCDATA,
    from_ := { type := .CONST, offset := Abi.PCDATA_StackMapIndex },
    to := { type := .CONST, offset := -1 } }
  return q

/-- `ctxt.StartUnsafePoint(p, newprog)` (`plist.go:308-317`). -/
def startUnsafePoint (p : Nat) : AsmM Nat := do
  let q ← appendp p
  modP q fun x => { x with as := .PCDATA,
    from_ := { type := .CONST, offset := Abi.PCDATA_UnsafePoint },
    to := { type := .CONST, offset := Abi.UnsafePointUnsafe } }
  return q

/-- `ctxt.EndUnsafePoint(p, newprog, oldval)` (`plist.go:323-332`). -/
def endUnsafePoint (p : Nat) (oldval : Int) : AsmM Nat := do
  let q ← appendp p
  modP q fun x => { x with as := .PCDATA,
    from_ := { type := .CONST, offset := Abi.PCDATA_UnsafePoint },
    to := { type := .CONST, offset := oldval } }
  return q

end AsmM

/-! ## Helpers shared by the ports -/

/-- `ctxt7.chipfloat7` (`asm7.go:3470-3500`): the 8-bit `FMOV` immediate of `e` (raw `float64`
bits), or −1. -/
def chipfloat7 (ei : UInt64) : Int :=
  let l : UInt32 := ei.toUInt32
  let h : UInt32 := (ei >>> 32).toUInt32
  if l != 0 || h &&& 0xffff != 0 then -1 else
  let h1 := h &&& 0x7fc00000
  if h1 != 0x40000000 && h1 != 0x3fc00000 then -1 else
  let n : Nat := (if h &&& 0x80000000 != 0 then 1 <<< 7 else 0)
    ||| (if h1 == 0x3fc00000 then 1 <<< 6 else 0)
    ||| ((h >>> 16) &&& 0x3f).toNat
  n

/-- The optab entry `Prog.Optab = k` names (`optab[k - 1]`). -/
def optabAt? (k : Nat) : Option ARM64.Optab :=
  if k = 0 then none else ARM64.optab[k - 1]?

end GoFV.Asm
