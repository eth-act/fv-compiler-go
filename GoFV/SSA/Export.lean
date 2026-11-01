import GoFV.SSA.Func

/-!
# Export files

One `gofv-ssa` file (`docs/contracts/export.md`): a function's SSA after each pass, with the
per-file definition tables (types, aux values, local slots, position bases) defined
incrementally. `Tables` is the accumulated state a pass reads next to its `Func`.
-/

namespace GoFV.SSA

/-- A token of the export format: a bare word or a (decoded) quoted string. -/
inductive Token where
  | word (s : String)
  | str (s : GoStr)
  deriving DecidableEq, Inhabited

/-- One definition line (with its sub-lines). -/
inductive Def where
  | posBase (index : Nat) (b : PosBase)
  | type (n : TypeRef) (t : TypeDef)
  | aux (n : AuxRef) (a : AuxDef)
  | slot (n : SlotRef) (s : SlotDef)
  deriving DecidableEq, Inhabited

/-- The function after one pass (section `index`; 0 is `start`). -/
structure Section where
  index : Nat
  pass : GoStr
  /-- Definitions made in this section, in file order. -/
  defs : Array Def
  func : Func
  /-- `typs` (section 0 only): the `Config.Types` fields (`Bool`, …, `ResultMem`) in order. -/
  typs : Option (Array (String × TypeRef))
  /-- `zvar`: type-object classes of zero-argument values whose type number has several
  `*types.Type` objects among them (`zcse` keys on the pointer); unlisted values: class 0. -/
  zvar : Array (ID × Nat)
  /-- `warn` lines (exporter invariant failures), in order. -/
  warns : Array GoStr
  deriving DecidableEq, Inhabited

/-- A whole export file. -/
structure ExportFile where
  version : Nat
  pkg : GoStr
  name : GoStr
  /-- `f.ABISelf.Which()`. -/
  abi : Nat
  nosplit : Bool
  pgohot : Bool
  /-- `config` lines in order: key and value tokens. -/
  config : Array (String × Array Token)
  sections : Array Section
  /-- The `frontend` block: definitions of the symbols reachable through relocations of
  exported read-only generic dictionaries that no section defines (export.md, "Frontend
  block"). -/
  frontend : Array Def
  /-- `warn` lines written after the last section (before `typeorder`). -/
  warns : Array GoStr
  /-- `ptrcache`: type numbers whose canonical object has a cached pointer type (the backend's
  `types.NewPtr` returns a shared object for them, a fresh one otherwise; #101). -/
  ptrCache : Array TypeRef
  /-- `typecmp` lines: pairs `(a, b, Compare(a, b))`, `a < b` by number, whose `Compare` result
  disagrees with the `typeorder` ranks (`Compare` is not a total preorder, #68). -/
  typeCmp : Array (TypeRef × TypeRef × Ordering)
  /-- `typeorder`: groups of `CMPeq` types in ascending `types.(*Type).Compare` order. -/
  typeOrder : Array (Array TypeRef)
  deriving DecidableEq, Inhabited

/-- The definition tables in force at some point of a file, indexed by table number (position
bases by `XPos` index). Later definitions with the same number replace earlier ones. -/
structure Tables where
  posBases : Array (Option PosBase) := #[]
  types : Array (Option TypeDef) := #[]
  auxes : Array (Option AuxDef) := #[]
  slots : Array (Option SlotDef) := #[]
  deriving Inhabited

namespace Tables

private def put {α} (a : Array (Option α)) (i : Nat) (x : α) : Array (Option α) :=
  let a := if i < a.size then a else a ++ Array.replicate (i + 1 - a.size) none
  a.set! i (some x)

def add (t : Tables) : Def → Tables
  | .posBase i b => { t with posBases := put t.posBases i b }
  | .type n d => { t with types := put t.types n d }
  | .aux n d => { t with auxes := put t.auxes n d }
  | .slot n d => { t with slots := put t.slots n d }

def addAll (t : Tables) (ds : Array Def) : Tables := ds.foldl add t

def posBase? (t : Tables) (i : Nat) : Option PosBase := (t.posBases[i]?).join
def type? (t : Tables) (n : TypeRef) : Option TypeDef := (t.types[n]?).join
def aux? (t : Tables) (n : AuxRef) : Option AuxDef := (t.auxes[n]?).join
def slot? (t : Tables) (n : SlotRef) : Option SlotDef := (t.slots[n]?).join

end Tables

/-- The tables in force for section `k` (definitions of sections `0..k`). -/
def ExportFile.tablesAt (e : ExportFile) (k : Nat) : Tables :=
  (e.sections.extract 0 (k + 1)).foldl (fun t s => t.addAll s.defs) {}

/-- All definitions of the file: the final tables plus the `frontend` block (the frontend's
objects a pass may look up by name, `PassEnv.frontend`). -/
def ExportFile.frontendTables (e : ExportFile) : Tables :=
  (e.tablesAt (e.sections.size - 1)).addAll e.frontend

end GoFV.SSA
