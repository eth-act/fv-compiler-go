import GoFV.SSA.Export

/-!
# Printer of the export format

Writes an `ExportFile` back as canonical `gofv-ssa` text (`docs/contracts/export.md`), the
inverse of `GoFV.SSA.parseExport`.
-/

namespace GoFV.SSA.Print

/-- Output buffer. -/
abbrev W := StateM String

@[inline] def s (x : String) : W Unit := modify (· ++ x)
@[inline] def sp : W Unit := modify (·.push ' ')
@[inline] def nl : W Unit := modify (·.push '\n')
@[inline] def q (x : GoStr) : W Unit := modify (GoStr.quoteInto · x)
@[inline] def n (x : Nat) : W Unit := s (toString x)
@[inline] def i (x : Int) : W Unit := s (toString x)
@[inline] def i64 (x : Int64) : W Unit := s (toString x)

def ref (c : Char) (x : Nat) : W Unit := do modify (·.push c); n x
def optRef (c : Char) : Option Nat → W Unit
  | some x => ref c x
  | none => s "-"
def optInt : Option Int → W Unit
  | some x => i x
  | none => s "?"
def bool (b : Bool) : W Unit := s (if b then "1" else "0")

/-- Comma list, `-` if empty. -/
def list {α} (p : α → W Unit) (xs : Array α) : W Unit := do
  if xs.isEmpty then s "-"
  else
    let mut first := true
    for x in xs do
      if !first then s ","
      first := false
      p x

def flags {α} (table : List (String × (α → Bool) × (α → α))) (f : α) : W Unit :=
  list s (table.filter (·.2.1 f) |>.map (·.1) |>.toArray)

def pos (p : Pos) : W Unit := do
  ref 'p' p.index; s ":"; n p.line; s ":"; n p.col; s ":"; n p.stmt; s ":"; n p.xlogue

def edge (e : Edge) : W Unit := do ref 'b' e.b; s ":"; n e.i

def slotKey (k : SlotKey) : W Unit := do
  ref 'a' k.name; s "/"; ref 't' k.type; s "/"; i k.off; s "/"; optRef 's' k.splitOf; s "/"
  i k.splitOffset

def hex (d : Option ByteArray) : W Unit := do
  match d with
  | none => s "-"
  | some b =>
    for x in b do
      let h (v : UInt8) : Char := if v < 10 then Char.ofNat (48 + v.toNat) else Char.ofNat (87 + v.toNat)
      modify fun o => (o.push (h (x >>> 4))).push (h (x &&& 15))

def token : Token → W Unit
  | .word w => s w
  | .str x => q x

def field (k : Nat) (f : Field) : W Unit := do
  s "field "; n k; sp; q f.name; sp; ref 't' f.type; sp; optInt f.offset; sp; bool f.embedded; nl

def typeDef (r : TypeRef) (t : TypeDef) : W Unit := do
  s "type "; ref 't' r; sp; s t.kind.name; sp; optInt t.size; sp; optInt t.align; sp
  optInt t.ptrdata; sp; flags TypeFlags.table t.flags; sp; q t.str; sp; q t.symName
  let fieldLines (fs : Array Field) : W Unit := do
    let mut k := 0
    for f in fs do
      field k f
      k := k + 1
  match t.tail with
  | .none => nl
  | .elem e => do sp; ref 't' e; nl
  | .array e m => do sp; ref 't' e; sp; i m; nl
  | .struct fs => do sp; n fs.size; nl; fieldLines fs
  | .func r p o fs => do sp; n r; sp; n p; sp; n o; nl; fieldLines fs
  | .tuple a b => do sp; ref 't' a; sp; ref 't' b; nl
  | .results ts => do sp; n ts.size; sp; list (ref 't') ts; nl

def auxDef (r : AuxRef) (a : AuxDef) : W Unit := do
  s "aux "; ref 'a' r; sp
  match a.kind with
  | .name sym cls t off esc fl p => do
    s "name "; q a.fmt; sp; q sym; sp; s cls.name; sp; ref 't' t; sp; i off; sp; n esc; sp
    flags NameFlags.table fl; sp; pos p; nl
  | .sym name abi kind size fl ti ii data relocs rt => do
    s "sym "; q a.fmt; sp; q name; sp; n abi; sp; s kind; sp; i size; sp
    flags SymFlags.table fl; sp; optRef 't' ti; sp; optRef 't' ii; sp; hex data; sp
    n relocs.size; nl
    for x in relocs do
      s "reloc "; i x.off; sp; i x.siz; sp; s x.type; sp; i x.add; sp; q x.target; sp
      i x.targetAbi; nl
    if let some x := rt then
      s "rtype "; optInt x.size; sp; optInt x.ptrdata; sp; optInt x.hash; sp; optInt x.abiKind
      sp; q x.gcdata; sp; q x.elemSym; nl
  | .str x d => do s "str "; q a.fmt; sp; q x; sp; q d; nl
  | .call fn none => do s "call "; q a.fmt; sp; optRef 'a' fn; s " - 0 0 0 0 0 0"; nl
  | .call fn (some c) => do
    s "call "; q a.fmt; sp; optRef 'a' fn; sp; n c.abi; sp; n c.nin; sp; n c.nout; sp
    i c.spillOff; sp; i c.spillSize; sp; i c.inRegs; sp; i c.outRegs; nl
    for p in c.params do
      s "abiparam "; s (if p.out then "out" else "in"); sp; n p.index; sp; ref 't' p.type; sp
      optRef 'a' p.name; sp; list n p.regs; sp; i p.offset; nl
  | .nameOff x off => do s "nameoff "; q a.fmt; sp; ref 'a' x; sp; i off; nl
  | .type t => do s "type "; q a.fmt; sp; ref 't' t; nl
  | .int x => do s "int "; q a.fmt; sp; i x; nl
  | .mark => do s "mark "; q a.fmt; nl
  | .pbc c => do s "pbc "; q a.fmt; sp; i c; nl
  | .pbcc x y => do s "pbcc "; q a.fmt; sp; i x; sp; i y; nl
  | .unknown t => do s "unknown "; q a.fmt; sp; q t; nl

def defn : Def → W Unit
  | .posBase k b => do
    s "posbase "; ref 'p' k; sp; q b.file; sp; i b.line; sp; i b.col; sp; i b.inl; nl
  | .type r t => typeDef r t
  | .aux r a => auxDef r a
  | .slot r d => do
    s "slot "; ref 's' r; sp; ref 'a' d.name; sp; ref 't' d.type; sp; i d.off; sp
    optRef 's' d.splitOf; sp; i d.splitOffset; nl

def value (v : Value) : W Unit := do
  s "v "; ref 'v' v.id; sp; s v.op.name; sp; ref 't' v.type; sp; i64 v.auxInt; sp
  optRef 'a' v.aux; sp; pos v.pos; sp; n v.uses; sp; list (ref 'v') v.args; nl

def block (f : Func) (b : Block) : W Unit := do
  s "b "; ref 'b' b.id; sp; s b.kind.name; sp; pos b.pos; sp; i b.likely.toInt; sp
  i64 b.auxInt; sp; optRef 'a' b.aux; sp; list (ref 'v') b.controls; sp; list edge b.succs; sp
  list edge b.preds; nl
  for id in b.values do
    match f.value? id with
    | some v => value v
    | none => s s!"v v{id} <missing>\n"

/-- Space-separated entries, `-` if none. -/
def entries {α} (p : α → W Unit) (xs : Array α) : W Unit := do
  if xs.isEmpty then s " -"
  else for x in xs do sp; p x

def func (f : Func) : W Unit := do
  s "f "; ref 'b' f.entry; sp; ref 't' f.type; sp; optRef 'a' f.ownAux; sp; n f.vidLast; sp
  n f.bidLast; nl
  for id in f.blocks do
    match f.block? id with
    | some b => block f b
    | none => s s!"b b{id} <missing>\n"
  s "names "; list (ref 's') (f.names.map (·.1)); nl
  for (k, vs) in f.names do
    s "named "; ref 's' k; sp; list (ref 'v') vs; nl
  for (k, vs) in f.namedx do
    s "namedx "; slotKey k; sp; list (ref 'v') vs; nl
  s "splits"
  entries (fun (k, r) => do ref 's' k.parent; s "/"; i k.off; s "/"; ref 't' k.type; s "="; ref 's' r) f.splits
  nl
  s "canon"; entries (fun (k, r) => do slotKey k; s "="; ref 's' r) f.canon; nl
  s "consts"; entries (fun (k, vs) => do i64 k; s "="; list (ref 'v') vs) f.consts; nl
  s "freev "; list (ref 'v') f.freeValues; nl
  s "freeb "; list (ref 'b') f.freeBlocks; nl
  let c := f.cache
  if let some po := c.postorder then
    s "cache postorder "; list (ref 'b') po; nl
  if let some d := c.idom then
    s "cache idom "; list (fun (b, x) => do ref 'b' b; s ":"; optRef 'b' x) d; nl
  if let some d := c.sdom then
    s "cache sdom "
    list (fun (x : SdomNode) => do
      ref 'b' x.block; s ":"; optRef 'b' x.parent; s ":"; optRef 'b' x.child; s ":"
      optRef 'b' x.sibling; s ":"; i x.entry; s ":"; i x.exit) d
    nl
  if c.loopnest then s "cache loopnest\n"
  if let some m := c.auxmap then
    s "cache auxmap "; list (fun (a, k) => do ref 'a' a; s ":"; i k) m; nl
  if let some ls := c.lineStarts then
    s "cache linestarts "; list (fun (x : LineRange) => do n x.index; s ":"; i x.first; s ":"; i x.last) ls
    nl

def sectionW (x : Section) : W Unit := do
  s "pass "; n x.index; sp; q x.pass; nl
  for d in x.defs do defn d
  func x.func
  for m in x.warns do
    s "warn "; q m; nl
  s "end\n"

def file (e : ExportFile) : W Unit := do
  s "gofv-ssa "; n e.version; nl
  s "pkg "; q e.pkg; nl
  s "func "; q e.name; sp; n e.abi; sp; bool e.nosplit; sp; bool e.pgohot; nl
  for (k, ts) in e.config do
    s "config "; s k
    for t in ts do sp; token t
    nl
  for x in e.sections do sectionW x
  for m in e.warns do
    s "warn "; q m; nl
  s "typeorder"
  for g in e.typeOrder do
    sp
    let mut first := true
    for t in g do
      if !first then s "="
      first := false
      ref 't' t
  nl
  s "eof\n"

end Print

/-- The canonical `gofv-ssa` text of an export file. -/
def printExport (e : ExportFile) : String := (Print.file e |>.run "").2

end GoFV.SSA
