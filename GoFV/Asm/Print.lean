import GoFV.Asm.Prog
import GoFV.SSA.Print

/-!
# Printer of the `gofv-prog 2` format

Writes a `ProgFile` back as canonical `.prog` text (`docs/contracts/export.md`, "gofv-prog 2"),
the inverse of `GoFV.Asm.parseProgFile`. Reuses the `gofv-ssa` printer's primitives.
-/

namespace GoFV.Asm.Print

open GoFV.SSA (GoStr Pos PosBase Token)
open GoFV.SSA.Print

/-- Bytes as lower-case hex, `-` when empty. -/
def bytes (b : ByteArray) : W Unit := if b.isEmpty then s "-" else hex (some b)

/-- A number as lower-case hex. -/
def hexNat (x : Nat) : W Unit := s (String.ofList (Nat.toDigits 16 x))

def val : AddrVal → W Unit
  | .none => s "-"
  | .target id => ref '@' id
  | .textSize k => do s "i"; i k
  | .float b => do s "f"; hexNat b.toNat
  | .str b => do s "s"; hex (some b)

def addr (a : Addr) : W Unit := do
  if a == {} then s "_"
  else
    s a.type.name; s "/"; i a.reg; s "/"; i a.index; s "/"; i a.scale; s "/"; s a.name.name
    s "/"; i a.cls; s "/"; i a.offset; s "/"; optRef 'y' a.sym; s "/"; val a.val

def symHole : Option Nat → W Unit
  | some y => ref 'y' y
  | none => s "_"

def optBool : Option Bool → W Unit
  | some b => bool b
  | none => s "?"

def defLine : Def → W Unit
  | .type k d => do
    s "type "; ref 't' k; sp; optInt d.size; sp; optInt d.align; sp; optInt d.ptrdata; sp
    optBool d.hasPtr; sp
    match d.ptrMask with
    | some b => bytes b
    | none => s "?"
    sp; q d.str; nl
  | .name k d => do
    s "name "; ref 'n' k; sp; q d.sym; sp; s d.cls; sp; optRef 't' d.type; sp; n d.esc; sp
    q d.linkName; sp; n d.linkAbi; sp; optRef 'a' d.aux; nl
  | .sym k name abi => do s "sym "; ref 'y' k; sp; q name; sp; n abi; nl
  | .posBase k b fi => do
    s "posbase "; ref 'p' k; sp; q b.file; sp; i b.line; sp; i b.col; sp; i b.inl; sp; optInt fi; nl
  | .inl k d => do
    s "inl "; ref 'i' k; sp; optRef 'i' d.parent; sp; pos d.pos; sp; optRef 'y' d.func; sp
    q d.name; nl

def warnsEnd (ws : Array GoStr) : W Unit := do
  for x in ws do s "warn "; q x; nl
  s "end\n"

def prog (p : Prog) : W Unit := do
  s "p "; n p.id; sp; i p.pc; sp; i p.spadj; sp; n p.isize; sp; n p.optab; sp
  optRef '@' p.pool; sp; s p.as.name; sp; n p.scond; sp; addr p.from_; sp; i p.reg; sp
  list (fun (k, a) => do n k; s ":"; addr a) p.rest; sp; addr p.to; sp; i p.regTo2; sp
  n p.mark; sp; pos p.pos; nl

def reloc (r : Reloc) : W Unit := do
  s "reloc "; i r.off; sp; n r.siz; sp; s r.type; sp; i r.add; sp; optRef 'y' r.sym; nl

def textLine (t : TextInfo) : W Unit := do
  ref 'y' t.sym; sp; i t.args; sp; i t.locals; sp; n t.funcID; sp; n t.funcFlag; sp
  i t.startLine; sp; hexNat t.attr; nl

def funcInfo (f : FuncInfo) : W Unit := do
  s "fn "
  textLine { sym := f.sym, args := f.args, locals := f.locals, funcID := f.funcID,
             funcFlag := f.funcFlag, startLine := f.startLine, attr := f.attr }
  for x in f.spills do
    s "spill "; addr x.addr; sp; i x.reg; sp; i x.reg2; sp; s x.spill.name; sp
    s x.unspill.name; nl
  for (p, k) in f.inlMarks do s "inlmark "; ref '@' p; sp; i k; nl
  for (y, ts) in f.jumpTables do s "jumptable "; ref 'y' y; sp; list (ref '@') ts; nl
  let a := f.aux
  s "funcaux "; optRef 'y' a.gcArgs; sp; optRef 'y' a.gcLocals; sp; optRef 'y' a.stackObjects
  sp; optRef 'y' a.openCodedDeferInfo; sp; optRef 'y' a.argInfo; sp; optRef 'y' a.argLiveInfo
  sp; optRef 'y' a.wrapInfo; nl

def dcl (tag : String) (d : DclEntry) : W Unit := do
  s tag; sp; ref 'n' d.name; sp; i d.off; sp; flags NameFlags.table d.flags; nl

def frame (f : Frame) : W Unit := do
  s "frame\n"
  for d in f.defs do defLine d
  for d in f.dclIn do dcl "in" d
  for d in f.dclOut do dcl "out" d
  for d in f.optDcl do dcl "opt" d
  for (l, fs) in f.merges do s "merge "; ref 'n' l; sp; list (ref 'n') fs; nl
  s "stack "; i f.stksize; sp; i f.stkptrsize; sp; i f.stkalign; nl
  warnsEnd f.warns

def regArgs (rs : Array RegArg) : W Unit := do
  s "regargs "; list (fun r => do i r.reg; s ":"; i r.off; s ":"; optRef 't' r.type) rs; nl

def genin (g : GenIn) : W Unit := do
  s "genin\n"
  for d in g.defs do defLine d
  s "curfn "; pos g.fnPos; sp; bool g.hasDefer; sp; bool g.openDeferDisallowed; nl
  if let some (name, abi) := g.wrapped then s "wrapped "; q name; sp; n abi; nl
  if let some (bits, slots) := g.openDefer then
    s "opendefer "; ref 'n' bits; sp; list (ref 'n') slots; nl
  regArgs g.regArgs
  s "text "; textLine g.text
  warnsEnd g.warns

def prog0 (p : Prog0) : W Unit := do
  s "prog0\n"
  for d in p.defs do defLine d
  for x in p.progs do prog x
  funcInfo p.fn
  s "needzero "; list (ref 'n') p.needzero; nl
  regArgs p.regArgs
  warnsEnd p.warns

def asm (a : Asm) : W Unit := do
  s "asm\n"
  for d in a.defs do defLine d
  for x in a.progs do prog x
  funcInfo a.fn
  s "text "; i a.textSize; sp; i a.textAlign; sp; bytes a.text; sp; n a.relocs.size; nl
  for r in a.relocs do reloc r
  let c := a.pcln
  s "pcln "; optRef 'y' c.pcsp; sp; optRef 'y' c.pcfile; sp; optRef 'y' c.pcline; sp
  optRef 'y' c.pcinline; sp; list symHole c.pcdata; sp; list symHole c.funcdata; nl
  s "usedfiles "; list n a.usedFiles; nl
  for h : k in [0:a.inlTree.size] do
    let x := a.inlTree[k]
    s "inltree "; n k; sp; i x.parent; sp; pos x.pos; sp; optRef 'y' x.func; sp; q x.name; sp
    i x.parentPC; nl
  for d in a.data do
    s "data "; ref 'y' d.sym; sp; s d.kind; sp; i d.size; sp; i d.align; sp; hexNat d.attr; sp
    bytes d.data; sp; n d.relocs.size; nl
    for r in d.relocs do reloc r
  warnsEnd a.warns

def file (f : ProgFile) : W Unit := do
  s "gofv-prog 2\npkg "; q f.pkg; nl
  s "func "; q f.name; sp; n f.abi; nl
  for (k, v) in f.config do s "config "; s k; sp; token v; nl
  frame f.frame
  genin f.genin
  prog0 f.prog0
  asm f.asm
  s "eof\n"

end Print

/-- The canonical `gofv-prog 2` text of `f`. -/
def printProgFile (f : ProgFile) : String := (Print.file f).run "" |>.2

end GoFV.Asm
