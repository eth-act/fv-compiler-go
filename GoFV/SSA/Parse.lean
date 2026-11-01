import GoFV.SSA.Export
import Std.Data.HashMap.Basic

/-!
# Parser of the export format

Parses a `gofv-ssa` file (`docs/contracts/export.md`) into an `ExportFile`. The parser is
strict: it accepts exactly the canonical text `GoFV.SSA.Print` produces (one space between
tokens, canonical numbers and string escapes, records in the documented order), so
`print ∘ parse` is the identity on every file it accepts; anything else is an error naming the
line. Words are parsed in place as byte slices of the input (no intermediate strings).
-/

namespace GoFV.SSA.Parse

/-! ## Byte slices -/

/-- Bytes `[start, stop)` of `data`. -/
structure Sl where
  data : ByteArray
  start : Nat
  stop : Nat
  deriving Inhabited

namespace Sl

@[inline] def size (s : Sl) : Nat := s.stop - s.start
@[inline] def get (s : Sl) (i : Nat) : UInt8 := s.data.get! (s.start + i)

def toString (s : Sl) : String := String.fromUTF8! (s.data.extract s.start s.stop)

instance : ToString Sl := ⟨Sl.toString⟩

/-- Byte-wise equality with an ASCII string. -/
def eqStr (s : Sl) (t : String) : Bool := Id.run do
  if t.utf8ByteSize != s.size then return false
  for i in [0:s.size] do
    if h : (⟨i⟩ : String.Pos.Raw) < t.rawEndPos then
      if t.getUTF8Byte ⟨i⟩ h != s.get i then return false
    else return false
  return true

@[inline] def isDash (s : Sl) : Bool := s.size == 1 && s.get 0 == 45

def drop (s : Sl) (n : Nat) : Sl := { s with start := min (s.start + n) s.stop }

/-- Splits at every byte `c`. -/
def split (s : Sl) (c : UInt8) : Array Sl := Id.run do
  let mut out := #[]
  let mut a := s.start
  for i in [s.start:s.stop] do
    if s.data.get! i == c then
      out := out.push { s with start := a, stop := i }
      a := i + 1
  out.push { s with start := a }

/-- Splits at the first byte `c`, if any. -/
def split2 (s : Sl) (c : UInt8) : Option (Sl × Sl) := Id.run do
  for i in [s.start:s.stop] do
    if s.data.get! i == c then
      return some ({ s with stop := i }, { s with start := i + 1 })
  return none

end Sl

/-! ## Lexer -/

/-- Splits `data` into lines (byte ranges, without the `\n`). The file must end with `\n`. -/
def lines (data : ByteArray) : Except String (Array (Nat × Nat)) := do
  let mut out := #[]
  let mut start := 0
  for h : i in [0:data.size] do
    if data[i] == 10 then
      out := out.push (start, i)
      start := i + 1
  if start != data.size then throw "file does not end with a newline"
  return out

private def hexVal (b : UInt8) : Option UInt8 :=
  if 48 ≤ b && b ≤ 57 then some (b - 48)
  else if 97 ≤ b && b ≤ 102 then some (b - 87)
  else none

/-- End of the word starting at `i` (at the next space or `stop`); words are printable ASCII. -/
def scanWord (data : ByteArray) (i stop : Nat) : Except String Nat := do
  let mut j := i
  for _ in [i:stop] do
    let b := data.get! j
    if b == 32 then break
    if b < 0x21 || b > 0x7e then throw "non-printable byte"
    j := j + 1
  if j == i then throw "empty token (double space?)"
  return j

/-- Decodes the string token starting with `"` at `i`; returns it and the index after the
closing quote. -/
def scanString (data : ByteArray) (i stop : Nat) : Except String (GoStr × Nat) := do
  let mut s := ByteArray.empty
  let mut j := i + 1
  -- fuel: every iteration consumes at least one byte
  for _ in [i+1:stop] do
    if j ≥ stop then break
    let b := data.get! j
    if b == 34 then return (⟨s⟩, j + 1)
    else if b == 92 then
      if j + 1 ≥ stop then throw "dangling escape"
      let c := data.get! (j + 1)
      if c == 34 || c == 92 then
        s := s.push c
        j := j + 2
      else if c == 120 && j + 3 < stop then
        match hexVal (data.get! (j + 2)), hexVal (data.get! (j + 3)) with
        | some h, some l =>
          let v := h * 16 + l
          if 0x20 ≤ v && v ≤ 0x7e && v != 34 && v != 92 then throw "non-canonical escape"
          s := s.push v
          j := j + 4
        | _, _ => throw "bad \\x escape"
      else throw "bad escape"
    else if 0x20 ≤ b && b ≤ 0x7e then
      s := s.push b
      j := j + 1
    else throw "unescaped byte in string"
  throw "unterminated string"

/-! ## Word parsers -/

/-- Decimal natural number, canonical (no sign, no leading zeros). -/
def natW (s : Sl) : Except String Nat := do
  if s.size == 0 || (s.size > 1 && s.get 0 == 48) then throw s!"expected a natural number, got {s}"
  let mut n := 0
  for i in [0:s.size] do
    let b := s.get i
    if b < 48 || b > 57 then throw s!"expected a natural number, got {s}"
    n := n * 10 + (b - 48).toNat
  return n

/-- Decimal integer, canonical (no `+`, no `-0`). -/
def intW (s : Sl) : Except String Int := do
  if s.size > 0 && s.get 0 == 45 then
    let n ← natW (s.drop 1)
    if n == 0 then throw s!"non-canonical number {s}"
    return -(n : Int)
  else return (← natW s)

def int64W (s : Sl) : Except String Int64 := do
  let n ← intW s
  if -2^63 ≤ n && n < 2^63 then pure (Int64.ofInt n) else throw s!"int64 out of range: {s}"

/-- `<c><n>`, e.g. `v12`. -/
def refW (c : Char) (s : Sl) : Except String Nat :=
  if s.size > 0 && s.get 0 == c.toUInt8 then natW (s.drop 1) else throw s!"expected {c}<n>, got {s}"

/-- `<c><n>` or `-`. -/
def optRefW (c : Char) (s : Sl) : Except String (Option Nat) :=
  if s.isDash then pure none else some <$> refW c s

/-- An integer or `?`. -/
def optIntW (s : Sl) : Except String (Option Int) :=
  if s.size == 1 && s.get 0 == 63 then pure none else some <$> intW s

/-- `0` or `1`. -/
def boolW (s : Sl) : Except String Bool :=
  if s.eqStr "0" then pure false else if s.eqStr "1" then pure true
  else throw s!"expected 0/1, got {s}"

/-- Comma list, `-` for empty. -/
def listW {α} (p : Sl → Except String α) (s : Sl) : Except String (Array α) :=
  if s.isDash then pure #[] else (s.split 44).mapM p

/-- Splits `s` at byte `sep` into exactly `n` parts. -/
def partsW (s : Sl) (sep : Char) (n : Nat) : Except String (Array Sl) :=
  let ps := s.split sep.toUInt8
  if ps.size == n then pure ps else throw s!"expected {n} parts separated by {sep} in {s}"

/-- A flag set as a comma list in table order, `-` for none. -/
def flagsW {α} [Inhabited α] (table : List (String × (α → Bool) × (α → α))) (s : Sl) :
    Except String α := do
  if s.isDash then return default
  let mut f : α := default
  let mut rest := table
  for n in s.split 44 do
    match rest.dropWhile (fun e => !n.eqStr e.1) with
    | (_, _, set) :: more =>
      f := set f
      rest := more
    | [] => throw s!"unknown or out-of-order flag {n} in {s}"
  return f

/-- `p<index>:<line>:<col>:<stmt>:<xlogue>`. -/
def posW (s : Sl) : Except String Pos := do
  let ps ← partsW s ':' 5
  return ⟨← refW 'p' ps[0]!, ← natW ps[1]!, ← natW ps[2]!, ← natW ps[3]!, ← natW ps[4]!⟩

/-- `b<ID>:<i>`. -/
def edgeW (s : Sl) : Except String Edge := do
  let ps ← partsW s ':' 2
  return ⟨← refW 'b' ps[0]!, ← natW ps[1]!⟩

/-- Inline slot `a<name>/t<type>/<off>/<splitof s|->/<splitoffset>`. -/
def slotKeyW (s : Sl) : Except String SlotKey := do
  let ps ← partsW s '/' 5
  return ⟨← refW 'a' ps[0]!, ← refW 't' ps[1]!, ← intW ps[2]!, ← optRefW 's' ps[3]!,
    ← intW ps[4]!⟩

/-- Lower-case hex bytes, `-` for none. -/
def hexW (s : Sl) : Except String (Option ByteArray) := do
  if s.isDash then return none
  if s.size % 2 != 0 then throw s!"odd hex length"
  let mut out := ByteArray.empty
  for i in [0:s.size/2] do
    match hexVal (s.get (2*i)), hexVal (s.get (2*i+1)) with
    | some h, some l => out := out.push (h * 16 + l)
    | _, _ => throw s!"bad hex {s}"
  return some out

/-! ## Line parsers -/

/-- The line being parsed: tokens are read from the state (byte index of the next token) up to
`stop`. -/
structure LineCtx where
  data : ByteArray
  stop : Nat

/-- Parser over the tokens of one line. -/
abbrev F := ReaderT LineCtx (EStateM String Nat)

/-- Lifts an `Except` into any `EStateM String`-based parser. -/
@[inline] def liftE {m α} [Monad m] [MonadExceptOf String m] (e : Except String α) : m α :=
  match e with
  | .ok a => pure a
  | .error m => throw m

/-- Moves past the separator after a token that ends at `j`. -/
@[inline] def endTok (j : Nat) : F Unit := fun c => do
  if j < c.stop then
    if c.data.get! j != 32 then throw "missing space after token"
    if j + 1 == c.stop then throw "trailing space"
    set (j + 1)
  else set c.stop

def word : F Sl := fun c => do
  let i ← get
  if i ≥ c.stop then throw "missing token"
  if c.data.get! i == 34 then throw "expected a word, got a string"
  let j ← liftE (scanWord c.data i c.stop)
  endTok j c
  return ⟨c.data, i, j⟩

def wordStr : F String := do return (← word).toString

def str : F GoStr := fun c => do
  let i ← get
  if i ≥ c.stop then throw "missing token"
  if c.data.get! i != 34 then throw "expected a string"
  let (s, j) ← liftE (scanString c.data i c.stop)
  endTok j c
  return s

/-- A word parsed with `p`. -/
@[inline] def w {α} (p : Sl → Except String α) : F α := do liftE (p (← word))

/-- The remaining tokens. -/
def rest : F (Array Token) := fun c => do
  let mut out := #[]
  for _ in [(← get):c.stop] do
    let i ← get
    if i ≥ c.stop then break
    if c.data.get! i == 34 then out := out.push (.str (← str c))
    else out := out.push (.word (← word c).toString)
  return out

/-! ## Records -/

/-- Lookup of op names. -/
def opTable : Std.HashMap ByteArray Op :=
  Op.all.foldl (fun m o => m.insert o.name.toUTF8 o) {}

def opW (s : Sl) : Except String Op :=
  match opTable[s.data.extract s.start s.stop]? with
  | some o => pure o
  | none => throw s!"unknown op {s}"

def blockKindW (s : Sl) : Except String BlockKind :=
  match BlockKind.all.find? (s.eqStr ·.name) with
  | some k => pure k
  | none => throw s!"unknown block kind {s}"

def fieldLine (i : Nat) : F Field := do
  let j ← w natW
  if i != j then throw s!"field {j} where {i} expected"
  return ⟨← str, ← w (refW 't'), ← w optIntW, ← w boolW⟩

/-- `type t<n> …` up to the tail; returns the number of `field` lines that follow. -/
def typeLine : F (TypeRef × TypeDef × Nat) := do
  let n ← w (refW 't')
  let kind ← w fun s => match TypeKind.all.find? (s.eqStr ·.name) with
    | some k => pure k
    | none => throw s!"unknown type kind {s}"
  let size ← w optIntW
  let align ← w optIntW
  let ptrdata ← w optIntW
  let flags ← w (flagsW TypeFlags.table)
  let s ← str
  let symName ← str
  let (tail, nf) ← match kind with
    | .PTR | .SLICE => do pure (TypeTail.elem (← w (refW 't')), 0)
    | .ARRAY => do pure (TypeTail.array (← w (refW 't')) (← w intW), 0)
    | .STRUCT => do let k ← w natW; pure (TypeTail.struct #[], k)
    | .FUNC => do
      let r ← w natW; let p ← w natW; let q ← w natW
      pure (TypeTail.func r p q #[], r + p + q)
    | .TUPLE => do pure (TypeTail.tuple (← w (refW 't')) (← w (refW 't')), 0)
    | .RESULTS => do
      let k ← w natW
      let ts ← w (listW (refW 't'))
      if ts.size != k then throw "RESULTS count mismatch"
      pure (TypeTail.results ts, 0)
    | _ => pure (TypeTail.none, 0)
  return (n, ⟨kind, size, align, ptrdata, flags, s, symName, tail⟩, nf)

def relocLine : F Reloc := do
  return ⟨← w intW, ← w intW, ← wordStr, ← w intW, ← str, ← w intW⟩

def rtypeLine : F RType := do
  return ⟨← w optIntW, ← w optIntW, ← w optIntW, ← w optIntW, ← str, ← str⟩

def abiParamLine : F ABIParam := do
  let dir ← wordStr
  let out ← if dir == "in" then pure false else if dir == "out" then pure true
    else throw s!"expected in/out, got {dir}"
  return ⟨out, ← w natW, ← w (refW 't'), ← w (optRefW 'a'), ← w (listW natW), ← w intW⟩

/-- What an `aux` line still needs from the following lines. -/
inductive AuxMore where
  | none
  /-- `sym`: `nrelocs` reloc lines, then an `rtype` line if `typeinfo` is set. -/
  | sym (nrelocs : Nat) (rtype : Bool)
  /-- `call` with ABI data: `nin + nout` abiparam lines. -/
  | call (n : Nat)

def auxLine : F (AuxRef × AuxDef × AuxMore) := do
  let n ← w (refW 'a')
  let tag ← wordStr
  let fmt ← str
  let (k, more) ← match tag with
    | "name" => do
      let k := AuxKind.name (← str) (← w fun s => match NameClass.all.find? (s.eqStr ·.name) with
          | some c => pure c
          | none => throw s!"unknown class {s}")
        (← w (refW 't')) (← w intW) (← w natW) (← w (flagsW NameFlags.table)) (← w posW)
      pure (k, AuxMore.none)
    | "sym" => do
      let name ← str; let abi ← w natW; let kind ← wordStr; let size ← w intW
      let flags ← w (flagsW SymFlags.table)
      let ti ← w (optRefW 't'); let ii ← w (optRefW 't')
      let data ← w hexW; let nr ← w natW
      pure (AuxKind.sym name abi kind size flags ti ii data #[] none, AuxMore.sym nr ti.isSome)
    | "str" => do pure (AuxKind.str (← str) (← str), AuxMore.none)
    | "call" => do
      let fn ← w (optRefW 'a')
      let abi ← word
      if abi.isDash then
        for _ in [0:6] do
          if !(← word).eqStr "0" then throw "call without ABI info must have zero fields"
        pure (AuxKind.call fn none, AuxMore.none)
      else
        let abi ← match natW abi with | .ok a => pure a | .error e => throw e
        let nin ← w natW; let nout ← w natW
        let c : CallABI := ⟨abi, nin, nout, ← w intW, ← w intW, ← w intW, ← w intW, #[]⟩
        pure (AuxKind.call fn (some c), AuxMore.call (nin + nout))
    | "nameoff" => do pure (AuxKind.nameOff (← w (refW 'a')) (← w intW), AuxMore.none)
    | "type" => do pure (AuxKind.type (← w (refW 't')), AuxMore.none)
    | "int" => do pure (AuxKind.int (← w intW), AuxMore.none)
    | "mark" => pure (AuxKind.mark, AuxMore.none)
    | "pbc" => do pure (AuxKind.pbc (← w intW), AuxMore.none)
    | "pbcc" => do pure (AuxKind.pbcc (← w intW) (← w intW), AuxMore.none)
    | "unknown" => do pure (AuxKind.unknown (← str), AuxMore.none)
    | t => throw s!"unknown aux tag {t}"
  return (n, ⟨fmt, k⟩, more)

def slotLine : F (SlotRef × SlotDef) := do
  return (← w (refW 's'), ⟨← w (refW 'a'), ← w (refW 't'), ← w intW, ← w (optRefW 's'), ← w intW⟩)

def posBaseLine : F (Nat × PosBase) := do
  return (← w (refW 'p'), ⟨← str, ← w intW, ← w intW, ← w intW⟩)

def valueLine (block : ID) : F Value := do
  let id ← w (refW 'v')
  let op ← w opW
  let t ← w (refW 't')
  let auxInt ← w int64W
  let aux ← w (optRefW 'a')
  let pos ← w posW
  let uses ← w natW
  let args ← w (listW (refW 'v'))
  return ⟨id, op, t, auxInt, aux, pos, uses, args, block⟩

/-- A `b` line; `values` is filled in from the following `v` lines. -/
def blockLine : F Block := do
  let id ← w (refW 'b')
  let kind ← w blockKindW
  let pos ← w posW
  let lk ← w fun s => do
    match BranchPrediction.ofInt? (← intW s) with
    | some l => pure l
    | none => throw s!"bad likely {s}"
  let auxInt ← w int64W
  let aux ← w (optRefW 'a')
  let controls ← w (listW (refW 'v'))
  let succs ← w (listW edgeW)
  let preds ← w (listW edgeW)
  return ⟨id, kind, pos, lk, auxInt, aux, controls, succs, preds, #[]⟩

/-- `consts` payload: `<key>=<v,…>` entries joined by commas (`-` for none). -/
def constsW (s : Sl) : Except String (Array (Int64 × Array ID)) := do
  if s.isDash then return #[]
  let mut out : Array (Int64 × Array ID) := #[]
  for part in s.split 44 do
    match part.split2 61 with
    | some (k, v) => out := out.push (← int64W k, #[← refW 'v' v])
    | none =>
      let some (k, vs) := out.back? | throw s!"bad consts {s}"
      out := out.pop.push (k, vs.push (← refW 'v' part))
  return out

def splitEntryW (s : Sl) : Except String (SplitKey × SlotRef) := do
  let kv ← partsW s '=' 2
  let ps ← partsW kv[0]! '/' 3
  return (⟨← refW 's' ps[0]!, ← intW ps[1]!, ← refW 't' ps[2]!⟩, ← refW 's' kv[1]!)

def canonEntryW (s : Sl) : Except String (SlotKey × SlotRef) := do
  let kv ← partsW s '=' 2
  return (← slotKeyW kv[0]!, ← refW 's' kv[1]!)


def sdomNodeW (s : Sl) : Except String (ID × SdomNode) := do
  let ps ← partsW s ':' 6
  return (← refW 'b' ps[0]!, ⟨← optRefW 'b' ps[1]!, ← optRefW 'b' ps[2]!, ← optRefW 'b' ps[3]!,
    ← intW ps[4]!, ← intW ps[5]!⟩)

def idomEntryW (s : Sl) : Except String (ID × Option ID) := do
  let ps ← partsW s ':' 2
  return (← refW 'b' ps[0]!, ← optRefW 'b' ps[1]!)

/-- A per-block cache (`idom`, `sdom`) as an array indexed by block ID (size `n`); its entries
must name the blocks of `f.Blocks`, in order. -/
def byBlockW {α} [Inhabited α] (blocks : Array ID) (n : Nat) (es : Array (ID × α)) :
    Except String (Array α) := do
  if es.map (·.1) != blocks then throw "cache entries do not list f.Blocks in order"
  return es.foldl (fun a (b, x) => a.set! b x) (Array.replicate n default)

def auxmapEntryW (s : Sl) : Except String (Option AuxRef × Int) := do
  let ps ← partsW s ':' 2
  return (← optRefW 'a' ps[0]!, ← intW ps[1]!)

def lineRangeW (s : Sl) : Except String LineRange := do
  let ps := s.split 58
  let index ← natW ps[0]!
  if ps.size == 2 && ps[1]!.isDash then return ⟨index, none, #[]⟩
  if ps.size < 3 then throw s!"bad linestarts entry {s}"
  let pending ← (ps.extract 3 ps.size).mapM fun p => do
    let kv ← partsW p '=' 2
    return (← intW kv[0]!, ← intW kv[1]!)
  return ⟨index, some (← intW ps[1]!, ← intW ps[2]!), pending⟩

/-! ## File structure -/

structure Input where
  data : ByteArray
  lines : Array (Nat × Nat)

/-- Parser over lines; the state is the index of the next line. -/
abbrev L := ReaderT Input (EStateM String Nat)

def lineNo : L Nat := get

/-- Tag (first word) of the next line, if any. -/
def peekTagSl : L (Option Sl) := fun inp => do
  let i ← get
  match inp.lines[i]? with
  | none => pure none
  | some (a, b) =>
    let mut j := a
    for _ in [a:b] do
      if inp.data.get! j == 32 then break
      j := j + 1
    pure (some ⟨inp.data, a, j⟩)

/-- Whether the next line has tag `t`. -/
def tagIs (t : String) : L Bool := do
  match ← peekTagSl with
  | some s => pure (s.eqStr t)
  | none => pure false

def peekTag : L (Option String) := do return (← peekTagSl).map (·.toString)

/-- Parses the next line, which must have tag `tag`, with `p` on the remaining tokens. -/
def line {α} (tag : String) (p : F α) : L α := fun inp => do
  let i ← get
  let some (a, b) := inp.lines[i]? | throw s!"line {i+1}: expected {tag}, got end of file"
  let r : Except String α := do
    if a == b then throw "empty line"
    let j ← scanWord inp.data a b
    let t : Sl := ⟨inp.data, a, j⟩
    if !t.eqStr tag then throw s!"expected {tag}, got {t}"
    let c : LineCtx := ⟨inp.data, b⟩
    match (do endTok j; let x ← p; pure x : F α) c |>.run j with
    | .ok x k => if k != b then throw "unexpected trailing token(s)" else pure x
    | .error e _ => throw e
  match r with
  | .ok x => set (i + 1); pure x
  | .error e => throw s!"line {i+1}: {e}"

def defs : L (Array Def) := do
  let mut out := #[]
  -- fuel: each iteration consumes at least one line
  for _ in [0:(← read).lines.size] do
    match ← peekTag with
    | some "posbase" =>
      let (i, b) ← line "posbase" posBaseLine
      out := out.push (.posBase i b)
    | some "type" =>
      let (n, d, nf) ← line "type" typeLine
      let mut fs := #[]
      for i in [0:nf] do
        fs := fs.push (← line "field" (fieldLine i))
      let tail := match d.tail with
        | .struct _ => .struct fs
        | .func r p q _ => .func r p q fs
        | t => t
      out := out.push (.type n { d with tail })
    | some "aux" =>
      let (n, d, more) ← line "aux" auxLine
      let kind ← match more, d.kind with
        | .sym nr hasR, .sym name abi kind size flags ti ii data _ _ => do
          let mut rs := #[]
          for _ in [0:nr] do
            rs := rs.push (← line "reloc" relocLine)
          let rt ← if hasR then some <$> line "rtype" rtypeLine else pure none
          pure (AuxKind.sym name abi kind size flags ti ii data rs rt)
        | .call np, .call fn (some c) => do
          let mut ps := #[]
          for _ in [0:np] do
            ps := ps.push (← line "abiparam" abiParamLine)
          pure (AuxKind.call fn (some { c with params := ps }))
        | _, k => pure k
      out := out.push (.aux n { d with kind })
    | some "slot" =>
      let (n, s) ← line "slot" slotLine
      out := out.push (.slot n s)
    | _ => break
  return out

def typsEntryW (s : Sl) : Except String (String × TypeRef) := do
  let kv ← partsW s '=' 2
  return (kv[0]!.toString, ← refW 't' kv[1]!)

def func : L (Func × Option (Array (String × TypeRef))) := do
  let (entry, type, ownAux, vidLast, bidLast) ← line "f" do
    return (← w (refW 'b'), ← w (refW 't'), ← w (optRefW 'a'), ← w natW, ← w natW)
  let typs ← if (← tagIs "typs") then some <$> line "typs" (w (listW typsEntryW))
    else pure none
  let mut blocks := #[]
  let mut blockTab : Array (Option Block) := Array.replicate (bidLast + 1) none
  let mut valueTab : Array (Option Value) := Array.replicate (vidLast + 1) none
  for _ in [0:(← read).lines.size] do
    if !(← tagIs "b") then break
    let b ← line "b" blockLine
    let mut vs := #[]
    for _ in [0:(← read).lines.size] do
      if !(← tagIs "v") then break
      let v ← line "v" (valueLine b.id)
      if v.id > vidLast then throw s!"line {← get}: value ID beyond vid.last"
      if valueTab[v.id]!.isSome then throw s!"line {← get}: duplicate value ID"
      valueTab := valueTab.set! v.id (some v)
      vs := vs.push v.id
    blocks := blocks.push b.id
    if b.id > bidLast then throw s!"block ID b{b.id} beyond bid.last"
    if blockTab[b.id]!.isSome then throw s!"duplicate block ID b{b.id}"
    blockTab := blockTab.set! b.id (some { b with values := vs })
  let names ← line "names" (w (listW (refW 's')))
  let mut named := #[]
  for s in names do
    let (s', vs) ← line "named" do return (← w (refW 's'), ← w (listW (refW 'v')))
    if s != s' then throw s!"named s{s'} where s{s} expected"
    named := named.push (s, vs)
  let mut namedx := #[]
  for _ in [0:(← read).lines.size] do
    if !(← tagIs "namedx") then break
    namedx := namedx.push (← line "namedx" do return (← w slotKeyW, ← w (listW (refW 'v'))))
  let splits ← line "splits" (w (listW splitEntryW))
  let canon ← line "canon" (w (listW canonEntryW))
  let consts ← line "consts" (w constsW)
  let freeValues ← line "freev" (w (listW (refW 'v')))
  let freeBlocks ← line "freeb" (w (listW (refW 'b')))
  let mut cache : Caches := {}
  -- cache lines in the order postorder, idom, sdom, loopnest, auxmap, linestarts
  let mut rank := 0
  for _ in [0:(← read).lines.size] do
    if !(← tagIs "cache") then break
    let (r, c) ← line "cache" do
      match ← wordStr with
      | "postorder" => return (1, { cache with postorder := some (← w (listW (refW 'b'))) })
      | "idom" =>
        let es ← w (listW idomEntryW)
        return (2, { cache with idom := some (← liftE (byBlockW blocks (bidLast + 1) es)) })
      | "sdom" =>
        let es ← w (listW sdomNodeW)
        return (3, { cache with sdom := some (← liftE (byBlockW blocks (bidLast + 1) es)) })
      | "loopnest" => return (4, { cache with loopnest := true })
      | "auxmap" => return (5, { cache with auxmap := some (← w (listW auxmapEntryW)) })
      | "linestarts" => return (6, { cache with lineStarts := some (← w (listW lineRangeW)) })
      | c => throw s!"unknown cache {c}"
    if r ≤ rank then throw s!"line {(← get)}: cache line out of order"
    rank := r
    cache := c
  let f : Func :=
    { entry := entry, type := type, ownAux := ownAux, vidLast := vidLast, bidLast := bidLast
      blocks := blocks, blockTab := blockTab, valueTab := valueTab, names := named
      namedx := namedx, splits := splits, canon := canon, consts := consts
      freeValues := freeValues.toList, freeBlocks := freeBlocks.toList, cache := cache }
  return (f, typs)

def sectionP : L Section := do
  let (index, pass) ← line "pass" do return (← w natW, ← str)
  let defs ← defs
  let (func, typs) ← func
  let zvar ← if ← tagIs "zvar" then
      line "zvar" (w (listW fun e => do
        let some (a, b) := e.split2 58 | throw s!"bad zvar entry {e}"
        return (← refW 'v' a, ← natW b)))
    else pure #[]
  let mut warns := #[]
  for _ in [0:(← read).lines.size] do
    if !(← tagIs "warn") then break
    warns := warns.push (← line "warn" str)
  line "end" (pure ())
  return { index, pass, defs, func, typs, zvar, warns }

def file : L ExportFile := do
  let version ← line "gofv-ssa" (w natW)
  let pkg ← line "pkg" str
  let (name, abi, nosplit, pgohot) ← line "func" do
    return (← str, ← w natW, ← w boolW, ← w boolW)
  let mut config := #[]
  for _ in [0:(← read).lines.size] do
    if !(← tagIs "config") then break
    config := config.push (← line "config" do return (← wordStr, ← rest))
  let mut sections := #[]
  for _ in [0:(← read).lines.size] do
    if !(← tagIs "pass") then break
    sections := sections.push (← sectionP)
  line "frontend" (pure ())
  let frontend ← defs
  line "end" (pure ())
  let mut warns := #[]
  for _ in [0:(← read).lines.size] do
    if !(← tagIs "warn") then break
    warns := warns.push (← line "warn" str)
  let ptrCache ← line "ptrcache" (w (listW (refW 't')))
  let mut typeCmp := #[]
  for _ in [0:(← read).lines.size] do
    if !(← tagIs "typecmp") then break
    typeCmp := typeCmp.push (← line "typecmp" do
      let a ← w (refW 't')
      let b ← w (refW 't')
      let o ← match ← wordStr with
        | "lt" => pure Ordering.lt
        | "eq" => pure Ordering.eq
        | "gt" => pure Ordering.gt
        | x => throw s!"expected lt|eq|gt, got {x}"
      return (a, b, o))
  let typeOrder ← line "typeorder" (w (listW fun g => (g.split 61).mapM (refW 't')))
  line "eof" (pure ())
  if (← get) != (← read).lines.size then throw s!"line {(← get) + 1}: data after eof"
  return { version, pkg, name, abi, nosplit, pgohot, config, sections, frontend, warns, ptrCache,
           typeCmp, typeOrder }

end Parse

/-- Parses a `gofv-ssa` file. -/
def parseExport (data : ByteArray) : Except String ExportFile := do
  let ls ← Parse.lines data
  match (Parse.file ⟨data, ls⟩).run 0 with
  | .ok f _ => pure f
  | .error e _ => throw e

end GoFV.SSA
