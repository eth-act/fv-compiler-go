import GoFV.SSA.Live
import GoFV.SSA.FmtFloat

/-!
# Go's `f.String()`

The human-readable SSA dump of `ssa/print.go` (`stringFuncPrinter`, `printDead = true`), with
`Value.LongString` and `Block.LongString` (`value.go`, `block.go`), for debugging and for diffing
against the stock compiler's text (`GOFV_SSA_GOTEXT=1`). Unscheduled order (all passes before
`lower`): phis first, then values in dependency order. Type and aux texts come from the export
(`t.String()`, `fmt.Sprint(aux)`).

Known differences: type spellings through aliases (`byte`, `rune`, `any`) follow the export,
which keeps one spelling per type identity; `%q` of a string aux keeps every non-ASCII rune of
valid UTF-8 as is (Go escapes the non-printable ones as `\u`/`\U`).
-/

namespace GoFV.SSA.GoString

open FmtFloat

/-- Go's `strconv.Quote`, except that every valid non-ASCII rune counts as printable. -/
def quoteGo (s : GoStr) : String := Id.run do
  let hex (v : Nat) : Char := if v < 10 then Char.ofNat (48 + v) else Char.ofNat (87 + v)
  let byteEsc (b : UInt8) : String := "\\x" ++ (hex (b.toNat / 16)).toString ++ (hex (b.toNat % 16)).toString
  let bs := s.bytes
  let mut out := "\""
  let mut i := 0
  for _ in [0:bs.size] do
    if i ≥ bs.size then break
    let b := bs.get! i
    if b < 0x80 then
      out := match b with
        | 0x22 => out ++ "\\\"" | 0x5c => out ++ "\\\\"
        | 0x07 => out ++ "\\a" | 0x08 => out ++ "\\b" | 0x0c => out ++ "\\f"
        | 0x0a => out ++ "\\n" | 0x0d => out ++ "\\r" | 0x09 => out ++ "\\t" | 0x0b => out ++ "\\v"
        | _ => if b < 0x20 || b == 0x7f then out ++ byteEsc b else out.push (Char.ofNat b.toNat)
      i := i + 1
    else
      -- longest valid UTF-8 sequence starting at i
      let n := if b ≥ 0xf0 then 4 else if b ≥ 0xe0 then 3 else 2
      match String.fromUTF8? (bs.extract i (i + n)) with
      | some t => out := out ++ t; i := i + n
      | none => out := out ++ byteEsc b; i := i + 1
  return out.push '"'

structure Ctx where
  tables : Tables
  f : Func
  /-- Rendered `LocalSlot` names of each value (`NamedValues`), sorted. -/
  names : Array (Array String)

def typeStr (c : Ctx) (t : TypeRef) : String :=
  match c.tables.type? t with
  | some d => d.str.toStringLossy
  | none => s!"<t{t}>"

def auxStr (c : Ctx) (a : AuxRef) : String :=
  match c.tables.aux? a with
  | some d => d.fmt.toStringLossy
  | none => s!"<a{a}>"

/-- `LocalSlot.String()`. -/
def slotStr (c : Ctx) (k : SlotKey) : String :=
  let n := auxStr c k.name
  if k.off == 0 then s!"{n}[{typeStr c k.type}]" else s!"{n}+{k.off}[{typeStr c k.type}]"

def slotRefStr (c : Ctx) (s : SlotRef) : String :=
  match c.tables.slot? s with
  | some d => slotStr c d
  | none => s!"<s{s}>"

/-- Signed value of the low `bits` bits of `x`. -/
def sext (x : Int64) (bits : Nat) : Int :=
  let u := x.toInt % (2 ^ bits)
  if u ≥ 2 ^ (bits - 1) then u - 2 ^ bits else u

/-- `Value.auxString()`. -/
def valueAux (c : Ctx) (v : Value) : String :=
  let aux (pre : String) : String := match v.aux with
    | some a => pre ++ "{" ++ auxStr c a ++ "}"
    | none => ""
  match v.op.auxType with
  | .Bool => if v.auxInt == 0 then " [false]" else " [true]"
  | .Int8 => s!" [{sext v.auxInt 8}]"
  | .Int16 => s!" [{sext v.auxInt 16}]"
  | .Int32 => s!" [{sext v.auxInt 32}]"
  | .Int64 | .Int128 => s!" [{v.auxInt}]"
  | .UInt8 => s!" [{v.auxInt.toInt % 256}]"
  | .Float32 | .Float64 => s!" [{fmtG v.auxInt.toUInt64}]"
  | .String => match v.aux.bind c.tables.aux? with
    | some ⟨_, .str s _⟩ => s!" \{{quoteGo s}}"
    | some d => s!" \{{quoteGo d.fmt}}"
    | none => " {%!q(<nil>)}"
  | .Sym | .Call | .Typ => aux " "
  | .SymOff | .CallOff | .TypSize | .NameOffsetInt8 =>
    aux " " ++ (if v.auxInt != 0 || v.op.auxType == .NameOffsetInt8 then s!" [{v.auxInt}]" else "")
  | .SymValAndOff =>
    aux " " ++ s!" [val={sext (v.auxInt >>> 32) 32},off={sext v.auxInt 32}]"
  | .None => ""
  | t => s!"[auxtype={t.ctorIdx} AuxInt={v.auxInt} Aux={(v.aux.map (auxStr c)).getD "<nil>"}]"

/-- `StmtString(v.Pos)`. -/
def stmtString (p : Pos) : String :=
  if p.isKnown then
    let pfx := if p.stmt == 1 then "+" else if p.stmt == 2 then "-" else ""
    s!"({pfx}{p.line}) "
  else "(?) "

/-- `Value.LongString()`. -/
def valueLong (c : Ctx) (v : Value) : String := Id.run do
  let mut s := s!"v{v.id} = {v.op.name} <{typeStr c v.type}>{valueAux c v}"
  for a in v.args do
    s := s ++ s!" v{a}"
  let ns := c.names.getD v.id #[]
  if !ns.isEmpty then
    s := s ++ " (" ++ ", ".intercalate ns.toList ++ ")"
  return s

/-- `Block.LongString()`. -/
def blockLong (c : Ctx) (b : Block) : String := Id.run do
  let mut s := b.kind.name
  if let some a := b.aux then s := s ++ s!" \{{auxStr c a}}"
  if b.kind.auxIntType != "" then s := s ++ s!" [{b.auxInt}]"
  for x in b.controls do
    s := s ++ s!" v{x}"
  if !b.succs.isEmpty then
    s := s ++ " ->"
    for e in b.succs do
      s := s ++ s!" b{e.b}"
  match b.likely with
  | .unlikely => s := s ++ " (unlikely)"
  | .likely => s := s ++ " (likely)"
  | .unknown => pure ()
  return s

/-- `f.String()` for function `name` with the definition tables `t` in force. -/
def funcString (name : GoStr) (t : Tables) (f : Func) : String := Id.run do
  -- names per value: every NamedValues key whose list contains it
  let mut names : Array (Array String) := Array.replicate (f.vidLast + 1) #[]
  let c0 : Ctx := ⟨t, f, #[]⟩
  let keys : Array (String × Array ID) :=
    f.names.map (fun (s, vs) => (slotRefStr c0 s, vs)) ++
    f.namedx.map (fun (k, vs) => (slotStr c0 k, vs))
  -- as `LongString`: one entry per key containing the value (a key listing it twice counts
  -- once), sorted; equal strings of different keys are all kept
  for (k, vs) in keys do
    let mut seen : Array ID := #[]
    for v in vs do
      if seen.contains v then continue
      seen := seen.push v
      if v < names.size then names := names.modify v (·.push k)
  let c : Ctx := { c0 with names := names.map (·.qsort (· < ·)) }
  let reachable := f.reachableBlocks
  let live := f.liveValues t reachable
  let mut out := s!"{name.toStringLossy} {typeStr c f.type}\n"
  let mut printed := Array.replicate (f.vidLast + 1) false
  for bid in f.blocks do
    let some b := f.block? bid | continue
    let reach := reachable.getD bid false
    out := out ++ s!"  b{bid}:"
    if !b.preds.isEmpty then
      out := out ++ " <-"
      for e in b.preds do
        out := out ++ s!" b{e.b}"
    if !reach then out := out ++ " DEAD"
    out := out ++ "\n"
    let vals := b.values.filterMap f.value?
    let emit (out : String) (v : Value) : String :=
      out ++ "    " ++ stmtString v.pos ++ valueLong c v ++
        (if live.getD v.id false then "" else " DEAD") ++ "\n"
    let mut n := 0
    for v in vals do
      if v.op == .Phi then
        out := emit out v
        printed := printed.set! v.id true
        n := n + 1
    for _ in [0:vals.size + 1] do
      if n ≥ vals.size then break
      let m := n
      for v in vals do
        if printed.getD v.id true then continue
        if v.args.any (fun a => (f.value? a).any (·.block == bid) && !printed.getD a true) then
          continue
        out := emit out v
        printed := printed.set! v.id true
        n := n + 1
      if m == n then
        out := out ++ "dependency cycle!\n"
        for v in vals do
          if printed.getD v.id true then continue
          out := emit out v
          printed := printed.set! v.id true
          n := n + 1
    out := out ++ "    " ++ blockLong c b ++ "\n"
  for (s, vs) in f.names do
    out := out ++ s!"name {slotRefStr c s}: [{" ".intercalate (vs.toList.map (s!"v{·}"))}]\n"
  return out

end GoString

/-- `f.String()` of section `k` of an export file. -/
def ExportFile.goString (e : ExportFile) (k : Nat) : String :=
  match e.sections[k]? with
  | some s => GoString.funcString e.name (e.tablesAt k) s.func
  | none => ""

end GoFV.SSA
