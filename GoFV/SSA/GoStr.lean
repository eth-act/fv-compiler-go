/-!
# Go byte strings

Go strings are byte sequences that need not be valid UTF-8 (symbol names, string constants), so
the IR keeps them as bytes. The export format writes them quoted with Go-independent escapes
(`docs/contracts/export.md`, "Lexical format"): bytes 0x20–0x7e except `"` and `\` literally,
`"` as `\"`, `\` as `\\`, every other byte as `\xHH` (lower-case hex).
-/

namespace GoFV.SSA

/-- A Go string: a sequence of bytes. -/
structure GoStr where
  bytes : ByteArray
  deriving DecidableEq, Hashable, Inhabited

namespace GoStr

/-- The UTF-8 bytes of a Lean string (e.g. a symbol name a pass compares with). -/
def ofString (s : String) : GoStr := ⟨s.toUTF8⟩

instance : Coe String GoStr := ⟨ofString⟩

def size (s : GoStr) : Nat := s.bytes.size

instance : Append GoStr := ⟨fun a b => ⟨a.bytes ++ b.bytes⟩⟩

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Appends the quoted, escaped form of `s` to `out`. -/
def quoteInto (out : String) (s : GoStr) : String := Id.run do
  let mut out := out.push '"'
  for b in s.bytes do
    if b == 0x22 then out := out ++ "\\\""
    else if b == 0x5c then out := out ++ "\\\\"
    else if 0x20 ≤ b && b ≤ 0x7e then out := out.push (Char.ofNat b.toNat)
    else out := ((out ++ "\\x").push (hexDigit (b >>> 4))).push (hexDigit (b &&& 15))
  out.push '"'

/-- The quoted, escaped form of `s`. -/
def quote (s : GoStr) : String := quoteInto "" s

/-- `s` as a Lean string, with invalid UTF-8 replaced by its `\xHH` escapes (for messages and
debug output). -/
def toStringLossy (s : GoStr) : String :=
  match String.fromUTF8? s.bytes with
  | some t => t
  | none => (quote s).drop 1 |>.dropEnd 1 |>.toString

instance : ToString GoStr := ⟨toStringLossy⟩
instance : Repr GoStr := ⟨fun s _ => .text (quote s)⟩

end GoStr

end GoFV.SSA
