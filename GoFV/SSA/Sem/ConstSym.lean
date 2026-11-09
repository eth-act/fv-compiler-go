import GoFV.SSA.Sem.Image

variable [GoFV.SSA.Sem.Addrs]

/-!
# The float constant symbols (`docs/plans/proofs3.md` §10)

`progedit` rewrites `FMOVD $c, Fd` (`FMOVS`), when `c` is no `FMOV` immediate and not 0, to a load
of the read-only data symbol `$f64.<bits>` (`$f32.<bits>`) that `ctxt.Float64Sym` makes
(`cmd/internal/obj/sym.go:163-191`; the port's `GoFV.Asm.float64Sym`): its name is the IEEE bits
in lowercase hexadecimal (16 digits, 8 for `$f32.`), its contents those bits little-endian, its
kind `SRODATA`. `constSymAlloc? name` is that allocation, read-only (`roAlloc`), from the name
alone; `constRo names` lists those of the constant symbols among `names`. `asm-parity` compares
the port's constant symbols, bytes included, with Go's (`Cmp.data`).
-/

namespace GoFV.SSA.Sem

/-- The value of `n` lowercase hexadecimal digits (`none` if `s` is not exactly that). -/
def hexDigits? (s : String) (n : Nat) : Option Nat :=
  if s.length != n then none else
  s.foldl (fun acc c => acc.bind fun a =>
    if c.isDigit then some (16 * a + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (16 * a + (c.toNat - 'a'.toNat + 10))
    else none) (some 0)

/-- The `n` little-endian bytes of `x`. -/
def leBytesU8 (x n : Nat) : Array UInt8 :=
  (List.range n).toArray.map fun i => UInt8.ofNat (x / 256 ^ i)

/-- The allocation of a float constant symbol, from its name: the bits' little-endian bytes,
read-only. -/
def constSymAlloc? (name : String) : Option Alloc :=
  if name.startsWith "$f64." then
    (hexDigits? (name.drop 5).toString 16).map fun x => roAlloc (leBytesU8 x 8)
  else if name.startsWith "$f32." then
    (hexDigits? (name.drop 5).toString 8).map fun x => roAlloc (leBytesU8 x 4)
  else none

/-- The float constant symbols among `names`, with their allocations. -/
def constRo (names : List String) : List (String × Alloc) :=
  names.filterMap fun n => (constSymAlloc? n).map (n, ·)

end GoFV.SSA.Sem
