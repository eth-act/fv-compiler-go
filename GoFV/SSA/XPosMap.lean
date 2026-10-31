import GoFV.SSA.Func
import GoFV.Util.SparseMap

/-!
# `xposmap` and `biasedSparseMap`

Port of `cmd/compile/internal/ssa/xposmap.go` and `biasedsparsemap.go` (go1.27.3): a map from
(file index, line) to `int32`, one `biasedSparseMap` per file index over a fixed line range.
`number lines` builds `f.cachedLineStarts` with one map per noted file (`newXposmap`); later
passes (`deadcode`, `applyRewrite`, `nilcheckelim`, …) use it as their `pendingLines` scratch
map (docs/PASSES.md §1.6). Exact behaviour kept: lines outside a file's range are silently
dropped by `set`/`remove`, `set` on an unknown file index is Go's panic (here `Except`), the
entries stay in the sparse map's dense order (insertion order, swap-remove), which the export
records (`cache linestarts`).

The persistent form is `Func.cache.lineStarts : Option (Array LineRange)` (the export's shape);
a pass converts it once with `XPosMap.ofCache` and writes it back with `XPosMap.toCache`.
-/

namespace GoFV.SSA

open GoFV.Util

/-- `biasedSparseMap`: a `sparseMap` over keys `line - first`. `s = none` is Go's `s == nil`
(empty range, `first = MaxInt32`). -/
structure BiasedSparseMap where
  first : Int
  s : Option (SparseMap Int)
  deriving Inhabited

namespace BiasedSparseMap

/-- `math.MaxInt32`. -/
def maxInt32 : Int := 2147483647

/-- `newBiasedSparseMap(first, last)`. -/
def new (first last : Int) : BiasedSparseMap :=
  if first > last then ⟨maxInt32, none⟩ else ⟨first, some (SparseMap.new (1 + last - first).toNat)⟩

/-- `cap()`: one past the last line in range (0 for an empty map). -/
def cap (m : BiasedSparseMap) : Int :=
  match m.s with
  | some s => s.cap + m.first
  | none => 0

/-- `size()`. -/
def size (m : BiasedSparseMap) : Nat :=
  match m.s with
  | some s => s.size
  | none => 0

@[inline] private def key? (m : BiasedSparseMap) (x : Nat) : Option (SparseMap Int × Nat) :=
  match m.s with
  | some s => if (x : Int) < m.first || (x : Int) ≥ m.cap then none else some (s, (x - m.first).toNat)
  | none => none

/-- `contains(x)`. -/
def contains (m : BiasedSparseMap) (x : Nat) : Bool :=
  match m.key? x with
  | some (s, k) => s.contains k
  | none => false

/-- `get(x)`. -/
def get (m : BiasedSparseMap) (x : Nat) : Option Int :=
  match m.key? x with
  | some (s, k) => s.get k
  | none => none

/-- `set(x, v)`: out-of-range lines are dropped. -/
def set (m : BiasedSparseMap) (x : Nat) (v : Int) : BiasedSparseMap :=
  match m.key? x with
  | some (s, k) => { m with s := some (s.set k v) }
  | none => m

/-- `remove(x)`: out-of-range lines are ignored. -/
def remove (m : BiasedSparseMap) (x : Nat) : BiasedSparseMap :=
  match m.key? x with
  | some (s, k) => { m with s := some (s.remove k) }
  | none => m

/-- `clear()`. -/
def clear (m : BiasedSparseMap) : BiasedSparseMap := { m with s := m.s.map SparseMap.clear }

/-- The entries `(line, value)` in dense order (`getEntry(0..size-1)`). -/
def entries (m : BiasedSparseMap) : Array (Int × Int) :=
  match m.s with
  | some s => s.dense.map fun e => ((e.key : Int) + m.first, e.val)
  | none => #[]

end BiasedSparseMap

/-- `xposmap`: one `biasedSparseMap` per file index, ascending by index (Go keeps a Go map; no
pass observes its iteration order, see `entries`). The `lastIndex`/`lastMap` lookup cache is
not state. -/
structure XPosMap where
  maps : Array (Nat × BiasedSparseMap)
  deriving Inhabited

namespace XPosMap

/-- `newXposmap(ranges)`: `ranges` lists `(file index, first line, last line)` with distinct
indices. -/
def new (ranges : Array (Nat × Nat × Nat)) : XPosMap :=
  let rs := ranges.qsort fun a b => a.1 < b.1
  ⟨rs.map fun (i, first, last) => (i, BiasedSparseMap.new first last)⟩

/-- The index of file `i`'s map in `maps`. -/
@[inline] def find? (m : XPosMap) (i : Nat) : Option Nat := m.maps.findIdx? (·.1 == i)

/-- `clear()`. -/
def clear (m : XPosMap) : XPosMap := ⟨m.maps.map fun (i, b) => (i, b.clear)⟩

/-- `set(p, v)`; an unknown file index is Go's panic. -/
def set (m : XPosMap) (p : Pos) (v : Int) : Except String XPosMap :=
  match m.find? p.index with
  | some j => .ok ⟨m.maps.modify j fun (i, b) => (i, b.set p.line v)⟩
  | none => .error s!"xposmap.set({p.index}), file index not found in map"

/-- `add(p)` = `set(p, 0)`. -/
def add (m : XPosMap) (p : Pos) : Except String XPosMap := m.set p 0

/-- `get(p)`. -/
def get (m : XPosMap) (p : Pos) : Option Int :=
  match m.find? p.index with
  | some j => m.maps[j]!.2.get p.line
  | none => none

/-- `contains(p)`. -/
def contains (m : XPosMap) (p : Pos) : Bool :=
  match m.find? p.index with
  | some j => m.maps[j]!.2.contains p.line
  | none => false

/-- `remove(p)`. -/
def remove (m : XPosMap) (p : Pos) : XPosMap :=
  match m.find? p.index with
  | some j => ⟨m.maps.modify j fun (i, b) => (i, b.remove p.line)⟩
  | none => m

/-- `foreachEntry`'s entries `(file index, line, value)`: per file in dense order, files in
ascending index. Go iterates the files in Go-map order, so callers must not depend on the order
across files. -/
def entries (m : XPosMap) : Array (Nat × Int × Int) :=
  m.maps.foldl (fun acc (i, b) => acc ++ b.entries.map fun (l, v) => (i, l, v)) #[]

/-- Rebuild the map from the persistent form (`cache linestarts`): the leftover entries are
re-inserted in dense order, which reproduces it. -/
def ofLineRanges (ls : Array LineRange) : XPosMap :=
  ⟨ls.map fun r =>
    match r.bounds with
    | none => (r.index, ⟨BiasedSparseMap.maxInt32, none⟩)
    | some (first, last) =>
      let b := BiasedSparseMap.new first last
      (r.index, r.pending.foldl (fun b (l, v) => b.set l.toNat v) b)⟩

/-- `f.cachedLineStarts` as a map (`none` when it is nil). -/
def ofCache (c : Option (Array LineRange)) : Option XPosMap := c.map ofLineRanges

/-- The persistent form: per file `index:first:last` (`last = cap - 1`) and the entries. -/
def toCache (m : XPosMap) : Array LineRange :=
  m.maps.map fun (i, b) =>
    match b.s with
    | none => ⟨i, none, #[]⟩
    | some _ => ⟨i, some (b.first, b.cap - 1), b.entries⟩

end XPosMap

end GoFV.SSA
