import GoFV.SSA.Type
import Std.Data.TreeMap

/-!
# `types.(*Type).Compare`

The export lists every type of a file in ascending `Compare` order, grouping `CMPeq` types
(`typeorder`, docs/contracts/export.md). `Compare` is not quite a total preorder (`*byte` is
`CMPeq` `*uint8` by the byte/uint8 special case, but `cmpsym` orders by name length, so
`*abi.Kind` sorts between them, #68), so the export also lists every pair whose `Compare`
disagrees with the ranks (`typecmp`). `Compare` is a rank comparison with those exceptions
(docs/PASSES.md §1.7). Users: `generic cse` (`cmpVal`), the constant cache
(`Compare == CMPeq`), `copyCompatibleType` in the rules.
-/

namespace GoFV.SSA

/-- The lexicographic order on type-number pairs, the key order of `TypeOrder.exceptions` (a
`TreeMap`, which the kernel can evaluate, unlike a `HashMap`). -/
def typePairCmp (a b : TypeRef × TypeRef) : Ordering := (compare a.1 b.1).then (compare a.2 b.2)

/-- The rank of each type number in `typeorder` (`none` for numbers it does not list) and the
`typecmp` exceptions, keyed by `(a, b)` with `a < b`. -/
structure TypeOrder where
  rank : Array (Option Nat)
  exceptions : Std.TreeMap (TypeRef × TypeRef) Ordering typePairCmp := {}
  deriving Inhabited

namespace TypeOrder

/-- Ranks from the export's `typeorder` groups (`ExportFile.typeOrder`) and the `typecmp`
exceptions (`ExportFile.typeCmp`). -/
def ofGroups (groups : Array (Array TypeRef))
    (exceptions : Array (TypeRef × TypeRef × Ordering) := #[]) : TypeOrder :=
  let n := groups.foldl (fun n g => g.foldl (fun n t => max n (t + 1)) n) 0
  let (rank, _) := groups.foldl
    (fun (acc : Array (Option Nat) × Nat) g =>
      (g.foldl (fun r t => r.set! t (some acc.2)) acc.1, acc.2 + 1))
    (Array.replicate n none, 0)
  { rank, exceptions := exceptions.foldl (fun m (a, b, o) => m.insert (a, b) o) {} }

/-- The rank of `t`, if `typeorder` lists it. -/
@[inline] def rank? (o : TypeOrder) (t : TypeRef) : Option Nat := (o.rank[t]?).join

/-- The `typecmp` exception for `t.Compare(u)`, if any. -/
def exception? (o : TypeOrder) (t u : TypeRef) : Option Ordering :=
  if t < u then o.exceptions[(t, u)]? else (o.exceptions[(u, t)]?).map Ordering.swap

/-- `t.Compare(u)` (`CMPlt`/`CMPeq`/`CMPgt` as `Ordering`), `none` if either type is not
ranked. Every type of an export file is ranked, so `none` means the caller passed a number from
another file or one it invented. -/
def compare? (o : TypeOrder) (t u : TypeRef) : Option Ordering := do
  let a ← o.rank? t
  let b ← o.rank? u
  return (o.exception? t u).getD (Ord.compare a b)

/-- `t.Compare(u)`. Two equal numbers are the same type (`CMPeq`); otherwise unranked numbers
sort after every ranked one, by number (never reached on export data, see `compare?`). -/
def compare (o : TypeOrder) (t u : TypeRef) : Ordering :=
  if t = u then .eq else
  match o.rank? t, o.rank? u with
  | some a, some b => (o.exception? t u).getD (Ord.compare a b)
  | some _, none => .lt
  | none, some _ => .gt
  | none, none => Ord.compare t u

/-- `t.Compare(u) == CMPeq`. -/
@[inline] def eq (o : TypeOrder) (t u : TypeRef) : Bool := o.compare t u == .eq

end TypeOrder

end GoFV.SSA
