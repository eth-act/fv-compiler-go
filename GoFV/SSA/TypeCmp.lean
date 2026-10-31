import GoFV.SSA.Type

/-!
# `types.(*Type).Compare`

`Compare` is a total preorder on types; the export lists every type of a file in ascending
order, grouping `CMPeq` types (`typeorder`, docs/contracts/export.md). `Compare` is therefore a
rank comparison (docs/PASSES.md §1.7). Users: `generic cse` (`cmpVal`), the constant cache
(`Compare == CMPeq`), `copyCompatibleType` in the rules.
-/

namespace GoFV.SSA

/-- The rank of each type number in `typeorder` (`none` for numbers it does not list). -/
structure TypeOrder where
  rank : Array (Option Nat)
  deriving Inhabited

namespace TypeOrder

/-- Ranks from the export's `typeorder` groups (`ExportFile.typeOrder`). -/
def ofGroups (groups : Array (Array TypeRef)) : TypeOrder :=
  let n := groups.foldl (fun n g => g.foldl (fun n t => max n (t + 1)) n) 0
  let (rank, _) := groups.foldl
    (fun (acc : Array (Option Nat) × Nat) g =>
      (g.foldl (fun r t => r.set! t (some acc.2)) acc.1, acc.2 + 1))
    (Array.replicate n none, 0)
  ⟨rank⟩

/-- The rank of `t`, if `typeorder` lists it. -/
@[inline] def rank? (o : TypeOrder) (t : TypeRef) : Option Nat := (o.rank[t]?).join

/-- `t.Compare(u)` (`CMPlt`/`CMPeq`/`CMPgt` as `Ordering`), `none` if either type is not
ranked. Every type of an export file is ranked, so `none` means the caller passed a number from
another file or one it invented. -/
def compare? (o : TypeOrder) (t u : TypeRef) : Option Ordering := do
  return Ord.compare (← o.rank? t) (← o.rank? u)

/-- `t.Compare(u)`. Two equal numbers are the same type (`CMPeq`); otherwise unranked numbers
sort after every ranked one, by number (never reached on export data, see `compare?`). -/
def compare (o : TypeOrder) (t u : TypeRef) : Ordering :=
  if t = u then .eq else
  match o.rank? t, o.rank? u with
  | some a, some b => Ord.compare a b
  | some _, none => .lt
  | none, some _ => .gt
  | none, none => Ord.compare t u

/-- `t.Compare(u) == CMPeq`. -/
@[inline] def eq (o : TypeOrder) (t u : TypeRef) : Bool := o.compare t u == .eq

end TypeOrder

end GoFV.SSA
