import GoFV.SSA.Export

/-!
# Type predicates

`*types.Type` predicates the passes ask of SSA types, over the export's type tables. Go
compares types by pointer; the export numbers `types.TypeMem` & co. once per file (`typs`).
-/

namespace GoFV.SSA

/-- `t.IsMemory()` (`types/type.go`): `t` is `types.TypeMem` (`mem`), a tuple whose second
component is, or a results type whose last component is. -/
def Tables.isMemory (tabs : Tables) (mem : TypeRef) (t : TypeRef) : Bool :=
  t == mem ||
    match (tabs.type? t).map (·.tail) with
    | some (TypeTail.tuple _ s) => s == mem
    | some (TypeTail.results ts) => ts.back? == some mem
    | _ => false

end GoFV.SSA
