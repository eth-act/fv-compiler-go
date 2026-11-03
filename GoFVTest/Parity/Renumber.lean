import GoFV.SSA.Export
import GoFV.SSA.Print
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

/-!
# Matching the objects a pass creates

A pass that creates types, aux objects or local slots numbers them itself (fresh numbers past
the input tables); the export numbers them while writing the output section. `pass-parity`
pairs them up by position in a canonical walk of each function — the function in print order
(`f` line, blocks, values, names, slot maps, `auxmap`), then, breadth first, the references
inside the definitions met (and inside redefined objects) — and renames the Lean side before
comparing. Two isomorphic results give corresponding walks, so a wrong pass shows up as a
definition or function difference after renaming.
-/

namespace GoFVTest.Parity

open GoFV.SSA

/-- References of the three kinds a pass can create. -/
inductive RefKind where
  | t | a | s
  deriving DecidableEq, Hashable

/-- New references in walk order, per kind. -/
structure Walk where
  t : Array Nat := #[]
  a : Array Nat := #[]
  s : Array Nat := #[]
  seen : Std.HashSet (RefKind × Nat) := {}

/-- Renaming maps (Lean number → stock number); unmapped numbers are kept. -/
structure Ren where
  t : Std.HashMap Nat Nat := {}
  a : Std.HashMap Nat Nat := {}
  s : Std.HashMap Nat Nat := {}

namespace Ren
@[inline] def ty (r : Ren) (x : Nat) : Nat := r.t.getD x x
@[inline] def ax (r : Ren) (x : Nat) : Nat := r.a.getD x x
@[inline] def sl (r : Ren) (x : Nat) : Nat := r.s.getD x x

def field (r : Ren) (f : Field) : Field := { f with type := r.ty f.type }

def typeDef (r : Ren) (d : TypeDef) : TypeDef :=
  { d with tail := match d.tail with
    | .none => .none
    | .elem e => .elem (r.ty e)
    | .array e n => .array (r.ty e) n
    | .struct fs => .struct (fs.map r.field)
    | .func a b c fs => .func a b c (fs.map r.field)
    | .tuple x y => .tuple (r.ty x) (r.ty y)
    | .results ts => .results (ts.map r.ty) }

def auxDef (r : Ren) (d : AuxDef) : AuxDef :=
  { d with kind := match d.kind with
    | .name sym cls t off esc fl p => .name sym cls (r.ty t) off esc fl p
    | .sym n abi k sz fl ti ii data rel rt => .sym n abi k sz fl (ti.map r.ty) (ii.map r.ty) data rel rt
    | .call fn abi => .call (fn.map r.ax) (abi.map fun c =>
        { c with params := c.params.map fun p => { p with type := r.ty p.type, name := p.name.map r.ax } })
    | .nameOff n off => .nameOff (r.ax n) off
    | .type t => .type (r.ty t)
    | k => k }

def slotDef (r : Ren) (d : SlotDef) : SlotDef :=
  { d with name := r.ax d.name, type := r.ty d.type, splitOf := d.splitOf.map r.sl }

def func (r : Ren) (f : Func) : Func :=
  { f with
    type := r.ty f.type, ownAux := f.ownAux.map r.ax
    blockTab := f.blockTab.map (·.map fun b => { b with aux := b.aux.map r.ax })
    valueTab := f.valueTab.map (·.map fun v => { v with type := r.ty v.type, aux := v.aux.map r.ax })
    names := f.names.map fun (s, vs) => (r.sl s, vs)
    namedx := f.namedx.map fun (k, vs) => (r.slotDef k, vs)
    splits := f.splits.map fun (k, s) =>
      ({ k with parent := r.sl k.parent, type := r.ty k.type }, r.sl s)
    canon := f.canon.map fun (k, s) => (r.slotDef k, r.sl s)
    cache := { f.cache with auxmap := f.cache.auxmap.map (·.map fun (a, n) => (a.map r.ax, n)) }
    low := { f.low with regAlloc := f.low.regAlloc.map fun (n, es) => (n, es.map fun (v, l) =>
      (v, match l with | .slot k => .slot (r.slotDef k) | l => l)) } }
end Ren

/-- The references of a function in print order. -/
def funcRefs (f : Func) : Array (RefKind × Nat) := Id.run do
  let mut out : Array (RefKind × Nat) := #[(.t, f.type)]
  if let some a := f.ownAux then out := out.push (.a, a)
  let slotKey (out : Array (RefKind × Nat)) (k : SlotDef) :=
    let out := (out.push (.a, k.name)).push (.t, k.type)
    match k.splitOf with | some s => out.push (.s, s) | none => out
  for bid in f.blocks do
    let some b := f.block? bid | continue
    if let some a := b.aux then out := out.push (.a, a)
    for vid in b.values do
      let some v := f.value? vid | continue
      out := out.push (.t, v.type)
      if let some a := v.aux then out := out.push (.a, a)
  for (s, _) in f.names do out := out.push (.s, s)
  for (k, _) in f.namedx do out := slotKey out k
  for (k, s) in f.splits do out := ((out.push (.s, k.parent)).push (.t, k.type)).push (.s, s)
  for (k, s) in f.canon do out := (slotKey out k).push (.s, s)
  if let some m := f.cache.auxmap then
    for (a, _) in m do
      if let some a := a then out := out.push (.a, a)
  if let some (_, es) := f.low.regAlloc then
    for (_, l) in es do
      if let .slot k := l then out := slotKey out k
  return out

/-- The references inside a definition. With `symNameOnly`, a symbol's references (its
`typeinfo`/`itabinfo` types) are not followed: only its name and ABI are compared. -/
def defRefs (tabs : Tables) (symNameOnly : Bool := false) : RefKind × Nat → Array (RefKind × Nat)
  | (.t, n) => match tabs.type? n with
    | none => #[]
    | some d => match d.tail with
      | .none => #[]
      | .elem e | .array e _ => #[(.t, e)]
      | .struct fs | .func _ _ _ fs => fs.map fun f => (.t, f.type)
      | .tuple x y => #[(.t, x), (.t, y)]
      | .results ts => ts.map (.t, ·)
  | (.a, n) => match tabs.aux? n with
    | none => #[]
    | some d => match d.kind with
      | .name _ _ t _ _ _ _ => #[(.t, t)]
      | .sym _ _ _ _ _ ti ii _ _ _ =>
        if symNameOnly then #[] else (ti.toArray.map (.t, ·)) ++ ii.toArray.map (.t, ·)
      | .call fn abi =>
        (fn.toArray.map (.a, ·)) ++ ((abi.map (·.params)).getD #[]).flatMap fun p =>
          #[(.t, p.type)] ++ p.name.toArray.map (.a, ·)
      | .nameOff x _ => #[(.a, x)]
      | .type t => #[(.t, t)]
      | _ => #[]
  | (.s, n) => match tabs.slot? n with
    | none => #[]
    | some d => #[(.a, d.name), (.t, d.type)] ++ d.splitOf.toArray.map (.s, ·)

def isDefined (tabs : Tables) : RefKind × Nat → Bool
  | (.t, n) => (tabs.type? n).isSome
  | (.a, n) => (tabs.aux? n).isSome
  | (.s, n) => (tabs.slot? n).isSome

/-- The references of `f` that are not defined in `input`, in walk order: the function, then
breadth first through the definitions (in `out`) of the new references and of `seeds`. -/
def newRefs (input out : Tables) (f : Func) (seeds : Array (RefKind × Nat))
    (symNameOnly : Bool := false) : Walk := Id.run do
  let mut w : Walk := {}
  let mut queue : Array (RefKind × Nat) := #[]
  let visit (w : Walk) (q : Array (RefKind × Nat)) (r : RefKind × Nat) :
      Walk × Array (RefKind × Nat) :=
    if isDefined input r || w.seen.contains r then (w, q) else
    let w := { w with seen := w.seen.insert r }
    let w := match r.1 with
      | .t => { w with t := w.t.push r.2 }
      | .a => { w with a := w.a.push r.2 }
      | .s => { w with s := w.s.push r.2 }
    (w, q.push r)
  for r in funcRefs f do (w, queue) := visit w queue r
  queue := seeds ++ queue
  let mut i := 0
  -- each reference enters the queue at most once, plus the seeds
  for _ in [0:seeds.size + (out.types.size + out.auxes.size + out.slots.size) + 1] do
    let some r := queue[i]? | break
    i := i + 1
    for x in defRefs out symNameOnly r do (w, queue) := visit w queue x
  return w

/-- Pair the Lean pass's new objects with the stock output's and rename the Lean function;
an error describes the first definition that does not correspond. With `symNameOnly`, a new
symbol on both sides only needs the same name and ABI (the driver's importer: a new symbol is
the frontend's, its contents are not the pass's). -/
def renumber (input leanT stockT : Tables) (leanF stockF : Func) (symNameOnly : Bool := false) :
    Except String Func := do
  -- objects that existed before and were redefined, on either side
  let mut seeds : Array (RefKind × Nat) := #[]
  for i in [0:input.types.size] do
    if (input.type? i).isSome && (leanT.type? i != input.type? i || stockT.type? i != input.type? i) then
      seeds := seeds.push (.t, i)
  for i in [0:input.auxes.size] do
    if (input.aux? i).isSome && (leanT.aux? i != input.aux? i || stockT.aux? i != input.aux? i) then
      seeds := seeds.push (.a, i)
  for i in [0:input.slots.size] do
    if (input.slot? i).isSome && (leanT.slot? i != input.slot? i || stockT.slot? i != input.slot? i) then
      seeds := seeds.push (.s, i)
  let wl := newRefs input leanT leanF seeds symNameOnly
  let ws := newRefs input stockT stockF seeds symNameOnly
  if wl.t.size != ws.t.size || wl.a.size != ws.a.size || wl.s.size != ws.s.size then
    throw s!"new objects: lean {wl.t.size} types, {wl.a.size} aux, {wl.s.size} slots; \
      stock {ws.t.size}, {ws.a.size}, {ws.s.size}"
  let zipMap (xs ys : Array Nat) : Std.HashMap Nat Nat :=
    (xs.zip ys).foldl (fun m (x, y) => m.insert x y) {}
  let r : Ren := { t := zipMap wl.t ws.t, a := zipMap wl.a ws.a, s := zipMap wl.s ws.s }
  let showD (d : Option Def) : String := match d with
    | some d => (Print.defn d |>.run "").2.trimAsciiEnd.toString
    | none => "(undefined)"
  for (x, y) in wl.t.zip ws.t do
    if (leanT.type? x).map r.typeDef != stockT.type? y then
      throw s!"new type t{y} (lean t{x}) differs from the stock definition\n    stock: \
        {showD ((stockT.type? y).map (.type y))}\n    lean:  {showD ((leanT.type? x).map (.type y ∘ r.typeDef))}"
  let sameSym (x y : Option AuxDef) : Bool := match x, y with
    | some { kind := .sym n abi .., .. }, some { kind := .sym n' abi' .., .. } => n == n' && abi == abi'
    | _, _ => false
  for (x, y) in wl.a.zip ws.a do
    if (leanT.aux? x).map r.auxDef != stockT.aux? y &&
        !(symNameOnly && sameSym (leanT.aux? x) (stockT.aux? y)) then
      throw s!"new aux a{y} (lean a{x}) differs from the stock definition\n    stock: \
        {showD ((stockT.aux? y).map (.aux y))}\n    lean:  {showD ((leanT.aux? x).map (.aux y ∘ r.auxDef))}"
  for (x, y) in wl.s.zip ws.s do
    if (leanT.slot? x).map r.slotDef != stockT.slot? y then
      throw s!"new slot s{y} (lean s{x}) differs from the stock definition\n    stock: \
        {showD ((stockT.slot? y).map (.slot y))}\n    lean:  {showD ((leanT.slot? x).map (.slot y ∘ r.slotDef))}"
  for (k, i) in seeds do
    let ok := match k with
      | .t => (leanT.type? i).map r.typeDef == stockT.type? i
      | .a => (leanT.aux? i).map r.auxDef == stockT.aux? i
      | .s => (leanT.slot? i).map r.slotDef == stockT.slot? i
    if !ok then
      let tag := match k with | .t => "t" | .a => "a" | .s => "s"
      throw s!"redefined {tag}{i} differs from the stock output section"
  return r.func leanF

/-- Self-check of `renumber` on stock data: section `k`'s function and definitions with every
object new in section `k` moved to a fresh number past all tables, i.e. what a correct pass
that numbers its new objects differently would return. `renumber` must map it back. -/
def shuffledStock (input : Tables) (s : Section) : Func × Tables := Id.run do
  let off := input.types.size + input.auxes.size + input.slots.size + 1000
  let mut r : Ren := {}
  for d in s.defs do
    match d with
    | .type n _ => if (input.type? n).isNone then r := { r with t := r.t.insert n (n + off) }
    | .aux n _ => if (input.aux? n).isNone then r := { r with a := r.a.insert n (n + off) }
    | .slot n _ => if (input.slot? n).isNone then r := { r with s := r.s.insert n (n + off) }
    | .posBase .. => pure ()
  let defs := s.defs.map fun
    | .type n d => .type (r.ty n) (r.typeDef d)
    | .aux n d => .aux (r.ax n) (r.auxDef d)
    | .slot n d => .slot (r.sl n) (r.slotDef d)
    | d => d
  return (r.func s.func, input.addAll defs)

end GoFVTest.Parity
