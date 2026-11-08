import GoFV.Opt.ExpandCallsCheck
import GoFV.Opt.Decompose

variable [GoFV.SSA.Sem.Addrs]

/-!
# The checker of decompose's phi splitting (`DecPhiCheck.decPhiCheck`, issue #17)

`decomposeUserPhi`/`decomposeBuiltinPhi` (`GoFV/Opt/Decompose/Phi.lean`) turn a `Phi` `v` of a
composite type into `<T>Make` (or, for a zero-sized type, `Empty`) of new component `Phi`s,
whose argument along edge `j` is a new extractor (`StructSelect [i]`, `StringPtr`, …) of `v`'s
argument `j`, placed in that argument's block; `decomposeUserPhi` recurses into the new `Phi`s
(nested `Make`s, extractor-of-extractor arguments).

`decPhiCheck tabs f g` relates the input `f` to the function `g` after the phi stage (both
read in the same tables `tabs`) as the simulation `GoFV.Proof.DecPhi` needs it. Every value of
`g` gets a **meaning** `(s, π)` (`meanOf`): the source value `s` and a path `π` of
(component index, component shape) steps, i.e. "component `π` of `s`". Source values mean
themselves (`(x, [])`); the arguments of a `Make` of meaning `(s, π)` mean `(s, π ++ [(k,
fieldₖ)])`; an extractor of component `k` of a value of meaning `(s, π)` means `(s, π ++ [(k,
t)])`. The checks:

* the same CFG and own aux; per block the same kind and controls, every source value listed in
  the same block, and the same sequence of non-pure nodes in both schedules;
* a source value is unchanged (same op, type, auxint, aux, arguments, block), or a source `Phi`
  became a `Make` whose arguments mean its components (`makeOK`) or, at the zero-sized shape,
  `Empty` (`emptyOK`), same type and block;
* a new value (an ID `f` does not define) has a meaning `(s, π)` with `π ≠ []`, the shape of
  its last step, is listed in the block of `s`, and is an extractor of the prefix's meaning
  (`selOK`), a `Make` or `Empty` as above, or a `Phi` whose argument `j` means `(aⱼ, π)` for
  argument `aⱼ` of the source `Phi` `s` (whose arguments have `s`'s shape; `phiOK`).

Structural recursion and `List` operations only: the checker runs compiled and in the kernel.
-/

namespace GoFV.Opt.DecPhiCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck

/-- A path into a composite: per step the component index and the component's shape. -/
abbrev Path := List (Nat × Ty)

/-- A meaning: component `π` of source value `s`. -/
abbrev Mean := ID × Path

def pathBeq : Path → Path → Bool
  | [], [] => true
  | (k, t) :: p, (k', t') :: p' => k == k' && Ty.beq t t' && pathBeq p p'
  | _, _ => false

/-- The meaning of `z`, if any. -/
@[inline] def meanAt (m : Array (Option Mean)) (z : ID) : Option Mean := (m[z]?).join

/-- `z` means `(s, π)`. -/
def meanIs (m : Array (Option Mean)) (z s : ID) (π : Path) : Bool :=
  match meanAt m z with
  | some (s', π') => s' == s && pathBeq π' π
  | none => false

/-- The shape of a value of meaning `(s, π)`: the last step's, or `s`'s. -/
def meanTy (sh : Array Ty) (f : Func) (s : ID) (π : Path) : Ty :=
  match π.getLast? with
  | some (_, t) => t
  | none => shapeOf sh f s

/-! ## Computing the meanings -/

/-- Give the arguments `as` of a `Make` of meaning `(s, π)` (from field `k` on) their meanings,
unless they have one. -/
def pushArgs (s : ID) (π : Path) : Nat → List (Nat × Ty) → List ID → Array (Option Mean) →
    Array (Option Mean)
  | k, (_, t) :: fs, a :: as, m =>
    pushArgs s π (k + 1) fs as
      (if (meanAt m a).isNone && a < m.size then m.set! a (some (s, π ++ [(k, t)])) else m)
  | _, _, _, m => m

/-- One pass over `g`'s values: `Make`s push meanings to their arguments, extractors of a value
with a meaning get one. -/
def stepMean (sh : Array Ty) (g : Func) (m : Array (Option Mean)) : Array (Option Mean) :=
  g.valueTab.foldl (init := m) fun m o =>
    match o with
    | none => m
    | some w =>
      match meanAt m w.id with
      | some (s, π) =>
        if isMake w.op then
          match (shapeOf sh g w.id).asAgg with
          | .agg fs _ => pushArgs s π 0 fs w.args.toList m
          | _ => m
        else m
      | none =>
        match selIdx? w, w.args.toList with
        | some k, [a] =>
          match meanAt m a with
          | some (s, π) =>
            if w.id < m.size then m.set! w.id (some (s, π ++ [(k, shapeOf sh g w.id)])) else m
          | none => m
        | _, _ => m

def countSome (m : Array (Option Mean)) : Nat := m.foldl (fun n o => if o.isSome then n + 1 else n) 0

/-- Iterate `stepMean` until no new meaning appears. -/
def iterMean (sh : Array Ty) (g : Func) : Nat → Array (Option Mean) → Array (Option Mean)
  | 0, m => m
  | fuel + 1, m =>
    let m' := stepMean sh g m
    if countSome m' == countSome m then m else iterMean sh g fuel m'

/-- The meanings of `g`'s values: source values mean themselves, the rest by propagation. -/
def meanOf (sh : Array Ty) (f g : Func) : Array (Option Mean) :=
  let m0 := (List.range g.valueTab.size).toArray.map fun z =>
    if (f.value? z).isSome then some (z, []) else none
  iterMean sh g (g.valueTab.size + 1) m0

/-! ## Local checks -/

/-- The arguments `as` of a `Make` of meaning `(s, π)` mean its components from `k` on. -/
def argsMeanOK (m : Array (Option Mean)) (s : ID) (π : Path) :
    Nat → List (Nat × Ty) → List ID → Bool
  | k, (_, t) :: fs, a :: as => meanIs m a s (π ++ [(k, t)]) && argsMeanOK m s π (k + 1) fs as
  | _, [], [] => true
  | _, _, _ => false

/-- `w` (meaning `(s, π)`) is a `Make` of its components. -/
def makeOK (sh : Array Ty) (g : Func) (m : Array (Option Mean)) (w : Value) (s : ID)
    (π : Path) : Bool :=
  isMake w.op &&
    match (shapeOf sh g w.id).asAgg with
    | .agg fs _ => argsMeanOK m s π 0 fs w.args.toList
    | _ => false

/-- `w` is `Empty` at the zero-sized shape. -/
def emptyOK (sh : Array Ty) (g : Func) (w : Value) : Bool :=
  w.op == .Empty && w.args.isEmpty && Ty.beq (shapeOf sh g w.id) .empty

/-- `w` (meaning `(s, π)`) extracts the last step of `π` from a value meaning its prefix. -/
def selOK (m : Array (Option Mean)) (w : Value) (s : ID) (π : Path) : Bool :=
  match selIdx? w, w.args.toList, π.getLast? with
  | some k, [a], some (k', _) => k == k' && meanIs m a s π.dropLast
  | _, _, _ => false

/-- `w` (meaning `(s, π)`) is a `Phi` whose argument `j` means component `π` of argument `j` of
the source `Phi` `s`, whose arguments have `s`'s shape. -/
def phiOK (sh : Array Ty) (f : Func) (m : Array (Option Mean)) (w : Value) (s : ID)
    (π : Path) : Bool :=
  w.op == .Phi &&
    match f.value? s with
    | some u => u.op == .Phi && w.args.size == u.args.size &&
        (w.args.toList.zip u.args.toList).all fun (c, a) =>
          meanIs m c a π && Ty.beq (shapeOf sh f a) (shapeOf sh f s)
    | none => false

/-- The checks of a new value `w` of `g`. -/
def newOK (sh : Array Ty) (f g : Func) (m : Array (Option Mean)) (fb : Block) (w : Value) :
    Bool :=
  match meanAt m w.id with
  | some (s, π) =>
    !π.isEmpty && Ty.beq (shapeOf sh g w.id) (meanTy sh f s π) && fb.values.contains s &&
      (selOK m w s π || phiOK sh f m w s π || makeOK sh g m w s π || emptyOK sh g w)
  | none => false

/-- The same value up to position and uses. -/
def sameOK (u w : Value) : Bool :=
  w.op == u.op && w.type == u.type && w.auxInt == u.auxInt && w.aux == u.aux && w.args == u.args

/-- The checks of a source value `u` and its version `w` in `g`. -/
def srcOK (sh : Array Ty) (g : Func) (m : Array (Option Mean)) (u w : Value) : Bool :=
  w.block == u.block && meanIs m u.id u.id [] &&
    (sameOK u w ||
      (u.op == .Phi && w.type == u.type && (makeOK sh g m w u.id [] || emptyOK sh g w)))

/-- The checks of block `bid`. -/
def blockOK (sh : Array Ty) (f g : Func) (m : Array (Option Mean)) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.controls == fb.controls &&
    fb.values.all (fun x => gb.values.contains x) &&
    gb.values.all (fun z => match g.value? z with
      | some w => w.id == z && match f.value? z with
        | some u => fb.values.contains z && srcOK sh g m u w
        | none => newOK sh f g m fb w
      | none => false) &&
    (match schedule f fb, schedule g gb with
      | some of, some og => of.toList.filter (npOf f fb) == og.toList.filter (npOf f fb)
      | _, _ => false)
  | _, _ => false

/-- **The checker**: `g` is `f` after decompose's phi splitting, both read in `tabs`. -/
def decPhiCheck (tabs : Tables) (f g : Func) : Bool :=
  let sh := typeShapes tabs
  let m := meanOf sh f g
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
    f.blocks.all (blockOK sh f g m)

end GoFV.Opt.DecPhiCheck

namespace GoFV.Opt.Decompose

/-- **The phi stage** of "decompose user" (`builtin = false`: `decomposeUserPhi` on every
`Phi`) and of "decompose builtin" (`builtin = true`: `decomposeUser`, then
`decomposeBuiltinPhi` on every `Phi`), without the names, the dec rules and `finish`: the
tables (with the types `ptrTo` adds) and the function `decPhiCheck` reads. -/
def phiStage (env : PassEnv) (builtin : Bool) (f : SSA.Func) :
    Except String (SSA.Tables × SSA.Func) := do
  let c ← ctxOf env
  let m : M Unit := if builtin then do decomposeUser; forEachPhi decomposeBuiltinPhi
    else forEachPhi (decomposeUserPhi typeFuel)
  let s ← runM c m (← ofFunc env.tables f)
  return (s.tabs, s.f)

end GoFV.Opt.Decompose
