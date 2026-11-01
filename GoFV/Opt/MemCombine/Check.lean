import GoFV.Opt.MemCombine
import GoFV.Opt.MemCombine.Sym
import GoFV.Opt.KnownBitsCheck
import GoFV.Opt.TabsAgree

/-!
# memcombine's checker (issue #35)

`mcOK tabs f g` accepts `g` as a result of `memcombine` on `f` (in the result's tables `tabs`):

- the blocks, their kinds, successors, controls and IDs are `f`'s, each listing `f`'s values
  first (`KnownBits.blocksOK`); both functions are closed (`RewriteCheck.closedOK`);
- atoms (`mcAtomsOK`): every atom of `g` is an atom of `f` with the same fields, or a `Store`
  of `f` that became another `Store` (a combined store); an atom of `f` that is no atom of `g`
  is droppable (`RewriteCheck.dropAtom`) or a `Store` (a store memcombine clobbered); each block
  evaluates the roots both functions share in the same order (`Sem.schedule`), and only
  `Store`s of `f` are no roots of `g`;
- the values `R` that atom arguments and controls reach through terms in `g` (`reachOK`
  checks the marks are closed) are, when listed in `f`, unchanged or a combined load (`rootOK`:
  an `Or` that became a `Copy` with the same symbolic bytes, `symOf`), and otherwise new
  terms; unchanged atoms keep their arguments;
- a combined store (`storeOK`) writes, at the lowest pointer of the chain of stores it replaces,
  the bytes they wrote (`symOf` of their values, contiguous and disjoint), from values whose
  opaque parts are defined whenever any stored value is.

`memcombineChecked` runs the pass with `loadSource := false` and returns its result if it
changed and `mcOK` (with `tabsAgree`) accepts it, else the input.
-/

namespace GoFV.Opt.MemCombine.Check

open GoFV.SSA GoFV.Opt.RewriteCheck

/-- The fields of `u` and `w` the semantics reads are equal. -/
def sameVal (u w : Value) : Bool :=
  u.id == w.id && u.op == w.op && u.type == w.type && u.auxInt == w.auxInt && u.aux == w.aux &&
    u.args == w.args && u.block == w.block

/-- An atom of `f` and of `g` with the same fields but possibly other arguments. -/
def sameAtom (u w : Value) : Bool :=
  u.op == w.op && u.type == w.type && u.auxInt == w.auxInt && u.aux == w.aux &&
    u.args.size == w.args.size && u.block == w.block && u.id == w.id

/-- A store of `f` combined into another store of `g`. -/
def changedStore (u w : Value) : Bool :=
  u.op == .Store && w.op == .Store && u.type == w.type && u.args.size == 3 &&
    w.args.size == 3 && u.block == w.block && u.id == w.id

/-- `x` is a root of `h`. -/
def rootB (h : Func) (x : ID) : Bool := (h.value? x).any (Sem.isRoot ·.op)

/-- **The atoms** (see the module doc). -/
def mcAtomsOK (f g : Func) : Bool :=
  f.entry == g.entry && f.blocks == g.blocks && f.ownAux == g.ownAux &&
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      fb.id == gb.id &&
      let af := atomsOf f fb
      let ag := atomsOf g gb
      ag.all (fun x => af.contains x && match f.value? x, g.value? x with
        | some u, some w => sameAtom u w || changedStore u w
        | _, _ => false) &&
      af.all (fun x => ag.contains x || (f.value? x).any fun u => dropAtom u.op || u.op == .Store) &&
      match Sem.schedule f fb, Sem.schedule g gb with
      | some of, some og =>
        of.toList.filter (fun x => rootB f x && rootB g x) == og.toList.filter (rootB g) &&
          of.toList.all fun x => !rootB f x || rootB g x || (f.value? x).any (·.op == .Store)
      | _, _ => false
    | _, _ => false

/-- The marks `R` of `g`: every control and every argument of a listed atom is marked, and so
is every argument of a marked listed term. -/
def reachOK (g : Func) (R : Array Bool) : Bool :=
  let m (x : ID) : Bool := R.getD x false
  g.blocks.all fun b =>
    match g.block? b with
    | some gb =>
      gb.controls.all m &&
      gb.values.all fun x => match listedD g x with
        | some v => (termOp v.op && !m x) || v.args.all m
        | none => true
    | none => true

/-- Marks of the values the atoms' arguments and the controls of `g` reach through terms. -/
def reachMarks (g : Func) : Array Bool := Id.run do
  let mut R := Array.replicate g.valueTab.size false
  let mut st : Array ID := #[]
  for b in g.blocks do
    match g.block? b with
    | some gb =>
      st := st ++ gb.controls
      for x in gb.values do
        match listedD g x with
        | some v => if !termOp v.op then st := st ++ v.args
        | none => pure ()
    | none => pure ()
  for _ in [0:g.valueTab.size + 1] do
    if st.isEmpty then break
    let mut next : Array ID := #[]
    for x in st do
      if !R.getD x false then
        R := R.set! x true
        match listedD g x with
        | some v => if termOp v.op then next := next ++ v.args
        | none => pure ()
    st := next
  return R

/-- The IDs a description reads are listed in `f`. -/
def leavesListed (f : Func) (bs : List SB) : Bool :=
  bs.all fun s => s.ids.all fun a => (listedD f a).isSome

/-- Source fuel of `symOf` (an `Or` tree of eight loads is 10 deep). -/
def srcFuel : Nat := 16

/-- Target fuel of `symOf` (`Copy (Lsh (ZeroExt (Bswap (Load …))))`). -/
def tgtFuel : Nat := 8

/-- The load `t` of the target reads through a pointer a load of the source `sf` reads through
(with the same memory and split), and loads of the source from the same memory and base, at
offsets from `t`'s on, cover each of its bytes. -/
def coveredOK (sf : List LoadRec) (t : LoadRec) : Bool :=
  sf.any (fun s => s.ptr == t.ptr && s.mem == t.mem && s.base == t.base && s.idx == t.idx &&
    s.off == t.off) &&
  (List.range t.size).all fun k => sf.any fun s =>
    s.mem == t.mem && s.base == t.base && s.idx == t.idx && decide (t.off ≤ s.off) &&
      decide (s.off ≤ t.off + k) && decide (t.off + k < s.off + s.size)

/-- **A combined load**: the `Or` `u` of `f` became the `Copy` `w` of `g` with the same bytes;
every load of `g` it goes through is covered by loads of `f` (`coveredOK`). -/
def rootOK (tabs : Tables) (f g : Func) (x : ID) (u w : Value) : Bool :=
  (orW u.op).isSome && w.op == .Copy && w.args.size == 1 && w.type == u.type &&
  match symOf tabs (listedD f) true srcFuel x, symOf tabs (listedD g) true tgtFuel x with
  | some (bs, sf), some (bt, sg) => bs == bt && sg.all (coveredOK sf) && leavesListed f bt
  | _, _ => false

/-- The chain of `Store`s from `x` down to (excluding) the memory `m0`. -/
def chainTo (D : Defs) (m0 : ID) : Nat → ID → Option (List ID)
  | 0, _ => none
  | n + 1, x =>
    if x == m0 then some []
    else match D x with
      | some v =>
        if v.op == .Store && v.args.size == 3 then (chainTo D m0 n v.args[2]!).map (x :: ·)
        else none
      | none => none

/-- The bytes a `Store` of `f` writes: its value's description at its type's shape, which is
an integer shape of the value's width, or `bool` for a `ConstBool`. -/
def storedBytes (tabs : Tables) (f : Func) (s : Value) : Option (List SB) :=
  let D := listedD f
  let x := s.args[1]!
  match D x with
  | some xv =>
    match Sem.auxTy tabs s.aux, tabs.ty xv.type with
    | .int w, .int w' =>
      if w = w' then
        match symOf tabs D false srcFuel x with
        | some (bs, []) => if bs.length = w.bytes then some bs else none
        | _ => none
      else none
    | .bool, .bool =>
      if xv.op == .ConstBool && xv.args.size == 0 then
        some [.lit (if xv.auxInt != 0 then 1 else 0)]
      else none
    | _, _ => none
  | none => none

/-- The opaque values of a description. -/
def vbIds (bs : List SB) : List ID := bs.filterMap SB.vbId?

/-- **A combined store**: `u` (with the chain of clobbered stores below it down to `w`'s
memory) became `w`. Each store of the chain writes its bytes at `base + idx + off`; the
offsets relative to `w`'s pointer (a pointer of the chain) tile `[0, W)`; `w`'s value has those
bytes at those places, reads no memory, and its opaque values are opaque values of every
stored value. -/
def storeOK (tabs : Tables) (f g : Func) (x : ID) (u w : Value) : Bool :=
  let Df := listedD f
  let Dg := listedD g
  match chainTo Df w.args[2]! 9 x with
  | none => false
  | some S =>
    2 ≤ S.length && S.all (fun s => (Df s).any (·.block == u.block)) &&
    let (b0, i0, _) := splitP tabs Df 64 w.args[0]! none 0
    ptrTyped tabs Df b0 &&
    match S.mapM (fun s => (Df s).bind fun sv =>
        let (b, i, o) := splitP tabs Df 64 sv.args[0]! none 0
        if b == b0 && i == i0 then (storedBytes tabs f sv).map (sv.args[0]!, o, ·) else none) with
    | none => false
    | some recs =>
      match recs.find? (·.1 == w.args[0]!) with
      | none => false
      | some (_, o0, _) =>
        match Sem.auxTy tabs w.aux, Dg w.args[1]! with
        | .int ww, some xv =>
          intW (tabs.ty xv.type) == some ww &&
          match symOf tabs Dg false tgtFuel w.args[1]! with
          | some (bt, []) =>
            bt.length == ww.bytes && bt.all (!·.isMb) && leavesListed f bt &&
            (recs.map (·.2.2.length)).sum == ww.bytes &&
            recs.all (fun (_, o, bs) =>
              decide (o0 ≤ o) && decide ((o - o0).toNat + bs.length ≤ ww.bytes) &&
              (List.range bs.length).all (fun k => bt[(o - o0).toNat + k]? == bs[k]?) &&
              (vbIds bt).all (vbIds bs).contains) &&
            -- disjoint: no byte is written twice
            (List.range ww.bytes).all fun k =>
              (recs.filter fun (_, o, bs) =>
                decide (o0 + k ≥ o) && decide (o0 + k < o + bs.length)).length ≤ 1
          | _ => false
        | _, _ => false

/-- Value `x` (see the module doc). -/
def valOK (tabs : Tables) (f g : Func) (R : Array Bool) (x : ID) : Bool :=
  match listedD g x with
  | none => true
  | some w =>
    match listedD f x with
    | some u =>
      if termOp w.op then !R.getD x false || sameVal u w || rootOK tabs f g x u w
      else sameVal u w || (changedStore u w && storeOK tabs f g x u w)
    | none => termOp w.op

/-- **The checker.** -/
def mcOK (tabs : Tables) (f g : Func) : Bool :=
  mcAtomsOK f g && closedOK f && closedOK g && KnownBits.blocksOK f g &&
  let R := reachMarks g
  reachOK g R && (List.range g.valueTab.size).all (valOK tabs f g R)

end GoFV.Opt.MemCombine.Check

namespace GoFV.Opt

open GoFV.SSA GoFV.Opt.MemCombine

/-- **memcombine, validated**: the pass without store-of-load combining; its result if it
changed and the checker accepts it (in the result's tables, which the input cannot tell from
its own, `tabsAgree`), else the input. -/
def memcombineChecked : Pass := fun env f => do
  let (c, u) ← memcombineCfg env
  let (g, tabs) ← memcombine { c with loadSource := false } u env.tables f
  if g != f && tabsAgree env.tables tabs f && Check.mcOK tabs f g then
    return { func := g, tables := tabs }
  else return { func := f, tables := env.tables }

end GoFV.Opt
