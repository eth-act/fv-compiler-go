import GoFV.Opt.MemCombine
import GoFV.Opt.MemCombine.Sym
import GoFV.Opt.KnownBitsCheck
import GoFV.Opt.TabsAgree

/-!
# memcombine's checker (issue #35)

`mcOK tabs f g` accepts `g` as a result of `memcombine` on `f` (in the result's tables `tabs`):

- atoms (`mcAtomsOK`): every atom of `g` is an atom of `f` with the same fields but the
  arguments and, for a `Store`, the aux (a combined store); each block evaluates the roots both
  functions have in the same order (`Sem.schedule`), and a root of `f` that is no root of `g`
  is a `Store` (memcombine clobbers the narrow stores it combines); the blocks, their kinds,
  successors, controls and IDs are `f`'s, each listing `f`'s values first
  (`KnownBits.blocksOK`); both functions are closed (`RewriteCheck.closedOK`);
- the values `R` that atom arguments and controls reach through terms in `g` (`reachMarks`;
  `reachOK` checks the marks are closed) are, when listed in `f`, unchanged (`sameVal`) or a
  combined load (`rootOK`: an `Or` that became a `Copy` with the same symbolic bytes, `symOf`,
  whose loads are covered by the source's), and otherwise new terms; an atom is unchanged or a
  combined store (`storeOK`): the `Store` `x` of `f` heads a chain of `Store`s of `f` down to
  the target's memory argument, each writing the bytes of its value (`storedBytes`: a
  description without memory bytes, or a `ConstBool`) at `base + idx + off` of one base and
  index (`splitP`); the offsets, from the target's pointer (a pointer of the chain), tile the
  target's width; the target's value has those bytes (`symOf`) and reads no memory, and every
  value it reads is read by each stored value (so if one stored value is an integer, the
  target's value is defined).

`memcombineChecked` runs the pass and returns its result if it changed and `mcOK` (with
`tabsAgree`: a combined store's aux may be a new type) accepts it, else the input.
-/

namespace GoFV.Opt.MemCombine.Check

open GoFV.SSA GoFV.Opt.RewriteCheck

/-- The fields of `u` and `w` the semantics reads are equal. -/
def sameVal (u w : Value) : Bool :=
  u.id == w.id && u.op == w.op && u.type == w.type && u.auxInt == w.auxInt && u.aux == w.aux &&
    u.args == w.args && u.block == w.block

/-- `x` is a root of `h` (`GoFV.Proof.AtomSim.rootP`). -/
def rootB (h : Func) (x : ID) : Bool := (h.value? x).any (Sem.isRoot ·.op)

/-- The atom `w` of `g` has the fields of the atom `u` of `f` but the arguments and, for a
`Store`, the aux. -/
def atomFieldsOK (u w : Value) : Bool :=
  u.op == w.op && u.type == w.type && u.auxInt == w.auxInt && (u.aux == w.aux || u.op == .Store) &&
    u.args.size == w.args.size && u.block == w.block && u.id == w.id

/-- **The atoms** (see the module doc). -/
def mcAtomsOK (f g : Func) : Bool :=
  f.entry == g.entry && f.blocks == g.blocks && f.ownAux == g.ownAux &&
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      fb.id == gb.id &&
      (atomsOf g gb).all (fun x => (atomsOf f fb).contains x && match f.value? x, g.value? x with
        | some u, some w => atomFieldsOK u w
        | _, _ => false) &&
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

/-- The values a load of a description reads: pointer, memory, base and index. -/
def LoadRec.ids (r : LoadRec) : List ID := [r.ptr, r.mem, r.base] ++ r.idx.toList

/-- The IDs a description reads, and those of its loads, are marked in `M` (the values the
proof relates: reached in `g`, listed in both functions). -/
def leavesIn (M : Array Bool) (bs : List SB) (sg : List LoadRec) : Bool :=
  bs.all (fun s => s.ids.all (M.getD · false)) && sg.all fun r => r.ids.all (M.getD · false)

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

/-- **A combined load**: the `Or` `u` of `f` became the `Copy` `w` of `g` with the same bytes,
which do not read `x` itself and are marked in `M`; every load of `g` it goes through is
covered by loads of `f` (`coveredOK`). -/
def rootOK (tabs : Tables) (f g : Func) (M : Array Bool) (x : ID) (u w : Value) : Bool :=
  (orW u.op).isSome && w.op == .Copy && w.args.size == 1 && w.type == u.type &&
  match symOf tabs f.value? false srcFuel x, symOf tabs (listedD g) true tgtFuel x with
  | some (bs, sf), some (bt, sg) =>
    bs == bt && bs.all (·.vbId? != some x) && sg.all (coveredOK sf) && leavesIn M bt sg
  | _, _ => false

/-- The `Store`s of a chain from `x` down to (excluding) the memory `m0`, last first. -/
def chainTo (D : Defs) (m0 : ID) : Nat → ID → Option (List ID)
  | 0, _ => none
  | n + 1, x =>
    if x == m0 then some []
    else match D x with
      | some v =>
        if v.op == .Store && v.args.size == 3 then (chainTo D m0 n v.args[2]!).map (x :: ·)
        else none
      | none => none

/-- The bytes the `Store` `s` writes: its value's description (with the loads it reads) at an
integer shape narrower than 8 bytes (the store's aux type's and the value's), or the byte of a
`ConstBool` at the `bool` shape. -/
def storedBytes (tabs : Tables) (D : Defs) (s : Value) : Option Desc :=
  let x := s.args[1]!
  match D x with
  | some xv =>
    match Sem.auxTy tabs s.aux, tabs.ty xv.type with
    | .int w, .int w' =>
      if w = w' ∧ w.bytes < 8 then
        match symOf tabs D false srcFuel x with
        | some r => if r.1.length = w.bytes then some r else none
        | none => none
      else none
    | .bool, .bool =>
      if xv.op == .ConstBool && xv.args.size == 0 then
        some ([.lit (if xv.auxInt != 0 then 1 else 0)], [])
      else none
    | _, _ => none
  | none => none

/-- The opaque values of a description. -/
def vbIds (bs : List SB) : List ID := bs.filterMap SB.vbId?

/-- An opaque byte `vb y k` names a byte of `y`'s integer shape in `E`. -/
def vbWidthOK (tabs : Tables) (E : Defs) : SB → Bool
  | .vb y k => match E y with
    | some v => (intW (tabs.ty v.type)).any (k < ·.bytes)
    | none => false
  | _ => true

/-- A store of a chain: its pointer, the pointer split (`splitP`) and its bytes. -/
abbrev StoreRec := ID × (ID × Option ID × Int) × Desc

/-- The records of the stores `S`. -/
def storeRecs (tabs : Tables) (D : Defs) (S : List ID) : Option (List StoreRec) :=
  S.mapM fun s => (D s).bind fun sv =>
    if sv.args.size == 3 then
      (storedBytes tabs D sv).map fun r => (sv.args[0]!, splitP tabs D 64 sv.args[0]! none 0, r)
    else none

/-- The records `recs` tile `[0, W)` from offset `o0`, and the description `(bt, sg)` has their
bytes at their places and reads only values (and loads) each of them reads. -/
def tileOK (recs : List StoreRec) (o0 : Int) (W : Nat) (bt : List SB) (sg : List LoadRec) : Bool :=
  recs.all (fun (_, (_, _, o), (bs, sf)) =>
    decide (o0 ≤ o) && decide ((o - o0).toNat + bs.length ≤ W) &&
    (List.range bs.length).all (fun k => bt[(o - o0).toNat + k]? == bs[k]?) &&
    (vbIds bt).all (vbIds bs).contains && sg.all (coveredOK sf)) &&
  (List.range W).all fun k =>
    (recs.filter fun (_, (_, _, o), (bs, _)) =>
      decide (o ≤ o0 + k) && decide (o0 + k < o + bs.length)).length == 1

/-- **A combined store** (see the module doc): the `Store` `u` of `f` with ID `x` became the
`Store` `w` of `g`. -/
def storeOK (tabs : Tables) (f g : Func) (M : Array Bool) (x : ID) (u w : Value) : Bool :=
  u.op == .Store && w.op == .Store && u.args.size == 3 && w.args.size == 3 &&
  let D := f.value?
  let m0 := w.args[2]!
  let pw := w.args[0]!
  M.getD m0 false && M.getD pw false &&
  match chainTo D m0 9 x with
  | none => false
  | some S =>
    2 ≤ S.length &&
    match storeRecs tabs D S with
    | none => false
    | some recs =>
      match recs.find? (·.1 == pw) with
      | none => false
      | some (_, (b0, i0, o0), _) =>
        ptrTyped tabs D b0 && recs.all (fun r => r.2.1.1 == b0 && r.2.1.2.1 == i0) &&
        match Sem.auxTy tabs w.aux, listedD g w.args[1]! with
        | .int ww, some sv =>
          intW (tabs.ty sv.type) == some ww &&
          match symOf tabs (listedD g) true tgtFuel w.args[1]! with
          | some (bt, sg) =>
            bt.length == ww.bytes && bt.all (vbWidthOK tabs (listedD g)) &&
              leavesIn M bt sg && tileOK recs o0 ww.bytes bt sg
          | _ => false
        | _, _ => false

/-- Value `x` (see the module doc). -/
def valOK (tabs : Tables) (f g : Func) (R M : Array Bool) (x : ID) : Bool :=
  match listedD g x with
  | none => true
  | some w =>
    match listedD f x with
    | some u =>
      if termOp w.op then !R.getD x false || sameVal u w || rootOK tabs f g M x u w
      else sameVal u w || storeOK tabs f g M x u w
    | none => termOp w.op

/-- The values the proof relates: reached in `g`, listed in both functions. -/
def relMarks (f g : Func) (R : Array Bool) : Array Bool :=
  let Lf := listedMarks f
  let Lg := listedMarks g
  (List.range g.valueTab.size).toArray.map fun x =>
    R.getD x false && Lf[x]? == some true && Lg[x]? == some true

/-- **The checker.** -/
def mcOK (tabs : Tables) (f g : Func) : Bool :=
  mcAtomsOK f g && closedOK f && closedOK g && KnownBits.blocksOK f g &&
  let R := reachMarks g
  reachOK g R && (List.range g.valueTab.size).all (valOK tabs f g R (relMarks f g R))

end GoFV.Opt.MemCombine.Check

namespace GoFV.Opt

open GoFV.SSA GoFV.Opt.MemCombine

/-- **memcombine, validated**: its result if it changed and the checker accepts it (in the
result's tables, which the input cannot tell from its own, `tabsAgree`), else the input. -/
def memcombineChecked : Pass := fun env f => do
  let (c, u) ← memcombineCfg env
  let (g, tabs) ← memcombine c u env.tables f
  if g != f && tabsAgree env.tables tabs f && Check.mcOK tabs f g then
    return { func := g, tables := tabs }
  else return { func := f, tables := env.tables }

end GoFV.Opt
