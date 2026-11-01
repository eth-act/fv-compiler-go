import GoFV.Opt.MemCombine
import GoFV.Opt.MemCombine.Sym
import GoFV.Opt.KnownBitsCheck

/-!
# memcombine's checker (issue #35)

`mcOK tabs f g` accepts `g` as a result of `memcombineLoads` on `f`:

- `f` and `g` have the same atoms with the same fields and roots in the same order
  (`RewriteCheck.atomsOK`); the blocks, their kinds, successors, controls and IDs are `f`'s,
  each listing `f`'s values first (`KnownBits.blocksOK`); both functions are closed
  (`RewriteCheck.closedOK`);
- the values `R` that atom arguments and controls reach through terms in `g` (`reachMarks`;
  `reachOK` checks the marks are closed) are, when listed in `f`, unchanged (`sameVal`) or a
  combined load (`rootOK`: an `Or` that became a `Copy` with the same symbolic bytes, `symOf`,
  whose loads are covered by the source's), and otherwise new terms; atoms are unchanged.

`memcombineChecked` runs the pass on loads only (`Cfg.stores := false`) and returns its result
if it changed and `mcOK` accepts it, else the input. Combined loads build no type, so the
tables stay the input's.
-/

namespace GoFV.Opt.MemCombine.Check

open GoFV.SSA GoFV.Opt.RewriteCheck

/-- The fields of `u` and `w` the semantics reads are equal. -/
def sameVal (u w : Value) : Bool :=
  u.id == w.id && u.op == w.op && u.type == w.type && u.auxInt == w.auxInt && u.aux == w.aux &&
    u.args == w.args && u.block == w.block

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

/-- The IDs a description reads, and the pointers of its loads, are marked in `M` (the values
the proof relates: reached in `g`, listed in both functions). -/
def leavesIn (M : Array Bool) (bs : List SB) (sg : List LoadRec) : Bool :=
  bs.all (fun s => s.ids.all (M.getD · false)) && sg.all fun r => M.getD r.ptr false

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
  match symOf tabs f.value? true srcFuel x, symOf tabs (listedD g) true tgtFuel x with
  | some (bs, sf), some (bt, sg) =>
    bs == bt && bs.all (·.vbId? != some x) && sg.all (coveredOK sf) && leavesIn M bt sg
  | _, _ => false

/-- Value `x` (see the module doc). -/
def valOK (tabs : Tables) (f g : Func) (R M : Array Bool) (x : ID) : Bool :=
  match listedD g x with
  | none => true
  | some w =>
    match listedD f x with
    | some u =>
      if termOp w.op then !R.getD x false || sameVal u w || rootOK tabs f g M x u w
      else sameVal u w
    | none => termOp w.op

/-- **The checker.** -/
def mcOK (tabs : Tables) (f g : Func) : Bool :=
  atomsOK f g && closedOK f && closedOK g && KnownBits.blocksOK f g &&
  let R := reachMarks g
  let Lf := listedMarks f
  let Lg := listedMarks g
  let M := (List.range g.valueTab.size).toArray.map fun x =>
    R.getD x false && Lf[x]? == some true && Lg[x]? == some true
  reachOK g R && (List.range g.valueTab.size).all (valOK tabs f g R M)

end GoFV.Opt.MemCombine.Check

namespace GoFV.Opt

open GoFV.SSA GoFV.Opt.MemCombine

/-- **memcombine, validated**: the pass on loads only; its result if it changed and the checker
accepts it, else the input. -/
def memcombineChecked : Pass := fun env f => do
  let (c, u) ← memcombineCfg env
  let (g, _) ← memcombine { c with stores := false } u env.tables f
  return { func := if g != f && Check.mcOK env.tables f g then g else f, tables := env.tables }

end GoFV.Opt
