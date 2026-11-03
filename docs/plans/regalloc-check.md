# Plan: the regalloc checker (H7, #385)

Status: checker implemented (`GoFV/Opt/RegallocCheck.lean`, probe `regalloc-probe`); soundness
proven (`checkRA_sound`, §4, §6). Context: `docs/plans/semantics2.md` §7 (L2, `runLoc`),
`docs/PASSES2.md` §1.5 (the output is not SSA: arguments need not dominate their uses). The allocator
(`GoFV/Opt/Regalloc/*`, 100% parity, #425) is untrusted; only the checker is proven.

## 1. What is compared

`checkRA tabs f g`: `f` is the input of `regalloc` (the `flagalloc` section, L1, run by
`runSched`), `g` its output (the `regalloc` section, L2, run by `runLoc`), both in the tables
`tabs` of the `regalloc` section (which extend those of `f`'s section by the new autos and the
`AuxCall.Reg` caches).

What the checker needs from `f`: its blocks (kinds, controls, successors), its values by ID, and
`runSched`'s **schedule order** of each block (`Ctx.makeSched`, `schedOrder`: `b.Values` minus
phis, when it is a schedule; a block without one is `stuck` under `runSched` and needs no check).
`g` must have the same blocks with the same kinds, aux, auxint, successors and number of
controls, the same entry and `ownAux`, and `f.lowered = g.lowered` (so both runners shape values
the same way: `LMode.loc g = LMode.sched f`).

## 2. Facts

A fact `(l, o)` relates a location `l` of the `runLoc` state to a source value `o`:

| `l` | the target's |
| --- | --- |
| `reg r` | register `r` (`ZERO`, number 29, is never a location: it reads as 0, §3) |
| `slot k` | stack slot `k` (a `LocalSlot`: name, type, offset) |
| `mem` | current memory |
| `flags` | flags register |
| `avail` | (no location) the source value `o` is *available*, below |

`o = ⟨id, comp, weak⟩`: source value `id`, or component `comp` of the tuple it is. Meaning, with
`fr` the `runSched` frame, `s` the `runLoc` state and `md = LMode.sched f`:

- `val o` is `fr.regs[id]` (component `comp`); for a *frame constant* `id` (`isKVal`:
  `MOVDconst`, `FMOVSconst`, `FMOVDconst`, `ZERO`, `LoweredGetCallerPC`, `SP`, `SB`, `MOVDaddr` of
  `SP`/`SB`, the values `regalloc` may rematerialise) it is the constant's value `kval id`, which
  depends on the activation only (and `fr.regs[id]` is `none` or `kval id`).
- exact (`weak = false`): `s.at l = val o`; weak: `md.retype (shape o) (s.at l) = val o`.
  A weak fact arises from a phi of a narrower integer type than its argument in the argument's
  register (`phi t32 (x : t64)`): reading the register at the phi's type gives the low bits, as
  `runSched`'s phi takes them.
- `(avail, v)` (`v` with `pureArm64 v.op`: evaluated by `Arm64.evalPure` alone): `fr.regs[v]` is
  `md.retype (shape v) (Arm64.evalPure v.op … (fr.regs[args v]))`, i.e. no argument of `v` has
  been redefined since `v` ran.

Facts name frame constants by one representative per (op, aux, auxint, type, args) (`Cx.canon`;
`sameConst` is re-checked, the table is untrusted): `regalloc` rematerialises constants and
`flagalloc` recomputes flags, so equal constants with different IDs must be one origin.

## 3. Transfer (per target value, mirroring `stepLoc`)

Reads (`argOK`): a target argument `a'` read from its home (`readLoc`, as `LocState.raw`: a slot,
a register, the components of a tuple, the memory, the flags) holds the source argument `a`: the
location has a fact for `a` (any flavour), and `a'` and `a` have the same shape up to the word
shapes (`shapeEq`: `int64` and pointers have the same values, `Val.hasTy`). `ZERO` holds exactly
the zero constants (`MOVDconst [0]`, `ZERO`) at their shape. A selector reads only its
component (`selIndex`); a whole tuple is never read.

Then, for the target value `w`:

1. **Kept** (`w` has the ID of the next source value `u` in the block's order, same op, aux,
   auxint, type and arity; source frame constants before it may be skipped): its arguments hold
   `u`'s (`argsOK`); `MOVDreg`/`MOVDnop` see the same sign extension (`signOK`: the source's
   producer op, `Arm64.signExtends`, against the target register's producer, `LocCtx.signOf`);
   the clobbers lose their facts (`clobberFacts`: `regInfo.clobbers` — every caller-saved
   register at a call —, `clobbersArg0/1`, `tempRegs`, `clobberFlags`); `u` is redefined (facts
   about `u`, and availability of values reading `u`, are dropped, `Cx.redefine`); the written
   locations (`writeLocs`: a register, a slot — killing overlapping slots of the same variable —,
   each component of a tuple home, memory, flags) lose their facts and hold `u` exactly. If an
   available `v` has `u`'s op, aux, auxint, type and arguments (`pureEqs`), they hold `v` too
   (`flagalloc`'s recomputation of a flags value at a block end has no SSA uses, the successor's
   control still names the original); for a selector `u`, an available selector `v` of `u`'s op,
   aux, auxint and type whose argument's component sits at the same location, exactly, holds
   `u`'s new value too (`selEqs`: `flagalloc` recomputes a flags-producing tuple op and a new
   `Select1` takes its flags). A `pureArm64` `u`, a selector and a `MakeResult` become available.
2. **Moves** (`Copy`, `LoadReg`, `StoreReg`): the facts of the argument's location whose shape is
   the move's (and composes with the argument's, `composes`) are copied, exactly, to the
   destination. A move out of `ZERO` holds the zero constant the argument is.
3. **Rematerialised constant** (a new ID; the certificate names the source constant, `remat`):
   same op, aux, auxint, type and arguments; its home holds the constant.
4. **`KeepAlive x m` → `Copy m` / `VarLive {n} m`** (`regalloc.go`, `OpKeepAlive`): all are `m`.
5. **Phis** do nothing (`runLoc`: every argument has the phi's home).

The terminator (`termOK`): kind, aux, auxint and successors as the source's; each control that
`stepTermL` reads (control 0 of an arm64 kind, `If`, `JumpTable`, `Ret`) holds the source's
control (a `Ret`'s `MakeResult`: each argument, read from its home, `LocState.control`); the
others are readable.

**Edges** (`phiEdge`): at the end of a predecessor, along incoming edge `i` of `s`, the home of
every phi `p` of `s` holds its `i`th argument `a` — exactly, or weakly when `p`'s shape composes
with `a`'s; then the phis take their values: facts about the phis and availability of values
reading a phi are dropped, and `p`'s home holds `p` (weakly unless exact and of `a`'s shape).

**Certificate.** `Cert.ins[b]`: the facts at the entry of `b` (after its phis); empty at the
entry block. The check verifies, for every block and successor edge, that the edge's facts imply
(`sub`; an exact fact implies the weak one) the successor's certificate. `certify` computes it
by forward iteration with intersection at merges (untrusted; no fixpoint theory in the proof).

## 4. Soundness statement

```
theorem GoFV.Proof.RA.checkWith_sound {cert : Cert} (h : checkWith (Cx.make tabs f g) cert = .ok ()) :
    RefinesLS tabs g tabs f
theorem GoFV.Proof.RA.checkRA_sound (h : checkRA tabs f g = .ok ()) : RefinesLS tabs g tabs f
```

(`GoFV/Proof/Regalloc/Sound.lean`; `RefinesLS`, `GoFV/Proof/RefineLoc.lean`: every returning or
panicking `runSched` of `f` is a `runLoc` of `g`), in fact with equal outcomes and equal fuel:
block entries correspond one to one, and every target value that is not a move, a
rematerialisation or a phi computes the same `evalOpL` on the same arguments as its source
value. Any certificate will do (`certify` is untrusted). No precondition on the inputs is needed
(`RefinesLS.from P` for any `P`), so it composes with the Phase 2 chain. The source runs in the
`regalloc` section's tables. Those differ from `f`'s own in the call auxes' register caches, so
`tabsAgree` rejects them for every function with a call; the verified pipeline drops the caches
from `regalloc`'s output tables (`GoFV.Opt.Verified.regallocV`, `eraseCallRegs`; no runner and,
after `regalloc`, no Go code reads them) and checks `tabsAgreeL` of `f` in them
(`GoFV.Proof.PipelineFull.runSched_tabsAgreeL`; `docs/PASSES2.md` §0, "The verified pipeline
through `trim`").

## 5. The simulation

`Match S fr s`: every fact of `S` holds (§2), the frames agree outside the registers
(`s.fr.args = fr.args`, images, closure, initial memory), every defined source register has its
shape (`fr.regs[id] = some x → md.retype (shape id) x = x`), and frame constants are `none` or
their constant. Then:

- `Match ∅` at entry (`entryFrame` is the same on both sides: same tables, `ownAux`, params);
- a checked target value preserves `Match` with the walk's new facts, the source having run
  the kept value and the skipped constants (`evalAllL` vs. `enterBlockLoc`); a kept value's
  `evalOpL` is the same function of the same arguments (the contexts differ only in the function
  and its shapes: `evalOpL` reads the tables, ABI, activation and frame, not `ctx.f`, except
  `MOVDreg`/`MOVDnop`, which `runLoc` evaluates as `movdLoc` and `signOK` relates), so the two
  sides panic together, or both continue;
- `termOK` gives the same `stepTermL` result (`stepTermLoc` stages the target controls' values in
  `s.fr.regs`); `phiEdge` and `sub` give `Match (ins succ)` after the source's phis;
- by induction on fuel, `runLoopLoc` equals `runLoopL` (scheduled mode) until either ends, and
  `finish` is the same function of the outcome on both sides.

## 6. Proof stages

1. **Locations** (`GoFV/Proof/Regalloc/Loc.lean`): `LocState.at`; the reads `readLoc`/`writeLocs`
   agree with `LocState.raw`/`write`; a write leaves every non-clashing location unchanged
   (`setReg`, `setSlot`, `writeParts`, `clobber`); hence facts at other locations survive
   (`killLoc`, `clobberFacts`).
2. **Shapes**: `LMode.retype` idempotent on shaped values; word shapes retype alike
   (`shapeEq`); `composes t t' → retype t ∘ retype t' = retype t`.
3. **Values**: `argOK` → the target argument equals the source's; kept values give equal
   `evalOpL` results (context independence of `evalOpL` from `ctx.f` and `ctx.sched`; `movdLoc`
   vs. `arm64Op`'s `MOVDreg` under `signOK`); moves, rematerialisations, `KeepAlive`.
4. **Blocks** (`Block.lean`): `walk_sim` (`evalAllL` of the schedule, with skipped constants,
   against `enterListLoc`; both panic alike or both continue with `Match`); `term_sim`
   (`termOK`: the same `stepTermL` result, the target's controls staged); `phiEdge_sim` and
   `sub_sound` (the source's phis along an accepted edge, then the certificate).
5. **Loop and theorem** (`Sound.lean`): `loop_sim` by induction on fuel (`EntryInv`: after the
   source's phis, the certificate's facts), `checkWith_sound`, `checkRA_sound`. Witness
   (`GoFV/Proof/Witness/RandnRA.lean`): `runtime.randn` from the corpus, whose argument is
   spilled (`StoreReg`) before a `CALLstatic` of `runtime.rand` and reloaded (`LoadReg`) after;
   `checkRA` accepts by kernel evaluation and both runs return `randn(1000) = 71`.

Status: stages 1–5 proven, no `sorry`, standard axioms only.

Kernel evaluation of `checkRA` needs a function without frame constants: `constReps` and
`rematHints` key `Std.HashMap`s by the op's name, and `String.hash` is opaque to the kernel.

## 7. Probe (`lake exe regalloc-probe <corpus>`)

| corpus | functions | accepted | rejected |
| --- | --- | --- | --- |
| quick-v7 | 9,297 | 9,297 | 0 |
| full-v9 | 96,560 | 96,560 | 0 |

full-v9: 1,444,732 blocks, 7,250,138 target values, 70,980,509 certificate facts (at most 9,794
per block); 67 minutes with 4 jobs on a loaded machine.

`runtime.checkdead` and `pkgbits.(*Encoder).Flush`, rejected before #453, were a `runL`
semantics gap, not regalloc errors: late lower turned `MOVWreg x:(MOVWload)` into `MOVDreg x`,
then `pair` merged the load into `LDPSW`, so `x` is `Select1 (LDPSW …)`; `regalloc` reloads `x`
with a sign-extending `MOVW`. #453 made `runL` sign-extend through the selectors of `LDPSW`
(`Arm64.signExtendsIn`), and `LocCtx.signOf` and `signOK` follow it.
`json/v2.parseDurationBase10` (`missing-flags`) was a checker gap: `flagalloc` recomputes a
flags-producing tuple op and takes the flags with a new `Select1`, which the successor's control
does not name; `selEqs` relates the two selectors. `certify` skips failing blocks (a failure is
reported where it happens, not as missing facts in its successors).

What the probe found on the way (each now handled, above): `ZERO` homes for zero constants of
every type and moves out of it; duplicate and rematerialised frame constants (`Cx.canon`); the
word shapes; narrowing phis (weak facts) and widening phis of narrow producers (exact facts);
`flagalloc`'s flag recomputations (availability); `KeepAlive` → `Copy`/`VarLive`; reloads of
signed narrow values feeding `MOVDreg` (`runLoc` now follows the register's producer,
`LocCtx.signOf`); functions without arm64 ops (`runLoc` shapes as `runSched` does).
