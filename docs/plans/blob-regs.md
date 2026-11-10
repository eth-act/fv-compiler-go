# Design review: byte-precise integer registers for `Move` → `MOV*store` (#385)

Status: design review, nothing implemented (issue #385; analysis by P2ProofLow39 in #385 comment
6730880066, deferral in 6741128337, review summary in 6768173103). Semantics of lowered code:
`docs/plans/semantics2.md`; Phase 3: `docs/plans/semantics3.md`, `docs/plans/proofs3.md`.

**Decision (integrator, 2026-11-10): deferred.** Reasons: 6–8 agent-days for +414 functions at
stock (≈ 0.4 % of full-v9, §9); B2 weakens `Mem.Refines` in principle, the relation every phase
rests on, a high-risk change to the trust story for a small gain; B3 adds a new premise. Revisit
when the remaining blockers on the same copies (the `FLDPQ`/`FMOVQload` offset folds, the indexed
`Move` stores, §9) are done and `Move` → `MOV*store` is the top remaining class.

## 1. The class

`lower` copies a small `Move [s]` through integer registers (`ARM64.rules:380`–`415` for
`s ≤ 15`; `420` for `16 < s ≤ 24` and `428` for `32 < s ≤ 40`, an 8-byte tail on a 128-bit copy):

```
(Move [8]  dst src mem) => (MOVDstore dst (MOVDload src mem) mem)                  -- 396
(Move [s] dst src mem) && s > 32 && s <= 40 =>
  (MOVDstore [s-8] dst (MOVDload [s-8] src mem) (FSTPQ dst (Select0 (FLDPQ src mem)) …)) -- 428
```

`moveQ2Op`, `GoFV.Proof.Low.Sim.moveQ_lower_eval`). The integer forms are not: on full-v9 the
validator's ceiling rejects 1,581 functions first at an atom `Move -> MOV…store` (plain or
indexed; 1,118 of them `MOVDstore`, `lower-next.md`), and `428` alone completes 666 functions in
the greedy cover.

## 2. Why the integer copy is false today

Two independent obstructions. P2ProofLow39's analysis covers the first; the second was found in
this review.

**A. Bytes that do not decode (padding, mixed fragments).** `Move` copies bytes as they are
(`memRoot`: `m.read` then `m.write`). `MOVDload` is `Arm64.loadN 8` (`Sem/Arm64/Mem.lean`):
`Mem.load (.int .w64)`, i.e. `decodeInt .w64`, which is `poison` unless the 8 bytes are all
concrete or exactly the 8 fragments of one pointer. `MOVDstore` of `poison` writes 8 `poison`
bytes (`storeBytes`). Counterexample (#385): `struct{a int32}` padded to 8 bytes after `VarDef` and
`a = 1` holds `[1,0,0,0,⊥,⊥,⊥,⊥]`; the copy loses `a`. The narrow forms (`MOVWUload` …) fail the
same way on a padding byte.

**B. A stored convertible pointer is re-materialised as its address bytes (new).** An 8-byte
integer load of the 8 fragments of a pointer `p` gives `Ptr.word p` (`decodeInt`), which is
`.int .w64 a` when `p` converts (`Ptr.convertible`: every heap pointer under `Addrs.fixed`).
`MOVDstore` then writes `intBytes 8 a`: concrete bytes where `Move` copied `frag p 0 … frag p 7`.
`Byte.Refines (.frag p i) (.b x)` is false, so the target's memory does not refine the source's
(`Mem.Refines` is bytewise) and `OutcomeRefines` fails on the final memory. Evaluated on main
(`Addrs.fixed`): `p = heap 0 + 8` stored at `heap 0 + 0`, `loadN (.int .w64) 8 false` gives
`i64:1099511627784`, and `storeBytes 8` of it is `[0x08,0,0,0,0,0x01,0,0]`, not `ptrBytes p`.
Every value the semantics computes at a word shape is already in this normal form (`Val.retype`
makes a convertible pointer its word), so such fragments come only from the input memory and
from callees' contracts, which no premise restricts (`VPre`). Blob registers alone (§3) do not
remove B: the 8 fragments decode, so no blob is involved. The 128-bit forms are not affected
(`Arm64.load16` is the raw bytes).

## 3. The semantic change for A (lowered layer only)

- **New `Arm64.loadB ty n m p`** for the unsigned integer loads only: `MOVBUload`, `MOVHUload`,
  `MOVWUload`, `MOVDload`, their `…idx`/`…idx{2,4,8}` forms, and the elements of `LDP`/`LDPW`
  (`pair` turns two `MOVDload`s into an `LDP`; `MoveL.pair_refinesL` must stay true). It is
  `loadN ty n false m p` unless that is `poison`, the access is valid with bytes `bs`, `ty ≠ .bool`
  and `blobOK n bs`; then it is `.blob bs`.
  `blobOK n bs`: not every byte is `poison`, and, for `n = 8`, there is no pointer `q` with every
  byte `poison` or `frag q i` at its position `i` (so no completion of `bs` decodes to a pointer
  word, which could be `.ptr q` or, outside its window, `poison`). `blobOK` is monotone in
  `BytesRefine`, which is what makes `loadB` monotone (§4).
  Signed loads (`MOVB/H/Wload`, `LDPSW`) and float loads (`FMOVS/Dload`, whose `ty` is the same
  `.int` shape) keep `loadN`: `loadN` itself is not changed, so its 18 Phase 2 and 54 Phase 3
  mentions stay as they are.
- **`Val.retypeL`** (`Sem/RunL.lean`) keeps `.blob bs` at an integer shape `.int w` with
  `bs.length ≤ w.bytes` (the zero-extended register); every other blob at a non-blob shape stays
  `poison`. Today `retypeL` = `widen` then Phase 1's `retype`, which makes it `poison`.
- `Arm64.reg (.blob _) = none` already (the `_ => none` arm): arithmetic on such a register is
  `poison`. `storeBytes n (.blob bs)` already writes `bs` when `bs.length = n`.
- Optional: `Arm64.regVal` (`MOVDreg`, `MOVDnop`, `CSEL`'s selected input) passes a blob through as
  it passes `.ptr p`, which is what `MOV`/`CSEL` do. Not needed for the rules in §1 (a blob there
  becomes `poison`, which refines); it keeps rules that insert a `MOVDreg` on a load sound.

Unchanged: `Val`, Phase 1's `Mem.load`, `decodeInt`, `decodePtr`, `encode`, `Val.retype`,
`memRoot`, `Arm64.load16`, `Arm64.move`, `loadN`. `run` is untouched (`runL_generic` keeps its
statement: a generic function has no arm64 load).

**Faithfulness.** arm64: `LDR`/`LDRB`/`LDRH`/`LDR Wt` and `STR*` move bits verbatim
(`arm64/ssa.go:926-944`, one instruction per op), and a `poison` byte stands for unspecified
contents, which the hardware copies like any other; `ValRel` relates a blob to the register
bytewise (§7). Go: `Move` is a byte copy, and the arm64 backend relies on it by copying
padding with integer loads and stores (`ARM64.rules:380-434`). Go never interprets padding: the
generated equality of a padded struct compares its fields and skips the padding
(`types/size.go:566-569`, `IsPaddedField`, `types/alg.go:81-92`; `compare/compare.go:36`), and
arithmetic on a partly unspecified word stays undefined (`reg = none`). The alternative, a
`Move` that poisons any 8-byte chunk holding a `⊥` byte, is unfaithful: Go guarantees a struct
copy copies its fields, and it would break Phase 1's `Move` proofs.

## 4. The refinement relation for A: options (a) and (b)

`loadB` must be monotone under memory refinement (every pass proof relates registers across
`Mem.Refines`; `GoFV.Proof.Low.Mono.loadN_mono` is today's lemma). From `m ⊑ m'`, a `.blob bs`
in `m` may be `.int w x` in `m'` with `bs ⊑ intBytes bs.length x`. It is never `.ptr q` or a
pointer word in `m'`: `blobOK` excludes every `bs` the 8 fragments of one pointer refine. So
exactly one new pair is needed, blob → integer:

```
blobInt {bs : List Byte} {w : Width} {x : BitVec w.bits} :
  bs.length ≤ w.bytes → BytesRefine bs (intBytes bs.length x.toNat).toList →
  x.toNat < 2 ^ (8 * bs.length) → Refines (.blob bs) (.int w x)
```

(P2ProofLow39 also listed blob → pointer; `blobOK` makes it unnecessary.) `Refines.trans` and
`Refines.refl` keep their statements (`BytesRefine` composes).

**(a) Add `blobInt` to the shared `GoFV.SSA.Sem.Refines`.** Inventory, by a Lean pass over the
compiled proofs of `GoFVTest.Proof.AllProof` on 544c0e3b (throwaway scripts, not committed;
`Refines.casesOn`/`Refines.rec` applications through matchers and auxiliary lemmas, and whether
their `blob` arm is reachable, i.e. not closed by `noConfusion`: a new arm appears exactly where
the source can be a blob):

| | declarations eliminating `Refines` | with a reachable `blob` arm | reachable arms |
|---|---:|---:|---:|
| Phase 1 (`Proof/*`, `Proof/Pass`, `Proof/Rules`, `ProveCheck`, witnesses) | 105 | 53 | 83 |
| Phase 2 (`Proof/Low`, `RefineL`, `RefineSched`, witnesses) | 63 | 42 | 114 |
| Phase 3 (`Proof/Gen`, `Proof/Obj`) | 0 | 0 | 0 |

The Phase 1 sites: `PureMono` 22, `RunMono` 6, `Pass.ECFinish` 4, `ABIBuild` 2, `Pass.ECStack` 2,
`Pass.ECChain` 2, `Pass.LoadFwdDrop` 2, `Rules.SelMake` 2, `Pass.RewriteTermBlock` 2 and 9 single
ones (`ValRefine` (`Refines.trans`), `TermStep`, `FinishMono`, `CallMono`, `AtomSimStep`,
`SccpInv`, `LoadFwdPtr`, `ECCall`, `Rules.Dec`). Phase 2: `Low.ArmMonoFam` 16 (`add_mono` and
`sub_mono` have 21 arms each, the `cmp*_mono` 10), `SimDen` 5, `QPart` 5, `ValBlock` 4, `TermL` 4,
`ArmMonoRetype` 3, `ValReplay` 2, `DenL` 2, `ValMul` 1. In almost every new arm the source blob
makes the op `poison` (`reg (.blob _) = none`, Phase 1 ops on a blob at a scalar shape), so the
arm is `exact .poison _`; the real ones are `encode_mono` (Phase 1 `encode (.int w) (.blob bs)` is
`bs`, a `BytesRefine` to `intBytes`), `retype_mono`/`widen_mono`/the new `retypeL` arm, `loadB_mono`
and `Refines.trans`. 1,097 declarations mention `Refines` in their statement (615 of them in
`Proof/Low`, none in Phase 3); none needs a new statement.

Statements: none changes textually (`verifiedPipeline_refines`, `verifiedPipelineFull_refines`,
`lower_refines`, the per-pass theorems, `verified_mach`, `verified_mach_atSP`, the G slices).
In principle every `Refines` statement admits one more pair. On the end-to-end statements this
is no weakening: the source is Phase 1's `run`, whose `finish` retypes results at their types
with Phase 1's `retype` (a blob at a scalar shape is `poison`, which `finish` rejects), so a
defined source result is never a blob where the target has an integer. The implementation PR
should prove this as a theorem (outcome refinement of a defined `run` without `blobInt` follows
from the one with it), so that "no weakened statement" is checked, not argued.

**(b) A lowered register relation `RefinesB` (= `Refines` plus `blobInt`), `Sem.Refines`
unchanged.** (The name `RefinesL` is taken: `GoFV.Proof.RefinesL` is the program refinement over
`runL`.) It spreads:
- through the value environment of every Phase 2 simulation (`SimL`, `CongL`, `EvalL`, the
  `Low.Sim*` family, `RefineSched`, `RefineLoc`, regalloc, the L0 → L0 passes), since a load's
  result enters the environment;
- into the lowered op monotonicity lemmas (237 statements in `Low.ArmMonoOps`, 79 in
  `ArmMonoFam`, `DenL`, `QPart`, `ArmMonoRetype`: arguments related by `RefinesB`);
- into Phase 1's monotonicity of the generic ops `runL` evaluates in lowered functions (`Phi`,
  `Copy`, `Store`, `MakeResult`, calls, selects): `PureMono` 43, `RunMono` 39, `CallMono` 17,
  `PhiMono` 13, `FinishMono` 13, `ABIBuild` 13 statements, restated for `RefinesB` or generalised
  over the relation, because `retypeL` hands them blobs at integer shapes.
The per-pass statements over lowered code (`RefinesFrom` between two `runL`s) stay
`OutcomeRefines` with `Refines`: a poison-free blob is refined only by itself (§5). Same new arms
as (a), duplicated in a second relation, plus the restatements.

**Recommendation for A: (a).** About half the work, one relation, no restated theorem; the
cost is that Phase 1's shared relation gains a constructor, covered by the theorem above.

## 5. The observable result relation stays `Refines`

`finish` rejects a result that contains `poison` deeply (including a blob's bytes), so a defined
source result is poison-free. A poison-free `bs` is refined bytewise only by itself (`BytesRefine`
with no `⊥` is equality; with B2 below, also by the addresses of its convertible fragments), so
`blobInt` relates it to `.int w x` only when `bs` holds `x`'s bytes, which `loadB` never makes a
blob (they decode). Under (a) and (b) the outcome relation is `OutcomeRefines` with `Refines`.

## 6. The fix for B

- **B1, raw registers for pointer fragments: not possible.** The copy's `MOVDload <uint64>` is the
  same op at the same shape as a lowered `Load <uint64>` (or `uintptr`), whose value must refine
  Phase 1's `.int a`.
- **B2, a byte refinement from a convertible pointer's fragment to its address byte (recommended
  if the class is pursued).** `Byte.Refines` gains `fragAddr : p.convertible → p.addr? = some a →
  Byte.Refines (.frag p i) (.b (a.extractLsb' (8*i) 8))`. Loads are monotone: 8 fragments decode
  to `Ptr.word p = .int a`, as their address bytes do; a narrow load of fragments is `poison`.
  `memEq` (`Sem/Ptr.lean`) must compare a convertible fragment as its address byte (today `frag`
  vs. `.b` is `false`, where the target may compare equal bytes: not monotone); that is what
  `runtime.memequal` does on the bits. Inventory: 9 Phase 1 declarations eliminate
  `Byte.Refines` (`ValRefine` 3, `MemRefine` 2, `Sem.Val` 2, `MemCombineSem` 1, a DSE witness),
  193 statements mention `Byte.Refines`/`BytesRefine`/`Mem.Refines` (183 Phase 1, 10 Phase 2), Phase
  3 none (`ByteRel` relates both to the same machine byte under `AddrAgree`). It weakens the
  memory part of `OutcomeRefines` in principle (a target may hold a convertible pointer's address
  bytes where the source holds its fragments: the same bits on the machine), so it is a
  decision under the "no weakened statement" criterion, and `memEq`'s change alters defined
  results (`false` → `true` on such bytes), which sem-difftest must show.
- **B3, a normal-form memory premise.** `NormMem m`: no fragment of a convertible pointer. All
  values the semantics stores are in normal form, so it is preserved by `run`/`runL`/`runLoc`,
  but it is a new premise on the input memory and a new trusted obligation on every callee
  contract (`CallOK`, `env.MemOps`, …). A weakened top-level statement.
- **B4, a normalising `Move` in Phase 1: rejected.** `(Move dst src mem) && isSamePtr(dst, src) =>
  mem` and dead-move elimination would become false.

## 7. Phase 3 impact (`runLoc`, `LocMatch`, `ValRel`)

A register may hold a blob after §3, so:
- `ValRel ι (.blob bs) r := bs.length ≤ 8 ∧ ∀ i (h : i < bs.length), ByteRel ι bs[i]
  (r.extractLsb' (8*i) 8)` (today `False`); the same case in `Lo` (`Proof/Gen/Value.lean`),
  `Fits c` (`8 * bs.length ≤ c`) and `FitsW`. `FValRel` is unchanged (float loads keep `loadN`).
  `SlotRel` is `ValRel` of the slot's bytes, so a spilled blob needs nothing more.
- Loads: `lo_loadN`'s blob path from `memInj_byteRel` (every byte of a live block is `ByteRel`
  under `AddrAgree`), for the plain, indexed (`loadIdx`) and pair (`loadPair_tuple*`) forms;
  `stepLoc_loadN`, `loadN_core`.
- Stores: `storeBytes_rel`, `storeBytes_relN`, `memInj_store`, `memInj_storeN` for a blob
  register (the stored bytes are `ByteRel` to the machine's by `ValRel`).
- Reads: `valRel_retypeL`, `valRel_retypeLW`, `fits_retype` (`retypeL` keeps the blob).
- Inventory: 70 Phase 3 declarations look inside `ValRel`/`Lo`/`Fits`/`FitsW` (matchers or
  equation lemmas; `Lo` 49, `ValRel` 10, `Fits` 10, `FitsW` 1); 850 statements mention a register
  relation, 166 mention `loadN`/`storeBytes`/`retypeL`. No Phase 3 statement changes;
  `verified_mach*` consume Phase 2's `OutcomeRefines` only.

## 8. Cost

| item | (a) + B2 | (b) + B2 |
|---|---|---|
| semantics (`loadB`, `retypeL`, `memEq`), sem-difftest | 0.5 day | 0.5 day |
| relation: new arms, `loadB_mono`, `encode_mono`, `retype*_mono` | 1.5–2 days | 5–8 days (restatements, Phase 1 mono for `RefinesB`) |
| B2: `fragAddr`, `load_mono`/`decode` lemmas, `memEq_mono` | 0.5–1 day | 0.5–1 day |
| no-weakening theorem (§4) | 0.5 day | — |
| Phase 3 (§7) | 1.5–2 days | 1.5–2 days |
| validator events and their soundness (`moveIOp`/`moveI2Op`, `MoveQRefL` and `qPart` for integer loads, `Sim.moveQ*_eval` generalised, `ld_ref`/`ldVal`), rule entries, witnesses | 1.5–2 days | 1.5–2 days |
| total | **≈ 6–8 agent-days** | ≈ 10–14 agent-days |

Agent-days of the kind spent on #607/#652; full-tree builds under the heavy lock are extra.

## 9. Expected gain (re-probed)

`lower-probe` on full-v9 with the validator extended to the integer `Move` copies as if their
rules held (branch `agent/blob-regs-probe`, probe only, not for merge: `moveIOp`/`moveI2Op`,
integer loads in `qVals`, `qStoreP` in `atomDef1`, and the pairing in `atomPair`/`compOKL`/`q2OKL`;
dump compared with #686's `dump-49.tsv`):

| full-v9 (96,560 functions) | main (#686) | probe |
|---|---:|---:|
| validator ceiling | 90,118 | **90,552** (+434, 0 lost) |
| ceiling-accepted, every fired rule proven | 88,539 | 88,539 |
| … with the integer `Move` rules (`380`–`428`) proven too | 88,539 | **88,953** (+414) |

So the class is worth about **+414 functions at stock** (89,618 → ≈ 90,030), not the 838 + 150
estimated before: of the 1,581 functions first rejected at an integer `Move` atom, 421 are then
accepted, and the rest stop at the next validator class on the same copies: `ARM64:876 FLDPQ`
and `872 FMOVQload` `[nomatch]` (572 + 103, an offset or symbol folded into the 128-bit half of
`420`/`428`), integer `Move` stores indexed (`atoms: Move -> MOV{B,H,W,D}storeidx*` and new
indexed atoms, ≈ 320), the integer load rules `1811`–`1814` `[ok]` (≈ 105). Those are validator
work on top; with them the class reaches about 1,500 functions.

## 10. Hard criteria for the implementation (as #607, #652)

1. No weakened statement: no top-level `*_refines`, `lower_refines`, pipeline, `verified_mach*`
   or witness statement changes; the theorem of §4 for `blobInt`; B2's memory weakening only
   with the integrator's explicit approval (else B3's premise is likewise a decision).
2. sem-difftest (native and the quick corpus, L0/L1/L2) identical to main, or every difference
   explained as strictly more defined (a padding copy now keeps its fields; fewer gaps), plus,
   under B2, every `memEq` result that changes listed and explained.
3. full-v9 and full-v11: Phase 1, through-`trim`, checked lower at stock and end-to-end counts do
   not drop.
4. Whole-tree `lake build GoFV GoFVTest`, `axioms-audit.sh --replay-changed`, no `sorry`, no new
   axioms, `check-reverts.sh`.
5. A dedicated semantics PR (`loadB`, `retypeL`, `blobInt`, B2) with this evidence, separate from
   the validator PR that adds the `Move` events and the rule entries.
