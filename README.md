# gofv

A formally verified port of the Go compiler's SSA optimiser to Lean 4.

Phase 1 covers the machine-independent passes of `cmd/compile/internal/ssa` (Go 1.27.3), from
`number lines` up to `lower`: each pass is ported to Lean, checked for exact parity against the
stock compiler on a corpus, and then proven to preserve the semantics of Go SSA.

- [docs/PLAN.md](docs/PLAN.md): design, milestones, correctness criterion
- [docs/PINS.md](docs/PINS.md): pinned versions
- [AGENTS.md](AGENTS.md): rules for contributors and their agents
- [LEARNINGS.md](LEARNINGS.md): measured tricks for fast Lean proofs and builds

## Setup

```
scripts/fetch-third-party.sh          # Go 1.27.3 source into third_party/go
scripts/memcap.sh lake build
```

## Checks

```
scripts/util-difftest.sh              # GoFV.Util (pdqsort, sparse set/maps) against Go on random cases
```
