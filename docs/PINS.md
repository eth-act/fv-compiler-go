# Pinned external dependencies

Upgrading any of these is an explicit migration: re-run the export parity corpus afterwards.

| Component | Pin | Notes |
| --- | --- | --- |
| Lean toolchain | `leanprover/lean4:v4.34.1` | `lean-toolchain`; same pin as clifv so tricks and code transfer |
| Go source | tag `go1.27.3`, commit `2aae1000ea1d4b28923b96db28acf4e3b99d6aff` | latest Go release at pin time; `scripts/fetch-third-party.sh` puts it in `third_party/go` (not committed) |
| Target | `GOOS=linux GOARCH=arm64` | the `ssa.Config` the generic passes are run and exported under (pointer size 8, arm64 register ABI in `expand calls`); arm64 so a later backend can reuse clifv's Arm model. Executables run under `qemu-aarch64-static`. |

## Paths used from the pinned tree

- Pass list: `third_party/go/src/cmd/compile/internal/ssa/compile.go` (`passes`)
- Generic ops: `third_party/go/src/cmd/compile/internal/ssa/_gen/genericOps.go`, `decOps.go`, `divisibleOps.go`, `divmodOps.go`
- Rewrite rules: `_gen/generic.rules`, `dec.rules`, `divisible.rules`, `divmod.rules` (rule parser: `_gen/rulegen.go`)

## Patched oracle toolchain

- `patches/go/*.patch` (the per-pass SSA exporter, `docs/contracts/export.md`) applied to the pinned
  tree by `scripts/build-go.sh` into `third_party/go-build` (not committed); bootstrap toolchain
  `$GOROOT_BOOTSTRAP`, default `/home/kev/work/go` (go1.26).
- Corpus: `scripts/export-corpus.sh` → `../gofv-corpus/<pin12>/` (not committed), manifest
  `corpus/manifest.txt`.
