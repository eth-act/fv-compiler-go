#!/usr/bin/env bash
# Differential test of GoFV.Util (PdqSort, SparseSet, SparseMap, SparseMapPos) against Go
# (issue #41). tools/utildiff and the compiler's sparseset.go, sparsemap.go, sparsemappos.go
# (pinned tree, docs/PINS.md) are copied into <repo>/tmp/utildiff; the Go program writes
# random cases with Go's results, and `lake exe util-difftest` recomputes them in Lean.
# slices.SortFunc and sort.Sort come from the host Go's standard library, so their sources
# must be byte-identical to the pinned go1.27.3 ones (checked below).
#
# usage: scripts/util-difftest.sh [-n cases per kind] [-seed s]   (go from $GO, default `go`)
#        UTILDIFF_COVER=1 also prints Go's statement coverage of the sort code by the cases.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
pinned=$root/third_party/go/src
work=$root/tmp/utildiff
go=${GO:-go}
goroot=$("$go" env GOROOT)
for f in slices/zsortanyfunc.go slices/sort.go sort/zsortinterface.go sort/sort.go; do
  if ! cmp -s "$goroot/src/$f" "$pinned/$f"; then
    echo "util-difftest: $goroot/src/$f differs from the pinned $f; set GO to a matching toolchain" >&2
    exit 1
  fi
done
rm -rf "$work"
mkdir -p "$work"
cp -r "$root/tools/utildiff/." "$work/"
for f in sparseset sparsemap sparsemappos; do
  sed 's#"cmd/internal/src"#"gofv/tools/utildiff/src"#' \
    "$pinned/cmd/compile/internal/ssa/$f.go" > "$work/ssa/$f.go"
done
cd "$work"
if [ -n "${UTILDIFF_COVER:-}" ]; then
  GOTOOLCHAIN=local "$root/scripts/memcap.sh" "$go" build -cover -coverpkg=slices,sort,gofv/tools/utildiff,gofv/tools/utildiff/ssa -o utildiff .
  mkdir -p cover
  GOCOVERDIR=$work/cover "$root/scripts/memcap.sh" ./utildiff -o "$work/cases.txt" "$@"
  "$go" tool covdata func -i=cover | grep -E 'zsort(anyfunc|interface)\.go|ssa/sparse' | grep -vE 'Ordered|stable|symMerge|rotate|swapRange|_func' || true
else
  GOTOOLCHAIN=local "$root/scripts/memcap.sh" "$go" run . -o "$work/cases.txt" "$@"
fi
cd "$root"
"$root/scripts/memcap.sh" lake build util-difftest
"$root/scripts/memcap.sh" lake exe util-difftest "$work/cases.txt"
