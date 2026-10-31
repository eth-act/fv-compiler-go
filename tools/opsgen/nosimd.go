package main

// simdGenericOps stands in for _gen/simdgenericOps.go, which scripts/gen-ops.sh does not copy:
// the 1,566 SIMD generic ops exist only under GOEXPERIMENT=simd, which go1.27.3 leaves off
// (the "cpufeatures" and "rewrite tern" passes are disabled without it), and an `Op` inductive
// with them took about 60 s to elaborate versus about 5 s without (LEARNINGS.md).
func simdGenericOps() []opData { return nil }
