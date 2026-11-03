package main

// simdGenericOps stands in for _gen/simdgenericOps.go, which scripts/gen-ops.sh does not copy:
// the 1,566 SIMD generic ops exist only under GOEXPERIMENT=simd, which go1.27.3 leaves off
// (the "cpufeatures" and "rewrite tern" passes are disabled without it), and an `Op` inductive
// with them took about 60 s to elaborate versus about 5 s without (LEARNINGS.md).
//
// The ARM64 SIMD ops of _gen/simdARM64ops.go (appended to the ARM64 op list by ARM64Ops.go)
// are left out for the same reason; that file is copied, so opsgen knows their names and
// filters them (simdARM64Names), and checks them against opGen.go. They are only produced by
// the rules of simdARM64.rules, whose patterns all start at a SIMD op.
func simdGenericOps() []opData { return nil }

// simdARM64Names are the names of the ops of simdARM64ops.go.
func simdARM64Names() map[string]bool {
	var r regInfo
	m := map[string]bool{}
	for _, o := range simdARM64Ops(r, r, r, r, r, r) {
		m[o.name] = true
	}
	return m
}
