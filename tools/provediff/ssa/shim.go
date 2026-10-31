// Package ssa holds a copy of the compiler's poset.go (copied in by scripts/prove-difftest.sh)
// with the minimal stand-ins it needs from package ssa.
package ssa

// ID is ssa.ID.
type ID int32

// Value stands in for *ssa.Value: the poset only reads the ID.
type Value struct{ ID ID }

// Cache stands in for ssa.Cache (allocBitset/freeBitset).
type Cache struct{}

func (c *Cache) allocUintSlice(n int) []uint { return make([]uint, n) }
func (c *Cache) freeUintSlice(s []uint)      {}
