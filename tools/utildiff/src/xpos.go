// Package src stands in for cmd/internal/src, of which sparsemappos.go only uses the XPos
// type: a position base index and a packed line/column/statement word.
package src

type XPos struct {
	Index int32
	Lico  uint32
}
