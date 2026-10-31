package ssa

import (
	"fmt"
	"math/rand/v2"
	"slices"
	"strings"
)

// PosetCase runs nops random operations on a fresh poset over the values v1..vk and returns
// one case line: "P <k> <nops> <op...> <result...>". Ops:
//
//	o:a:b SetOrder   e:a:b SetOrderOrEqual   q:a:b SetEqual   n:a:b SetNonEqual
//	O:a:b Ordered    L:a:b OrderedOrEqual    E:a:b Equal      N:a:b NonEqual
//	c Checkpoint     u Undo (only while a checkpoint is open)
//
// Each result is "<bool 0|1 or ->/<state>", the state after the op being
// "lastidx;roots;nodes;values;noneq;undolen" (nodes 1..lastidx as l.r packed edges, values as
// id=idx sorted by id, noneq as hi.lo pairs sorted). The undo stack's length is compared, not
// its contents: aliasnodes pushes its records in map order.
func PosetCase(r *rand.Rand, k, nops int, unsigned bool) string {
	po := newPoset()
	po.SetUnsigned(unsigned)
	vals := make([]*Value, k+1)
	for i := 1; i <= k; i++ {
		vals[i] = &Value{ID: ID(i)}
	}
	var ops, res []string
	open := 0
	pair := func() (int, int) {
		a := 1 + r.IntN(k)
		b := 1 + r.IntN(k-1)
		if b >= a {
			b++
		}
		return a, b
	}
	b2s := func(b bool) string {
		if b {
			return "1"
		}
		return "0"
	}
	for range nops {
		var op, out string
		switch x := r.IntN(100); {
		case x < 6:
			op, out = "c", "-"
			po.Checkpoint()
			open++
		case x < 10 && open > 0:
			op, out = "u", "-"
			po.Undo()
			open--
		default:
			a, b := pair()
			kinds := "oeqnOLEN"
			c := kinds[r.IntN(len(kinds))]
			op = fmt.Sprintf("%c:%d:%d", c, a, b)
			va, vb := vals[a], vals[b]
			switch c {
			case 'o':
				out = b2s(po.SetOrder(va, vb))
			case 'e':
				out = b2s(po.SetOrderOrEqual(va, vb))
			case 'q':
				out = b2s(po.SetEqual(va, vb))
			case 'n':
				out = b2s(po.SetNonEqual(va, vb))
			case 'O':
				out = b2s(po.Ordered(va, vb))
			case 'L':
				out = b2s(po.OrderedOrEqual(va, vb))
			case 'E':
				out = b2s(po.Equal(va, vb))
			case 'N':
				out = b2s(po.NonEqual(va, vb))
			}
		}
		ops = append(ops, op)
		res = append(res, out+"/"+posetState(po))
	}
	return fmt.Sprintf("P %d %d %s %s", k, nops, strings.Join(ops, " "), strings.Join(res, " "))
}

func posetState(po *poset) string {
	var sb strings.Builder
	fmt.Fprintf(&sb, "%d;", po.lastidx)
	for i, rt := range po.roots {
		if i > 0 {
			sb.WriteByte(',')
		}
		fmt.Fprint(&sb, rt)
	}
	sb.WriteByte(';')
	for i := 1; i < len(po.nodes); i++ {
		if i > 1 {
			sb.WriteByte(',')
		}
		fmt.Fprintf(&sb, "%d.%d", uint32(po.nodes[i].l), uint32(po.nodes[i].r))
	}
	sb.WriteByte(';')
	var ids []int
	for id := range po.values {
		ids = append(ids, int(id))
	}
	slices.Sort(ids)
	for i, id := range ids {
		if i > 0 {
			sb.WriteByte(',')
		}
		fmt.Fprintf(&sb, "%d=%d", id, po.values[ID(id)])
	}
	sb.WriteByte(';')
	var his []int
	for hi := range po.noneq {
		his = append(his, int(hi))
	}
	slices.Sort(his)
	first := true
	for _, hi := range his {
		bs := po.noneq[uint32(hi)]
		for lo := range len(bs) * uintSize {
			if bs.Test(uint32(lo)) {
				if !first {
					sb.WriteByte(',')
				}
				first = false
				fmt.Fprintf(&sb, "%d.%d", hi, lo)
			}
		}
	}
	fmt.Fprintf(&sb, ";%d", len(po.undo))
	return sb.String()
}
