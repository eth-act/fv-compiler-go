package main

// Functions of the P5 difftest: sync/atomic's intrinsics (arm64: AtomicAdd/Exchange/
// CompareAndSwap/And*value/Or*value, each guarded by HasCPUFeature with its LSE *Variant;
// AtomicStore, AtomicLoad), on locals, through pointers (nil-guarded: an atomic access through
// nil faults on arm64, which the semantics leaves stuck), on slice elements and struct fields,
// and the typed atomic.Int32/Int64/Uint32/Uint64/Bool/Uintptr wrappers.

import "sync/atomic"

func init() {
	for k, v := range map[string]any{
		"atomAdd32": atomAdd32, "atomAdd64": atomAdd64, "atomAddU32": atomAddU32,
		"atomAddU64": atomAddU64, "atomSwap32": atomSwap32, "atomSwap64": atomSwap64,
		"atomCAS32": atomCAS32, "atomCAS64": atomCAS64, "atomLoadStore32": atomLoadStore32,
		"atomLoadStore64": atomLoadStore64, "atomAnd32": atomAnd32, "atomOr32": atomOr32,
		"atomAnd64": atomAnd64, "atomOr64": atomOr64, "atomPtrAdd32": atomPtrAdd32,
		"atomPtrCAS64": atomPtrCAS64, "atomPtrSwap64": atomPtrSwap64, "atomSlice": atomSlice,
		"atomStruct": atomStruct, "atomTyped64": atomTyped64, "atomTyped32": atomTyped32,
		"atomTypedU": atomTypedU, "atomBool": atomBool, "atomUintptr": atomUintptr,
		"atomCASLoop": atomCASLoop, "atomCounter": atomCounter,
	} {
		funcs[k] = v
	}
}

func atomAdd32(x, d int32) (int32, int32) {
	r := atomic.AddInt32(&x, d)
	return r, x
}

func atomAdd64(x, d int64) (int64, int64) {
	r := atomic.AddInt64(&x, d)
	return r, x
}

func atomAddU32(x, d uint32) (uint32, uint32) {
	r := atomic.AddUint32(&x, d)
	return r, x
}

func atomAddU64(x, d uint64) (uint64, uint64) {
	r := atomic.AddUint64(&x, d)
	return r, x
}

func atomSwap32(x, n int32) (int32, int32) {
	r := atomic.SwapInt32(&x, n)
	return r, x
}

func atomSwap64(x, n int64) (int64, int64) {
	r := atomic.SwapInt64(&x, n)
	return r, x
}

func atomCAS32(x, o, n int32) (bool, int32) {
	r := atomic.CompareAndSwapInt32(&x, o, n)
	return r, x
}

func atomCAS64(x, o, n int64) (bool, int64) {
	r := atomic.CompareAndSwapInt64(&x, o, n)
	return r, x
}

func atomLoadStore32(x, v int32) (int32, int32) {
	old := atomic.LoadInt32(&x)
	atomic.StoreInt32(&x, v)
	return old, atomic.LoadInt32(&x)
}

func atomLoadStore64(x, v int64) (int64, int64) {
	old := atomic.LoadInt64(&x)
	atomic.StoreInt64(&x, v)
	return old, atomic.LoadInt64(&x)
}

func atomAnd32(x, m int32) (int32, int32) {
	r := atomic.AndInt32(&x, m)
	return r, x
}

func atomOr32(x, m uint32) (uint32, uint32) {
	r := atomic.OrUint32(&x, m)
	return r, x
}

func atomAnd64(x, m uint64) (uint64, uint64) {
	r := atomic.AndUint64(&x, m)
	return r, x
}

func atomOr64(x, m int64) (int64, int64) {
	r := atomic.OrInt64(&x, m)
	return r, x
}

func atomPtrAdd32(p *int32, d int32) int32 {
	if p == nil {
		return -1
	}
	return atomic.AddInt32(p, d)
}

func atomPtrCAS64(p *int64, o, n int64) bool {
	if p == nil {
		return false
	}
	return atomic.CompareAndSwapInt64(p, o, n)
}

func atomPtrSwap64(p *uint64, n uint64) uint64 {
	if p == nil {
		return 0
	}
	return atomic.SwapUint64(p, n)
}

func atomSlice(s []int32, i int, d int32) int32 {
	return atomic.AddInt32(&s[i], d)
}

type atomFields struct {
	a int32
	b int64
	c uint32
}

func atomStruct(s *atomFields, d int64) int64 {
	if s == nil {
		return 0
	}
	atomic.AddInt32(&s.a, int32(d))
	atomic.StoreUint32(&s.c, atomic.LoadUint32(&s.c)|uint32(d))
	return atomic.AddInt64(&s.b, d)
}

func atomTyped64(x, d int64) (int64, bool, int64) {
	var a atomic.Int64
	a.Store(x)
	a.Add(d)
	ok := a.CompareAndSwap(x+d, 7)
	return a.Load(), ok, a.Swap(-x)
}

func atomTyped32(x, d int32) (int32, int32, int32) {
	var a atomic.Int32
	a.Store(x)
	o := a.And(d)
	n := a.Or(^d)
	return o, n, a.Load()
}

func atomTypedU(x, d uint64) (uint64, uint64, bool) {
	var a atomic.Uint64
	var b atomic.Uint32
	a.Store(x)
	b.Store(uint32(d))
	b.Add(uint32(x))
	ok := b.CompareAndSwap(uint32(x+d), 1)
	return a.Add(d), uint64(b.Load()), ok
}

func atomBool(x bool) (bool, bool) {
	var a atomic.Bool
	a.Store(x)
	old := a.Swap(!x)
	return old, a.Load()
}

func atomUintptr(x, d uintptr) (uintptr, uintptr) {
	var a atomic.Uintptr
	a.Store(x)
	r := a.Add(d)
	return r, a.Swap(x)
}

func atomCASLoop(p *int64, n int) int64 {
	if p == nil {
		return 0
	}
	for range n % 16 {
		for {
			old := atomic.LoadInt64(p)
			if atomic.CompareAndSwapInt64(p, old, old*3+1) {
				break
			}
		}
	}
	return atomic.LoadInt64(p)
}

func atomCounter(xs []int32) (int32, int64) {
	var sum int32
	var cnt int64
	for i := range xs {
		atomic.AddInt32(&sum, xs[i])
		atomic.AddInt64(&cnt, 1)
	}
	return atomic.LoadInt32(&sum), atomic.LoadInt64(&cnt)
}
