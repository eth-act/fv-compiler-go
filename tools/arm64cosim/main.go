//go:build linux && arm64

// arm64cosim: native side of the ARM64 instruction-semantics co-simulation (issue #552,
// docs/plans/semantics3.md §3 (a)). It executes given instruction words on given machine
// states, natively (under qemu-aarch64-static), and reports the final states; the Lean side
// (GoFV.Arm64) runs the same cases through its semantics and compares.
//
// Protocol (binary, little-endian). stdin: cases until EOF; stdout: one result per case, in
// order.
//
//	case:   u32 nwords (1..8), nwords × u32 instruction words,
//	        state, 256 bytes: initial contents of the memory window WIN
//	result: state after, u32 exit tag, 256 bytes: the window after
//	state:  31 × u64 X0..X30, u64 SP, u64 NZCV (MRS format: N bit 31, Z 30, C 29, V 28, other
//	        bits 0), 32 × 16 bytes V0..V31 (each register low byte first)
//
// Exit tag 0: execution fell through past the last word; 1: it reached the TAKEN landing.
//
// Fixed address layout (the Lean generator relies on these addresses):
//
//	CODE  = 0x40000000, 64 KiB RWX
//	        CODE+0x0000 entry stub
//	TEST  = CODE+0x1000 test words (word i at TEST+4i), then `B exit0` at TEST+4*nwords
//	TAKEN = CODE+0x2000 `B exit1`
//	        CODE+0x3000 exit0 stub (tag 0), CODE+0x4000 exit1 stub (tag 1)
//	        CODE+0x8000 save area, CODE+0x9008 input state, CODE+0xa008 output state + tag
//	WIN   = 0x50000800 (page 0x50000000..0x50001000 mapped RW); the window [WIN, WIN+256) is
//	        written before and read after each case; the rest of the page is not reset.
//
// The generator only produces cases whose memory accesses fall in the window and whose branch
// targets are TEST+4*nwords or TAKEN (BL writes X30 = its own PC+4, which is the generator's
// business). Any other access or target crashes this program.
//
// Mechanism: callCode (tramp_arm64.s) BLRs into the entry stub, which saves Go's SP, X28 (g),
// X29, X30, flushes the test words from the caches, loads Q0-Q31, NZCV, SP and X0-X30 from the
// input block and branches to TEST. An exit stub parks X0 in TPIDR_EL0 (restored by callCode),
// stores X0-X30, SP, NZCV, Q0-Q31 and the tag into the output block, restores Go's registers and
// returns. While the test code runs, Go's registers hold arbitrary values, so no signal must
// arrive: run with GODEBUG=asyncpreemptoff=1 GOMAXPROCS=1 (the GC is switched off here).
//
// Build (GOPATH mode): GO111MODULE=off GOOS=linux GOARCH=arm64 CGO_ENABLED=0 go build -trimpath.
// `arm64cosim -selftest` runs a few hand-made cases and prints PASS/FAIL.
package main

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"errors"
	"flag"
	"fmt"
	"io"
	"math"
	"os"
	"runtime"
	"runtime/debug"
	"syscall"
	"unsafe"
)

func callCode(fn uintptr)

const mapFixedNoreplace = 0x100000

func mmapFixed(addr, size uintptr, prot int) error {
	p, _, errno := syscall.Syscall6(syscall.SYS_MMAP, addr, size, uintptr(prot),
		syscall.MAP_PRIVATE|syscall.MAP_ANON|mapFixedNoreplace, ^uintptr(0), 0)
	if errno != 0 {
		return fmt.Errorf("mmap %#x: %v", addr, errno)
	}
	if p != addr {
		// Kernels before 4.17 ignore MAP_FIXED_NOREPLACE and return another address.
		syscall.Syscall(syscall.SYS_MUNMAP, p, size, 0)
		return fmt.Errorf("mmap %#x: got %#x", addr, p)
	}
	return nil
}

func mem(addr, size uintptr) []byte {
	return unsafe.Slice((*byte)(unsafe.Pointer(addr)), size)
}

var code, win []byte

func setup() error {
	if err := mmapFixed(codeBase, codeSize,
		syscall.PROT_READ|syscall.PROT_WRITE|syscall.PROT_EXEC); err != nil {
		return err
	}
	if err := mmapFixed(memBase, memSize, syscall.PROT_READ|syscall.PROT_WRITE); err != nil {
		return err
	}
	code = mem(codeBase, codeSize)
	win = mem(winAddr, winSize)
	put := func(addr uint64, ws []uint32) {
		for i, w := range ws {
			binary.LittleEndian.PutUint32(code[addr-codeBase+4*uint64(i):], w)
		}
	}
	put(codeBase, entryStub())
	put(takenAdr, []uint32{b(exit1Adr - takenAdr)})
	put(exit0Adr, exitStub(exit0Adr, 0))
	put(exit1Adr, exitStub(exit1Adr, 1))
	return nil
}

// runCase runs words on the state st (wire layout) with window contents w; it fills st and w
// with the final state and window and returns the exit tag.
func runCase(words []uint32, st *[stateSize]byte, w *[winSize]byte) uint32 {
	t := code[testAddr-codeBase:]
	for i, x := range words {
		binary.LittleEndian.PutUint32(t[4*i:], x)
	}
	n := int64(len(words))
	binary.LittleEndian.PutUint32(t[4*n:], b(exit0Adr-(testAddr+4*n)))
	copy(code[inAddr-codeBase:], st[:])
	copy(win, w[:])
	callCode(codeBase)
	copy(st[:], code[outAddr-codeBase:])
	copy(w[:], win)
	return binary.LittleEndian.Uint32(code[outAddr-codeBase+tagOff:])
}

func serve(in io.Reader, out io.Writer) error {
	r := bufio.NewReaderSize(in, 1<<20)
	wr := bufio.NewWriterSize(out, 1<<20)
	var hdr [4]byte
	var wbuf [4 * maxWords]byte
	words := make([]uint32, 0, maxWords)
	var st [stateSize]byte
	var w [winSize]byte
	for ncase := 0; ; ncase++ {
		if _, err := io.ReadFull(r, hdr[:]); err != nil {
			if err == io.EOF {
				break
			}
			return fmt.Errorf("case %d: %v", ncase, err)
		}
		n := binary.LittleEndian.Uint32(hdr[:])
		if n < 1 || n > maxWords {
			return fmt.Errorf("case %d: nwords %d not in 1..%d", ncase, n, maxWords)
		}
		if _, err := io.ReadFull(r, wbuf[:4*n]); err != nil {
			return fmt.Errorf("case %d: %v", ncase, err)
		}
		if _, err := io.ReadFull(r, st[:]); err != nil {
			return fmt.Errorf("case %d: %v", ncase, err)
		}
		if _, err := io.ReadFull(r, w[:]); err != nil {
			return fmt.Errorf("case %d: %v", ncase, err)
		}
		words = words[:0]
		for i := range n {
			words = append(words, binary.LittleEndian.Uint32(wbuf[4*i:]))
		}
		tag := runCase(words, &st, &w)
		binary.LittleEndian.PutUint32(hdr[:], tag)
		wr.Write(st[:])
		wr.Write(hdr[:])
		if _, err := wr.Write(w[:]); err != nil {
			return err
		}
	}
	return wr.Flush()
}

// Self-test.

type state [stateSize]byte

func (s *state) x(i int) uint64       { return binary.LittleEndian.Uint64(s[8*i:]) }
func (s *state) setX(i int, v uint64) { binary.LittleEndian.PutUint64(s[8*i:], v) }
func (s *state) setSP(v uint64)       { binary.LittleEndian.PutUint64(s[spOff:], v) }
func (s *state) setNZCV(v uint64)     { binary.LittleEndian.PutUint64(s[nzcvOff:], v) }
func (s *state) setV(i int, lo, hi uint64) {
	binary.LittleEndian.PutUint64(s[vOff+16*i:], lo)
	binary.LittleEndian.PutUint64(s[vOff+16*i+8:], hi)
}

func regName(off int) string {
	switch {
	case off < spOff:
		return fmt.Sprintf("X%d", off/8)
	case off < nzcvOff:
		return "SP"
	case off < vOff:
		return "NZCV"
	}
	return fmt.Sprintf("V%d", (off-vOff)/16)
}

type testCase struct {
	name  string
	words []uint32
	init  func(s *state, w *[winSize]byte)        // adjusts the base state
	want  func(s *state, w *[winSize]byte) uint32 // adjusts the initial state into the expected one
}

func baseState() (s state, w [winSize]byte) {
	x := uint64(0x9e3779b97f4a7c15)
	next := func() uint64 { x ^= x << 13; x ^= x >> 7; x ^= x << 17; return x }
	for i := range 31 {
		s.setX(i, next())
	}
	s.setSP(next())
	s.setNZCV(0x90000000)
	for i := range 32 {
		s.setV(i, next(), next())
	}
	for i := range w {
		w[i] = byte(next())
	}
	return
}

func selftest() bool {
	const n, z, c, v = 1 << 31, 1 << 30, 1 << 29, 1 << 28
	beq := uint32(0x54000000 | ((takenAdr-testAddr)/4)<<5) // B.EQ TAKEN from TEST
	cases := []testCase{
		{"NOP: every register round-trips", []uint32{0xd503201f},
			func(s *state, w *[winSize]byte) {},
			func(s *state, w *[winSize]byte) uint32 { return 0 }},
		{"ADD X0, X1, X2", []uint32{0x8b020020},
			func(s *state, w *[winSize]byte) { s.setX(1, 5); s.setX(2, 7) },
			func(s *state, w *[winSize]byte) uint32 { s.setX(0, 12); return 0 }},
		{"SUBS X0, X1, X2 (negative)", []uint32{0xeb020020},
			func(s *state, w *[winSize]byte) { s.setX(1, 3); s.setX(2, 5); s.setNZCV(z | v) },
			func(s *state, w *[winSize]byte) uint32 { s.setX(0, ^uint64(1)); s.setNZCV(n); return 0 }},
		{"SUBS X0, X1, X2 (equal)", []uint32{0xeb020020},
			func(s *state, w *[winSize]byte) { s.setX(1, 42); s.setX(2, 42); s.setNZCV(n | v) },
			func(s *state, w *[winSize]byte) uint32 { s.setX(0, 0); s.setNZCV(z | c); return 0 }},
		{"SUBS X0, X1, X2 (signed overflow)", []uint32{0xeb020020},
			func(s *state, w *[winSize]byte) { s.setX(1, 1<<63); s.setX(2, 1); s.setNZCV(0) },
			func(s *state, w *[winSize]byte) uint32 { s.setX(0, 1<<63-1); s.setNZCV(c | v); return 0 }},
		{"LDR X3, [X4]", []uint32{0xf9400083},
			func(s *state, w *[winSize]byte) { s.setX(4, winAddr) },
			func(s *state, w *[winSize]byte) uint32 {
				s.setX(3, binary.LittleEndian.Uint64(w[:]))
				return 0
			}},
		{"STP X1, X2, [X4, #16]", []uint32{0xa9010881},
			func(s *state, w *[winSize]byte) { s.setX(4, winAddr) },
			func(s *state, w *[winSize]byte) uint32 {
				binary.LittleEndian.PutUint64(w[16:], s.x(1))
				binary.LittleEndian.PutUint64(w[24:], s.x(2))
				return 0
			}},
		{"FADD D0, D1, D2", []uint32{0x1e622820},
			func(s *state, w *[winSize]byte) {
				s.setV(1, math.Float64bits(1.5), 0x1111)
				s.setV(2, math.Float64bits(2.25), 0x2222)
			},
			func(s *state, w *[winSize]byte) uint32 { s.setV(0, math.Float64bits(3.75), 0); return 0 }},
		{"B.EQ TAKEN (taken)", []uint32{beq},
			func(s *state, w *[winSize]byte) { s.setNZCV(z) },
			func(s *state, w *[winSize]byte) uint32 { return 1 }},
		{"B.EQ TAKEN (not taken)", []uint32{beq},
			func(s *state, w *[winSize]byte) { s.setNZCV(n | c) },
			func(s *state, w *[winSize]byte) uint32 { return 0 }},
		{"BLR X5", []uint32{0xd63f00a0},
			func(s *state, w *[winSize]byte) { s.setX(5, takenAdr) },
			func(s *state, w *[winSize]byte) uint32 { s.setX(30, testAddr+4); return 1 }},
		{"ADD X0, X1, X2; SUBS X0, X1, X2; LDR X3, [X4]", []uint32{0x8b020020, 0xeb020020, 0xf9400083},
			func(s *state, w *[winSize]byte) { s.setX(1, 9); s.setX(2, 4); s.setX(4, winAddr+8) },
			func(s *state, w *[winSize]byte) uint32 {
				s.setX(0, 5)
				s.setNZCV(c)
				s.setX(3, binary.LittleEndian.Uint64(w[8:]))
				return 0
			}},
	}
	ok := true
	for _, tc := range cases {
		s, w := baseState()
		tc.init(&s, &w)
		got, gotW := s, w
		wantTag := tc.want(&s, &w)
		tag := runCase(tc.words, (*[stateSize]byte)(&got), &gotW)
		var diffs []string
		if tag != wantTag {
			diffs = append(diffs, fmt.Sprintf("tag %d, want %d", tag, wantTag))
		}
		for off := 0; off < stateSize; {
			size := 8
			if off >= vOff {
				size = 16
			}
			if !bytes.Equal(got[off:off+size], s[off:off+size]) {
				diffs = append(diffs, fmt.Sprintf("%s = %x, want %x", regName(off),
					got[off:off+size], s[off:off+size]))
			}
			off += size
		}
		if gotW != w {
			diffs = append(diffs, fmt.Sprintf("window = %x, want %x", gotW, w))
		}
		if len(diffs) == 0 {
			fmt.Printf("PASS %s\n", tc.name)
		} else {
			ok = false
			fmt.Printf("FAIL %s\n", tc.name)
			for _, d := range diffs {
				fmt.Printf("     %s\n", d)
			}
		}
	}
	return ok
}

func main() {
	self := flag.Bool("selftest", false, "run the built-in cases and print PASS/FAIL")
	flag.Parse()
	runtime.LockOSThread()
	debug.SetGCPercent(-1)
	if err := setup(); err != nil {
		fmt.Fprintln(os.Stderr, "arm64cosim:", err)
		os.Exit(1)
	}
	if *self {
		if !selftest() {
			fmt.Println("FAIL")
			os.Exit(1)
		}
		fmt.Println("PASS")
		return
	}
	if err := serve(os.Stdin, os.Stdout); err != nil && !errors.Is(err, syscall.EPIPE) {
		fmt.Fprintln(os.Stderr, "arm64cosim:", err)
		os.Exit(1)
	}
}
