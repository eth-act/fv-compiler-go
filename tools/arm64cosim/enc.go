package main

// Fixed address layout and the hand-encoded stubs (see the comment in main.go). This file
// has no build constraint so that the encoders can be checked on any host.

const (
	codeBase = 0x40000000 // CODE: 64 KiB RWX
	codeSize = 0x10000
	testAddr = codeBase + 0x1000 // test words; word i at testAddr+4i, then `B exit0`
	takenAdr = codeBase + 0x2000 // TAKEN landing: `B exit1`
	exit0Adr = codeBase + 0x3000 // exit stub, tag 0
	exit1Adr = codeBase + 0x4000 // exit stub, tag 1
	saveAddr = codeBase + 0x8000 // Go's SP, X28, X29, X30 while the test code runs
	// Input and output state blocks, in the wire layout (stateSize bytes; the exit stubs also
	// write the tag right after the output state). Placed so that V0 (offset vOff) is 16-byte
	// aligned.
	inAddr  = codeBase + 0x9008
	outAddr = codeBase + 0xa008

	memBase  = 0x50000000 // RW data page
	memSize  = 0x1000
	winAddr  = 0x50000800 // WIN: the 256-byte memory window
	winSize  = 256
	maxWords = 8

	spOff     = 31 * 8      // 248
	nzcvOff   = spOff + 8   // 256
	vOff      = nzcvOff + 8 // 264
	stateSize = vOff + 32*16
	tagOff    = stateSize // offset of the tag in the output block
)

func reg(r int) uint32 {
	if r < 0 || r > 31 {
		panic("bad register")
	}
	return uint32(r)
}

func simm(v int64, bits uint, scale int64) uint32 {
	if v%scale != 0 {
		panic("misaligned immediate")
	}
	v /= scale
	if v < -(1<<(bits-1)) || v >= 1<<(bits-1) {
		panic("immediate out of range")
	}
	return uint32(v) & (1<<bits - 1)
}

func uimm(v int64, bits uint, scale int64) uint32 {
	if v%scale != 0 || v < 0 || v/scale >= 1<<bits {
		panic("unsigned immediate out of range")
	}
	return uint32(v / scale)
}

// Register 31 means SP in ADD (immediate) and as a load/store base, XZR elsewhere.
const sp = 31

// adr encodes ADR Xd, pc+off.
func adr(rd int, off int64) uint32 {
	imm := simm(off, 21, 1)
	return (imm&3)<<29 | 0x10000000 | (imm>>2)<<5 | reg(rd)
}

// addImm encodes ADD Xd|SP, Xn|SP, #imm (MOV to/from SP when imm = 0).
func addImm(rd, rn int, imm int64) uint32 {
	return 0x91000000 | uimm(imm, 12, 1)<<10 | reg(rn)<<5 | reg(rd)
}

// ldpX/stpX: LDP/STP Xt, Xt2, [Xn|SP, #off] (signed offset).
func ldpX(rt, rt2, rn int, off int64) uint32 {
	return 0xa9400000 | simm(off, 7, 8)<<15 | reg(rt2)<<10 | reg(rn)<<5 | reg(rt)
}
func stpX(rt, rt2, rn int, off int64) uint32 {
	return 0xa9000000 | simm(off, 7, 8)<<15 | reg(rt2)<<10 | reg(rn)<<5 | reg(rt)
}

// ldpQ/stpQ: LDP/STP Qt, Qt2, [Xn|SP, #off] (signed offset).
func ldpQ(rt, rt2, rn int, off int64) uint32 {
	return 0xad400000 | simm(off, 7, 16)<<15 | reg(rt2)<<10 | reg(rn)<<5 | reg(rt)
}
func stpQ(rt, rt2, rn int, off int64) uint32 {
	return 0xad000000 | simm(off, 7, 16)<<15 | reg(rt2)<<10 | reg(rn)<<5 | reg(rt)
}

// ldrX/strX: LDR/STR Xt, [Xn|SP, #off] (unsigned offset).
func ldrX(rt, rn int, off int64) uint32 {
	return 0xf9400000 | uimm(off, 12, 8)<<10 | reg(rn)<<5 | reg(rt)
}
func strX(rt, rn int, off int64) uint32 {
	return 0xf9000000 | uimm(off, 12, 8)<<10 | reg(rn)<<5 | reg(rt)
}

func msrNZCV(rt int) uint32  { return 0xd51b4200 | reg(rt) }
func mrsNZCV(rt int) uint32  { return 0xd53b4200 | reg(rt) }
func msrTPIDR(rt int) uint32 { return 0xd51bd040 | reg(rt) }
func mrsTPIDR(rt int) uint32 { return 0xd53bd040 | reg(rt) }
func dcCVAU(rt int) uint32   { return 0xd50b7b20 | reg(rt) }
func icIVAU(rt int) uint32   { return 0xd50b7520 | reg(rt) }

// movz encodes MOVZ Xd, #imm16.
func movz(rd int, imm int64) uint32 { return 0xd2800000 | uimm(imm, 16, 1)<<5 | reg(rd) }

// b encodes B pc+off.
func b(off int64) uint32 { return 0x14000000 | simm(off, 26, 4) }

const (
	dsbISH = 0xd5033b9f
	isb    = 0xd5033fdf
	ret    = 0xd65f03c0
)

// stub accumulates instruction words placed at base.
type stub struct {
	base  uint64
	words []uint32
}

func (s *stub) pc() int64 { return int64(s.base) + 4*int64(len(s.words)) }

func (s *stub) emit(ws ...uint32) { s.words = append(s.words, ws...) }

func (s *stub) adr(rd int, target uint64) { s.emit(adr(rd, int64(target)-s.pc())) }

func (s *stub) b(target uint64) { s.emit(b(int64(target) - s.pc())) }

// entryStub is called (BLR) from callCode with Go's state in SP, X28, X29, X30. It saves those,
// makes the test words visible to instruction fetch, loads the whole input state and branches
// to TEST.
func entryStub() []uint32 {
	s := &stub{base: codeBase}
	s.adr(16, saveAddr)
	s.emit(addImm(17, sp, 0), stpX(17, 28, 16, 0), stpX(29, 30, 16, 16))
	// The test words span at most 9 words (36 bytes) from the 64-byte aligned TEST; clean and
	// invalidate them for any cache line size >= 16.
	s.adr(16, testAddr)
	for _, k := range []int64{0, 16, 32} {
		s.emit(addImm(17, 16, k), dcCVAU(17))
	}
	s.emit(dsbISH)
	for _, k := range []int64{0, 16, 32} {
		s.emit(addImm(17, 16, k), icIVAU(17))
	}
	s.emit(dsbISH, isb)
	s.adr(17, inAddr+vOff)
	for q := 0; q < 32; q += 2 {
		s.emit(ldpQ(q, q+1, 17, int64(q)*16))
	}
	s.adr(16, inAddr)
	s.emit(ldrX(17, 16, nzcvOff), msrNZCV(17))
	s.emit(ldrX(17, 16, spOff), addImm(sp, 17, 0))
	for x := 2; x < 30; x += 2 {
		if x != 16 {
			s.emit(ldpX(x, x+1, 16, int64(x)*8))
		}
	}
	s.emit(ldrX(30, 16, 30*8))
	s.emit(addImm(0, 16, 0), ldpX(16, 17, 0, 16*8), ldpX(0, 1, 0, 0))
	s.b(testAddr)
	return s.words
}

// exitStub stores the whole state and the tag into the output block, restores Go's SP, X28,
// X29, X30 and returns to callCode. TPIDR_EL0 holds X0 meanwhile (callCode restores it).
func exitStub(base uint64, tag int64) []uint32 {
	s := &stub{base: base}
	s.emit(msrTPIDR(0))
	s.adr(0, outAddr)
	s.emit(strX(1, 0, 8))
	for x := 2; x < 30; x += 2 {
		s.emit(stpX(x, x+1, 0, int64(x)*8))
	}
	s.emit(strX(30, 0, 30*8))
	s.emit(addImm(1, sp, 0), strX(1, 0, spOff))
	s.emit(mrsNZCV(1), strX(1, 0, nzcvOff))
	s.emit(mrsTPIDR(1), strX(1, 0, 0))
	s.adr(1, outAddr+vOff)
	for q := 0; q < 32; q += 2 {
		s.emit(stpQ(q, q+1, 1, int64(q)*16))
	}
	s.emit(movz(1, tag), strX(1, 0, tagOff))
	s.adr(0, saveAddr)
	s.emit(ldpX(1, 28, 0, 0), addImm(sp, 1, 0), ldpX(29, 30, 0, 16), ret)
	return s.words
}
