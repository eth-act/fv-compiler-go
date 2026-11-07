#include "textflag.h"

// func callCode(fn uintptr)
// Calls the entry stub at fn. The nonzero frame makes the prologue save LR (and FP); the
// stubs save and restore Go's SP, X28 (g), X29 and X30 themselves. TPIDR_EL0, which the exit
// stubs use as scratch, is saved here and restored after the run.
TEXT ·callCode(SB), NOSPLIT, $16-8
	MOVD	fn+0(FP), R0
	WORD	$0xd53bd041 // MRS X1, TPIDR_EL0
	MOVD	R1, 8(RSP)
	BL	(R0)
	MOVD	8(RSP), R1
	WORD	$0xd51bd041 // MSR TPIDR_EL0, X1
	RET
