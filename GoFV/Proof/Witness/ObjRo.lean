import GoFV.Proof.Obj.RoReach
import GoFV.Proof.Witness.ObjWhole
import GoFV.SSA.Sem.ConstSym

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: the read-only symbols along a run and in the machine's memory

`pallocSum.start` (`GenG3.lc`, `ObjWhole`): in the Phase 1 test environment `plRunEnv`, whose
global image has the read-only, zero `runtime.writeBarrier` flag and whose contracts keep the
read-only allocations (`plRunEnv_keeps`), `memTyL` accepts the function (compiled evaluation,
`ro_facts`, listed in `scripts/axioms-allowlist.txt`, as are the flag in the image and the constant
symbol below). `lreach_roMem` then gives the flag in the
memory of the state after the entry values (`sI`, `ObjWhole.lc_premises`), and `ro_byte` its
first byte, 0, in the machine's memory `ObjWhole.mm` at `gAddr2`, where `ObjWhole.ι` links it
(`ObjWhole.memInj`). `constSymAlloc?` of `$f64.3ff0000000000000` (the constant 1.0): its eight
bytes, read-only.
-/

namespace GoFV.Proof.Witness.ObjRo

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Proof.Obj GoFV.Proof.Witness.ObjWhole
open GoFV.Proof (enterListLoc)

/-- `plRunEnv`'s write-barrier flag: four zero bytes, read-only. -/
def wbFlag : Alloc := { data := #[.b 0, .b 0, .b 0, .b 0], writable := false }

/-- The read-only allocation of `plRunEnv`'s write-barrier flag. -/
def roWB : List (String × Alloc) := [("runtime.writeBarrier", wbFlag)]

/-- What compiled evaluation checks: `memTyL` accepts `pallocSum.start`, `plRunEnv`'s global
image has the flag, the float constant symbol of 1.0 is its eight little-endian bytes, and the
entry values run to `sI` with the frame memory `memI` (`ObjWhole.sIIs`). -/
def roFacts : Bool :=
  memTyL GenG3.lc && (addGlobals plRunEnv {}).find? (.global "runtime.writeBarrier") == some wbFlag &&
    constSymAlloc? "$f64.3ff0000000000000" == some (roAlloc #[0, 0, 0, 0, 0, 0, 0xf0, 0x3f]) &&
    GenG1.okThen (enterListLoc plRunEnv GenG3.lc (locInit plRunEnv GenG3.lc args {})
      ((blkOf GenG3.lc).values.toList.take 2)) sIIs

theorem ro_facts : roFacts = true := by
  native_decide

theorem ro_facts' : memTyL GenG3.lc = true ∧
    (addGlobals plRunEnv {}).find? (.global "runtime.writeBarrier") = some wbFlag ∧
    constSymAlloc? "$f64.3ff0000000000000" = some (roAlloc #[0, 0, 0, 0, 0, 0, 0xf0, 0x3f]) ∧
    GenG1.okThen (enterListLoc plRunEnv GenG3.lc (locInit plRunEnv GenG3.lc args {})
      ((blkOf GenG3.lc).values.toList.take 2)) sIIs = true := by
  have h := ro_facts
  simp only [roFacts, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem plRunEnv_keepsRo : plRunEnv.KeepsRo := fun name c hc =>
  plRunEnv_keeps Mem.KeepsRo.refl name c hc

theorem roWB_image : RoMem roWB (addGlobals plRunEnv {}) := by
  intro n a h
  simp only [roWB, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, ro_facts'.2.1⟩

/-- **The read-only flag along `pallocSum.start`'s run and in the machine's memory**: after the
entry values, `runLoc`'s memory has `runtime.writeBarrier` read-only (`lreach_roMem`), and the
machine memory holds its first byte at its linked address (`ro_byte`). -/
theorem objRo_witness :
    ∃ sI mmI, enterListLoc plRunEnv GenG3.lc (locInit plRunEnv GenG3.lc args {})
        ((blkOf GenG3.lc).values.toList.take 2) = .ok sI ∧ sI.mem = .mem mmI ∧
      RoMem roWB mmI ∧ mm (gAddr2 + BitVec.ofNat 64 0) = 0 := by
  obtain ⟨sI, hsI, hIs⟩ := GenG1.okThen_spec ro_facts'.2.2.2
  obtain ⟨-, -, -, hmem⟩ := sIIs_spec hIs
  have hro : RoMem roWB memI :=
    lreach_roMem plRunEnv_keepsRo ro_facts'.1 roWB_image hsI (.refl (b0 := 0) (i0 := 0)) hmem
  refine ⟨sI, memI, hsI, hmem, hro, ?_⟩
  exact ro_byte addrAgree memInj hro List.mem_cons_self rfl (i := 0) rfl

/-- The float constant symbol of 1.0: its little-endian bits, read-only. -/
theorem constSym_witness :
    constSymAlloc? "$f64.3ff0000000000000" =
      some (roAlloc #[0, 0, 0, 0, 0, 0, 0xf0, 0x3f]) :=
  ro_facts'.2.2.1

end GoFV.Proof.Witness.ObjRo
