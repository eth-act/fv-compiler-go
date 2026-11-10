import GoFV.Proof.Obj.Sim
import GoFV.Proof.Witness.ObjFrame
import GoFV.Proof.Witness.GenG57b2
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witnesses: `DMB` and `PRFM` in `checkObj` (#553)

`checkObj` takes `DMB $k` and `PRFM 0(Rn), $k` as no-ops: `progSym`'s `DMB`/`PRFM` arms (P0, as
`progEffect`'s) and `symAccess` of a `PRFM` word (the machine's `execLdSt`).

* `objBarrier_dmb_witness`: `std/std/runtime/mallocgcSmallNoscanReuse,1.prog` of the corpus
  (`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim as `GenG57b2.fProg`), run through
  the assembler port and the validator as `obj-check` does (`GoFVTest/ObjCheck.lean`, `checkFile`:
  `parseProgFile`, `flush`, P0' by `p0Prime`, `checkObj` on P0', the spills and the port's output).
  By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`, as
  `ObjFrame.obj_facts`; `barrier_facts`), `checkObj` accepts it; its Prog `DMB $14` has the symbolic
  effect `({}, .fall)` and its word decodes to `.barrier 5 14`. `progSym_sound` on that Prog (the
  `DMB` arm) then runs `progStep` from any state to the fall-through with every register kept.
* `objBarrier_prfm_witness`: `PRFM PLDL1KEEP, [X0]` (`0xf9800000`, the word of `scanObject`'s
  `PRFM (R0), $0`) decodes to `.ldst 3 false 2 (.uimm 0) 0 0`, `symInsn` gives `({}, .fall)`, and
  `symInsn_sound` (the `PRFM` case of `symAccess`) runs it from a state with `X0 = 0` (in the nil
  page, where a load faults) to the next word with the memory unchanged; the P0 Prog `PRFM (R0),
  $0` (`progSym`'s `PRFM` arm) has the same effect (`sameEffect`).
-/

namespace GoFV.Proof.Witness.ObjBarrier

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj GoFV.Proof.Obj
open GoFV.Proof.Witness.ObjFrame (isOk getOk eq_getOk)
open GoFV.Asm.ARM64 (REG_R0)

/-- P0' (`p0Prime`), the spills and the port's output of `runtime.mallocgcSmallNoscanReuse` (as
`obj-check`). -/
def objIn : Except String (Array Prog × Array Spill × ObjIn) := do
  let pf ← parseProgFile GenG57b2.fProg.toUTF8
  let out ← flush pf
  let ps ← p0Prime (fun n => out.st.symIdx[(GoFV.SSA.GoStr.ofString n, Obj.ABI0.toNat)]?)
    pf.prog0.progs
  return (ps, pf.prog0.fn.spills,
    { text := out.st.textP, relocs := out.st.textR, progs := out.progs })

def ps : Array Prog :=
  match objIn with
  | .ok x => x.1
  | .error _ => #[]

def spills : Array Spill :=
  match objIn with
  | .ok x => x.2.1
  | .error _ => #[]

def obj : ObjIn :=
  match objIn with
  | .ok x => x.2.2
  | .error _ => ⟨ByteArray.empty, #[], #[]⟩

/-- What `checkObj` returns on `runtime.mallocgcSmallNoscanReuse`. -/
def tab : Tab := getOk (checkObj ps spills obj)

/-- The index of the first `DMB` among the Progs. -/
def jD : Nat := (ps.findIdx? (·.as == .DMB)).getD 0

/-- The `DMB $14`. -/
def pD : Prog := ps[jD]!

/-- The ID layout of the Progs with the frame `az`, `ez`. -/
def L (az ez : Int) : Link := Link.byId (fun _ => 0x100000) 0x10000 az ez ps.toList

/-- What compiled evaluation checks: `checkObj` accepts the function; its Prog `pD` is
`DMB $14`, no skip, with the symbolic effect `({}, .fall)`; its word decodes to `.barrier 5 14`
(`DMB`, `CRm = 14`); and it has a fall-through address in `L`. -/
def barrierFacts : Bool :=
  isOk (checkObj ps spills obj) && pD.as == .DMB && pD.from_.offset == 14 && !pD.isSkip &&
    isOk (progSym tab.autosize tab.extrasize pD) &&
    getOk (progSym tab.autosize tab.extrasize pD) == ({}, .fall) &&
    decode (wordAt obj.text tab.offs[jD]!) == some (.barrier 5 14) &&
    ((L tab.autosize tab.extrasize).nextAddr pD.id).isSome

theorem barrier_facts : barrierFacts = true := by
  native_decide

/-- The facts of `barrier_facts` as hypotheses. -/
theorem facts :
    checkObj ps spills obj = .ok tab ∧ pD.as = .DMB ∧ pD.from_.offset = 14 ∧ pD.isSkip = false ∧
      progSym tab.autosize tab.extrasize pD = .ok ({}, .fall) ∧
      decode (wordAt obj.text tab.offs[jD]!) = some (.barrier 5 14) ∧
      ((L tab.autosize tab.extrasize).nextAddr pD.id).isSome = true := by
  have hf := barrier_facts
  simp only [barrierFacts, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, has⟩, hk⟩, hsk⟩, hpo⟩, hpe⟩, hd⟩, hn⟩ := hf
  exact ⟨eq_getOk hc, has, hk, hsk, by rw [eq_getOk hpo, hpe], hd, hn⟩

/-- `progSym_sound` on `pD` in the layout `L az ez`. -/
private theorem dmb_step {az ez : Int} (hps : progSym az ez pD = .ok ({}, .fall))
    (hsk : pD.isSkip = false) (has : pD.as = .DMB) (hn : ((L az ez).nextAddr pD.id).isSome = true)
    (s : MState) :
    ∃ s', progStep (L az ez) pD s = .ok s' ∧ HoldsCore ⟨s, (L az ez).sym⟩ {} s' ∧
      PcP (L az ez) pD {} s .fall s' := by
  obtain ⟨next, hnx⟩ := Option.isSome_iff_exists.mp hn
  have hs := GoFV.Proof.Gen.progStep_barrier57 (s := s) hnx (.inl has)
  have hL1 : (L az ez).autosize = az := rfl
  have hL2 : (L az ez).extrasize = ez := rfl
  have h := progSym_sound (L := L az ez) hps hL1 hL2 hsk hs
  exact ⟨_, hs, h.2.1, h.2.2⟩

/-- **`checkObj` on a function with `DMB`**: it accepts `runtime.mallocgcSmallNoscanReuse`, whose
`DMB $14` assembles to a barrier word that `symInsn` runs as a no-op; `progSym_sound` on that
Prog runs `progStep` from any state to the fall-through, every register kept. -/
theorem objBarrier_dmb_witness :
    checkObj ps spills obj = .ok tab ∧ pD.as = .DMB ∧
      decode (wordAt obj.text tab.offs[jD]!) = some (.barrier 5 14) ∧
      (∀ o, symInsn (.barrier 5 14) o {} = .ok ({}, .fall)) ∧
      ∀ s : MState, ∃ s', progStep (L tab.autosize tab.extrasize) pD s = .ok s' ∧
        HoldsCore ⟨s, (L tab.autosize tab.extrasize).sym⟩ {} s' ∧
        PcP (L tab.autosize tab.extrasize) pD {} s .fall s' := by
  obtain ⟨hc, has, -, hsk, hps, hd, hn⟩ := facts
  exact ⟨hc, has, hd, fun _ => rfl, dmb_step hps hsk has hn⟩

/-- A machine state with every register `0` (so `X0` points into the nil page), at `0x1000`. -/
def t0 : MState :=
  { x := fun _ => 0, sp := 0x8000, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := 0x1000, mem := fun _ => 0 }

/-- `PRFM PLDL1KEEP, [X0]`, as the assembler encodes `scanObject`'s `PRFM (R0), $0`. -/
def prfmW : BitVec 32 := 0xf9800000

/-- The decoded `PRFM`: a single-register access of size 3 and `opc` 2. -/
def prfm : Insn := .ldst 3 false 2 (.uimm 0) 0 0

/-- `PRFM (R0), $0`. -/
def prfmP : Prog := mkProg 7 .PRFM { type := .MEM, reg := REG_R0 } { type := .CONST }

theorem objBarrier_prfm_witness :
    decode prfmW = some prfm ∧ symInsn prfm 0 {} = .ok ({}, .fall) ∧
      (∃ t', exec prfm t0 = .ok t' ∧ WordsPost ⟨t0, fun _ => 0⟩ 0x1000 0 {} .fall t' ∧
        t'.mem = t0.mem) ∧
      progSym 0 0 prfmP = .ok ({}, .fall) ∧ sameEffect {} {} = .ok () := by
  have h : symInsn prfm 0 {} = .ok ({}, .fall) := rfl
  obtain ⟨t', he, hp⟩ := symInsn_sound (c := ⟨t0, fun _ => 0⟩) (base := 0x1000) h (holds_init _)
    (by simp [t0]) ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
  refine ⟨by decide, h, ⟨t', he, hp, ?_⟩, by rfl, rfl⟩
  rw [hp.1.mem]
  rfl

end GoFV.Proof.Witness.ObjBarrier
