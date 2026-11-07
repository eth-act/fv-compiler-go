import GoFV.Proof.Gen.Basic
import GoFV.Proof.Gen.Branch
import GoFV.Proof.Gen.Mem
import GoFV.Proof.Gen.Spec
import GoFV.Proof.Gen.Step

/-!
# Soundness of the genssa validator's slice G1 (`docs/plans/proofs3.md` §3)

`g1_value`: when `checkG1` accepts a function, every value of a block (other than the entry
values) run by `runLoc` from a state related by `LocMatch` to a machine state is matched by
`runProg` steps of genssa's P0 Progs (laid out by `Link.byId`) to a state related before the next
value. `g1_term`: a terminator that goes to a successor is matched by steps to a state related
before the successor's first value.

The activation (`G1Env`): the PC of value `i` of block `b` is the address of the Prog at index
`tab[b][i]` (`pcOfTab`), `ret` is no Prog's address, `ι` puts every block with a Phase 1 address
there (`AddrAgree`), and the function has no frame. The invariant (`G1Inv`): no stack slot,
every register holds a value of its width class, the memory's block keys are distinct. The
per-step premises (`G1Pre`, `G1TermPre`): the arguments of a compare and the control of a
register test are not pointers without an integer form, and a load reads 8 valid bytes.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## The PC table -/

/-- The address of the Prog at index `j` of `ps` under `Link.byId` (past the end: the fall-through
of the last Prog). -/
def pcAt (text : BitVec 64) (ps : List Prog) (j : Nat) : BitVec 64 :=
  text + BitVec.ofNat 64 (4 * if h : j < ps.length then ps[j].id else maxId ps + 1)

/-- `MatchEnv.pcOf` from `checkG1`'s table: the address of the first Prog of value `i` of block
`b` (`i` = the number of values: of the terminator). -/
def pcOfTab (text : BitVec 64) (ps : List Prog) (tab : PcTab) (b : ID) (i : Nat) : BitVec 64 :=
  pcAt text ps (((tab.lookup b).getD []).getD i 0)

/-! ## The premises -/

/-- The activation of a function `checkG1` accepted with table `tab`. -/
structure G1Env (lc : LocCtx) (L : Link) (ps : Array Prog) (ret : BitVec 64) (tab : PcTab)
    (E : MatchEnv) : Prop where
  lc : E.lc = lc
  link : L = Link.byId L.sym L.text L.autosize L.extrasize ps.toList
  pcOf : E.pcOf = pcOfTab L.text ps.toList tab
  ret : ∀ p ∈ ps.toList, L.addr p.id ≠ some ret
  addr : AddrAgree E.ι
  leaf : E.framed = false

/-- The invariant of G1's `runLoc` states. -/
structure G1Inv (lc : LocCtx) (s : LocState) : Prop where
  slots : s.slots = []
  regs : ∀ r v c, r ≠ zeroReg → s.regs[r]? = some v → regCls lc r = some c → Fits c v
  mem : ∃ mm, s.mem = .mem mm ∧ KeysNodup mm

/-- A register content that is not a pointer without an integer form. -/
def NoBarePtr (x : Val) : Prop := ∀ p, x = .ptr p → (Arm64.ptrReg p).isSome = true

/-- The per-value premises: compare arguments are not pointers without an integer form, a load
reads 8 valid bytes. -/
def G1Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  ((v.op = .ARM64CMP ∨ v.op = .ARM64CMPconst) →
    ∀ a ∈ v.args.toList, ∀ x, s.read lc a = .ok x → NoBarePtr x) ∧
  (v.op = .ARM64MOVDload → ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
    ∃ p mm bs, Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p ∧ s.mem = .mem mm ∧
      mm.read p 8 = some bs)

/-- The per-terminator premise: the control of a register test is not a pointer without an
integer form. -/
def G1TermPre (lc : LocCtx) (s : LocState) (blk : Block) : Prop :=
  (blk.kind = .ARM64Z ∨ blk.kind = .ARM64NZ) →
    ∀ c x, blk.controls[0]? = some c → s.read lc c = .ok x → NoBarePtr x

/-! ## The theorems -/

theorem g1_value {env : Env} {H : Hooks} {lc : LocCtx} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {E : MatchEnv} {bid : ID}
    {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG1 lc ps bstart = .ok tab) (hE : G1Env lc L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp v.op = false) (hm : LocMatch E s bid i m) (hinv : G1Inv lc s)
    (hpre : G1Pre lc s v) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' bid (i + 1) m' ∧ G1Inv lc s' := by
  sorry

theorem g1_term {H : Hooks} {lc : LocCtx} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {E : MatchEnv} {bid : ID}
    {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG1 lc ps bstart = .ok tab) (hE : G1Env lc L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m) (hinv : G1Inv lc s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G1Inv lc s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  sorry

end GoFV.Proof.Gen
