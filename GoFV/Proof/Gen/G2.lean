import GoFV.Proof.Gen.Stack
import GoFV.Proof.Gen.Progs2
import GoFV.Proof.Gen.Spec2

/-!
# Soundness of the genssa validator's slice G2 (`docs/plans/proofs3.md` §4)

`g2_value`: when `checkG2` accepts a function, every value of a block (other than the entry
values) run by `runLoc` from a state related by `LocMatch` to a machine state is matched by
`runProg` steps of genssa's P0 Progs (laid out by `Link.byId`, P0's `CALL sym(SB)` going to the
symbol) to a state related before the next value, under an injection that grows only at a call.
`g2_term`: a terminator that goes to a successor is matched by steps to a state related before the
successor's first value (an `Exit` block never does).

The activation (`G2Env`): G1's premises, but with a frame (`framed` when the function calls),
globals at their linked symbol addresses under `ι`, the callees' symbols outside the Prog list,
each spill slot at its frame operand (`frameOff`), and the frame layout `FrameOK`. The invariant
(`G2Inv`): G1's register classes and distinct block keys, the live blocks away from the saved
`LR`/`FP` words and the spill slots (`CoreInv … (StkAt E)`), and every live slot a 64-bit value of a
home slot.

A call runs the callee through the runtime hook `H.call`. Its behaviour is the trusted callee
contract of semantics3 §6 (the hook lifts the callee's Phase 1 contract through the ABI), assumed
at each call (`CallOK`, `CallSpec`, listed in `docs/proofs/STATUS.md` Assumptions): from the state
at the callee's entry whose ABI argument registers hold the arguments `runLoc` passes and whose
memory injects `runLoc`'s, the hook returns to `X30` with `SP`, `R28`, `R29` and the frame's saved
words and slots kept, `runLoc`'s results in the ABI result registers and its memory injected by a
larger injection. What the compiled code must do for that (the arguments in their ABI registers,
the results homed there, the `CALL` of the callee's symbol with the return address in `X30`, the
frame kept apart from the live blocks) is proven here from what `checkG2` accepted.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## The premises -/

/-- The activation of a function `checkG2` accepted with table `tab`. -/
structure G2Env (lc : LocCtx) (g : G2In) (L : Link) (ps : Array Prog) (ret : BitVec 64)
    (tab : PcTab) (E : MatchEnv) : Prop where
  lcEq : E.lc = lc
  link : L = Link.byId L.sym L.text L.autosize L.extrasize ps.toList
  pcOf : E.pcOf = pcOfTab L.text ps.toList tab
  retOut : ∀ p ∈ ps.toList, L.addr p.id ≠ some ret
  addr : AddrAgree E.ι
  /-- A global sits at its linked symbol address. -/
  glob : ∀ y name abi, g.syms[y]? = some (name, abi) →
    E.ι (.global name.toStringLossy) = some (L.sym y)
  /-- Symbols (callees) are neither Prog addresses nor the return address. -/
  syms : ∀ y, L.sym y ≠ ret ∧ ∀ p ∈ ps.toList, L.addr p.id ≠ some (L.sym y)
  /-- A function that calls has a frame. -/
  calls : E.framed = false → ∀ id v, lc.ctx.f.value? id = some v → v.op ≠ .ARM64CALLstatic
  /-- Each spill slot at its frame operand. -/
  slot : ∀ k nc off, g.slotOp k = some (nc, off) → E.slot k = some (frameOff L nc off)
  extra : 0 ≤ L.extrasize
  frame : FrameOK E

/-- The invariant of G2's `runLoc` states. -/
structure G2Inv (E : MatchEnv) (lc : LocCtx) (s : LocState) : Prop where
  core : CoreInv E.ι (StkAt E) lc s
  slots : ∀ k v, s.slots.lookup k = some v → Fits 64 v ∧ ∃ i, lc.home i = some (.slot k)

/-- A Go register and the machine: its X or V register holds the value. -/
def RegRel (ι : Blk → Option (BitVec 64)) (x : Val) (m : MState) (r : Nat) : Prop :=
  (∀ k, objX? r = some k → ValRel ι x (m.x k)) ∧ (∀ k, objV? r = some k → FValRel x (m.v k))

/-- **The callee contract at a static call** (trusted, semantics3 §6; `docs/proofs/STATUS.md`
Assumptions): from the machine state `m` at the callee's entry, if the ABI argument registers
`ins` hold the arguments `args` and the memory injects `runLoc`'s memory `mm` (distinct keys, the
live blocks away from the frame), the hook returns to `X30` with `SP`, `R28`, `R29` and the frame
(`StkAt`) kept, the memory of `runLoc`'s state after the call `s'` injected by an extension of
`ι` that still puts Phase 1's blocks at their addresses, and the registers of `s'` in the ABI
result registers `outs`. -/
def CallSpec (H : Hooks) (E : MatchEnv) (ins outs : List Nat) (args : List Val) (mm : Mem)
    (s' : LocState) (m : MState) : Prop :=
  args.length = ins.length →
    (∀ (j r : Nat) (x : Val), ins[j]? = some r → args[j]? = some x → RegRel E.ι x m r) →
    MemInj E.ι mm m.mem → KeysNodup mm → SepFrom E.ι (StkAt E) mm →
  ∃ ι' m' mm', H.call m = some (.ret m') ∧ (∀ b a, E.ι b = some a → ι' b = some a) ∧
    AddrAgree ι' ∧ m'.pc = m.x 30 ∧ m'.sp = m.sp ∧ m'.x 28 = m.x 28 ∧ m'.x 29 = m.x 29 ∧
    (∀ y, StkAt E y → m'.mem y = m.mem y) ∧
    s'.mem = .mem mm' ∧ MemInj ι' mm' m'.mem ∧ KeysNodup mm' ∧ SepFrom ι' (StkAt E) mm' ∧
    ∀ r ∈ outs, ∀ x, s'.regs[r]? = some x → RegRel ι' x m' r

/-- The callee contract (`CallSpec`) at the static call `v` from `s` (to `s'`), at every machine
state at the callee's symbol that is `m` but for `X30`. -/
def CallOK (H : Hooks) (E : MatchEnv) (g : G2In) (L : Link) (lc : LocCtx) (s s' : LocState)
    (v : Value) (m : MState) : Prop :=
  v.op = .ARM64CALLstatic → ∀ name abi cabi ins outs y args mm (m₁ : MState),
    callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) → callRegs cabi = .ok (ins, outs) →
    g.syms[y]? = some (name, abi) →
    args.length = v.args.toList.dropLast.length →
    (∀ (j : Nat) (a : ID) (x : Val), v.args.toList.dropLast[j]? = some a → args[j]? = some x →
      s.read lc a = .ok x) →
    s.mem = .mem mm → m₁.pc = L.sym y → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv →
    m₁.mem = m.mem → (∀ k, k ≠ 30 → m₁.x k = m.x k) → CallSpec H E ins outs args mm s' m₁

/-! ## `runLoc` -/

section Loc

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

theorem lookup_filter {α β : Type} [DecidableEq α] (p : α × β → Bool)
    (hp : ∀ a b b', p (a, b) = p (a, b')) {k : α} {x : β} :
    ∀ l : List (α × β), (l.filter p).lookup k = some x → l.lookup k = some x
  | [], h => h
  | (k1, v1) :: l, h => by
    by_cases hq : p (k1, v1) = true
    · rw [List.filter_cons_of_pos hq] at h
      simp only [List.lookup] at h ⊢
      split at h
      · exact h
      · exact lookup_filter p hp l h
    · rw [List.filter_cons_of_neg hq] at h
      simp only [List.lookup]
      split
      · rename_i hk
        have hk' : k = k1 := by simpa using hk
        subst hk'
        have : ∀ l : List (α × β), (l.filter p).lookup k = none := by
          intro l
          induction l with
          | nil => rfl
          | cons e l ih =>
            obtain ⟨e1, e2⟩ := e
            by_cases he : p (e1, e2) = true
            · rw [List.filter_cons_of_pos he]
              simp only [List.lookup]
              split
              · rename_i hk2
                have : k = e1 := by simpa using hk2
                subst this
                rw [hp k e2 v1] at he; exact absurd he hq
              · exact ih
            · rw [List.filter_cons_of_neg he]; exact ih
        rw [this] at h; cases h
      · exact lookup_filter p hp l h

/-- A slot after `setSlot`: the slot written, or an old slot (one the write did not kill). -/
theorem lookup_setSlot {tabs : Tables} {k k' : SlotKey} {x v : Val}
    (h : (s.setSlot tabs k x).slots.lookup k' = some v) :
    (k' = k ∧ v = x) ∨ (k' ≠ k ∧ s.slots.lookup k' = some v) := by
  simp only [LocState.setSlot, List.lookup] at h
  split at h
  · rename_i hk
    left; exact ⟨by simpa using hk, (Option.some.inj h).symm⟩
  · rename_i hk
    right
    exact ⟨by simpa using hk, lookup_filter _ (fun _ _ _ => rfl) _ h⟩

theorem setSlot_lookup_self {tabs : Tables} {k : SlotKey} {x : Val} :
    (s.setSlot tabs k x).slots.lookup k = some x := by
  simp [LocState.setSlot, List.lookup]

/-- The value of a slot home. -/
theorem read_slot {a : ID} {k : SlotKey} (hl : lc.ctx.f.lowered = true)
    (hh : lc.home a = some (.slot k)) :
    s.read lc a = .ok (((s.slots.lookup k).getD .poison).retypeL (lc.ty a)) := by
  unfold LocState.read LocState.raw
  rw [hh]; simp only [lmode_retype hl]
  rfl

theorem write_slot {id : ID} {k : SlotKey} {x : Val} (hh : lc.home id = some (.slot k)) :
    s.write lc id x = s.setSlot lc.ctx.tabs k x := by
  unfold LocState.write; rw [hh]

/-- `StoreReg`/`LoadReg`: the argument moved to the value's home at the value's shape. -/
theorem stepLoc_move (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .StoreReg ∨ v.op = .LoadReg) {a : ID} (ha : v.args = #[a])
    (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a = .ok x ∧ s' = s.write lc v.id (x.retypeL (lc.ty v.id)) := by
  have hne : (v.op == Op.Phi) = false := by rcases hop with h | h <;> rw [h] <;> rfl
  unfold stepLoc at h
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
  rw [ha] at h
  change ((s.read lc a).bind fun x => Res.ok [x]) >>= _ = _ at h
  cases hx : s.read lc a with
  | ok x =>
    rw [hx] at h
    have hc : s.clobber lc v = s := by
      rcases hop with hop | hop <;>
        exact clobber_none (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) ht (by rw [hop]; rfl)
    rcases hop with hop | hop <;>
    · simp only [bind, Res.bind, hop] at h
      cases h
      exact ⟨x, rfl, by rw [hc, lmode_retype hl]⟩
  | panic e m => rw [hx] at h; cases h
  | stuck msg => rw [hx] at h; cases h

/-- `SelectN [i]` of one argument. -/
theorem stepLoc_selectN (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .SelectN) {a : ID} (ha : v.args = #[a]) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a = .ok x ∧
      s' = s.write lc v.id ((Tuple.selectN v.auxInt [x]).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hm
  change ((s.read lc a).bind fun x => Res.ok [x]) = _ at hm
  cases hx : s.read lc a with
  | ok x =>
    rw [hx] at hm; cases hm
    have he : evalOpL true env lc.ctx s.fr v [x] (lc.ty v.id) = .ok (Tuple.selectN v.auxInt [x]) := by
      unfold evalOpL evalOp frameVal; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨_, rfl, rfl⟩
  | panic e m => rw [hx] at hm; cases hm
  | stuck msg => rw [hx] at hm; cases hm

/-- The symbol of a global aux. -/
theorem symAddr_global {ctx : Ctx} {x : AuxRef} {name : GoStr} {abi : Nat} {a : Val}
    (hs : symOf? ctx.tabs x = some (name, abi)) (hx : v.aux = some x) :
    symAddr ctx v a = some ⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt⟩ := by
  unfold symOf? at hs
  unfold symAddr
  rw [hx]
  split at hs
  · rename_i n ab _ _ hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    simp [hd]
  · cases hs

/-- `MOVDaddr` of a global: the pointer to the global at the offset, at the value's shape. -/
theorem stepLoc_addr (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64MOVDaddr) {a x : Nat} {name : GoStr} {abi : Nat} (ha : v.args = #[a])
    (hx : v.aux = some x) (hs : symOf? lc.ctx.tabs x = some (name, abi))
    (h : stepLoc env lc s v = .ok s') :
    s' = s.write lc v.id ((PtrOps.ptrRes ⟨.global name.toStringLossy,
      BitVec.ofInt 64 v.auxInt.toInt⟩).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hm
  change ((s.read lc a).bind fun x => Res.ok [x]) = _ at hm
  cases hy : s.read lc a with
  | ok y =>
    rw [hy] at hm; cases hm
    have he : evalOpL true env lc.ctx s.fr v [y] (lc.ty v.id) =
        match nilFaults true lc.ctx v [y] with
        | some m => .panic .nilDeref m
        | none => .ok ((symAddr lc.ctx v y).elim .poison PtrOps.ptrRes) := by
      unfold evalOpL arm64Op; rw [hop]; rfl
    rw [he] at hr
    split at hr
    · cases hr
    · cases hr
      rw [symAddr_global hs hx]
      rfl
  | panic e m => rw [hy] at hm; cases hm
  | stuck msg => rw [hy] at hm; cases hm

/-- What a successful step of a non-`Phi`, non-move op writes. -/
theorem stepLoc_call (hl : lc.ctx.f.lowered = true) (hop : v.op = .ARM64CALLstatic)
    (h : stepLoc env lc s v = .ok s') :
    ∃ r : Val, s' = (s.clobber lc v).write lc v.id (r.retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, -, -, rfl⟩ := stepLoc_ok_eval (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) h
  exact ⟨r, by rw [lmode_retype hl]⟩

/-! ### Tuples of a call -/

theorem cls_notFlags {t : Ty} (h : (cls t).isSome = true) : t.isFlags = false := by
  cases t <;> simp_all [Gen.Check.cls, Ty.isFlags]

theorem cls_notMem {t : Ty} (h : (cls t).isSome = true) : memTy t = false := by
  cases t <;> simp_all [Gen.Check.cls, memTy]

theorem writeParts_slots : ∀ (ts : List Ty) (xs : List Val) (rs : List (Option Nat)) (s : LocState),
    (s.writeParts ts xs rs).slots = s.slots
  | [], _, _, _ => by simp [LocState.writeParts]
  | _ :: _, [], _, _ => by simp [LocState.writeParts]
  | t :: ts, x :: xs, rs, s => by
    unfold LocState.writeParts
    split
    · exact writeParts_slots ts xs rs _
    · split
      · exact writeParts_slots ts xs rs _
      · split
        · rw [writeParts_slots]; rfl
        · exact writeParts_slots ts xs _ _
        · exact writeParts_slots ts xs _ _

theorem writeParts_flags : ∀ (ts : List Ty) (xs : List Val) (rs : List (Option Nat)) (s : LocState),
    (∀ t ∈ ts, t.isFlags = false) → (s.writeParts ts xs rs).flags = s.flags
  | [], _, _, _, _ => by simp [LocState.writeParts]
  | _ :: _, [], _, _, _ => by simp [LocState.writeParts]
  | t :: ts, x :: xs, rs, s, h => by
    have ih := fun rs s => writeParts_flags ts xs rs s (fun t ht => h t (by simp [ht]))
    unfold LocState.writeParts
    split
    · exact ih _ _
    · split
      · rename_i hf; rw [h t (by simp)] at hf; cases hf
      · split
        · rw [ih]; rfl
        · exact ih _ _
        · exact ih _ _

/-- The registers after a call's results are written: unchanged, or result `j` in register
`outs[j]`. -/
theorem writeParts_call : ∀ (ts : List Ty) (xs : List Val) (outs : List Nat) (s : LocState),
    (∀ t ∈ ts, (cls t).isSome = true) → ts.length = outs.length →
    ∀ r v, (s.writeParts (ts ++ [.mem]) xs (outs.map some)).regs[r]? = some v →
      s.regs[r]? = some v ∨ ∃ (j : Nat) (t : Ty), ts[j]? = some t ∧ outs[j]? = some r ∧
        xs[j]? = some v
  | [], xs, outs, s, _, hlen, r, v, h => by
    left
    cases xs with
    | nil => simpa [LocState.writeParts] using h
    | cons x xs => simpa [LocState.writeParts] using h
  | t :: ts, xs, outs, s, hc, hlen, r, v, h => by
    obtain ⟨o, outs, rfl⟩ : ∃ o outs', outs = o :: outs' := by
      cases outs with
      | nil => simp at hlen
      | cons o outs => exact ⟨o, outs, rfl⟩
    cases xs with
    | nil => left; simpa [LocState.writeParts] using h
    | cons x xs =>
      have hct := hc t (by simp)
      have hm : memTy t = false := cls_notMem hct
      have hf : t.isFlags = false := cls_notFlags hct
      have hw : s.writeParts (t :: ts ++ [.mem]) (x :: xs) ((o :: outs).map some) =
          (s.setReg o x).writeParts (ts ++ [.mem]) xs (outs.map some) := by
        cases t <;> simp_all [LocState.writeParts, memTy]
      rw [hw] at h
      rcases writeParts_call ts xs outs (s.setReg o x) (fun t ht => hc t (by simp [ht]))
        (by simpa using hlen) r v h with h' | ⟨j, t', h1, h2, h3⟩
      · simp only [LocState.setReg] at h'
        split at h'
        · rename_i hlt
          rw [Array.set!_eq_setIfInBounds] at h'
          by_cases hro : r = o
          · subst hro
            rw [Array.getElem?_setIfInBounds_self_of_lt (by simp at hlt; exact hlt.1)] at h'
            right; exact ⟨0, t, rfl, rfl, by simpa using h'⟩
          · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hro)] at h'
            left; exact h'
        · left; exact h'
      · right; exact ⟨j + 1, t', by simpa using h1, by simpa using h2, by simpa using h3⟩

theorem replicate_get {α : Type} {n j : Nat} {a x : α} (h : (List.replicate n a)[j]? = some x) :
    x = a := by
  rw [List.getElem?_replicate] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem retypePre_get : ∀ (ts : List Ty) (ws ws' : List Val), Val.retypePre ts ws = some ws' →
    ∀ (j : Nat) (t : Ty) (x : Val), ts[j]? = some t → ws'[j]? = some x →
      ∃ w : Val, ws[j]? = some w ∧ x = w.retype t
  | [], ws, ws', h, j, t, x, ht, _ => by simp at ht
  | t0 :: ts, [], ws', h, _, _, _, _, _ => by simp [Val.retypePre] at h
  | t0 :: ts, w :: ws, ws', h, j, t, x, ht, hx => by
    simp only [Val.retypePre, Option.map_eq_some_iff] at h
    obtain ⟨ws'', h', rfl⟩ := h
    cases j with
    | zero =>
      simp at ht hx; subst ht; subst hx; exact ⟨w, rfl, rfl⟩
    | succ j =>
      simp at ht hx
      obtain ⟨w', h1, h2⟩ := retypePre_get ts ws ws'' h' j t x ht hx
      exact ⟨w', by simpa using h1, h2⟩

theorem widenList_get : ∀ (ts : List Ty) (vs : List Val) (j : Nat) (t : Ty) (w : Val),
    ts[j]? = some t → (Val.widenList ts vs)[j]? = some w → ∃ x : Val, vs[j]? = some x ∧ w = x.widen t
  | [], vs, j, t, w, ht, _ => by simp at ht
  | t0 :: ts, [], j, t, w, _, hw => by simp [Val.widenList] at hw
  | t0 :: ts, v :: vs, j, t, w, ht, hw => by
    cases j with
    | zero => simp [Val.widenList] at ht hw; subst ht; subst hw; exact ⟨v, rfl, rfl⟩
    | succ j =>
      simp [Val.widenList] at ht hw
      obtain ⟨x, h1, h2⟩ := widenList_get ts vs j t w ht hw
      exact ⟨x, by simpa using h1, h2⟩

/-- A component of a tuple read at a tuple shape: its element read at the component's shape (or
`poison`). -/
theorem tuple_get {ts : List Ty} {r : Val} {j : Nat} {t : Ty} {x : Val} (ht : ts[j]? = some t)
    (hx : ((Val.retypeL (.tuple ts) r).partsOf ts.length)[j]? = some x) :
    x = .poison ∨ ∃ y : Val, (match r with | .tuple vs => vs[j]? | _ => none) = some y ∧
      x = y.retypeL t := by
  cases r with
  | tuple vs =>
    simp only [Val.retypeL, Val.widen, Val.retype] at hx
    split at hx
    · rename_i ws' hw
      simp only [Val.partsOf] at hx
      obtain ⟨w, hw1, rfl⟩ := retypePre_get ts _ ws' hw j t x ht hx
      obtain ⟨y, hy, rfl⟩ := widenList_get ts vs j t w ht hw1
      exact Or.inr ⟨y, hy, rfl⟩
    · left; simp only [Val.partsOf] at hx; exact replicate_get hx
  | _ =>
    left
    simp only [Val.retypeL, Val.widen, Val.retype, Val.partsOf] at hx
    exact replicate_get hx

theorem fits_tuple_get {ts : List Ty} {r : Val} {j : Nat} {t : Ty} {x : Val} {c : Nat}
    (ht : ts[j]? = some t) (hc : cls t = some c)
    (hx : ((Val.retypeL (.tuple ts) r).partsOf ts.length)[j]? = some x) : Fits c x := by
  rcases tuple_get ht hx with rfl | ⟨y, -, rfl⟩
  · trivial
  · exact fits_retypeL hc y

theorem readParts_cons {s : LocState} {t : Ty} (hm : memTy t = false) (hf : t.isFlags = false)
    (rest : List Ty) (rs : List (Option Nat)) :
    s.readParts (t :: rest) rs =
      (match rs with | some r :: _ => s.reg t r | _ => .poison) :: s.readParts rest rs.tail := by
  rcases rs with _ | ⟨_ | r, rs⟩ <;> cases t <;> simp_all [LocState.readParts, memTy]

/-- The components of a call's tuple read from its home: result `j` the register `outs[j]`, the
memory last. -/
theorem readParts_call : ∀ (ts : List Ty) (rs : List (Option Nat)) (s : LocState),
    (∀ t ∈ ts, (cls t).isSome = true) →
    (s.readParts (ts ++ [.mem]) rs).length = ts.length + 1 ∧
    (s.readParts (ts ++ [.mem]) rs)[ts.length]? = some s.mem ∧
    ∀ (j : Nat) (t : Ty) (r : Nat), ts[j]? = some t → rs[j]? = some (some r) →
      (s.readParts (ts ++ [.mem]) rs)[j]? = some (s.reg t r)
  | [], rs, s, _ => by simp [LocState.readParts]
  | t :: ts, rs, s, hc => by
    have hct := hc t (by simp)
    have hm : memTy t = false := cls_notMem hct
    have hf : t.isFlags = false := cls_notFlags hct
    have hstep : s.readParts (t :: ts ++ [.mem]) rs =
        (match rs with | some r :: _ => s.reg t r | _ => .poison) ::
          s.readParts (ts ++ [.mem]) rs.tail := by
      rw [List.cons_append]; exact readParts_cons hm hf _ rs
    have ih := readParts_call ts rs.tail s (fun t ht => hc t (by simp [ht]))
    rw [hstep]
    refine ⟨?_, ?_, fun j t' r ht' hr => ?_⟩
    · rw [List.length_cons, ih.1, List.length_cons]
    · simp only [List.length_cons, List.getElem?_cons_succ]; exact ih.2.1
    · cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ht' ⊢
        subst ht'
        rcases rs with _ | ⟨r0, rs⟩
        · simp at hr
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
          subst hr; rfl
      | succ j =>
        simp only [List.getElem?_cons_succ] at ht' ⊢
        refine ih.2.2 j t' r ht' ?_
        rcases rs with _ | ⟨r0, rs⟩
        · simp at hr
        · simpa using hr

end Loc

/-! ## The machine side -/

section Machine

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s : LocState} {b : ID} {i : Nat} {m : MState}

/-- `OneAt2` on the list: no-ops from `j` up to the Prog at `k` matching `pat`, `j' = k + 1`. -/
theorem pstar_oneAt2 (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {j j' : Nat} {pat : Pat} (h : OneAt2 psA j pat j') (m : MState) :
    ∃ k, j' = k + 1 ∧ ∃ hk : k < psA.toList.length, pat.ok psA.toList[k] = true ∧
      PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } { m with pc := pcAt text psA.toList k } := by
  obtain ⟨k, hjk, rfl, hk, hok, hno⟩ := h
  refine ⟨k, rfl, by simpa using hk, by simpa using hok, ?_⟩
  exact pstar_noops hnd hlt hret hjk (by simp; omega)
    (fun l hl h1 h2 => by simpa using hno l (by simpa using hl) h1 h2) m

/-- A value whose one Prog writes its register (G1's `op_reg` for a G2 pattern). -/
theorem op_reg2 {P : BitVec 64 → Prop} (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P lc s) {j j' : Nat}
    (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {pat : Pat} (hone : OneAt2 psA j pat j')
    {vid r c kd : Nat} {x : Val} {val : BitVec 64}
    (hh : lc.home vid = some (.reg r)) (hc : cls (lc.ty vid) = some c) (hd : destOK r = true)
    (hkd : kd < 32) (hrk : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + kd))
    (hx : ValRel E.ι x val) (hfx : Fits c x)
    (hstep : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m.wX (BitVec.ofNat 5 kd) val with pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E (s.setReg r x) b (i + 1) m' ∧ CoreInv E.ι P lc (s.setReg r x) := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hone m
  rw [pc_eta hm hj] at hstar
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv (F.home vid r hh) hh hc hd hkd hrk hx hfx
    (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl (hstep k hk hok)), hlm, hinv'⟩

theorem progAt?_none {L : Link} {ps : List Prog} {pc : BitVec 64}
    (h : ∀ p ∈ ps, L.addr p.id ≠ some pc) : progAt? L ps pc = none := by
  unfold progAt?
  rw [List.find?_eq_none]
  intro p hp
  simp [h p hp]

end Machine

/-! ## Frame facts from `checkFrame` -/

/-- Two distinct home slots lie 8 bytes apart. -/
theorem slot_apart {lc : LocCtx} {g : G2In} {L : Link} {E : MatchEnv}
    (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k nc off, g.slotOp k = some (nc, off) → E.slot k = some (frameOff L nc off))
    (hext : 0 ≤ L.extrasize) {k k' : SlotKey} (hk : k ∈ homeSlots lc) (hk' : k' ∈ homeSlots lc)
    (hne : k ≠ k') {o o' : Int} (ho : E.slot k = some o) (ho' : E.slot k' = some o') :
    o + 8 ≤ o' ∨ o' + 8 ≤ o := by
  obtain ⟨hok, hdis⟩ := checkFrame_spec hcf
  have h1 := hok k hk
  have h2 := hok k' hk'
  have hd := hdis k hk k' hk' hne
  obtain ⟨⟨nc, off⟩, hs⟩ : ∃ p, g.slotOp k = some p := by
    cases h : g.slotOp k with
    | none => simp [slotOK, h] at h1
    | some p => exact ⟨p, rfl⟩
  obtain ⟨⟨nc', off'⟩, hs'⟩ : ∃ p, g.slotOp k' = some p := by
    cases h : g.slotOp k' with
    | none => simp [slotOK, h] at h2
    | some p => exact ⟨p, rfl⟩
  rw [hslot k nc off hs] at ho
  rw [hslot k' nc' off' hs'] at ho'
  cases ho; cases ho'
  rw [hs, hs'] at hd
  simp only [slotOK, hs, hs', Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1 h2
  cases nc <;> cases nc' <;> simp_all [frameOff] <;> omega

/-- `StkAt`: the window of a spill slot is in it, the window of another home slot is not. -/
theorem slot_windows_apart {E : MatchEnv} (hF : FrameOK E) {k k' : SlotKey} {o o' : Int}
    (ho : E.slot k = some o) (ho' : E.slot k' = some o') (hap : o + 8 ≤ o' ∨ o' + 8 ≤ o)
    {j j' : Nat} (hj : j < 8) (hj' : j' < 8) :
    E.sp + BitVec.ofInt 64 o' + BitVec.ofNat 64 j' ≠ E.sp + BitVec.ofInt 64 o + BitVec.ofNat 64 j := by
  obtain ⟨h8, hhi⟩ := hF.slot k o ho
  obtain ⟨h8', hhi'⟩ := hF.slot k' o' ho'
  intro he
  have := congrArg BitVec.toNat he
  rw [win_toNat (by omega) hhi' hj', win_toNat (by omega) hhi hj] at this
  omega

/-- A home slot that `checkFrame` accepted: 8 bytes at its `runLoc` shape, a frame operand of
the locals or the parameters. -/
theorem home_slot {lc : LocCtx} {g : G2In} (hcf : checkFrame lc g = .ok ()) {i : Nat} {k : SlotKey}
    (hh : lc.home i = some (.slot k)) :
    (lc.slotTy k).size = 8 ∧ ∃ nc off, g.slotOp k = some (nc, off) ∧ (nc = .AUTO ∨ nc = .PARAM) := by
  have h := (checkFrame_spec hcf).1 k (mem_homeSlots hh)
  unfold slotOK at h
  cases hs : g.slotOp k with
  | none => simp [hs] at h
  | some p =>
    obtain ⟨nc, off⟩ := p
    simp only [hs, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨h.1.2, nc, off, rfl, ?_⟩
    cases nc <;> simp_all

theorem homeOK_of_2 {lc : LocCtx} (h : ∀ i, homeOK2 lc i = true) :
    ∀ i r, lc.home i = some (.reg r) → homeOK lc i = true := by
  intro i r hh
  have := h i
  simp only [homeOK2, hh] at this
  exact this

theorem vstep_v2 {ps : Array Prog} {kd : VKind} {j j' : Nat} (h : VStep2 ps kd.v2 j j') :
    VStep ps kd j j' := by
  cases kd <;> exact h

theorem fits_word (p : Ptr) : Fits 64 p.word := by
  unfold Ptr.word; split <;> rfl

/-- A `callTy` tuple: the register shapes, then the memory. -/
theorem callTy_split {n : Nat} {ts : List Ty} (h : callTy n (.tuple ts) = true) :
    ∃ ts', ts = ts' ++ [.mem] ∧ ts'.length = n ∧ ∀ t ∈ ts', (cls t).isSome = true := by
  simp only [callTy, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hlen, hlast⟩, hall⟩ := h
  obtain ⟨t, ht⟩ : ∃ t, ts.getLast? = some t := by
    cases h' : ts.getLast? with
    | none => rw [h'] at hlast; cases hlast
    | some t => exact ⟨t, rfl⟩
  rw [ht] at hlast
  have htm : t = .mem := memTy_eq (by simpa using hlast)
  subst htm
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 ht
  refine ⟨ys, rfl, by simpa using hlen, fun t h => hall t (by simpa using h)⟩

/-- The slots `G2Inv` allows have 8-byte shapes. -/
theorem slot_sizes {E : MatchEnv} {lc : LocCtx} {g : G2In} {s : LocState} (hlc : E.lc = lc)
    (hcf : checkFrame lc g = .ok ()) (hinv : G2Inv E lc s) :
    ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8 := by
  intro k v hk
  obtain ⟨-, i, hh⟩ := hinv.slots k v hk
  rw [hlc]; exact (home_slot hcf hh).1

/-- The frame of a memory that agrees on the saved `LR`/`FP` words. -/
theorem frameRel_mem {E : MatchEnv} {m : MState} {M : Memory} (hF : FrameOK E) (h : FrameRel E m)
    (hag : E.framed = true → ∀ j, j < 8 → M (E.sp + BitVec.ofNat 64 j) = m.mem (E.sp + BitVec.ofNat 64 j) ∧
      M (E.sp - 8 + BitVec.ofNat 64 j) = m.mem (E.sp - 8 + BitVec.ofNat 64 j)) :
    FrameRel E { m with mem := M } := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun hf => ?_, h4⟩
  obtain ⟨a1, a2, a3⟩ := h3 hf
  refine ⟨a1, ?_, ?_⟩
  · unfold MState.word at a2 ⊢
    rw [readMem_congr 8 E.sp (fun j hj => (hag hf j hj).1)]; exact a2
  · unfold MState.word at a3 ⊢
    rw [readMem_congr 8 (E.sp - 8) (fun j hj => (hag hf j hj).2)]; exact a3

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat}

/-- A value of slice G1, in a framed activation with slots. -/
theorem g2_g1 (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : G2Inv E lc s) {kd : VKind}
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hvs : VStep2 psA kd.v2 j j') (hVK : VK lc v kd) (htemp : (lc.temps[v.id]?).join = none)
    (hpre : G1Pre lc s v) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ G2Inv E lc s' := by
  obtain ⟨m', hstar, hlm, hcore, hsl⟩ :=
    value_core F hm hinv.core (stk_keeps hm hF hsz) hj hj' (vstep_v2 hvs) hVK htemp hpre hs
  exact ⟨m', hstar, hlm, hcore, by rw [hsl]; exact hinv.slots⟩

/-- A reload of a 64-bit value from its slot. -/
theorem g2_reload (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E) (hlc : E.lc = lc)
    (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k nc off, g.slotOp k = some (nc, off) →
      E.slot k = some (frameOff (Link.byId sym text az ez psA.toList) nc off))
    (hm : LocMatch E s b i m) (hinv : G2Inv E lc s)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {a : ID} {k : SlotKey} {nc : AddrName} {off : Int} {rd : Int} {pat : Pat}
    (hop : v.op = .LoadReg) (hsz1 : v.args.size = 1) (ha0 : v.args[0]? = some a)
    (hah : lc.home a = some (.slot k)) (hso : g.slotOp k = some (nc, off))
    (hca : cls (lc.ty a) = some 64) (hro : resObj lc v = .ok (64, rd))
    (hpat : ∀ p, pat.ok p = true → p.as = .MOVD ∧ slotA p.from_ nc off = true ∧ p.to = regA rd ∧
      p.reg = 0 ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0)
    (hvs : OneAt2 psA j pat j') (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ G2Inv E lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, rfl⟩ := stepLoc_move hl htemp (Or.inr hop) (arr1 hsz1 ha0) hs
  rw [read_slot hl hah] at hx
  cases hx
  rw [write_reg hvh hcv]
  obtain ⟨h8, nc', off', hso', hnc⟩ := home_slot hcf hah
  rw [hso] at hso'
  cases hso'
  have hsl := hslot k nc off hso
  obtain ⟨ho8, hohi⟩ := hF.slot k _ hsl
  have hsp : m.sp = E.sp := hm.frame.1
  -- the slot's machine word
  have hrel : ValRel E.ι (((s.slots.lookup k).getD .poison).retypeL (lc.ty a))
      ((readMem m.mem (m.sp + BitVec.ofInt 64 (frameOff (Link.byId sym text az ez psA.toList) nc off))
        8).setWidth 64) := by
    cases hk : s.slots.lookup k with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some v0 =>
      simp only [Option.getD_some]
      obtain ⟨o', ho', hsr⟩ := hm.slots k v0 hk
      rw [hsl] at ho'; cases ho'
      unfold SlotRel at hsr
      rw [hlc, h8] at hsr
      rw [hsp]
      exact valRel_retypeL hA hca (hinv.slots k v0 hk).1 hsr
  refine (op_reg2 (H := H) F hm hinv.core hj hj' hvs hvh hcv hd hkd hor
    (valRel_retypeL hA hcv (fits_retypeL hca _) hrel) (fits_retypeL hcv _)
    (fun k0 hk0 hok => ?_)).imp fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hinv.slots⟩
  obtain ⟨has, hf, ht, -, -, -, -⟩ := hpat _ hok
  rw [progStep_slotLoad hkd (nextAddr_pcAt F.nodup hk0) has hf hnc ht ?_, wX_pc]
  simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
  show 4096 ≤ (m.sp + BitVec.ofInt 64 _).toNat
  rw [hsp, win0_toNat (by omega) hohi]
  have := hF.lo; omega

/-- The address of a global. -/
theorem g2_addr (F : Facts lc sym text az ez psA.toList ret E)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : G2Inv E lc s)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {a x : Nat} {name : GoStr} {abi : Nat} {rd : Int} {pat : Pat}
    (hop : v.op = .ARM64MOVDaddr) (hsz1 : v.args.size = 1) (ha0 : v.args[0]? = some a)
    (hx : v.aux = some x) (hsym : symOf? lc.ctx.tabs x = some (name, abi))
    (hro : resObj lc v = .ok (64, rd))
    (hpat : ∀ p, pat.ok p = true → p.as = .MOVD ∧ p.from_.type = .ADDR ∧ p.from_.name = .EXTERN ∧
      p.from_.offset = v.auxInt.toInt ∧ (∃ y, p.from_.sym = some y ∧ g.syms[y]? = some (name, abi)) ∧
      p.to = regA rd ∧ p.reg = 0 ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0)
    (hvs : OneAt2 psA j pat j') (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ G2Inv E lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  rw [stepLoc_addr hl htemp hop (arr1 hsz1 ha0) hx hsym hs, write_reg hvh hcv]
  obtain ⟨k0, -, hk0, hok0, -⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  obtain ⟨-, -, -, -, ⟨y, -, hy⟩, -⟩ := hpat _ hok0
  have hrel : ValRel E.ι (PtrOps.ptrRes ⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt⟩)
      (sym y + BitVec.ofInt 64 v.auxInt.toInt) := by
    unfold PtrOps.ptrRes
    split
    · exact valRel_word hA ⟨sym y, hglob y name abi hy, rfl⟩
    · trivial
  have hfit : Fits 64 (PtrOps.ptrRes ⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt⟩) := by
    unfold PtrOps.ptrRes; split
    · exact fits_word _
    · trivial
  refine (op_reg2 (H := H) F hm hinv.core hj hj' hvs hvh hcv hd hkd hor
    (valRel_retypeL hA hcv hfit hrel) (fits_retypeL hcv _)
    (fun k0 hk0 hok => ?_)).imp fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hinv.slots⟩
  obtain ⟨has, hf1, hf2, hf3, ⟨y', hy1, hy'⟩, ht, -⟩ := hpat _ hok
  rw [progStep_movAddr hkd (nextAddr_pcAt F.nodup hk0) has hf1 hf2 hf3 hy1 ht, wX_pc]
  have hyy : sym y' = sym y := Option.some.inj ((hglob y' name abi hy').symm.trans (hglob y name abi hy))
  rw [show (Link.byId sym text az ez psA.toList).sym y' = sym y from hyy]

/-- A spill of a 64-bit value to its slot. -/
theorem g2_spill (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E) (hlc : E.lc = lc)
    (hcf : checkFrame lc g = .ok ())
    (hslot : ∀ k nc off, g.slotOp k = some (nc, off) →
      E.slot k = some (frameOff (Link.byId sym text az ez psA.toList) nc off))
    (hext : 0 ≤ (Link.byId sym text az ez psA.toList).extrasize)
    (hm : LocMatch E s b i m) (hinv : G2Inv E lc s)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {k : SlotKey} {nc : AddrName} {off : Int} {rs : Int} {pat : Pat}
    (hop : v.op = .StoreReg) (hh : lc.home v.id = some (.slot k)) (hso : g.slotOp k = some (nc, off))
    (hsz1 : v.args.size = 1) (hcv : cls (lc.ty v.id) = some 64) (hao : argObj lc v 0 = .ok (64, rs))
    (hpat : ∀ p, pat.ok p = true → p.as = .MOVD ∧ p.from_ = regA rs ∧ slotA p.to nc off = true ∧
      p.reg = 0 ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0)
    (hvs : OneAt2 psA j pat j') (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ G2Inv E lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨a, r1, ha0, hah, hor1, hca⟩ := argObj_spec hao
  obtain ⟨ks, hks, rfl, hkk⟩ := objOf?_some hor1
  obtain ⟨x, hx, hxv, hxf⟩ := arg_rel hA hl F.home hm hinv.core hah hca hkk
  obtain ⟨x', hx', rfl⟩ := stepLoc_move hl htemp (Or.inl hop) (arr1 hsz1 ha0) hs
  rw [hx] at hx'
  cases hx'
  rw [write_slot hh]
  obtain ⟨h8, nc', off', hso', hnc⟩ := home_slot hcf hh
  rw [hso] at hso'
  cases hso'
  have hsl := hslot k nc off hso
  generalize ho : frameOff (Link.byId sym text az ez psA.toList) nc off = o at hsl
  obtain ⟨ho8, hohi⟩ := hF.slot k o hsl
  have hsp : m.sp = E.sp := hm.frame.1
  obtain ⟨k0, rfl, hk0, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, hf, ht, -, -, -, -⟩ := hpat _ hok
  obtain ⟨A, hAe⟩ : ∃ A, A = E.sp + BitVec.ofInt 64 o := ⟨_, rfl⟩
  obtain ⟨V, hVe⟩ : ∃ V : BitVec 64,
      V = ({ m with pc := pcAt text psA.toList k0 } : MState).rX (BitVec.ofNat 5 ks) := ⟨_, rfl⟩
  have hVeq : (BitVec.ofNat (8 * 8) (V.toNat % 2 ^ (8 * 8)) : BitVec 64) = V := by
    apply BitVec.eq_of_toNat_eq; simpa using V.isLt
  have hstep : progStep (Link.byId sym text az ez psA.toList) psA.toList[k0]
      { m with pc := pcAt text psA.toList k0 } =
      .ok { m with mem := writeMem m.mem A 8 V, pc := pcAt text psA.toList (k0 + 1) } := by
    rw [progStep_slotStore hks (nextAddr_pcAt F.nodup hk0) has hf ht hnc]
    · rw [← hVe, hVeq, hsp, ho, ← hAe]
    · simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
      show 4096 ≤ (m.sp + BitVec.ofInt 64 _).toNat
      rw [hsp, ho, win0_toNat (by omega) hohi]
      have := hF.lo; omega
  subst hAe
  have hxV : ValRel E.ι x V := by rw [hVe]; exact hxv
  have hMout : ∀ y : BitVec 64, (∀ j, j < 8 → y ≠ E.sp + BitVec.ofInt 64 o + BitVec.ofNat 64 j) →
      writeMem m.mem (E.sp + BitVec.ofInt 64 o) 8 V y = m.mem y :=
    fun y hy => writeMem_other 8 _ _ _ y hy
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk0 rfl hstep), ?_, ?_⟩
  · obtain ⟨mm, hmm, hMI⟩ := hm.mem
    obtain ⟨mm0, hmm0, -, hsep⟩ := hinv.core.mem
    rw [hmm] at hmm0
    cases hmm0
    refine ⟨hm.regs, hm.flags, ?_, ⟨mm, hmm, ?_⟩, ?_, by rw [hj']⟩
    · intro k' v' hk'
      rcases lookup_setSlot hk' with ⟨rfl, rfl⟩ | ⟨hne, hold⟩
      · refine ⟨o, hsl, ?_⟩
        unfold SlotRel
        rw [hlc, h8, readMem_writeMem_self]
        simpa using valRel_retypeL hA hcv hxf hxV
      · obtain ⟨o', ho', hsr⟩ := hm.slots k' v' hold
        refine ⟨o', ho', ?_⟩
        obtain ⟨-, i', hi'⟩ := hinv.slots k' v' hold
        have hap := slot_apart hcf hslot hext (mem_homeSlots hh) (mem_homeSlots hi') (Ne.symm hne)
          hsl ho'
        unfold SlotRel at hsr ⊢
        have h8' : (E.lc.slotTy k').size = 8 := slot_sizes hlc hcf hinv k' v' hold
        rw [h8'] at hsr ⊢
        rw [readMem_congr 8 (E.sp + BitVec.ofInt 64 o')
          (fun j hj => hMout _ (fun j' hj' => slot_windows_apart hF hsl ho' hap hj' hj))]
        exact hsr
    · exact memInj_congr hMI (fun b al a hb ha i hi =>
        hMout _ (fun j hj => ne_of_sep hMI hsep hb ha (stk_slot hF hsl hj) hi))
    · refine frameRel_mem hF hm.frame (fun _ j hj => ⟨hMout _ (fun j' hj' he => ?_),
        hMout _ (fun j' hj' he => ?_)⟩)
      · have := congrArg BitVec.toNat he
        rw [sp_toNat hF hj, win_toNat (by omega) hohi hj'] at this
        omega
      · have := congrArg BitVec.toNat he
        rw [spm8_toNat hF hj, win_toNat (by omega) hohi hj'] at this
        have := hF.lo
        omega
  · refine ⟨⟨hinv.core.regs, hinv.core.mem⟩, fun k' v' hk' => ?_⟩
    rcases lookup_setSlot hk' with ⟨rfl, rfl⟩ | ⟨-, hold⟩
    · exact ⟨fits_retypeL hcv _, v.id, hh⟩
    · exact hinv.slots k' v' hold

/-- A read of a call's tuple: the components of a `callTy` tuple read from the call's home. -/
theorem read_call {c : ID} {ts' : List Ty} (hl : lc.ctx.f.lowered = true)
    (hts : lc.ty c = .tuple (ts' ++ [.mem])) (hcls : ∀ t ∈ ts', (cls t).isSome = true)
    (hnot : ∀ k, lc.home c ≠ some (.slot k)) :
    ∃ xs, s.read lc c = .ok ((Val.tuple xs).retypeL (.tuple (ts' ++ [.mem]))) ∧
      xs.length = ts'.length + 1 ∧ xs[ts'.length]? = some s.mem ∧
      ∀ (j : Nat) (t : Ty) (r : Nat), ts'[j]? = some t →
        (((lc.home c).map Location.regList).getD [])[j]? = some (some r) →
        xs[j]? = some (s.reg t r) := by
  obtain ⟨h1, h2, h3⟩ := readParts_call ts' (((lc.home c).map Location.regList).getD []) s hcls
  refine ⟨_, ?_, h1, h2, h3⟩
  unfold LocState.read LocState.raw
  rw [hts]
  cases hh : lc.home c with
  | none => simp only [lmode_retype hl]; rfl
  | some h =>
    cases h with
    | slot k => exact absurd hh (hnot k)
    | _ => simp only [lmode_retype hl]; rfl

/-- `SelectN [i]` of a tuple read at a tuple shape: component `i` at its shape. -/
theorem selectN_retypeL {ts : List Ty} {xs : List Val} (hlen : xs.length = ts.length) {a : Int64}
    (ha : 0 ≤ a.toInt) {t : Ty} {x : Val} (ht : ts[a.toInt.toNat]? = some t)
    (hx : xs[a.toInt.toNat]? = some x) :
    Tuple.selectN a [(Val.tuple xs).retypeL (.tuple ts)] = x.retypeL t := by
  have hw : (Val.tuple xs).retypeL (.tuple ts) =
      .tuple (List.zipWith (fun t x => (x.widen t).retype t) ts xs) := by
    simp only [Val.retypeL, Val.widen, Val.retype, retypePre_widen ts xs hlen.symm]
  rw [hw]
  simp only [Tuple.selectN, show ¬ a.toInt < 0 from by omega, decide_false, ↓reduceIte]
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, ht, hx]
  rfl

theorem objOf?_low {r : Nat} (hr : r < 16) : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + r) := by
  have hz : r ≠ zeroReg := by unfold zeroReg; omega
  simp only [objOf?, hz, ↓reduceIte, objX?, show r < 18 by omega, Option.map_some]
  congr 2
  simp; omega

theorem objX?_low {r : Nat} (hr : r < 16) : objX? r = some (BitVec.ofNat 5 r) := by
  simp [objX?, show r < 18 by omega]

theorem objV?_low {r : Nat} (hr : r < 31) : objV? r = none := by
  simp [objV?]; omega

/-- A call's home is no slot. -/
theorem call_not_slot {c : ID} {u : Value} (hhome2 : ∀ i, homeOK2 lc i = true)
    (hu : lc.ctx.f.value? c = some u) (hcop : u.op = .ARM64CALLstatic) :
    ∀ k, lc.home c ≠ some (.slot k) := by
  intro k hk
  have := hhome2 c
  simp [homeOK2, hk, hu, hcop] at this

/-- `SelectN` of a call's memory changes nothing. -/
theorem g2_selMem (F : Facts lc sym text az ez psA.toList ret E) (hhome2 : ∀ i, homeOK2 lc i = true)
    (hm : LocMatch E s b i m) (hinv : G2Inv E lc s)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : ID} {u : Value} {ts : List Ty}
    (hop : v.op = .SelectN) (hsz1 : v.args.size = 1) (hc0 : v.args[0]? = some c)
    (hu : lc.ctx.f.value? c = some u) (hcop : u.op = .ARM64CALLstatic) (hts : lc.ty c = .tuple ts)
    (hct : callTy (ts.length - 1) (.tuple ts) = true) (hpos : 0 ≤ v.auxInt.toInt)
    (hmt : memTy (lc.ty v.id) = true) (hnone : lc.home v.id = none)
    (hidx : v.auxInt.toInt.toNat + 1 = ts.length) (hvs : j' = j)
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ G2Inv E lc s' := by
  have hl := F.lowered
  obtain ⟨ts', rfl, -, hcls⟩ := callTy_split hct
  obtain ⟨xs, hread, hlen, hmemc, -⟩ := read_call (s := s) hl hts hcls (call_not_slot hhome2 hu hcop)
  obtain ⟨x, hx, rfl⟩ := stepLoc_selectN hl htemp hop (arr1 hsz1 hc0) hs
  rw [hread] at hx
  cases hx
  have hi : v.auxInt.toInt.toNat = ts'.length := by simp at hidx; omega
  rw [selectN_retypeL (by simp [hlen]) hpos (by rw [hi]; simp) (by rw [hi]; exact hmemc)]
  obtain ⟨mm, hmm, -⟩ := hm.mem
  rw [write_mem hnone hmt, memTy_eq hmt, hmm]
  have hs' : ({ s with mem := Val.retypeL .mem (Val.retypeL .mem (.mem mm)) } : LocState) = s := by
    cases s; simp_all; rfl
  rw [hs']
  exact ⟨m, .refl, locMatch_pc hm (by rw [hj', hj, hvs, hm.pc]), hinv⟩

/-- `SelectN [i]` of a call's result `i` in its result register changes nothing on the machine. -/
theorem g2_selReg (F : Facts lc sym text az ez psA.toList ret E) (hhome2 : ∀ i, homeOK2 lc i = true)
    (hm : LocMatch E s b i m) (hinv : G2Inv E lc s)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : ID} {u : Value} {ts : List Ty} {r : Nat} {rs : Array (Option Nat)}
    (hop : v.op = .SelectN) (hsz1 : v.args.size = 1) (hc0 : v.args[0]? = some c)
    (hu : lc.ctx.f.value? c = some u) (hcop : u.op = .ARM64CALLstatic) (hts : lc.ty c = .tuple ts)
    (hct : callTy (ts.length - 1) (.tuple ts) = true) (hpos : 0 ≤ v.auxInt.toInt)
    (hvh : lc.home v.id = some (.reg r)) (hr16 : r < 16)
    (hlt : v.auxInt.toInt.toNat + 1 < ts.length)
    (hcl : (ts[v.auxInt.toInt.toNat]?.bind cls) = cls (lc.ty v.id))
    (hhc : lc.home c = some (.results rs)) (hrs : rs[v.auxInt.toInt.toNat]? = some (some r))
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ G2Inv E lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨ts', rfl, -, hcls⟩ := callTy_split hct
  obtain ⟨xs, hread, hlen, -, hcomp⟩ := read_call (s := s) hl hts hcls (call_not_slot hhome2 hu hcop)
  obtain ⟨x, hx, rfl⟩ := stepLoc_selectN hl htemp hop (arr1 hsz1 hc0) hs
  rw [hread] at hx
  cases hx
  have hi' : v.auxInt.toInt.toNat < ts'.length := by simp at hlt; omega
  obtain ⟨t, ht'⟩ : ∃ t, ts'[v.auxInt.toInt.toNat]? = some t :=
    ⟨ts'[v.auxInt.toInt.toNat], by simp [hi']⟩
  have ht : (ts' ++ [Ty.mem])[v.auxInt.toInt.toNat]? = some t := by
    rw [List.getElem?_append_left hi']; exact ht'
  obtain ⟨c0, hc0t⟩ : ∃ c0, cls t = some c0 :=
    Option.isSome_iff_exists.1 (hcls t (List.mem_of_getElem? ht'))
  have hcv : cls (lc.ty v.id) = some c0 := by rw [← hcl, ht]; exact hc0t
  have hxs := hcomp _ t r ht' (by simp [hhc, Location.regList, hrs])
  rw [selectN_retypeL (by simp [hlen]) hpos ht hxs, write_reg hvh hcv]
  have hrz : r ≠ zeroReg := by unfold zeroReg; omega
  have hrel : ValRel E.ι (((s.reg t r).retypeL t).retypeL (lc.ty v.id)) (m.rX (BitVec.ofNat 5 r)) := by
    rw [rX_lt (by omega)]
    simp only [LocState.reg, beq_iff_eq, hrz, ↓reduceIte]
    cases hv : s.regs[r]? with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some raw =>
      simp only [Option.getD_some]
      have hcr := regCls_of_home (F.home _ _ hvh) hvh hrz hcv
      have hfit := hinv.core.regs r raw c0 hrz hv hcr
      have h1 := valRel_retypeL hA hc0t hfit ((hm.regs r raw hv).1 _ (objX?_low hr16))
      exact valRel_retypeL hA hcv (fits_retypeL hc0t _) h1
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv.core (F.home _ _ hvh) hvh hcv (by simp [destOK]; omega)
    (by omega : r < 32) (objOf?_low hr16) hrel (fits_retypeL hcv _) (b' := b) (i' := i + 1)
  rw [wX_rX_self, hj', hvs, ← hj, ← hm.pc] at hlm
  exact ⟨m, .refl, hlm, hinv', hinv.slots⟩

end Cases

end GoFV.Proof.Gen
