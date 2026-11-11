import GoFV.Gen.Check2
import GoFV.Proof.Gen.Spec

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G2 accepted (`docs/plans/proofs3.md` §4)

`checkG2 lc ps bstart g = .ok tab` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G2.lean`) uses: G1's (`Spec.lean`) for the values and terminators G2 takes from
G1, and for G2's own values (`VK2`): a static call with its arguments in their ABI registers, its
results' homes and shapes and its `CALL` Prog; `SelectN` of such a call; `MOVDaddr` of a global;
spills and reloads of 64-bit values at their frame operands; `Exit` blocks; `checkFrame`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-! ## Prog positions -/

/-- From index `j`, after no-ops, the Prog at index `j' - 1` matches `pat`. -/
def OneAt2 (ps : Array Prog) (j : Nat) (pat : Pat) (j' : Nat) : Prop :=
  ∃ k, j ≤ k ∧ j' = k + 1 ∧ ∃ hk : k < ps.size, pat.ok ps[k] = true ∧
    ∀ l (hl : l < ps.size), j ≤ l → l < k → noop ps[l] = true

theorem Cx2.one_spec {c : Cx2} {j j' : Nat} {pat : Pat} (h : c.one j pat = .ok j') :
    OneAt2 c.cx.ps j pat j' := by
  unfold Cx2.one at h
  simp only at h
  cases hp : c.cx.ps[skipFrom c.cx.ps j c.cx.ps.size]? with
  | none => simp [hp, ex_throw] at h
  | some p =>
    simp only [hp] at h
    obtain ⟨hs, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hk, hk'⟩ := Array.getElem?_eq_some_iff.mp hp
    obtain ⟨h1, h2⟩ := skipFrom_spec c.cx.ps c.cx.ps.size j
    exact ⟨_, h1, rfl, hk, hk' ▸ hs, h2⟩

/-- From index `j`, Progs matching `pats` in order, each after no-ops; `j'` after the last. -/
def ManyAt2 (ps : Array Prog) : Nat → List Pat → Nat → Prop
  | j, [], j' => j' = j
  | j, pat :: pats, j' => ∃ k, OneAt2 ps j pat k ∧ ManyAt2 ps k pats j'

theorem Cx2.many_spec {c : Cx2} : ∀ {j j' : Nat} {pats : List Pat}, c.many j pats = .ok j' →
    ManyAt2 c.cx.ps j pats j'
  | j, j', [], h => by
    simp only [Cx2.many, ex_pure, Except.ok.injEq] at h
    exact h.symm
  | j, j', pat :: pats, h => by
    simp only [Cx2.many] at h
    obtain ⟨k, hk, h⟩ := ex_bind_eq_ok h
    exact ⟨k, Cx2.one_spec hk, Cx2.many_spec h⟩

/-- The Progs between the start index of a value and the next. -/
def VStep2 (ps : Array Prog) : VKind2 → Nat → Nat → Prop
  | .entry, j, j' => j' = j
  | .none, j, j' => j' = j
  | .prog pat, j, j' => OneAt2 ps j pat j'
  | .progs pats, j, j' => ManyAt2 ps j pats j'

theorem Cx2.values_spec {c : Cx2} {entry : Bool} :
    ∀ {ids : List ID} {j : Nat} {head : Bool} {js : List Nat} {e : Nat},
      c.values entry ids j head = .ok (js, e) →
      js.length = ids.length ∧ (js ++ [e]).getD 0 0 = j ∧
      ∀ i (hi : i < ids.length), ∃ v kd, c.cx.lc.ctx.f.value? ids[i] = some v ∧
        c.vk v = .ok kd ∧
        VStep2 c.cx.ps kd ((js ++ [e]).getD i 0) ((js ++ [e]).getD (i + 1) 0) := by
  intro ids
  induction ids with
  | nil =>
    intro j head js e h
    simp only [Cx2.values, ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons id ids ih =>
    intro j head js e h
    simp only [Cx2.values] at h
    cases hv : c.cx.lc.ctx.f.value? id with
    | none => simp [hv, ex_throw] at h
    | some v =>
      simp only [hv] at h
      obtain ⟨kd, hk, h⟩ := ex_bind_eq_ok h
      have fin : ∀ k head', VStep2 c.cx.ps kd j k →
          (c.values entry ids k head' >>= fun x => pure (j :: x.fst, x.snd)) =
            Except.ok (js, e) →
          js.length = (id :: ids).length ∧ (js ++ [e]).getD 0 0 = j ∧
          ∀ i (hi : i < (id :: ids).length), ∃ v kd, c.cx.lc.ctx.f.value? (id :: ids)[i] = some v ∧
            c.vk v = .ok kd ∧
            VStep2 c.cx.ps kd ((js ++ [e]).getD i 0) ((js ++ [e]).getD (i + 1) 0) := by
        intro k head' hstep h
        obtain ⟨⟨js', e'⟩, hrest, h⟩ := ex_bind_eq_ok h
        simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ih1, ih2, ih3⟩ := ih hrest
        refine ⟨by simp [ih1], rfl, ?_⟩
        intro i hi
        cases i with
        | zero =>
          refine ⟨v, kd, hv, hk, ?_⟩
          simp only [List.cons_append, List.getD_cons_zero, List.getD_cons_succ, ih2]
          exact hstep
        | succ i =>
          have := ih3 i (by simpa using hi)
          simpa only [List.cons_append, List.getD_cons_succ, List.getElem_cons_succ] using this
      cases kd with
      | entry =>
        obtain ⟨_, h⟩ := ex_guard h
        exact fin j _ rfl h
      | none => exact fin j _ rfl h
      | prog pat =>
        obtain ⟨k, hkk, h⟩ := ex_bind_eq_ok h
        exact fin k _ (Cx2.one_spec hkk) h
      | progs pats =>
        obtain ⟨k, hkk, h⟩ := ex_bind_eq_ok h
        exact fin k _ (Cx2.many_spec hkk) h

/-! ## Values -/

/-- G1's kinds as G2's. -/
def VKind.v2 : VKind → VKind2
  | .entry => .entry
  | .none => .none
  | .prog sh => .prog (.ofShape sh)

theorem slotHome?_eq {lc : LocCtx} {a : ID} {k : SlotKey} :
    slotHome? lc a = some k ↔ lc.home a = some (.slot k) := by
  unfold slotHome?
  split <;> simp_all

private theorem callTy_tuple {n : Nat} {t : Ty} (h : callTy n t = true) :
    t = .tuple (tupleTys t) := by
  cases t <;> first | rfl | simp [callTy] at h

/-- What `vkind2` accepted of a value that is not an entry value, and what it emits. -/
inductive VK2 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G1. -/
  | g1 {kd : VKind} : v.op ≠ .ARM64CALLstatic → v.op ≠ .SelectN → v.op ≠ .ARM64MOVDaddr →
      v.op ≠ .StoreReg → v.op ≠ .LoadReg → VK lc v kd → VK2 lc g v kd.v2
  /-- A static call: register arguments in their ABI registers, results in the ABI's result
  registers (`results` home, or no home and no result), a `CALL` of the callee's symbol. -/
  | call {name : GoStr} {abi : Nat} {cabi : CallABI} {ins outs : List Nat} {mem : ID} {pat : Pat} :
      v.op = .ARM64CALLstatic → callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
      callRegs cabi = .ok (ins, outs) → v.args.back? = some mem → memTy (lc.ty mem) = true →
      lc.home mem = none → (∀ r ∈ ins ++ outs, r < 16) → v.args.toList.dropLast.length = ins.length →
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r)) →
      (lc.home v.id = some (.results (outs.map some).toArray) ∨ (lc.home v.id = none ∧ outs = [])) →
      callTy outs.length (lc.ty v.id) = true →
      (∀ t r, (t, r) ∈ (tupleTys (lc.ty v.id)).zip outs → resultReg lc t r = true) →
      (∀ p, pat.ok p = true → p.as = .CALL ∧ p.from_ = {} ∧ p.reg = 0 ∧ p.scond = 0 ∧
        p.rest.isEmpty = true ∧ p.regTo2 = 0 ∧ p.to.type = .MEM ∧ p.to.name = .EXTERN ∧
        p.to.offset = 0 ∧ ∃ y, p.to.sym = some y ∧ g.syms[y]? = some (name, abi)) →
      VK2 lc g v (.prog pat)
  /-- The memory of a static call: its last component. -/
  | selMem {c : ID} {u : Value} {ts : List Ty} : v.op = .SelectN → v.args.size = 1 →
      v.args[0]? = some c → lc.ctx.f.value? c = some u → u.op = .ARM64CALLstatic →
      lc.ty c = .tuple ts → callTy (ts.length - 1) (.tuple ts) = true → 0 ≤ v.auxInt.toInt →
      memTy (lc.ty v.id) = true → lc.home v.id = none → v.auxInt.toInt.toNat + 1 = ts.length →
      VK2 lc g v .none
  /-- Result `i` of a static call, homed in the call's result register `i`. -/
  | selReg {c : ID} {u : Value} {ts : List Ty} {r : Nat} {rs : Array (Option Nat)} :
      v.op = .SelectN → v.args.size = 1 → v.args[0]? = some c → lc.ctx.f.value? c = some u →
      u.op = .ARM64CALLstatic → lc.ty c = .tuple ts → callTy (ts.length - 1) (.tuple ts) = true →
      0 ≤ v.auxInt.toInt → memTy (lc.ty v.id) = false → lc.home v.id = some (.reg r) → r < 16 →
      v.auxInt.toInt.toNat + 1 < ts.length →
      (ts[v.auxInt.toInt.toNat]?.bind cls) = cls (lc.ty v.id) →
      lc.home c = some (.results rs) → rs[v.auxInt.toInt.toNat]? = some (some r) →
      VK2 lc g v .none
  /-- The address of a global: `MOVD $sym+off(SB), Rd`. -/
  | addr {a x : Nat} {name : GoStr} {abi : Nat} {rd : Int} {pat : Pat} :
      v.op = .ARM64MOVDaddr → v.args.size = 1 → v.args[0]? = some a →
      (lc.ctx.f.value? a).map (·.op) = some .SB → v.aux = some x →
      symOf? lc.ctx.tabs x = some (name, abi) → resObj lc v = .ok (64, rd) →
      (∀ p, pat.ok p = true → p.as = .MOVD ∧ p.from_.type = .ADDR ∧ p.from_.name = .EXTERN ∧
        p.from_.offset = v.auxInt.toInt ∧ (∃ y, p.from_.sym = some y ∧ g.syms[y]? = some (name, abi)) ∧
        p.to = regA rd ∧ p.reg = 0 ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0) →
      VK2 lc g v (.prog pat)
  /-- A spill: `MOVD Rs, off(RSP)` at the slot's frame operand. -/
  | spill {k : SlotKey} {nc : AddrName} {off : Int} {rs : Int} {pat : Pat} :
      v.op = .StoreReg → lc.home v.id = some (.slot k) → g.slotOp k = some (nc, off) →
      v.args.size = 1 → cls (lc.ty v.id) = some 64 → argObj lc v 0 = .ok (64, rs) →
      (∀ p, pat.ok p = true → p.as = .MOVD ∧ p.from_ = regA rs ∧ slotA p.to nc off = true ∧
        p.reg = 0 ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0) →
      VK2 lc g v (.prog pat)
  /-- A reload: `MOVD off(RSP), Rd` from the slot's frame operand. -/
  | reload {a : ID} {k : SlotKey} {nc : AddrName} {off : Int} {rd : Int} {pat : Pat} :
      v.op = .LoadReg → v.args.size = 1 → v.args[0]? = some a → lc.home a = some (.slot k) →
      g.slotOp k = some (nc, off) → cls (lc.ty a) = some 64 → resObj lc v = .ok (64, rd) →
      (∀ p, pat.ok p = true → p.as = .MOVD ∧ slotA p.from_ nc off = true ∧ p.to = regA rd ∧
        p.reg = 0 ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0) →
      VK2 lc g v (.prog pat)

/-- What `vkind2` accepted of a value that is not an entry value: no temporary, and `VK2`. -/
theorem vkind2_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : vkind2 lc g v = .ok kd)
    (hen : entryOp v.op = false) : (lc.temps[v.id]?).join = none ∧ VK2 lc g v kd := by
  have ht : (lc.temps[v.id]?).join = none := by
    by_cases ht : (lc.temps[v.id]?).join = none
    · exact ht
    · unfold vkind2 at h
      simp [ht, ex_throw, ex_bind_error] at h
  refine ⟨ht, ?_⟩
  unfold vkind2 at h
  simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ex_pure] at h
  split at h
  next hop =>
    split at h
    next name abi cabi hcall =>
      obtain ⟨⟨ins, outs⟩, hcr, h⟩ := ex_bind_eq_ok h
      split at h
      next m hm =>
        obtain ⟨hmem, h⟩ := ex_guard h
        obtain ⟨h16, h⟩ := ex_guard h
        obtain ⟨hlen, h⟩ := ex_guard h
        obtain ⟨hargs, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hmem hlen
        simp only [List.all_eq_true, decide_eq_true_eq] at h16
        have hargs' : ∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r) := by
          intro a r har
          have := (List.all_eq_true.mp hargs) (a, r) har
          simpa only [beq_iff_eq, regHome?_eq] using this
        have hres : lc.home v.id = some (.results (outs.map some).toArray) ∨
            (lc.home v.id = none ∧ outs = []) := by
          split at h
          next rs hrs =>
            obtain ⟨hc, -⟩ := ex_guard h
            simp only [beq_iff_eq] at hc
            left
            rw [hrs, ← hc]
          next hn =>
            obtain ⟨hc, -⟩ := ex_guard h
            exact Or.inr ⟨hn, List.isEmpty_iff.mp hc⟩
          next => simp [ex_throw, ex_bind_error] at h
        split at h
        all_goals first
          | (simp [ex_throw, ex_bind_error] at h; done)
          | (obtain ⟨-, h⟩ := ex_guard h
             obtain ⟨hsh, h⟩ := ex_guard h
             cases h)
        all_goals
          simp only [Bool.and_eq_true] at hsh
          refine VK2.call hop hcall hcr hm hmem.1 hmem.2 h16 hlen hargs' hres hsh.1 ?_ ?_
          · intro t r htr
            have := (List.all_eq_true.mp hsh.2) (t, r) htr
            simpa only using this
          · intro p hp
            simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hp
            obtain ⟨has, hfrom, hreg, hty, hnm, hr0, hix, hoff, hsym, hsc, hrest, hr2⟩ := hp
            refine ⟨has, hfrom, hreg, hsc, hrest, hr2, hty, hnm, hoff, ?_⟩
            split at hsym
            next y hy => exact ⟨y, hy, by simpa using hsym⟩
            next => simp at hsym
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next hop =>
    split at h
    next c hc0 =>
      split at h
      next u hu =>
        obtain ⟨hsz, h⟩ := ex_guard h
        obtain ⟨hct, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsz hct
        obtain ⟨ts, hts⟩ : ∃ ts, lc.ty c = .tuple ts := ⟨_, callTy_tuple hct.1⟩
        simp only [hts, tupleTys] at hct h
        split at h
        next hm =>
          obtain ⟨hc, h⟩ := ex_guard h
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          exact VK2.selMem hop hsz.1 hc0 hu hsz.2 hts hct.1 hct.2 hm hc.1 hc.2
        next hm =>
          split at h
          next r hr =>
            obtain ⟨hc, h⟩ := ex_guard h
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
            split at h
            next rs hrs =>
              obtain ⟨hrr, h⟩ := ex_guard h
              cases h
              simp only [beq_iff_eq] at hrr
              exact VK2.selReg hop hsz.1 hc0 hu hsz.2 hts hct.1 hct.2 (by simpa using hm)
                (regHome?_eq.mp hr) hc.1.1 hc.1.2 hc.2 hrs hrr
            next => simp [ex_throw, ex_bind_error] at h
          next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next hop =>
    split at h
    next a ha =>
      obtain ⟨hsz, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq] at hsz
      split at h
      next x hx =>
        split at h
        next name abi hsym =>
          obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
          obtain ⟨hc, h⟩ := ex_guard h
          cases h
          simp only [beq_iff_eq] at hc
          subst hc
          refine VK2.addr hop hsz.1 ha hsz.2 hx hsym hro ?_
          intro p hp
          simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hp
          obtain ⟨has, hty, hnm, hr0, hix, hoff, hsym', hreg, hto, hsc, hrest, hr2⟩ := hp
          refine ⟨has, hty, hnm, hoff, ?_, hto, hreg, hsc, hrest, hr2⟩
          split at hsym'
          next y hy => exact ⟨y, hy, by simpa using hsym'⟩
          next => simp at hsym'
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next hop =>
    split at h
    next k hk =>
      split at h
      next nc off hso =>
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨⟨c, rs⟩, hao, h⟩ := ex_bind_eq_ok h
        obtain ⟨hc, h⟩ := ex_guard h
        cases h
        simp only [beq_iff_eq] at hc
        subst hc
        refine VK2.spill hop (slotHome?_eq.mp hk) hso hsz.1 hsz.2 hao ?_
        intro p hp
        simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hp
        obtain ⟨has, hfrom, hreg, hto, hsc, hrest, hr2⟩ := hp
        exact ⟨has, hfrom, hto, hreg, hsc, hrest, hr2⟩
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next hop =>
    split at h
    next a ha =>
      split at h
      next k hk =>
        split at h
        next nc off hso =>
          obtain ⟨hsz, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq] at hsz
          obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
          obtain ⟨hc, h⟩ := ex_guard h
          cases h
          simp only [beq_iff_eq] at hc
          subst hc
          refine VK2.reload hop hsz.1 ha (slotHome?_eq.mp hk) hso hsz.2 hro ?_
          intro p hp
          simp only [plain, Bool.and_eq_true, beq_iff_eq, and_assoc] at hp
          obtain ⟨has, hfrom, hreg, hto, hsc, hrest, hr2⟩ := hp
          exact ⟨has, hfrom, hto, hreg, hsc, hrest, hr2⟩
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next h1 h2 h3 h4 h5 =>
    obtain ⟨kd1, hk, h⟩ := ex_bind_eq_ok h
    have hvk := (vkind_spec hk hen).2
    cases kd1 <;> simp only [Except.ok.injEq] at h <;> subst h
    · exact VK2.g1 (kd := .entry) h1 h2 h3 h4 h5 hvk
    · exact VK2.g1 (kd := .none) h1 h2 h3 h4 h5 hvk
    · exact VK2.g1 (kd := .prog _) h1 h2 h3 h4 h5 hvk

/-! ## Terminators, blocks, the frame and the whole check -/

/-- What `Cx.termG2` accepted: an `Exit` block without successors, or G1's terminators. -/
theorem Cx.termG2_spec {cx : Cx} {b : Block} {j : Nat} {next : Option (ID × Nat)}
    (h : cx.termG2 b j next = .ok ()) :
    (b.kind = .Exit ∧ b.succs = #[]) ∨ (b.kind ≠ .Exit ∧ TermOK cx b j next) := by
  unfold Cx.termG2 at h
  split at h
  next hk =>
    obtain ⟨hs, -⟩ := ex_guard h
    exact Or.inl ⟨by simpa using hk, by simpa using hs⟩
  next hk => exact Or.inr ⟨by simpa using hk, Cx.term_spec h⟩

theorem Cx2.blocks_spec {c : Cx2} : ∀ {bids : List ID} {tab : PcTab}, c.blocks bids = .ok tab →
    ∀ bid ∈ bids, ∃ b j js e next, c.cx.lc.ctx.f.block? bid = some b ∧ c.cx.startIdx bid = .ok j ∧
      c.values (bid == c.cx.lc.ctx.f.entry) b.values.toList j true = .ok (js, e) ∧
      c.tm b e next = .ok () ∧
      (∀ n k, next = some (n, k) → c.cx.startIdx n = .ok k) ∧
      tab.lookup bid = some (js ++ [e]) := by
  intro bids
  induction bids with
  | nil => intro tab _ bid hb; cases hb
  | cons bid0 rest ih =>
    intro tab h bid hbid
    unfold Cx2.blocks at h
    cases hb : c.cx.lc.ctx.f.block? bid0 with
    | none => simp [hb, ex_throw] at h
    | some b =>
      simp only [hb] at h
      obtain ⟨j, hj, h⟩ := ex_bind_eq_ok h
      obtain ⟨⟨js, e⟩, hv, h⟩ := ex_bind_eq_ok h
      obtain ⟨next, hn, h⟩ : ∃ next, (∀ n k, next = some (n, k) → c.cx.startIdx n = .ok k) ∧
          (do c.tm b e next; let tab ← c.blocks rest; pure ((bid0, js ++ [e]) :: tab)) =
            Except.ok tab := by
        split at h
        next n _ =>
          obtain ⟨k, hk, h⟩ := ex_bind_eq_ok h
          refine ⟨some (n, k), fun n' k' he => ?_, h⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact hk
        next => exact ⟨none, (fun _ _ he => nomatch he), h⟩
      obtain ⟨⟨⟩, ht, h⟩ := ex_bind_eq_ok h
      obtain ⟨tab', htab, h⟩ := ex_bind_eq_ok h
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      by_cases hbe : bid = bid0
      · subst hbe
        exact ⟨b, j, js, e, next, hb, hj, hv, ht, hn, by simp [List.lookup]⟩
      · have hmem : bid ∈ rest := by
          cases hbid with
          | head => exact absurd rfl hbe
          | tail _ hm => exact hm
        obtain ⟨b', j', js', e', next', h1, h2, h3, h4, h5, h6⟩ := ih htab bid hmem
        refine ⟨b', j', js', e', next', h1, h2, h3, h4, h5, ?_⟩
        have hne : (bid == bid0) = false := by simp [hbe]
        simp only [List.lookup, hne, h6]

theorem mem_homeSlots {lc : LocCtx} {i : Nat} {k : SlotKey} (h : lc.home i = some (.slot k)) :
    k ∈ homeSlots lc := by
  unfold homeSlots
  have hi : i < lc.homes.size := by
    refine Nat.lt_of_not_le fun hn => ?_
    simp [LocCtx.home, getElem?_neg lc.homes i (Nat.not_lt_of_le hn)] at h
  exact List.mem_filterMap.mpr ⟨i, List.mem_range.mpr hi, slotHome?_eq.mpr h⟩

/-- What `checkFrame` accepted, in full: every home slot `slotOK`, distinct home slots at distinct
frame operands with disjoint windows (`slotsApart`), every homed value of its slot's class and
size (`homeFits`). -/
theorem checkFrame_full {lc : LocCtx} {g : G2In} (h : checkFrame lc g = .ok ()) :
    (∀ k ∈ homeSlots lc, slotOK lc g k = true) ∧
    (∀ k ∈ homeSlots lc, ∀ k' ∈ homeSlots lc, k ≠ k' → g.slotOp k' ≠ g.slotOp k) ∧
    (∀ k ∈ homeSlots lc, ∀ k' ∈ homeSlots lc, k ≠ k' → slotsApart lc g k k' = true) ∧
    ∀ i, i < lc.homes.size → homeFits lc i = true := by
  unfold checkFrame at h
  cases hf : (homeSlots lc).find? (fun k => !slotOK lc g k) with
  | some k => simp [hf, ex_throw, ex_bind_error] at h
  | none =>
    simp only [hf] at h
    by_cases hall : ((homeSlots lc).all fun k => (homeSlots lc).all fun k' =>
        k' == k || g.slotOp k' != g.slotOp k) = true
    · by_cases hap : ((homeSlots lc).all fun k => (homeSlots lc).all fun k' =>
          k' == k || slotsApart lc g k k') = true
      · by_cases hfit : ((List.range lc.homes.size).all (homeFits lc)) = true
        · simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
            List.mem_range] at hall hap hfit
          refine ⟨fun k hk => ?_, fun k hk k' hk' hne => ?_, fun k hk k' hk' hne => ?_, hfit⟩
          · simpa using List.find?_eq_none.mp hf k hk
          · rcases hall k hk k' hk' with he | he
            · exact absurd he.symm hne
            · exact he
          · rcases hap k hk k' hk' with he | he
            · exact absurd he.symm hne
            · exact he
        · simp [hall, hap, hfit, ex_throw, ex_bind_error] at h
      · simp [hall, hap, ex_throw, ex_bind_error] at h
    · simp [hall, ex_throw, ex_bind_error] at h

/-- What `checkFrame` accepted: every home slot `slotOK`, distinct home slots at distinct frame
operands. -/
theorem checkFrame_spec {lc : LocCtx} {g : G2In} (h : checkFrame lc g = .ok ()) :
    (∀ k ∈ homeSlots lc, slotOK lc g k = true) ∧
    ∀ k ∈ homeSlots lc, ∀ k' ∈ homeSlots lc, k ≠ k' → g.slotOp k' ≠ g.slotOp k :=
  ⟨(checkFrame_full h).1, (checkFrame_full h).2.1⟩

theorem checkG2_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} (h : checkG2 lc ps bstart g = .ok tab) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind2 lc g ∧ c.tm = c.cx.termG2 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK2 lc i = true) ∧ checkFrame lc g = .ok () ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG2 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  cases hf : List.find? (fun x => !homeOK2 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq] at h
    subst h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb⟩
    by_cases hi : i < lc.homes.size
    · have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
      simpa using this
    · have hh : lc.home i = none := by
        simp only [LocCtx.home]
        rw [getElem?_neg lc.homes i hi]
        rfl
      unfold homeOK2 homeOK
      rw [hh]

end GoFV.Gen.Check
