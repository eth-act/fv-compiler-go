import GoFV.Gen.Check61a
import GoFV.Proof.Gen.Spec54a
import GoFV.Proof.Gen.Spec38

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `vkind61a` accepted (`GoFV/Gen/Check61a.lean`)

`VK61a`: the read-modify-writes `p x mem` of group A (`rmw`: every family but the
compare-and-swaps), the compare-and-swaps `p old new mem` (`cas`), and the components of either
(`sel0`, `sel1`), with the Progs each emits (`vkind61a_spec`). `vkind61a` is `none` off `op61a`
(`vkind61a_none`). `atomOK_spec` gives the branch targets `atomOK` checked at a value's start.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The temporary of a read-modify-write of group A: none, or (`andL`, `orL`) a register G1 may
write in `rt`, distinct from the pointer's and the result's. -/
def TempOK61 (lc : LocCtx) (v : Value) (f : AtomF61) (rp rd rt : Int) : Prop :=
  ((lc.temps[v.id]?).join = none ∧ f ≠ .andL ∧ f ≠ .orL ∧ rt = 0) ∨
    ∃ t, (lc.temps[v.id]?).join = some t ∧ (f = .andL ∨ f = .orL) ∧ objOf? t = some rt ∧
      t ≠ zeroReg ∧ destOK t = true ∧ rt ≠ rp ∧ rt ≠ rd

/-- What `vkind61a` accepted, and what it emits. -/
inductive VK61a (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- A read-modify-write `p x mem` of family `f` (not a compare-and-swap) of `n` bytes: the
  pointer in `rp` (64 bits, not `ZERO`), the operand in `rv` (class `8n`), the component of class
  `8n` in `rd`, none of them `R27`, `rd` neither `rp` nor `rv`; the temporary `TempOK61`. -/
  | rmw {f : AtomF61} {n : Nat} {t0 : Ty} {rp rv rd rt : Int} {r : Nat} :
      atom61? v.op = some (f, n) → f ≠ .cas → f ≠ .casV → v.args.size = 3 → v.aux = none →
      lc.ty v.id = .tuple [t0, .mem] → cls t0 = some (8 * n) →
      argObj lc v 0 = .ok (64, rp) → rp ≠ r27A → rp ≠ ARM64.REGZERO →
      argObj lc v 1 = .ok (8 * n, rv) → rv ≠ r27A → memArg lc v 2 = .ok () →
      lc.home v.id = some (.pair (some r) none) → r ≠ zeroReg → destOK r = true →
      objOf? r = some rd → rd ≠ rp → rd ≠ rv → TempOK61 lc v f rp rd rt →
      VK61a lc v (.progs (atomPats61 f n rp rv rv rd rt))
  /-- A compare-and-swap `p old new mem` (`cas`, `casV`) of `n` bytes, no temporary: the pointer
  in `rp` (64 bits, not `ZERO`), `old` in `ro` and `new` in `rn` (class `8n`), the boolean in
  `rd`, none of the operands `R27`. -/
  | cas {f : AtomF61} {n : Nat} {t0 : Ty} {rp ro rn rd : Int} {r : Nat} :
      atom61? v.op = some (f, n) → (f = .cas ∨ f = .casV) → (lc.temps[v.id]?).join = none →
      v.args.size = 4 → v.aux = none → lc.ty v.id = .tuple [t0, .mem] → cls t0 = some 1 →
      argObj lc v 0 = .ok (64, rp) → rp ≠ r27A → rp ≠ ARM64.REGZERO →
      argObj lc v 1 = .ok (8 * n, ro) → ro ≠ r27A → argObj lc v 2 = .ok (8 * n, rn) →
      rn ≠ r27A → memArg lc v 3 = .ok () →
      lc.home v.id = some (.pair (some r) none) → r ≠ zeroReg → destOK r = true →
      objOf? r = some rd →
      VK61a lc v (.progs (atomPats61 f n rp ro rn rd 0))
  /-- `Select0` of a value of group A, homed in its register: no code. -/
  | sel0 {c : ID} {r : Nat} {t0 : Ty} :
      (lc.temps[v.id]?).join = none →
      v.op = .Select0 → v.args.size = 1 → v.args[0]? = some c →
      ((lc.ctx.f.value? c).any fun u => (atom61? u.op).isSome) = true →
      lc.ty c = .tuple [t0, .mem] → (cls t0).isSome = true →
      lc.home c = some (.pair (some r) none) → lc.home v.id = some (.reg r) → r ≠ zeroReg →
      destOK r = true → (objOf? r).isSome = true → (cls (lc.ty v.id)).isSome = true →
      cls t0 = cls (lc.ty v.id) → VK61a lc v .none
  /-- `Select1` of a value of group A: the memory, no home, no code. -/
  | sel1 {c : ID} {r : Nat} {t0 : Ty} :
      (lc.temps[v.id]?).join = none →
      v.op = .Select1 → v.args.size = 1 → v.args[0]? = some c →
      ((lc.ctx.f.value? c).any fun u => (atom61? u.op).isSome) = true →
      lc.ty c = .tuple [t0, .mem] → (cls t0).isSome = true →
      lc.home c = some (.pair (some r) none) → memTy (lc.ty v.id) = true →
      lc.home v.id = none → VK61a lc v .none

section Helpers

variable {lc : LocCtx} {v : Value} {kd : VKind2}

theorem atomTy61_spec {cas : Bool} {n : Nat} {t : Ty} (h : atomTy61 cas n t = true) :
    ∃ t0, t = .tuple [t0, .mem] ∧ cls t0 = some (if cas then 1 else 8 * n) := by
  unfold atomTy61 at h
  split at h
  · rename_i t0
    exact ⟨t0, rfl, by simpa using h⟩
  · cases h

theorem atomArg61_spec {i c : Nat} {r : Int} (h : atomArg61 lc v i c = .ok r) :
    argObj lc v i = .ok (c, r) ∧ r ≠ r27A := by
  unfold atomArg61 at h
  obtain ⟨⟨ca, r'⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨hk, h⟩ := ex_guard h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hk
  obtain ⟨rfl, hk⟩ := hk
  exact ⟨hao, hk⟩

theorem atomHome61_spec {rd : Int} (h : atomHome61 lc v = .ok rd) :
    ∃ r, lc.home v.id = some (.pair (some r) none) ∧ r ≠ zeroReg ∧ destOK r = true ∧
      objOf? r = some rd := by
  unfold atomHome61 at h
  cases hh : ldarHome? lc v.id with
  | none => rw [hh] at h; simp [ex_throw] at h
  | some r =>
    rw [hh] at h
    obtain ⟨hr, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hr
    cases ho : objOf? r with
    | none => rw [ho] at h; simp [ex_throw] at h
    | some rd' =>
      rw [ho] at h
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      exact ⟨r, ldarHome?_some hh, hr.1, hr.2, ho⟩

private theorem rmwKind61_spec {f : AtomF61} {n : Nat} (hop : atom61? v.op = some (f, n))
    (hf1 : f ≠ .cas) (hf2 : f ≠ .casV) (h : rmwKind61 lc v f n = .ok kd) : VK61a lc v kd := by
  unfold rmwKind61 at h
  obtain ⟨hs, h⟩ := ex_guard h
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨hsz, hax⟩, hty⟩ := hs
  obtain ⟨t0, hty, hc0⟩ := atomTy61_spec hty
  simp only [Bool.false_eq_true, ↓reduceIte] at hc0
  obtain ⟨rp, hrp, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpz, h⟩ := ex_guard h
  simp only [bne_iff_ne, ne_eq] at hpz
  obtain ⟨rv, hrv, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  obtain ⟨rd, hrd, h⟩ := ex_bind_eq_ok h
  obtain ⟨hd, h⟩ := ex_guard h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hd
  obtain ⟨hap, hpr⟩ := atomArg61_spec hrp
  obtain ⟨hav, hvr⟩ := atomArg61_spec hrv
  obtain ⟨r, hh, hrz, hdo, hor⟩ := atomHome61_spec hrd
  split at h
  next ht =>
    split at h
    next => simp [ex_throw, Functor.map, Except.map] at h
    next hn =>
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hn
      exact .rmw hop hf1 hf2 hsz hax hty hc0 hap hpr hpz hav hvr hma hh hrz hdo hor hd.1 hd.2
        (.inl ⟨ht, hn.1, hn.2, rfl⟩)
  next t ht =>
    obtain ⟨hy, h⟩ := ex_guard h
    simp only [Bool.or_eq_true, beq_iff_eq] at hy
    cases ho : objOf? t with
    | none => rw [ho] at h; simp [ex_throw] at h
    | some rt =>
      rw [ho] at h
      obtain ⟨hk, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      exact .rmw hop hf1 hf2 hsz hax hty hc0 hap hpr hpz hav hvr hma hh hrz hdo hor hd.1 hd.2
        (.inr ⟨t, ht, hy, ho, hk.1.1.1, hk.1.1.2, hk.1.2, hk.2⟩)

private theorem casKind61_spec {f : AtomF61} {n : Nat} (hop : atom61? v.op = some (f, n))
    (hf : f = .cas ∨ f = .casV) (h : casKind61 lc v f n = .ok kd) : VK61a lc v kd := by
  unfold casKind61 at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  obtain ⟨hs, h⟩ := ex_guard h
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨hsz, hax⟩, hty⟩ := hs
  obtain ⟨t0, hty, hc0⟩ := atomTy61_spec hty
  simp only [↓reduceIte] at hc0
  obtain ⟨rp, hrp, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpz, h⟩ := ex_guard h
  simp only [bne_iff_ne, ne_eq] at hpz
  obtain ⟨ro, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨rn, hrn, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  obtain ⟨rd, hrd, h⟩ := ex_bind_eq_ok h
  simp only [ex_pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hap, hpr⟩ := atomArg61_spec hrp
  obtain ⟨hao, hor'⟩ := atomArg61_spec hro
  obtain ⟨han, hnr⟩ := atomArg61_spec hrn
  obtain ⟨r, hh, hrz, hdo, hor⟩ := atomHome61_spec hrd
  exact .cas hop hf ht hsz hax hty hc0 hap hpr hpz hao hor' han hnr hma hh hrz hdo hor

private theorem selAtom61_spec (hsel : selAtom61 lc v = true) (h : selLdarKind lc v = .ok kd) :
    VK61a lc v kd := by
  unfold selAtom61 at hsel
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hsel
  obtain ⟨hop, hu⟩ := hsel
  unfold selLdarKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  cases hc : v.args[0]? with
  | none => rw [hc] at h; simp [ex_throw] at h
  | some c =>
    rw [hc] at h
    rw [hc, Option.bind_some] at hu
    obtain ⟨hsz, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsz
    obtain ⟨hsz, hst⟩ := hsz
    obtain ⟨t0, htc, hc0⟩ := ldarSelTy_spec hst
    cases hh : ldarHome? lc c with
    | none => rw [hh] at h; simp [ex_throw] at h
    | some r =>
      rw [hh] at h
      rcases hop with hop | hop
      · simp only [hop, beq_self_eq_true, ↓reduceIte] at h
        obtain ⟨hk, h⟩ := ex_guard h
        simp only [ex_pure, Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hk
        obtain ⟨⟨⟨⟨⟨hvh, hrz⟩, hd⟩, hob⟩, hcl⟩, hcc⟩ := hk
        rw [htc] at hcc
        exact .sel0 ht hop hsz hc hu htc hc0 (ldarHome?_some hh) hvh hrz hd hob hcl
          (by simpa [tupleTys] using hcc)
      · have h0 : (v.op == .Select0) = false := by rw [hop]; rfl
        simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨hk, h⟩ := ex_guard h
        simp only [ex_pure, Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        exact .sel1 ht hop hsz hc hu htc hc0 (ldarHome?_some hh) hk.1 hk.2

end Helpers

/-- What `vkind61a` accepted. -/
theorem vkind61a_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (h : vkind61a lc v = some (.ok kd)) : VK61a lc v kd := by
  unfold vkind61a at h
  cases hop : atom61? v.op with
  | some p =>
    obtain ⟨f, n⟩ := p
    rw [hop] at h
    simp only [Option.some.injEq] at h
    unfold atomKind61 at h
    by_cases hc : f = .cas ∨ f = .casV
    · have hb : (f == .cas || f == .casV) = true := by
        rcases hc with rfl | rfl <;> rfl
      rw [hb] at h
      simp only [↓reduceIte] at h
      exact casKind61_spec hop hc h
    · have hb : (f == .cas || f == .casV) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        exact ⟨fun e => hc (.inl e), fun e => hc (.inr e)⟩
      rw [hb] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact rmwKind61_spec hop (fun e => hc (.inl e)) (fun e => hc (.inr e)) h
  | none =>
    rw [hop] at h
    simp only at h
    split at h
    · rename_i hs
      simp only [Option.some.injEq] at h
      exact selAtom61_spec hs h
    · cases h

/-- Off the ops of G61's group A and their components, `vkind61a` is `none`. -/
theorem vkind61a_none {lc : LocCtx} {v : Value} (h : op61a v.op = false) : vkind61a lc v = none := by
  simp only [op61a, Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
    beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hs : selAtom61 lc v = false := by
    simp [selAtom61, h2, h3]
  simp only [vkind61a, h1, hs, Bool.false_eq_true, ↓reduceIte]

/-- A value `VK61a` accepted has an op of G61's group A, or is a component. -/
theorem vk61a_op {lc : LocCtx} {v : Value} {kd : VKind2} (h : VK61a lc v kd) :
    op61a v.op = true := by
  cases h with
  | rmw hop => simp [op61a, hop]
  | cas hop => simp [op61a, hop]
  | sel0 _ hop => simp [op61a, hop]
  | sel1 _ hop => simp [op61a, hop]

/-! ## The branch targets -/

private theorem mem_of_lookup61 {l : List (ID × List Nat)} {b : ID} {r : List Nat}
    (h : l.lookup b = some r) : (b, r) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨a, x⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hba
      cases h
      simp only [beq_iff_eq] at hba
      subst hba
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- What `atomOK` checked of a value of group A at its start in the PC table. -/
theorem atomOK_spec {lc : LocCtx} {ps : Array Prog} {tab : PcTab} (h : atomOK lc ps tab = true)
    {bid : ID} {row : List Nat} (hrow : tab.lookup bid = some row) {b : Block}
    (hb : lc.ctx.f.block? bid = some b) {i : Nat} {id : ID} (hi : b.values[i]? = some id)
    {v : Value} (hv : lc.ctx.f.value? id = some v) {f : AtomF61} {n : Nat}
    (hop : atom61? v.op = some (f, n)) : atomTgt f ps (row.getD i 0) = true := by
  unfold atomOK at h
  have hmem : (bid, row) ∈ tab := mem_of_lookup61 hrow
  have := List.all_eq_true.1 h _ hmem
  simp only [hb] at this
  have hi' : i < b.values.size := (Array.getElem?_eq_some_iff.1 hi).1
  have := List.all_eq_true.1 this i (List.mem_range.2 hi')
  simpa [hi, hv, hop] using this

end GoFV.Gen.Check
